{-# LANGUAGE PolymorphicComponents, RecordWildCards, ScopedTypeVariables #-}
module RefineReachFair where

import Control.Monad.ST.Lazy
import Data.STRef.Lazy
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Arrow
import Data.List
import Control.Monad
import Data.Maybe
import Data.Tuple.All
import Data.Tuple
import Debug.Trace as T
import Control.Monad.State

import Safe

import Util
import RefineUtil
import BddRecord
import BddUtil
import BddInterp
import Interface
import RefineCommon

--Input to the refinement algorithm. Represents the spec.
data Abstractor s u sp lp = Abstractor {
    goalAbs   :: forall pdb. VarOps pdb (BAPred sp lp) BAVar s u -> StateT pdb (ST s) (DDNode s u),
    fairAbs   :: forall pdb. VarOps pdb (BAPred sp lp) BAVar s u -> StateT pdb (ST s) (DDNode s u),
    updateAbs :: forall pdb. [(sp, DDNode s u)] -> [(String, [DDNode s u])] -> VarOps pdb (BAPred sp lp) BAVar s u -> StateT pdb (ST s) (DDNode s u),
    initAbs   :: forall pdb. VarOps pdb (BAPred sp lp) BAVar s u -> StateT pdb (ST s) (DDNode s u)
}

-- ===Data structures for keeping track of abstraction state===
data RefineStatic s u = RefineStatic {
    goal :: DDNode s u,
    fair :: DDNode s u,
    init :: DDNode s u
}

data RefineDynamic s u = RefineDynamic {
    --relations
    trans              :: DDNode s u,
    consistentPlusCU   :: DDNode s u,
    consistentMinusCUL :: DDNode s u,
    consistentPlusCUL  :: DDNode s u
}

--Returns {<state, untracked, label>}
cPre' :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cPre' Ops{..} SectionInfo{..} RefineDynamic{..} hasOutgoings target = do
    t0 <- mapVars target
    t1 <- liftM bnot $ andAbstract _nextCube trans (bnot t0)
    deref t0
    t2 <- hasOutgoings .& t1
    deref t1
    return t2

cPreOver :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cPreOver ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} hasOutgoings target = do
    t2 <- cPre' ops si rd hasOutgoings target
    ccube <- _labelCube .& _untrackedCube
    t3 <- andAbstract ccube consistentPlusCUL t2
    deref t2
    deref ccube
    return t3

cPreUnder :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cPreUnder ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} hasOutgoings target = do
    t2 <- cPre' ops si rd hasOutgoings target
    t3 <- andAbstract _labelCube consistentMinusCUL t2
    deref t2
    t4 <- liftM bnot $ andAbstract _untrackedCube consistentPlusCU (bnot t3)
    deref t3
    return t4

solveFair :: (Ops s u -> SectionInfo s u -> RefineDynamic s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)) -> Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> ST s (DDNode s u)
solveFair cpreFunc ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} winning = do
    hasOutgoings <- bexists _nextCube trans
    fp <- fixedPoint ops (func hasOutgoings) btrue
    deref hasOutgoings
    return fp
    where
    func hasOutgoings target = do
        traceST "solveFair: iteration"
        t1 <- target .& fair
        t2 <- t1 .| winning
        deref t1
        res <- cpreFunc ops si rd hasOutgoings t2
        deref t2
        return res

solveGame :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> ST s (DDNode s u)
solveGame ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} startingPoint = do
    fixedPoint ops func startingPoint
    where
    func target = do
        traceST "solveGame: iteration"
        t1 <- target .| goal
        res <- solveFair cPreUnder ops si rs rd t1
        deref t1
        return res

--Create an initial abstraction and set up the data structures
initialAbstraction :: (Show sp, Show lp, Ord sp, Ord lp) => Ops s u -> Abstractor s u sp lp -> StateT (DB s u sp lp) (ST s) (RefineDynamic s u, RefineStatic s u)
initialAbstraction ops@Ops{..} Abstractor{..} = do
    lift $ check "InitialAbstraction start" ops
    --abstract init
    initExpr <- doInit ops initAbs
    lift $ check "After compiling init" ops
    --abstract the goal
    (goalExpr, newVarsGoal) <- doGoal ops goalAbs
    lift $ check "After compiling goal" ops
    --abstract the fair region
    (fairExpr, newVarsFair) <- doGoal ops fairAbs
    lift $ check "After compiling fair" ops
    --get the abstract update functions for the goal predicates and variables
    updateExprConj'' <- doUpdate ops (updateAbs (nub $ _allocatedStatePreds newVarsGoal ++ _allocatedStatePreds newVarsFair) (nub $ _allocatedStateVars newVarsGoal ++ _allocatedStateVars newVarsFair))
    updateExprConj   <- updateWrapper ops updateExprConj''
    --create the consistency constraints
    let consistentPlusCU   = btrue
        consistentPlusCUL  = btrue
    lift $ ref consistentPlusCU
    lift $ ref consistentPlusCUL
    labelPreds <- gets $ _labelPreds . _symbolTable
    consistentMinusCUL <- lift $ conj ops $ map (bnot . fst . snd) $ Map.elems labelPreds
    --construct the RefineDynamic and RefineStatic
    let rd = RefineDynamic {
            trans           = updateExprConj,
            ..
        }
        rs = RefineStatic {
            goal = goalExpr,
            fair = fairExpr,
            init = initExpr
        }
    return (rd, rs)

check msg ops = return ()

refineStrategy = refineLeastPreds

pickUntrackedToPromote :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> ST s (Maybe [Int])
pickUntrackedToPromote ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} RefineStatic{..} win lastLFP = do
    hasOutgoings <- bexists _nextCube trans
    win'' <- win .& fair
    win' <- win'' .| lastLFP
    deref win''
    sul  <- cPre' ops si rd hasOutgoings win'
    deref win'
    deref hasOutgoings
    su   <- andAbstract _labelCube consistentPlusCUL sul
    deref sul
    toDrop <- (bnot su) .& win
    deref su
    res <- refineStrategy ops si toDrop
    deref toDrop
    return res

--Promote untracked state variables to full state variables so that we can make progress towards the goal. Does not refine the consistency relations.
promoteUntracked :: (Ord lp, Ord sp, Show sp, Show lp) => Ops s u -> Abstractor s u sp lp -> RefineDynamic s u -> [Int] -> StateT (DB s u sp lp) (ST s) (RefineDynamic s u)
promoteUntracked ops@Ops{..} Abstractor{..} rd@RefineDynamic{..} indices = do
    --look up the predicates to promote
    stateRev             <- gets $ _stateRev . _symbolTable
    let refineVars       =  nub $ map (fromJustNote "promoteUntracked: untracked indices not in stateRev" . flip Map.lookup stateRev) indices
    lift $ traceST $ "Promoting: " ++ show refineVars

    NewVars{..}          <- promoteUntrackedVars ops refineVars
    labelPredsPreUpdate  <- gets $ _labelPreds . _symbolTable

    --compute the update functions
    updateExprConj''     <- doUpdate ops $ updateAbs _allocatedStatePreds _allocatedStateVars
    updateExprConj       <- updateWrapper ops updateExprConj''

    --update the transition relation
    trans'               <- lift $ andDeref ops trans updateExprConj

    labelPreds           <- gets $ _labelPreds . _symbolTable
    consistentMinusCUL'' <- lift $ conj ops $ map (bnot . fst . snd) $ Map.elems $ labelPreds Map.\\ labelPredsPreUpdate
    consistentMinusCUL'  <- lift $ andDeref ops consistentMinusCUL consistentMinusCUL''

    return rd {
        trans              = trans',
        consistentMinusCUL = consistentMinusCUL'
    }

refineConsistency _ _ _ _ _ = return Nothing

{-
--Refine one of the consistency relations so that we make progress. Does not promote untracked state.
refineConsistency :: (Ord sp, Ord lp, Show sp, Show lp) => Ops s u -> TheorySolver s u sp lp -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) (Maybe (RefineDynamic s u))
refineConsistency ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} win = do
    syi@SymbolInfo{..} <- gets _symbolTable 
    si@SectionInfo{..} <- gets _sections
    win'               <- lift $ win .& safeRegion
    hasOutgoings       <- lift $ bexists _nextCube trans
    winNoConstraint    <- lift $ cPre' ops si rd hasOutgoings win'
    lift $ mapM deref [win', hasOutgoings]
    winActOver         <- lift $ winNoConstraint .& consistentPlusCUL
    winActUnder        <- lift $ andAbstract _labelCube winNoConstraint consistentMinusCUL
    lift $ deref winNoConstraint
    toCheckConsistency <- lift $ winActOver .& bnot winActUnder
    lift $ mapM deref [winActOver, winActUnder]
    --Alive : toCheckConsistency
    case toCheckConsistency==bfalse of 
        True  -> do
            --no refinement of consistency relations will shrink the winning region
            lift $ traceST "no consistency refinement possible"
            lift $ deref toCheckConsistency
            return Nothing
        False -> do
            --There may be a refinement
            --extract a <s, u, l> pair that will make progress if one exists
            c <- lift $ presentInLargePrime ops toCheckConsistency
            lift $ deref toCheckConsistency

            let (cStatePreds, cLabelPreds) = partitionStateLabelPreds si syi c
            lift $ traceST $ "label preds for solver: " ++ show cLabelPreds
            lift $ traceST $ "state preds for solver: " ++ show cStatePreds
            --Alive : nothing
            case unsatCoreStateLabel cStatePreds cLabelPreds of
                Just (statePairs, labelPairs) -> do
                    --statePairs, labelPairs is inconsistent so subtract this from consistentPlusCUL
                    lift $ traceST "refining consistentPlusCUL"
                    inconsistent       <- lift $ stateLabelInconsistent ops syi statePairs labelPairs
                    consistentPlusCUL' <- lift $ andDeref ops consistentPlusCUL (bnot inconsistent)
                    lift $ check "refineConsistency4" ops
                    refineConsistency ops ts (rd {consistentPlusCUL = consistentPlusCUL'}) rs win
                Nothing -> do
                    --the (s, u, l) tuple is consistent so add this to consistentMinusCUL
                    lift $ traceST "predicates are consistent. refining consistentMinusCUL..."
                    eQuantExpr <- doUpdate ops (eQuant cLabelPreds)

                    consistentCube'     <- lift $ stateLabelConsistent ops syi cLabelPreds 
                    consistentCube      <- lift $ andDeref ops consistentCube' eQuantExpr
                    consistentMinusCUL' <- lift $ orDeref ops consistentMinusCUL consistentCube

                    return $ Just $ rd {
                        consistentMinusCUL = consistentMinusCUL'
                    }
-}

fixedPoint2 :: Ops s u -> (DDNode s u -> DDNode s u -> ST s (DDNode s u, DDNode s u)) -> DDNode s u -> DDNode s u -> ST s (DDNode s u, DDNode s u)
fixedPoint2 ops@Ops{..} func state set = do
    (state', set') <- func state set
    deref set
    deref state
    case (set'==set) of --this is safe 
        True -> return (state', set')
        False -> fixedPoint2 ops func state' set'

strategy :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> RefineStatic s u -> ST s (DDNode s u)
strategy ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} rs@RefineStatic{..} = do
    (strat, set) <- fixedPoint2 ops func bfalse bfalse
    return strat
    where
    func strat target = do
        traceST "strategy: iteration"
        t1 <- target .| goal
        res <- solveFair cPreUnder ops si rs rd t1
        deref t1
        t2 <- res .& fair
        t3 <- t2 .| target
        deref t2
        hasOutgoings <- bexists _nextCube trans
        res2 <- cPre' ops si rd hasOutgoings t3
        deref hasOutgoings
        deref t3
        resConsistent <- res2 .& consistentMinusCUL 
        deref res2
        stratNew <- resConsistent .& bnot target
        deref target
        deref resConsistent
        strat' <- strat .| stratNew
        deref strat
        deref stratNew
        return (strat', res)

--The abstraction-refinement loop
absRefineLoop :: forall s u o sp lp. (Ord sp, Ord lp, Show sp, Show lp) => STDdManager s u -> Abstractor s u sp lp -> TheorySolver s u sp lp -> o -> ST s (Maybe String)
absRefineLoop m spec ts abstractorState = 
    let ops@Ops{..} = constructOps m in
    flip evalStateT (initialDB ops) $ do
        (rd, rs) <- initialAbstraction ops spec
        lift $ traceST "Refinement state after initial abstraction: " 
        lift $ traceST $ "Goal is: " ++ (bddSynopsis ops $ goal rs)
        lift $ traceST $ "Fair is: " ++ (bddSynopsis ops $ fair rs)
        lift $ traceST $ "Init is: " ++ (bddSynopsis ops $ RefineReachFair.init rs)
        refineLoop ops rs rd bfalse
        where
            refineLoop :: Ops s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) (Maybe String)
            refineLoop ops@Ops{..} rs@RefineStatic{..} = refineLoop'
                where 
                refineLoop' :: RefineDynamic s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) (Maybe String)
                refineLoop' rd@RefineDynamic{..} lastWin = do
                    si@SectionInfo{..} <- gets _sections
                    lift $ setVarMap _trackedNodes _nextNodes
                    winRegion <- lift $ solveGame ops si rs rd lastWin
                    lift $ deref lastWin
                    winning <- lift $ init `leq` winRegion
                    --Alive: winRegion, rd, rs
                    case winning of
                        True -> lift $ do
                            traceST "Winning"
                            deref winRegion
                            strat <- strategy ops si rd rs 
                            return $ Just $ bddSynopsis ops strat
                        False -> do
                            lift $ traceST "Not winning without further refinement"
                            winAndGoal <- lift $ winRegion .| goal
                            newWin <- lift $ solveFair cPreOver ops si rs rd winAndGoal
                            res <- refineConsistency ops ts rd rs newWin
                            si@SectionInfo{..} <- gets _sections
                            case res of
                                Just newRD -> do
                                    lift $ traceST "Refined consistency relations. Re-solving..."
                                    lift $ mapM deref [newWin, winAndGoal]
                                    refineLoop' newRD winRegion
                                Nothing -> do
                                    lift $ traceST "Could not refine consistency relations. Attempting to refine untracked state variables"
                                    res <- lift $ pickUntrackedToPromote ops si rd rs newWin winAndGoal
                                    lift $ mapM deref [newWin, winAndGoal]
                                    case res of 
                                        Just vars -> do
                                            newRD <- promoteUntracked ops spec rd vars 
                                            refineLoop' newRD winRegion
                                        Nothing -> lift $ do
                                            traceST "Losing"
                                            return Nothing

