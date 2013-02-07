{-# LANGUAGE PolymorphicComponents, RecordWildCards, ScopedTypeVariables #-}
module RefineLFP where

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
    safeAbs   :: forall pdb. VarOps pdb (BAPred sp lp) BAVar s u -> StateT pdb (ST s) (DDNode s u),
    updateAbs :: forall pdb. [(sp, DDNode s u)] -> [(String, [DDNode s u])] -> VarOps pdb (BAPred sp lp) BAVar s u -> StateT pdb (ST s) (DDNode s u),
    initAbs   :: forall pdb. VarOps pdb (BAPred sp lp) BAVar s u -> StateT pdb (ST s) (DDNode s u)
}

-- ===Data structures for keeping track of abstraction state===
data RefineStatic s u = RefineStatic {
    safeRegion :: DDNode s u,
    init       :: DDNode s u
}

data RefineDynamic s u = RefineDynamic {
    --relations
    trans              :: DDNode s u,
    consistentPlusCU   :: DDNode s u,
    consistentMinusCUL :: DDNode s u,
    consistentPlusCUL  :: DDNode s u
}

cPre' :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cPre' Ops{..} SectionInfo{..} RefineDynamic{..} hasOutgoings target = do
    t0 <- mapVars target
    t1 <- liftM bnot $ andAbstract _nextCube trans (bnot t0)
    deref t0
    t2 <- hasOutgoings .& t1
    deref t1
    return t2

cPre :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cPre ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} hasOutgoings target = do
    t2 <- cPre' ops si rd hasOutgoings target
    ccube <- _labelCube .& _untrackedCube
    t3 <- andAbstract ccube consistentPlusCUL t2
    deref t2
    deref ccube
    return t3

solveGame :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> ST s (DDNode s u)
solveGame ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} target = do
    hasOutgoings <- bexists _nextCube trans
    fp <- fixedPoint ops (func hasOutgoings) target
    deref hasOutgoings
    return fp
    where
    func hasOutgoings target = do
        traceST "solveGame: iteration"
        t1 <- target .& safeRegion
        res <- cPre ops si rd hasOutgoings t1
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
    (safeExpr, NewVars{..}) <- doGoal ops safeAbs
    lift $ check "After compiling goal" ops
    --get the abstract update functions for the goal predicates and variables
    updateExprConj'' <- doUpdate ops (updateAbs _allocatedStatePreds _allocatedStateVars)
    outcomeCube <- gets $ _outcomeCube . _sections
    updateExprConj' <- lift $ bexists outcomeCube updateExprConj''
    lift $ deref updateExprConj''
    labelPreds <- gets $ _labelPreds . _symbolTable
    updateExprConj  <- lift $ doEnVars ops updateExprConj' $ map (fst *** fst) $ Map.elems labelPreds
    lift $ deref updateExprConj'
    --create the consistency constraints
    let consistentPlusCU   = btrue
        consistentPlusCUL  = btrue
    lift $ ref consistentPlusCU
    lift $ ref consistentPlusCUL
    consistentMinusCUL <- lift $ conj ops $ map (bnot . fst . snd) $ Map.elems labelPreds
    --construct the RefineDynamic and RefineStatic
    let rd = RefineDynamic {
            trans           = updateExprConj,
            ..
        }
        rs = RefineStatic {
            safeRegion = safeExpr,
            init       = initExpr
        }
    return (rd, rs)

check msg ops = return ()

refineStrategy = refineLeastPreds

pickUntrackedToPromote :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> ST s (Maybe [Int])
pickUntrackedToPromote ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} RefineStatic{..} win = do
    hasOutgoings <- bexists _nextCube trans
    win' <- win .& safeRegion
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
    stateRev <- gets $ _stateRev . _symbolTable
    let refineVars = nub $ map (fromJustNote "promoteUntracked: untracked indices not in stateRev" . flip Map.lookup stateRev) indices
    lift $ traceST $ "Promoting: " ++ show refineVars

    NewVars{..} <- promoteUntrackedVars ops refineVars
    labelPredsPreUpdate <- gets $ _labelPreds . _symbolTable

    --compute the update functions
    updateExprConj'' <- doUpdate ops $ updateAbs _allocatedStatePreds _allocatedStateVars
    outcomeCube <- gets $ _outcomeCube . _sections
    updateExprConj' <- lift $ bexists outcomeCube updateExprConj''
    lift $ deref updateExprConj''

    labelPreds <- gets $ _labelPreds . _symbolTable
    updateExprConj <- lift $ doEnVars ops updateExprConj' $ map (fst *** fst) $ Map.elems labelPreds
    lift $ deref updateExprConj'

    --update the transition relation
    trans' <- lift $ trans .& updateExprConj
    lift $ deref updateExprConj
    lift $ deref trans

    consistentMinusCUL'' <- lift $ conj ops $ map (bnot . fst . snd) $ Map.elems $ labelPreds Map.\\ labelPredsPreUpdate
    consistentMinusCUL'  <- lift $ consistentMinusCUL .& consistentMinusCUL''
    lift $ deref consistentMinusCUL''
    lift $ deref consistentMinusCUL

    let rd = RefineDynamic {
        trans              = trans',
        consistentPlusCU   = consistentPlusCU,
        consistentMinusCUL = consistentMinusCUL',
        consistentPlusCUL  = consistentPlusCUL
    }

    return rd

--Refine one of the consistency relations so that we make progress. Does not promote untracked state.
refineConsistency :: (Ord sp, Ord lp, Show sp, Show lp) => Ops s u -> TheorySolver s u sp lp -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) (Maybe (RefineDynamic s u))
refineConsistency ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} win = do
    SymbolInfo{..}     <- gets _symbolTable 
    let stp            =  map (show *** (:[]) . getIdx) $ Map.toList _statePreds
    let stv            =  map (show *** map getIdx) $ Map.toList _stateVars
    let lv             =  map (show *** map getIdx)  $ Map.toList _labelVars
    let a              =  map (show *** (:[]) . getIdx . fst) $ Map.toList _labelPreds
    let b              =  map (show *** (:[]) . getIdx . snd) $ Map.toList _labelPreds
    si@SectionInfo{..} <- gets $ _sections
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

            let (stateIndices, labelIndices) = partition (\(p, x) -> elem p _trackedInds || elem p _untrackedInds) c
            let cStatePreds = getPredicates $ map (first $ fromJustNote "refineConsistency2" . flip Map.lookup _stateRev) stateIndices
            let cLabelPreds = getPredicates $ catMaybes $ map (uncurry func) labelIndices
                    where
                    func idx polarity = case fromJustNote "refineConsistency3" $ Map.lookup idx _labelRev of
                        (_, True)   -> Nothing
                        (pred, False) -> Just (pred, polarity)
            lift $ traceST $ "label preds for solver: " ++ show cLabelPreds
            lift $ traceST $ "state preds for solver: " ++ show cStatePreds
            --Alive : nothing
            case unsatCoreStateLabel cStatePreds cLabelPreds of
                Just (statePairs, labelPairs) -> do
                    --statePairs, labelPairs is inconsistent so subtract this from consistentPlusCUL
                    lift $ traceST "refining consistentPlusCUL"
                    inconsistentState <- lift $ makeCube ops $ map (first (getNode . fromJustNote "refineConsistency" . flip Map.lookup _statePreds)) statePairs
                    inconsistentLabel <- lift $ makeCube ops $ map (first (getNode . sel1 . fromJustNote "refineConsistency" . flip Map.lookup _labelPreds)) labelPairs
                    inconsistent <- lift $ inconsistentState .& inconsistentLabel
                    lift $ deref inconsistentState
                    lift $ deref inconsistentLabel
                    consistentPlusCUL' <- lift $ consistentPlusCUL .& bnot inconsistent
                    lift $ deref inconsistent
                    lift $ deref consistentPlusCUL
                    lift $ check "refineConsistency4" ops
                    refineConsistency ops ts (rd {consistentPlusCUL = consistentPlusCUL'}) rs win
                Nothing -> do
                    --the (s, u, l) tuple is consistent so add this to consistentMinusCUL
                    lift $ traceST "predicates are consistent. refining consistentMinusCUL..."
                    eQuantExpr <- doUpdate ops (eQuant cStatePreds cLabelPreds)

                    let statePreds' = map (first $ fst . fromJustNote "refineConsistency" . flip Map.lookup _statePreds) cStatePreds
                        labelPreds' = map (first $ fromJustNote "refineConsistency" . flip Map.lookup _labelPreds) cLabelPreds

                    let func ((lp, le), pol) = [(fst lp, pol), (fst le, True)]
                    labelCube <- lift $ uncurry computeCube $ unzip $ concatMap func labelPreds'

                    let otherEnabling = map (getNode. snd . snd) $ filter (\(p, _) -> not $ p `elem` map fst cLabelPreds) $ Map.toList _labelPreds
                    otherCube <- lift $ uncurry computeCube $ unzip $ zip otherEnabling (repeat False)

                    consistentCube' <- lift $ labelCube .& eQuantExpr
                    consistentCube  <- lift $ consistentCube' .& otherCube
                    lift $ mapM deref [labelCube, eQuantExpr, consistentCube', otherCube]

                    consistentMinusCUL'  <- lift $ consistentMinusCUL .| consistentCube
                    lift $ deref consistentCube
                    lift $ deref consistentMinusCUL

                    return $ Just $ rd {
                        consistentMinusCUL = consistentMinusCUL'
                    }

--The abstraction-refinement loop
absRefineLoop :: forall s u o sp lp. (Ord sp, Ord lp, Show sp, Show lp) => STDdManager s u -> Abstractor s u sp lp -> TheorySolver s u sp lp -> o -> ST s Bool
absRefineLoop m spec ts abstractorState = 
    let ops@Ops{..} = constructOps m in
    flip evalStateT (initialDB ops) $ do
        (rd, rs) <- initialAbstraction ops spec
        lift $ traceST "Refinement state after initial abstraction: " 
        lift $ traceST $ "Goal is: " ++ (bddSynopsis ops $ safeRegion rs)
        lift $ traceST $ "Init is: " ++ (bddSynopsis ops $ RefineLFP.init rs)
        refineLoop ops rs rd btrue
        where
            refineLoop :: Ops s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) Bool
            refineLoop ops@Ops{..} rs@RefineStatic{..} = refineLoop'
                where 
                refineLoop' :: RefineDynamic s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) Bool
                refineLoop' rd@RefineDynamic{..} lastWin = do
                    si@SectionInfo{..} <- gets _sections
                    lift $ setVarMap _trackedNodes _nextNodes
                    winRegion <- lift $ solveGame ops si rs rd lastWin
                    lift $ deref lastWin
                    winning <- lift $ (bnot winRegion) `leq` (bnot init)
                    --Alive: winRegion, rd, rs
                    case winning of
                        False -> lift $ do
                            traceST "Losing"
                            deref winRegion
                            return False
                        True -> do
                            lift $ traceST "Possibly winning, confirming with further refinement"
                            res <- refineConsistency ops ts rd rs winRegion 
                            si@SectionInfo{..} <- gets _sections
                            case res of
                                Just newRD -> do
                                    lift $ traceST "Refined consistency relations. Re-solving..."
                                    refineLoop' newRD winRegion
                                Nothing -> do
                                    lift $ traceST "Could not refine consistency relations. Attempting to refine untracked state variables"
                                    res <- lift $ pickUntrackedToPromote ops si rd rs winRegion
                                    case res of 
                                        Just vars -> do
                                            newRD <- promoteUntracked ops spec rd vars 
                                            refineLoop' newRD winRegion
                                        Nothing -> lift $ do
                                            traceST "Winning"
                                            deref winRegion
                                            return True

