{-# LANGUAGE PolymorphicComponents, RecordWildCards, ScopedTypeVariables #-}
module TermiteGame where

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
import RefineCommon hiding (doEnVars)

--Input to the refinement algorithm. Represents the spec.
data Abstractor s u sp lp = Abstractor {
    goalAbs    :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) (DDNode s u),
    fairAbs    :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) (DDNode s u),
    initAbs    :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) (DDNode s u),
    contAbs    :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) (DDNode s u),
    updateAbs  :: forall pdb. [(sp, [DDNode s u])] -> VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) (DDNode s u)
}

-- ===Data structures for keeping track of abstraction state===
data RefineStatic s u = RefineStatic {
    cont :: DDNode s u,
    goal :: DDNode s u,
    fair :: DDNode s u,
    init :: DDNode s u
}

data RefineDynamic s u = RefineDynamic {
    --relations
    trans                   :: DDNode s u,
    consistentMinusCULCont  :: DDNode s u,
    consistentPlusCULCont   :: DDNode s u,
    consistentMinusCULUCont :: DDNode s u,
    consistentPlusCULUCont  :: DDNode s u
}

type Lab s u = [([DDNode s u], DDNode s u)]

doEnVars :: (Ops s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)) -> Ops s u -> DDNode s u -> Lab s u -> ST s (DDNode s u)
doEnVars qFunc ops@Ops{..} strat envars = do
    ref strat
    foldM func strat envars
    where
    func soFar (var, en) = do
        varCube <- nodesToCube var
        e <- qFunc ops varCube soFar
        deref varCube
        res <- bite en soFar e
        deref e
        return res

doEnCont  = doEnVars bforall
doEnUCont = doEnVars bexists

--Find the <state, untracked, label> tuples that guaranteed to be in the goal for a given transition relation
cpre' :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cpre' ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} hasOutgoings target = do
    nextWin  <- mapVars target
    strat    <- liftM bnot $ andAbstract _nextCube trans (bnot nextWin)
    deref nextWin
    stratAvl <- hasOutgoings .& strat
    deref strat
    return stratAvl

--Returns the set of <state, untracked> pairs that are winning 
cpreOver'' :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> ST s (DDNode s u)
cpreOver'' ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} hasOutgoingsCont labelPreds target = do
    strat     <- cpre' ops si rd hasOutgoingsCont target
    stratCont <- doEnCont ops strat labelPreds
    deref strat
    winCont   <- andAbstract _labelCube consistentPlusCULCont stratCont
    winUCont  <- liftM bnot $ andAbstract _labelCube btrue (bnot strat)
    win       <- bite cont winCont winUCont
    mapM deref [winCont, winUCont]
    return win
    
--Returns the set of <state, untracked> pairs that are winning 
cpreUnder'' :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> ST s (DDNode s u)
cpreUnder'' ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} hasOutgoingsCont labelPreds target = do
    strat     <- cpre' ops si rd hasOutgoingsCont target
    stratCont <- doEnCont ops strat labelPreds
    deref strat
    winCont   <- andAbstract _labelCube consistentMinusCULCont stratCont
    winUCont  <- liftM bnot $ andAbstract _labelCube btrue (bnot strat)
    win       <- bite cont winCont winUCont
    mapM deref [winCont, winUCont]
    return win

cPreOver :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> ST s (DDNode s u)
cPreOver ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} hasOutgoingsCont labelPreds target = do
    su  <- cpreOver'' ops si rs rd hasOutgoingsCont labelPreds target
    res <- bexists _untrackedCube su
    deref su
    return res

cPreUnder :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> ST s (DDNode s u)
cPreUnder ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} hasOutgoingsCont labelPreds target = do
    su  <- cpreUnder'' ops si rs rd hasOutgoingsCont labelPreds target
    res <- bforall _untrackedCube su
    deref su
    return res

winningSU :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> Lab s u -> DDNode s u -> ST s (DDNode s u)
winningSU ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} labelPreds target = do
    hasOutgoings <- bexists _nextCube trans
    res <- cpreOver'' ops si rs rd hasOutgoings labelPreds target
    deref hasOutgoings
    return res

solveFair :: (Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> ST s (DDNode s u)) -> Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> Lab s u -> DDNode s u -> ST s (DDNode s u)
solveFair cpreFunc ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} labelPreds winning = do
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
        res <- cpreFunc ops si rs rd hasOutgoings labelPreds t2
        deref t2
        return res

solveGame :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> Lab s u -> DDNode s u -> ST s (DDNode s u)
solveGame ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} labelPreds startingPoint = do
    fixedPoint ops func startingPoint
    where
    func target = do
        traceST "solveGame: iteration"
        t1 <- target .| goal
        res <- solveFair cPreUnder ops si rs rd labelPreds t1
        deref t1
        return res

check msg ops = return ()

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
    --abstract the controllable condition
    (contExpr, newVarsCont) <- doGoal ops contAbs
    lift $ check "After compiling fair" ops
    --get the abstract update functions for the goal predicates and variables
    updateExprConj' <- doUpdate ops (updateAbs (nub $ _allocatedStateVars newVarsGoal ++ _allocatedStateVars newVarsFair ++ _allocatedStateVars newVarsCont))
    outcomeCube <- gets $ _outcomeCube . _sections
    updateExprConj <- lift $ bexists outcomeCube updateExprConj'
    lift $ deref updateExprConj'

    --create the consistency constraints
    let consistentPlusCULCont  = btrue
        consistentPlusCULUCont = btrue
    lift $ ref consistentPlusCULCont
    lift $ ref consistentPlusCULUCont
    labelPreds <- gets $ _labelVars . _symbolTable
    consistentMinusCULCont <- lift $ conj ops $ map (bnot . fst . snd) $ Map.elems labelPreds
    let consistentMinusCULUCont = consistentMinusCULCont
    lift $ ref consistentMinusCULUCont
    --construct the RefineDynamic and RefineStatic
    let rd = RefineDynamic {
            trans  = updateExprConj,
            ..
        }
        rs = RefineStatic {
            goal = goalExpr,
            fair = fairExpr,
            init = initExpr,
            cont = contExpr
        }
    return (rd, rs)

refineStrategy = refineLeastPreds

pickUntrackedToPromote :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> RefineStatic s u -> Lab s u -> DDNode s u -> DDNode s u -> ST s (Maybe [Int])
pickUntrackedToPromote ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} rs@RefineStatic{..} labelPreds win lastLFP = do
    win''  <- win .& fair
    win'   <- win'' .| lastLFP
    deref win''
    su     <- winningSU ops si rs rd labelPreds win'
    deref win'
    toDrop <- (bnot su) .& win
    deref su
    res    <- refineStrategy ops si toDrop
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
    labelPredsPreUpdate  <- gets $ _labelVars . _symbolTable

    --compute the update functions
    updateExprConj'   <- doUpdate ops (updateAbs _allocatedStateVars)
    outcomeCube <- gets $ _outcomeCube . _sections
    updateExprConj''  <- lift $ bexists outcomeCube updateExprConj'
    lift $ deref updateExprConj'

    --update the transition relation
    updateExprConj  <- lift $ andDeref ops trans updateExprConj''

    {-
    labelPreds           <- gets $ _labelVars . _symbolTable
    consistentMinusCUL'' <- lift $ conj ops $ map (bnot . fst . snd) $ Map.elems $ labelPreds Map.\\ labelPredsPreUpdate
    consistentMinusCUL'  <- lift $ andDeref ops consistentMinusCUL consistentMinusCUL''
    -}

    return rd {
        trans  = updateExprConj
    }

--Refine one of the consistency relations so that we make progress. Does not promote untracked state.
refineConsistency :: (Ord sp, Ord lp, Show sp, Show lp) => Ops s u -> TheorySolver s u sp lp -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) (Maybe (RefineDynamic s u))
refineConsistency ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} win winning = do
    syi@SymbolInfo{..} <- gets _symbolTable 
    si@SectionInfo{..} <- gets _sections
    win''              <- lift $ win .& fair
    win'               <- lift $ win'' .| winning
    lift $ deref win''
    hasOutgoings       <- lift $ bexists _nextCube trans
    winNoConstraint'   <- lift $ cpre' ops si rd hasOutgoings win'
    let lp             =  map (map fst *** fst) $ Map.elems _labelVars
    winNoConstraint    <- lift $ doEnCont ops winNoConstraint' lp
    lift $ deref winNoConstraint'
    lift $ mapM deref [win', hasOutgoings]
    winActOver         <- lift $ winNoConstraint .& consistentPlusCULCont
    winActUnder        <- lift $ andAbstract _labelCube winNoConstraint consistentMinusCULCont
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
            --Alive : nothing
            let groupedState = groupForUnsatCore cStatePreds
                groupedLabel = groupForUnsatCore cLabelPreds
            lift $ traceST $ "state preds for solver: " ++ show groupedState
            lift $ traceST $ "label preds for solver: " ++ show groupedLabel
            case unsatCoreStateLabel groupedState groupedLabel of
                Just (statePairs, labelPairs) -> do
                    --statePairs, labelPairs is inconsistent so subtract this from consistentPlusCUL
                    lift $ traceST "refining consistentPlusCUL"
                    inconsistent       <- lift $ stateLabelInconsistent ops syi statePairs labelPairs
                    consistentPlusCUL' <- lift $ andDeref ops consistentPlusCULCont (bnot inconsistent)
                    lift $ check "refineConsistency4" ops
                    refineConsistency ops ts (rd {consistentPlusCULCont = consistentPlusCUL'}) rs win winning
                Nothing -> do
                    --the (s, u, l) tuple is consistent so add this to consistentMinusCUL
                    lift $ traceST "predicates are consistent. refining consistentMinusCUL..."
                    eQuantExpr <- doUpdate ops (eQuant groupedLabel)

                    consistentCube'     <- lift $ stateLabelConsistent ops syi groupedLabel 
                    consistentCube      <- lift $ andDeref ops consistentCube' eQuantExpr
                    consistentMinusCUL' <- lift $ orDeref ops consistentMinusCULCont consistentCube

                    return $ Just $ rd {
                        consistentMinusCULCont = consistentMinusCUL'
                    }
   
--The abstraction-refinement loop
absRefineLoop :: forall s u o sp lp. (Ord sp, Ord lp, Show sp, Show lp) => STDdManager s u -> Abstractor s u sp lp -> TheorySolver s u sp lp -> o -> ST s Bool
absRefineLoop m spec ts abstractorState = 
    let ops@Ops{..} = constructOps m in
    flip evalStateT (initialDB ops) $ do
        (rd, rs) <- initialAbstraction ops spec
        lift $ traceST "Refinement state after initial abstraction: " 
        lift $ traceST $ "Goal is: " ++ (bddSynopsis ops $ goal rs)
        lift $ traceST $ "Fair is: " ++ (bddSynopsis ops $ fair rs)
        lift $ traceST $ "Init is: " ++ (bddSynopsis ops $ TermiteGame.init rs)
        refineLoop ops rs rd bfalse
        where
            refineLoop :: Ops s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) Bool
            refineLoop ops@Ops{..} rs@RefineStatic{..} = refineLoop'
                where 
                refineLoop' :: RefineDynamic s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) Bool
                refineLoop' rd@RefineDynamic{..} lastWin = do
                    si@SectionInfo{..} <- gets _sections
                    lift $ setVarMap _trackedNodes _nextNodes
                    labelPreds <- gets $ _labelVars . _symbolTable
                    let lp = map (map fst *** fst) $ Map.elems labelPreds
                    winRegion <- lift $ solveGame ops si rs rd lp lastWin
                    lift $ deref lastWin
                    winning <- lift $ init `leq` winRegion
                    --Alive: winRegion, rd, rs
                    case winning of
                        True -> lift $ do
                            traceST "Winning"
                            deref winRegion
                            return $ True
                        False -> do
                            lift $ traceST "Not winning without further refinement"
                            winAndGoal <- lift $ winRegion .| goal
                            newWin <- lift $ solveFair cPreOver ops si rs rd lp winAndGoal
                            res <- refineConsistency ops ts rd rs newWin winAndGoal
                            si@SectionInfo{..} <- gets _sections
                            case res of
                                Just newRD -> do
                                    lift $ traceST "Refined consistency relations. Re-solving..."
                                    lift $ mapM deref [newWin, winAndGoal]
                                    refineLoop' newRD winRegion
                                Nothing -> do
                                    lift $ traceST "Could not refine consistency relations. Attempting to refine untracked state variables"
                                    res <- lift $ pickUntrackedToPromote ops si rd rs lp newWin winAndGoal
                                    lift $ mapM deref [newWin, winAndGoal]
                                    case res of 
                                        Just vars -> do
                                            newRD <- promoteUntracked ops spec rd vars 
                                            refineLoop' newRD winRegion
                                        Nothing -> lift $ do
                                            traceST "Losing"
                                            return False

