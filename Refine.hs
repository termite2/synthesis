{-# LANGUAGE RecordWildCards, ScopedTypeVariables, GADTs, PolymorphicComponents #-}
module Refine (absRefineLoop, VarInfo, Abstractor(..), TheorySolver(..)) where

import Control.Monad.ST.Lazy
import Data.STRef.Lazy
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Arrow
import Data.List
import Control.Monad
import Data.List
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

--Input to the refinement algorithm. Represents the spec.
data Abstractor s u sp lp = Abstractor {
    goalAbs   :: forall pdb. VarOps pdb (BAPred sp lp) BAVar s u -> StateT pdb (ST s) (DDNode s u),
    updateAbs :: forall pdb. [(sp, DDNode s u)] -> [(String, [DDNode s u])] -> VarOps pdb (BAPred sp lp) BAVar s u -> StateT pdb (ST s) (DDNode s u),
    initAbs   :: forall pdb. VarOps pdb (BAPred sp lp) BAVar s u -> StateT pdb (ST s) (DDNode s u)
}

--Theory solving
data TheorySolver s u sp lp = TheorySolver {
    unsatCoreState      :: [(sp, Bool)] -> Maybe [(sp, Bool)],
    unsatCoreStateLabel :: [(sp, Bool)] -> [(lp, Bool)] -> Maybe ([(sp, Bool)], [(lp, Bool)]),
    eQuant              :: forall pdb. [(sp, Bool)] -> [(lp, Bool)] -> VarOps pdb (BAPred sp lp) BAVar s u -> StateT pdb (ST s) (DDNode s u)
}

-- ===Data structures for keeping track of abstraction state===
data RefineStatic s u = RefineStatic {
    goal :: DDNode s u,
    init :: DDNode s u
}

data RefineDynamic s u = RefineDynamic {
    --relations
    trans              :: DDNode s u,
    consistentPlusCU   :: DDNode s u,
    consistentMinusCUL :: DDNode s u,
    consistentPlusCUL  :: DDNode s u
}

-- ===Solve an abstracted and compiled game===

cPre' :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cPre' Ops{..} SectionInfo{..} RefineDynamic{..} hasOutgoings target = do
    t0 <- mapVars target
    t1 <- liftM bnot $ andAbstract _nextCube trans (bnot t0)
    deref t0
    t2 <- hasOutgoings .& t1
    deref t1
    t3 <- consistentMinusCUL .& t2
    deref t2
    t4 <- bexists _labelCube t3
    deref t3
    t5 <- consistentPlusCU .-> t4
    deref t4
    return t5

cPre :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cPre ops@Ops {..} si@SectionInfo{..} rd@RefineDynamic{..} hasOutgoings target = do
    su <- cPre' ops si rd hasOutgoings target
    t6 <- bforall _untrackedCube su
    deref su
    return t6

fixedPoint :: Ops s u -> (DDNode s u -> ST s (DDNode s u)) -> DDNode s u -> ST s (DDNode s u)
fixedPoint (ops @ Ops {..}) func start = do
    res <- func start
    deref start 
    case (res==start) of --this is safe 
        True -> return start
        False -> fixedPoint ops func res
        
solveGame :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> ST s (DDNode s u)
solveGame ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} target = do 
    hasOutgoings <- bexists _nextCube trans
    fp <- fixedPoint ops (func hasOutgoings) target
    deref hasOutgoings
    return fp
    where
    func hasOutgoings target = do
        traceST "solveGame: iteration"
        t1 <- target .| goal
        res <- cPre ops si rd hasOutgoings t1
        deref t1
        return res

-- ===Abstraction refinement===

check msg ops = unsafeIOToST (putStrLn ("checking bdd consistency" ++ msg ++ "\n")) >> debugCheck ops >> checkKeys ops
--check msg ops = return ()

doEnVars :: Ops s u -> DDNode s u -> [(DDNode s u, DDNode s u)] -> ST s (DDNode s u)
doEnVars Ops{..} trans enVars = do
        ref trans
        foldM func trans enVars
    where
    func soFar (pred, en) = do
        e <- bexists pred soFar
        e1 <- e .& bnot en
        deref e
        c <- en .& soFar
        deref soFar
        res <- e1 .| c
        deref c
        deref e1
        return res

--Variable promotion strategies

refineStrategy = refineAny

refineAny :: Ops s u -> SectionInfo  s u -> RefineDynamic s u -> DDNode s u -> ST s (Maybe [Int])
refineAny Ops{..} SectionInfo{..} RefineDynamic{..} newSU = do
    si <- supportIndices newSU
    let ui = si `intersect` _untrackedInds
    return $ case ui of
        []  -> Nothing
        x:_ -> Just [x]

refineFirstPrime :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> DDNode s u -> ST s (Maybe [Int])
refineFirstPrime Ops{..} SectionInfo{..} RefineDynamic{..} newSU = do
    (lc, sz) <- largestCube newSU
    prime    <- makePrime lc newSU
    deref lc
    si       <- supportIndices prime
    deref prime
    let ui = si `intersect` _untrackedInds
    return $ case ui of
        [] -> Nothing
        x  -> Just x

--Refine the least number of untracked state predicates possible to make progress
refineLeastPreds :: forall s u o sp lp. Ops s u -> SectionInfo s u -> RefineDynamic s u -> DDNode s u -> ST s (Maybe [Int])
refineLeastPreds ops@Ops{..} SectionInfo{..} RefineDynamic{..} newSU 
    | newSU == bfalse = return Nothing
    | otherwise       = do
        ref newSU
        (size, vars, remaining) <- sizeVarsNext newSU
        (size, vars) <- doLoop size vars remaining
        return $ Just vars
    where
    sizeVarsNext :: DDNode s u -> ST s (Int, [Int], DDNode s u)
    sizeVarsNext remaining = do
        (lc, sz) <- largestCube remaining
        prime <- makePrime lc newSU
        deref lc
        (size, vars) <- analyseCube prime
        nextRemaining <- band remaining $ bnot prime
        deref remaining
        deref prime
        return (size, vars, nextRemaining)
    doLoop :: Int -> [Int] -> DDNode s u -> ST s (Int, [Int])
    doLoop size vars remaining 
        | remaining == bfalse = return (size, vars)
        | otherwise           = do
            (size', vars', remaining') <- sizeVarsNext remaining
            if (size' < size) then doLoop size' vars' remaining' else doLoop size vars remaining'
    analyseCube :: DDNode s u -> ST s (Int, [Int])
    analyseCube cube' = do
        untrackedCube <- bexists _trackedCube cube'
        support <- supportIndices _untrackedCube
        deref untrackedCube
        return (length support, support)

pickUntrackedToPromote :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> ST s (Maybe [Int])
pickUntrackedToPromote ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} RefineStatic{..} win = do
    traceST "Picking untracked to promote"
    hasOutgoings <- bexists _nextCube trans
    win' <- win .| goal
    su    <- cPre' ops si rd hasOutgoings win'
    deref hasOutgoings
    newSU <- su .& bnot win
    deref win'
    deref su
    res <- refineStrategy ops si rd newSU
    deref newSU
    return res

--Create an initial abstraction and set up the data structures
initialAbstraction :: (Show sp, Show lp, Ord sp, Ord lp) => Ops s u -> Abstractor s u sp lp -> StateT (DB s u sp lp) (ST s) (RefineDynamic s u, RefineStatic s u)
initialAbstraction ops@Ops{..} Abstractor{..} = do
    lift $ check "InitialAbstraction start" ops
    --abstract init
    initExpr <- doInit ops initAbs
    lift $ check "After compiling init" ops
    --abstract the goal
    (goalExpr, NewVars{..}) <- doGoal ops goalAbs
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
            goal = goalExpr,
            init = initExpr
        }
    return (rd, rs)

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

getPredicates :: [(Variable p s u, a)] -> [(p, a)]
getPredicates = mapMaybe func 
    where
    func (Predicate p _, x) = Just (p, x)
    func _                  = Nothing

--Refine one of the consistency relations so that we make progress. Does not promote untracked state.
refineConsistency :: (Ord sp, Ord lp, Show sp, Show lp) => Ops s u -> TheorySolver s u sp lp -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) (Maybe (RefineDynamic s u))
refineConsistency ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} win = do
    SymbolInfo{..} <- gets _symbolTable 
    si@SectionInfo{..} <- gets $ _sections
    win' <- lift $ win .| goal
    t0 <- lift $ mapVars win'
    t2 <- lift $ liftM bnot $ andAbstract _nextCube trans (bnot t0)
    lift $ deref t0
    t3 <- lift $ consistentPlusCUL .& t2
    lift $ deref t2
    hasOutgoings <- lift $ bexists _nextCube trans
    tt3 <- lift $ hasOutgoings .& t3
    --deref hasOutgoings
    lift $ deref t3
    t4 <- lift $ tt3 .& bnot win
    --Alive : win', hasOutgoings, tt3, t4
    case t4==bfalse of 
        True  -> do
            --no refinement of consistency relations will make progress
            --there are no <c, u, l> tuples that are winning with the overapproximation of consistentCUL
            lift $ traceST "no consistency refinement possible"
            lift $ mapM deref [win', hasOutgoings, tt3, t4]
            return Nothing
        False -> do
            --There may be a refinement
            --extract a <s, u> pair that will make progress if one exists
            t5 <- lift $ bexists _labelCube t4
            lift $ deref t4
            (t6, sz) <- lift $ largestCube t5
            t7 <- lift $ makePrime t6 t5
            lift $ deref t5
            lift $ deref t6
            c <- lift $ presentVars ops t7 
            lift $ deref t7
            let stateUntrackedProgress = map (first $ fromJustNote "refineConsistency1" . flip Map.lookup _stateRev) c
            lift $ traceST $ "Tuple that will make progress: " ++ show stateUntrackedProgress
            let preds = getPredicates stateUntrackedProgress
            lift $ traceST $ "Preds being checked for consistency: " ++ show preds
            lift $ check "refineConsistency end2" ops
            --Alive : win', hasOutgoings, tt3 
            case unsatCoreState preds of
                Just pairs -> do
                    --consistentPlusCU can be refined
                    lift $ traceST "refining consistentPlusCU"
                    lift $ mapM deref [win', hasOutgoings, tt3]
                    inconsistent <- lift $ makeCube ops $ map (first (getNode . fromJustNote "refineConsistency" . flip Map.lookup _statePreds)) pairs
                    consistentPlusCU'  <- lift $ consistentPlusCU .& bnot inconsistent
                    lift $ deref consistentPlusCU
                    consistentPlusCUL' <- lift $ consistentPlusCUL .& bnot inconsistent
                    lift $ deref consistentPlusCUL'
                    lift $ deref inconsistent
                    lift $ check "refineConsistency2" ops
                    return $ Just $ rd {consistentPlusCU = consistentPlusCU', consistentPlusCUL = consistentPlusCUL'}
                Nothing -> do
                    lift $ traceST "consistentPlusCU could not be refined"
                    --consistentPlusCU cannot be refined but maybe consistentPlusCUL or consistentMinusCUL can be
                    cpr <- lift $ cPre' ops si rd hasOutgoings win'
                    lift $ mapM deref [win', hasOutgoings]
                    t4 <- lift $ tt3 .& bnot cpr
                    lift $ mapM deref [tt3, cpr]
                    --Alive :t4
                    case t4==bfalse of
                        True -> do
                            lift $ traceST "consistentPlusCUL could not be refined"
                            lift $ deref t4
                            lift $ check "refineConsistency3" ops
                            return Nothing
                        False -> do
                            lift $ check "refineConsistency start3" ops
                            (t6, sz) <- lift $ largestCube t4
                            t7 <- lift $ makePrime t6 t4
                            lift $ deref t4
                            lift $ deref t6
                            c <- lift $ presentVars ops t7
                            lift $ deref t7
                            let (stateIndices, labelIndices) = partition (\(p, x) -> elem p _trackedInds || elem p _untrackedInds) c
                            let cStatePreds = getPredicates $ map (first $ fromJustNote "refineConsistency2" . flip Map.lookup _stateRev) stateIndices
                            let cLabelPreds = getPredicates $ catMaybes $ map (uncurry func) labelIndices
                                    where
                                    func idx polarity = case fromJustNote "refineConsistency3" $ Map.lookup idx _labelRev of
                                        (_, False)   -> Nothing
                                        (pred, True) -> Just (pred, polarity)
                            lift $ traceST $ "label preds for solver: " ++ show cLabelPreds
                            lift $ check "refineConsistency end3" ops
                            --Alive : nothing
                            case unsatCoreStateLabel cStatePreds cLabelPreds of
                                Just (statePairs, labelPairs) -> do
                                    --consistentPlusCUL can be refined
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

                                    consistentCube  <- lift $ labelCube .& eQuantExpr
                                    lift $ mapM deref [labelCube, eQuantExpr]

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
        lift $ traceST $ "Goal is: " ++ (bddSynopsis ops $ goal rs)
        lift $ traceST $ "Init is: " ++ (bddSynopsis ops $ Refine.init rs)
        refineLoop ops rs rd bfalse
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
                    winning <- lift $ init `leq` winRegion 
                    --Alive: winRegion, rd, rs
                    case winning of
                        True -> lift $ do
                            traceST "Winning"
                            deref winRegion
                            return True
                        False -> do
                            lift $ traceST "Not winning without further refinement"
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
                                            lift $ traceST "Found untracked variables to promote. Promoting them..."
                                            newRD <- promoteUntracked ops spec rd vars 
                                            refineLoop' newRD winRegion
                                        Nothing -> lift $ do
                                            traceST "Game is not winning"
                                            deref winRegion
                                            return False

