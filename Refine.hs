{-# LANGUAGE RecordWildCards, ScopedTypeVariables, GADTs #-}
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

import Safe

import Util
import RefineUtil
import BddRecord
import BddUtil
import BddInterp

--Input to the refinement algorithm. Represents the spec.
data Abstractor s u o sp lp = Abstractor {
    goalAbs   :: VarOps pdb p v s u -> StateT pdb (ST s) (DDNode s u),
    updateAbs :: VarOps pdb p v s u -> StateT pdb (ST s) (DDNode s u),
    initAbs   :: VarOps pdb p v s u -> StateT pdb (ST s) (DDNode s u)
}

--Theory solving
data TheorySolver sp lp s u o = TheorySolver {
    unsatCoreState      :: [(sp, Bool)] -> Maybe [(sp, Bool)],
    unsatCoreStateLabel :: [(sp, Bool)] -> [(lp, Bool)] -> Maybe ([(sp, Bool)], [(lp, Bool)]),
    eQuant              :: [(sp, Bool)] -> [(lp, Bool)] -> Ops s u -> StateT pdb (ST s) (DDNode s u)
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

cPre' :: Ops s u -> RefineDynamic s u o sp lp -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cPre' Ops{..} RefineDynamic{..} hasOutgoings target = do
    t0 <- mapVars target
    t1 <- liftM bnot $ andAbstract (cube next) trans (bnot t0)
    deref t0
    t2 <- hasOutgoings .& t1
    deref t1
    t3 <- consistentMinusCUL .& t2
    deref t2
    t4 <- bexists (cube label) t3
    deref t3
    t5 <- consistentPlusCU .-> t4
    deref t4
    return t5

cPre :: Ops s u -> RefineDynamic s u o sp lp -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cPre (ops @ (Ops {..})) (rd @ (RefineDynamic {..})) hasOutgoings target = do
    su <- cPre' ops rd hasOutgoings target
    t6 <- bforall (cube untrackedState) su
    deref su
    return t6

fixedPoint :: Ops s u -> (DDNode s u -> ST s (DDNode s u)) -> DDNode s u -> ST s (DDNode s u)
fixedPoint (ops @ Ops {..}) func start = do
    res <- func start
    deref start 
    case (res==start) of --this is safe 
        True -> return start
        False -> fixedPoint ops func res
        
solveGame :: Ops s u -> RefineStatic s u -> RefineDynamic s u o sp lp -> DDNode s u -> ST s (DDNode s u)
solveGame (ops@Ops{..}) (rs @ RefineStatic{..}) (rd @ RefineDynamic{..}) target = do 
    hasOutgoings <- bexists (cube next) trans
    fp <- fixedPoint ops (func hasOutgoings) target
    deref hasOutgoings
    return fp
    where
    func hasOutgoings target = do
        traceST "solveGame: iteration"
        t1 <- target .| goal
        res <- cPre ops rd hasOutgoings t1
        deref t1
        return res

-- ===Abstraction refinement===

--check msg ops = unsafeIOToST (putStrLn ("checking bdd consistency" ++ msg)) >> debugCheck ops >> checkKeys ops
check msg ops = return ()

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

refineAny :: Ops s u -> RefineDynamic s u o sp lp -> DDNode s u -> ST s (Maybe [Int])
refineAny Ops{..} RefineDynamic{..} newSU = do
    si <- supportIndices newSU
    let ui = si `intersect` untrackedInds
    return $ case ui of
        []  -> Nothing
        x:_ -> Just [x]

refineFirstPrime :: Ops s u -> RefineDynamic s u o sp lp -> DDNode s u -> ST s (Maybe [Int])
refineFirstPrime Ops{..} RefineDynamic{..} newSU = do
    (lc, sz) <- largestCube newSU
    prime    <- makePrime lc newSU
    deref lc
    si       <- supportIndices prime
    deref prime
    let ui = si `intersect` untrackedInds
    return $ case ui of
        [] -> Nothing
        x  -> Just x

--Refine the least number of untracked state predicates possible to make progress
refineLeastPreds :: forall s u o sp lp. Ops s u -> RefineDynamic s u o sp lp -> DDNode s u -> ST s (Maybe [Int])
refineLeastPreds ops@Ops{..} RefineDynamic{..} newSU 
    | newSU == bfalse = return Nothing
    | otherwise       = do
        ref newSU
        (size, vars, remaining) <- sizeVarsNext newSU
        (size, vars) <- doLoop size vars remaining
        check "after doLoop" ops
        return $ Just vars
    where
    sizeVarsNext :: DDNode s u -> ST s (Int, [Int], DDNode s u)
    sizeVarsNext remaining = do
        check "before sizeVarsNext" ops
        (lc, sz) <- largestCube remaining
        prime <- makePrime lc newSU
        deref lc
        (size, vars) <- analyseCube prime
        nextRemaining <- band remaining $ bnot prime
        deref remaining
        deref prime
        check "after sizeVarsNext" ops
        return (size, vars, nextRemaining)
    doLoop :: Int -> [Int] -> DDNode s u -> ST s (Int, [Int])
    doLoop size vars remaining 
        | remaining == bfalse = return (size, vars)
        | otherwise           = do
            (size', vars', remaining') <- sizeVarsNext remaining
            if (size' < size) then doLoop size' vars' remaining' else doLoop size vars remaining'
    analyseCube :: DDNode s u -> ST s (Int, [Int])
    analyseCube cube' = do
        check "before analyseCube" ops
        untrackedCube <- bexists trackedCube cube'
        support <- supportIndices untrackedCube
        deref untrackedCube
        check "after analyseCube" ops
        return (length support, support)

pickUntrackedToPromote :: Ops s u -> RefineDynamic s u o sp lp -> RefineStatic s u -> DDNode s u -> ST s (Maybe [Int])
pickUntrackedToPromote ops@Ops{..} rd@RefineDynamic{..} RefineStatic{..} win = do
    traceST "Picking untracked to promote"
    hasOutgoings <- bexists (cube next) trans
    win' <- win .| goal
    su    <- cPre' ops rd hasOutgoings win'
    deref hasOutgoings
    newSU <- su .& bnot win
    deref win'
    deref su
    check "before refineLeastPreds" ops
    res <- refineStrategy ops rd newSU
    check "after refineLeastPreds" ops
    deref newSU
    return res

--Create an initial abstraction and set up the data structures
initialAbstraction :: (Show sp, Show lp, Ord sp, Ord lp) => Ops s u -> Abstractor s u o sp lp -> o -> StateT (DB s u sp lp) (ST s) (RefineDynamic s u, RefineStatic s u)
initialAbstraction ops@Ops{..} Abstractor{..} abstractorState = do
    check "InitialAbstraction start" ops
    --abstract init
    initExpr <- doInit ops initAbs
    check "After compiling init" ops
    --abstract the goal
    DoGoalRet{..} <- doGoal ops goalAbs
    check "After compiling goal" ops
    --get the abstract update functions for the goal predicates and variables
    updateExprConj' <- doUpdate ops updateAbs goalNextPredicates goalNextVariables
    updateExprConj  <- doEnVars ops updateExprConj' $ map (fst *** fst) $ Map.elems labelPreds
    deref updateExprConj'
    --create the consistency constraints
    let consistentPlusCU   = btrue
        consistentPlusCUL  = btrue
    ref consistentPlusCU
    ref consistentPlusCUL
    consistentMinusCUL <- conj ops $ map (bnot . fst . snd) $ Map.elems labelPreds
    --construct the RefineDynamic and RefineStatic
    let rd = RefineDynamic {
            trans           = updateExprConj,
            ...
        }
        rs = RefineStatic {
            goal = goalExpr,
            init = initExpr
        }
    return (rd, rs)

--Promote untracked state variables to full state variables so that we can make progress towards the goal. Does not refine the consistency relations.
promoteUntracked :: (Ord lp, Ord sp, Show sp, Show lp) => Ops s u -> Abstractor s u o sp lp -> RefineDynamic s u o sp lp -> [Int] -> StateT (DB s u sp lp) (ST s) (RefineDynamic s u)
promoteUntracked ops@Ops{..} Abstractor{..} rd@RefineDynamic{..} indices = do
    --look up the predicates to promote
    let refineVars    = nub $ map (fromJustNote "promoteUntracked: untracked indices not in stateRev" . flip Map.lookup stateRev) indices
    traceST $ "Promoting: " ++ show refineVars

    let (toPromotePreds', toPromoteVars') = partitionEithers $ map func refineVars
            where
            func (Predicate p v) = Left  (p, v)
            func (NonAbs n v)    = Right (n, v)

    (toPromotePreds, toPromoteVars) <- promote toPromotePreds' toPromoteVars'

    --compute the update functions
    updateExprConj'  <- doUpdate ops updateAbs toPromotePreds toPromoteVars

    updateExprConj  <- doEnVars ops updateExprConj' $ map (fst *** fst) $ Map.elems labelPreds
    deref updateExprConj'

    --update the transition relation
    trans'             <- trans .& updateExprConj
    deref updateExprConj
    deref trans

    consistentMinusCUL'' <- conj ops $ map (bnot . fst . snd) $ Map.elems $ updateLabelPreds Map.\\ labelPreds
    consistentMinusCUL'  <- consistentMinusCUL .& consistentMinusCUL''
    deref consistentMinusCUL''
    deref consistentMinusCUL

    let rd = RefineDynamic {
        trans              = trans',
        consistentPlusCU   = consistentPlusCU,
        consistentMinusCUL = consistentMinusCUL',
        consistentPlusCUL  = consistentPlusCUL,
    }

    return rd

getPredicates :: [(Variable p s u, a)] -> [(p, a)]
getPredicates = mapMaybe func 
    where
    func (Predicate p _, x) = Just (p, x)
    func _                  = Nothing

--Refine one of the consistency relations so that we make progress. Does not promote untracked state.
refineConsistency :: (Ord sp, Ord lp, Show sp, Show lp) => Ops s u -> TheorySolver sp lp s u o -> RefineDynamic s u o sp lp -> RefineStatic s u -> DDNode s u -> ST s (Maybe (RefineDynamic s u o sp lp))
refineConsistency ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} win = do
    win' <- win .| goal
    t0 <- mapVars win'
    t2 <- liftM bnot $ andAbstract (cube next) trans (bnot t0)
    deref t0
    t3 <- consistentPlusCUL .& t2
    deref t2
    hasOutgoings <- bexists (cube next) trans
    tt3 <- hasOutgoings .& t3
    --deref hasOutgoings
    deref t3
    t4 <- tt3 .& bnot win
    --Alive : win', hasOutgoings, tt3, t4
    case t4==bfalse of 
        True  -> do
            --no refinement of consistency relations will make progress
            --there are no <c, u, l> tuples that are winning with the overapproximation of consistentCUL
            traceST "no consistency refinement possible"
            mapM deref [win', hasOutgoings, tt3, t4]
            return Nothing
        False -> do
            --There may be a refinement
            --extract a <s, u> pair that will make progress if one exists
            t5 <- bexists (cube label) t4
            deref t4
            (t6, sz) <- largestCube t5
            t7 <- makePrime t6 t5
            deref t5
            deref t6
            c <- presentVars ops t7 
            deref t7
            let stateUntrackedProgress = map (first $ fromJustNote "refineConsistency1" . flip Map.lookup stateRev) c
            traceST $ "Tuple that will make progress: " ++ show stateUntrackedProgress
            let preds = getPredicates stateUntrackedProgress
            traceST $ "Preds being checked for consistency: " ++ show preds
            check "refineConsistency end2" ops
            --Alive : win', hasOutgoings, tt3 
            case unsatCoreState preds of
                Just pairs -> do
                    --consistentPlusCU can be refined
                    traceST "refining consistentPlusCU"
                    mapM deref [win', hasOutgoings, tt3]
                    inconsistent <- makeCube ops $ map (first (node . fromJustNote "refineConsistency" . flip Map.lookup statePreds)) pairs
                    consistentPlusCU'  <- consistentPlusCU .& bnot inconsistent
                    deref consistentPlusCU
                    consistentPlusCUL' <- consistentPlusCUL .& bnot inconsistent
                    deref consistentPlusCUL'
                    deref inconsistent
                    check "refineConsistency2" ops
                    return $ Just $ rd {consistentPlusCU = consistentPlusCU', consistentPlusCUL = consistentPlusCUL'}
                Nothing -> do
                    traceST "consistentPlusCU could not be refined"
                    --consistentPlusCU cannot be refined but maybe consistentPlusCUL or consistentMinusCUL can be
                    cpr <- cPre' ops rd hasOutgoings win'
                    mapM deref [win', hasOutgoings]
                    t4 <- tt3 .& bnot cpr
                    mapM deref [tt3, cpr]
                    --Alive :t4
                    case t4==bfalse of
                        True -> do
                            traceST "consistentPlusCUL could not be refined"
                            deref t4
                            check "refineConsistency3" ops
                            return Nothing
                        False -> do
                            check "refineConsistency start3" ops
                            (t6, sz) <- largestCube t4
                            t7 <- makePrime t6 t4
                            deref t4
                            deref t6
                            c <- presentVars ops t7
                            deref t7
                            let (stateIndices, labelIndices) = partition (\(p, x) -> elem p (inds trackedState) || elem p (inds untrackedState)) c
                            let cStatePreds = getPredicates $ map (first $ fromJustNote "refineConsistency2" . flip Map.lookup stateRev) stateIndices
                            let cLabelPreds = getPredicates $ catMaybes $ map (uncurry func) labelIndices
                                    where
                                    func idx polarity = case fromJustNote "refineConsistency3" $ Map.lookup idx labelRev of
                                        (_, False)   -> Nothing
                                        (pred, True) -> Just (pred, polarity)
                            traceST $ "label preds for solver: " ++ show cLabelPreds
                            check "refineConsistency end3" ops
                            --Alive : nothing
                            case unsatCoreStateLabel cStatePreds cLabelPreds of
                                Just (statePairs, labelPairs) -> do
                                    --consistentPlusCUL can be refined
                                    traceST "refining consistentPlusCUL"
                                    inconsistentState <- makeCube ops $ map (first (node . fromJustNote "refineConsistency" . flip Map.lookup statePreds)) statePairs
                                    inconsistentLabel <- makeCube ops $ map (first (node . sel1 . fromJustNote "refineConsistency" . flip Map.lookup labelPreds)) labelPairs
                                    inconsistent <- inconsistentState .& inconsistentLabel
                                    deref inconsistentState
                                    deref inconsistentLabel
                                    consistentPlusCUL' <- consistentPlusCUL .& bnot inconsistent
                                    deref inconsistent
                                    deref consistentPlusCUL
                                    check "refineConsistency4" ops
                                    refineConsistency ops ts (rd {consistentPlusCUL = consistentPlusCUL'}) rs win
                                Nothing -> do
                                    --the (s, u, l) tuple is consistent so add this to consistentMinusCUL
                                    traceST "predicates are consistent. refining consistentMinusCUL..."
                                    eQuantExpr <- doEQuant eQuant cStatePreds cLabelPreds ops initPreds 

                                    let statePreds' = map (first $ fst . fromJustNote "refineConsistency" . flip Map.lookup statePreds) cStatePreds
                                        labelPreds' = map (first $ fromJustNote "refineConsistency" . flip Map.lookup labelPreds) cLabelPreds

                                    --stateCube <- uncurry computeCube $ unzip statePreds'
                                    let func ((lp, le), pol) = [(fst lp, pol), (fst le, True)]
                                    labelCube <- uncurry computeCube $ unzip $ concatMap func labelPreds'

                                    --consistentCube' <- stateCube .& labelCube
                                    consistentCube  <- labelCube .& equantExpr
                                    mapM deref [labelCube, equantExpr]

                                    consistentMinusCUL'  <- consistentMinusCUL .| consistentCube
                                    deref consistentCube
                                    deref consistentMinusCUL

                                    let newUntracked = Map.elems (equantStatePreds Map.\\ statePreds) ++ concat (Map.elems (equantStateVars Map.\\ stateVars))
                                    untrackedState' <- addVariables ops newUntracked untrackedState

                                    let statePredsRev  = constructStatePredRev $ Map.toList equantStatePreds
                                        stateVarsRev   = constructStateVarRev  $ Map.toList equantStateVars
                                        stateRev'      = Map.union statePredsRev stateVarsRev
                        
                                    return $ Just $ rd {
                                        consistentMinusCUL = consistentMinusCUL', 
                                        untrackedState     = untrackedState',
                                        nextAvlIndex       = equantEnd,
                                        stateRev           = stateRev',
                                        statePreds         = equantStatePreds,
                                        stateVars          = equantStateVars,
                                        abstractorState    = equantAbsState
                                    }

--The abstraction-refinement loop
absRefineLoop :: forall s u o sp lp. (Ord sp, Ord lp, Show sp, Show lp) => STDdManager s u -> Abstractor s u o sp lp -> TheorySolver sp lp s u o -> o -> ST s Bool
absRefineLoop m spec ts abstractorState = do
    let ops@Ops{..} = constructOps m
    (rd, rs) <- initialAbstraction ops spec abstractorState
    traceST "Refinement state after initial abstraction: " 
    traceST $ "Goal is: " ++ (bddSynopsis ops $ goal rs)
    traceST $ "Init is: " ++ (bddSynopsis ops $ Refine.init rs)
    refineLoop ops rs rd bfalse
    where
        refineLoop :: Ops s u -> RefineStatic s u -> RefineDynamic s u o sp lp -> DDNode s u -> ST s Bool
        refineLoop ops@Ops{..} rs@RefineStatic{..} = refineLoop'
            where 
            refineLoop' rd@RefineDynamic{..} lastWin = do
                setVarMap (vars trackedState) (vars next) 
                winRegion <- solveGame ops rs rd lastWin
                deref lastWin
                winning   <- init `leq` winRegion 
                --Alive: winRegion, rd, rs
                case winning of
                    True -> do
                        traceST "Winning"
                        deref winRegion
                        return True
                    False -> do
                        traceST "Not winning without further refinement"
                        res <- refineConsistency ops ts rd rs winRegion 
                        case res of
                            Just newRD -> do
                                traceST "Refined consistency relations. Re-solving..."
                                refineLoop' newRD winRegion
                            Nothing -> do
                                traceST "Could not refine consistency relations. Attempting to refine untracked state variables"
                                res <- pickUntrackedToPromote ops rd rs winRegion
                                case res of 
                                    Just vars -> do
                                        traceST "Found untracked variables to promote. Promoting them..."
                                        newRD <- promoteUntracked ops spec rd vars 
                                        refineLoop' newRD winRegion
                                    Nothing -> do
                                        traceST "Game is not winning"
                                        deref winRegion
                                        return False

