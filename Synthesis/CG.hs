{-# LANGUAGE RecordWildCards, TemplateHaskell, FlexibleContexts, DeriveFunctor, ConstraintKinds #-}

module Synthesis.CG (
    IteratorM(..),
    SynthData(..),
    availableLabels,
    pickLabel,
    pickLabel2,
    enumerateEquivalentLabels,
    ifCondition,
    applyLabel,
    applyUncontrollableTC
    ) where

import Control.Monad.Trans
import Control.Monad
import Control.Monad.ST
import Control.Arrow
import Data.Tuple.All
import qualified Data.Map as Map

import Util
import Synthesis.Resource
import Synthesis.BddRecord
import Synthesis.Interface
import Synthesis.BddUtil
import Synthesis.TermiteGame
import Synthesis.RefineCommon hiding (fixedPoint)

faXnor :: (RM s u t) => Ops s u -> DDNode s u -> DDNode s u -> DDNode s u -> t (ST s) (DDNode s u)
faXnor Ops{..} cube x y = liftM bnot $ $r2 (xorExistAbstract cube) x y

{-
- We use an iterator for functions that return many BDDs. This allows us to:
- * Not generate the next BDD until it is needed in the calling code. This
-   prevents BDDs from being generated that arent actually needed and
-   minimizes live BDDs
- * Move the BDD deallocation code to this file, where the BDDs are
-   created. This is not actually implemented.
-}

data IteratorM m a = 
      Empty
    | Item  a (m (IteratorM m a))
    deriving (Functor)

iMapM :: Monad m => (a -> m b) -> IteratorM m a -> m (IteratorM m b)
iMapM func Empty      = return Empty
iMapM func (Item x r) = do
    this <- func x
    rest <- r
    return $ Item this $ iMapM func rest

iFoldM :: Monad m => (accum -> item -> m accum) -> accum -> IteratorM m item -> m accum
iFoldM func accum Empty      = return accum
iFoldM func accum (Item x r) = do
    accum' <- func accum x
    r <- r
    iFoldM func accum' r

genPair :: (RM s u t) => Ops s u -> DDNode s u -> DDNode s u -> DDNode s u -> t (ST s) (Maybe (DDNode s u, DDNode s u))
genPair ops@Ops{..} x y rel = case rel == bfalse of
    True  -> return Nothing
    False -> do
        xOnly         <- $r1 (bexists y) rel
        xMinterm      <- $r1 (largePrime ops) xOnly
        $d deref xOnly

        concXSupport  <- $r1 support xMinterm
        remainingVars <- $r $ bexists concXSupport x
        $d deref concXSupport
        concX         <- $r2 band remainingVars xMinterm
        $d deref xMinterm
        $d deref remainingVars

        img           <- $r2 (andAbstract x) rel concX
        $d deref concX
        genX          <- faXnor ops y rel img
        return $ Just (genX, img)

enumerate :: (RM s u t) => Ops s u -> DDNode s u -> DDNode s u -> DDNode s u -> t (ST s) (IteratorM (t (ST s)) (DDNode s u, DDNode s u))
enumerate ops@Ops{..} x y rel = do
    $rp ref rel
    enumerate' rel
    where 
    enumerate' rel = do
        pair <- genPair ops x y rel 
        case pair of
            Nothing               -> $d deref rel >> return Empty
            Just (pair@(genX, _)) -> do
                restricted <- $r2 band rel (bnot genX)
                $d deref rel
                return $ Item pair (enumerate' restricted)

data SynthData s u = SynthData {
    sections     :: SectionInfo s u,
    transitions  :: [(DDNode s u, DDNode s u)],
    cont         :: DDNode s u,
    rd           :: RefineDynamic s u,
    lp           :: Lab s u
}

enumerateEquivalentLabels :: (RM s u t) => Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> t (ST s) (IteratorM (t (ST s)) (DDNode s u))
enumerateEquivalentLabels ops@Ops{..} SynthData{sections = SectionInfo{..}, ..} stateSet label = do
    rel   <- $r $ conj ops (map snd transitions ++ [stateSet, label])
    yVars <- $r $ conj ops [_trackedCube, _untrackedCube, _nextCube]
    res   <- enumerate ops _labelCube yVars rel
    $d deref rel
    $d deref yVars
    iMapM func res
    where func (label, nextState) = do
            $d deref nextState
            return label

--Given a state and a strategy, create an iterator that lists pairs of (label, condition over state variables for this label to be available)
availableLabels :: (RM s u t) => Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> t (ST s) (IteratorM (t (ST s)) (DDNode s u, DDNode s u))
availableLabels ops@Ops{..} sd@SynthData{sections = SectionInfo{..}, ..} strategy stateSet = do
    yVars            <- $r $ conj ops [_trackedCube, _untrackedCube, _nextCube]
    avlWinningLabels <- $r3 andAbstract yVars strategy stateSet
    rel              <- $r $ conj ops (map snd transitions ++ [stateSet, avlWinningLabels])
    $d deref avlWinningLabels
    res              <- enumerate ops _labelCube yVars rel
    $d deref yVars
    $d deref rel
    iMapM func res
    where 
    func (label, nextState) = do
        $d deref nextState
        cond <- condFunc ops (Synthesis.CG.sections sd) stateSet strategy label
        return (label, cond)

condFunc :: (RM s u t) => Ops s u -> SectionInfo s u -> DDNode s u -> DDNode s u -> DDNode s u -> t (ST s) (DDNode s u)
condFunc Ops{..} SectionInfo{..} stateSet strategy label = do
    avlStates <- $r2 (andAbstract _labelCube) strategy label
    cond      <- $r2 liCompact avlStates stateSet
    return cond

condFuncRemove :: (RM s u t) => Ops s u -> SectionInfo s u -> DDNode s u -> DDNode s u -> DDNode s u -> DDNode s u -> t (ST s) (Maybe (DDNode s u))
condFuncRemove Ops{..} SectionInfo{..} strategy stateSet label removeCube = do

    --Figure out for which states the label is part of the strategy. This may include states not in stateSet
    avlStates  <- $r2 (andAbstract _labelCube) strategy label

    --Combine this with the state set to get the subset of 'stateSet' from which we may play this label
    avlAndSet  <- $r2 band avlStates stateSet
    
    --Remove the variables we dont want. This will possibly grow the set.
    noUnwanted <- $r1 (bexists removeCube) avlAndSet

    --Compute a small condition to ensure we are in this set when we are in stateSet
    cond       <- $r2 liCompact noUnwanted stateSet

    --Check that this still gives us the set we want
    condAndSet <- $r2 band cond stateSet
    if condAndSet == avlAndSet 
        then return $ Just cond
        else return Nothing

--Pick any winning label 
--The returned label is part of the strategy for every state and consistent substate in the stateSet argument
pickLabel :: (RM s u t) => Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> t (ST s) (Maybe (DDNode s u))
pickLabel Ops{..} SynthData{rd = RefineDynamic{..}, ..} strategy stateSet = do
    let SectionInfo{..} = sections
    cube <- $r $ band _trackedCube _untrackedCube
    x    <- $r2 bor (bnot stateSet) strategy
    cons <- $r1 (bexists _labelCube) consistentPlusCULCont
    act  <- liftM bnot $ $r3 andAbstract cube cons (bnot x)
    $d deref cube
    $d deref x
    $d deref cons
    case act == bfalse of
        True  -> return Nothing
        False -> return $ Just act

foldMF init list func = foldM func init list

--The list of DDNodes is the set of winning regions at each distance from the goal. They are inclusive.
--The head of the list is the furthest from the goal. The sets monotonically shrink.
--assumes stateSet is not entirely contained within the goal
pickLabel2 :: (RM s u t) => Ops s u -> SynthData s u -> [DDNode s u] -> DDNode s u -> DDNode s u -> DDNode s u -> t (ST s) (Maybe (DDNode s u, DDNode s u))
pickLabel2 ops@Ops{..} SynthData{..} regions goal strategy stateSet = do
    let findSets (x:y:rest) = do
            res <- lift $ stateSet `leq` y
            case res of
                True  -> return (y, x)
                False -> findSets (y : rest)
        findSets _          = error "findSets - pickLabel2"

    (furthestSet, nextFurthestSet) <- findSets (goal : reverse regions)

    stateUntrackedCube       <- $r $ band (_trackedCube sections) (_untrackedCube sections)
    consCU                   <- $r1 (bexists $ _labelCube sections) (consistentPlusCULCont rd)
    consC                    <- $r1 (bexists $ _untrackedCube sections) consCU
    consistentStateUntracked <- $r2 band stateSet consCU
    --This includes all states at smaller distances as well. Compute the labels that take us into that set.
    --Assumes hasOutgoings is btrue
    $rp ref btrue
    stateLabelsNotBackwards' <- cpreCont' ops sections rd lp cont furthestSet
    $d deref btrue
    stateLabelsNotBackwards  <- $r2 band (consistentMinusCULCont rd) stateLabelsNotBackwards'
    $d deref stateLabelsNotBackwards'
    labelsNotBackwards      <- $r2 (faImp ops stateUntrackedCube) consistentStateUntracked stateLabelsNotBackwards
    $d deref consistentStateUntracked
    $d deref stateUntrackedCube
    $d deref stateLabelsNotBackwards

    --Compute the set of strategy labels available in at least one entire superstate in stateSet at the maximum distance
    --TODO: Maybe this could be made more liberal by considering labels from some untracked partition (not all)
    atMaxDist         <- $r2 band stateSet (bnot nextFurthestSet)
    stratAndState     <- $r2 band atMaxDist strategy
    labelsSomewhere'  <- $r2 (faImp ops (_untrackedCube sections)) consCU stratAndState
    $d deref consCU
    labelsSomewhere'' <- $r2 band labelsSomewhere' consC
    $d deref consC
    $d deref labelsSomewhere'
    --TODO should check that the tracked cube has a consistent substate
    labelsSomewhere   <- $r1 (bexists $ _trackedCube sections) labelsSomewhere''
    $d deref labelsSomewhere''
    $d deref atMaxDist
    $d deref stratAndState
    
    --Conjunct these
    result <- $r2 band labelsSomewhere labelsNotBackwards
    $d deref labelsSomewhere
    $d deref labelsNotBackwards
    outerRegion <- $r2 band furthestSet (bnot nextFurthestSet)
    case result == bfalse of
        True  -> return Nothing
        False -> return $ Just (result, outerRegion)

--Generate a bdd X over state variables such that (state & X) has some label available from all of it
ifCondition :: (RM s u t) => Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> t (ST s) (Maybe (DDNode s u))
ifCondition ops@Ops{..} sd@SynthData{sections = SectionInfo{..}, ..} strategy stateSet = do
    labelIterator <- availableLabels ops sd strategy stateSet
    case labelIterator of
        Empty                -> return Nothing
        Item (label, cond) r -> do
            $d deref label
            s <- lift $ dagSize cond
            r <- r
            res <- iFoldM func (cond, s) r
            return $ Just $ fst res
    where
    func accum@(bestCond, bestSize) (label, cond) = do
        $d deref label
        res <- lift $ dagSize cond
        case res < bestSize of 
            True  -> $d deref bestCond >> return (cond, res)
            False -> $d deref cond     >> return accum

fixedPoint :: (RM s u t) => Ops s u -> DDNode s u -> (DDNode s u -> t (ST s) (DDNode s u)) -> t (ST s) (DDNode s u)
fixedPoint ops@Ops{..} start func = do
    res <- func start
    $d deref start
    case (res == start) of
        True  -> return res
        False -> fixedPoint ops res func

forLoop start list func  = foldM func start list

applyTrel :: (RM s u t) => Ops s u -> SynthData s u -> [(DDNode s u, DDNode s u)] -> DDNode s u -> DDNode s u -> t (ST s) (DDNode s u)
applyTrel Ops{..} SynthData{..} trel constraint stateSet = do
    let SectionInfo{..} = sections

    $rp ref btrue
    combined <- forLoop btrue trel $ \accum (cube, trel) -> do
        constrainedTrel <- $r2 band trel constraint
        constrained     <- $r2 band constrainedTrel stateSet
        $d deref constrainedTrel
        accum'          <- $r2 band constrained accum
        $d deref constrained
        $d deref accum
        return accum'

    combconsistent <- $r2 band combined (consistentPlusCULCont rd)
    $d deref combined

    sul' <- $r $ band _trackedCube _untrackedCube
    sul  <- $r1 (band _labelCube) sul'
    $d deref sul'

    res' <- $r2 bexists sul combconsistent
    $d deref combconsistent
    $d deref sul

    res <- $r1 mapVars res'
    $d deref res'

    return res

applyUncontrollableTC :: (RM s u t) => Ops s u -> SynthData s u -> DDNode s u -> t (ST s) (DDNode s u)
applyUncontrollableTC ops@Ops{..} sd@SynthData{..} stateSet = do
    $rp ref stateSet
    fixedPoint ops stateSet $ \set -> do
        res      <- applyTrel ops sd transitions (bnot cont) set
        combined <- $r2 bor res stateSet
        $d deref res
        return combined

--Given a label and a state, apply the label and then the transitive closure of uncontrollable transitions to compute the set of possible next states
applyLabel :: (RM s u t) => Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> t (ST s) (DDNode s u)
applyLabel ops@Ops{..} sd@SynthData{..} stateSet label = do
    $rp ref btrue
    afterControllableAction    <- applyTrel ops sd transitions btrue stateSet
    afterUncontrollableActions <- applyUncontrollableTC ops sd afterControllableAction
    $d deref afterControllableAction
    return afterUncontrollableActions

