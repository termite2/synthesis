{-# LANGUAGE RecordWildCards, TemplateHaskell #-}

module CG (
    SynthData(..),
    availableLabels,
    pickLabel,
    pickLabel2,
    ifCondition,
    applyLabel,
    applyUncontrollableTC
    ) where

import Control.Monad
import Control.Monad.ST
import Control.Arrow
import Data.Tuple.All
import qualified Data.Map as Map
import Control.Monad.Trans.Identity

import BddRecord
import Interface
import BddUtil
import TermiteGame

faXnor :: Ops s u -> DDNode s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
faXnor Ops{..} cube x y = liftM bnot $ xorExistAbstract cube x y

faImp :: Ops s u -> DDNode s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
faImp Ops{..} cube x y = liftM bnot $ andAbstract cube x (bnot y)

data IteratorM m a = 
      Empty
    | Item  a (m (IteratorM m a))

instance Functor m => Functor (IteratorM m) where
    fmap _ Empty      = Empty
    fmap f (Item x r) = Item (f x) $ fmap (fmap f) r

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

genPair :: Ops s u -> DDNode s u -> DDNode s u -> DDNode s u -> ST s (Maybe (DDNode s u, DDNode s u))
genPair ops@Ops{..} x y rel = case rel == bfalse of
    True  -> return Nothing
    False -> do
        xOnly         <- bexists y rel
        xMinterm      <- largePrime ops xOnly

        concXSupport  <- support xMinterm
        remainingVars <- bexists concXSupport x
        concX         <- band remainingVars xMinterm

        img           <- andAbstract x rel concX
        genX          <- faXnor ops y rel img
        return $ Just (genX, img)

enumerate :: Ops s u -> DDNode s u -> DDNode s u -> DDNode s u -> ST s (IteratorM (ST s) (DDNode s u, DDNode s u))
enumerate ops@Ops{..} x y rel = do
    pair <- genPair ops x y rel 
    case pair of
        Nothing               -> return Empty
        Just (pair@(genX, _)) -> do
            restricted <- band rel (bnot genX)
            return $ Item pair (enumerate ops x y restricted)

data SynthData s u = SynthData {
    sections     :: SectionInfo s u,
    transitions  :: [(DDNode s u, DDNode s u)],
    cont         :: DDNode s u,
    rd           :: RefineDynamic s u,
    lp           :: Lab s u
}

enumerateEquivalentLabels :: Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> ST s (IteratorM (ST s) (DDNode s u))
enumerateEquivalentLabels ops@Ops{..} SynthData{sections = SectionInfo{..}, ..} stateSet label = do
    rel   <- conj ops (map snd transitions ++ [stateSet, label])
    yVars <- conj ops [_trackedCube, _untrackedCube, _nextCube]
    res   <- enumerate ops _labelCube yVars rel
    iMapM func res
    where func (label, nextState) = do
            deref nextState
            return label

--Given a state and a strategy, create an iterator that lists pairs of (label, condition over state variables for this label to be available)
availableLabels :: Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> ST s (IteratorM (ST s) (DDNode s u, DDNode s u))
availableLabels ops@Ops{..} SynthData{sections = SectionInfo{..}, ..} strategy stateSet = do
    yVars            <- conj ops [_trackedCube, _untrackedCube, _nextCube]
    avlWinningLabels <- andAbstract yVars strategy stateSet
    rel              <- conj ops (map snd transitions ++ [stateSet, avlWinningLabels])
    res              <- enumerate ops _labelCube yVars rel
    iMapM func res
    where func (label, nextState) = do
            deref nextState
            avlStates <- andAbstract _labelCube strategy label 
            cond      <- liCompact avlStates stateSet
            return (label, cond)

--Pick any winning label 
--The returned label is part of the strategy for every state and consistent substate in the stateSet argument
pickLabel :: Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> ST s (Maybe (DDNode s u))
pickLabel Ops{..} SynthData{rd = RefineDynamic{..}, ..} strategy stateSet = do
    let SectionInfo{..} = sections
    cube <- band _trackedCube _untrackedCube
    x    <- bor (bnot stateSet) strategy
    cons <- bexists _labelCube consistentPlusCULCont
    act  <- liftM bnot $ andAbstract cube cons (bnot x)
    case act == bfalse of
        True  -> return Nothing
        False -> return $ Just act

foldMF init list func = foldM func init list

--The list of DDNodes is the set of winning regions at each distance from the goal. They are inclusive.
--The head of the list is the furthest from the goal. The sets monotonically shrink.
--assumes stateSet is not entirely contained within the goal
pickLabel2 :: Ops s u -> SynthData s u -> [DDNode s u] -> DDNode s u -> DDNode s u -> DDNode s u -> ST s (Maybe (DDNode s u))
pickLabel2 ops@Ops{..} SynthData{..} regions goal strategy stateSet = do

    let findSets (x:y:rest) = do
            res <- stateSet `leq` y
            case res of
                True  -> return (y, x)
                False -> findSets (y : rest)
        findSets []         = error "findSets - pickLabel2"

    (furthestSet, nextFurthestSet) <- findSets (goal : reverse regions)

    stateUntrackedCube       <- band (_trackedCube sections) (_untrackedCube sections)
    consCU                   <- bexists (_labelCube sections) (consistentPlusCULCont rd)
    consistentStateUntracked <- band stateSet consCU
    
    --This includes all states at smaller distances as well. Compute the labels that take us into that set.
    --Assumes hasOutgoings is btrue
    ref btrue
    stateLabelsNotBackwards <- runIdentityT $ cpreCont' ops sections rd lp cont btrue furthestSet
    labelsNotBackwards      <- faImp ops stateUntrackedCube consistentStateUntracked stateLabelsNotBackwards
    
    --Compute the set of strategy labels available in at least one entire superstate in stateSet at the maximum distance
    --TODO: Maybe this could be made more liberal by considering labels from some untracked partition (not all)
    atMaxDist        <- band stateSet (bnot nextFurthestSet)
    stratAndState    <- band atMaxDist strategy
    labelsSomewhere' <- faImp ops (_untrackedCube sections) consCU stratAndState
    --TODO should check that the tracked cube has a consistent substate
    labelsSomewhere  <- bexists (_trackedCube sections) labelsSomewhere'
    deref atMaxDist
    deref stratAndState
    
    --Conjunct these
    result <- band labelsSomewhere labelsNotBackwards
    deref labelsSomewhere
    deref labelsNotBackwards

    case result == bfalse of
        True  -> return Nothing
        False -> return $ Just result

--Generate a bdd X over state variables such that (state & X) has some label available from all of it
ifCondition :: Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> ST s (Maybe (DDNode s u))
ifCondition ops@Ops{..} sd@SynthData{sections = SectionInfo{..}, ..} strategy stateSet = do
    labelIterator <- availableLabels ops sd strategy stateSet
    case labelIterator of
        Empty                -> return Nothing
        Item (label, cond) r -> do
            s <- dagSize cond
            r <- r
            res <- iFoldM func (cond, s) r
            return $ Just $ fst res
    where
    func accum@(bestCond, bestSize) (label, cond) = do
        res <- dagSize cond
        case res < bestSize of 
            True  -> return (cond, res)
            False -> return accum

fixedPoint :: Ops s u -> DDNode s u -> (DDNode s u -> ST s (DDNode s u)) -> ST s (DDNode s u)
fixedPoint ops@Ops{..} start func = do
    res <- func start
    deref start
    case (res == start) of
        True  -> return res
        False -> fixedPoint ops res func

forLoop start list func  = foldM func start list

applyTrel :: Ops s u -> SynthData s u -> [(DDNode s u, DDNode s u)] -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
applyTrel Ops{..} SynthData{..} trel constraint stateSet = do
    let SectionInfo{..} = sections

    ref btrue
    combined <- forLoop btrue trel $ \accum (cube, trel) -> do
        constrainedTrel <- band trel constraint
        constrained     <- band constrainedTrel stateSet
        deref constrainedTrel
        accum'          <- band constrained accum
        deref constrained
        deref accum
        return accum'

    sul' <- band _trackedCube _untrackedCube
    sul  <- band sul' _labelCube
    deref sul'

    res <- bexists sul combined
    deref sul
    deref combined

    res <- mapVars res

    return res

applyUncontrollableTC :: Ops s u -> SynthData s u -> DDNode s u -> ST s (DDNode s u)
applyUncontrollableTC ops@Ops{..} sd@SynthData{..} stateSet = do
    ref stateSet
    fixedPoint ops stateSet $ \set -> do
        res      <- applyTrel ops sd transitions (bnot cont) set
        combined <- bor res stateSet
        return combined

--Given a label and a state, apply the label and then the transitive closure of uncontrollable transitions to compute the set of possible next states
applyLabel :: Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
applyLabel ops@Ops{..} sd@SynthData{..} stateSet label = do
    ref btrue
    afterControllableAction    <- applyTrel ops sd transitions btrue stateSet
    ref afterControllableAction
    afterUncontrollableActions <- applyUncontrollableTC ops sd afterControllableAction
    return afterUncontrollableActions

