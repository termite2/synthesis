{-# LANGUAGE RecordWildCards #-}

module CG (
    SynthData(..),
    availableLabels,
    pickLabel,
    ifCondition,
    applyLabel,
    applyUncontrollableTC
    ) where

import Control.Monad
import Control.Monad.ST

import BddRecord
import Interface
import BddUtil

faXnor :: Ops s u -> DDNode s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
faXnor Ops{..} cube x y = liftM bnot $ xorExistAbstract cube x y

genPair :: Ops s u -> DDNode s u -> DDNode s u -> DDNode s u -> ST s (Maybe (DDNode s u, DDNode s u))
genPair ops@Ops{..} x y rel = case rel == bfalse of
    True  -> return Nothing
    False -> do
        xOnly <- bexists y rel
        concX <- largePrime ops xOnly
        img   <- andAbstract x rel concX
        genX  <- faXnor ops y rel img
        return $ Just (genX, img)

data IteratorM m a = 
      Empty
    | Item  a (m (IteratorM m a))

instance Functor m => Functor (IteratorM m) where
    fmap _ Empty      = Empty
    fmap f (Item x r) = Item (f x) $ fmap (fmap f) r

enumerate :: Ops s u -> DDNode s u -> DDNode s u -> DDNode s u -> ST s (IteratorM (ST s) (DDNode s u, DDNode s u))
enumerate ops@Ops{..} x y rel = do
    pair <- genPair ops x y rel 
    case pair of
        Nothing               -> return Empty
        Just (pair@(genX, _)) -> do
            restricted <- band rel (bnot genX)
            return $ Item pair (enumerate ops x y restricted)

data SynthData s u = SynthData {
    sections                  :: SectionInfo s u,
    transitions               :: [(DDNode s u, DDNode s u)],
    combinedTrel              :: DDNode s u,
    uncontrollableTransitions :: [(DDNode s u, DDNode s u)]
}

--Given a state and a strategy, create an iterator that lists all available winning lables
availableLabels :: Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> ST s (IteratorM (ST s) (DDNode s u, DDNode s u))
availableLabels ops@Ops{..} SynthData{sections = SectionInfo{..}, ..} strategy stateSet = do
    yVars            <- conj ops [_trackedCube, _untrackedCube, _nextCube]
    avlWinningLabels <- andAbstract _trackedCube strategy stateSet
    rel              <- conj ops [combinedTrel, stateSet, avlWinningLabels]
    enumerate ops _labelCube yVars rel

--Pick any winning label 
pickLabel :: Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> ST s (Maybe (DDNode s u))
pickLabel Ops{..} SynthData{..} strategy stateSet = do
    let SectionInfo{..} = sections
    x   <- bor (bnot stateSet) strategy
    act <- bforall _trackedCube x
    case act == bfalse of
        True  -> return Nothing
        False -> return $ Just act

--Generate a bdd X over state variables such that (state & X) has some label available from all of it
ifCondition :: Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> ST s (Maybe (DDNode s u))
ifCondition Ops{..} SynthData{..} strategy stateSet = do
    undefined

fixedPoint :: Ops s u -> (DDNode s u -> ST s (DDNode s u)) -> DDNode s u -> ST s (DDNode s u)
fixedPoint ops@Ops{..} func start = do
    res <- func start
    deref start
    case (res == start) of
        True  -> return start
        False -> fixedPoint ops func start

forLoop start list func  = foldM func start list

applyTrel :: Ops s u -> SynthData s u -> [(DDNode s u, DDNode s u)] -> DDNode s u -> ST s (DDNode s u)
applyTrel Ops{..} SynthData{..} trel stateSet = do
    let SectionInfo{..} = sections

    combined <- forLoop bfalse trel $ \accum (cube, trel) -> do
        constrained <- band trel stateSet
        accum'      <- band constrained accum
        deref constrained
        deref accum
        return accum'

    sul' <- band _trackedCube _untrackedCube
    sul  <- band sul' _labelCube
    deref sul'

    res <- bexists sul combined
    deref sul
    deref combined

    return res

applyUncontrollableTC :: Ops s u -> SynthData s u -> DDNode s u -> ST s (DDNode s u)
applyUncontrollableTC ops sd@SynthData{..} stateSet = fixedPoint ops (applyTrel ops sd uncontrollableTransitions) stateSet

--Given a label and a state, apply the label and then the transitive closure of uncontrollable transitions to compute the set of possible next states
applyLabel :: Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
applyLabel ops@Ops{..} sd@SynthData{..} stateSet label = do
    afterControllableAction    <- applyTrel ops sd transitions stateSet
    afterUncontrollableActions <- fixedPoint ops (applyTrel ops sd uncontrollableTransitions ) afterControllableAction
    return afterControllableAction

