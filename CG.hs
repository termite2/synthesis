{-# LANGUAGE RecordWildCards #-}

module CG (
    SynthData(..),
    pickLabel
    ) where

import Control.Monad.ST

import BddRecord
import Interface

data SynthData s u = SynthData {
    sections    :: SectionInfo s u,
    transitions :: [(DDNode s u, DDNode s u)]
}

data IteratorM m a = IteratorM {
    item :: a,
    next :: m (IteratorM m a)
}

--Given a state and a strategy, create an iterator that lists all available winning lables
availableLabels :: Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> ST s (IteratorM (ST s) (DDNode s u))
availableLabels Ops{..} SynthData{..} strategy stateSet = do
    undefined

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

--Given a label and a state, apply the label and then the transitive closure of uncontrollable transitions to compute the set of possible next states
applyLabel :: Ops s u -> SynthData s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
applyLabel Ops{..} SynthData{..} stateSet label = do
    undefined

