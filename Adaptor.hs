{-# LANGUAGE RecordWildCards #-}

module Adaptor where

import Control.Monad.ST.Lazy
import Control.Monad.State
import Control.Arrow

import CuddST
import CuddExplicitDeref as C

import Refine
import AbsGame
import PredicateDB

conj :: STDdManager s u -> [DDNode s u] -> ST s (DDNode s u)
conj m nodes = go (C.bone m) nodes
    where
    go accum []     = return accum
    go accum (n:ns) = do
        accum' <- C.band m accum n
        C.deref m accum
        go accum' ns

theGoalAbs m absGame ops spdb svdb offset absState = do
    let state = PredDBState m spdb svdb (error "shoudn't need label preds") (error "shouldn't need label vars") offset absState
    ((_, goal):_, PredDBState{..}) <- runStateT (gameGoals absGame) state
    return $ GoalAbsRet dbStatePreds dbStateVars dbNextIndex goal dbUserState

theUpdateAbs m absGame ops spdb svdb lpdb lvdb offset absState preds vars = do
    let state = PredDBState m spdb svdb lpdb lvdb offset absState
    (res, PredDBState{..}) <- runStateT (gameVarUpdateC absGame ((map (PredVar *** (:[])) preds) ++ (map (uncurry help) vars))) state
    res <- conj m res
    return $ UpdateAbsRet dbStatePreds dbStateVars dbLabelPreds dbLabelVars dbNextIndex res dbUserState
    
help vname vnodes = (NonPredVar vname (length vnodes), vnodes)

--Arguments: AbsGame structure, abstractor state
doEverything :: (Ord p, Show p) => AbsGame p o s u -> o -> ST s Bool
doEverything absGame initialAbsState = do
    m <- cuddInitSTDefaults 
    let abstractor = Abstractor {
        goalAbs   = theGoalAbs m absGame,
        updateAbs = theUpdateAbs m absGame
    }
    absRefineLoop m abstractor undefined initialAbsState

