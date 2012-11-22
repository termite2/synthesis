{-# LANGUAGE RecordWildCards #-}

module Adaptor where

import Control.Monad.ST.Lazy
import Control.Monad.State
import Control.Arrow
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List

import CuddST
import CuddExplicitDeref as C

import Refine
import AbsGame
import PredicateDB
import Solver

conj :: STDdManager s u -> [DDNode s u] -> ST s (DDNode s u)
conj m nodes = go (C.bone m) nodes
    where
    go accum []     = return accum
    go accum (n:ns) = do
        accum' <- C.band m accum n
        C.deref m accum
        go accum' ns

theGoalAbs m absGame ops ipdb ivdb spdb svdb offset absState = do
    let state = PredDBState m ipdb ivdb spdb svdb (error "shouldn't need label preds") (error "shouldn't need label vars") offset absState
    ((_, goal):_, PredDBState{..}) <- runStateT (gameGoals absGame) state
    return $ GoalAbsRet dbStatePreds dbStateVars dbNextIndex goal dbUserState

theUpdateAbs m absGame ops ipdb ivdb spdb svdb lpdb lvdb offset absState preds vars = do
    let state = PredDBState m ipdb ivdb spdb svdb lpdb lvdb offset absState
    (res, PredDBState{..}) <- runStateT (gameVarUpdateU absGame ((map (PredVar *** (:[])) preds) ++ (map (uncurry help) vars))) state
    res <- conj m res
    return $ UpdateAbsRet dbStatePreds dbStateVars dbLabelPreds dbLabelVars dbNextIndex res dbUserState
    
help vname vnodes = (NonPredVar vname (length vnodes), vnodes)

theInitAbs m absGame ops offset absState = do
    let state = PredDBState m Map.empty Map.empty Map.empty Map.empty (error "shouldn't need label preds") (error "shouldn't need label vars") offset absState
    (res, PredDBState {..}) <- runStateT (gameInit absGame) state
    return $ InitAbsRet dbStatePreds dbStateVars res dbNextIndex dbUserState

theUCState solver preds = case unsatCore solver preds of
    (SatYes,   _)  -> Nothing
    (SatMaybe, _)  -> error "Solver returned SatMaybe"
    (SatNo,    uc) -> Just uc

theUCLabel solver statePreds labelPreds = case unsatCore solver (statePreds ++ labelPreds) of 
    (SatYes, _) -> Nothing
    (SatMaybe, _) -> error "Solver returned SatMaybe"
    (SatNo, uc) -> Just $ partition (flip elem (map fst statePreds) . fst) uc

--Arguments: AbsGame structure, abstractor state
doEverything :: (Ord p, Show p) => AbsGame p o s u -> o -> Solver p s u -> ST s Bool
doEverything absGame initialAbsState solver = do
    m <- cuddInitSTDefaults 
    let abstractor = Abstractor {
            goalAbs   = theGoalAbs m absGame,
            updateAbs = theUpdateAbs m absGame,
            initAbs   = theInitAbs m absGame
        }
        theorySolver = TheorySolver {
            unsatCoreState      = theUCState solver,
            unsatCoreStateLabel = theUCLabel solver
        }
    absRefineLoop m abstractor theorySolver initialAbsState

