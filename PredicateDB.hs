module PredicateDB(VarCategory(..), 
                   AbsVar(..),
                   PredicateDB,
                   pdbCtx,
                   pdbPred,
                   pdbGetVar,
                   pdbLookupVar,
                   pdbAllocVar,
                   pdbAllocTmpVar,
                   pdbPutExt,
                   pdbGetExt) where

import Control.Monad.ST.Lazy
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.State
import Safe

import LogicClasses
import CuddExplicitDeref

data VarCategory = VarState
                 | VarTmp
                 deriving (Eq)

-- Predicate class.  A predicate can be converted to a string and compared
-- with other predicates.  
class (Show p, Eq p, Ord p) => Pred p where
    predOverlap :: p -> p -> Bool   -- True if predicates share a common variable

data AbsVar p = PredVar    {avarPred::p}
              | NonPredVar {avarName::String, avarSize::Int}

instance Eq p => Eq (AbsVar p) where
    (==) (PredVar p1)      (PredVar p2)      = p1 == p2
    (==) (NonPredVar n1 _) (NonPredVar n2 _) = n1 == n2
    (==) _                 _                 = False

instance Ord p => Ord (AbsVar p) where
    compare (PredVar p1)      (PredVar p2)      = compare p1 p2
    compare (NonPredVar n1 _) (NonPredVar n2 _) = compare n1 n2
    compare (PredVar _)       (NonPredVar _ _)  = LT
    compare (NonPredVar _ _)  (PredVar _)       = GT


data PredDBState p o s u = PredDBState {
    dbManager    :: STDdManager s u,
    dbStatePreds :: Map p (DDNode s u),
    dbStateVars  :: Map String [DDNode s u],
    dbLabelPreds :: Map p (DDNode s u),
    dbLabelVars  :: Map String [DDNode s u],
    dbUserState  :: o,
    dbNextIndex  :: Int
}

-- Predicate DB type:
-- c - logic context
-- v - logic variable
-- p - predicate type
-- o - opaque state stored by the predicate update algorithm in the PDB
type PredicateDB p o s u = StateT (PredDBState p o s u) (ST s)

-- Return logic context
pdbCtx :: PredicateDB p o s u (STDdManager s u)
pdbCtx = gets dbManager

-- List all predicates
pdbPred :: PredicateDB p o s u [p]
pdbPred = do
    sp <- gets dbStatePreds
    lp <- gets dbLabelPreds
    return $ Map.keys sp ++ Map.keys lp

-- Retrieve existing var that is known to exist in the DB
pdbGetVar :: Ord p => AbsVar p -> PredicateDB p o s u [DDNode s u]
pdbGetVar p = do
    res <- pdbLookupVar p
    return $ fromJustNote "pdbGetVar" res

-- Lookup variable
pdbLookupVar :: Ord p => AbsVar p -> PredicateDB p o s u (Maybe [DDNode s u])
pdbLookupVar (PredVar pred) = do
    sp <- gets dbStatePreds
    lp <- gets dbLabelPreds 
    return $ liftM (:[]) $ Map.lookup pred (Map.union sp lp)
pdbLookupVar (NonPredVar name _) = do
    sp <- gets dbStateVars
    lp <- gets dbLabelVars
    return $ Map.lookup name (Map.union sp lp)

-- Lookup or allocate variable
pdbAllocVar :: (Ord p) => AbsVar p -> VarCategory -> PredicateDB p o s u [DDNode s u]
pdbAllocVar (PredVar p) VarState = do
    theMap <- gets dbStatePreds
    m      <- gets dbManager
    case Map.lookup p theMap of
        Just var -> return [var]
        Nothing -> do
            st <- get
            newVar <- lift $ bvar m $ dbNextIndex st
            modify $ \st -> st {dbNextIndex = dbNextIndex st + 1}
            modify $ \st -> st {dbStatePreds = Map.insert  p newVar (dbStatePreds st)}
            return [newVar]
pdbAllocVar (PredVar p) VarTmp = do
    theMap <- gets dbLabelPreds
    m      <- gets dbManager
    case Map.lookup p theMap of
        Just var -> return [var]
        Nothing -> do
            st <- get
            newVar <- lift $ bvar m $ dbNextIndex st
            modify $ \st -> st {dbNextIndex = dbNextIndex st + 1}
            modify $ \st -> st {dbLabelPreds = Map.insert  p newVar (dbLabelPreds st)}
            return [newVar]
pdbAllocVar (NonPredVar nm sz) VarState = do
    theMap <- gets dbStateVars
    m      <- gets dbManager
    case Map.lookup nm theMap of
        Just var -> return var
        Nothing -> do
            st <- get
            newVar <- lift $ sequence $ map (bvar m) (take sz $ iterate (+1) (dbNextIndex st))
            modify $ \st -> st {dbNextIndex = dbNextIndex st + sz}
            modify $ \st -> st {dbStateVars = Map.insert nm newVar (dbStateVars st)}
            return newVar
pdbAllocVar (NonPredVar nm sz) VarTmp = do
    theMap <- gets dbLabelVars
    m      <- gets dbManager
    case Map.lookup nm theMap of
        Just var -> return var
        Nothing -> do
            st <- get
            newVar <- lift $ sequence $ map (bvar m) (take sz $ iterate (+1) (dbNextIndex st))
            modify $ \st -> st {dbNextIndex = dbNextIndex st + sz}
            modify $ \st -> st {dbLabelVars = Map.insert nm newVar (dbLabelVars st)}
            return newVar

-- Allocate temporary logic variable 
-- This variable is not part of the PDB and is only used internally
-- by the variable update function computation algorithm
pdbAllocTmpVar :: Int -> PredicateDB p o s u [DDNode s u]
pdbAllocTmpVar sz = do
    st <- get
    m  <- gets dbManager
    newVar <- lift $ sequence $ map (bvar m) (take sz $ iterate (+1) (dbNextIndex st))
    modify $ \st -> st {dbNextIndex = dbNextIndex st + sz}
    return newVar

-- Retrieve extended opaque state
pdbGetExt :: PredicateDB p o s u o
pdbGetExt = gets dbUserState

-- Update extended opaque state
pdbPutExt :: o -> PredicateDB p o s u ()
pdbPutExt us = modify $ \st -> st {dbUserState = us}

