module PredicateDB(VarCategory(..), 
                   AbsVar(..),
                   PredicateDB,
                   pdbCtx,
                   pdbPred,
                   pdbAbsVar,
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

data AbsVar p = PredVar {avarName::String, avarPred::p}
              | BoolVar {avarName::String}
              | EnumVar {avarName::String, avarSize::Int}

instance Eq (AbsVar p) where
    (==) v1 v2 = avarName v1 == avarName v2

instance Ord (AbsVar p) where
    compare v1 v2 = compare (avarName v1) (avarName v2)

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

-- List all abstract variables in PDB
pdbAbsVar :: PredicateDB p o s u [AbsVar p]
pdbAbsVar = undefined

-- Retrieve existing var that is known to exist in the DB
pdbGetVar :: Ord p => AbsVar p -> PredicateDB p o s u [DDNode s u]
pdbGetVar p = do
    res <- pdbLookupVar p
    return $ fromJustNote "pdbGetVar" res

singleton x = [x]

-- Lookup variable
pdbLookupVar :: Ord p => AbsVar p -> PredicateDB p o s u (Maybe [DDNode s u])
pdbLookupVar (PredVar _ pred) = do
    sp <- gets dbStatePreds
    lp <- gets dbLabelPreds 
    return $ liftM singleton $ Map.lookup pred (Map.union sp lp)
pdbLookupVar (BoolVar name)   = do
    sp <- gets dbStateVars
    lp <- gets dbLabelVars
    return $ Map.lookup name (Map.union sp lp)
pdbLookupVar (EnumVar name _) = do
    sp <- gets dbStateVars
    lp <- gets dbLabelVars
    return $ Map.lookup name (Map.union sp lp)

-- Lookup or allocate variable
pdbAllocVar :: (Ord p) => AbsVar p -> VarCategory -> PredicateDB p o s u [DDNode s u]
pdbAllocVar (PredVar _ p)   VarState = something dbStatePreds p  (:[]) 1
pdbAllocVar (PredVar _ p)   VarTmp   = something dbLabelPreds p  (:[]) 1
pdbAllocVar (BoolVar nm)    VarState = something dbStateVars  nm id    1
pdbAllocVar (BoolVar nm)    VarTmp   = something dbLabelVars  nm id    1
pdbAllocVar (EnumVar nm sz) VarState = something dbStateVars  nm id    sz
pdbAllocVar (EnumVar nm sz) VarTmp   = something dbLabelVars  nm id    sz

--TODO actually put it in the map
something accessor key func sz = do
    theMap <- gets accessor
    m      <- gets dbManager
    case Map.lookup key theMap of
        Just var -> return $ func var
        Nothing -> do
            st <- get
            newVar <- lift $ sequence $ map (bvar m) (take sz $ iterate (+1) (dbNextIndex st))
            modify $ \st -> st {dbNextIndex = dbNextIndex st + sz}
            return newVar


-- Allocate temporary logic variable 
-- This variable is not part of the PDB and is only used internally
-- by the variable update function computation algorithm
pdbAllocTmpVar :: Int -> PredicateDB p o s u [DDNode s u]
pdbAllocTmpVar = undefined

-- Retrieve extended opaque state
pdbGetExt :: PredicateDB p o s u o
pdbGetExt = gets dbUserState

-- Update extended opaque state
pdbPutExt :: o -> PredicateDB p o s u ()
pdbPutExt us = do
    modify $ \st -> st {dbUserState = us}

