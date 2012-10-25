module PredicateDB(VarCategory(..), 
                   AbsVar(..),
                   PredicateDB,
                   pdbCtx,
                   pdbPred,
                   pdbGetVar,
                   pdbLookupVar,
                   pdbAllocVar,
                   pdbPutExt,
                   pdbGetExt) where

import LogicClasses

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

-- Predicate DB type:
-- c - logic context
-- v - logic variable
-- p - predicate type
-- o - opaque state stored by the predicate update algorithm in the PDB
data PredicateDB c v p o x = PredicateDB

instance Monad (PredicateDB c v p o) where
    (>>=)  = undefined
    return = undefined

---- Predicate database
--data PredicateDB c v p = PredicateDB { 
--    pdbCtx          :: c,                  -- Logic context used to allocate vars
--    pdbStateVar     :: M.Map (AbsVar p) v, -- Map predicate or variable name to logic variables
--    pdbTmpVar       :: M.Map (AbsVar p) v, -- Map predicate or variable name to logic variables
--    pdbUntrackedVar :: M.Map (AbsVar p) v  -- Map predicate or variable name to logic variables
--}

--pdbPred :: PredicateDB c v p -> [p]
--pdbPred pdb = map avarPred $ filter (\v -> case v of 
--                                                PredVar _ _ -> True
--                                                _           -> False) 
--                           $ M.keys (pdbStateVar pdb) ++ M.keys (pdbTmpVar pdb) ++ M.keys (pdbUntrackedVar pdb)

-- Return logic context
pdbCtx :: PredicateDB c v p o c
pdbCtx = undefined

-- List all predicates
pdbPred :: PredicateDB c v p o [p]
pdbPred = undefined

-- Retrieve existing var that is known to exist in the DB
pdbGetVar :: AbsVar p -> PredicateDB c v p o v
pdbGetVar = undefined

-- Lookup variable
pdbLookupVar :: AbsVar p -> PredicateDB c v p o (Maybe v)
pdbLookupVar = undefined

-- Lookup or allocate variable
pdbAllocVar :: AbsVar p -> VarCategory -> PredicateDB c v p o v
pdbAllocVar = undefined

-- Retrieve extended opaque state
pdbGetExt :: PredicateDB c v p o o
pdbGetExt = undefined

-- Update extended opaque state
pdbPutExt :: o -> PredicateDB c v p o ()
pdbPutExt = undefined
