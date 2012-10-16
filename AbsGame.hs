module AbsGame(VarCategory(..),
               Pred(..),
               AbsVar(..),
               PredicateDB(..),
               pdbPred,
               AbsGame(..)) where

import Control.Monad.State

import qualified Data.Map as M

import LogicClasses

data VarCategory = VarState
                 | VarTmp

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

-- Predicate database
data PredicateDB c v p = PredicateDB { 
    pdbCtx          :: c,                  -- Logic context used to allocate vars
    pdbStateVar     :: M.Map (AbsVar p) v, -- Map predicate or variable name to logic variables
    pdbTmpVar       :: M.Map (AbsVar p) v, -- Map predicate or variable name to logic variables
    pdbUntrackedVar :: M.Map (AbsVar p) v  -- Map predicate or variable name to logic variables
}

pdbPred :: PredicateDB c v p -> [p]
pdbPred pdb = map avarPred $ filter (\v -> case v of 
                                                PredVar _ _ -> True
                                                _           -> False) 
                           $ M.keys (pdbStateVar pdb) ++ M.keys (pdbTmpVar pdb) ++ M.keys (pdbUntrackedVar pdb)

-- Everything the abstraction algorithm needs to know about the game.
data AbsGame c v a p = AbsGame {
    -- Decompose goal relations into predicates and compile them.
    -- Returns the list of named goals.  The predicate DB contains
    -- newly discovered predicates and variables.
    gameGoals       :: State (PredicateDB c v p) [(String,a)],

    -- Decompose fair set relations into predicates and compile them.
    -- Returns the list of fair sets.  The predicate DB contains
    -- newly discovered predicates and variables.
    gameFair        :: State (PredicateDB c v p) [a],

    -- Decompose initial state relation into predicates and compile it.
    -- In order to obtain an abstraction of the initial relation wrt predicate
    -- already in the DB, just quantify away all newly discovered predicates
    -- and variables.
    gameInit        :: State (PredicateDB c v p) a,

    -- Compute controllable and uncontrollable  update function.
    gameVarUpdateC :: [AbsVar p] -> State (PredicateDB c v p) [a],
    gameVarUpdateU :: [AbsVar p] -> State (PredicateDB c v p) [a]
}
