module AbsGame(VarCategory(..),
               PredicateDB(..),
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

-- Predicate database
data PredicateDB c v p = PredicateDB { 
    pdbCtx  :: c,                            -- Logic context used to allocate vars
    pdbPred :: [(p, VarCategory)],           -- Predicates.  Do we need to store the tracked/untracked flag?
    pdbBool :: [(String, VarCategory)],      -- Boolean variables.
    pdbEnum :: [(String, VarCategory, Int)], -- Enum variables (name, number of values)
    pdbVar  :: M.Map String v                -- Map predicate or variable name to logic variables
}

-- 
data AbsGame c v a p = AbsGame { 
    -- Decompose goal relations into predicates and compile them.
    -- Returns the list of named goals.  The predicate DB contains
    -- newly discovered predicates and variables.
    gameGoals      :: State (PredicateDB c v p) [(String,a)],

    -- Decompose fair set relations into predicates and compile them.
    -- Returns the list of fair sets.  The predicate DB contains
    -- newly discovered predicates and variables.
    gameFair       :: State (PredicateDB c v p) [a],

    -- Decompose initial state relation into predicates and compile it.
    -- In order to obtain an abstraction of the initial relation wrt predicate
    -- already in the DB, just quantify away all newly discovered predicates
    -- and variables.
    gameInit       :: State (PredicateDB c v p) a,

    -- Compute predicate update function.
    gamePredUpdate :: p -> State (PredicateDB c v p) a,

    -- Compute predicate update function.
    gameBoolUpdate :: String -> State (PredicateDB c v p) a,

    -- Compute enum variable update function.
    gameEnumUpdate :: String -> State (PredicateDB c v p) a
}
