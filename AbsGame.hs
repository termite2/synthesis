module AbsGame(AbsGame(..)) where

import Control.Monad.State
import qualified Data.Map as M

import PredicateDB

-- Everything the abstraction algorithm needs to know about the game.
data AbsGame c v a p o = AbsGame {
    -- Decompose goal relations into predicates and compile them.
    -- Returns the list of named goals.  The predicate DB contains
    -- newly discovered predicates and variables.
    gameGoals       :: PredicateDB c v p o [(String,a)],

    -- Decompose fair set relations into predicates and compile them.
    -- Returns the list of fair sets.  The predicate DB contains
    -- newly discovered predicates and variables.
    gameFair        :: PredicateDB c v p o [a],

    -- Decompose initial state relation into predicates and compile it.
    -- In order to obtain an abstraction of the initial relation wrt predicate
    -- already in the DB, just quantify away all newly discovered predicates
    -- and variables.
    gameInit        :: PredicateDB c v p o a,

    -- Compute controllable/uncontrollable update functions.
    -- Input arguments: list of abstract variables and corresponding next-state
    -- logic variables.
    -- Output: relation between current-state abstract variables and 
    -- next-state values of input variables
    gameVarUpdateC :: [(AbsVar p, v)] -> PredicateDB c v p o [a],
    gameVarUpdateU :: [(AbsVar p, v)] -> PredicateDB c v p o [a]
}
