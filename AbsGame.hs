module AbsGame(AbsGame(..)) where

import Control.Monad.State
import qualified Data.Map as M

import PredicateDB
import CuddExplicitDeref

-- Everything the abstraction algorithm needs to know about the game.
data AbsGame p o s u = AbsGame {
    -- Decompose goal relations into predicates and compile them.
    -- Returns the list of named goals.  The predicate DB contains
    -- newly discovered predicates and variables.
    gameGoals       :: PredicateDB p o s u [(String, DDNode s u)],

    -- Decompose fair set relations into predicates and compile them.
    -- Returns the list of fair sets.  The predicate DB contains
    -- newly discovered predicates and variables.
    gameFair        :: PredicateDB p o s u [DDNode s u],

    -- Decompose initial state relation into predicates and compile it.
    -- In order to obtain an abstraction of the initial relation wrt predicate
    -- already in the DB, just quantify away all newly discovered predicates
    -- and variables.
    gameInit        :: PredicateDB p o s u (DDNode s u),

    -- Generate consistency constraint over abstract variables in the game
    gameConsistent  :: PredicateDB p o s u (DDNode s u),

    -- Compute controllable/uncontrollable update functions.
    -- Input arguments: list of abstract variables and corresponding next-state
    -- logic variables.
    -- Output: relation between current-state abstract variables and 
    -- next-state values of input variables
    gameVarUpdateC :: [(AbsVar p, [DDNode s u])] -> PredicateDB p o s u [DDNode s u],
    gameVarUpdateU :: [(AbsVar p, [DDNode s u])] -> PredicateDB p o s u [DDNode s u]
}
