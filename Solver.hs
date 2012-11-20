{-# LANGUAGE ExistentialQuantification#-}


-- Interface to SMT solver

module Solver(SatResult(..),
              Solver(..)) where

import CuddExplicitDeref
import PredicateDB

data SatResult = SatYes
               | SatNo
               | SatMaybe
               deriving (Eq)

data Solver p s u = forall o . Solver {

    -- Check satisfiability of a conjunction of predicates
    checkSat :: [(p, Bool)] -> SatResult,

    -- Check satisfiability of a conjunction of predicates and 
    -- compute unsatisfiable core if it is unsat
    unsatCore :: [(p, Bool)] -> (SatResult, [(p, Bool)]),

    -- Existentially quantify away a set of concrete variables from 
    -- a conjunction of predicates.  May introduce new predicates.
    -- Returns logic relation that represents the formula after 
    -- quantification.
    equant :: [(p, Bool)] -> [String] -> PredicateDB p o s u (DDNode s u)
}


