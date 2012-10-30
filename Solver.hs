{-# LANGUAGE ExistentialQuantification#-}


-- Interface to SMT solver

module Solver(SatResult(..),
              Solver(..)) where

import PredicateDB

data SatResult = SatYes
               | SatNo
               | SatMaybe
               deriving (Eq)

data Solver c v a p = forall o . Solver {

    -- Check satisfiability of a conjunction of predicates
    checkSat :: [p] -> SatResult,

    -- Check satisfiability of a conjunction of predicates and 
    -- compute unsatisfiable core if it is unsat
    unsatCore :: [p] -> (SatResult, [p]),

    -- Existentially quantify away a set of concrete variables from 
    -- a conjunction of predicates.  May introduce new predicates.
    -- Returns logic relation that represents the formula after 
    -- quantification.
    equant :: [p] -> [String] -> PredicateDB c v p o a
}


