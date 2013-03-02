-- Interface to SMT solver

module Solver(SatResult(..),
              Solver(..)) where

import CuddExplicitDeref
--import PredicateDB
import Predicate

data SatResult = SatYes
               | SatNo
               | SatMaybe
               deriving (Eq)

data Solver p s u = Solver {

    -- Check satisfiability of a conjunction of predicates
    checkSat :: [(p, Bool)] -> SatResult,

    -- Check satisfiability of a conjunction of predicates and 
    -- compute unsatisfiable core if it is unsat
    unsatCore :: [(p, Bool)] -> (SatResult, [(p, Bool)]),

    -- Existentially quantify away a set of concrete variables from 
    -- a conjunction of predicates.  May introduce new predicates.
    -- Returns logic relation that represents the formula after 
    -- quantification.
    equant :: [(p, Bool)] -> [String] -> PDB pdb s u (DDNode s u),

    --predVars :: p -> [(String, VarCategory)]
}


