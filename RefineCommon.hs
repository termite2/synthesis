{-# LANGUAGE PolymorphicComponents, RecordWildCards, ScopedTypeVariables #-}
module RefineCommon (
    TheorySolver(..),
    fixedPoint,
    doEnVars,
    refineAny,
    refineFirstPrime,
    refineLeastPreds
    ) where

import Control.Monad.State
import Data.List

import Interface
import BddRecord

--Theory solving
data TheorySolver s u sp lp = TheorySolver {
    unsatCoreState      :: [(sp, Bool)] -> Maybe [(sp, Bool)],
    unsatCoreStateLabel :: [(sp, Bool)] -> [(lp, Bool)] -> Maybe ([(sp, Bool)], [(lp, Bool)]),
    eQuant              :: forall pdb. [(sp, Bool)] -> [(lp, Bool)] -> VarOps pdb (BAPred sp lp) BAVar s u -> StateT pdb (ST s) (DDNode s u)
}

fixedPoint :: Ops s u -> (DDNode s u -> ST s (DDNode s u)) -> DDNode s u -> ST s (DDNode s u)
fixedPoint (ops @ Ops {..}) func start = do
    res <- func start
    deref start 
    case (res==start) of --this is safe 
        True -> return start
        False -> fixedPoint ops func res
        
doEnVars :: Ops s u -> DDNode s u -> [(DDNode s u, DDNode s u)] -> ST s (DDNode s u)
doEnVars Ops{..} trans enVars = do
        ref trans
        foldM func trans enVars
    where
    func soFar (pred, en) = do
        e <- bexists pred soFar
        e1 <- e .& bnot en
        deref e
        c <- en .& soFar
        deref soFar
        res <- e1 .| c
        deref c
        deref e1
        return res

refineAny :: Ops s u -> SectionInfo  s u -> DDNode s u -> ST s (Maybe [Int])
refineAny Ops{..} SectionInfo{..} newSU = do
    si <- supportIndices newSU
    let ui = si `intersect` _untrackedInds
    return $ case ui of
        []  -> Nothing
        x:_ -> Just [x]

refineFirstPrime :: Ops s u -> SectionInfo s u -> DDNode s u -> ST s (Maybe [Int])
refineFirstPrime Ops{..} SectionInfo{..} newSU = do
    (lc, sz) <- largestCube newSU
    prime    <- makePrime lc newSU
    deref lc
    si       <- supportIndices prime
    deref prime
    let ui = si `intersect` _untrackedInds
    return $ case ui of
        [] -> Nothing
        x  -> Just x

--Refine the least number of untracked state predicates possible to make progress
refineLeastPreds :: forall s u o sp lp. Ops s u -> SectionInfo s u -> DDNode s u -> ST s (Maybe [Int])
refineLeastPreds ops@Ops{..} SectionInfo{..} newSU 
    | newSU == bfalse = return Nothing
    | otherwise       = do
        ref newSU
        (size, vars, remaining) <- sizeVarsNext newSU
        (size, vars) <- doLoop size vars remaining
        return $ Just vars
    where
    sizeVarsNext :: DDNode s u -> ST s (Int, [Int], DDNode s u)
    sizeVarsNext remaining = do
        (lc, sz) <- largestCube remaining
        prime <- makePrime lc newSU
        deref lc
        (size, vars) <- analyseCube prime
        nextRemaining <- band remaining $ bnot prime
        deref remaining
        deref prime
        return (size, vars, nextRemaining)
    doLoop :: Int -> [Int] -> DDNode s u -> ST s (Int, [Int])
    doLoop size vars remaining 
        | remaining == bfalse = return (size, vars)
        | otherwise           = do
            (size', vars', remaining') <- sizeVarsNext remaining
            if (size' < size) then doLoop size' vars' remaining' else doLoop size vars remaining'
    analyseCube :: DDNode s u -> ST s (Int, [Int])
    analyseCube cube' = do
        untrackedCube <- bexists _trackedCube cube'
        support <- supportIndices _untrackedCube
        deref untrackedCube
        return (length support, support)

