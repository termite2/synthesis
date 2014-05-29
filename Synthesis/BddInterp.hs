{-# LANGUAGE RecordWildCards #-}

module Synthesis.BddInterp (
    listPrimeImplicants,
    interp,
    formatPrimeImplicants,
    stateInterp,
    formatStateInterp
    ) where

import Data.Maybe
import Data.List

import Util

import Synthesis.BddRecord
import Synthesis.BddUtil

listPrimeImplicants :: Ops s u -> [[(String, [Int])]] -> DDNode s u -> ST s [[[(String, [Int])]]]
listPrimeImplicants ops@Ops{..} varss trans = do
    pc <- primeCover ops trans
    mapM func pc
    where
    func prime = mapM func2 varss
        where
        func2 section = interp ops section prime

interp :: Ops s u -> [(String, [Int])] -> DDNode s u -> ST s [(String, [Int])]
interp Ops{..} theList node = do
    st <- satCube node 
    return $ mapMaybe (func st) theList
    where
    func bits (name, idxs) 
        | all (== DontCare) encoding = Nothing
        | otherwise = Just (name, map b2IntLSF expanded)
        where
        encoding = map (bits !!) idxs
        expanded = allComb $ map expand encoding

formatPrimeImplicants :: [[[(String, [Int])]]] -> String
formatPrimeImplicants = intercalate "\n" . map func 
    where
    func = intercalate " -- " . map func2
        where
        func2 = intercalate ", " . map (uncurry func3)
            where
            func3 name values = name ++ ": " ++ show values

stateInterp :: Ops s u -> [(String, [Int])] -> DDNode s u -> ST s [(String, [Int])]
stateInterp Ops{..} theList node = do
    st <- satCube node
    return $ map (func st) theList
    where
    func bits (name, idxs) = (name, map b2IntLSF expanded)
        where
        encoding = map (bits !!) idxs
        expanded = allComb $ map expand encoding

formatStateInterp :: [(String, [Int])] -> String
formatStateInterp = intercalate ", " . map (uncurry func)
    where
    func name values = name ++ ": " ++ show values

