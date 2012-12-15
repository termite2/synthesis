{-# LANGUAGE RecordWildCards #-}

module BddInterp (
    listPrimeImplicants,
    interp,
    formatPrimeImplicants,
    stateInterp,
    formatStateInterp
    ) where

import Data.Maybe
import Data.List

import Util

import BddRecord
import BddUtil

listPrimeImplicants :: Ops s u -> [[(String, [Int])]] -> DDNode s u -> ST s [[[(String, [Int])]]]
listPrimeImplicants ops@Ops{..} varss trans = do
    pc <- primeCover ops trans
    mapM func pc
    where
    func prime = do
        mapM func2 varss
        where
        func2 section = interp ops section prime

interp :: Ops s u -> [(String, [Int])] -> DDNode s u -> ST s [(String, [Int])]
interp Ops{..} theList node = do
    st <- satCube node 
    return $ mapMaybe (func st) theList
    where
    func bits (name, idxs) 
        | all (==2) encoding = Nothing
        | otherwise = Just (name, (map b2IntLSF expanded))
        where
        encoding = map (bits !!) idxs
        expanded = allComb $ map func encoding
        func 0 = [False]
        func 1 = [True]
        func 2 = [False, True]

formatPrimeImplicants :: [[[(String, [Int])]]] -> String
formatPrimeImplicants = concat . intersperse "\n" . map func 
    where
    func = concat . intersperse " -- " . map func2
        where
        func2 = concat . intersperse ", " . map (uncurry func3)
            where
            func3 name values = name ++ ": " ++ show values

stateInterp :: Ops s u -> [(String, [Int])] -> DDNode s u -> ST s [(String, [Int])]
stateInterp Ops{..} theList node = do
    st <- satCube node
    return $ map (func st) theList
    where
    func bits (name, idxs) = (name, (map b2IntLSF expanded))
        where
        encoding = map (bits !!) idxs
        expanded = allComb $ map func encoding
        func 0 = [False]
        func 1 = [True]
        func 2 = [False, True]

formatStateInterp :: [(String, [Int])] -> String
formatStateInterp = concat . intersperse ", " . map (uncurry func)
    where
    func name values = name ++ ": " ++ show values

