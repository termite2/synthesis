{-# LANGUAGE RecordWildCards #-}

module BddUtil (
    conj,
    disj,
    allMinterms,
    concPart,
    primeCover,
    presentVars,
    makeCube,
    bddSynopsis,
    largePrime,
    presentInLargePrime,
    andDeref,
    orDeref,
    subtractBdd,
    addBdd,
    checkManagerConsistency
    ) where

import Control.Monad
import Control.Arrow
import Control.Monad.ST.Lazy.Unsafe (unsafeIOToST)

import BddRecord
import qualified CuddExplicitDeref as C

conj :: Ops s u -> [DDNode s u] -> ST s (DDNode s u)
conj Ops{..} nodes = do
        ref btrue
        go btrue nodes
    where
    go accum []     = return accum
    go accum (n:ns) = do
        accum' <- accum .&  n
        deref accum
        go accum' ns

disj :: Ops s u -> [DDNode s u] -> ST s (DDNode s u)
disj Ops{..} nodes = do
        ref bfalse
        go bfalse nodes
    where
    go accum []     = return accum
    go accum (n:ns) = do
        accum' <- accum .| n
        deref accum
        go accum' ns

allMinterms :: Ops s u -> [DDNode s u] -> DDNode s u -> ST s [DDNode s u]
allMinterms Ops{..} vars node = do
    ref node
    allMinterms' node
    where
    allMinterms' node
        | node == bfalse = return []
        | otherwise      = do
            mt <- pickOneMinterm node vars
            remaining <- node .& bnot mt
            deref node
            res <- allMinterms' remaining
            return $ mt : res

concPart :: Ops s u -> [DDNode s u] -> DDNode s u -> DDNode s u -> DDNode s u -> ST s [(DDNode s u, DDNode s u)]
concPart ops@Ops{..} concVars concCube restCube node = do
    concOnly <- bexists restCube node
    allMT <- allMinterms ops concVars concOnly
    support <- mapM supportIndices allMT
    forM allMT $ \mt -> do 
        rest <- andAbstract concCube mt node
        return (mt, rest)

primeCover :: Ops s u -> DDNode s u -> ST s [DDNode s u]
primeCover Ops{..} node = do
    ref node
    primeCover' node
    where
    primeCover' node
        | node == bfalse = return []
        | otherwise = do
            (lc, _) <- largestCube node
            pm <- makePrime lc node
            deref lc
            next <- node .& bnot pm
            deref node
            res <- primeCover' next
            return $ pm : res

presentVars :: Ops s u -> DDNode s u -> ST s [(Int, Bool)]
presentVars Ops{..} x = do
    res <- satCube x
    return $ map (second (/=0)) $ filter ((/=2) . snd) $ zip [0..] res

makeCube :: Ops s u -> [(DDNode s u, Bool)] -> ST s (DDNode s u)
makeCube Ops{..} = uncurry computeCube . unzip

bddSynopsis Ops{..} node = case node==bfalse of
    True -> "Zero"
    False -> case node==btrue of
        True -> "True"
        False -> "Non-constant: " ++ show (C.toInt node)

largePrime :: Ops s u -> DDNode s u -> ST s (DDNode s u)
largePrime Ops{..} set = do
    (lc, sz) <- largestCube set
    pm <- makePrime lc set
    deref lc
    return pm

presentInLargePrime :: Ops s u -> DDNode s u -> ST s [(Int, Bool)]
presentInLargePrime ops@Ops{..} set = do
    pm  <- largePrime ops set
    res <- presentVars ops pm
    deref pm
    return res

andDeref :: Ops s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
andDeref Ops{..} x y = do
    res <- x .& y
    mapM deref [x, y]
    return res

orDeref :: Ops s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
orDeref Ops{..} x y = do
    res <- x .| y
    mapM deref [x, y]
    return res

subtractBdd :: Ops s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
subtractBdd Ops{..} thing toSub = do
    res <- thing .& toSub
    deref thing
    return res

addBdd :: Ops s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
addBdd Ops{..} thing toAdd = do
    res <- thing .| toAdd
    deref thing
    return res

checkManagerConsistency :: String -> Ops s u -> ST s ()
checkManagerConsistency msg ops = unsafeIOToST (putStrLn ("checking bdd consistency" ++ msg ++ "\n")) >> debugCheck ops >> checkKeys ops

