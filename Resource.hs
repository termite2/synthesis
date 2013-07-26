{-# LANGUAGE NoMonomorphismRestriction, GeneralizedNewtypeDeriving, TemplateHaskell #-}
module Resource where

import Control.Monad.State.Strict
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Control.Arrow
import Data.List
import Data.Maybe
import Control.Monad.ST

import Language.Haskell.TH

{-# NOINLINE trace #-}
trace :: String -> ST s ()
trace = unsafeIOToST . putStrLn

type InUse k = Map k ([String], Int)

incRef n = Map.alter func 
    where
    func Nothing        = Just ([n], 1)
    func (Just (ns, x)) = Just (nub (n:ns), x+1)

decRef loc = Map.alter func 
    where
    func Nothing       = error $ "tried to delete key that wasn't referenced: " ++ loc
    func (Just (_, 1)) = Nothing
    func (Just (n, x)) = Just $ (n, x - 1)

checkRef loc mp x = case Map.lookup x mp of
    Nothing -> error $ "Argument is not in map: " ++ loc
    Just _  -> return $ ()

newtype ResourceT t m a = ResourceT {unResourceT :: StateT (InUse t) m a} deriving (Monad)

runResourceT = flip runStateT (Map.empty) . unResourceT

evalResourceT = flip evalStateT (Map.empty) . unResourceT

instance MonadTrans (ResourceT t) where
    lift = ResourceT . lift

rf1 :: (Monad m, Ord a) => (a -> a) -> String -> (a -> m a) -> a -> ResourceT a m a
rf1 reg loc f arg = ResourceT $ do
    mp <- get
    checkRef loc mp (reg arg)
    x <- lift $ f arg
    modify $ incRef loc (reg x)
    return x

rf2 :: (Monad m, Ord a) => (a -> a) -> String -> (a -> a -> m a) -> a -> a -> ResourceT a m a
rf2 reg loc f arg1 arg2 = ResourceT $ do
    mp <- get
    checkRef (loc ++ " 1") mp (reg arg1)
    checkRef (loc ++ " 2") mp (reg arg2)
    x <- lift $ f arg1 arg2
    modify $ incRef loc (reg x)
    return x

rf3 :: (Monad m, Ord a) => (a -> a) -> String -> (a -> a -> a -> m a) -> a -> a -> a -> ResourceT a m a
rf3 reg loc f arg1 arg2 arg3 = ResourceT $ do
    mp <- get
    checkRef loc mp (reg arg1)
    checkRef loc mp (reg arg2)
    checkRef loc mp (reg arg3)
    x <- lift $ f arg1 arg2 arg3
    modify $ incRef loc (reg x)
    return x

rf :: (Monad m, Ord a) => (a -> a) -> String -> m a -> ResourceT a m a
rf reg loc m = ResourceT $ do
    x <- lift $ m
    modify $ incRef loc (reg x)
    return x

rrf :: (Monad m, Ord a) => (a -> a) -> String -> ResourceT a m a -> ResourceT a m a
rrf reg loc m = ResourceT $ do
    x <- unResourceT m
    modify $ incRef loc (reg x)
    return x

de :: (Monad m, Ord a) => (a -> a) -> String -> (a -> m ()) -> a -> ResourceT a m ()
de reg loc f x = ResourceT $ do
    modify $ decRef loc (reg x)
    lift $ f x
    st <- get
    st `seq` return ()

withLocatedError :: Q Exp -> Q Exp
withLocatedError f = do
    let error = locatedError =<< location
    appE f error

locatedError :: Loc -> Q Exp
locatedError loc = litE $ stringL $ formatLoc loc

formatLoc :: Loc -> String
formatLoc loc = let file = loc_module loc
                    (line, col) = loc_start loc
                in concat [file, ":", show line, ":", show col]

appToReg :: Q Exp -> Q Exp
appToReg f = appE f $ liftM (VarE . fromJust) $ lookupValueName "regular"

--Template haskell to increment the reference counter of a resource
r :: Q Exp
r = withLocatedError $ appToReg [| rf |]

r1 :: Q Exp
r1 = withLocatedError $ appToReg [| rf1 |]

r2 :: Q Exp
r2 = withLocatedError $ appToReg [| rf2 |]

r3 :: Q Exp
r3 = withLocatedError $ appToReg [| rf3 |]

--Template haskell to increment the reference counter of a resource that is already in the monad
rr :: Q Exp
rr = withLocatedError $ appToReg [| rrf |]

--Template haskell to decrement the reference counter of a resource
d :: Q Exp
d = withLocatedError $ appToReg [| de |]
