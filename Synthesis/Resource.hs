{-# LANGUAGE GeneralizedNewtypeDeriving, TemplateHaskell, MultiParamTypeClasses, FlexibleInstances #-}
module Synthesis.Resource where

import Control.Monad.State.Strict
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Maybe
import Control.Monad.Trans.Identity
import Language.Haskell.TH

class Regular r where
    reg :: r -> r

type InUse k = Map k (Set String, Int)

--Resource monad class definition
class (MonadTrans t) => MonadResource r t where
    checkResource :: Monad m => String -> r -> t m ()
    refResource   :: Monad m => String -> r -> t m ()
    derefResource :: Monad m => String -> r -> t m ()
    getInUse      :: Monad m => t m (InUse r)

--Helper functions for use in this monad
rf1 :: (Monad (t m), Monad m, MonadResource a t, Ord a) => String -> (a -> m a) -> a -> t m a
rf1 loc f arg = do
    checkResource loc arg
    x <- lift $ f arg
    refResource loc x
    return x

rf2 :: (Monad (t m), Monad m, MonadResource a t) => String -> (a -> a -> m a) -> a -> a -> t m a
rf2 loc f arg1 arg2 = do
    checkResource (loc ++ ": arg 1") arg1
    checkResource (loc ++ ": arg 2") arg2
    x <- lift $ f arg1 arg2
    refResource loc x
    return x

rf3 :: (Monad (t m), Monad m, MonadResource a t) => String -> (a -> a -> a -> m a) -> a -> a -> a -> t m a
rf3 loc f arg1 arg2 arg3 = do
    checkResource (loc ++ ": arg 1") arg1
    checkResource (loc ++ ": arg 2") arg2
    checkResource (loc ++ ": arg 3") arg3
    x <- lift $ f arg1 arg2 arg3
    refResource loc x
    return x

rf :: (Monad (t m), Monad m, MonadResource a t) => String -> m a -> t m a
rf loc m = do
    x <- lift $ m
    refResource loc x
    return x

rrf :: (Monad (t m), Monad m, MonadResource a t) => String -> t m a -> t m a
rrf loc m = do
    x <- m
    refResource loc x
    return x

de :: (Monad (t m), Monad m, MonadResource a t) => String -> (a -> m ()) -> a -> t m ()
de loc f x = do
    derefResource loc x
    lift $ f x
    return ()

rp' :: (Monad (t m), Monad m, MonadResource a t) => String -> (a -> m ()) -> a -> t m ()
rp' loc f x = do
    refResource loc x
    lift $ f x

--Template haskell
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

--Template haskell to increment the reference counter of a resource
rp :: Q Exp
rp = withLocatedError [| rp' |]

r :: Q Exp
r = withLocatedError [| rf |]

r1 :: Q Exp
r1 = withLocatedError [| rf1 |]

r2 :: Q Exp
r2 = withLocatedError [| rf2 |]

r3 :: Q Exp
r3 = withLocatedError [| rf3 |]

--Template haskell to increment the reference counter of a resource that is already in the monad
rr :: Q Exp
rr = withLocatedError [| rrf |]

--Template haskell to decrement the reference counter of a resource
d :: Q Exp
d = withLocatedError [| de |]

--A concrete type implementing the Resource class
newtype ResourceT r m a = ResourceT {unResourceT :: StateT (InUse r) m a} deriving (Monad)

runResourceT  inUse = flip runStateT  inUse . unResourceT
evalResourceT inUse = flip evalStateT inUse . unResourceT

instance MonadTrans (ResourceT t) where
    lift = ResourceT . lift

incRef n = Map.alter func 
    where
    func Nothing        = Just (Set.singleton n, 1)
    func (Just (ns, x)) = Just (Set.insert n ns, x+1)

decRef loc = Map.alter func 
    where
    func Nothing       = error $ "tried to delete key that wasn't referenced: " ++ loc
    func (Just (_, 1)) = Nothing
    func (Just (n, x)) = Just $ (n, x - 1)

checkRef loc mp x = case Map.lookup x mp of
    Nothing -> error $ "Argument is not in map: " ++ loc
    Just _  -> return $ ()

instance (Ord r, Regular r) => MonadResource r (ResourceT r) where

    checkResource loc x = ResourceT $ do
        mp <- get
        checkRef loc mp (reg x)

    refResource   loc x = ResourceT $ modify $ incRef loc (reg x)

    derefResource loc x = ResourceT $ modify $ decRef loc (reg x)

    getInUse = ResourceT $ get

instance MonadResource r IdentityT where
    checkResource _ _ = return ()
    refResource   _ _ = return ()
    derefResource _ _ = return ()
    getInUse          = return $ Map.empty

runIdentityTAsResource :: (Monad m) => b -> IdentityT m a -> m (a, b)
runIdentityTAsResource inuse f = do 
    res <- runIdentityT f
    return (res, inuse)

runResource = runResourceT
--runResource = runIdentityTAsResource
