{-# LANGUAGE NoMonomorphismRestriction, GeneralizedNewtypeDeriving, TemplateHaskell, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}
module Resource where

import Control.Monad.State.Strict
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Maybe
import Control.Monad.Trans.Identity
import Language.Haskell.TH

--Resource monad class definition
class (MonadTrans t, Monad m, Monad (t m)) => MonadResource r m t | t -> r where
    checkResource :: String -> r -> t m ()
    refResource   :: String -> r -> t m ()
    derefResource :: String -> r -> t m ()
    getInUse      :: t m (InUse r)

--Helper functions for use in this monad
rf1 :: (MonadResource a m t, Ord a) => (a -> a) -> String -> (a -> m a) -> a -> t m a
rf1 reg loc f arg = do
    checkResource loc (reg arg)
    x <- lift $ f arg
    refResource loc (reg x)
    return x

rf2 :: (MonadResource a m t) => (a -> a) -> String -> (a -> a -> m a) -> a -> a -> t m a
rf2 reg loc f arg1 arg2 = do
    checkResource (loc ++ " 1") (reg arg1)
    checkResource (loc ++ " 2") (reg arg2)
    x <- lift $ f arg1 arg2
    refResource loc (reg x)
    return x

rf3 :: (MonadResource a m t) => (a -> a) -> String -> (a -> a -> a -> m a) -> a -> a -> a -> t m a
rf3 reg loc f arg1 arg2 arg3 = do
    checkResource (loc ++ " 1") (reg arg1)
    checkResource (loc ++ " 2") (reg arg2)
    checkResource (loc ++ " 3") (reg arg3)
    x <- lift $ f arg1 arg2 arg3
    refResource loc (reg x)
    return x

rf :: (MonadResource a m t) => (a -> a) -> String -> m a -> t m a
rf reg loc m = do
    x <- lift $ m
    refResource loc (reg x)
    return x

rrf :: (MonadResource a m t) => (a -> a) -> String -> t m a -> t m a
rrf reg loc m = do
    x <- m
    refResource loc (reg x)
    return x

de :: (MonadResource a m t) => (a -> a) -> String -> (a -> m ()) -> a -> t m ()
de reg loc f x = do
    derefResource loc (reg x)
    lift $ f x
    return ()

rp' :: (MonadResource a m t) => (a -> a) -> String -> (a -> m ()) -> a -> t m ()
rp' reg loc f x = do
    refResource loc (reg x)
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

appToReg :: Q Exp -> Q Exp
appToReg f = appE f $ liftM (VarE . fromJust) $ lookupValueName "regular"

--Template haskell to increment the reference counter of a resource
rp :: Q Exp
rp = withLocatedError $ appToReg [| rp' |]

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

--A concrete type implementing the Resource class
type InUse k = Map k (Set String, Int)
newtype ResourceT t m a = ResourceT {unResourceT :: StateT (InUse t) m a} deriving (Monad)

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

instance (Ord r, Monad m) => MonadResource r m (ResourceT r) where

    checkResource loc x = ResourceT $ do
        mp <- get
        checkRef loc mp x

    refResource   loc x = ResourceT $ modify $ incRef loc x

    derefResource loc x = ResourceT $ modify $ decRef loc x

    getInUse = ResourceT $ get

instance (Monad m) => MonadResource r m IdentityT where
    checkResource _ _ = return ()
    refResource   _ _ = return ()
    derefResource _ _ = return ()
    getInUse          = return $ Map.empty

runIdentityTAsResource :: (Monad m) => b -> IdentityT m a -> m (a, b)
runIdentityTAsResource inuse f = do 
    res <- runIdentityT f
    return (res, inuse)

--runResource = runResourceT
runResource = runIdentityTAsResource
