{-# LANGUAGE RecordWildCards #-}

module BddRecord (
    Ops(..),
    constructOps,
    DDNode,
    STDdManager,
    ST,
    C.CuddReorderingType(..)
    ) where

import Control.Monad.ST
import Control.Monad

import qualified CuddExplicitDeref as C
import qualified CuddST as C
import qualified CuddReorder as C
import CuddExplicitDeref (DDNode, STDdManager)
import qualified MTR as C

data Ops s u = Ops {
    band, bor, bxor, bxnor, bimp, bnand, bnor :: DDNode s u -> DDNode s u -> ST s (DDNode s u),
    (.&), (.|), (.->)                         :: DDNode s u -> DDNode s u -> ST s (DDNode s u),
    bite                                      :: DDNode s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u),
    bnot                                      :: DDNode s u -> DDNode s u,
    btrue, bfalse                             :: DDNode s u,
    bforall, bexists                          :: DDNode s u -> DDNode s u -> ST s (DDNode s u),
    andAbstract, xorExistAbstract             :: DDNode s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u),
    leq                                       :: DDNode s u -> DDNode s u -> ST s Bool,
    leqUnless                                 :: DDNode s u -> DDNode s u -> DDNode s u -> ST s Bool,
    makePrime                                 :: DDNode s u -> DDNode s u -> ST s (DDNode s u),
    largestCube                               :: DDNode s u -> ST s (DDNode s u, Int),
    supportIndices                            :: DDNode s u -> ST s [Int],
    ithVar                                    :: Int -> ST s (DDNode s u),
    varAtLevel                                :: Int -> ST s (DDNode s u),
    shift                                     :: [DDNode s u] -> [DDNode s u] -> DDNode s u -> ST s (DDNode s u),
    ref                                       :: DDNode s u -> ST s (),
    deref                                     :: DDNode s u -> ST s (),
    indicesToCube                             :: [Int] -> ST s (DDNode s u),
    computeCube                               :: [DDNode s u] -> [Bool] -> ST s (DDNode s u),
    nodesToCube                               :: [DDNode s u] -> ST s (DDNode s u),
    satCube                                   :: DDNode s u -> ST s [Int],
    setVarMap                                 :: [DDNode s u] -> [DDNode s u] -> ST s (),
    mapVars                                   :: DDNode s u -> ST s (DDNode s u),
    debugCheck                                :: ST s (),
    checkKeys                                 :: ST s (),
    pickOneMinterm                            :: DDNode s u -> [DDNode s u] -> ST s (DDNode s u),
    checkZeroRef                              :: ST s Int,
    readSize                                  :: ST s Int,
    readInvPerm                               :: Int -> ST s Int,
    readPerm                                  :: Int -> ST s Int,
    shuffleHeap                               :: [Int] -> ST s (),
    makeTreeNode                              :: Int -> Int -> Int -> ST s (),
    dagSize                                   :: DDNode s u -> ST s Int,
    readNodeCount                             :: ST s Integer,
    readPeakNodeCount                         :: ST s Integer,
    regular                                   :: DDNode s u -> DDNode s u,
    reduceHeap                                :: C.CuddReorderingType -> Int -> ST s Int,
    andLimit                                  :: DDNode s u -> DDNode s u -> Int -> ST s (Maybe (DDNode s u)),
    readTree                                  :: ST s (C.MtrNode)
}

constructOps :: STDdManager s u -> Ops s u
constructOps m = Ops {..}
    where
    band                   = C.band             m
    bor                    = C.bor              m
    bxor                   = C.bxor             m
    bxnor                  = C.bxnor            m
    bimp x y               = C.bor              m (C.bnot x) y
    bnand                  = C.bnand            m
    bnor                   = C.bnor             m
    (.&)                   = C.band             m
    (.|)                   = C.bor              m
    (.->) x y              = C.bor              m (C.bnot x) y
    bite                   = C.bite             m
    bnot                   = C.bnot              
    btrue                  = C.bone             m
    bfalse                 = C.bzero            m
    bforall                = flip $ C.bforall   m
    bexists                = flip $ C.bexists   m
    andAbstract c f g      = C.andAbstract      m f g c
    xorExistAbstract c f g = C.xorExistAbstract m f g c
    supportIndices         = C.supportIndices   m
    ithVar                 = C.bvar             m
    varAtLevel             = C.newVarAtLevel    m
    leq                    = C.leq              m
    leqUnless              = C.leqUnless        m
    shift                  = C.shift            m
    ref                    = C.ref               
    deref                  = C.deref            m
    makePrime              = C.makePrime        m
    largestCube            = C.largestCube      m
    indicesToCube          = C.indicesToCube    m
    computeCube            = C.computeCube      m
    nodesToCube            = C.nodesToCube      m
    satCube                = C.satCube          m
    setVarMap              = C.setVarMap        m
    mapVars                = C.mapVars          m
    debugCheck             = C.debugCheck       m
    checkKeys              = C.checkKeys        m
    pickOneMinterm         = C.pickOneMinterm   m
    checkZeroRef           = C.checkZeroRef     m
    readSize               = C.readSize         m
    readInvPerm            = C.readInvPerm      m
    readPerm               = C.readPerm         m
    shuffleHeap            = C.cuddShuffleHeapST m
    makeTreeNode x y z     = void $ C.cuddMakeTreeNode m x y z
    dagSize                = C.dagSize
    readNodeCount          = C.readNodeCount m
    readPeakNodeCount      = C.readPeakNodeCount m
    regular                = C.regular
    reduceHeap             = C.cuddReduceHeap m
    andLimit               = C.andLimit m
    readTree               = C.readTree m
    
