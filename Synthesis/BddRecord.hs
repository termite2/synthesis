{-# LANGUAGE RecordWildCards #-}

module Synthesis.BddRecord (
    Ops(..),
    constructOps,
    DDNode,
    DDManager,
    ST,
    C.CuddReorderingType(..),
    SatBit(..),
    C.expand
    ) where

import Control.Monad.ST
import Control.Monad

import Cudd.Imperative (DDNode, DDManager, SatBit)
import qualified Cudd.Imperative as C
import qualified Cudd.Reorder as C
import qualified Cudd.MTR as C

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
    support                                   :: DDNode s u -> ST s (DDNode s u),
    supportIndices                            :: DDNode s u -> ST s [Int],
    ithVar                                    :: Int -> ST s (DDNode s u),
    varAtLevel                                :: Int -> ST s (DDNode s u),
    swapVariables                             :: [DDNode s u] -> [DDNode s u] -> DDNode s u -> ST s (DDNode s u),
    ref                                       :: DDNode s u -> ST s (),
    deref                                     :: DDNode s u -> ST s (),
    indicesToCube                             :: [Int] -> ST s (DDNode s u),
    computeCube                               :: [DDNode s u] -> [Bool] -> ST s (DDNode s u),
    nodesToCube                               :: [DDNode s u] -> ST s (DDNode s u),
    satCube                                   :: DDNode s u -> ST s [SatBit],
    setVarMap                                 :: [DDNode s u] -> [DDNode s u] -> ST s (),
    mapVars                                   :: DDNode s u -> ST s (DDNode s u),
    debugCheck                                :: ST s Int,
    checkKeys                                 :: ST s Int,
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
    readTree                                  :: ST s (C.MtrNode s),
    liCompact                                 :: DDNode s u -> DDNode s u -> ST s (DDNode s u)
}

constructOps :: DDManager s u -> Ops s u
constructOps m = Ops {..}
    where
    band                   = C.bAnd             m
    bor                    = C.bOr              m
    bxor                   = C.bXor             m
    bxnor                  = C.bXnor            m
    bimp x y               = C.bOr              m (C.bNot x) y
    bnand                  = C.bNand            m
    bnor                   = C.bNor             m
    (.&)                   = C.bAnd             m
    (.|)                   = C.bOr              m
    (.->) x y              = C.bOr              m (C.bNot x) y
    bite                   = C.bIte             m
    bnot                   = C.bNot              
    btrue                  = C.bOne             m
    bfalse                 = C.bZero            m
    bforall                = flip $ C.bForall   m
    bexists                = flip $ C.bExists   m
    andAbstract c f g      = C.andAbstract      m f g c
    xorExistAbstract c f g = C.xorExistAbstract m f g c
    support                = C.support          m
    supportIndices         = C.supportIndices   m
    ithVar                 = C.ithVar           m
    varAtLevel             = C.newVarAtLevel    m
    leq                    = C.lEq              m
    leqUnless              = C.leqUnless        m
    swapVariables          = C.swapVariables    m
    ref                    = C.ref               
    deref                  = C.deref            m
    makePrime              = C.makePrime        m
    largestCube            = C.largestCube      m
    indicesToCube          = C.indicesToCube    m
    computeCube            = C.computeCube      m
    nodesToCube            = C.nodesToCube      m
    satCube                = C.bddToCubeArray   m
    setVarMap              = C.setVarMap        m
    mapVars                = C.varMap           m
    debugCheck             = C.debugCheck       m
    checkKeys              = C.checkKeys        m
    pickOneMinterm         = C.pickOneMinterm   m
    checkZeroRef           = C.checkZeroRef     m
    readSize               = C.readSize         m
    readInvPerm            = C.readInvPerm      m
    readPerm               = C.readPerm         m
    shuffleHeap            = C.shuffleHeap m
    makeTreeNode x y z     = void $ C.cuddMakeTreeNode m x y z
    dagSize                = C.dagSize
    readNodeCount          = C.readNodeCount m
    readPeakNodeCount      = C.readPeakNodeCount m
    regular                = C.regular
    reduceHeap             = C.cuddReduceHeap m
    andLimit               = C.andLimit m
    readTree               = C.readTree m
    liCompact              = C.liCompaction m
    
