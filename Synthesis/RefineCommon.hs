{-# LANGUAGE PolymorphicComponents, RecordWildCards, ScopedTypeVariables, TemplateHaskell, FlexibleContexts #-}
module Synthesis.RefineCommon (
    TheorySolver(..),
    fixedPoint,
    doEnVars,
    refineAny,
    refineFirstPrime,
    refineLeastPreds,
    partitionStateLabel,
    indicesToStatePreds,
    indicesToStatePreds',
    indicesToLabelPreds,
    partitionStateLabelPreds,
    stateLabelInconsistent,
    stateLabelConsistent,
    updateWrapper,
    groupForUnsatCore,
    setupManager,
    makeCubeInt
    ) where

import Control.Monad.State
import Data.List
import Data.Maybe
import Control.Arrow
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Tuple.All
import Data.Function

import Safe

import Synthesis.Interface
import Synthesis.BddRecord
import Synthesis.BddUtil
import Synthesis.Resource
import Synthesis.RefineUtil

import Cudd.Reorder
import Cudd.Imperative

--Theory solving
data TheorySolver s u sp lp lv = TheorySolver {
    unsatCoreState      :: [(sp, [Bool])] -> Maybe [(sp, [Bool])],
    unsatCoreStateLabel :: [(sp, [Bool])] -> [(lp, [Bool])] -> Maybe ([(sp, [Bool])], [(lp, [Bool])]),
    eQuant              :: forall pdb. [(lp, [Bool])] -> VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) (DDNode s u),
    getVarsLabel        :: lp -> [lv]
}

fixedPoint :: Ops s u -> (DDNode s u -> ST s (DDNode s u)) -> DDNode s u -> ST s (DDNode s u)
fixedPoint ops@Ops{..} func start = do
    res <- func start
    deref start 
    case (res==start) of --this is safe 
        True -> return start
        False -> fixedPoint ops func res
        
doEnVars :: Ops s u -> DDNode s u -> [([DDNode s u], DDNode s u)] -> ST s (DDNode s u)
doEnVars Ops{..} trans enVars = do
        ref trans
        foldM func trans enVars
    where
    func soFar (var, en) = do
        varCube <- nodesToCube var
        e <- bexists varCube soFar
        deref varCube
        e1 <- e .& bnot en
        deref e
        c <- en .& soFar
        deref soFar
        res <- e1 .| c
        deref c
        deref e1
        return res

refineAny :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> SectionInfo  s u -> DDNode s u -> t (ST s) (Maybe [Int])
refineAny Ops{..} SectionInfo{..} newSU = do
    si <- lift $ supportIndices newSU
    let ui = si `intersect` _untrackedInds
    return $ case ui of
        []  -> Nothing
        x:_ -> Just [x]

refineFirstPrime :: Ops s u -> SectionInfo s u -> DDNode s u -> ST s (Maybe [Int])
refineFirstPrime Ops{..} SectionInfo{..} newSU = do
    if newSU == bfalse then
        return Nothing
    else do
        (lc, sz) <- largestCube newSU
        prime    <- makePrime lc newSU
        deref lc
        si       <- supportIndices prime
        deref prime
        let ui = si `intersect` _untrackedInds
        case ui of
            [] -> error "refineFirstPrime"
            x  -> return $ Just x

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
        support <- supportIndices untrackedCube
        deref untrackedCube
        return (length support, support)

partitionStateLabel :: SectionInfo s u -> [(Int, a)] -> ([(Int, a)], [(Int, a)])
partitionStateLabel SectionInfo{..} = partition (f . fst)
    where f p = elem p _trackedInds || elem p _untrackedInds

indicesToStatePreds :: SymbolInfo s u sp lp -> [(Int, a)] -> [((Int, sp), a)]
indicesToStatePreds SymbolInfo{..} = map func
    where
    func = first $ (id &&& fromJustNote "refineConsistency2" . flip Map.lookup _stateRev)

indicesToStatePreds' :: SymbolInfo s u sp lp -> [(Int, a)] -> [((Int, sp), a)]
indicesToStatePreds' SymbolInfo{..} x = catMaybes $ map func x
    where
    func (idx, val) = case Map.lookup idx _stateRev of
                          Just x  -> Just ((idx, x), val)
                          Nothing -> Nothing

indicesToLabelPreds :: SymbolInfo s u sp lp -> [(Int, a)] -> [((Int, lp), a)]
indicesToLabelPreds SymbolInfo{..} = catMaybes . map (uncurry func)
    where
    func idx polarity = case fromJustNote "refineConsistency3" $ Map.lookup idx _labelRev of
        (_, True)   -> Nothing
        (pred, False) -> Just ((idx, pred), polarity)

partitionStateLabelPreds :: SectionInfo s u -> SymbolInfo s u sp lp -> [(Int, a)] -> ([((Int, sp), a)], [((Int, lp), a)])
partitionStateLabelPreds si syi x = (statePairs, labelPairs)
    where
    statePairs = indicesToStatePreds syi stateIndices
    labelPairs = indicesToLabelPreds syi labelIndices
    (stateIndices, labelIndices) = partitionStateLabel si x

makeCubeInt :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> [([DDNode s u], [Bool])] -> t (ST s) (DDNode s u)
makeCubeInt ops@Ops{..} x = $r $ makeCube ops $ concatMap (uncurry zip ) x

stateLabelInconsistent :: (Ord sp, Ord lp, MonadResource (DDNode s u) (ST s) t) => Ops s u -> SymbolInfo s u sp lp -> [(sp, [Bool])] -> [(lp, [Bool])] -> t (ST s) (DDNode s u)
stateLabelInconsistent ops@Ops{..} SymbolInfo{..} statePairs labelPairs = do
    inconsistentState <- makeCubeInt ops $ map (first getStates) statePairs
    inconsistentLabel <- makeCubeInt ops $ map (first getLabels) labelPairs
    res <- $r $ band inconsistentState inconsistentLabel
    $d deref inconsistentLabel
    $d deref inconsistentState
    return res
    where
    getStates = sel1 . fromJustNote "refineConsistency" . flip Map.lookup _stateVars
    getLabels = sel1 . fromJustNote "refineConsistency" . flip Map.lookup _labelVars

stateLabelConsistent :: (Ord sp, Ord lp, MonadResource (DDNode s u) (ST s) t) => Ops s u -> SymbolInfo s u sp lp -> [(lp, [Bool])] -> t (ST s) (DDNode s u) 
stateLabelConsistent ops@Ops{..} SymbolInfo{..} cLabelPreds = do
    labelCube <- makeCubeInt ops $ concatMap func labelPreds'
    otherCube <- $r $ makeCube ops    $ zip otherEnabling (repeat False)
    res <- $r $ band labelCube otherCube
    $d deref labelCube
    $d deref otherCube
    return res
    where
    otherEnabling = map (sel3 . snd) $ filter (\(p, _) -> not $ p `elem` map fst cLabelPreds) $ Map.toList _labelVars
    labelPreds' = map (first $ fromJustNote "refineConsistency" . flip Map.lookup _labelVars) cLabelPreds
    func (l, pol) = [(sel1 l, pol), ([sel3 l], [True])]

updateWrapper :: Ops s u -> DDNode s u -> StateT (DB s u dp lp) (ST s) (DDNode s u)
updateWrapper ops@Ops{..} updateExprConj'' = do
    outcomeCube <- gets $ _outcomeCube . _sections
    updateExprConj' <- lift $ bexists outcomeCube updateExprConj''
    lift $ deref updateExprConj''
    labelPreds <- gets $ _labelVars . _symbolTable
    updateExprConj  <- lift $ doEnVars ops updateExprConj' $ map (sel1 &&& sel3) $ Map.elems labelPreds
    lift $ deref updateExprConj'
    return updateExprConj

groupForUnsatCore :: (Ord sp) => (sp -> [Int]) -> [((Int, sp), Bool)] -> [(sp, [Bool])]
groupForUnsatCore func svs = map (uncurry reconstruct) $ aggregate svs
    where    
    aggregate args = Map.toList $ foldl f Map.empty args
        where
        f mp ((idx, a), b) = case Map.lookup a mp of
            Just x  -> Map.insert a ((idx, b) : x) mp
            Nothing -> Map.insert a [(idx, b)] mp
    reconstruct pred list = (pred, map funcy $ func pred)
        where
        funcy idx = maybe False snd $ find ((==idx) . fst) list 

setupManager :: STDdManager s u -> ST s ()
setupManager m = void $ do
    cuddAutodynEnable m CuddReorderGroupSift
    regStdPreReordHook m
    regStdPostReordHook m
    cuddEnableReorderingReporting m
