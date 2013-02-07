{-# LANGUAGE PolymorphicComponents, RecordWildCards, ScopedTypeVariables #-}
module RefineCommon (
    TheorySolver(..),
    fixedPoint,
    doEnVars,
    refineAny,
    refineFirstPrime,
    refineLeastPreds,
    getPredicates,
    partitionStateLabel,
    indicesToStatePreds,
    indicesToLabelPreds,
    partitionStateLabelPreds,
    stateLabelInconsistent,
    stateLabelConsistent
    ) where

import Control.Monad.State
import Data.List
import Data.Maybe
import Control.Arrow
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Tuple.All

import Safe

import Interface
import BddRecord
import BddUtil

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

getPredicates :: [(Variable p s u, a)] -> [(p, a)]
getPredicates = mapMaybe func 
    where
    func (Predicate p _, x) = Just (p, x)
    func _                  = Nothing

partitionStateLabel :: SectionInfo s u -> [(Int, a)] -> ([(Int, a)], [(Int, a)])
partitionStateLabel SectionInfo{..} = partition (f . fst)
    where f p = elem p _trackedInds || elem p _untrackedInds

indicesToStatePreds :: SymbolInfo s u sp lp -> [(Int, a)] -> [(sp, a)]
indicesToStatePreds SymbolInfo{..} = getPredicates . map func
    where
    func = first $ fromJustNote "refineConsistency2" . flip Map.lookup _stateRev

indicesToLabelPreds :: SymbolInfo s u sp lp -> [(Int, a)] -> [(lp, a)]
indicesToLabelPreds SymbolInfo{..} = getPredicates . catMaybes . map (uncurry func)
    where
    func idx polarity = case fromJustNote "refineConsistency3" $ Map.lookup idx _labelRev of
        (_, True)   -> Nothing
        (pred, False) -> Just (pred, polarity)

partitionStateLabelPreds :: SectionInfo s u -> SymbolInfo s u sp lp -> [(Int, a)] -> ([(sp, a)], [(lp, a)])
partitionStateLabelPreds si syi x = (statePairs, labelPairs)
    where
    statePairs = indicesToStatePreds syi stateIndices
    labelPairs = indicesToLabelPreds syi labelIndices
    (stateIndices, labelIndices) = partitionStateLabel si x

stateLabelInconsistent :: (Ord sp, Ord lp) => Ops s u -> SymbolInfo s u sp lp -> [(sp, Bool)] -> [(lp, Bool)] -> ST s (DDNode s u)
stateLabelInconsistent ops@Ops{..} SymbolInfo{..} statePairs labelPairs = do
    inconsistentState <- makeCube ops $ map (first getStates) statePairs
    inconsistentLabel <- makeCube ops $ map (first getLabels) labelPairs
    inconsistent      <- andDeref ops inconsistentState inconsistentLabel
    return inconsistent
    where
    getStates = getNode . fromJustNote "refineConsistency" . flip Map.lookup _statePreds
    getLabels = getNode . sel1 . fromJustNote "refineConsistency" . flip Map.lookup _labelPreds

stateLabelConsistent :: (Ord sp, Ord lp) => Ops s u -> SymbolInfo s u sp lp -> [(sp, Bool)] -> [(lp, Bool)] -> ST s (DDNode s u) 
stateLabelConsistent ops@Ops{..} SymbolInfo{..} cStatePreds cLabelPreds = do
    labelCube <- uncurry computeCube $ unzip $ concatMap func labelPreds'
    otherCube <- uncurry computeCube $ unzip $ zip otherEnabling (repeat False)
    res       <- andDeref ops labelCube otherCube
    return res
    where
    otherEnabling = map (getNode. snd . snd) $ filter (\(p, _) -> not $ p `elem` map fst cLabelPreds) $ Map.toList _labelPreds
    statePreds' = map (first $ fst . fromJustNote "refineConsistency" . flip Map.lookup _statePreds) cStatePreds
    labelPreds' = map (first $ fromJustNote "refineConsistency" . flip Map.lookup _labelPreds) cLabelPreds
    func ((lp, le), pol) = [(fst lp, pol), (fst le, True)]

