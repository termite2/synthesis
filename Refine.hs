{-# LANGUAGE RecordWildCards, ScopedTypeVariables #-}
module Refine where

import Control.Monad.ST.Lazy
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Arrow
import Data.List
import Control.Monad

import Safe

import CuddExplicitDeref as C
import CuddExplicitDeref (DDNode)

traceST :: String -> ST s ()
traceST = unsafeIOToST . putStrLn

data Ops s u = Ops {
    band, bor, bxor, bxnor, bimp, bnand, bnor :: DDNode s u -> DDNode s u -> ST s (DDNode s u),
    (.&), (.|), (.->)                         :: DDNode s u -> DDNode s u -> ST s (DDNode s u),
    bnot                                      :: DDNode s u -> DDNode s u,
    btrue, bfalse                             :: DDNode s u,
    bforall, bexists                          :: DDNode s u -> DDNode s u -> ST s (DDNode s u),
    leq                                       :: DDNode s u -> DDNode s u -> ST s Bool,
    makePrime                                 :: DDNode s u -> DDNode s u -> ST s (DDNode s u),
    largestCube                               :: DDNode s u -> ST s (DDNode s u),
    supportIndices                            :: DDNode s u -> ST s ([Int]),
    supportIndex                              :: DDNode s u -> Int -> ST s Bool,
    ithVar                                    :: Int -> ST s (DDNode s u),
    shift                                     :: [DDNode s u] -> [DDNode s u] -> DDNode s u -> ST s (DDNode s u),
    ref                                       :: DDNode s u -> ST s (),
    deref                                     :: DDNode s u -> ST s ()
}

constructOps :: STDdManager s u -> Ops s u
constructOps m = Ops {..}
    where
    band           = C.band    m
    bor            = C.bor     m
    bxor           = C.bxor    m
    bxnor          = C.bxnor   m
    bimp x y       = C.bor     m (C.bnot x) y
    bnand          = C.bnand   m
    bnor           = C.bnor    m
    (.&)           = C.band    m
    (.|)           = C.bor     m
    (.->) x y      = C.bor     m (C.bnot x) y
    bnot           = C.bnot     
    btrue          = C.bone    m
    bfalse         = C.bzero   m
    bforall        = C.bforall m
    bexists        = C.bexists m
    supportIndices = undefined m
    supportIndex   = undefined m
    ithvar         = C.bvar    m
    leq            = C.leq     m
    shift          = C.shift   m
    ref            = C.ref      
    deref          = C.deref   m

--TODO deref in below functions, especially the foldMs
removeVariables :: Ops s u -> [(DDNode s u, Int)] -> Section s u -> ST s (Section s u)
removeVariables Ops{..} nodeInds Section{..} = do
    let (vars'', inds'') = unzip nodeInds
        inds' = inds \\ inds''
        vars' = vars \\ vars''
    cube' <- foldM bexists cube vars''
    return $ Section cube' vars' inds'

addVariables :: Ops s u -> [(DDNode s u, Int)] -> Section s u -> ST s (Section s u)
addVariables Ops{..} nodeInds Section{..} = do
    let (vars'', inds'') = unzip nodeInds
        inds' = inds ++ inds''
        vars' = vars ++ vars''
    cube' <- foldM (.&) cube vars''
    return $ Section cube' vars' inds'
    
data Section s u = Section {
    cube :: DDNode s u,
    vars :: [DDNode s u],
    inds :: [Int]
}

type PredicateDB s u p = Map p (DDNode s u, Int)
emptyPredDB  = Map.empty
extractPreds = Map.keys
extractVars  = map snd . Map.toList

data RefineDynamic s u sp lp = RefineDynamic {
    trans              :: DDNode s u,
    consistentPlusCU   :: DDNode s u,
    consistentMinusCUL :: DDNode s u,
    consistentPlusCUL  :: DDNode s u,
    trackedState       :: Section s u,
    untrackedState     :: Section s u,
    label              :: Section s u,
    next               :: Section s u,
    nextAvlIndex       :: Int,
    untrackedPredsRev  :: Map Int sp,
    statePredsRev      :: Map Int sp,
    trackedPreds       :: Map sp (DDNode s u, Int),
    untrackedPreds     :: Map sp (DDNode s u, Int),
    labelPreds         :: Map lp (DDNode s u, Int)
}

data RefineStatic s u = RefineStatic {
    goal :: DDNode s u
}

data Abstractor s u sp lp = Abstractor {
    goalAbs :: 
        Ops s u -> 
        PredicateDB s u sp -> 
        Int -> 
        (PredicateDB s u sp, Int, ST s (DDNode s u)),
    updateAbs :: 
        Ops s u -> 
        --state predicate db
        PredicateDB s u sp -> 
        --untracked 
        PredicateDB s u sp ->
        --label
        PredicateDB s u lp -> 
        --Free var offset
        Int ->
        --Next state node, predicate being update pairs
        [(DDNode s u, sp)] -> 
        --((new untracked pred db, new label pred db, new offset, new state predicates, new label predicates), update function conjunction)
        ((PredicateDB s u sp, PredicateDB s u lp, Int, [(sp, (DDNode s u, Int))], [(lp, (DDNode s u, Int))]), ST s (DDNode s u))
}

data TheorySolver p = TheorySolver {
    check     :: [(p, Bool)] -> Bool,
    unsatCore :: [(p, Bool)] -> Maybe [(p, Bool)]
}

createCubeNodes :: Ops s u -> [Int] -> ST s (DDNode s u, [DDNode s u])
createCubeNodes = undefined

createSection :: Ops s u -> [Int] -> ST s (Section s u)
createSection ops inds = do
    (cube, nodes) <- createCubeNodes ops inds
    return $ Section {..}

createSection2 :: Ops s u -> [(DDNode s u, Int)] -> ST s (Section s u)
createSection2 = undefined

initialAbstraction :: Ops s u -> Abstractor s u sp lp -> ST s (RefineDynamic s u sp lp, RefineStatic s u)
initialAbstraction ops@Ops{..} Abstractor{..} = do
    let (statePredDB, endState, goalExpr) = goalAbs ops emptyPredDB 0 
        endNext = 2*endState
    next <- createSection ops [endState .. endNext-1]
    let ((untrackedPredDB, labelPredDB, endUntracked, _, _), transs) = updateAbs ops statePredDB emptyPredDB emptyPredDB endNext (zip (vars next) (extractPreds statePredDB))

    trans            <- transs

    let consistentPlusCU  = btrue
        consistentMinusCU = bfalse
        consistentPlusCUL = btrue

    trackedState      <- createSection2 ops $ extractVars statePredDB
    untrackedState    <- createSection2 ops $ extractVars untrackedPredDB
    label             <- createSection2 ops $ extractVars labelPredDB
    goal              <- goalExpr
    return (RefineDynamic {..}, RefineStatic {..})

--TODO take into account existence of next some state
cPre' :: Ops s u -> RefineDynamic s u sp lp -> DDNode s u -> ST s (DDNode s u)
cPre' Ops{..} RefineDynamic{..} target = do
    t0 <- shift (vars trackedState) (vars next) target
    t1 <- trans .-> t0
    deref t0
    t2 <- bforall (cube next) t1
    deref t1
    t3 <- consistentMinusCUL .& t2
    deref t2
    t4 <- bexists (cube label) t3
    deref t3
    t5 <- consistentPlusCU .-> t4
    deref t4
    return t5

cPre :: Ops s u -> RefineDynamic s u sp lp -> DDNode s u -> ST s (DDNode s u)
cPre (ops @ (Ops {..})) (rd @ (RefineDynamic {..})) target = do
    su <- cPre' ops rd target
    t6 <- bforall (cube untrackedState) su
    deref su
    return t6

fixedPoint :: Ops s u -> (DDNode s u -> ST s (DDNode s u)) -> DDNode s u -> ST s (DDNode s u)
fixedPoint (ops @ Ops {..}) func start = do
    res <- func start
    deref start 
    case (res==start) of --this is safe 
        True -> return start
        False -> fixedPoint ops func res
        
solveGame :: Ops s u -> RefineStatic s u -> RefineDynamic s u sp lp -> DDNode s u -> ST s (DDNode s u)
solveGame (ops@Ops{..}) (rs @ RefineStatic{..}) (rd @ RefineDynamic{..}) target = fixedPoint ops func target
    where
    func target = do
        t1 <- bor target goal
        res <- cPre ops rd t1
        deref t1
        return res

singleton x = [x]

findM :: Monad m => (a -> m Bool) -> [a] -> m a
findM f []     = error "findM: no matching items in list"
findM f (x:xs) = do
    res <- f x
    case res of 
        True  -> return x
        False -> findM f xs

--Variable promotion strategies
refineAny :: Ops s u -> RefineDynamic s u sp lp -> DDNode s u -> ST s (Maybe [Int])
refineAny Ops{..} RefineDynamic{..} newSU = (fmap (Just . singleton)) $ findM (supportIndex newSU) $ inds untrackedState

--TODO wrong. must find prime implicant wrt newSU
refineLeastPreds :: forall s u sp lp. Ops s u -> RefineDynamic s u sp lp -> DDNode s u -> ST s (Maybe [Int])
refineLeastPreds (Ops{..}) (RefineDynamic{..}) newSU 
    | newSU == bfalse = return Nothing
    | otherwise       = do
        ref newSU
        (size, vars, remaining) <- sizeVarsNext newSU
        (size, vars) <- doLoop size vars remaining
        return $ Just vars
    where
    sizeVarsNext :: DDNode s u -> ST s (Int, [Int], DDNode s u)
    sizeVarsNext remaining = do
        lc    <- largestCube remaining
        prime <- makePrime lc remaining
        deref remaining
        deref lc
        (size, vars) <- analyseCube prime
        nextRemaining <- band remaining $ bnot prime
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
        --TODO optimise below a lot
        untrackedCube <- bexists (cube trackedState) cube'
        support <- supportIndices untrackedCube
        deref untrackedCube
        return (length support, support)

pickUntrackedToPromote :: Ops s u -> RefineDynamic s u sp lp -> DDNode s u -> ST s (Maybe [Int])
pickUntrackedToPromote (ops@Ops{..}) rd win = do
    su    <- cPre' ops rd win
    newSU <- su .& bnot win
    deref su
    res <- refineLeastPreds ops rd newSU
    deref newSU
    return res

makePairs :: Ops s u -> [Int] -> ST s [(DDNode s u, Int)]
makePairs Ops{..} inds = sequence $ map func inds
    where
    func idx = do
        n <- ithVar idx
        return (n, idx)

insertList :: (Ord k) => [(k, v)] -> Map k v -> Map k v
insertList = flip $ foldl (flip $ uncurry Map.insert) 

deleteList :: (Ord k) => [k] -> Map k v -> Map k v
deleteList = flip $ foldl (flip Map.delete) 

--TODO deref foldMs
promoteUntracked :: (Ord lp, Ord sp) => Ops s u -> Abstractor s u sp lp -> RefineDynamic s u sp lp -> [Int] -> ST s (RefineDynamic s u sp lp)
promoteUntracked ops@Ops{..} Abstractor{..} rd@RefineDynamic{..} indices = do
    --look up the predicates to promote
    let refinePreds    = map (fromJustNote "promoteUntracked" . flip Map.lookup untrackedPredsRev) indices

    --create a section consisting of the new variables to promote
    toPromote          <- makePairs ops indices

    --create a section consisting of the newly allocated next states for the promoted variables
    nextPairs          <- makePairs ops [nextAvlIndex ..  nextAvlIndex + length indices - 1]
    let nextAvlIndex   = nextAvlIndex + length indices

    --compute the update functions
    let ((untrackedPredDB', labelPredDB', newOffset', newUPreds, newLPreds), predUpdates) = updateAbs ops trackedPreds untrackedPreds labelPreds nextAvlIndex $ zip (map fst nextPairs) refinePreds

    --update the transition relation
    predUpdates        <- predUpdates
    trans'             <- trans .& predUpdates
    deref predUpdates  
    deref trans

    --update the sections
    trackedState       <- addVariables    ops toPromote trackedState 
    untrackedState'    <- removeVariables ops toPromote untrackedState
    untrackedState     <- addVariables    ops (map snd newUPreds) untrackedState'
    label              <- addVariables    ops (map snd newLPreds) label
    next               <- addVariables    ops nextPairs next

    --update the predicate dbs
    let trackedPreds'   = deleteList refinePreds trackedPreds'
    let untrackedPreds' = insertList newUPreds $ deleteList refinePreds untrackedPreds
    let labelPreds'     = insertList newLPreds labelPreds
    
    --update the untracked preds reverse map
    let untrackedPredsRev' = insertList (zip indices refinePreds) $ deleteList indices untrackedPredsRev 

    --update the next available index
    let nextAvlIndex   = newOffset'

    --update the consistency relations
    --TODO need to allow for enabling variables
    consistentPlusCU   <- return consistentPlusCU   
    consistentMinusCUL <- return consistentMinusCUL 
    consistentPlusCUL  <- return consistentPlusCUL 

    return $ RefineDynamic {
        trans              = trans',
        consistentPlusCU   = consistentPlusCU,
        consistentMinusCUL = consistentMinusCUL,
        consistentPlusCUL  = consistentPlusCUL,
        trackedState       = trackedState,
        untrackedState     = untrackedState,
        label              = label,
        next               = next,
        nextAvlIndex       = nextAvlIndex,
        untrackedPredsRev  = untrackedPredsRev,
        trackedPreds       = trackedPreds',
        untrackedPreds     = untrackedPreds',
        labelPreds         = labelPreds'
    }

--TODO win must be next state
refineConsistency :: Ops s u -> RefineDynamic s u sp lp -> DDNode s u -> ST s (Maybe (RefineDynamic s u sp lp))
refineConsistency ops@Ops{..} rd@RefineDynamic{..} win = do
    t0 <- shift (vars trackedState) (vars next) win
    t1 <- trans .-> t0
    deref t0
    t2 <- bforall (cube next) t1
    deref t1
    t3 <- consistentPlusCUL .& t2
    deref t2
    t4 <- t3 .& bnot win
    deref t3
    case t4==bfalse of 
        True -> return Nothing
        False -> do
            t5 <- bexists (cube label) t4
            (t6, cubeSize) <- largestCube t5
            t7 <- makePrime t6 t5
            deref t5
            deref t6
            c <- presentVars t7 
            deref t7
            let preds = map (fst $ fromJustNote "refineConsistency" . flip Map.lookup statePredsRev) c
            case unsatCore preds of
                Just pairs -> do
                    deref t4
                    inconsistent <- cube pairs
                    consistentPlusCU'  <- consistentPlusCU .& bnot inconsistent
                    deref consistentPlusCU
                    consistentPlusCUL' <- consistentPlusCUL .& bnot inconsistent
                    deref consistentPlusCUL'
                    deref inconsistent
                    return $ Just $ rd {consistentPlusCU = consistentPlusCU', consistentPlusCUL = consistentPlusCUL'}
                Nothing -> do
                    (t6, cubeSize) <- largestCube t4
                    t7 <- makePrime t6 t4
                    deref t4
                    deref t6
                    c <- presentVars t7
                    deref t7
                    let preds = undefined
                    case unsatCore preds of
                        Just pairs -> do
                            inconsistent <- toBdd pairs
                            consistentPlusCUL' <- consistentPlusCUL .& bnot inconsistent
                            deref inconsistent
                            deref consistentPlusCUL
                            return $ Just $ rd {consistentPlusCUL = consistentPlusCUL'}
                        Nothing -> return Nothing

absRefineLoop :: STDdManager s u -> Abstractor s u sp lp -> ST s Bool
absRefineLoop m spec = do
    let ops@Ops{..} = constructOps m
    (rd, rs) <- initialAbstraction ops spec
    f <- bfalse
    refineLoop ops rs rd f
    where
        refineLoop :: Ops s u -> RefineStatic s u -> RefineDynamic s u sp lp -> DDNode s u -> ST s Bool
        refineLoop (ops@Ops{..}) rs = refineLoop'
            where 
            refineLoop' (rd@RefineDynamic{..}) lastWin = do
                winRegion <- solveGame ops rs rd lastWin
                deref lastWin --TODO maybe
                winning <- winRegion `leq` init
                case winning of
                    True -> do
                        deref winRegion
                        deref lastWin
                        return True
                    False -> do
                        res <- pickUntrackedToPromote ops rd winRegion
                        deref winRegion
                        case res of 
                            Just vars -> do
                                newRD <- promoteUntracked spec rd vars 
                                refineLoop' newRD
                            Nothing -> do
                                case refineConsistency ops rd winRegion of
                                    Nothing -> return False
                                    Just newRD -> refineLoop' newRD

