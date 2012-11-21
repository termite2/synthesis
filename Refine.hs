{-# LANGUAGE RecordWildCards, ScopedTypeVariables, GADTs #-}
module Refine where

import Control.Monad.ST.Lazy
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Arrow
import Data.List
import Control.Monad
import Data.List
import Data.Maybe
import Data.Tuple.All

import Safe

import qualified CuddExplicitDeref as C
import CuddExplicitDeref (DDNode, STDdManager)

-- ===Utility functions===
{-# NOINLINE traceST #-}
traceST :: String -> ST s ()
traceST = unsafeIOToST . putStrLn

singleton x = [x]

findM :: Monad m => (a -> m Bool) -> [a] -> m a
findM f []     = error "findM: no matching items in list"
findM f (x:xs) = do
    res <- f x
    case res of 
        True  -> return x
        False -> findM f xs

pairToList :: (a, a) -> [a]
pairToList (x, y) = [x, y]

insertList :: (Ord k) => [(k, v)] -> Map k v -> Map k v
insertList = flip $ foldl (flip $ uncurry Map.insert) 

deleteList :: (Ord k) => [k] -> Map k v -> Map k v
deleteList = flip $ foldl (flip Map.delete) 

--BDD operations record instead of a class
data Ops s u = Ops {
    band, bor, bxor, bxnor, bimp, bnand, bnor :: DDNode s u -> DDNode s u -> ST s (DDNode s u),
    (.&), (.|), (.->)                         :: DDNode s u -> DDNode s u -> ST s (DDNode s u),
    bnot                                      :: DDNode s u -> DDNode s u,
    btrue, bfalse                             :: DDNode s u,
    bforall, bexists                          :: DDNode s u -> DDNode s u -> ST s (DDNode s u),
    andAbstract, xorExistAbstract             :: DDNode s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u),
    leq                                       :: DDNode s u -> DDNode s u -> ST s Bool,
    makePrime                                 :: DDNode s u -> DDNode s u -> ST s (DDNode s u),
    largestCube                               :: DDNode s u -> ST s (DDNode s u, Int),
    supportIndices                            :: DDNode s u -> ST s ([Int]),
    ithVar                                    :: Int -> ST s (DDNode s u),
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
    checkKeys                                 :: ST s ()
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
    bnot                   = C.bnot              
    btrue                  = C.bone             m
    bfalse                 = C.bzero            m
    bforall                = flip $ C.bforall   m
    bexists                = flip $ C.bexists   m
    andAbstract c f g      = C.andAbstract      m f g c
    xorExistAbstract c f g = C.xorExistAbstract m f g c
    supportIndices         = C.supportIndices   m
    ithVar                 = C.bvar             m
    leq                    = C.leq              m
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

-- ===Data structures for keeping track of abstraction state===

data Section s u = Section {
    cube :: DDNode s u,
    vars :: [DDNode s u],
    inds :: [Int]
}

data RefineStatic s u = RefineStatic {
    goal :: DDNode s u,
    init :: DDNode s u
}

data Variable p v where
    Predicate :: p -> Variable p v
    NonAbs    :: String -> v -> Variable p v

instance (Show p, Show v) => Show (Variable p v) where
    show (Predicate p) = "Predicate variable: " ++ show p
    show (NonAbs n v)  = "Non-abstracted variable: " ++ show n

getPredicate :: Variable p v -> Maybe p
getPredicate (Predicate p) = Just p
getPredicate (NonAbs n v)  = Nothing

getPredicates :: [(Variable p v, a)] -> [(p, a)]
getPredicates = mapMaybe func 
    where
    func (Predicate p, x) = Just (p, x)
    func _                = Nothing

type VarInfo s u = (DDNode s u, Int)
node :: VarInfo s u -> DDNode s u
node = fst
idx  :: VarInfo s u -> Int
idx  = snd

data RefineDynamic s u o sp lp = RefineDynamic {
    --relations
    trans              :: DDNode s u,
    consistentPlusCU   :: DDNode s u,
    consistentMinusCUL :: DDNode s u,
    consistentPlusCUL  :: DDNode s u,
    --sections
    trackedState       :: Section s u,
    untrackedState     :: Section s u,
    label              :: Section s u,
    next               :: Section s u,
    nextAvlIndex       :: Int,
    --mappings from index to variable/predicate
    stateRev           :: Map Int (Variable sp [DDNode s u]),
    labelRev           :: Map Int (Variable lp [DDNode s u], Bool),
    --below maps are used for update function compilation and constructing
    initPreds          :: Map sp (VarInfo s u),
    initVars           :: Map String [VarInfo s u],
    statePreds         :: Map sp (VarInfo s u),
    stateVars          :: Map String [VarInfo s u],
    labelPreds         :: Map lp (VarInfo s u, VarInfo s u),
    labelVars          :: Map String ([VarInfo s u], VarInfo s u),
    --All enabling vars in existance
    enablingVars       :: [Int],
    --abstractor state
    abstractorState    :: o
}

--convenience functions for constructing the reverse mappings
constructStatePredRev :: [(sp, VarInfo s u)] -> Map Int (Variable sp [DDNode s u])
constructStatePredRev pairs = Map.fromList $ map (uncurry func) pairs
    where
    func pred vi = (idx vi, Predicate pred)

constructStateVarRev  :: [(String, [VarInfo s u])] -> Map Int (Variable sp [DDNode s u])
constructStateVarRev pairs = Map.fromList $ concatMap (uncurry func) pairs
    where
    func name vars = map func' vars
        where
        func' var = (idx var, NonAbs name (map node vars))

constructLabelPredRev :: [(lp, (VarInfo s u, VarInfo s u))] -> Map Int (Variable lp [DDNode s u], Bool)
constructLabelPredRev pairs = Map.fromList $ concatMap (uncurry func) pairs
    where
    func pred (vi, evi) = [(idx vi, (Predicate pred, True)), (idx evi, (Predicate pred, False))]

constructLabelVarRev  :: [(String, ([VarInfo s u], VarInfo s u))] -> Map Int (Variable lp [DDNode s u], Bool)
constructLabelVarRev pairs = Map.fromList $ concatMap (uncurry func) pairs
    where
    func name (vi, evi) = (idx evi, (NonAbs name (map node vi), False)) : map func' vi
        where
        func' var = (idx var, (NonAbs name (map node vi), True))

format :: [(String, String)] -> String
format = concat . map ('\t' :) . intersperse "\n" . map (uncurry (\x y -> x ++ ": " ++ y))

--debug dump
dumpState :: (Show sp, Show lp) => RefineDynamic s u o sp lp -> ST s ()
dumpState RefineDynamic{..} = unsafeIOToST $ do
    putStrLn $ "******************Refinement state***********************"
    putStrLn $ "State inds: "                   ++ show (inds trackedState)
    putStrLn $ "Next inds: "                    ++ show (inds next)
    putStrLn $ "Untracked inds: "               ++ show (inds untrackedState)
    putStrLn $ "label inds: "                   ++ show (inds label)
    putStrLn $ "Nxt avl ixd: "                  ++ show nextAvlIndex
    putStrLn $ "stateRev: \n"                   ++ format (map (show *** show) $ Map.toList stateRev)
    putStrLn $ "labelRev: \n"                   ++ format (map (show *** show) $ Map.toList labelRev)
    putStrLn $ "Init preds: \n"                 ++ format (map (show *** show) $ Map.toList initPreds)
    putStrLn $ "Init vars: \n"                  ++ format (map (show *** show) $ Map.toList initVars)
    putStrLn $ "State and untracked preds: "    ++ show (Map.keys statePreds)
    putStrLn $ "State and untracked vars: "     ++ show (Map.keys stateVars)
    putStrLn $ "label preds: "                  ++ show (Map.keys labelPreds)
    putStrLn $ "label vars: "                   ++ show (Map.keys labelVars)
    putStrLn $ "enabling vars: "                ++ show enablingVars
    putStrLn $ "*********************************************************\n"

-- ===Solve an abstracted and compiled game===

cPre' :: Ops s u -> RefineDynamic s u o sp lp -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cPre' Ops{..} RefineDynamic{..} hasOutgoings target = do
    t0 <- mapVars target
    t1 <- liftM bnot $ andAbstract (cube next) trans (bnot t0)
    deref t0
    t2 <- hasOutgoings .& t1
    deref t1
    t3 <- consistentMinusCUL .& t2
    deref t2
    t4 <- bexists (cube label) t3
    deref t3
    t5 <- consistentPlusCU .-> t4
    deref t4
    return t5

cPre :: Ops s u -> RefineDynamic s u o sp lp -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cPre (ops @ (Ops {..})) (rd @ (RefineDynamic {..})) hasOutgoings target = do
    su <- cPre' ops rd hasOutgoings target
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
        
solveGame :: Ops s u -> RefineStatic s u -> RefineDynamic s u o sp lp -> DDNode s u -> ST s (DDNode s u)
solveGame (ops@Ops{..}) (rs @ RefineStatic{..}) (rd @ RefineDynamic{..}) target = do 
    hasOutgoings <- bexists (cube next) trans
    fp <- fixedPoint ops (func hasOutgoings) target
    deref hasOutgoings
    return fp
    where
    func hasOutgoings target = do
        traceST "solveGame: iteration"
        t1 <- target .| goal
        res <- cPre ops rd hasOutgoings t1
        deref t1
        return res

-- ===Abstraction refinement===

removeVariables :: Ops s u -> [(DDNode s u, Int)] -> Section s u -> ST s (Section s u)
removeVariables Ops{..} nodeInds Section{..} = do
    let (vars'', inds'') = unzip nodeInds
        inds' = inds \\ inds''
        vars' = vars \\ vars''
    cube'' <- nodesToCube vars'' --foldM bexists cube vars''
    cube'  <- bexists cube'' cube
    deref cube''
    deref cube
    return $ Section cube' vars' inds'

addVariables :: Ops s u -> [(DDNode s u, Int)] -> Section s u -> ST s (Section s u)
addVariables Ops{..} nodeInds Section{..} = do
    let (vars'', inds'') = unzip nodeInds
        inds' = inds ++ inds''
        vars' = vars ++ vars''
    cube'' <- nodesToCube vars''
    cube' <- cube .& cube''
    deref cube''
    deref cube
    return $ Section cube' vars' inds'

data GoalAbsRet s u o sp = GoalAbsRet {
    goalStatePreds :: Map sp (VarInfo s u),
    goalStateVars  :: Map String [VarInfo s u],
    endGoalState   :: Int,
    goalExpr       :: DDNode s u,
    goalAbsState   :: o
}

data UpdateAbsRet s u o sp lp = UpdateAbsRet {
    updateStatePreds :: Map sp (VarInfo s u),
    updateStateVars  :: Map String [VarInfo s u],
    updateLabelPreds :: Map lp (VarInfo s u, VarInfo s u),
    updateLabelVars  :: Map String ([VarInfo s u], VarInfo s u),
    updateOffset     :: Int,
    --predicate variable, enabling variable
    updateExpr       :: DDNode s u,
    updateAbsState   :: o
}

data InitAbsRet s u o sp = InitAbsRet {
    initStatePreds :: Map sp (VarInfo s u),
    initStateVars  :: Map String [VarInfo s u],
    initExpr       :: DDNode s u,
    initOffset     :: Int,
    initAbsState   :: o
}

--Input to the refinement algorithm. Represents the spec.
data Abstractor s u o sp lp = Abstractor {
    goalAbs :: 
        Ops s u -> 
        --init pred map
        Map sp (VarInfo s u) -> 
        --init var map 
        Map String [VarInfo s u] -> 
        --state pred db
        Map sp (VarInfo s u) -> 
        --variable DB
        Map String [VarInfo s u] -> 
        --free var offset
        Int -> 
        --Abstractor state
        o -> 
        --return
        ST s (GoalAbsRet s u o sp),
    updateAbs :: 
        Ops s u -> 
        --init pred map 
        Map sp (VarInfo s u) -> 
        --init var map 
        Map String [VarInfo s u] -> 
        --state predicate db
        Map sp (VarInfo s u) -> 
        --state variable db
        Map String [VarInfo s u] -> 
        --label
        Map lp (VarInfo s u, VarInfo s u) -> 
        --Label var db
        Map String ([VarInfo s u], VarInfo s u) -> 
        --Free var offset
        Int ->
        --Abstractor state
        o -> 
        --Predicates being updated, next state node pairs
        [(sp, DDNode s u)] -> 
        --State variables being updated, next state nodes pairs
        [(String, [DDNode s u])] -> 
        --return
        ST s (UpdateAbsRet s u o sp lp),
    initAbs :: 
        Ops s u -> 
        --Free var offset
        Int -> 
        --Abstractor state
        o -> 
        --return
        ST s (InitAbsRet s u o sp)
}

--Theory solving
data TheorySolver sp lp = TheorySolver {
    unsatCoreState      :: [(sp, Bool)] -> Maybe [(sp, Bool)],
    unsatCoreStateLabel :: [(sp, Bool)] -> [(lp, Bool)] -> Maybe ([(sp, Bool)], [(lp, Bool)])
}

createCubeNodes :: Ops s u -> [Int] -> ST s (DDNode s u, [DDNode s u])
createCubeNodes Ops{..} inds = do
    nodes <- mapM ithVar inds 
    cube  <- nodesToCube nodes
    return (cube, nodes)

createSection :: Ops s u -> [Int] -> ST s (Section s u)
createSection ops inds = do
    (cube, vars) <- createCubeNodes ops inds
    return $ Section {..}

createSection2 :: Ops s u -> [(DDNode s u, Int)] -> ST s (Section s u)
createSection2 Ops{..} pairs = do
    let (vars, inds) = unzip pairs
    cube <- nodesToCube vars
    return $ Section {..}

func :: Monad m => (a, m b) -> m (a, b)
func (x, y) = do
    y <- y
    return (x, y)

check ops = debugCheck ops >> checkKeys ops

asterixs = "*******************************************"

--Create an initial abstraction and set up the data structures
initialAbstraction :: (Show sp, Show lp, Ord sp, Ord lp) => Ops s u -> Abstractor s u o sp lp -> o -> ST s (RefineDynamic s u o sp lp, RefineStatic s u)
initialAbstraction ops@Ops{..} Abstractor{..} abstractorState = do
    check ops
    --abstract init
    InitAbsRet {..}     <- initAbs ops 0 abstractorState
    check ops
    traceST "*******************************************\n"
    traceST $ "Abstraction of Init: \nState Preds: \n" ++ format (map (show *** (show . snd)) $ Map.toList initStatePreds) ++ "\nState Vars: \n" ++ format (map (show *** (show . map (show . snd))) $ Map.toList initStateVars)
    traceST "******************************************\n\n"
    --abstract the goal
    GoalAbsRet {..}     <- goalAbs ops initStatePreds initStateVars Map.empty Map.empty initOffset initAbsState 
    check ops
    traceST "*****************************************\n"
    traceST $ "Abstraction of Goal: \nStatePreds: \n" ++ format (map (show *** (show . snd)) $ Map.toList goalStatePreds) ++ "\nState vars: \n" ++ format (map (show *** (show . map (show . snd))) $ Map.toList goalStateVars)
    traceST "****************************************\n\n"
    let
        numStateVars    = length $ Map.elems goalStatePreds ++ concat (Map.elems goalStateVars)
        endStateAndNext = endGoalState + numStateVars
        goalPreds       = map (second ((+ endGoalState) . idx)) $ Map.toList goalStatePreds
        goalVars        = map (second (map $ (+ endGoalState) . idx)) $ Map.toList goalStateVars
    goalPreds <- sequence $ map (func . second ithVar) goalPreds 
    goalVars  <- sequence $ map (func . second (sequence . map ithVar)) goalVars
    --get the abstract update functions for the goal predicates and variables
    traceST "***************************************\n"
    traceST $ "calling update on predicates: " ++ show (map fst goalPreds) ++ " and variables: " ++ show (map fst goalVars)
    UpdateAbsRet {..}   <- updateAbs ops initStatePreds initStateVars goalStatePreds goalStateVars Map.empty Map.empty endStateAndNext goalAbsState goalPreds goalVars
    traceST $ "Abstraction of variable updates: \nState and untracked preds after update: " ++ format (map (show *** (show . snd)) $ Map.toList updateStatePreds) ++ "\nVars: " ++ format (map (show *** (show . map (show . snd))) $ Map.toList updateStateVars)
    traceST $ "\nLabel preds after update: " ++ format (map (show *** (show . snd . fst)) $ Map.toList updateLabelPreds) ++ "\nVars: " ++ format (map (show *** (show . map (show . snd) . fst)) $ Map.toList updateLabelVars)
    traceST "***************************************\n\n"
    --create the consistency constraints
    let consistentPlusCU   = btrue
        consistentMinusCUL = bfalse
        consistentPlusCUL  = btrue
    --create the sections
    trackedState       <- createSection2 ops $ 
        Map.elems goalStatePreds ++ concat (Map.elems goalStateVars)
    untrackedState     <- createSection2 ops $ 
        Map.elems (updateStatePreds Map.\\ goalStatePreds) ++ concat (Map.elems (updateStateVars Map.\\ goalStateVars))
    label              <- createSection2 ops $ 
        concatMap pairToList (Map.elems updateLabelPreds) ++ concatMap (uncurry (flip (:))) (Map.elems updateLabelVars)
    next               <- createSection ops [endGoalState .. endStateAndNext-1]
    --construct the reverse mappings and enabling variables list
    let statePredsRev  = constructStatePredRev $ Map.toList updateStatePreds
        stateVarsRev   = constructStateVarRev  $ Map.toList updateStateVars
        stateRev       = Map.union statePredsRev stateVarsRev
        labelPredsRev  = constructLabelPredRev $ Map.toList updateLabelPreds
        labelVarsRev   = constructLabelVarRev  $ Map.toList updateLabelVars
        labelRev       = Map.union labelPredsRev labelVarsRev
        enablingVars   = map (idx . snd) (Map.elems updateLabelPreds) ++ map (idx . snd) (Map.elems updateLabelVars)
    --construct the RefineDynamic and RefineStatic
    let rd = RefineDynamic {
            trans           = updateExpr, 
            nextAvlIndex    = updateOffset, 
            statePreds      = updateStatePreds, 
            stateVars       = updateStateVars, 
            labelPreds      = updateLabelPreds, 
            labelVars       = updateLabelVars, 
            abstractorState = updateAbsState,
            initPreds       = initStatePreds,
            initVars        = initStateVars,
            ..
        }
        rs = RefineStatic {
            goal = goalExpr,
            init = initExpr
        }
    return (rd, rs)

--Variable promotion strategies

{-
refineAny :: Ops s u -> RefineDynamic s u sp lp -> DDNode s u -> ST s (Maybe [Int])
refineAny Ops{..} RefineDynamic{..} newSU = (fmap (Just . singleton)) $ findM (supportIndex newSU) $ inds untrackedState
-}

--Refine the least number of untracked state predicates possible to make progress
refineLeastPreds :: forall s u o sp lp. Ops s u -> RefineDynamic s u o sp lp -> DDNode s u -> ST s (Maybe [Int])
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
        (lc, sz) <- largestCube remaining
        prime <- makePrime lc newSU
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
        untrackedCube <- bexists (cube trackedState) cube'
        support <- supportIndices untrackedCube
        deref untrackedCube
        return (length support, support)

pickUntrackedToPromote :: Ops s u -> RefineDynamic s u o sp lp -> RefineStatic s u -> DDNode s u -> ST s (Maybe [Int])
pickUntrackedToPromote ops@Ops{..} rd@RefineDynamic{..} RefineStatic{..} win = do
    hasOutgoings <- bexists (cube next) trans
    win' <- win .| goal
    su    <- cPre' ops rd hasOutgoings win'
    deref hasOutgoings
    traceST $ "Asdfasdf"
    newSU <- su .& bnot win'
    error "halt"
    deref win'
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

--Promote untracked state variables to full state variables so that we can make progress towards the goal. Does not refine the consistency relations.
promoteUntracked :: (Ord lp, Ord sp) => Ops s u -> Abstractor s u o sp lp -> RefineDynamic s u o sp lp -> [Int] -> ST s (RefineDynamic s u o sp lp)
promoteUntracked ops@Ops{..} Abstractor{..} rd@RefineDynamic{..} indices = do
    --look up the predicates to promote
    let refinePreds    = map (fromJustNote "promoteUntracked" . flip Map.lookup stateRev) indices

    --create a section consisting of the new variables to promote
    toPromote          <- makePairs ops indices

    --create a section consisting of the newly allocated next states for the promoted variables
    nextPairs          <- makePairs ops [nextAvlIndex ..  nextAvlIndex + length indices - 1]
    let nextAvlIndex   = nextAvlIndex + length indices

    --compute the update functions
    UpdateAbsRet {..}  <- updateAbs ops initPreds initVars statePreds stateVars labelPreds labelVars nextAvlIndex abstractorState undefined undefined 

    --update the transition relation
    trans'             <- trans .& updateExpr
    deref updateExpr  
    deref trans

    --update the sections
    trackedState       <- addVariables    ops toPromote trackedState 
    untrackedState'    <- removeVariables ops toPromote untrackedState
    untrackedState     <- addVariables    ops undefined untrackedState'
    label              <- addVariables    ops undefined label
    next               <- addVariables    ops nextPairs next

    --update the predicate dbs
    let statePreds'     = insertList undefined statePreds
    let labelPreds'     = insertList undefined labelPreds
    
    --update the untracked preds reverse map
    let stateRev'       = insertList (zip indices refinePreds) stateRev

    --update the consistency relations
    consistentPlusCU   <- return consistentPlusCU   
    consistentPlusCUL  <- return consistentPlusCUL 

    newEnFalse <- makeCube ops $ zip undefined (repeat False)
    consistentMinusCUL' <- consistentMinusCUL .& newEnFalse
    deref consistentMinusCUL'
    deref newEnFalse

    let enablingVars' = enablingVars ++ undefined

    let labelRev' = insertList (concatMap func undefined) labelRev
            where func (lp, ((_, i), (_, e))) = [(i, (lp, True)), (e, (lp, False))]

    return $ RefineDynamic {
        trans              = trans',
        consistentPlusCU   = consistentPlusCU,
        consistentMinusCUL = consistentMinusCUL',
        consistentPlusCUL  = consistentPlusCUL,
        trackedState       = trackedState,
        untrackedState     = untrackedState,
        label              = label,
        next               = next,
        nextAvlIndex       = updateOffset,
        stateRev           = stateRev',
        statePreds         = statePreds',
        labelPreds         = labelPreds',
        enablingVars       = enablingVars', 
        labelRev           = undefined,
        abstractorState    = updateAbsState
    }

presentVars :: Ops s u -> DDNode s u -> ST s [(Int, Bool)]
presentVars Ops{..} x = do
    res <- satCube x
    return $ map (second (/=0)) $ filter ((/=2) . snd) $ zip [0..] res

makeCube :: Ops s u -> [(DDNode s u, Bool)] -> ST s (DDNode s u)
makeCube Ops{..} = uncurry computeCube . unzip

makeCubeIdx :: Ops s u -> [(Int, Bool)] -> ST s (DDNode s u)
makeCubeIdx Ops{..} list = do
    let (idxs, phases) = unzip list
    nodes <- mapM ithVar idxs
    computeCube nodes phases 

bddSynopsis Ops{..} node = case node==bfalse of
                               True -> "Zero"
                               False -> case node==btrue of
                                            True -> "True"
                                            False -> "Non-constant"

--Refine one of the consistency relations so that we make progress. Does not promote untracked state.
--TODO: check for existence of label first
refineConsistency :: (Ord sp, Ord lp, Show sp, Show lp) => Ops s u -> TheorySolver sp lp -> RefineDynamic s u o sp lp -> RefineStatic s u -> DDNode s u -> ST s (Maybe (RefineDynamic s u o sp lp))
refineConsistency ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} win = do
    win' <- win .| goal
    t0 <- mapVars win'
    t1 <- trans .-> t0
    deref t0
    t2 <- bforall (cube next) t1
    deref t1
    t3 <- consistentPlusCUL .& t2
    deref t2
    hasOutgoings <- bexists (cube next) trans
    tt3 <- hasOutgoings .& t3
    deref hasOutgoings
    deref t3
    t4 <- tt3 .& bnot win'
    deref win'
    deref tt3
    case t4==bfalse of 
        True  -> do
            --no refinement of consistency relations will make progress
            --there are no <c, u, l> tuples that are winning with the overapproximation of consistentCUL
            traceST "no consistency refinement possible"
            check ops
            return Nothing
        False -> do
            --There may be a refinement
            --extract a <s, u> pair that will make progress if one exists
            traceST "consistency refinement may be possible"
            t5 <- bexists (cube label) t4
            (t6, sz) <- largestCube t5
            t7 <- makePrime t6 t5
            deref t5
            deref t6
            c <- presentVars ops t7 
            deref t7
            let stateUntrackedProgress = map (first $ fromJustNote "refineConsistency1" . flip Map.lookup stateRev) c
            traceST $ "Tuple that will make progress: " ++ show stateUntrackedProgress
            let preds = getPredicates stateUntrackedProgress
            traceST $ "Preds being checked for consistency: " ++ show preds
            case unsatCoreState preds of
                Just pairs -> do
                    --consistentPlusCU can be refined
                    traceST "refining consistentPlusCU"
                    deref t4
                    inconsistent <- makeCube ops $ map (first (node . fromJustNote "refineConsistency" . flip Map.lookup statePreds)) pairs
                    consistentPlusCU'  <- consistentPlusCU .& bnot inconsistent
                    deref consistentPlusCU
                    consistentPlusCUL' <- consistentPlusCUL .& bnot inconsistent
                    deref consistentPlusCUL'
                    deref inconsistent
                    check ops
                    return $ Just $ rd {consistentPlusCU = consistentPlusCU', consistentPlusCUL = consistentPlusCUL'}
                Nothing -> do
                    --consistentPlusCU cannot be refined but maybe consistentPlusCUL or consistentMinusCUL can be
                    traceST "consistentPlusCU could not be refined"
                    (t6, sz) <- largestCube t4
                    t7 <- makePrime t6 t4
                    deref t4
                    deref t6
                    c <- presentVars ops t7
                    deref t7
                    let (stateIndices, labelIndices) = partition (\(p, x) -> elem p (inds trackedState) || elem p (inds untrackedState)) c
                    let cStatePreds = getPredicates $ map (first $ fromJustNote "refineConsistency2" . flip Map.lookup stateRev) stateIndices
                    let cLabelPreds = getPredicates $ catMaybes $ map (uncurry func) labelIndices
                            where
                            func idx polarity = case fromJustNote "refineConsistency3" $ Map.lookup idx labelRev of
                                (_, False)   -> Nothing
                                (pred, True) -> Just (pred, polarity)
                    traceST $ "state preds for solver: " ++ show cStatePreds
                    traceST $ "label preds for solver: " ++ show cLabelPreds
                    case unsatCoreStateLabel cStatePreds cLabelPreds of
                        Just (statePairs, labelPairs) -> do
                            --consistentPlusCUL can be refined
                            traceST "refining consistentPlusCUL"
                            inconsistentState <- makeCube ops $ map (first (node . fromJustNote "refineConsistency" . flip Map.lookup statePreds)) statePairs
                            inconsistentLabel <- makeCube ops $ map (first (node . sel1 . fromJustNote "refineConsistency" . flip Map.lookup labelPreds)) labelPairs
                            inconsistent <- inconsistentState .& inconsistentLabel
                            deref inconsistentState
                            deref inconsistentLabel
                            consistentPlusCUL' <- consistentPlusCUL .& bnot inconsistent
                            deref inconsistent
                            deref consistentPlusCUL
                            check ops
                            refineConsistency ops ts (rd {consistentPlusCUL = consistentPlusCUL'}) rs win
                        Nothing -> do
                            --the (s, u, l) tuple is consistent so add this to consistentMinusCUL
                            traceST "refining consistentMinusCUL"
                            consistentMinusCUL'' <- makeCubeIdx ops c --TODO wrong
                            let enTrue  = zip (map ((+1) . fst) labelIndices) (repeat True)
                                enFalse = zip (enablingVars \\ (map ((+1) . fst) labelIndices)) (repeat False)
                            enablePreds          <- makeCubeIdx ops $ enTrue ++ enFalse
                            consistentMinusCUL'  <- consistentMinusCUL'' .& enablePreds
                            deref consistentMinusCUL'
                            deref enablePreds
                            check ops
                            return $ Just $ rd {consistentMinusCUL = consistentMinusCUL'}

--The abstraction-refinement loop
absRefineLoop :: forall s u o sp lp. (Ord sp, Ord lp, Show sp, Show lp) => STDdManager s u -> Abstractor s u o sp lp -> TheorySolver sp lp -> o -> ST s Bool
absRefineLoop m spec ts abstractorState = do
    let ops@Ops{..} = constructOps m
    (rd, rs) <- initialAbstraction ops spec abstractorState
    traceST "Refinement state after initial abstraction: " 
    dumpState rd
    traceST $ "Goal is: " ++ (bddSynopsis ops $ goal rs)
    traceST $ "Init is: " ++ (bddSynopsis ops $ Refine.init rs)
    refineLoop ops rs rd bfalse
    where
        refineLoop :: Ops s u -> RefineStatic s u -> RefineDynamic s u o sp lp -> DDNode s u -> ST s Bool
        refineLoop ops@Ops{..} rs@RefineStatic{..} = refineLoop'
            where 
            refineLoop' rd@RefineDynamic{..} lastWin = do
                setVarMap (vars trackedState) (vars next) 
                winRegion <- solveGame ops rs rd lastWin
                traceST "Game solved"
                winning   <- init `leq` winRegion 
                case winning of
                    True -> do
                        traceST "winning"
                        deref winRegion
                        return True
                    False -> do
                        traceST "Not winning without further refinement"
                        res <- refineConsistency ops ts rd rs winRegion 
                        case res of
                            Just newRD -> do
                                traceST "Refined consistency relations. Resolving"
                                refineLoop' newRD winRegion
                            Nothing -> do
                                traceST "Could not refine consistency relations. Attempting to refine untracked state variables"
                                res <- pickUntrackedToPromote ops rd rs winRegion
                                case res of 
                                    Just vars -> do
                                        traceST "Found untracked variables to promote. Promoting them..."
                                        newRD <- promoteUntracked ops spec rd vars 
                                        refineLoop' newRD winRegion
                                    Nothing -> do
                                        traceST "Game is not winning"
                                        deref winRegion
                                        --Below line is a hack to make
                                        --haskell print things because for
                                        --some reason it doesnt
                                        error "asdf"
                                        return False

{-
--Top level interface
absRefine :: (Ord sp, Ord lp, Show sp, Show lp) => STDdManager s u -> Abstractor s u sp lp -> UnsatCore p -> (sp -> p) -> (lp -> p) -> (p -> sp) -> (p -> sp) -> ST s Bool
absRefine m spec uc ps pl sp lp = absRefineLoop m spec $ TheorySolver ucs ucl
    where
    ucs = undefined
    ucl = undefined
-}
