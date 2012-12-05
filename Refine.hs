{-# LANGUAGE RecordWildCards, ScopedTypeVariables, GADTs #-}
module Refine (absRefineLoop, VarInfo, GoalAbsRet(..), UpdateAbsRet(..), InitAbsRet(..), Abstractor(..), TheorySolver(..), EQuantRet(..), traceST) where

import Control.Monad.ST.Lazy
import Data.STRef.Lazy
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Arrow
import Data.List
import Control.Monad
import Data.List
import Data.Maybe
import Data.Tuple.All
import Data.Tuple
import Debug.Trace as T

import Safe

import qualified CuddExplicitDeref as C
import CuddExplicitDeref (DDNode, STDdManager)
import Util

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
    bite                                      :: DDNode s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u),
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
    checkKeys                                 :: ST s (),
    pickOneMinterm                            :: DDNode s u -> [DDNode s u] -> ST s (DDNode s u),
    checkZeroRef                              :: ST s (Int)
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
    pickOneMinterm         = C.pickOneMinterm   m
    checkZeroRef           = C.checkZeroRef     m

-- ==BDD utility functions==
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

-- ===BDD interpretation ===

listPrimeImplicants :: Ops s u -> [[(String, [Int])]] -> DDNode s u -> ST s [[[(String, [Int])]]]
listPrimeImplicants ops@Ops{..} varss trans = do
    pc <- primeCover ops trans
    mapM func pc
    where
    func prime = do
        mapM func2 varss
        where
        func2 section = interp ops section prime

interp :: Ops s u -> [(String, [Int])] -> DDNode s u -> ST s [(String, [Int])]
interp Ops{..} theList node = do
    st <- satCube node 
    return $ mapMaybe (func st) theList
    where
    func bits (name, idxs) 
        | all (==2) encoding = Nothing
        | otherwise = Just (name, (map b2IntLSF expanded))
        where
        encoding = map (bits !!) idxs
        expanded = allComb $ map func encoding
        func 0 = [False]
        func 1 = [True]
        func 2 = [False, True]

formatPrimeImplicants :: [[[(String, [Int])]]] -> String
formatPrimeImplicants = concat . intersperse "\n" . map func 
    where
    func = concat . intersperse " -- " . map func2
        where
        func2 = concat . intersperse ", " . map (uncurry func3)
            where
            func3 name values = name ++ ": " ++ show values

stateInterp :: Ops s u -> [(String, [Int])] -> DDNode s u -> ST s [(String, [Int])]
stateInterp Ops{..} theList node = do
    st <- satCube node
    return $ map (func st) theList
    where
    func bits (name, idxs) = (name, (map b2IntLSF expanded))
        where
        encoding = map (bits !!) idxs
        expanded = allComb $ map func encoding
        func 0 = [False]
        func 1 = [True]
        func 2 = [False, True]

formatStateInterp :: [(String, [Int])] -> String
formatStateInterp = concat . intersperse ", " . map (uncurry func)
    where
    func name values = name ++ ": " ++ show values

-- ===Graph drawing ===

toDot' :: (Show sp, Show lp, Ord sp) => Ops s u -> RefineDynamic s u o sp lp -> RefineStatic s u -> DDNode s u -> String -> ST s ()
toDot' ops@Ops{..} RefineDynamic{..} RefineStatic{..} rel fname = do
    setVarMap (vars trackedState) (vars next) 
    initCube <- nodesToCube $ map fst $ Map.elems initPreds ++ concat (Map.elems initVars)
    initNoState <- bexists (cube trackedState) initCube
    initStates <- bexists initNoState init
    let theMap = Map.filterWithKey f stateVars
            where
            f k v = not $ null $ (map snd v) `intersect` (inds trackedState)
    let theSPMap = Map.filterWithKey f statePreds
            where
            f k v = snd v `elem` (inds trackedState)
    let theUMap = Map.filterWithKey f stateVars
            where
            f k v = not $ null $ (map snd v) `intersect` (inds untrackedState)
    let theupMap = Map.filterWithKey f statePreds
            where
            f k v = snd v `elem` (inds untrackedState)
    graph <- toDot ops theSPMap theMap theupMap theUMap labelPreds labelVars (vars trackedState) (vars next) (cube trackedState) (cube untrackedState) (cube label) (cube next) goal initStates rel
    unsafeIOToST $ writeFile fname graph

toDot :: (Show sp, Show lp) => Ops s u -> Map sp (VarInfo s u) -> Map String [VarInfo s u] -> Map sp (VarInfo s u) -> Map String [VarInfo s u] -> Map lp (VarInfo s u, VarInfo s u) -> Map String ([VarInfo s u], VarInfo s u) -> [DDNode s u] -> [DDNode s u] -> DDNode s u -> DDNode s u -> DDNode s u -> DDNode s u -> DDNode s u -> DDNode s u -> DDNode s u -> ST s String
toDot ops@Ops{..} spMap svMap upMap uvMap lpMap lvMap stateVars nextVars stateCube untrackedCube labelCube nextCube goal init trans = do
    let stateNextVars = stateVars ++ nextVars
    stateNextCube <- stateCube .& nextCube
    untrackedLabelCube <- untrackedCube .& labelCube
    transitions <- concPart ops stateNextVars stateNextCube untrackedLabelCube trans
    culnTuples <- mapM split transitions
    transSection <- mapM (uncurryN draw) culnTuples
    goalNodes <- allMinterms ops stateVars goal
    gs <- mapM (goalFunc "[color=\"Blue\"]") goalNodes
    let goalSection = concat $ intersperse ";\n" gs
    initNodes <- allMinterms ops stateVars init
    is <- mapM (goalFunc "[style=\"dashed\"]") initNodes
    let initSection = concat $ intersperse ";\n" is 
    check "toDot1" ops
    return $ "digraph trans {\n" ++ concat (intersperse ";\n" transSection) ++ "\n" ++ goalSection ++ "\n" ++ initSection ++ "}\n"
    where
        goalFunc attrib node = do
            let theList = map (second (map snd)) (Map.toList svMap) ++ map (show *** (singleton . snd)) (Map.toList spMap)
            si <- stateInterp ops theList node
            return $ "\"" ++ (formatStateInterp si) ++ "\" " ++ attrib
        split (currentNext, untrackedLabel) = do
            s  <- bexists nextCube currentNext
            n' <- bexists stateCube currentNext
            n  <- mapVars n'
            labCubes <- primeCover ops untrackedLabel
            labs <- mapM lfunc labCubes
            return (s, labs, n)
        lfunc ulc = do
            u  <- bexists labelCube ulc
            l  <- bexists untrackedCube ulc
            return (u, l)
        draw c uls n = do
            let theList = map (second (map snd)) (Map.toList svMap) ++ map (show *** (singleton . snd)) (Map.toList spMap)
            si <- stateInterp ops theList c
            ni <- stateInterp ops theList n
            labs <- mapM doLabs uls
            return $ "\"" ++ formatStateInterp si ++ "\" -> \"" ++ formatStateInterp ni ++ "\" [label=\"" ++ concat (intersperse "; " labs) ++ "\"]"
            where
            doLabs (u, l) = do
                let theList = map (second (map snd)) (Map.toList uvMap) ++ map (show *** (singleton . snd)) (Map.toList upMap)
                li <- labelInterp l
                ui <- stateInterp ops theList u
                return $ (formatStateInterp ui) ++ " -- " ++ li
            labelInterp node = do
                let a = map (second (map snd *** snd)) (Map.toList lvMap) ++ map (show *** (singleton . snd *** snd)) (Map.toList lpMap)
                st <- satCube node
                return $ concat $ intersperse ", " $ map (func st) a
                where
                func bits (name, (idxs, en)) = name ++ ": " ++ show (map b2IntLSF expanded) ++ name ++ ".en: " ++ show (map b2IntLSF eexpanded)
                    where
                    encoding = map (bits !!) idxs
                    expanded = allComb $ map func encoding
                    eencoding = bits !! en
                    eexpanded = allComb [func eencoding]
                    func 0 = [False]
                    func 1 = [True]
                    func 2 = [False, True]

-- === Public input data structures===
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
    updateExpr       :: [DDNode s u],
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

data EQuantRet sp s u o = EQuantRet {
    equantStatePreds :: Map sp (VarInfo s u),
    equantStateVars  :: Map String [VarInfo s u],
    equantEnd        :: Int,
    equantExpr       :: DDNode s u,
    equantAbsState   :: o
}

--Theory solving
data TheorySolver sp lp s u o = TheorySolver {
    unsatCoreState      :: [(sp, Bool)] -> Maybe [(sp, Bool)],
    unsatCoreStateLabel :: [(sp, Bool)] -> [(lp, Bool)] -> Maybe ([(sp, Bool)], [(lp, Bool)]),
    eQuant              :: [(sp, Bool)] -> [(lp, Bool)] -> 
                           Ops s u -> 
                           --init pred map
                           Map sp (VarInfo s u) -> 
                           --init var map
                           Map String [VarInfo s u] -> 
                           --state pred db
                           Map sp (VarInfo s u) -> 
                           --state var db
                           Map String [VarInfo s u] -> 
                           --free var offset
                           Int -> 
                           --Abstractor state
                           o -> 
                           --return 
                           ST s (EQuantRet sp s u o)
}

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

data Variable p s u where
    Predicate :: p -> VarInfo s u -> Variable p s u
    NonAbs    :: String -> [VarInfo s u] -> Variable p s u

instance Eq p => Eq (Variable p s u) where
    (Predicate p _) == (Predicate q _) = p==q
    (NonAbs n _)    == (NonAbs m _)    = n==m
    _               == _               = False

instance (Show p) => Show (Variable p s u) where
    show (Predicate p v) = "Predicate variable: " ++ show p ++ ", index: " ++ show (snd v)
    show (NonAbs n v)    = "Non-abstracted variable: " ++ show n ++ ", indices: " ++ show (map snd v)

getPredicates :: [(Variable p s u, a)] -> [(p, a)]
getPredicates = mapMaybe func 
    where
    func (Predicate p _, x) = Just (p, x)
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
    stateRev           :: Map Int (Variable sp s u),
    labelRev           :: Map Int (Variable lp s u, Bool),
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
constructStatePredRev :: [(sp, VarInfo s u)] -> Map Int (Variable sp s u)
constructStatePredRev pairs = Map.fromList $ map (uncurry func) pairs
    where
    func pred vi = (idx vi, Predicate pred vi)

constructStateVarRev  :: [(String, [VarInfo s u])] -> Map Int (Variable sp s u)
constructStateVarRev pairs = Map.fromList $ concatMap (uncurry func) pairs
    where
    func name vars = map func' vars
        where
        func' var = (idx var, NonAbs name vars)

constructLabelPredRev :: [(lp, (VarInfo s u, VarInfo s u))] -> Map Int (Variable lp s u, Bool)
constructLabelPredRev pairs = Map.fromList $ concatMap (uncurry func) pairs
    where
    func pred (vi, evi) = [(idx vi, (Predicate pred vi, True)), (idx evi, (Predicate pred evi, False))]

constructLabelVarRev  :: [(String, ([VarInfo s u], VarInfo s u))] -> Map Int (Variable lp s u, Bool)
constructLabelVarRev pairs = Map.fromList $ concatMap (uncurry func) pairs
    where
    func name (vi, evi) = (idx evi, (NonAbs name vi, False)) : map func' vi
        where
        func' var = (idx var, (NonAbs name vi, True))

format :: [(String, String)] -> String
format = concat . map ('\t' :) . intersperse "\n" . map (uncurry (\x y -> x ++ ": " ++ y))

format2 :: [String] -> String
format2 = concat . map ('\t' :) . intersperse "\n"

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
    putStrLn $ "Init preds: \n"                 ++ format (map (show *** show . snd) $ Map.toList initPreds)
    putStrLn $ "Init vars: \n"                  ++ format (map (show *** show . map snd) $ Map.toList initVars)
    putStrLn $ "State and untracked preds: "    ++ format2 (map show (Map.keys statePreds))
    putStrLn $ "State and untracked vars: "     ++ format2 (map show (Map.keys stateVars))
    putStrLn $ "label preds: "                  ++ format2 (map show (Map.keys labelPreds))
    putStrLn $ "label vars: "                   ++ format2 (map show (Map.keys labelVars))
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

--check msg ops = unsafeIOToST (putStrLn ("checking bdd consistency" ++ msg)) >> debugCheck ops >> checkKeys ops
check msp ops = return ()

asterixs = "*******************************************"

assign :: Int -> [(a, [b])] -> ([(a, [Int])], Int)
assign offset []       = ([], offset)
assign offset ((nm, vars) : rst) = ((nm, take (length vars) [offset..]) : rest, end)
    where (rest, end) = assign (offset + length vars) rst

assignPreds :: Int -> [(a, b)] -> ([(a, Int)], Int)
assignPreds offset [] = ([], offset)
assignPreds offset ((nm, var) : rst) = ((nm, offset) : rest, end)
    where (rest, end) = assignPreds (offset + 1) rst

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

--Create an initial abstraction and set up the data structures
initialAbstraction :: (Show sp, Show lp, Ord sp, Ord lp) => Ops s u -> Abstractor s u o sp lp -> o -> ST s (RefineDynamic s u o sp lp, RefineStatic s u)
initialAbstraction ops@Ops{..} Abstractor{..} abstractorState = do
    check "initialAbstraction1" ops
    --abstract init
    InitAbsRet {..}     <- initAbs ops 0 abstractorState
    check "initialAbstraction2" ops
    traceST "*******************************************\n"
    traceST $ "Abstraction of Init: \nState Preds: \n" ++ format (map (show *** (show . snd)) $ Map.toList initStatePreds) ++ "\nState Vars: \n" ++ format (map (show *** (show . map (show . snd))) $ Map.toList initStateVars)
    traceST "******************************************\n\n"
    --abstract the goal
    GoalAbsRet {..}     <- goalAbs ops initStatePreds initStateVars Map.empty Map.empty initOffset initAbsState 
    check "initialAbstraction3" ops
    traceST "*****************************************\n"
    traceST $ "Abstraction of Goal: \nStatePreds: \n" ++ format (map (show *** (show . snd)) $ Map.toList goalStatePreds) ++ "\nState vars: \n" ++ format (map (show *** (show . map (show . snd))) $ Map.toList goalStateVars)
    traceST "****************************************\n\n"
    let
        (goalPreds', ni) = assignPreds endGoalState (map (second idx) (Map.toList goalStatePreds))
        (goalVars', nni) = assign ni (map (second (map idx)) (Map.toList goalStateVars))
        endStateAndNext  = nni
    goalPreds <- sequence $ map (func . second ithVar) goalPreds'
    goalVars  <- sequence $ map (func . second (sequence . map ithVar)) goalVars'
    --get the abstract update functions for the goal predicates and variables
    traceST "***************************************\n"
    traceST $ "calling update on predicates: " ++ show (map fst goalPreds) ++ " and variables: " ++ show (map fst goalVars)
    UpdateAbsRet {..}   <- updateAbs ops initStatePreds initStateVars goalStatePreds goalStateVars Map.empty Map.empty endStateAndNext goalAbsState goalPreds goalVars
    updateExprConj' <- conj ops updateExpr
    mapM deref updateExpr
    updateExprConj  <- doEnVars ops updateExprConj' $ map (fst *** fst) $ Map.elems updateLabelPreds
    deref updateExprConj'
    traceST $ "Abstraction of variable updates: \nState and untracked preds after update: " ++ format (map (show *** (show . snd)) $ Map.toList updateStatePreds) ++ "\nVars: " ++ format (map (show *** (show . map (show . snd))) $ Map.toList updateStateVars)
    traceST $ "\nLabel preds after update: " ++ format (map (show *** (show . snd . fst)) $ Map.toList updateLabelPreds) ++ "\nVars: " ++ format (map (show *** (show . map (show . snd) . fst)) $ Map.toList updateLabelVars)
    traceST "***************************************\n\n"
    --create the consistency constraints
    let consistentPlusCU   = btrue
        consistentPlusCUL  = btrue
    ref consistentPlusCU
    ref consistentPlusCUL
    consistentMinusCUL <- conj ops $ map (bnot . fst . snd) $ Map.elems updateLabelPreds
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
            trans           = updateExprConj, 
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

refineStrategy = refineAny

refineAny :: Ops s u -> RefineDynamic s u o sp lp -> DDNode s u -> ST s (Maybe [Int])
refineAny Ops{..} RefineDynamic{..} newSU = do
    si <- supportIndices newSU
    let untrackedInds = si `intersect` inds untrackedState
    return $ case untrackedInds of
        []  -> Nothing
        x:_ -> Just [x]

refineFirstPrime :: Ops s u -> RefineDynamic s u o sp lp -> DDNode s u -> ST s (Maybe [Int])
refineFirstPrime Ops{..} RefineDynamic{..} newSU = do
    (lc, sz) <- largestCube newSU
    prime    <- makePrime lc newSU
    deref lc
    si       <- supportIndices prime
    deref prime
    let untrackedInds = si `intersect` inds untrackedState
    return $ case untrackedInds of
        [] -> Nothing
        x  -> Just x

--Refine the least number of untracked state predicates possible to make progress
refineLeastPreds :: forall s u o sp lp. Ops s u -> RefineDynamic s u o sp lp -> DDNode s u -> ST s (Maybe [Int])
refineLeastPreds ops@Ops{..} RefineDynamic{..} newSU 
    | newSU == bfalse = return Nothing
    | otherwise       = do
        ref newSU
        (size, vars, remaining) <- sizeVarsNext newSU
        (size, vars) <- doLoop size vars remaining
        check "after doLoop" ops
        return $ Just vars
    where
    sizeVarsNext :: DDNode s u -> ST s (Int, [Int], DDNode s u)
    sizeVarsNext remaining = do
        check "before sizeVarsNext" ops
        (lc, sz) <- largestCube remaining
        prime <- makePrime lc newSU
        deref lc
        (size, vars) <- analyseCube prime
        nextRemaining <- band remaining $ bnot prime
        deref remaining
        deref prime
        check "after sizeVarsNext" ops
        return (size, vars, nextRemaining)
    doLoop :: Int -> [Int] -> DDNode s u -> ST s (Int, [Int])
    doLoop size vars remaining 
        | remaining == bfalse = return (size, vars)
        | otherwise           = do
            (size', vars', remaining') <- sizeVarsNext remaining
            if (size' < size) then doLoop size' vars' remaining' else doLoop size vars remaining'
    analyseCube :: DDNode s u -> ST s (Int, [Int])
    analyseCube cube' = do
        check "before analyseCube" ops
        untrackedCube <- bexists (cube trackedState) cube'
        support <- supportIndices untrackedCube
        deref untrackedCube
        check "after analyseCube" ops
        return (length support, support)

pickUntrackedToPromote :: Ops s u -> RefineDynamic s u o sp lp -> RefineStatic s u -> DDNode s u -> ST s (Maybe [Int])
pickUntrackedToPromote ops@Ops{..} rd@RefineDynamic{..} RefineStatic{..} win = do
    traceST "Picking untracked to promote"
    hasOutgoings <- bexists (cube next) trans
    win' <- win .| goal
    su    <- cPre' ops rd hasOutgoings win'
    deref hasOutgoings
    newSU <- su .& bnot win
    deref win'
    deref su
    check "before refineLeastPreds" ops
    res <- refineStrategy ops rd newSU
    check "after refineLeastPreds" ops
    deref newSU
    return res

makePairs :: Ops s u -> [Int] -> ST s [(DDNode s u, Int)]
makePairs Ops{..} inds = sequence $ map func inds
    where
    func idx = do
        n <- ithVar idx
        return (n, idx)

--Promote untracked state variables to full state variables so that we can make progress towards the goal. Does not refine the consistency relations.
promoteUntracked :: (Ord lp, Ord sp, Show sp, Show lp) => Ops s u -> Abstractor s u o sp lp -> RefineDynamic s u o sp lp -> [Int] -> ST s (RefineDynamic s u o sp lp)
promoteUntracked ops@Ops{..} Abstractor{..} rd@RefineDynamic{..} indices = do
    --look up the predicates to promote
    let refineVars    = nub $ map (fromJustNote "promoteUntracked: untracked indices not in stateRev" . flip Map.lookup stateRev) indices
    traceST $ "Promoting: " ++ show refineVars

    --create a section consisting of the new variables to promote
    let toPromoteVars' = mapMaybe func refineVars 
            where
            func (Predicate p _) = Nothing
            func (NonAbs n v)    = Just (n, v)

    let toPromotePreds' = mapMaybe (uncurry func) $ zip indices refineVars
            where
            func idx (Predicate p v) = Just (p, v)
            func _   (NonAbs _ _)    = Nothing

    let allRefineVars = concat (map snd toPromoteVars') ++ map snd toPromotePreds'

    let (toPromoteVars, ni)             = assign nextAvlIndex toPromoteVars'
    let (toPromotePreds, nextAvlIndex') = assignPreds ni toPromotePreds'

    toPromotePreds <- sequence $ map (func . second ithVar) toPromotePreds
    toPromoteVars  <- sequence $ map (func . second (sequence . map ithVar)) toPromoteVars

    let nextIndices = [nextAvlIndex .. nextAvlIndex' - 1]
    traceST $ "Adding next indices: " ++ show nextIndices
    nextPairs <- sequence $ map (func . (id &&& ithVar)) nextIndices

    --compute the update functions
    UpdateAbsRet {..}  <- updateAbs ops initPreds initVars statePreds stateVars labelPreds labelVars nextAvlIndex' abstractorState toPromotePreds toPromoteVars

    updateExprConj' <- conj ops updateExpr
    traceST $  "update synopsys: " ++ bddSynopsis ops (head updateExpr)
    --toDot' ops rd (RefineStatic bfalse bfalse) updateExprConj' "promoteu.dot"
    mapM deref updateExpr
    updateExprConj  <- doEnVars ops updateExprConj' $ map (fst *** fst) $ Map.elems updateLabelPreds
    deref updateExprConj'

    --update the transition relation
    trans'             <- trans .& updateExprConj
    deref updateExprConj
    deref trans

    let newUntracked = Map.elems (updateStatePreds Map.\\ statePreds) ++ concat (Map.elems (updateStateVars Map.\\ stateVars))
    let newLabel     = concatMap pairToList (Map.elems (updateLabelPreds Map.\\ labelPreds)) ++ concatMap (uncurry (flip (:))) (Map.elems (updateLabelVars Map.\\ labelVars))

    --update the sections
    trackedState       <- addVariables    ops allRefineVars trackedState 
    untrackedState'    <- removeVariables ops allRefineVars untrackedState
    untrackedState     <- addVariables    ops newUntracked  untrackedState'
    label              <- addVariables    ops newLabel label
    next               <- addVariables    ops (map swap nextPairs) next

    --update the untracked preds reverse map
    let stateRev'       = constructStatePredRev (Map.toList updateStatePreds) `Map.union` constructStateVarRev (Map.toList updateStateVars)

    consistentMinusCUL'' <- conj ops $ map (bnot . fst . snd) $ Map.elems $ updateLabelPreds Map.\\ labelPreds
    consistentMinusCUL'  <- consistentMinusCUL .& consistentMinusCUL''
    deref consistentMinusCUL''
    deref consistentMinusCUL

    --deref newEnFalse

    let enablingVars' = map (idx . snd) (Map.elems updateLabelPreds) ++ map (idx . snd) (Map.elems updateLabelVars)

    let labelRev' = constructLabelPredRev (Map.toList updateLabelPreds) `Map.union` constructLabelVarRev (Map.toList updateLabelVars)

    let rd = RefineDynamic {
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
        statePreds         = updateStatePreds,
        stateVars          = updateStateVars,
        labelPreds         = updateLabelPreds,
        labelVars          = updateLabelVars,
        enablingVars       = enablingVars', 
        labelRev           = labelRev',
        abstractorState    = updateAbsState,
        ..
    }

    --toDot' ops rd (RefineStatic bfalse bfalse) (head updateExpr) "premote.dot"
    --toDot' ops rd (RefineStatic bfalse bfalse) (head updateExpr) "promote.dot"
    --toDot' ops rd (RefineStatic bfalse bfalse) trans' "promotee.dot"

    return rd


--Refine one of the consistency relations so that we make progress. Does not promote untracked state.
refineConsistency :: (Ord sp, Ord lp, Show sp, Show lp) => Ops s u -> TheorySolver sp lp s u o -> RefineDynamic s u o sp lp -> RefineStatic s u -> DDNode s u -> ST s (Maybe (RefineDynamic s u o sp lp))
refineConsistency ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} win = do
    check "refineConsistency start" ops
    win' <- win .| goal
    t0 <- mapVars win'
    t2 <- liftM bnot $ andAbstract (cube next) trans (bnot t0)
    deref t0
    t3 <- consistentPlusCUL .& t2
    deref t2
    hasOutgoings <- bexists (cube next) trans
    tt3 <- hasOutgoings .& t3
    --deref hasOutgoings
    deref t3
    traceST "***************************"
    traceST "Consistency refinement"
    t4 <- tt3 .& bnot win
    check "refineConsistency end1" ops
    --Alive : win', hasOutgoings, tt3, t4
    case t4==bfalse of 
        True  -> do
            --no refinement of consistency relations will make progress
            --there are no <c, u, l> tuples that are winning with the overapproximation of consistentCUL
            traceST "no consistency refinement possible"
            mapM deref [win', hasOutgoings, tt3, t4]
            check "refineConsistency1" ops
            return Nothing
        False -> do
            check "refineConsistency start2" ops
            --There may be a refinement
            --extract a <s, u> pair that will make progress if one exists
            traceST "consistency refinement may be possible"
            t5 <- bexists (cube label) t4
            deref t4
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
            check "refineConsistency end2" ops
            --Alive : win', hasOutgoings, tt3 
            case unsatCoreState preds of
                Just pairs -> do
                    --consistentPlusCU can be refined
                    traceST "refining consistentPlusCU"
                    mapM deref [win', hasOutgoings, tt3]
                    inconsistent <- makeCube ops $ map (first (node . fromJustNote "refineConsistency" . flip Map.lookup statePreds)) pairs
                    consistentPlusCU'  <- consistentPlusCU .& bnot inconsistent
                    deref consistentPlusCU
                    consistentPlusCUL' <- consistentPlusCUL .& bnot inconsistent
                    deref consistentPlusCUL'
                    deref inconsistent
                    check "refineConsistency2" ops
                    return $ Just $ rd {consistentPlusCU = consistentPlusCU', consistentPlusCUL = consistentPlusCUL'}
                Nothing -> do
                    traceST "consistentPlusCU could not be refined"
                    --consistentPlusCU cannot be refined but maybe consistentPlusCUL or consistentMinusCUL can be
                    cpr <- cPre' ops rd hasOutgoings win'
                    mapM deref [win', hasOutgoings]
                    t4 <- tt3 .& bnot cpr
                    mapM deref [tt3, cpr]
                    --Alive :t4
                    case t4==bfalse of
                        True -> do
                            traceST "consistentPlusCUL could not be refined"
                            deref t4
                            check "refineConsistency3" ops
                            return Nothing
                        False -> do
                            check "refineConsistency start3" ops
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
                            traceST $ "label preds for solver: " ++ show cLabelPreds
                            check "refineConsistency end3" ops
                            --Alive : nothing
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
                                    check "refineConsistency4" ops
                                    refineConsistency ops ts (rd {consistentPlusCUL = consistentPlusCUL'}) rs win
                                Nothing -> do
                                    --the (s, u, l) tuple is consistent so add this to consistentMinusCUL
                                    traceST "predicates are consistent. refining consistentMinusCUL..."
                                    EQuantRet {..} <- eQuant cStatePreds cLabelPreds ops initPreds initVars statePreds stateVars nextAvlIndex abstractorState

                                    let statePreds' = map (first $ fst . fromJustNote "refineConsistency" . flip Map.lookup statePreds) cStatePreds
                                        labelPreds' = map (first $ fromJustNote "refineConsistency" . flip Map.lookup labelPreds) cLabelPreds

                                    --stateCube <- uncurry computeCube $ unzip statePreds'
                                    let func ((lp, le), pol) = [(fst lp, pol), (fst le, True)]
                                    labelCube <- uncurry computeCube $ unzip $ concatMap func labelPreds'

                                    --consistentCube' <- stateCube .& labelCube
                                    consistentCube  <- labelCube .& equantExpr
                                    mapM deref [labelCube, equantExpr]

                                    consistentMinusCUL'  <- consistentMinusCUL .| consistentCube
                                    deref consistentCube
                                    deref consistentMinusCUL

                                    let newUntracked = Map.elems (equantStatePreds Map.\\ statePreds) ++ concat (Map.elems (equantStateVars Map.\\ stateVars))
                                    untrackedState' <- addVariables ops newUntracked untrackedState

                                    let statePredsRev  = constructStatePredRev $ Map.toList equantStatePreds
                                        stateVarsRev   = constructStateVarRev  $ Map.toList equantStateVars
                                        stateRev'      = Map.union statePredsRev stateVarsRev
                        
                                    check "refineConsistency5" ops
                                    return $ Just $ rd {
                                        consistentMinusCUL = consistentMinusCUL', 
                                        untrackedState     = untrackedState',
                                        nextAvlIndex       = equantEnd,
                                        stateRev           = stateRev',
                                        statePreds         = equantStatePreds,
                                        stateVars          = equantStateVars,
                                        abstractorState    = equantAbsState
                                    }

--The abstraction-refinement loop
absRefineLoop :: forall s u o sp lp. (Ord sp, Ord lp, Show sp, Show lp) => STDdManager s u -> Abstractor s u o sp lp -> TheorySolver sp lp s u o -> o -> ST s Bool
absRefineLoop m spec ts abstractorState = do
    let ops@Ops{..} = constructOps m
    (rd, rs) <- initialAbstraction ops spec abstractorState
    traceST "Refinement state after initial abstraction: " 
    traceST $ "Goal is: " ++ (bddSynopsis ops $ goal rs)
    traceST $ "Init is: " ++ (bddSynopsis ops $ Refine.init rs)
    reff <- newSTRef (0 :: Int)
    check "after initialAbstractions" ops
    refineLoop reff ops rs rd bfalse
    where
        refineLoop :: STRef s Int -> Ops s u -> RefineStatic s u -> RefineDynamic s u o sp lp -> DDNode s u -> ST s Bool
        refineLoop reff ops@Ops{..} rs@RefineStatic{..} = refineLoop'
            where 
            refineLoop' rd@RefineDynamic{..} lastWin = do
                check "start refine loop" ops
                dumpState rd
                num <- readSTRef reff
                modifySTRef reff (+1)
                setVarMap (vars trackedState) (vars next) 
                check "before solve game" ops
                winRegion <- solveGame ops rs rd lastWin
                deref lastWin
                traceST "Game solved"
                winning   <- init `leq` winRegion 
                check "after solve game" ops
                --Alive: winRegion, rd, rs
                case winning of
                    True -> do
                        traceST "winning"
                        deref winRegion
                        check "absRefineLoop1" ops
                        refs <- checkZeroRef 
                        traceST $ show refs
                        return True
                    False -> do
                        traceST "Not winning without further refinement"
                        res <- refineConsistency ops ts rd rs winRegion 
                        case res of
                            Just newRD -> do
                                traceST "Refined consistency relations. Re-solving..."
                                refineLoop' newRD winRegion
                            Nothing -> do
                                traceST "Could not refine consistency relations. Attempting to refine untracked state variables"
                                check "before pick untracked" ops
                                res <- pickUntrackedToPromote ops rd rs winRegion
                                check "after pick untracked" ops
                                case res of 
                                    Just vars -> do
                                        traceST "Found untracked variables to promote. Promoting them..."
                                        newRD <- promoteUntracked ops spec rd vars 
                                        refineLoop' newRD winRegion
                                    Nothing -> do
                                        traceST "Game is not winning"
                                        deref winRegion
                                        check "absRefineLoop2" ops
                                        refs <- checkZeroRef
                                        traceST $ show refs
                                        return False

