{-# LANGUAGE RecordWildCards, PolymorphicComponents, GADTs, TemplateHaskell #-}

module Interface where

import Control.Monad.ST.Lazy
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.State
import Control.Arrow
import Data.List as List

import Control.Lens

import BddRecord

--types that appear in the backend syntax tree
data BAPred sp lp where
    StatePred :: sp -> BAPred sp lp
    LabelPred :: lp -> BAPred sp lp
    OutPred   :: lp -> BAPred sp lp
    deriving (Show, Eq, Ord)

data BAVar where
    StateVar :: String -> Int -> BAVar 
    LabelVar :: String -> Int -> BAVar
    OutVar   :: String -> Int -> BAVar
    deriving (Show, Eq, Ord)

--Operations that are given to the backend for compilation. 
data VarOps pdb p v s u = VarOps {
    getPred :: p -> StateT pdb (ST s) (DDNode s u),
    getVar  :: v -> StateT pdb (ST s) [DDNode s u],
    withTmp :: forall a. (DDNode s u -> StateT pdb (ST s) a) -> StateT pdb (ST s) a
}

--Generic utility functions
findWithDefaultM :: (Monad m, Ord k) => (v -> v') -> k -> Map k v -> m v' -> m v'
findWithDefaultM modF key theMap func = maybe func (return . modF) $ Map.lookup key theMap 

findWithDefaultProcessM :: (Monad m, Ord k) => (v -> v') -> k -> Map k v -> m v' -> (v -> m ()) -> m v'
findWithDefaultProcessM modF key theMap funcAbsent funcPresent = maybe funcAbsent func $ Map.lookup key theMap
    where
    func v = do
        funcPresent v
        return $ modF v

modifyM :: Monad m => (s -> m s) -> StateT s m ()
modifyM f = get >>= (lift . f) >>= put

infixl 1 =>=
(=>=) :: Monad m => m a -> (a -> m ()) -> m a
a =>= b = do
    res <- a
    b res
    return res

monadOut :: Monad m => (a, m b) -> m (a, b)
monadOut (x, y) = do
    y <- y
    return (x, y)

--Variable type
type VarInfo s u = (DDNode s u, Int)
getNode = fst
getIdx = snd

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

--Symbol table
data SymbolInfo s u sp lp = SymbolInfo {
    --below maps are used for update function compilation and constructing
    _initPreds          :: Map sp (VarInfo s u),
    _initVars           :: Map String [VarInfo s u],
    _statePreds         :: Map sp (VarInfo s u),
    _stateVars          :: Map String [VarInfo s u],
    _labelPreds         :: Map lp (VarInfo s u, VarInfo s u),
    _labelVars          :: Map String [VarInfo s u],
    _outcomePreds       :: Map lp (VarInfo s u),
    _outcomeVars        :: Map String [VarInfo s u],
    --mappings from index to variable/predicate
    _stateRev           :: Map Int (Variable sp s u),
    _labelRev           :: Map Int (Variable lp s u, Bool)
}

makeLenses ''SymbolInfo
initialSymbolTable = SymbolInfo Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty

--Sections
data SectionInfo s u = SectionInfo {
    _trackedCube   :: DDNode s u,
    _trackedNodes  :: [DDNode s u],
    _trackedInds   :: [Int],
    _untrackedCube :: DDNode s u,
    _untrackedInds :: [Int],
    _labelCube     :: DDNode s u,
    _outcomeCube   :: DDNode s u,
    _nextCube      :: DDNode s u,
    _nextNodes     :: [DDNode s u]
}

makeLenses ''SectionInfo
initialSectionInfo Ops{..} = SectionInfo btrue [] [] btrue [] btrue btrue btrue []

--Variable/predicate database
data DB s u sp lp = DB {
    _symbolTable :: SymbolInfo s u sp lp,
    _sections    :: SectionInfo s u,
    _avlOffset   :: Int
}

makeLenses ''DB
initialDB ops = DB initialSymbolTable (initialSectionInfo ops) 0

--Generic variable allocations
alloc :: Ops s u -> StateT (DB s u sp lp) (ST s) (DDNode s u, Int)
alloc Ops{..} = do
    offset <- use avlOffset
    res    <- lift $ ithVar offset
    avlOffset += 1
    return (res, offset)

allocN :: Ops s u -> Int -> StateT (DB s u sp lp) (ST s) ([DDNode s u], [Int])
allocN Ops{..} size = do
    offset <- use avlOffset
    let indices = take size $ iterate (+1) offset
    res    <- lift $ mapM ithVar indices
    avlOffset += size
    return (res, indices)

--Do the variable allocation and symbol table tracking
addToCube :: Ops s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
addToCube Ops{..} add cb = do
    res <- add .& cb
    deref cb
    return res

addToCubeDeref :: Ops s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
addToCubeDeref Ops{..} add cb = do
    res <- add .& cb
    deref add
    deref cb
    return res

--initial state helpers
allocInitPred :: Ord sp => Ops s u -> sp -> StateT (DB s u sp lp) (ST s) (DDNode s u)
allocInitPred ops p = liftM fst $ do
    val <- alloc ops 
    symbolTable . initPreds %= Map.insert p val
    return val

allocInitVar  :: Ops s u -> String -> Int -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocInitVar ops v size = liftM fst $ do
    val <- allocN ops size
    symbolTable . initVars %= Map.insert v (uncurry zip val)
    return val

-- === goal helpers ===
data NewVars s u sp = NewVars {
    _allocatedStatePreds :: [(sp, DDNode s u)],
    _allocatedStateVars  :: [(String, [DDNode s u])]
}

makeLenses ''NewVars

data GoalState s u sp lp = GoalState {
    _nv :: NewVars s u sp,
    _db :: DB s u sp lp,
    _oi :: [(Int, Int)]
}

makeLenses ''GoalState

listInsertDrop :: (Ord a) => [a] -> [(a, a)] -> [a]
listInsertDrop list items = listInsertDrop' list
    where
    mp = Map.fromList items
    st = Set.fromList $ map snd items
    listInsertDrop' [] = []
    listInsertDrop' (x:xs) = case Map.lookup x mp of
        Nothing -> case Set.member x st of
            False -> x : listInsertDrop' xs
            True  -> listInsertDrop' xs
        Just y -> x : y : listInsertDrop' xs

doOrder :: Ops s u -> [(Int, Int)] -> ST s ()
doOrder Ops {..} pairs = do
    size <- readSize
    perm <- mapM readInvPerm [0..size-1]
    let order = listInsertDrop perm pairs
    shuffleHeap order 
    mapM_ (\pos -> makeTreeNode pos 2 0) (map fst pairs)

liftToGoalState :: StateT (DB s u sp lp) (ST s) a -> StateT (GoalState s u sp lp) (ST s) a
liftToGoalState (StateT func) = StateT $ \st -> do
    (res, st') <- func (_db st) 
    return (res, GoalState (_nv st) st' (_oi st))

allocStatePred :: Ord sp => Ops s u -> sp -> StateT (GoalState s u sp lp) (ST s) (DDNode s u)
allocStatePred ops pred = liftM fst $ liftToGoalState (alloc ops) =>= uncurry (addPredToState ops pred)

allocStateVar :: Ops s u -> String -> Int -> StateT (GoalState s u sp lp) (ST s) [DDNode s u]
allocStateVar ops name size = liftM fst $ liftToGoalState (allocN ops size) =>= uncurry (addVarToState ops name)

type Update a = a -> a

addStatePredSymbol :: Ord sp => sp -> DDNode s u -> Int -> Update (SymbolInfo s u sp lp)
addStatePredSymbol pred var idx = 
    statePreds %~ Map.insert pred (var, idx) >>> 
    stateRev   %~ Map.insert idx (Predicate pred (var, idx))

addStateVarSymbol :: String -> [DDNode s u] -> [Int] -> Update (SymbolInfo s u sp lp)
addStateVarSymbol name vars idxs = 
    stateVars %~ Map.insert name (zip vars idxs) >>>
    stateRev  %~ flip (foldl func) idxs 
        where func theMap idx = Map.insert idx (NonAbs name (zip vars idxs)) theMap

addPredToStateSection :: Ops s u -> sp -> DDNode s u -> Int -> StateT (GoalState s u sp lp) (ST s) ()
addPredToStateSection ops@Ops{..} pred var idx = do
    db . sections . trackedNodes %= (var :) 
    db . sections . trackedInds  %= (idx :)
    modifyM $ db . sections . trackedCube %%~ addToCube ops var
    (nextVar, nextIdx) <- liftToGoalState $ alloc ops
    db . sections . nextNodes %= (nextVar :)
    modifyM $ db . sections . nextCube %%~ addToCube ops nextVar
    oi %= ((idx, nextIdx) :)
    nv . allocatedStatePreds %= ((pred, nextVar) :)

addVarToStateSection :: Ops s u -> String -> [DDNode s u] -> [Int] -> StateT (GoalState s u sp lp )(ST s) ()
addVarToStateSection ops@Ops{..} name vars idxs = do
    db . sections . trackedNodes %= (vars ++)
    db . sections . trackedInds  %= (idxs ++)
    modifyM $ db . sections . trackedCube %%~ \c -> do
        cb <- nodesToCube vars
        addToCubeDeref ops c cb
    (nextVars, nextIdxs) <- liftToGoalState $ allocN ops (length vars)
    db . sections . nextNodes %= (nextVars ++)
    modifyM $ db . sections . nextCube %%~ \c -> do
        cb <- nodesToCube nextVars
        addToCubeDeref ops c cb
    oi %= (zip idxs nextIdxs ++) 
    nv . allocatedStateVars %= ((name, nextVars) :)

addPredToState :: Ord sp => Ops s u -> sp -> DDNode s u -> Int -> StateT (GoalState s u sp lp) (ST s) ()
addPredToState ops@Ops{..} pred var idx = do
    db . symbolTable %= addStatePredSymbol pred var idx
    addPredToStateSection ops pred var idx

addVarToState :: Ops s u -> String -> [DDNode s u] -> [Int] -> StateT (GoalState s u sp lp) (ST s) ()
addVarToState ops@Ops{..} name vars idxs = do
    db . symbolTable %= addStateVarSymbol name vars idxs
    addVarToStateSection ops name vars idxs

-- === update helpers ===
allocUntrackedPred :: (Ord sp) => Ops s u -> sp -> StateT (DB s u sp lp) (ST s) (DDNode s u)
allocUntrackedPred ops pred = liftM fst $ alloc ops =>= uncurry (addPredToUntracked ops pred)

allocUntrackedVar :: Ops s u -> String -> Int -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocUntrackedVar ops var size = liftM fst $ allocN ops size =>= uncurry (addVarToUntracked ops var)

addPredToUntracked :: Ord sp => Ops s u -> sp -> DDNode s u -> Int -> StateT (DB s u sp lp) (ST s) ()
addPredToUntracked ops@Ops{..} pred var idx = do
    symbolTable %= addStatePredSymbol pred var idx
    sections . untrackedInds %= (idx :)
    modifyM $ sections . untrackedCube %%~ addToCube ops var

addVarToUntracked  :: Ops s u -> String -> [DDNode s u] -> [Int] -> StateT (DB s u sp lp) (ST s) ()
addVarToUntracked ops@Ops {..} name vars idxs = do
    symbolTable %= addStateVarSymbol name vars idxs
    sections . untrackedInds %= (idxs ++)
    modifyM $ sections . untrackedCube %%~ \c -> do
        cb <- nodesToCube vars
        addToCubeDeref ops c cb

allocLabelPred :: Ord lp => Ops s u -> lp -> StateT (DB s u sp lp) (ST s) (DDNode s u)
allocLabelPred ops@Ops{..} pred = do
    (var, idx)  <- alloc ops 
    (en, enIdx) <- alloc ops
    symbolTable . labelPreds %= Map.insert pred ((var, idx), (en, enIdx))
    symbolTable . labelRev   %= (
        Map.insert idx (Predicate pred (var, idx), False)  >>> 
        Map.insert enIdx (Predicate pred (var, idx), True)
        )
    modifyM $ sections . labelCube %%~ \c -> do
        r1 <- addToCube ops var c
        addToCube ops en r1
    return var

allocLabelVar :: Ops s u -> String -> Int -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocLabelVar ops@Ops{..} var size = do
    (vars, idxs) <- allocN ops size
    symbolTable . labelVars %= Map.insert var (zip vars idxs)
    symbolTable . labelRev  %= flip (foldl (func vars idxs)) idxs
    modifyM $ sections . labelCube %%~ \c -> do
        cb <- nodesToCube vars
        addToCubeDeref ops cb c
    return vars
        where func vars idxs theMap idx = Map.insert idx (NonAbs var (zip vars idxs), False) theMap

allocOutcomePred :: Ord lp => Ops s u -> lp -> StateT (DB s u sp lp) (ST s) (DDNode s u)
allocOutcomePred ops@Ops{..} pred = do
    (var, idx) <- alloc ops
    symbolTable . outcomePreds %= Map.insert pred (var, idx)
    modifyM $ sections . outcomeCube %%~ addToCube ops var
    return var

allocOutcomeVar :: Ops s u -> String -> Int -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocOutcomeVar ops@Ops{..} name size = do
    (vars, idxs) <- allocN ops size
    symbolTable . outcomeVars %= Map.insert name (zip vars idxs)
    modifyM $ sections . outcomeCube %%~ \c -> do
        cb <- nodesToCube vars
        addToCubeDeref ops cb c
    return vars

-- === Variable promotion helpers ===
promoteUntrackedVar :: Ops s u -> Variable sp s u -> StateT (GoalState s u sp lp) (ST s) ()
promoteUntrackedVar ops@Ops{..} (Predicate pred (var, idx)) = do
    --add to state
    addPredToStateSection ops pred var idx
    --remove from untracked
    db . sections . untrackedInds %= (delete idx)
    modifyM $ db . sections . untrackedCube %%~ bexists var
promoteUntrackedVar ops@Ops{..} (NonAbs var vi) = do
    let (vars, idxs) = unzip vi
    addVarToStateSection ops var vars idxs
    --remove from untracked
    db . sections . untrackedInds %= (\\ idxs)
    modifyM $ db . sections . untrackedCube %%~ \c -> do
        cb <- nodesToCube vars
        bexists cb c

promoteUntrackedVars :: Ops s u -> [Variable sp s u] -> StateT (DB s u sp lp) (ST s) (NewVars s u sp)
promoteUntrackedVars ops vars = StateT $ \st -> do
    (_, GoalState{..}) <- runStateT (mapM_ (promoteUntrackedVar ops) vars) (GoalState (NewVars [] []) st [])
    doOrder ops _oi
    return (_nv, _db)

withTmp' :: Ops s u -> (DDNode s u -> StateT (DB s u sp lp) (ST s) a) -> StateT (DB s u sp lp) (ST s) a
withTmp' Ops{..} func = do
    ind <- use avlOffset
    var <- lift $ ithVar ind
    avlOffset += 1
    func var

--Construct the VarOps for compiling particular parts of the spec
goalOps :: Ord sp => Ops s u -> VarOps (GoalState s u sp lp) (BAPred sp lp) BAVar s u
goalOps ops = VarOps {withTmp = undefined {-withTmp' ops -}, ..}
    where
    getPred (StatePred pred) = do
        SymbolInfo{..} <- use $ db . symbolTable
        findWithDefaultM getNode pred _statePreds $ findWithDefaultProcessM getNode pred _initPreds (allocStatePred ops pred) (uncurry $ addPredToState ops pred)
    getPred _ = error "Requested non-state variable when compiling goal section"
    getVar  (StateVar var size) = do
        SymbolInfo{..} <- use $ db . symbolTable
        findWithDefaultM (map getNode) var _stateVars $ findWithDefaultProcessM (map getNode) var _initVars (allocStateVar ops var size) (uncurry (addVarToState ops var) . unzip)
    getVar  _ = error "Requested non-state variable when compiling goal section"

doGoal :: Ord sp => Ops s u -> (VarOps (GoalState s u sp lp) (BAPred sp lp) BAVar s u -> StateT (GoalState s u sp lp) (ST s) (DDNode s u)) -> StateT (DB s u sp lp) (ST s) (DDNode s u, NewVars s u sp)
doGoal ops complFunc = StateT $ \st -> do
    (res, GoalState{..}) <- runStateT (complFunc $ goalOps ops) (GoalState (NewVars [] []) st [])
    doOrder ops _oi
    return ((res, _nv), _db)

initOps :: Ord sp => Ops s u -> VarOps (DB s u sp lp) (BAPred sp lp) BAVar s u
initOps ops = VarOps {withTmp = withTmp' ops, ..}
    where
    getPred (StatePred pred) = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM getNode pred _initPreds (allocInitPred ops pred)
    getPred _ = error "Requested non-state variable when compiling init section"
    getVar  (StateVar var size) = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM (map getNode) var _initVars (allocInitVar ops var size)
    getVar _ = error "Requested non-state variable when compiling init section"

doInit :: Ord sp => Ops s u -> (VarOps (DB s u sp lp) (BAPred sp lp) BAVar s u -> StateT (DB s u sp lp) (ST s) (DDNode s u)) -> StateT (DB s u sp lp) (ST s) (DDNode s u)
doInit ops complFunc = complFunc (initOps ops)

updateOps :: (Ord sp, Ord lp) => Ops s u -> VarOps (DB s u sp lp) (BAPred sp lp) BAVar s u
updateOps ops = VarOps {withTmp = withTmp' ops, ..}
    where
    getPred (StatePred pred) = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM getNode pred _statePreds $ findWithDefaultProcessM getNode pred _initPreds (allocUntrackedPred ops pred) (uncurry $ addPredToUntracked ops pred)
    getPred (LabelPred pred) = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM (fst . fst) pred _labelPreds $ allocLabelPred ops pred
    getPred (OutPred pred) = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM fst pred _outcomePreds $ allocOutcomePred ops pred
    getVar  (StateVar var size) = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM (map getNode) var _stateVars $ findWithDefaultProcessM (map getNode) var _initVars (allocUntrackedVar ops var size) (uncurry (addVarToUntracked ops var) . unzip)
    getVar  (LabelVar var size) = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM (map getNode) var _labelVars $ allocLabelVar ops var size
    getVar  (OutVar var size) = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM (map getNode) var _outcomeVars $ allocOutcomeVar ops var size

doUpdate :: (Ord sp, Ord lp) => Ops s u -> (VarOps (DB s u sp lp) (BAPred sp lp) BAVar s u -> StateT (DB s u sp lp) (ST s) (DDNode s u)) -> StateT (DB s u sp lp) (ST s) (DDNode s u)
doUpdate ops complFunc = complFunc (updateOps ops)

