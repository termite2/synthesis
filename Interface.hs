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
data BAVar sp lp where
    StateVar :: sp -> Int -> BAVar sp lp
    LabelVar :: lp -> Int -> BAVar sp lp
    OutVar   :: lp -> Int -> BAVar sp lp
    deriving (Show, Eq, Ord)

--Operations that are given to the backend for compilation. 
data VarOps pdb v s u = VarOps {
    getVar  :: v -> StateT pdb (ST s) [DDNode s u],
    withTmp :: forall a. (DDNode s u -> StateT pdb (ST s) a) -> StateT pdb (ST s) a,
    allVars :: StateT pdb (ST s) [v]
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

data Variable p s u = Variable {
    ident :: p,
    vars  :: [VarInfo s u]
} 

instance (Show p) => Show (Variable p s u) where
    show x = show $ ident x

instance (Eq p) => Eq (Variable p s u) where
    x == y = ident x == ident y

instance (Ord p) => Ord (Variable p s u) where
    x `compare` y = ident x `compare` ident y

--Symbol table
data SymbolInfo s u sp lp = SymbolInfo {
    --below maps are used for update function compilation and constructing
    _initVars           :: Map sp [VarInfo s u],
    _stateVars          :: Map sp [VarInfo s u],
    _labelVars          :: Map lp ([VarInfo s u], VarInfo s u),
    _outcomeVars        :: Map lp [VarInfo s u],
    --mappings from index to variable/predicate
    _stateRev           :: Map Int (Variable sp s u),
    _labelRev           :: Map Int (Variable lp s u, Bool)
}
makeLenses ''SymbolInfo
initialSymbolTable = SymbolInfo Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty 

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
initialDB ops@Ops{..} = do
    let isi@SectionInfo{..} = initialSectionInfo ops
    let res = DB initialSymbolTable isi 0
    ref _trackedCube
    ref _untrackedCube
    ref _labelCube
    ref _outcomeCube
    ref _nextCube
    return res

--Generic variable allocations
alloc :: Ops s u -> StateT (DB s u sp lp) (ST s) (DDNode s u, Int)
alloc Ops{..} = do
    offset <- use avlOffset
    res    <- lift $ ithVar offset
    avlOffset += 1
    return (res, offset)

allocPair :: Ops s u -> StateT (DB s u sp lp) (ST s) ((DDNode s u, Int), (DDNode s u, Int))
allocPair ops@Ops{..} = do
    r1 <- alloc ops
    r2 <- alloc ops
    return (r1, r2)

allocN :: Ops s u -> Int -> StateT (DB s u sp lp) (ST s) ([DDNode s u], [Int])
allocN Ops{..} size = do
    offset <- use avlOffset
    let indices = take size $ iterate (+1) offset
    res    <- lift $ mapM ithVar indices
    avlOffset += size
    return (res, indices)

allocNPair :: Ops s u -> Int -> StateT (DB s u sp lp) (ST s ) (([DDNode s u], [Int]), ([DDNode s u], [Int]))
allocNPair Ops{..} size = do
    offset <- use avlOffset
    let indices1 = take size $ iterate (+2) offset
    let indices2 = take size $ iterate (+2) (offset + 1)
    res1    <- lift $ mapM ithVar indices1
    res2    <- lift $ mapM ithVar indices2
    avlOffset += size * 2
    return ((res1, indices1), (res2, indices2))

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
allocInitVar  :: (Ord sp) => Ops s u -> sp -> Int -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocInitVar ops v size = liftM fst $ do
    val <- allocN ops size
    symbolTable . initVars %= Map.insert v (uncurry zip val)
    return val

-- === goal helpers ===
data NewVars s u sp = NewVars {
    _allocatedStateVars  :: [(sp, [DDNode s u])]
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

allocStateVar :: (Ord sp) => Ops s u -> sp -> Int -> StateT (GoalState s u sp lp) (ST s) [DDNode s u]
allocStateVar ops name size = liftM fst $ liftToGoalState (allocN ops size) =>= uncurry (addVarToState ops name)

type Update a = a -> a

addStateVarSymbol :: (Ord sp) => sp -> [DDNode s u] -> [Int] -> Update (SymbolInfo s u sp lp)
addStateVarSymbol name vars idxs = 
    stateVars %~ Map.insert name (zip vars idxs) >>>
    stateRev  %~ flip (foldl func) idxs 
        where func theMap idx = Map.insert idx (Variable name (zip vars idxs)) theMap

addVarToStateSection :: Ops s u -> sp -> [DDNode s u] -> [Int] -> StateT (GoalState s u sp lp )(ST s) ()
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

addVarToState :: (Ord sp) => Ops s u -> sp -> [DDNode s u] -> [Int] -> StateT (GoalState s u sp lp) (ST s) ()
addVarToState ops@Ops{..} name vars idxs = do
    db . symbolTable %= addStateVarSymbol name vars idxs
    addVarToStateSection ops name vars idxs

-- === update helpers ===
allocUntrackedVar :: (Ord sp) => Ops s u -> sp -> Int -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocUntrackedVar ops var size = liftM fst $ allocN ops size =>= uncurry (addVarToUntracked ops var)

addVarToUntracked  :: (Ord sp) => Ops s u -> sp -> [DDNode s u] -> [Int] -> StateT (DB s u sp lp) (ST s) ()
addVarToUntracked ops@Ops {..} name vars idxs = do
    symbolTable %= addStateVarSymbol name vars idxs
    sections . untrackedInds %= (idxs ++)
    modifyM $ sections . untrackedCube %%~ \c -> do
        cb <- nodesToCube vars
        addToCubeDeref ops c cb

allocLabelVar :: (Ord lp) => Ops s u -> lp -> Int -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocLabelVar ops@Ops{..} var size = do
    (vars, idxs) <- allocN ops size
    (en, enIdx) <- alloc ops
    symbolTable . labelVars %= Map.insert var ((zip vars idxs), (en, enIdx))
    symbolTable . labelRev  %= (
        flip (foldl (func vars idxs)) idxs >>>
        Map.insert enIdx (Variable var (zip vars idxs), True)
        )
    modifyM $ sections . labelCube %%~ \c -> do
        cb <- nodesToCube vars
        r1 <- addToCubeDeref ops cb c
        addToCubeDeref ops en r1
    return vars
        where func vars idxs theMap idx = Map.insert idx (Variable var (zip vars idxs), False) theMap

allocOutcomeVar :: (Ord lp) => Ops s u -> lp -> Int -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocOutcomeVar ops@Ops{..} name size = do
    (vars, idxs) <- allocN ops size
    symbolTable . outcomeVars %= Map.insert name (zip vars idxs)
    modifyM $ sections . outcomeCube %%~ \c -> do
        cb <- nodesToCube vars
        addToCubeDeref ops cb c
    return vars

-- === Variable promotion helpers ===
promoteUntrackedVar :: Ops s u -> Variable sp s u -> StateT (GoalState s u sp lp) (ST s) ()
promoteUntrackedVar ops@Ops{..} (Variable var vi) = do
    let (vars, idxs) = unzip vi
    addVarToStateSection ops var vars idxs
    --remove from untracked
    db . sections . untrackedInds %= (\\ idxs)
    modifyM $ db . sections . untrackedCube %%~ \c -> do
        cb <- nodesToCube vars
        bexists cb c

promoteUntrackedVars :: Ops s u -> [Variable sp s u] -> StateT (DB s u sp lp) (ST s) (NewVars s u sp)
promoteUntrackedVars ops vars = StateT $ \st -> do
    (_, GoalState{..}) <- runStateT (mapM_ (promoteUntrackedVar ops) vars) (GoalState (NewVars []) st [])
    doOrder ops _oi
    return (_nv, _db)

withTmp' :: Ops s u -> (DDNode s u -> StateT (DB s u sp lp) (ST s) a) -> StateT (DB s u sp lp) (ST s) a
withTmp' Ops{..} func = do
    ind <- use avlOffset
    var <- lift $ ithVar ind
    avlOffset += 1
    func var

--Construct the VarOps for compiling particular parts of the spec
goalOps :: Ord sp => Ops s u -> VarOps (GoalState s u sp lp) (BAVar sp lp) s u
goalOps ops = VarOps {withTmp = undefined {-withTmp' ops -}, ..}
    where
    getVar  (StateVar var size) = do
        SymbolInfo{..} <- use $ db . symbolTable
        findWithDefaultM (map getNode) var _stateVars $ findWithDefaultProcessM (map getNode) var _initVars (allocStateVar ops var size) (uncurry (addVarToState ops var) . unzip)
    getVar  _ = error "Requested non-state variable when compiling goal section"

doGoal :: Ord sp => Ops s u -> (VarOps (GoalState s u sp lp) (BAVar sp lp) s u -> StateT (GoalState s u sp lp) (ST s) (DDNode s u)) -> StateT (DB s u sp lp) (ST s) (DDNode s u, NewVars s u sp)
doGoal ops complFunc = StateT $ \st -> do
    (res, GoalState{..}) <- runStateT (complFunc $ goalOps ops) (GoalState (NewVars []) st [])
    doOrder ops _oi
    return ((res, _nv), _db)

initOps :: Ord sp => Ops s u -> VarOps (DB s u sp lp) (BAVar sp lp) s u
initOps ops = VarOps {withTmp = withTmp' ops, ..}
    where
    getVar  (StateVar var size) = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM (map getNode) var _initVars (allocInitVar ops var size)
    getVar _ = error "Requested non-state variable when compiling init section"

doInit :: Ord sp => Ops s u -> (VarOps (DB s u sp lp) (BAVar sp lp) s u -> StateT (DB s u sp lp) (ST s) (DDNode s u)) -> StateT (DB s u sp lp) (ST s) (DDNode s u)
doInit ops complFunc = complFunc (initOps ops)

updateOps :: (Ord sp, Ord lp) => Ops s u -> VarOps (DB s u sp lp) (BAVar sp lp) s u
updateOps ops = VarOps {withTmp = withTmp' ops, ..}
    where
    getVar (StateVar var size) = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM (map getNode) var _stateVars $ findWithDefaultProcessM (map getNode) var _initVars (allocUntrackedVar ops var size) (uncurry (addVarToUntracked ops var) . unzip)
    getVar (LabelVar var size) = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM (map getNode . fst) var _labelVars $ allocLabelVar ops var size
    getVar (OutVar var size) = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM (map getNode) var _outcomeVars $ allocOutcomeVar ops var size

doUpdate :: (Ord sp, Ord lp) => Ops s u -> (VarOps (DB s u sp lp) (BAVar sp lp) s u -> StateT (DB s u sp lp) (ST s) (DDNode s u)) -> StateT (DB s u sp lp) (ST s) (DDNode s u)
doUpdate ops complFunc = complFunc (updateOps ops)

