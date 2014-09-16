{-# LANGUAGE RecordWildCards, PolymorphicComponents, GADTs, TemplateHaskell #-}

module Synthesis.Interface where

import Control.Monad.ST
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.State
import Control.Arrow
import Data.List as List
import Safe
import Data.Tuple.All

import Control.Lens

import Cudd.MTR

import Synthesis.BddRecord
import Synthesis.RefineUtil

--types that appear in the backend syntax tree
data BAVar sp lp where
    StateVar :: sp -> Int -> BAVar sp lp
    LabelVar :: lp -> Int -> BAVar sp lp
    OutVar   :: lp -> Int -> BAVar sp lp
    deriving (Show, Eq, Ord)

--Operations that are given to the backend for compilation. 
data VarOps pdb v s u = VarOps {
    getVar  :: v -> Maybe String -> StateT pdb (ST s) [DDNode s u],
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

--Variable type
getNode = fst
getIdx = snd

--Symbol table
data SymbolInfo s u sp lp = SymbolInfo {
    --below maps are used for update function compilation and constructing
    _initVars           :: Map sp ([DDNode s u], [Int], [DDNode s u], [Int]),
    _stateVars          :: Map sp ([DDNode s u], [Int], [DDNode s u], [Int]),
    _labelVars          :: Map lp ([DDNode s u], [Int], DDNode s u, Int),
    _outcomeVars        :: Map lp ([DDNode s u], [Int]),
    --mappings from index to variable/predicate
    _stateRev           :: Map Int sp,
    _labelRev           :: Map Int (lp, Bool)
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

derefSectionInfo :: Ops s u -> SectionInfo s u -> ST s ()
derefSectionInfo Ops{..} SectionInfo{..} = do
    deref _trackedCube
    deref _untrackedCube
    deref _labelCube
    deref _outcomeCube
    deref _nextCube

--Variable/predicate database
data DB s u sp lp = DB {
    _symbolTable :: SymbolInfo s u sp lp,
    _sections    :: SectionInfo s u,
    _avlOffset   :: Int,
    _freeInds    :: [Int],
    _groups      :: Map String (Int, Int, Int)
}
makeLenses ''DB
initialDB ops@Ops{..} = do
    let isi@SectionInfo{..} = initialSectionInfo ops
    let res = DB initialSymbolTable isi 0 [] Map.empty
    ref _trackedCube
    ref _untrackedCube
    ref _labelCube
    ref _outcomeCube
    ref _nextCube
    return res

extractStatePreds :: DB s u sp lp -> [sp]
extractStatePreds db = map sel1 $ filter (filt . snd) $ Map.toList (_stateVars $ _symbolTable db)
    where filt vars = not $ null $ sel2 vars `intersect` _trackedInds (_sections db)

extractUntrackedPreds :: DB s u sp lp -> [sp]
extractUntrackedPreds db = map sel1 $ filter (filt . snd) $ Map.toList (_stateVars $ _symbolTable db)
    where filt vars = not $ null $ sel2 vars `intersect` _untrackedInds (_sections db)

--Below two functions are only used for temporary variables
allocIdx :: StateT (DB s u sp lp) (ST s) Int
allocIdx = do
    st <- use freeInds
    case st of 
        [] -> do
            ind <- use avlOffset
            avlOffset += 1
            return ind
        x:xs -> do
            freeInds .= xs
            return x 

freeIdx :: Int -> StateT (DB s u sp lp) (ST s) ()
freeIdx idx = freeInds %= (idx :)

--Generic variable allocations
allocN :: Ops s u -> Int -> Maybe String -> StateT (DB s u sp lp) (ST s) ([DDNode s u], [Int])
allocN Ops{..} size group = do
    offset <- use avlOffset
    avlOffset += size
    case group of 
        Nothing -> do
            let indices = take size $ iterate (+1) offset
            res <- lift $ mapM ithVar indices
            lift $ makeTreeNode offset size 4
            return (res, indices)
        Just grName -> do
            grps <- use groups
            case Map.lookup grName grps of 
                Nothing -> do
                    let indices = take size $ iterate (+1) offset
                    res    <- lift $ mapM ithVar indices
                    lift $ makeTreeNode offset size 4
                    lift $ makeTreeNode offset size 4
                    groups %= Map.insert grName (offset, size, last indices)
                    return (res, indices)
                Just (startIdx, sizeGrp, lastIdx) -> do
                    lvl <- lift $ readPerm lastIdx
                    let levels = take size $ iterate (+1) (lvl + 1)
                    let indices = take size $ iterate (+1) offset
                    res <- lift $ mapM varAtLevel levels
                    lift $ makeTreeNode (head indices) size 4
                    lift $ makeTreeNode startIdx (sizeGrp + size) 4
                    tr <- lift readTree
                    lvl <- lift $ readPerm startIdx
                    oldGroup <- lift $ mtrFindGroup tr lvl sizeGrp
                    lift $ mtrDissolveGroup oldGroup
                    groups %= Map.insert grName (startIdx, sizeGrp + size, last indices)
                    return (res, indices)

deinterleave :: [a] -> ([a], [a])
deinterleave []        = ([], [])
deinterleave (x:y:rst) = (x:xs, y:ys) 
    where (xs, ys) = deinterleave rst

allocNPair :: Ops s u -> Int -> Maybe String -> StateT (DB s u sp lp) (ST s ) (([DDNode s u], [Int]), ([DDNode s u], [Int]))
allocNPair ops size group = do
    (vars, idxs) <- allocN ops (size*2) group 
    let (vc, vn)  = deinterleave vars
        (ic, inn) = deinterleave idxs
    return ((vc, ic), (vn, inn))

--Do the variable allocation and symbol table tracking
addToCubeDeref :: Ops s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
addToCubeDeref Ops{..} add cb = do
    res <- add .& cb
    deref add
    deref cb
    return res

subFromCubeDeref :: Ops s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
subFromCubeDeref Ops{..} sub cb = do
    res <- bexists sub cb
    deref sub
    deref cb
    return res

--initial state helpers
allocInitVar  :: (Ord sp) => Ops s u -> sp -> Int -> Maybe String -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocInitVar ops@Ops{..} v size group = do
    ((cn, ci), (nn, ni)) <- allocNPair ops size group
    symbolTable . initVars %= Map.insert v (cn, ci, nn, ni)
    symbolTable . stateRev  %= flip (foldl func) ci
    return cn
        where func theMap idx = Map.insert idx v theMap

-- === goal helpers ===
data NewVars s u sp = NewVars {
    _allocatedStateVars  :: [(sp, [DDNode s u])]
}
makeLenses ''NewVars

data GoalState s u sp lp = GoalState {
    _nv :: NewVars s u sp,
    _db :: DB s u sp lp
}
makeLenses ''GoalState

liftToGoalState :: StateT (DB s u sp lp) (ST s) a -> StateT (GoalState s u sp lp) (ST s) a
liftToGoalState (StateT func) = StateT $ \st -> do
    (res, st') <- func (_db st) 
    return (res, GoalState (_nv st) st')

allocStateVar :: (Ord sp) => Ops s u -> sp -> Int -> Maybe String -> StateT (GoalState s u sp lp) (ST s) [DDNode s u]
allocStateVar ops@Ops{..} name size group = do
    ((cn, ci), (nn, ni)) <- liftToGoalState $ allocNPair ops size group
    addVarToState ops name cn ci nn ni
    return cn

type Update a = a -> a

addStateVarSymbol :: (Ord sp) => sp -> [DDNode s u] -> [Int] -> [DDNode s u] -> [Int] -> Update (SymbolInfo s u sp lp)
addStateVarSymbol name vars idxs vars' idxs' = 
    stateVars %~ Map.insert name (vars, idxs, vars', idxs') >>>
    --TODO dont need to do this every time
    stateRev  %~ flip (foldl func) idxs 
        where func theMap idx = Map.insert idx name theMap

addVarToStateSection :: Ops s u -> sp -> [DDNode s u] -> [Int] -> [DDNode s u] -> [Int] -> StateT (GoalState s u sp lp )(ST s) ()
addVarToStateSection ops@Ops{..} name varsCurrent idxsCurrent varsNext idxsNext = do
    db . sections . trackedNodes %= (varsCurrent ++)
    db . sections . trackedInds  %= (idxsCurrent ++)
    modifyM $ db . sections . trackedCube %%~ \c -> do
        cb <- nodesToCube varsCurrent
        addToCubeDeref ops c cb
    db . sections . nextNodes %= (varsNext ++)
    modifyM $ db . sections . nextCube %%~ \c -> do
        cb <- nodesToCube varsNext
        addToCubeDeref ops c cb
    nv . allocatedStateVars %= ((name, varsNext) :)

addVarToState :: (Ord sp) => Ops s u -> sp -> [DDNode s u] -> [Int] -> [DDNode s u] -> [Int] -> StateT (GoalState s u sp lp) (ST s) ()
addVarToState ops@Ops{..} name vars idxs vars' idxs' = do
    db . symbolTable %= addStateVarSymbol name vars idxs vars' idxs'
    addVarToStateSection ops name vars idxs vars' idxs'

-- === update helpers ===
allocUntrackedVar :: (Ord sp) => Ops s u -> sp -> Int -> Maybe String -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocUntrackedVar ops@Ops{..} var size group = do
    ((cn, ci), (nn, ni)) <- allocNPair ops size group
    addVarToUntracked ops var cn ci nn ni
    return cn

addVarToUntracked  :: (Ord sp) => Ops s u -> sp -> [DDNode s u] -> [Int] -> [DDNode s u] -> [Int] -> StateT (DB s u sp lp) (ST s) ()
addVarToUntracked ops@Ops {..} name vars idxs vars' idxs' = do
    symbolTable %= addStateVarSymbol name vars idxs vars' idxs'
    sections . untrackedInds %= (idxs ++)
    modifyM $ sections . untrackedCube %%~ \c -> do
        cb <- nodesToCube vars
        addToCubeDeref ops c cb

allocLabelVar :: (Ord lp) => Ops s u -> lp -> Int -> Maybe String -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocLabelVar ops@Ops{..} var size group = do
    (vars', idxs') <- allocN ops (size + 1) group
    let (en, enIdx)  = (head vars', head idxs')
        (vars, idxs) = (tail vars', tail idxs')
    symbolTable . labelVars %= Map.insert var (vars, idxs, en, enIdx)
    symbolTable . labelRev  %= (
        flip (foldl (func vars idxs)) idxs >>>
        Map.insert enIdx (var, True)
        )
    modifyM $ sections . labelCube %%~ \c -> do
        cb <- nodesToCube vars
        r1 <- addToCubeDeref ops cb c
        addToCubeDeref ops en r1
    return vars
        where func vars idxs theMap idx = Map.insert idx (var, False) theMap

allocOutcomeVar :: (Ord lp) => Ops s u -> lp -> Int -> Maybe String -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocOutcomeVar ops@Ops{..} name size group = do
    (vars, idxs) <- allocN ops size group
    symbolTable . outcomeVars %= Map.insert name (vars, idxs)
    modifyM $ sections . outcomeCube %%~ \c -> do
        cb <- nodesToCube vars
        addToCubeDeref ops cb c
    return vars

-- === Variable promotion helpers ===
promoteUntrackedVar :: (Ord sp) => Ops s u -> sp -> StateT (GoalState s u sp lp) (ST s) ()
promoteUntrackedVar ops@Ops{..} var = do
    mp <- use $ db . symbolTable . stateVars
    let (vars, idxs, vars', idxs') = fromJustNote "promoteUntrackedVar" $ Map.lookup var mp
    addVarToStateSection ops var vars idxs vars' idxs'
    db . sections . untrackedInds %= (\\ idxs)
    modifyM $ db . sections . untrackedCube %%~ \c -> do
        cb <- nodesToCube vars
        subFromCubeDeref ops cb c

promoteUntrackedVars :: (Ord sp) => Ops s u -> [sp] -> StateT (DB s u sp lp) (ST s) (NewVars s u sp)
promoteUntrackedVars ops vars = StateT $ \st -> do
    (_, GoalState{..}) <- runStateT (mapM_ (promoteUntrackedVar ops) vars) (GoalState (NewVars []) st)
    return (_nv, _db)

withTmp' :: Ops s u -> (DDNode s u -> StateT (DB s u sp lp) (ST s) a) -> StateT (DB s u sp lp) (ST s) a
withTmp' Ops{..} func = do
    ind <- allocIdx
    var <- lift $ ithVar ind
    res <- func var
    freeIdx ind
    lift $ deref var
    return res

withTmpGoal' :: Ops s u -> (DDNode s u -> StateT (GoalState s u sp lp) (ST s) a) -> StateT (GoalState s u sp lp) (ST s) a
withTmpGoal' Ops{..} func = do
    ind <- liftToGoalState allocIdx
    var <- lift $ ithVar ind
    res <- func var
    liftToGoalState $ freeIdx ind
    lift $ deref var
    return res

allVars' :: StateT (DB s u sp lp) (ST s) [BAVar sp lp]
allVars' = do
    SymbolInfo {..} <- use symbolTable 
    return $ map (uncurry StateVar . second (length . sel1)) (Map.toList _stateVars) ++ map (uncurry LabelVar . second (length . sel1)) (Map.toList _labelVars) ++ map (uncurry OutVar . second (length . sel1)) (Map.toList _outcomeVars)

--Construct the VarOps for compiling particular parts of the spec
goalOps :: Ord sp => Ops s u -> VarOps (GoalState s u sp lp) (BAVar sp lp) s u
goalOps ops = VarOps {withTmp = withTmpGoal' ops, allVars = liftToGoalState allVars', ..}
    where
    getVar (StateVar var size) group = do
        SymbolInfo{..} <- use $ db . symbolTable
        findWithDefaultM sel1 var _stateVars $ findWithDefaultProcessM sel1 var _initVars (allocStateVar ops var size group) (uncurryN $ addVarToState ops var)
    getVar  _ _ = error "Requested non-state variable when compiling goal section"

doGoal :: (Ord sp, Monad (rm (ST s)))
       => Ops s u 
       -> (VarOps (GoalState s u sp lp) (BAVar sp lp) s u -> StateT st (StateT (GoalState s u sp lp) (rm (ST s))) a) 
       -> StateT st (StateT (DB s u sp lp) (rm (ST s))) (a, NewVars s u sp)
doGoal ops complFunc = StateT $ \st1 -> StateT $ \st -> do
    ((res, st1'), GoalState{..}) <- runStateT (runStateT (complFunc $ goalOps ops) st1) (GoalState (NewVars []) st)
    return (((res, _nv), st1'), _db)

stateLabelOps :: (Ord sp, Ord lp) => Ops s u -> VarOps (GoalState s u sp lp) (BAVar sp lp) s u
stateLabelOps ops = VarOps {withTmp = withTmpGoal' ops, allVars = liftToGoalState allVars', ..}
    where
    getVar  (StateVar var size) group = do
        SymbolInfo{..} <- use $ db . symbolTable
        findWithDefaultM sel1 var _stateVars $ findWithDefaultProcessM sel1 var _initVars (allocStateVar ops var size group) (uncurryN $ addVarToState ops var)
    getVar  (LabelVar var size) group = do
        SymbolInfo{..} <- use $ db . symbolTable
        liftToGoalState $ findWithDefaultM sel1 var _labelVars $ allocLabelVar ops var size group
    getVar  _ _ = error "Requested non-state variable when compiling goal section"

doStateLabel :: (Ord sp, Ord lp, Monad (rm (ST s))) 
             => Ops s u 
             -> (VarOps (GoalState s u sp lp) (BAVar sp lp) s u -> StateT st (StateT (GoalState s u sp lp) (rm (ST s))) a) 
             -> StateT st (StateT (DB s u sp lp) (rm (ST s))) (a, NewVars s u sp)
doStateLabel ops complFunc = StateT $ \st1 -> StateT $ \st -> do
    ((res, st1'), GoalState{..}) <- runStateT (runStateT (complFunc $ stateLabelOps ops) st1) (GoalState (NewVars []) st)
    return (((res, _nv), st1'), _db)

stateLabelOutcomeOps :: (Ord sp, Ord lp) => Ops s u -> VarOps (GoalState s u sp lp) (BAVar sp lp) s u
stateLabelOutcomeOps ops = VarOps {withTmp = withTmpGoal' ops, allVars = liftToGoalState allVars', ..}
    where
    getVar  (StateVar var size) group = do
        SymbolInfo{..} <- use $ db . symbolTable
        findWithDefaultM sel1 var _stateVars $ findWithDefaultProcessM sel1 var _initVars (allocStateVar ops var size group) (uncurryN $ addVarToState ops var)
    getVar  (LabelVar var size) group = do
        SymbolInfo{..} <- use $ db . symbolTable
        liftToGoalState $ findWithDefaultM sel1 var _labelVars $ allocLabelVar ops var size group
    getVar  (OutVar var size) group = do
        SymbolInfo{..} <- use $ db . symbolTable
        liftToGoalState $ findWithDefaultM sel1 var _outcomeVars $ allocOutcomeVar ops var size group
    getVar  _ _ = error "Requested non-state variable when compiling goal section"

doStateLabelOutcome :: (Ord sp, Ord lp) => Ops s u -> (VarOps (GoalState s u sp lp) (BAVar sp lp) s u -> StateT (GoalState s u sp lp) (ST s) a) -> StateT (DB s u sp lp) (ST s) (a, NewVars s u sp)
doStateLabelOutcome ops complFunc = StateT $ \st -> do
    (res, GoalState{..}) <- runStateT (complFunc $ stateLabelOps ops) (GoalState (NewVars []) st)
    return ((res, _nv), _db)

initOps :: Ord sp => Ops s u -> VarOps (DB s u sp lp) (BAVar sp lp) s u
initOps ops = VarOps {withTmp = withTmp' ops, allVars = allVars', ..}
    where
    getVar  (StateVar var size) group = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM sel1 var _initVars (allocInitVar ops var size group)
    getVar _ _ = error "Requested non-state variable when compiling init section"

doInit :: Ord sp => Ops s u -> (VarOps (DB s u sp lp) (BAVar sp lp) s u -> a) -> a
doInit ops complFunc = complFunc (initOps ops)

updateOps :: (Ord sp, Ord lp) => Ops s u -> VarOps (DB s u sp lp) (BAVar sp lp) s u
updateOps ops = VarOps {withTmp = withTmp' ops, allVars = allVars', ..}
    where
    getVar (StateVar var size) group = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM sel1 var _stateVars $ findWithDefaultProcessM sel1 var _initVars (allocUntrackedVar ops var size group) (uncurryN $ addVarToUntracked ops var)
    getVar (LabelVar var size) group = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM sel1 var _labelVars $ allocLabelVar ops var size group
    getVar (OutVar var size) group = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM sel1 var _outcomeVars $ allocOutcomeVar ops var size group

doUpdate :: (Ord sp, Ord lp) => Ops s u -> (VarOps (DB s u sp lp) (BAVar sp lp) s u -> a) -> a
doUpdate ops complFunc = complFunc (updateOps ops)

getStaticVar :: Ord sp => Ops s u -> sp -> Int -> Maybe String -> StateT (DB s u sp lp) (ST s) [DDNode s u]
getStaticVar ops var size group = StateT $ \st -> do
    (res, st') <- flip runStateT (GoalState (NewVars []) st) $ do
        SymbolInfo{..} <- use $ db . symbolTable
        findWithDefaultM sel3 var _stateVars $ findWithDefaultProcessM sel3 var _initVars (allocStateVar ops var size group) (uncurryN $ addVarToState ops var)
    return (res, _db st')

