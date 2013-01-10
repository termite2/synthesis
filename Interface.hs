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

--Generic utility functions
findWithDefaultM :: (Monad m, Ord k) => (v -> v') -> k -> Map k v -> m v' -> m v'
findWithDefaultM modF key theMap func = maybe func (return . modF) $ Map.lookup key theMap 

findWithDefaultProcessM :: (Monad m, Ord k) => (v -> v') -> k -> Map k v -> m v' -> (v -> m ()) -> m v'
findWithDefaultProcessM modF key theMap funcAbsent funcPresent = maybe funcAbsent func $ Map.lookup key theMap
    where
    func v = do
        funcPresent v
        return $ modF v

getState :: MonadState s m => (s -> m a) -> m a
getState func = do
    st <- get
    func st

getStatePart :: MonadState s m => (s -> s') -> (s' -> m a) -> m a
getStatePart getFunc func = getState (func . getFunc)

modifyM :: Monad m => (s -> m s) -> StateT s m ()
modifyM f = get >>= (lift . f) >>= put

infixl 1 =>=
(=>=) :: Monad m => m a -> (a -> m ()) -> m a
a =>= b = undefined

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
    --mappings from index to variable/predicate
    _stateRev           :: Map Int (Variable sp s u),
    _labelRev           :: Map Int (Variable lp s u, Bool)
}

makeLenses ''SymbolInfo

--Sections
data SectionInfo s u = SectionInfo {
    _trackedCube   :: DDNode s u,
    _trackedNodes  :: [DDNode s u],
    _trackedInds   :: [Int],
    _untrackedCube :: DDNode s u,
    _untrackedInds :: [Int],
    _labelCube     :: DDNode s u,
    _nextCube      :: DDNode s u,
    _nextNodes     :: [DDNode s u]
}

makeLenses ''SectionInfo

--Variable/predicate database
data DB s u sp lp = DB {
    _symbolTable :: SymbolInfo s u sp lp,
    _sections    :: SectionInfo s u,
    _avlOffset   :: Int
}

makeLenses ''DB

--types that appear in the backend syntax tree
data BAPred sp lp where
    StatePred :: sp -> BAPred sp lp
    LabelPred :: lp -> BAPred sp lp
    OutPred   :: lp -> BAPred sp lp

data BAVar where
    StateVar :: String -> Int -> BAVar 
    LabelVar :: String -> Int -> BAVar
    OutVar   :: String -> Int -> BAVar

--Operations that are given to the backend for compilation. 
data VarOps pdb p v s u = VarOps {
    getPred :: p -> StateT pdb (ST s) (DDNode s u),
    getVar  :: v -> StateT pdb (ST s) [DDNode s u],
    withTmp :: forall a. (DDNode s u -> StateT pdb (ST s) a) -> StateT pdb (ST s) a
}

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
    let indices = iterate (+1) offset
    res    <- lift $ mapM ithVar indices
    avlOffset += size
    return (res, indices)

--Do the variable allocation and symbol table tracking

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
allocStatePred :: Ord sp => Ops s u -> sp -> StateT (DB s u sp lp) (ST s) (DDNode s u)
allocStatePred ops pred = liftM fst $ alloc ops =>= uncurry (addPredToState ops pred)

allocStateVar :: Ops s u -> String -> Int -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocStateVar ops name size = liftM fst $ allocN ops size =>= uncurry (addVarToState ops name)

type Update a = a -> a

addStatePredSymbol :: Ord sp => sp -> DDNode s u -> Int -> Update (SymbolInfo s u sp lp)
addStatePredSymbol pred var idx = 
    statePreds %~ Map.insert pred (var, idx) >>> 
    stateRev   %~ Map.insert idx (Predicate pred (var, idx))

addStateVarSymbol :: String -> [DDNode s u] -> [Int] -> Update (SymbolInfo s u sp lp)
addStateVarSymbol name vars idxs = 
    stateVars %~ Map.insert name (zip vars idxs) >>>
    undefined --stateRev  %~ Map.insert idx (Non name (zip vars idxs))

addPredToState :: Ord sp => Ops s u -> sp -> DDNode s u -> Int -> StateT (DB s u sp lp) (ST s) ()
addPredToState Ops{..} pred var idx = do
    symbolTable %= addStatePredSymbol pred var idx
    sections . trackedNodes %= (var :) 
    sections . trackedInds  %= (idx :)
    modifyM $ sections . trackedCube %%~ band var

addVarToState :: Ops s u -> String -> [DDNode s u] -> [Int] -> StateT (DB s u sp lp) (ST s) ()
addVarToState Ops{..} name vars idxs = do
    symbolTable %= addStateVarSymbol name vars idxs
    sections . trackedNodes %= (vars ++)
    sections . trackedInds  %= (idxs ++)
    modifyM $ sections . trackedCube %%~ \c -> do
        cb <- nodesToCube vars
        band c cb

-- === update helpers ===
allocUntrackedPred :: (Ord sp) => Ops s u -> sp -> StateT (DB s u sp lp) (ST s) (DDNode s u)
allocUntrackedPred ops pred = liftM fst $ alloc ops =>= uncurry (addPredToUntracked ops pred)

allocUntrackedVar :: Ops s u -> String -> Int -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocUntrackedVar ops var size = liftM fst $ allocN ops size =>= uncurry (addVarToUntracked ops var)

addPredToUntracked :: Ord sp => Ops s u -> sp -> DDNode s u -> Int -> StateT (DB s u sp lp) (ST s) ()
addPredToUntracked Ops{..} pred var idx = do
    symbolTable %= addStatePredSymbol pred var idx
    sections . untrackedInds %= (idx :)
    modifyM $ sections . untrackedCube %%~ band var

addVarToUntracked  :: Ops s u -> String -> [DDNode s u] -> [Int] -> StateT (DB s u sp lp) (ST s) ()
addVarToUntracked Ops {..} name vars idxs = do
    symbolTable %= addStateVarSymbol name vars idxs
    sections . untrackedInds %= (idxs ++)
    modifyM $ sections . untrackedCube %%~ \c -> do
        cb <- nodesToCube vars
        band c cb

allocLabelPred :: Ord lp => Ops s u -> lp -> StateT (DB s u sp lp) (ST s) (DDNode s u)
allocLabelPred ops@Ops{..} pred = do
    (var, idx)  <- alloc ops 
    (en, enIdx) <- alloc ops
    symbolTable . labelPreds %= Map.insert pred ((var, idx), (en, enIdx))
    symbolTable . labelRev   %= undefined
    modifyM $ sections . labelCube %%~ \c -> do
        r1 <- c .& var
        r1 .& en
    return var

allocLabelVar :: Ops s u -> String -> Int -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocLabelVar ops@Ops{..} var size = do
    (vars, idxs) <- allocN ops size
    symbolTable . labelVars %= Map.insert var (zip vars idxs)
    symbolTable . labelRev  %= undefined
    modifyM $ sections . labelCube %%~ \c -> do
        cb <- nodesToCube vars
        cb .& c
    return vars

-- === Variable promotion helpers ===

promoteUntrackedVar :: Ops s u -> [Variable sp s u] -> StateT (DB s u sp lp) (ST s) ([(sp, [DDNode s u])], [(String, DDNode s u)])
promoteUntrackedVar = undefined

withTmp' :: Ops s u -> (DDNode s u -> StateT (DB s u sp lp) (ST s) a) -> StateT (DB s u sp lp) (ST s) a
withTmp' Ops{..} func = do
    ind <- use avlOffset
    var <- lift $ ithVar ind
    avlOffset += 1
    func var

{-
data GoalState s u sp lp = GoalState {
    db                  :: DB s u sp lp,
    allocatedStatePreds :: Set sp, 
    allocatedStateVars  :: Map String Int
}


--Construct the VarOps for compiling particular parts of the spec
goalOps :: Ops s u -> VarOps (GoalState s u sp lp) (BAPred sp lp) BAVar s u
goalOps ops = VarOps {withTmp = withTmp' ops, ..}
    where
    getPred (StatePred pred)      = do
        getStatePart (symbolTable . db) func
        modify $ \st -> st {allocatedStatePreds = Set.insert pred (allocatedStatePreds st)}
        where 
        func st = findWithDefaultM getNode pred (statePreds st) $ findWithDefaultProcessM getNode pred (initPreds st) (allocStatePred ops pred) (uncurry $ promotePredToState pred)
    getPred _                         = error "Requested non-state variable when compiling goal section"
    getVar  (StateVar var size) = do
        getStatePart (symbolTable . db) func
        modify $ \st -> st {allocatedStateVars = Map.insert var size (allocatedStateVars st)}
        where 
        func st = findWithDefaultM (map getNode) var (stateVars st) $ findWithDefaultProcessM (map getNode) var (initVars st) (allocStateVar ops var size) (promoteVarToState var)
    getVar  _                         = error "Requested non-state variable when compiling goal section"

data DoGoalRet s u sp = DoGoalRet {
    goalNextPredicates :: [(sp, DDNode s u)],
    goalNextVariables  :: [(String, DDNode s u)],
    goalExpr           :: DDNode s u
}

--TODO add the next states to the sections
doGoal :: Ops s u -> (VarOps pdb p v s u -> StateT pdb (ST s) (DDNode s u)) -> StateT (DB s u sp lp) (ST s) (DoGoalRet s u sp)
doGoal ops complFunc = do
    (goalExpr, goalNextPredicates, goalNextVariables) <- StateT $ \st -> do
        (node, GoalState{..}) <- runStateT (complFunc (goalOps ops)) (GoalState st Set.empty Map.empty)
        return ((node, goalNextPredicates, goalNextVariables), db)
    goalNextPredicates' <- sequence $ map monadOut $ map (id &&& alloc ops)  $ Set.elems goalNextPredicates
    goalNextVariables'  <- sequence $ map monadOut $ map (id *** allocN ops) $ Map.toList goalNextVariables
    return $ DoGoalRet {
        goalNextPredicates = map (second getNode) goalNextPredicates',
        goalNextVariables  = map (second getNode) goalNextVariables'
    }

-}

initOps :: Ord sp => Ops s u -> VarOps (DB s u sp lp) (BAPred sp lp) BAVar s u
initOps ops = VarOps {withTmp = withTmp' ops, ..}
    where
    getPred (StatePred pred) = do
        st <- get
        findWithDefaultM getNode pred (st ^. symbolTable . initPreds) (allocInitPred ops pred)
    getPred _ = error "Requested non-state variable when compiling init section"
    getVar  (StateVar var size) = do
        st <- get
        findWithDefaultM (map getNode) var (st ^. symbolTable . initVars) (allocInitVar ops var size)
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
    getVar  (StateVar var size) = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM (map getNode) var _stateVars $ findWithDefaultProcessM (map getNode) var _initVars (allocUntrackedVar ops var size) (uncurry (addVarToUntracked ops var) . unzip)
    getVar  (LabelVar var size) = do
        SymbolInfo{..} <- use symbolTable
        findWithDefaultM (map getNode) var _labelVars $ allocLabelVar ops var size

doUpdate :: (Ord sp, Ord lp) => Ops s u -> (VarOps (DB s u sp lp) (BAPred sp lp) BAVar s u -> StateT (DB s u sp lp) (ST s) (DDNode s u)) -> StateT (DB s u sp lp) (ST s) (DDNode s u)
doUpdate ops complFunc = complFunc (updateOps ops)

{-
promote :: Ops s u -> (sp, VarInfo s u) -> (String, [VarInfo s u]) -> ST s ((sp, VarInfo s u), (String, [VarInfo s u]))
promote preds vars = do
    predRet <- sequence $ map (monadOut . (id *** const (alloc ops))) preds
    varRet  <- sequence $ map (monadOut . (id *** alloc ops . length)) vars
    promoteStuff

-}
