{-# LANGUAGE RecordWildCards, PolymorphicComponents, GADTs #-}

module Interface where

import Control.Monad.ST.Lazy
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.State
import Control.Arrow

import BddRecord

--Generic utility functions
findWithDefaultM :: (Monad m, Ord k) => (v -> v') -> k -> Map k v -> m v' -> m v'
findWithDefaultM modF key theMap func = maybe func (return . modF) $ Map.lookup key theMap 

findWithDefaultProcessM :: (Monad m, Ord k) => (v -> v') -> k -> Map k v -> m v' -> (v -> m ()) -> m v'
findWithDefaultProcessM modF key theMap funcAbsent funcPresent = maybe funcAbsent funcPresent $ Map.lookup key theMap

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
    initPreds          :: Map sp (VarInfo s u),
    initVars           :: Map String [VarInfo s u],
    statePreds         :: Map sp (VarInfo s u),
    stateVars          :: Map String [VarInfo s u],
    labelPreds         :: Map lp (VarInfo s u, VarInfo s u),
    labelVars          :: Map String [VarInfo s u],
    --mappings from index to variable/predicate
    stateRev           :: Map Int (Variable sp s u),
    labelRev           :: Map Int (Variable lp s u, Bool)
}

updateInitPreds :: (Map sp (VarInfo s u) -> Map sp (VarInfo s u)) -> SymbolInfo s u sp lp -> SymbolInfo s u sp lp
updateInitPreds func rec = rec {initPreds = func (initPreds rec)}

updateInitVars :: (Map String [VarInfo s u] -> Map String [VarInfo s u]) -> SymbolInfo s u sp lp -> SymbolInfo s u sp lp
updateInitVars func rec = rec {initVars = func (initVars rec)}

updateStatePreds :: (Map sp (VarInfo s u) -> Map sp (VarInfo s u)) -> SymbolInfo s u sp lp -> SymbolInfo s u sp lp
updateStatePreds func rec = rec {statePreds = func (statePreds rec)}

updateStateVars :: (Map String [VarInfo s u] -> Map String [VarInfo s u]) -> SymbolInfo s u sp lp -> SymbolInfo s u sp lp
updateStateVars func rec = rec {stateVars = func (stateVars rec)}

updateLabelPreds :: (Map lp (VarInfo s u, VarInfo s u) -> Map lp (VarInfo s u, VarInfo s u)) -> SymbolInfo s u sp lp -> SymbolInfo s u sp lp
updateLabelPreds func rec = rec {labelPreds = func (labelPreds rec)}

updateLabelVars :: (Map String [VarInfo s u] -> Map String [VarInfo s u]) -> SymbolInfo s u sp lp -> SymbolInfo s u sp lp
updateLabelVars func rec = rec {labelVars = func (labelVars rec)}

updateStateRev :: (Map Int (Variable sp s u) -> Map Int (Variable sp s u)) -> SymbolInfo s u sp lp -> SymbolInfo s u sp lp
updateStateRev func rec = rec {stateRev = func (stateRev rec)}

updateLabelRev :: (Map Int (Variable lp s u, Bool) -> Map Int (Variable lp s u, Bool)) -> SymbolInfo s u sp lp -> SymbolInfo s u sp lp
updateLabelRev func rec = rec {labelRev = func (labelRev rec)}

--Sections
data SectionInfo s u = SectionInfo {
    trackedCube   :: DDNode s u,
    trackedNodes  :: [DDNode s u],
    trackedInds   :: [Int],
    untrackedCube :: DDNode s u,
    untrackedInds :: [Int],
    labelCube     :: DDNode s u,
    nextCube      :: DDNode s u,
    nextNodes     :: [DDNode s u]
}

updateTrackedNodes :: ([DDNode s u] -> [DDNode s u]) -> SectionInfo s u -> SectionInfo s u
updateTrackedNodes func rec = rec {trackedNodes = func (trackedNodes rec)}

updateTrackedInds :: ([Int] -> [Int]) -> SectionInfo s u -> SectionInfo s u
updateTrackedInds func rec = rec {trackedInds = func (trackedInds rec)}

updateUntrackedCubeM :: Monad m => (DDNode s u -> m (DDNode s u)) -> SectionInfo s u -> m (SectionInfo s u)
updateUntrackedCubeM = undefined

updateLabelCubeM :: Monad m => (DDNode s u -> m (DDNode s u)) -> SectionInfo s u -> m (SectionInfo s u)
updateLabelCubeM = undefined

updateNextCubeM :: Monad m => (DDNode s u -> m (DDNode s u)) -> SectionInfo s u -> m (SectionInfo s u)
updateNextCubeM = undefined

updateNextNodes :: ([DDNode s u] -> [DDNode s u]) -> SectionInfo s u -> SectionInfo s u
updateNextNodes = undefined

--Variable/predicate database
data DB s u sp lp = DB {
    symbolTable :: SymbolInfo s u sp lp,
    sections    :: SectionInfo s u,
    avlOffset   :: Int
}

updateSymbolTable :: (SymbolInfo s u sp lp -> SymbolInfo s u sp lp) -> DB s u sp lp -> DB s u sp lp
updateSymbolTable func rec = rec {symbolTable = func (symbolTable rec)}

updateSections :: (SectionInfo s u -> SectionInfo s u) -> DB s u sp lp -> DB s u sp lp
updateSections func rec = rec {sections = func (sections rec)}

updateSectionsM :: Monad m => (SectionInfo s u -> m (SectionInfo s u)) -> DB s u sp lp -> m (DB s u sp lp)
updateSectionsM = undefined

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
    offset <- gets avlOffset
    res    <- lift $ ithVar offset
    modify $ \st -> st {avlOffset = offset + 1}
    return (res, offset)

allocN :: Ops s u -> Int -> StateT (DB s u sp lp) (ST s) ([DDNode s u], [Int])
allocN Ops{..} size = do
    offset <- gets avlOffset
    let indices = iterate (+1) offset
    res    <- lift $ mapM ithVar indices
    modify $ \st -> st {avlOffset = offset + size}
    return (res, indices)

--Do the variable allocation and symbol table tracking

--initial state helpers
allocInitPred :: (Ord sp ) => Ops s u -> sp -> StateT (DB s u sp lp) (ST s) (DDNode s u)
allocInitPred ops p = liftM fst $ alloc ops =>= modify . updateSymbolTable . updateInitPreds . Map.insert p 

allocInitVar  :: Ops s u -> String -> Int -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocInitVar ops v size = liftM fst $ allocN ops size =>= modify . updateSymbolTable . updateInitVars . Map.insert v . uncurry zip

--goal helpers
allocStatePred :: Ord sp => Ops s u -> sp -> StateT (DB s u sp lp) (ST s) (DDNode s u)
allocStatePred ops pred = liftM fst $ alloc ops  =>= uncurry (promotePredToState pred)

allocStateVar :: Ops s u -> String -> Int -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocStateVar ops name size = liftM fst $ allocN ops size =>= uncurry (promoteVarToState name)

--TODO add to reverse map
promotePredToState :: Ord sp => sp -> DDNode s u -> Int -> StateT (DB s u sp lp) (ST s) ()
promotePredToState pred var idx = do
    modify $ updateSymbolTable $ addStatePredSymbol pred var idx
    modify $ updateSections    $ updateTrackedNodes (var :) . updateTrackedInds  (idx :)

promoteVarToState  :: String -> [DDNode s u] -> [Int] -> StateT (DB s u sp lp) (ST s) ()
promoteVarToState = undefined

--update helpers
allocUntrackedPred :: (Ord sp) => Ops s u -> sp -> StateT (DB s u sp lp) (ST s) (DDNode s u)
allocUntrackedPred ops pred = liftM fst $ alloc ops =>= uncurry (promotePredToUntracked ops pred)

allocUntrackedVar :: Ops s u -> String -> Int -> StateT (DB s u sp lp) (ST s) [DDNode s u]
allocUntrackedVar ops var size = liftM fst $ allocN ops size =>= uncurry (promoteVarToUntracked ops var)

addStatePredSymbol :: Ord sp => sp -> DDNode s u -> Int -> SymbolInfo s u sp lp -> SymbolInfo s u sp lp
addStatePredSymbol pred var idx = updateStatePreds (Map.insert pred (var, idx)) . updateStateRev (Map.insert idx undefined)

promotePredToUntracked :: Ord sp => Ops s u -> sp -> DDNode s u -> Int -> StateT (DB s u sp lp) (ST s) ()
promotePredToUntracked Ops{..} pred var idx = do
    modify  $ updateSymbolTable $ addStatePredSymbol pred var idx
    modifyM $ updateSectionsM   $ updateUntrackedCubeM $ band var

promoteVarToUntracked  :: Ops s u -> String -> [DDNode s u] -> [Int] -> StateT (DB s u sp lp) (ST s) ()
promoteVarToUntracked = undefined

allocLabelPred = undefined

allocLabelVar = undefined

withTmp' :: Ops s u -> (DDNode s u -> StateT (DB s u sp lp) (ST s) a) -> StateT (DB s u sp lp) (ST s) a
withTmp' Ops{..} func = do
    ind <- gets avlOffset
    var <- lift $ ithVar ind
    modify $ \st -> st {avlOffset = ind + 1}
    func var

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

monadOut :: Monad m => (a, m b) -> m (a, b)
monadOut (x, y) = do
    y <- y
    return (x, y)

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

initOps :: Ord sp => Ops s u -> VarOps (DB s u sp lp) (BAPred sp lp) BAVar s u
initOps ops = VarOps {withTmp = withTmp' ops, ..}
    where
    getPred (StatePred pred)    = getState func
        where
        func st = findWithDefaultM getNode pred (initPreds $ symbolTable st) (allocInitPred ops pred)
    getPred _                          = error "Requested non-state variable when compiling init section"
    getVar  (StateVar var size) = getState func
        where
        func st = findWithDefaultM (map getNode) var (initVars $ symbolTable st) (allocInitVar ops var size)
    getVar  _                          = error "Requested non-state variable when compiling init section"

doInit :: Ord sp => Ops s u -> (VarOps (DB s u sp lp) (BAPred sp lp) BAVar s u -> StateT (DB s u sp lp) (ST s) (DDNode s u)) -> StateT (DB s u sp lp) (ST s) (DDNode s u)
doInit ops complFunc = complFunc (initOps ops)

updateOps :: Ops s u -> VarOps (DB s u sp lp) (BAPred sp lp) BAVar s u
updateOps ops = VarOps {withTmp = withTmp' ops, ..}
    where
    getPred (StatePred pred) = getStatePart symbolTable func
        where
        func st = findWithDefaultM getNode pred (statePreds st) $ findWithDefaultProcessM getNode pred (initPreds st) (allocUntrackedPred ops pred) (uncurry $ promotePredToUntracked ops pred)
    getPred (LabelPred pred) = getStatePart symbolTable func
        where
        func st = findWithDefaultM pred (labelPreds st) $ allocLabelPred pred
    getVar  (StateVar var size) = getStatePart symbolTable func 
        where
        func st = findWithDefaultM (map getNode) var (stateVars st) $ findWithDefaultProcessM (map getNode) var (initVars st) (allocUntrackedVar ops var size) (promoteVarToUntracked ops var)
    getVar  (LabelVar var size) = getStatePart symbolTable func
        where
        func st = findWithDefaultM (map getNode) var (labelVars st) $ allocLabelVar  var

doUpdate :: Ops s u -> (VarOps (DB s u sp lp) (BAPred sp lp) BAVar s u -> StateT (DB s u sp lp) (ST s) (DDNode s u)) -> StateT (DB s u sp lp) (ST s) (DDNode s u)
doUpdate ops complFunc = complFunc (updateOps ops)

promote :: Ops s u -> (sp, VarInfo s u) -> (String, [VarInfo s u]) -> ST s ((sp, VarInfo s u), (String, [VarInfo s u]))
promote preds vars = do
    predRet <- sequence $ map (monadOut . (id *** const (alloc ops))) preds
    varRet  <- sequence $ map (monadOut . (id *** alloc ops . length)) vars
    promoteStuff

