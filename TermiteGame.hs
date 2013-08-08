{-# LANGUAGE PolymorphicComponents, RecordWildCards, ScopedTypeVariables, TemplateHaskell #-}
module TermiteGame (
    Abstractor(..),
    absRefineLoop,
    RefineStatic(..),
    RefineDynamic(..),
    RefineInfo(..),
    cex,
    strat
    ) where

import Control.Monad.ST
import Data.STRef.Lazy
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Arrow
import Data.List
import Control.Monad
import Data.Maybe
import Data.Tuple.All
import Data.Tuple
import Debug.Trace as T
import Control.Monad.State
import System.IO

import Safe
import Data.Text.Lazy hiding (intercalate, map, take, length, zip, replicate, foldl, concatMap, filter)
import Text.PrettyPrint.Leijen.Text
import Control.Monad.Morph
import Data.Graph
import Data.Tree

import Util
import RefineUtil
import BddRecord
import BddUtil
import BddInterp
import Interface
import RefineCommon hiding (doEnVars)

import Resource

debugLevel = 0

debugDo :: Monad m => Int -> m () -> m ()
debugDo lvl = when (lvl <= debugLevel) 

traceMsg :: String -> ST s ()
traceMsg m = unsafeIOToST $ do
    putStr m
    hFlush stdout

forAccumM i l f = foldM f i l

transSynopsys :: (Show sp, Show lp, Eq sp, Eq lp) => Ops s u -> sp -> DDNode s u -> StateT (DB s u sp lp) (ST s) ()
transSynopsys Ops{..} name trans = do
    SymbolInfo{..} <- gets _symbolTable
    lift $ do
        support <- supportIndices trans
        sz      <- dagSize trans
        let stateSup = nub $ catMaybes $ map (flip Map.lookup _stateRev) support
            labelSup = nub $ map fst $ catMaybes $ map (flip Map.lookup _labelRev) support
        --let doc = text (pack $ show name) <$$> indent 4 (text (pack $ "size: " ++ show sz) <$$> text (pack $ show stateSup ++ show labelSup)) 
        let doc = text (pack $ show name) <$$> indent 4 (text (pack $ "size: " ++ show sz) <$$> (list $ map (text . pack . show) stateSup ++ map (text . pack . show) labelSup))
        traceST $ show $ renderPretty 0.8 100 doc

--Input to the refinement algorithm. Represents the spec.
data Abstractor s u sp lp = Abstractor {
    goalAbs                 :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) [DDNode s u],
    fairAbs                 :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) [DDNode s u],
    initAbs                 :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) (DDNode s u),
    contAbs                 :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) (DDNode s u),
    updateAbs               :: forall pdb. [(sp, [DDNode s u])] -> VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) ([DDNode s u]),
    stateLabelConstraintAbs :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) (DDNode s u)
}

-- ===Data structures for keeping track of abstraction state===
data RefineStatic s u = RefineStatic {
    slRel :: DDNode s u,
    cont  :: DDNode s u,
    goal  :: [DDNode s u],
    fair  :: [DDNode s u],
    init  :: DDNode s u
}

derefStatic :: Ops s u -> RefineStatic s u -> ST s ()
derefStatic Ops{..} RefineStatic{..} = do
    deref cont
    mapM deref goal
    mapM deref fair
    deref init

data RefineDynamic s u = RefineDynamic {
    --relations
    --                         cube, rel
    trans                   :: [(DDNode s u, DDNode s u)],
    consistentMinusCULCont  :: DDNode s u,
    consistentPlusCULCont   :: DDNode s u,
    consistentMinusCULUCont :: DDNode s u,
    consistentPlusCULUCont  :: DDNode s u,
    inconsistentInit        :: DDNode s u
}

derefDynamic :: Ops s u -> RefineDynamic s u -> ST s ()
derefDynamic Ops{..} RefineDynamic{..} = do
    mapM (deref . fst) trans
    mapM (deref . snd) trans
    deref consistentMinusCULCont
    deref consistentPlusCULCont
    deref consistentMinusCULUCont
    deref consistentPlusCULUCont

dumpSizes :: Ops s u -> RefineDynamic s u -> ST s ()
dumpSizes Ops{..} RefineDynamic{..} = do
    let func x = do
        ds <- dagSize x
        traceST $ show ds
    mapM (func . snd) trans
    func consistentMinusCULCont
    func consistentPlusCULCont
    func consistentMinusCULUCont
    func consistentPlusCULUCont

type Lab s u = [([DDNode s u], DDNode s u)]

doEnVars :: (Ops s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)) -> Ops s u -> DDNode s u -> Lab s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)
doEnVars qFunc ops@Ops{..} strat envars = do
    $r $ return strat
    lift $ ref strat
    foldM func strat envars
    where
    func soFar (var, en) = do
        varCube <- $r $ nodesToCube var
        e <- $r1 (qFunc ops varCube) soFar
        $d deref varCube
        res <- $r2 (bite en) soFar e
        $d deref soFar
        $d deref e
        return res

doEnCont  = doEnVars bforall
doEnUCont = doEnVars bexists

groupSize = 1000

andLimit2 :: Ops s u -> Int -> DDNode s u -> DDNode s u -> ResourceT (DDNode s u) (ST s) (Maybe (DDNode s u))
andLimit2 Ops{..} limit x y = do
    dsx <- lift $ dagSize x
    case dsx > limit of
        True -> return Nothing
        False -> do
            dsy <- lift $ dagSize y
            case dsy > limit of 
                True -> return Nothing
                False -> do
                    res <- $r2 band x y
                    dsr <- lift $ dagSize res
                    case dsr > limit of
                        True -> do
                            $d deref res
                            return Nothing
                        False -> return $ Just res

groupTrels :: Ops s u -> [(DDNode s u, DDNode s u)] -> ResourceT (DDNode s u) (ST s) [(DDNode s u, DDNode s u)]
groupTrels ops@Ops{..} x = do
    groupTrels'' x
    where
    groupTrels'' [] = return []
    groupTrels'' (hd:rst) = groupTrels' hd rst
        where
        groupTrels' accum [] = return [accum]
        groupTrels' (accum@(accumCube, accumRel)) (allRels@((hdCube, hdRel):rels)) = do
            res <- andLimit2 ops groupSize accumRel hdRel 
            case res of 
                Nothing -> do
                    sz <- lift $ dagSize accumRel
                    res <- groupTrels'' allRels
                    return $ accum : res
                Just res -> do
                    mapM ($d deref) [accumRel, hdRel]
                    cb <- $r2 band accumCube hdCube
                    mapM ($d deref) [accumCube, hdCube]
                    groupTrels' (cb, res) rels

partitionedThing :: Ops s u -> [(DDNode s u, DDNode s u)] -> DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)
partitionedThing Ops{..} pairs win = do
    $r $ return win
    lift $ ref win
    forAccumM win pairs $ \win (cube, rel) -> do
        res <- liftM bnot $ $r2 (andAbstract cube) (bnot win) rel
        $d deref win
        return res

doHasOutgoings :: Ops s u -> [(DDNode s u, DDNode s u)] -> ResourceT (DDNode s u) (ST s) (DDNode s u)
doHasOutgoings Ops{..} pairs = do
    $r $ return btrue
    lift $ ref btrue
    forAccumM btrue pairs $ \has (cube, rel) -> do
        rr <- $r1 (bexists cube) rel
        a <- $r2 band rr has
        $d deref has
        $d deref rr
        return a

--Find the <state, untracked, label> tuples that are guaranteed to lead to the goal for a given transition relation
cpre' :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)
cpre' ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} target = do
    nextWin  <- $r1 mapVars target
    strat    <- partitionedThing ops trans nextWin
    $d deref nextWin
    return strat
   
--Returns the set of <state, untracked> pairs that are winning 
cpre'' :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> DDNode s u -> DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)
cpre'' ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} hasOutgoingsCont labelPreds cc cu target = do
    strat       <- cpre' ops si rd target
    stratContHas' <- $r2 band strat hasOutgoingsCont
    stratContHas <- $r2 band stratContHas' slRel
    $d deref stratContHas'
    stratCont    <- doEnCont ops stratContHas labelPreds
    $d deref stratContHas
    asdf         <- $r2 band slRel (bnot strat)
    $d deref strat
    stratUCont   <- doEnCont ops asdf labelPreds
    $d deref asdf
    winCont      <- $r2 (andAbstract _labelCube) cc stratCont
    winUCont     <- liftM bnot $ $r2 (andAbstract _labelCube) cu stratUCont
    mapM ($d deref) [stratCont, stratUCont]
    win          <- $r3 bite cont winCont winUCont
    mapM ($d deref) [winCont, winUCont]
    return win

--Returns the set of <state, untracked> pairs that are winning 
cpreOver' :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)
cpreOver' ops si rs rd@RefineDynamic{..} hasOutgoingsCont labelPreds = cpre'' ops si rs rd hasOutgoingsCont labelPreds consistentPlusCULCont consistentMinusCULUCont 
    
--Returns the set of <state, untracked> pairs that are winning 
cpreUnder' :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)
cpreUnder' ops si rs rd@RefineDynamic{..} hasOutgoingsCont labelPreds = cpre'' ops si rs rd hasOutgoingsCont labelPreds consistentMinusCULCont consistentPlusCULUCont

cPreHelper cpreFunc quantFunc ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} hasOutgoingsCont labelPreds target = do
    su  <- cpreFunc ops si rs rd hasOutgoingsCont labelPreds target
    res <- $r1 (quantFunc _untrackedCube) su
    $d deref su
    return res

cPreOver :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)
cPreOver ops@Ops{..} = cPreHelper cpreOver' bexists ops  

cPreUnder :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)
cPreUnder ops@Ops{..} = cPreHelper cpreUnder' bforall ops

fixedPointR :: Ops s u -> (DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)) -> DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)
fixedPointR ops@Ops{..} func start = do
    res <- func start
    $d deref start 
    case (res==start) of --this is safe 
        True -> return start
        False -> fixedPointR ops func res

solveFair :: (DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)) -> Ops s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)
solveFair cpreFunc ops@Ops{..} rs@RefineStatic{..} startPt winning fairr = do
    lift $ ref startPt
    $r $ return startPt
    fixedPointR ops func startPt
    where
    func target = do
        lift $ debugDo 1 $ traceST "solveFair: iteration"
        lift $ check "solveFair" ops
        t1 <- $r2 band target fairr
        t2 <- $r2 bor t1 winning
        $d deref t1
        res <- cpreFunc t2
        $d deref t2
        return res

solveReach :: (DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)) -> Ops s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)
solveReach cpreFunc ops@Ops{..} rs@RefineStatic{..} startPt goall = do
    $r $ return bfalse
    lift $ ref bfalse
    fixedPointR ops func bfalse
    where
    func target = do
        lift $ debugDo 1 $ traceST "solveReach: iteration"
        sz <- lift $ dagSize target
        lift $ traceMsg $ "r(" ++ show sz ++ ")"
        t1 <- $r2 bor target goall
        $r $ return bfalse
        lift $ ref bfalse
        res <- forAccumM bfalse fair $ \accum val -> do
            res' <- solveFair cpreFunc ops rs startPt t1 val
            res  <- $r2 bor res' accum
            $d deref res'
            $d deref accum
            return res
        $d deref t1
        return res

solveBuchi :: (DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)) -> Ops s u -> RefineStatic s u -> DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)
solveBuchi cpreFunc ops@Ops{..} rs@RefineStatic{..} startingPoint = do
    $r $ return startingPoint
    lift $ ref startingPoint
    fixedPointR ops func startingPoint
    where
    func reachN = do
        lift $ traceMsg "b"
        lift $ debugDo 1 $ traceST "solveBuchi: iteration"
        $r $ return btrue
        lift $ ref btrue
        res <- forAccumM btrue goal $ \accum val -> do
            lift $ traceMsg "g"
            t1 <- $r2 band reachN val
            --TODO terminate when t1s are equal
            res' <- solveReach cpreFunc ops rs reachN t1
            $d deref t1
            res <- $r2 band res' accum
            $d deref res'
            $d deref accum
            return res
        return res

check msg ops = return ()
--check msg ops = unsafeIOToST (putStrLn ("checking bdd consistency" ++ msg ++ "\n")) >> debugCheck ops >> checkKeys ops

mkVarsMap :: (Ord b) => [(a, [b])] -> Map b [a]
mkVarsMap args = foldl f Map.empty args
    where
    f mp (a, bs) = foldl g mp bs 
        where
        g mp b = case Map.lookup b mp of
            Just x  -> Map.insert b (a:x) mp
            Nothing -> Map.insert b [a] mp

mkInitConsistency :: (Ord lv, Ord lp) => Ops s u -> (lp -> [lv]) -> Map lv [lp] -> Map lp (DDNode s u) -> [(lp, DDNode s u)] -> DDNode s u -> ResourceT (DDNode s u) (ST s) (DDNode s u)
mkInitConsistency Ops{..} getVars mp mp2 labs initCons = do
    $r $ return btrue
    lift $ ref btrue
    forAccumM btrue labs $ \accum (lp, en) -> do
        let theOperlappingPreds = concatMap (fromJustNote "mkInitConsistency" . flip Map.lookup mp) (getVars lp)
            theEns              = map (fromJustNote "mkInitConsistency2" . flip Map.lookup mp2) theOperlappingPreds
        forAccumM accum theEns $ \accum theEn -> do
            constr <- $r $ bnot en .| bnot theEn
            res <- $r2 band accum constr
            mapM ($d deref) [constr, accum]
            return res

--Create an initial abstraction and set up the data structures
initialAbstraction :: (Show sp, Show lp, Ord sp, Ord lp, Ord lv) => Ops s u -> Abstractor s u sp lp -> TheorySolver s u sp lp lv -> StateT (DB s u sp lp) (ResourceT (DDNode s u) (ST s)) (RefineDynamic s u, RefineStatic s u)
initialAbstraction ops@Ops{..} Abstractor{..} TheorySolver{..} = do
    lift $ lift $ check "InitialAbstraction start" ops
    --abstract init
    initExpr <- hoist lift $ doInit ops initAbs
    lift $ $r $ return initExpr
    lift $ lift $ check "After compiling init" ops
    --abstract the goal
    (goalExprs, newVarsGoals) <- hoist lift $ doGoal ops goalAbs
    lift $ mapM ($r . return) goalExprs
    lift $ lift $ check "After compiling goal" ops
    --abstract the fair region
    (fairExprs, newVarsFairs) <- hoist lift $ doGoal ops fairAbs
    lift $ mapM ($r . return) fairExprs
    lift $ lift $ check "After compiling fair" ops
    --abstract the controllable condition
    (contExpr, newVarsCont) <- hoist lift $ doGoal ops contAbs
    lift $ $r $ return contExpr
    lift $ lift $ check "After compiling controllable" ops
    --abstract the stateLabelConstraint 
    (stateLabelExpr, newVarsStateLabel) <- hoist lift $ doStateLabel ops stateLabelConstraintAbs
    lift $ $r $ return stateLabelExpr
    lift $ lift $ check "After compiling stateLabelConstraint" ops
    --get the abstract update functions for the goal predicates and variables
    let toUpdate = nub $ _allocatedStateVars newVarsGoals ++ _allocatedStateVars newVarsFairs ++ _allocatedStateVars newVarsCont
    lift $ lift $ traceST $ "Initial transition relation state vars: \n" ++ (intercalate "\n" $ map (('\t' :) . show . fst) $ toUpdate)
    updateExprs' <- hoist lift $ doUpdate ops (updateAbs toUpdate)
    lift $ mapM ($r . return) updateExprs'
    outcomeCube <- gets $ _outcomeCube . _sections
    updateExprs <- lift $ mapM ($r . bexists outcomeCube) updateExprs'
    lift $ mapM ($d deref) updateExprs'
    hoist lift $ zipWithM (transSynopsys ops) (map fst toUpdate) updateExprs
    cubes <- lift $ mapM ($r . nodesToCube . snd) toUpdate
    groups <- lift $ groupTrels ops $ zip cubes updateExprs
    lift $ lift $ traceST $ "Number of transition partitions: " ++ show (length groups)

    --create the consistency constraints
    let consistentPlusCULCont  = btrue
        consistentPlusCULUCont = btrue
    lift $ lift $ ref consistentPlusCULCont
    lift $ lift $ ref consistentPlusCULUCont
    lift $ $r $ return consistentPlusCULCont
    lift $ $r $ return consistentPlusCULUCont
    let inconsistentInit = bfalse
    lift $ lift $ ref inconsistentInit
    lift $ $r $ return inconsistentInit

    --compute the initial consistentMinus being as liberal as possible
    labelPreds <- gets $ _labelVars . _symbolTable
    let theMap = mkVarsMap $ map (id &&& getVarsLabel) $ Map.keys labelPreds
    lift $ $r $ return btrue
    lift $ lift $ ref btrue
    consistentMinusCULCont <- lift $ mkInitConsistency ops getVarsLabel theMap (Map.map sel3 labelPreds) (map (id *** sel3) $ Map.toList labelPreds) btrue
    --lift $ lift $ traceST $ bddSynopsis ops consistentMinusCULCont 

    --consistentMinusCULCont <- lift $ $r $ conj ops $ map (bnot . sel3) $ Map.elems labelPreds

    let consistentMinusCULUCont = consistentMinusCULCont
    lift $ lift $ ref consistentMinusCULUCont
    lift $ $r $ return consistentMinusCULUCont
    --construct the RefineDynamic and RefineStatic
    let rd = RefineDynamic {
            trans  = groups,
            ..
        }
        rs = RefineStatic {
            slRel = stateLabelExpr,
            goal  = goalExprs,
            fair  = fairExprs,
            init  = initExpr,
            cont  = contExpr
        }
    return (rd, rs)

refineStrategy = refineFirstPrime

pickUntrackedToPromote :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> RefineStatic s u -> Lab s u -> DDNode s u -> DDNode s u -> DDNode s u -> DDNode s u -> ResourceT (DDNode s u) (ST s) (Maybe [Int])
pickUntrackedToPromote ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} rs@RefineStatic{..} labelPreds hasOutgoings win lastLFP fairr = do
    win''  <- $r2 band win fairr
    win'   <- $r2 bor win'' lastLFP
    $d deref win''
    su     <- cpreOver' ops si rs rd hasOutgoings labelPreds win'
    $d deref win'
    toDrop <- $r2 band (bnot su) win
    $d deref su
    res    <- lift $ refineStrategy ops si toDrop
    $d deref toDrop
    return res

--Promote untracked state variables to full state variables so that we can make progress towards the goal. Does not refine the consistency relations.
promoteUntracked :: (Ord lp, Ord sp, Ord lv, Show sp, Show lp) => Ops s u -> Abstractor s u sp lp -> TheorySolver s u sp lp lv -> RefineDynamic s u -> [Int] -> StateT (DB s u sp lp) (ResourceT (DDNode s u) (ST s)) (RefineDynamic s u)
promoteUntracked ops@Ops{..} Abstractor{..} TheorySolver{..} rd@RefineDynamic{..} indices = do
    --look up the predicates to promote
    stateRev             <- gets $ _stateRev . _symbolTable
    let refineVars       =  nub $ map (fromJustNote "promoteUntracked: untracked indices not in stateRev" . flip Map.lookup stateRev) indices
    lift $ lift $ traceST $ "* Promoting: \n" ++ (intercalate "\n" $ map (('\t' :) . show) $ refineVars)

    NewVars{..}          <- hoist lift $ promoteUntrackedVars ops refineVars
    labelPredsPreUpdate  <- gets $ _labelVars . _symbolTable

    --compute the update functions
    updateExprs'   <- hoist lift $ doUpdate ops (updateAbs _allocatedStateVars)
    lift $ mapM ($r . return) updateExprs'
    outcomeCube <- gets $ _outcomeCube . _sections
    updateExprs  <- lift $ mapM ($r . bexists outcomeCube) updateExprs'
    lift $ mapM ($d deref) updateExprs'
    hoist lift $ zipWithM (transSynopsys ops) (map fst _allocatedStateVars) updateExprs
    cubes <- lift $ mapM ($r . nodesToCube . snd) _allocatedStateVars
    groups <- lift $ groupTrels ops $ zip cubes updateExprs
    lift $ lift $ traceST $ "Number of transition partitions: " ++ show (length groups)

    labelPreds              <- gets $ _labelVars . _symbolTable
    let newLabelPreds       = labelPreds Map.\\ labelPredsPreUpdate
    let theMap              = mkVarsMap $ map (id &&& getVarsLabel) $ Map.keys labelPreds
    consistentMinusCULCont' <- lift $ mkInitConsistency ops getVarsLabel theMap (Map.map sel3 labelPreds) (map (id *** sel3) $ Map.toList newLabelPreds) consistentMinusCULCont
    --TODO update uncontrollable consistency as well

    return rd {
        --TODO does this order matter?
        trans  = groups ++ trans,
        consistentMinusCULCont = consistentMinusCULCont'
    }

refineConsistency :: (Ord sp, Ord lp, Ord lv, Show sp, Show lp) => Ops s u -> TheorySolver s u sp lp lv -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> DDNode s u -> DDNode s u -> StateT (DB s u sp lp) (ResourceT (DDNode s u) (ST s)) (Bool, RefineDynamic s u)
refineConsistency ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} hasOutgoings win winning fairr = do
    (res, rd) <- refineConsistencyCont ops ts rd rs hasOutgoings win winning fairr
    case res of
        True -> do
            return $ (res, rd)
        False  -> do
            res <- refineConsistencyUCont ops ts rd rs win winning fairr
            return res

refineConsistencyCont :: (Ord sp, Ord lp, Ord lv, Show sp, Show lp) => Ops s u -> TheorySolver s u sp lp lv -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> DDNode s u -> DDNode s u -> StateT (DB s u sp lp) (ResourceT (DDNode s u) (ST s)) (Bool, RefineDynamic s u)
refineConsistencyCont ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} hasOutgoings win winning fairr = do
    lift $ check "refineConsistencyCont" ops
    syi@SymbolInfo{..} <- gets _symbolTable 
    si@SectionInfo{..} <- gets _sections
    win''              <- lift $ $r2 band win fairr
    win'               <- lift $ $r2 bor win'' winning
    lift $ $d deref win''
    winNoConstraint'   <- lift $ cpre' ops si rd win'
    stratContHas'      <- lift $ $r2 band winNoConstraint' hasOutgoings
    stratContHas       <- lift $ $r2 band stratContHas' slRel
    lift $ $d deref stratContHas'
    lift $ $d deref winNoConstraint'
    let lp             =  map (sel1 &&& sel3) $ Map.elems _labelVars
    winNoConstraint    <- lift $ doEnCont ops stratContHas lp
    lift $ $d deref stratContHas
    winNoConstraint2   <- lift $ $r2 band cont winNoConstraint
    lift $ mapM ($d deref) [win', winNoConstraint]
    (res, (consistentPlusCULCont', consistentMinusCULCont'))  <- doConsistency ops ts consistentPlusCULCont consistentMinusCULCont winNoConstraint2
    lift $ lift $ check "refineConsistencyCont End" ops
    let rd' = rd {consistentPlusCULCont = consistentPlusCULCont', consistentMinusCULCont = consistentMinusCULCont'}
    return (res, rd')

refineConsistencyUCont :: (Ord sp, Ord lp, Ord lv, Show sp, Show lp) => Ops s u -> TheorySolver s u sp lp lv -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> DDNode s u -> StateT (DB s u sp lp) (ResourceT (DDNode s u) (ST s)) (Bool, RefineDynamic s u)
refineConsistencyUCont ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} win winning fairr = do
    lift $ check "refineConsistencyUCont" ops
    syi@SymbolInfo{..} <- gets _symbolTable 
    si@SectionInfo{..} <- gets _sections
    win''              <- lift $ $r2 band win fairr
    win'               <- lift $ $r2 bor  win'' winning
    lift $ $d deref win''
    winNoConstraint''  <- lift $ cpre' ops si rd win'
    winNoConstraint'   <- lift $ $r2 band (bnot winNoConstraint'') slRel
    lift $ $d deref winNoConstraint''
    let lp             =  map (sel1 &&& sel3) $ Map.elems _labelVars
    winNoConstraint    <- lift $ doEnCont ops winNoConstraint' lp
    lift $ $d deref winNoConstraint'
    winNoConstraint2   <- lift $ $r2 band (bnot cont) winNoConstraint
    lift $ mapM ($d deref) [win', winNoConstraint]
    (res, (consistentPlusCULUCont', consistentMinusCULUCont')) <- doConsistency ops ts consistentPlusCULUCont consistentMinusCULUCont winNoConstraint2
    lift $ lift $ check "refineConsistencyUCont End" ops
    let rd' = rd {consistentPlusCULUCont = consistentPlusCULUCont', consistentMinusCULUCont = consistentMinusCULUCont'}
    return (res, rd')

sccs :: (Ord lv, Ord lp, Show lp) => SymbolInfo s u sp lp -> TheorySolver s u sp lp lv -> [(lp, a)] -> [[(lp, a)]]
sccs SymbolInfo{..} TheorySolver{..} labelCube = fmap (flatten . fmap (sel1 . func)) $ components theGraph
    where
    list             = map func labelCube
        where
        func pred    = (pred, fst pred, filter (flip elem (map fst labelCube)) $ concatMap (fromJust . flip Map.lookup vMap) $ getVarsLabel (fst pred))
    (theGraph, func) = graphFromEdges' list 
    vMap             = mkVarsMap $ map (id &&& getVarsLabel) $ Map.keys _labelVars

doConsistency :: (Ord sp, Ord lp, Ord lv, Show sp, Show lp) => Ops s u -> TheorySolver s u sp lp lv -> DDNode s u -> DDNode s u -> DDNode s u -> StateT (DB s u sp lp) (ResourceT (DDNode s u) (ST s)) (Bool, (DDNode s u, DDNode s u))
doConsistency ops@Ops{..} ts@TheorySolver{..} cPlus cMinus winNoConstraint = do
    syi@SymbolInfo{..} <- gets _symbolTable 
    si@SectionInfo{..} <- gets _sections
    winActOver         <- lift $ $r2 band winNoConstraint cPlus
    winActUnder        <- lift $ $r2 (andAbstract _labelCube) winNoConstraint cMinus
    toCheckConsistency <- lift $ $r2 band winActOver (bnot winActUnder)
    lift $ mapM ($d deref) [winActOver, winActUnder]
    --Alive : toCheckConsistency
    case toCheckConsistency==bfalse of 
        True  -> do
            --no refinement of consistency relations will shrink the winning region
            --lift $ lift $ debugDo 2 $ traceST "no consistency refinement possible"
            lift $ mapM ($d deref) [toCheckConsistency, winNoConstraint]
            return (False, (cPlus, cMinus))
        False -> do
            --There may be a refinement
            --extract a <s, u, l> pair that will make progress if one exists
            c <- lift $ lift $ presentInLargePrime ops toCheckConsistency
            lift $ $d deref toCheckConsistency

            let (cStatePreds, cLabelPreds) = partitionStateLabelPreds si syi c
            --Alive : nothing
            let groupedState = groupForUnsatCore (sel2 . fromJustNote "doConsistency" . flip Map.lookup _stateVars) cStatePreds
                groupedLabel = groupForUnsatCore (sel2 . fromJustNote "doConsistency" . flip Map.lookup _labelVars) cLabelPreds
            let fmt (name, enc) = show name ++ ":" ++ map (alt 'T' 'F') enc
            lift $ lift $ traceMsg $ "* Refining Consistency: " ++ intercalate ", " (map fmt groupedState) ++ " -- " ++ intercalate ", " (map fmt groupedLabel) ++ " ..."
            case unsatCoreStateLabel groupedState groupedLabel of
                Just (statePairs, labelPairs) -> do
                    --statePairs, labelPairs is inconsistent so subtract this from consistentPlusCUL
                    lift $ lift $ traceST "UNSAT"
                    inconsistent       <- lift $ stateLabelInconsistent ops syi statePairs labelPairs
                    consistentPlusCUL' <- lift $ $r2 band cPlus (bnot inconsistent)
                    lift $ $d deref cPlus
                    lift $ $d deref inconsistent
                    lift $ check "refineConsistency4" ops
                    doConsistency ops ts consistentPlusCUL' cMinus winNoConstraint
                Nothing -> do
                    --the (s, u, l) tuple is consistent so add this to consistentMinusCUL
                    lift $ $d deref winNoConstraint
                    lift $ lift $ traceST "SAT"

                    let scs = sccs syi ts groupedLabel
                    let labelPreds = _labelVars 
                    let theMap = mkVarsMap $ map (id &&& getVarsLabel) $ Map.keys labelPreds
                    cMinus' <- forAccumM cMinus scs $ \cons scc_val -> do
                        let scc = map fst scc_val
                        lift $ lift $ traceST $ "SCC: " ++ show scc
                        let allPreds = concatMap (fromJustNote "doConsistency" . flip Map.lookup theMap) $ nub $ concatMap getVarsLabel scc
                        lift $ lift $ traceST $ "All preds: " ++ show allPreds
                        let fringePreds = allPreds \\ scc
                        lift $ lift $ traceST $ "Fringe Preds: " ++ show fringePreds
                        lift $ lift $ traceST ""
                        let labelPreds' = map (first $ fromJustNote "refineConsistency" . flip Map.lookup _labelVars) scc_val
                        let func (l, pol) = [(sel1 l, pol), ([sel3 l], [True])]
                        let allEns = map (sel3 . fromJustNote "refineConsistency" . flip Map.lookup _labelVars) allPreds
                        thisLabel <- lift $ makeCubeInt ops $ concatMap func labelPreds'
                        eQuantExpr <- hoist lift $ doUpdate ops (eQuant scc_val)
                        lift $ $r $ return eQuantExpr
                        allCube <- lift $ $r $ nodesToCube allEns
                        allCubeFalse <- lift $ $r $ makeCube ops $ zip allEns (repeat False)
                        cons1 <- lift $ $r2 band cons allCubeFalse
                        lift $ $d deref allCubeFalse
                        cons2 <- lift $ $r2 bexists allCube cons1
                        lift $ $d deref allCube
                        lift $ $d deref cons1
                        cons3 <- lift $ $r2 band cons2 eQuantExpr
                        lift $ $d deref cons2
                        lift $ $d deref eQuantExpr
                        cons4 <- lift $ $r2 band cons3 thisLabel
                        lift $ $d deref cons3
                        lift $ $d deref thisLabel
                        cons5 <- lift $ $r2 bor cons4 cons
                        lift $ $d deref cons4
                        lift $ $d deref cons
                        return cons5

                    return $ (True, (cPlus, cMinus'))

mSumMaybe :: Monad m => [m (Maybe a)] -> m (Maybe a)
mSumMaybe (x:xs) = do
    res <- x
    case res of
        Nothing -> mSumMaybe xs
        Just y  -> return $ Just y
mSumMaybe [] = return Nothing

forAccumLM :: Monad m => acc -> [x] -> (acc -> x -> m (acc, y)) -> m (acc, [y])
forAccumLM a b c = mapAccumLM c a b

fixedPoint2 :: Ops s u -> DDNode s u -> a -> (DDNode s u -> a -> ST s (DDNode s u, a)) -> ST s (DDNode s u, a)
fixedPoint2 ops@Ops{..} start thing func = do
    (res, thing') <- func start thing
    deref start 
    case (res==start) of 
        True -> return (start, thing')
        False -> fixedPoint2 ops res thing' func

strategy :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> Lab s u -> DDNode s u -> ResourceT (DDNode s u) (ST s) [[DDNode s u]]
strategy ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} labelPreds win = do
    lift $ traceST "* Computing strategy"
    hasOutgoings <- doHasOutgoings ops trans
    --For each goal
    res <- forM goal $ \goal -> do 
        winAndGoal <- $r2 band goal win
        $r $ return bfalse
        lift $ ref bfalse
        --Reachabiliy least fixedpoint
        res <- fixedPoint2R ops bfalse (repeat bfalse) $ \soFar strats -> do 
            soFarOrWinAndGoal <- $r2 bor soFar winAndGoal
            $r $ return bfalse
            lift $ ref bfalse
            --For each fair
            (res, strats') <- forAccumLM bfalse fair $ \accum fair -> do
                --Fairness greatest fixedpoint
                --TODO optimise: dont use btrue below
                winFair <- solveFair (cPreUnder ops si rs rd hasOutgoings labelPreds)  ops rs btrue soFarOrWinAndGoal fair
                thing <- $r2 band winFair fair
                $d deref winFair
                thing2 <- $r2 bor thing soFarOrWinAndGoal
                $d deref thing
                (win', strats) <- cpre hasOutgoings thing2
                $d deref thing2
                win <- $r2 bor win' accum 
                $d deref win'
                when (winFair /= win') (error "wrs not equal")
                return (win, strats)
            $d deref soFarOrWinAndGoal
            strats <- zipWithM (combineStrats soFar) strats strats'
            return (res, strats)
        $d deref winAndGoal
        return res
    $d deref hasOutgoings
    let (wins, strats) = unzip res
    win' <- $r $ conj ops wins
    mapM ($d deref) wins
    $d deref win'
    when (win' /= win) (error "Winning regions are not equal in strategy generation")
    return strats
    where
    combineStrats prevWin oldC newC = do
        c <- $r2 band newC (bnot prevWin)
        $d deref newC
        c' <- $r2 bor c oldC
        $d deref oldC
        return c'
    cpre hasOutgoings target = do
        strat      <- cpre' ops si rd target
        stratContHas <- $r2 band strat hasOutgoings
        stratCont  <- doEnCont ops stratContHas labelPreds
        $d deref stratContHas
        stratUCont <- doEnCont ops (bnot strat) labelPreds
        $d deref strat
        winCont    <- $r2 (andAbstract _labelCube) consistentMinusCULCont stratCont
        winUCont   <- liftM bnot $ $r2 (andAbstract _labelCube) consistentPlusCULUCont stratUCont
        su         <- $r3 bite cont winCont winUCont
        win        <- $r1 (bforall _untrackedCube) su
        $d deref su
        mapM ($d deref) [winCont, stratUCont, winUCont]
        return (win, stratCont)

fixedPoint2R :: Ops s u -> DDNode s u -> a -> (DDNode s u -> a -> ResourceT (DDNode s u) (ST s) (DDNode s u, a)) -> ResourceT (DDNode s u) (ST s) (DDNode s u, a)
fixedPoint2R ops@Ops{..} start thing func = do
    (res, thing') <- func start thing
    $d deref start 
    case (res==start) of 
        True -> return (start, thing')
        False -> fixedPoint2R ops res thing' func

counterExample :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> Lab s u -> DDNode s u -> ResourceT (DDNode s u) (ST s) [[DDNode s u]]
counterExample ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} labelPreds win = do
    lift $ traceST "* Computing counterexample"
    hasOutgoings <- doHasOutgoings ops trans 
    lift $ sequence $ replicate (length goal * length fair) (ref bfalse)
    sequence $ replicate (length goal * length fair + 1) ($r $ return bfalse)
    lift $ ref bfalse
    (win', strat) <- fixedPoint2R ops bfalse (zip goal $ repeat $ zip fair $ repeat bfalse) $ \win strat -> do
        lift $ ref bfalse
        $r $ return bfalse
        res <- forAccumLM bfalse strat $ \tot (goal, strats) -> do
            tgt               <- $r2 bor (bnot goal) win
            --TODO optimise: dont use btrue below
            winBuchi          <- liftM bnot $ solveReach (cPreOver ops si rs rd hasOutgoings labelPreds) ops rs btrue (bnot tgt)
            (winStrat, strat) <- stratReach si rs rd hasOutgoings fair win strats winBuchi tgt
            when (winStrat /= winBuchi) (lift $ traceST "Warning: counterexample winning regions are not equal")
            $d deref winStrat
            $d deref tgt
            tot' <- $r2 bor tot winBuchi
            mapM ($d deref) [tot, winBuchi]
            return (tot', (goal, strat))
        return res
    when (win /= bnot win') (error "the counterexample winning region is not the complement of the game winning region")
    lift $ traceST $ bddSynopsis ops win
    $d deref hasOutgoings
    return $ map (map snd . snd) strat

    where

    target fair goal winN reach = do
        a   <- $r2 bor reach fair
        b   <- $r2 band a winN
        $d deref a
        c   <- $r2 band b goal
        $d deref b
        return c

    --TODO check winning regions coincide
    stratReach si rs rd hasOutgoings fairs startingWin stratSoFar winN goal = do
        $r $ return startingWin
        lift $ ref startingWin
        fixedPoint2R ops startingWin stratSoFar $ \reach strat -> do
            $r $ return btrue
            lift $ ref btrue
            res <- forAccumLM btrue strat $ \winAccum (fair, strat) -> do
                tgt            <- target fair goal winN reach
                (win', strat') <- strategy si rs rd hasOutgoings tgt
                $d deref tgt
                strat''        <- $r2 band strat' (bnot reach)
                $d deref strat'
                --TODO use ite for strat
                strat'''       <- $r2 bor strat'' strat
                $d deref strat''
                $d deref strat
                win            <- $r1 (bforall _untrackedCube) win'
                $d deref win'
                winAccum'      <- $r2 band winAccum win
                mapM ($d deref) [win, winAccum]
                return (winAccum', (fair, strat'''))
            return res

    strategy SectionInfo{..} RefineStatic{..} RefineDynamic{..} hasOutgoings target = do
        strt        <- cpre' ops si rd (bnot target)
        stratContHas <- $r2 band strt hasOutgoings
        stratCont'  <- doEnCont ops stratContHas labelPreds
        $d deref stratContHas
        winCont     <- liftM bnot $ $r2 (andAbstract _labelCube) consistentPlusCULCont stratCont'
        $d deref stratCont'
        stratUCont' <- doEnCont ops (bnot strt) labelPreds
        $d deref strt
        stratUCont  <- $r2 band consistentMinusCULUCont stratUCont'
        $d deref stratUCont'
        winUCont    <- $r1 (bexists _labelCube) stratUCont
        win         <- $r3 bite cont winCont winUCont
        mapM ($d deref) [winCont, winUCont]
        return (win, stratUCont)

data RefineInfo s u sp lp = RefineInfo {
    si :: SectionInfo s u,
    rs :: RefineStatic s u,
    rd :: RefineDynamic s u,
    db :: DB s u sp lp,
    lp :: Lab s u,
    wn :: DDNode s u,
    op :: Ops s u
}

refineInit :: Ord sp => Ops s u -> TheorySolver s u sp lp lv -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> StateT (DB s u sp lp) (ResourceT (DDNode s u) (ST s)) (RefineDynamic s u, Bool)
refineInit ops@Ops{..} ts@TheorySolver{..} rs@RefineStatic{..} rd@RefineDynamic{..} winRegion = do
    syi@SymbolInfo{..} <- gets _symbolTable 
    si@SectionInfo{..} <- gets _sections
    winning <- lift $ lift $ leqUnless (bnot winRegion) (bnot init) inconsistentInit
    case winning of 
        False -> do
            witness' <- lift $ $r2 band init (bnot winRegion)
            witness  <- lift $ $r2 band witness' (bnot inconsistentInit)
            lift $ $d deref witness'
            c <- lift $ lift $ presentInLargePrime ops witness
            lift $ $d deref witness
            let groupedState = groupForUnsatCore (sel2 . fromJustNote "refineInit" . flip Map.lookup _stateVars) $ indicesToStatePreds' syi c
            case unsatCoreState groupedState of
                Nothing -> return (rd, False)
                Just uc -> do
                    lift $ lift $ traceST "* Found inconsistent initial state. Refining..."
                    unsat <- lift $ makeCubeInt ops $ map (first (sel1 . fromJustNote "refineInit" . flip Map.lookup _stateVars)) uc
                    inconsistentInit' <- lift $ $r2 bor inconsistentInit unsat
                    lift $ $d deref inconsistentInit 
                    lift $ $d deref unsat
                    refineInit ops ts rs (rd {inconsistentInit = inconsistentInit'}) winRegion
        True  -> return (rd, True)

--The abstraction-refinement loop
absRefineLoop :: forall s u o sp lp lv. (Ord sp, Ord lp, Show sp, Show lp, Ord lv) => STDdManager s u -> Abstractor s u sp lp -> TheorySolver s u sp lp lv -> o -> ResourceT (DDNode s u) (ST s) (Bool, RefineInfo s u sp lp)
absRefineLoop m spec ts abstractorState = let ops@Ops{..} = constructOps m in do
    idb <- lift $ initialDB ops
    ((winning, (si, rs, rd, lp, wn)), db) <- flip runStateT idb $ do
        (rd, rs) <- initialAbstraction ops spec ts
        lift $ lift $ debugDo 1 $ traceST "Refinement state after initial abstraction: " 
        lift $ lift $ debugDo 1 $ traceST $ "Goal is: " ++ (intercalate ", " $ map (bddSynopsis ops) $ goal rs)
        lift $ lift $ debugDo 1 $ traceST $ "Fair is: " ++ (intercalate ", " $ map (bddSynopsis ops) $ fair rs)
        lift $ lift $ debugDo 1 $ traceST $ "Init is: " ++ (bddSynopsis ops $ TermiteGame.init rs)
        lift $ lift $ ref btrue
        lift $ $r $ return btrue
        refineLoop ops rs rd btrue
    return $ (winning, RefineInfo{op=ops, ..})
    where
    refineLoop ops@Ops{..} rs@RefineStatic{..} = refineLoop'
        where 
        refineLoop' rd@RefineDynamic{..} lastWin = do
            si@SectionInfo{..} <- gets _sections
            lift $ lift $ setVarMap _trackedNodes _nextNodes
            labelPreds <- gets $ _labelVars . _symbolTable
            let lp = map (sel1 &&& sel3) $ Map.elems labelPreds
            hasOutgoings <- lift $ doHasOutgoings ops trans
            winRegion <- lift $ solveBuchi (cPreOver ops si rs rd hasOutgoings lp) ops rs lastWin
            lift $ lift $ traceST ""
            lift $ $d deref lastWin
            (rd, winning) <- refineInit ops ts rs rd winRegion
            --Alive: winRegion, rd, rs, hasOutgoings
            case winning of
                False -> lift $ do
                    lift $ traceST "Losing"
                    mapM ($d deref) [hasOutgoings]
                    return (False, (si, rs, rd, lp, winRegion))
                True -> do
                    --lift $ lift $ traceST "Possibly winning, Confirming with further refinement"
                    res <- mSumMaybe $ flip map goal $ \g -> do
                        overAndGoal <- lift $ $r2 band winRegion g
                        underReach <- lift $ solveReach (cPreUnder ops si rs rd hasOutgoings lp) ops rs winRegion overAndGoal
                        lift $ lift $ traceST ""
                        urog <- lift $ $r2 bor underReach overAndGoal
                        lift $ $d deref underReach
                        res <- mSumMaybe $ flip map fair $ \fairr -> do
                            --TODO is this the right cpre?
                            newWin <- lift $ solveFair (cPreOver ops si rs rd hasOutgoings lp) ops rs winRegion urog fairr
                            (res, rd) <- refineConsistency ops ts rd rs hasOutgoings newWin urog fairr
                            case res of
                                True -> do
                                    --lift $ lift $ traceST "Refined consistency relations. Re-solving..."
                                    lift $ mapM ($d deref) [newWin]
                                    return $ Just rd
                                False -> do
                                    --lift $ lift $ traceST "Could not refine consistency relations. Attempting to refine untracked state variables"
                                    res <- lift $ pickUntrackedToPromote ops si rd rs lp hasOutgoings newWin urog fairr
                                    lift $ mapM ($d deref) [newWin]
                                    case res of 
                                        Just vars -> do
                                            newRD <- promoteUntracked ops spec ts rd vars 
                                            return $ Just newRD
                                        Nothing -> lift $ do
                                            return Nothing
                        lift $ mapM ($d deref) [urog, overAndGoal, hasOutgoings]
                        return res
                    case res of 
                        Nothing -> do 
                            lift $ lift $ traceST "Winning"
                            return (True, (si, rs, rd, lp, winRegion))
                        Just rd -> refineLoop' rd winRegion

cex :: RefineInfo s u sp lp -> ResourceT (DDNode s u) (ST s) [[DDNode s u]]
cex RefineInfo{..} = counterExample op si rs rd lp wn

strat :: RefineInfo s u sp lp -> ResourceT (DDNode s u) (ST s) [[DDNode s u]]
strat RefineInfo{..} = strategy op si rs rd lp wn

