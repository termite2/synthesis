{-# LANGUAGE PolymorphicComponents, RecordWildCards, ScopedTypeVariables #-}
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
import Data.Text.Lazy hiding (intercalate, map, take, length, zip, replicate)
import Text.PrettyPrint.Leijen.Text

import Util
import RefineUtil
import BddRecord
import BddUtil
import BddInterp
import Interface
import RefineCommon hiding (doEnVars)

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
    goalAbs    :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) [DDNode s u],
    fairAbs    :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) [DDNode s u],
    initAbs    :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) (DDNode s u),
    contAbs    :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) (DDNode s u),
    updateAbs  :: forall pdb. [(sp, [DDNode s u])] -> VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) ([DDNode s u])
}

-- ===Data structures for keeping track of abstraction state===
data RefineStatic s u = RefineStatic {
    cont :: DDNode s u,
    goal :: [DDNode s u],
    fair :: [DDNode s u],
    init :: DDNode s u
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
    consistentPlusCULUCont  :: DDNode s u
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

doEnVars :: (Ops s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)) -> Ops s u -> DDNode s u -> Lab s u -> ST s (DDNode s u)
doEnVars qFunc ops@Ops{..} strat envars = do
    ref strat
    foldM func strat envars
    where
    func soFar (var, en) = do
        varCube <- nodesToCube var
        e <- qFunc ops varCube soFar
        deref varCube
        res <- bite en soFar e
        deref soFar
        deref e
        return res

doEnCont  = doEnVars bforall
doEnUCont = doEnVars bexists

groupSize = 1000

andLimit2 :: Ops s u -> Int -> DDNode s u -> DDNode s u -> ST s (Maybe (DDNode s u))
andLimit2 Ops{..} limit x y = do
    dsx <- dagSize x
    case dsx > limit of
        True -> return Nothing
        False -> do
            dsy <- dagSize y
            case dsy > limit of 
                True -> return Nothing
                False -> do
                    res <- band x y
                    dsr <- dagSize res
                    case dsr > limit of
                        True -> do
                            deref res
                            return Nothing
                        False -> return $ Just res

groupTrels :: Ops s u -> [(DDNode s u, DDNode s u)] -> ST s [(DDNode s u, DDNode s u)]
groupTrels _ [] = return []
groupTrels ops@Ops{..} (hd:rst) = groupTrels' hd rst
    where
    groupTrels' accum [] = return [accum]
    groupTrels' (accum@(accumCube, accumRel)) (allRels@((hdCube, hdRel):rels)) = do
        res <- andLimit2 ops groupSize accumRel hdRel 
        case res of 
            Nothing -> do
                sz <- dagSize accumRel
                res <- groupTrels ops allRels
                return $ accum : res
            Just res -> do
                mapM deref [accumRel, hdRel]
                cb <- band accumCube hdCube
                mapM deref [accumCube, hdCube]
                groupTrels' (cb, res) rels

partitionedThing :: Ops s u -> [(DDNode s u, DDNode s u)] -> DDNode s u -> ST s (DDNode s u)
partitionedThing Ops{..} pairs win = do
    ref win
    forAccumM win pairs $ \win (cube, rel) -> do
        res <- liftM bnot $ andAbstract cube (bnot win) rel
        deref win
        return res

doHasOutgoings :: Ops s u -> [(DDNode s u, DDNode s u)] -> ST s (DDNode s u)
doHasOutgoings Ops{..} pairs = do
    ref btrue
    forAccumM btrue pairs $ \has (cube, rel) -> do
        r <- bexists cube rel
        a <- band r has
        deref has
        deref r
        return a

--Find the <state, untracked, label> tuples that are guaranteed to lead to the goal for a given transition relation
cpre' :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> DDNode s u -> ST s (DDNode s u)
cpre' ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} target = do
    nextWin  <- mapVars target
    strat    <- partitionedThing ops trans nextWin
    deref nextWin
    return strat
   
--Returns the set of <state, untracked> pairs that are winning 
cpre'' :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cpre'' ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} hasOutgoingsCont labelPreds cc cu target = do
    strat      <- cpre' ops si rd target
    --TODO should they both be doEnCont?
    stratContHas <- strat .& hasOutgoingsCont
    stratCont  <- doEnCont ops stratContHas labelPreds
    deref stratContHas
    stratUCont <- doEnCont ops (bnot strat) labelPreds
    deref strat
    winCont    <- andAbstract _labelCube cc stratCont
    winUCont   <- liftM bnot $ andAbstract _labelCube cu stratUCont
    mapM deref [stratCont, stratUCont]
    win        <- bite cont winCont winUCont
    mapM deref [winCont, winUCont]
    return win

--Returns the set of <state, untracked> pairs that are winning 
cpreOver' :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> ST s (DDNode s u)
cpreOver' ops si rs rd@RefineDynamic{..} hasOutgoingsCont labelPreds = cpre'' ops si rs rd hasOutgoingsCont labelPreds consistentPlusCULCont consistentMinusCULUCont 
    
--Returns the set of <state, untracked> pairs that are winning 
cpreUnder' :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> ST s (DDNode s u)
cpreUnder' ops si rs rd@RefineDynamic{..} hasOutgoingsCont labelPreds = cpre'' ops si rs rd hasOutgoingsCont labelPreds consistentMinusCULCont consistentPlusCULUCont

cPreHelper cpreFunc quantFunc ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} hasOutgoingsCont labelPreds target = do
    su  <- cpreFunc ops si rs rd hasOutgoingsCont labelPreds target
    res <- quantFunc _untrackedCube su
    deref su
    return res

cPreOver :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> ST s (DDNode s u)
cPreOver ops@Ops{..} = cPreHelper cpreOver' bexists ops  

cPreUnder :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> ST s (DDNode s u)
cPreUnder ops@Ops{..} = cPreHelper cpreUnder' bforall ops

winningSU :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> Lab s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
winningSU ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} labelPreds hasOutgoings target = do
    res <- cpreOver' ops si rs rd hasOutgoings labelPreds target
    return res

solveFair :: (DDNode s u -> ST s (DDNode s u)) -> Ops s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
solveFair cpreFunc ops@Ops{..} rs@RefineStatic{..} startPt winning fairr = do
    ref startPt
    fixedPoint ops func startPt
    where
    func target = do
        debugDo 1 $ traceST "solveFair: iteration"
        check "solveFair" ops
        t1 <- target .& fairr
        t2 <- t1 .| winning
        deref t1
        res <- cpreFunc t2
        deref t2
        return res

solveReach :: (DDNode s u -> ST s (DDNode s u)) -> Ops s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
solveReach cpreFunc ops@Ops{..} rs@RefineStatic{..} startPt goall = do
    ref bfalse
    fixedPoint ops func bfalse
    where
    func target = do
        debugDo 1 $ traceST "solveReach: iteration"
        sz <- dagSize target
        traceMsg $ "r(" ++ show sz ++ ")"
        t1 <- target .| goall
        ref bfalse
        res <- forAccumM bfalse fair $ \accum val -> do
            res' <- solveFair cpreFunc ops rs startPt t1 val
            res  <- res' .| accum
            deref res'
            deref accum
            return res
        deref t1
        return res

solveBuchi :: (DDNode s u -> ST s (DDNode s u)) -> Ops s u -> RefineStatic s u -> DDNode s u -> ST s (DDNode s u)
solveBuchi cpreFunc ops@Ops{..} rs@RefineStatic{..} startingPoint = do
    ref startingPoint
    fixedPoint ops func startingPoint
    where
    func reachN = do
        traceMsg "b"
        debugDo 1 $ traceST "solveBuchi: iteration"
        ref btrue
        res <- forAccumM btrue goal $ \accum val -> do
            traceMsg "g"
            t1 <- reachN .& val
            --TODO terminate when t1s are equal
            res' <- solveReach cpreFunc ops rs reachN t1
            deref t1
            res <- res' .& accum
            deref res'
            deref accum
            return res
        return res

check msg ops = return ()
--check msg ops = unsafeIOToST (putStrLn ("checking bdd consistency" ++ msg ++ "\n")) >> debugCheck ops >> checkKeys ops

--Create an initial abstraction and set up the data structures
initialAbstraction :: (Show sp, Show lp, Ord sp, Ord lp) => Ops s u -> Abstractor s u sp lp -> StateT (DB s u sp lp) (ST s) (RefineDynamic s u, RefineStatic s u)
initialAbstraction ops@Ops{..} Abstractor{..} = do
    lift $ check "InitialAbstraction start" ops
    --abstract init
    initExpr <- doInit ops initAbs
    lift $ check "After compiling init" ops
    --abstract the goal
    (goalExprs, newVarsGoals) <- doGoal ops goalAbs
    lift $ check "After compiling goal" ops
    --abstract the fair region
    (fairExprs, newVarsFairs) <- doGoal ops fairAbs
    lift $ check "After compiling fair" ops
    --abstract the controllable condition
    (contExpr, newVarsCont) <- doGoal ops contAbs
    lift $ check "After compiling fair" ops
    --get the abstract update functions for the goal predicates and variables
    let toUpdate = nub $ _allocatedStateVars newVarsGoals ++ _allocatedStateVars newVarsFairs ++ _allocatedStateVars newVarsCont
    lift $ traceST $ "Initial transition relation state vars: \n" ++ (intercalate "\n" $ map (('\t' :) . show . fst) $ toUpdate)
    updateExprs' <- doUpdate ops (updateAbs toUpdate)
    outcomeCube <- gets $ _outcomeCube . _sections
    updateExprs <- lift $ mapM (bexists outcomeCube) updateExprs'
    lift $ mapM deref updateExprs'
    zipWithM (transSynopsys ops) (map fst toUpdate) updateExprs
    cubes <- lift $ mapM (nodesToCube . snd) toUpdate
    groups <- lift $ groupTrels ops $ zip cubes updateExprs
    lift $ traceST $ "Number of transition partitions: " ++ show (length groups)

    --create the consistency constraints
    let consistentPlusCULCont  = btrue
        consistentPlusCULUCont = btrue
    lift $ ref consistentPlusCULCont
    lift $ ref consistentPlusCULUCont
    labelPreds <- gets $ _labelVars . _symbolTable
    consistentMinusCULCont <- lift $ conj ops $ map (bnot . sel3) $ Map.elems labelPreds
    let consistentMinusCULUCont = consistentMinusCULCont
    lift $ ref consistentMinusCULUCont
    --construct the RefineDynamic and RefineStatic
    let rd = RefineDynamic {
            trans  = groups,
            ..
        }
        rs = RefineStatic {
            goal = goalExprs,
            fair = fairExprs,
            init = initExpr,
            cont = contExpr
        }
    return (rd, rs)

refineStrategy = refineLeastPreds

pickUntrackedToPromote :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> RefineStatic s u -> Lab s u -> DDNode s u -> DDNode s u -> DDNode s u -> DDNode s u -> ST s (Maybe [Int])
pickUntrackedToPromote ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} rs@RefineStatic{..} labelPreds hasOutgoings win lastLFP fairr = do
    win''  <- win .& fairr
    win'   <- win'' .| lastLFP
    deref win''
    su     <- winningSU ops si rs rd labelPreds hasOutgoings win'
    deref win'
    toDrop <- (bnot su) .& win
    deref su
    res    <- refineStrategy ops si toDrop
    deref toDrop
    return res

--Promote untracked state variables to full state variables so that we can make progress towards the goal. Does not refine the consistency relations.
promoteUntracked :: (Ord lp, Ord sp, Show sp, Show lp) => Ops s u -> Abstractor s u sp lp -> RefineDynamic s u -> [Int] -> StateT (DB s u sp lp) (ST s) (RefineDynamic s u)
promoteUntracked ops@Ops{..} Abstractor{..} rd@RefineDynamic{..} indices = do
    --look up the predicates to promote
    stateRev             <- gets $ _stateRev . _symbolTable
    let refineVars       =  nub $ map (fromJustNote "promoteUntracked: untracked indices not in stateRev" . flip Map.lookup stateRev) indices
    lift $ traceST $ "* Promoting: \n" ++ (intercalate "\n" $ map (('\t' :) . show) $ refineVars)

    NewVars{..}          <- promoteUntrackedVars ops refineVars
    labelPredsPreUpdate  <- gets $ _labelVars . _symbolTable

    --compute the update functions
    updateExprs'   <- doUpdate ops (updateAbs _allocatedStateVars)
    outcomeCube <- gets $ _outcomeCube . _sections
    updateExprs  <- lift $ mapM (bexists outcomeCube) updateExprs'
    lift $ mapM deref updateExprs'
    zipWithM (transSynopsys ops) (map fst _allocatedStateVars) updateExprs
    cubes <- lift $ mapM (nodesToCube . snd) _allocatedStateVars
    groups <- lift $ groupTrels ops $ zip cubes updateExprs
    lift $ traceST $ "Number of transition partitions: " ++ show (length groups)

    --TODO why is this commented out?
    {-
    labelPreds           <- gets $ _labelVars . _symbolTable
    consistentMinusCUL'' <- lift $ conj ops $ map (bnot . fst . snd) $ Map.elems $ labelPreds Map.\\ labelPredsPreUpdate
    consistentMinusCUL'  <- lift $ andDeref ops consistentMinusCUL consistentMinusCUL''
    -}

    return rd {
        --TODO does this order matter
        trans  = groups ++ trans
    }

refineConsistency :: (Ord sp, Ord lp, Show sp, Show lp) => Ops s u -> TheorySolver s u sp lp -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> DDNode s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) (Maybe (RefineDynamic s u))
refineConsistency ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} hasOutgoings win winning fairr = do
    r1 <- refineConsistencyCont ops ts rd rs hasOutgoings win winning fairr
    case r1 of
        Just res -> do
            return $ Just res
        Nothing  -> do
            res <- refineConsistencyUCont ops ts rd rs win winning fairr
            return res

refineConsistencyCont :: (Ord sp, Ord lp, Show sp, Show lp) => Ops s u -> TheorySolver s u sp lp -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> DDNode s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) (Maybe (RefineDynamic s u))
refineConsistencyCont ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} hasOutgoings win winning fairr = do
    lift $ check "refineConsistencyCont" ops
    syi@SymbolInfo{..} <- gets _symbolTable 
    si@SectionInfo{..} <- gets _sections
    win''              <- lift $ win .& fairr
    win'               <- lift $ win'' .| winning
    lift $ deref win''
    winNoConstraint'   <- lift $ cpre' ops si rd win'
    stratContHas       <- lift $ winNoConstraint' .& hasOutgoings
    lift $ deref winNoConstraint'
    let lp             =  map (sel1 &&& sel3) $ Map.elems _labelVars
    winNoConstraint    <- lift $ doEnCont ops stratContHas lp
    lift $ deref stratContHas
    winNoConstraint2   <- lift $ cont .& winNoConstraint
    lift $ mapM deref [win', winNoConstraint]
    res <- doConsistency ops ts consistentPlusCULCont consistentMinusCULCont winNoConstraint2
    lift $ check "refineConsistencyCont End" ops
    case res of 
        Nothing -> return Nothing
        Just (consistentPlusCULCont', consistentMinusCULCont') -> 
            return $ Just $ rd {consistentPlusCULCont = consistentPlusCULCont', consistentMinusCULCont = consistentMinusCULCont'}

refineConsistencyUCont :: (Ord sp, Ord lp, Show sp, Show lp) => Ops s u -> TheorySolver s u sp lp -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) (Maybe (RefineDynamic s u))
refineConsistencyUCont ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} win winning fairr = do
    lift $ check "refineConsistencyUCont" ops
    syi@SymbolInfo{..} <- gets _symbolTable 
    si@SectionInfo{..} <- gets _sections
    win''              <- lift $ win .& fairr
    win'               <- lift $ win'' .| winning
    lift $ deref win''
    winNoConstraint'   <- lift $ liftM bnot $ cpre' ops si rd win'
    let lp             =  map (sel1 &&& sel3) $ Map.elems _labelVars
    winNoConstraint    <- lift $ doEnCont ops winNoConstraint' lp
    lift $ deref winNoConstraint'
    winNoConstraint2   <- lift $ bnot cont .& winNoConstraint
    lift $ mapM deref [win', winNoConstraint]
    res <- doConsistency ops ts consistentPlusCULUCont consistentMinusCULUCont winNoConstraint2
    lift $ check "refineConsistencyUCont End" ops
    case res of 
        Nothing -> return Nothing
        Just (consistentPlusCULUCont', consistentMinusCULUCont') -> 
            return $ Just $ rd {consistentPlusCULUCont = consistentPlusCULUCont', consistentMinusCULUCont = consistentMinusCULUCont'}

doConsistency :: (Ord sp, Ord lp, Show sp, Show lp) => Ops s u -> TheorySolver s u sp lp -> DDNode s u -> DDNode s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) (Maybe (DDNode s u, DDNode s u))
doConsistency ops@Ops{..} ts@TheorySolver{..} cPlus cMinus winNoConstraint = do
    syi@SymbolInfo{..} <- gets _symbolTable 
    si@SectionInfo{..} <- gets _sections
    winActOver         <- lift $ winNoConstraint .& cPlus
    winActUnder        <- lift $ andAbstract _labelCube winNoConstraint cMinus
    toCheckConsistency <- lift $ winActOver .& bnot winActUnder
    lift $ mapM deref [winActOver, winActUnder]
    --Alive : toCheckConsistency
    case toCheckConsistency==bfalse of 
        True  -> do
            --no refinement of consistency relations will shrink the winning region
            lift $ debugDo 2 $ traceST "no consistency refinement possible"
            lift $ mapM deref [toCheckConsistency, winNoConstraint]
            return Nothing
        False -> do
            --There may be a refinement
            --extract a <s, u, l> pair that will make progress if one exists
            c <- lift $ presentInLargePrime ops toCheckConsistency
            lift $ deref toCheckConsistency

            let (cStatePreds, cLabelPreds) = partitionStateLabelPreds si syi c
            --Alive : nothing
            let groupedState = groupForUnsatCore (sel2 . fromJustNote "doConsistency" . flip Map.lookup _stateVars) cStatePreds
                groupedLabel = groupForUnsatCore (sel2 . fromJustNote "doConsistency" . flip Map.lookup _labelVars) cLabelPreds
            let fmt (name, enc) = show name ++ ":" ++ map (alt 'T' 'F') enc
            lift $ traceMsg $ "* Refining Consistency: " ++ intercalate ", " (map fmt groupedState) ++ " -- " ++ intercalate ", " (map fmt groupedLabel) ++ " ..."
            case unsatCoreStateLabel groupedState groupedLabel of
                Just (statePairs, labelPairs) -> do
                    --statePairs, labelPairs is inconsistent so subtract this from consistentPlusCUL
                    lift $ traceST "UNSAT"
                    inconsistent       <- lift $ stateLabelInconsistent ops syi statePairs labelPairs
                    consistentPlusCUL' <- lift $ andDeref ops cPlus (bnot inconsistent)
                    lift $ check "refineConsistency4" ops
                    doConsistency ops ts consistentPlusCUL' cMinus winNoConstraint
                Nothing -> do
                    --the (s, u, l) tuple is consistent so add this to consistentMinusCUL
                    lift $ deref winNoConstraint
                    lift $ traceST "SAT"
                    eQuantExpr <- doUpdate ops (eQuant groupedLabel)

                    consistentCube'     <- lift $ stateLabelConsistent ops syi groupedLabel 
                    consistentCube      <- lift $ andDeref ops consistentCube' eQuantExpr
                    consistentMinusCUL' <- lift $ orDeref ops cMinus consistentCube

                    return $ Just (cPlus, consistentMinusCUL')

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

strategy :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> Lab s u -> DDNode s u -> ST s [[DDNode s u]]
strategy ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} labelPreds win = do
    hasOutgoings <- doHasOutgoings ops trans
    --For each goal
    res <- forM goal $ \goal -> do 
        winAndGoal <- goal .& win
        ref bfalse
        --Reachabiliy least fixedpoint
        res <- fixedPoint2 ops bfalse (repeat bfalse) $ \soFar strats -> do 
            soFarOrWinAndGoal <- soFar .| winAndGoal
            ref bfalse
            --For each fair
            (res, strats') <- forAccumLM bfalse fair $ \accum fair -> do
                --Fairness greatest fixedpoint
                --TODO optimise: dont use btrue below
                winFair <- solveFair (cPreUnder ops si rs rd hasOutgoings labelPreds)  ops rs btrue soFarOrWinAndGoal fair
                thing <- winFair .& fair
                deref winFair
                thing2 <- thing .| soFarOrWinAndGoal
                deref thing
                (win', strats) <- cpre hasOutgoings thing2
                win <- win' .| accum 
                deref win'
                when (winFair /= win') (error "wrs not equal")
                return (win, strats)
            deref soFarOrWinAndGoal
            strats <- zipWithM (combineStrats soFar) strats strats'
            return (res, strats)
        deref winAndGoal
        return res
    deref hasOutgoings
    let (wins, strats) = unzip res
    win' <- conj ops wins
    mapM deref wins
    deref win'
    when (win' /= win) (error "Winning regions are not equal in strategy generation")
    return strats
    where
    combineStrats prevWin oldC newC = do
        c <- newC .& bnot prevWin
        deref newC
        c' <- c .| oldC
        deref oldC
        return c'
    cpre hasOutgoings target = do
        strat      <- cpre' ops si rd target
        stratContHas <- strat .& hasOutgoings
        stratCont  <- doEnCont ops stratContHas labelPreds
        deref stratContHas
        stratUCont <- doEnCont ops (bnot strat) labelPreds
        deref strat
        winCont    <- andAbstract _labelCube consistentMinusCULCont stratCont
        winUCont   <- liftM bnot $ andAbstract _labelCube consistentPlusCULUCont stratUCont
        su         <- bite cont winCont winUCont
        win        <- bforall _untrackedCube su
        deref su
        mapM deref [winCont, stratUCont, winUCont]
        return (win, stratCont)

counterExample :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> Lab s u -> DDNode s u -> ST s [[DDNode s u]]
counterExample ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} labelPreds win = do
    hasOutgoings <- doHasOutgoings ops trans 
    sequence $ replicate (length goal * length fair) (ref bfalse)
    ref bfalse
    (win', strat) <- fixedPoint2 ops bfalse (zip goal $ repeat $ zip fair $ repeat bfalse) $ \win strat -> do
        ref bfalse
        res <- forAccumLM bfalse strat $ \tot (goal, strats) -> do
            tgt               <- bnot goal .| win
            --TODO optimise: dont use btrue below
            winBuchi          <- liftM bnot $ solveReach (cPreOver ops si rs rd hasOutgoings labelPreds) ops rs btrue (bnot tgt)
            (winStrat, strat) <- stratReach si rs rd hasOutgoings fair win strats winBuchi tgt
            when (winStrat /= winBuchi) (traceST "Warning: counterexample winning regions are not equal")
            deref winStrat
            deref tgt
            tot'              <- tot .| winBuchi
            mapM deref [tot, winBuchi]
            return (tot', (goal, strat))
        return res
    when (win /= bnot win') (error "the counterexample winning region is not the complement of the game winning region")
    traceST $ bddSynopsis ops win
    deref hasOutgoings
    return $ map (map snd . snd) strat

    where

    fixedPoint' ops = flip $ fixedPoint ops 

    target fair goal winN reach = do
        a   <- reach .| fair
        b   <- a .& winN
        deref a
        c   <- b .& goal
        deref b
        return c

    --TODO check winning regions coincide
    stratReach si rs rd hasOutgoings fairs startingWin stratSoFar winN goal = do
        ref startingWin
        fixedPoint2 ops startingWin stratSoFar $ \reach strat -> do
            ref btrue
            res <- forAccumLM btrue strat $ \winAccum (fair, strat) -> do
                tgt            <- target fair goal winN reach
                (win', strat') <- strategy si rs rd hasOutgoings tgt
                deref tgt
                strat''        <- strat' .& bnot reach
                deref strat'
                --TODO use ite for strat
                strat'''       <- strat'' .| strat
                deref strat''
                deref strat
                win            <- bforall _untrackedCube win'
                deref win'
                winAccum'      <- winAccum .& win
                mapM deref [win, winAccum]
                return (winAccum', (fair, strat'''))
            return res

    strategy SectionInfo{..} RefineStatic{..} RefineDynamic{..} hasOutgoings target = do
        strt        <- cpre' ops si rd (bnot target)
        stratContHas <- strt .& hasOutgoings
        stratCont'  <- doEnCont ops stratContHas labelPreds
        deref stratContHas
        winCont     <- liftM bnot $ andAbstract _labelCube consistentPlusCULCont stratCont'
        deref stratCont'
        stratUCont' <- doEnCont ops (bnot strt) labelPreds
        deref strt
        stratUCont  <- band consistentMinusCULUCont stratUCont'
        deref stratUCont'
        winUCont    <- bexists _labelCube stratUCont
        win         <- bite cont winCont winUCont
        mapM deref [winCont, winUCont]
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

--The abstraction-refinement loop
absRefineLoop :: forall s u o sp lp. (Ord sp, Ord lp, Show sp, Show lp) => STDdManager s u -> Abstractor s u sp lp -> TheorySolver s u sp lp -> o -> ST s (Bool, RefineInfo s u sp lp)
absRefineLoop m spec ts abstractorState = let ops@Ops{..} = constructOps m in do
    idb <- initialDB ops
    ((winning, (si, rs, rd, lp, wn)), db) <- flip runStateT idb $ do
        (rd, rs) <- initialAbstraction ops spec
        lift $ debugDo 1 $ traceST "Refinement state after initial abstraction: " 
        lift $ debugDo 1 $ traceST $ "Goal is: " ++ (intercalate ", " $ map (bddSynopsis ops) $ goal rs)
        lift $ debugDo 1 $ traceST $ "Fair is: " ++ (intercalate ", " $ map (bddSynopsis ops) $ fair rs)
        lift $ debugDo 1 $ traceST $ "Init is: " ++ (bddSynopsis ops $ TermiteGame.init rs)
        lift $ ref bfalse
        refineLoop ops rs rd btrue
    return $ (winning, RefineInfo{op=ops, ..})
    where
    refineLoop ops@Ops{..} rs@RefineStatic{..} = refineLoop'
        where 
        refineLoop' rd@RefineDynamic{..} lastWin = do
            si@SectionInfo{..} <- gets _sections
            lift $ setVarMap _trackedNodes _nextNodes
            labelPreds <- gets $ _labelVars . _symbolTable
            let lp = map (sel1 &&& sel3) $ Map.elems labelPreds
            hasOutgoings <- lift $ doHasOutgoings ops trans
            winRegion <- lift $ solveBuchi (cPreOver ops si rs rd hasOutgoings lp) ops rs lastWin
            lift $ traceST ""
            lift $ deref lastWin
            winning <- lift $ bnot winRegion `leq` bnot init
            --Alive: winRegion, rd, rs, hasOutgoings
            case winning of
                False -> lift $ do
                    traceST "Losing"
                    mapM deref [hasOutgoings]
                    return (False, (si, rs, rd, lp, winRegion))
                True -> do
                    lift $ debugDo 1 $ traceST "Possibly winning, Confirming with further refinement"
                    res <- mSumMaybe $ flip map goal $ \g -> do
                        overAndGoal <- lift $ winRegion .& g
                        underReach <- lift $ solveReach (cPreUnder ops si rs rd hasOutgoings lp) ops rs winRegion overAndGoal
                        lift $ traceST ""
                        urog <- lift $ underReach .| overAndGoal
                        lift $ deref underReach
                        res <- mSumMaybe $ flip map fair $ \fairr -> do
                            newWin <- lift $ solveFair (cPreOver ops si rs rd hasOutgoings lp) ops rs winRegion urog fairr
                            res <- refineConsistency ops ts rd rs hasOutgoings newWin urog fairr
                            case res of
                                Just newRD -> do
                                    lift $ debugDo 1 $ traceST "Refined consistency relations. Re-solving..."
                                    lift $ mapM deref [newWin]
                                    return $ Just newRD
                                Nothing -> do
                                    lift $ debugDo 1 $ traceST "Could not refine consistency relations. Attempting to refine untracked state variables"
                                    res <- lift $ pickUntrackedToPromote ops si rd rs lp hasOutgoings newWin urog fairr
                                    lift $ mapM deref [newWin]
                                    case res of 
                                        Just vars -> do
                                            newRD <- promoteUntracked ops spec rd vars 
                                            return $ Just newRD
                                        Nothing -> lift $ do
                                            return Nothing
                        lift $ mapM deref [urog, overAndGoal, hasOutgoings]
                        return res
                    case res of 
                        Nothing -> return (True, (si, rs, rd, lp, winRegion))
                        Just rd -> refineLoop' rd winRegion

cex :: RefineInfo s u sp lp -> ST s [[DDNode s u]]
cex RefineInfo{..} = counterExample op si rs rd lp wn

strat :: RefineInfo s u sp lp -> ST s [[DDNode s u]]
strat RefineInfo{..} = strategy op si rs rd lp wn

