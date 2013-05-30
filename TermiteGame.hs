{-# LANGUAGE PolymorphicComponents, RecordWildCards, ScopedTypeVariables #-}
module TermiteGame (
    Abstractor(..),
    absRefineLoop,
    RefineStatic(..),
    RefineDynamic(..)
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

import Safe

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

forAccumM i l f = foldM f i l

--Input to the refinement algorithm. Represents the spec.
data Abstractor s u sp lp = Abstractor {
    goalAbs    :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) [DDNode s u],
    fairAbs    :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) [DDNode s u],
    initAbs    :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) (DDNode s u),
    contAbs    :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) (DDNode s u),
    updateAbs  :: forall pdb. [(sp, [DDNode s u])] -> VarOps pdb (BAVar sp lp) s u -> StateT pdb (ST s) (DDNode s u)
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
    trans                   :: DDNode s u,
    consistentMinusCULCont  :: DDNode s u,
    consistentPlusCULCont   :: DDNode s u,
    consistentMinusCULUCont :: DDNode s u,
    consistentPlusCULUCont  :: DDNode s u
}

derefDynamic :: Ops s u -> RefineDynamic s u -> ST s ()
derefDynamic Ops{..} RefineDynamic{..} = do
    deref trans
    deref consistentMinusCULCont
    deref consistentPlusCULCont
    deref consistentMinusCULUCont
    deref consistentPlusCULUCont

dumpSizes :: Ops s u -> RefineDynamic s u -> ST s ()
dumpSizes Ops{..} RefineDynamic{..} = do
    let func x = do
        ds <- dagSize x
        traceST $ show ds
    func trans
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
        deref e
        return res

doEnCont  = doEnVars bforall
doEnUCont = doEnVars bexists

--Find the <state, untracked, label> tuples that are guaranteed to lead to the goal for a given transition relation
cpre' :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cpre' ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} hasOutgoings target = do
    nextWin  <- mapVars target
    strat    <- liftM bnot $ andAbstract _nextCube trans (bnot nextWin)
    deref nextWin
    stratAvl <- hasOutgoings .& strat
    deref strat
    return stratAvl
   
--Returns the set of <state, untracked> pairs that are winning 
cpre'' :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
cpre'' ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} hasOutgoingsCont labelPreds cc cu target = do
    strat      <- cpre' ops si rd hasOutgoingsCont target
    --TODO should they both be doEnCont?
    stratCont  <- doEnCont ops strat labelPreds
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

winningSU :: Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> Lab s u -> DDNode s u -> ST s (DDNode s u)
winningSU ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} labelPreds target = do
    hasOutgoings <- bexists _nextCube trans
    res <- cpreOver' ops si rs rd hasOutgoings labelPreds target
    deref hasOutgoings
    return res

solveFair :: (DDNode s u -> ST s (DDNode s u)) -> Ops s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
solveFair cpreFunc ops@Ops{..} rs@RefineStatic{..} winning fairr = do
    ref btrue
    fixedPoint ops func btrue
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

solveReach :: (DDNode s u -> ST s (DDNode s u)) -> Ops s u -> RefineStatic s u -> DDNode s u -> ST s (DDNode s u)
solveReach cpreFunc ops@Ops{..} rs@RefineStatic{..} goall = do
    ref bfalse
    fixedPoint ops func bfalse
    where
    func target = do
        debugDo 1 $ traceST "solveReach: iteration"
        t1 <- target .| goall
        ref bfalse
        res <- forAccumM bfalse fair $ \accum val -> do
            res' <- solveFair cpreFunc ops rs t1 val
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
        debugDo 1 $ traceST "solveBuchi: iteration"
        ref btrue
        res <- forAccumM btrue goal $ \accum val -> do
            t1 <- reachN .& val
            res' <- solveReach cpreFunc ops rs t1
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
    updateExprConj' <- doUpdate ops (updateAbs (nub $ _allocatedStateVars newVarsGoals ++ _allocatedStateVars newVarsFairs ++ _allocatedStateVars newVarsCont))
    outcomeCube <- gets $ _outcomeCube . _sections
    updateExprConj <- lift $ bexists outcomeCube updateExprConj'
    lift $ deref updateExprConj'

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
            trans  = updateExprConj,
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

pickUntrackedToPromote :: Ops s u -> SectionInfo s u -> RefineDynamic s u -> RefineStatic s u -> Lab s u -> DDNode s u -> DDNode s u -> DDNode s u -> ST s (Maybe [Int])
pickUntrackedToPromote ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} rs@RefineStatic{..} labelPreds win lastLFP fairr = do
    win''  <- win .& fairr
    win'   <- win'' .| lastLFP
    deref win''
    su     <- winningSU ops si rs rd labelPreds win'
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
    lift $ traceST $ "Promoting: " ++ show refineVars

    NewVars{..}          <- promoteUntrackedVars ops refineVars
    labelPredsPreUpdate  <- gets $ _labelVars . _symbolTable

    --compute the update functions
    updateExprConj'   <- doUpdate ops (updateAbs _allocatedStateVars)
    outcomeCube <- gets $ _outcomeCube . _sections
    updateExprConj''  <- lift $ bexists outcomeCube updateExprConj'
    lift $ deref updateExprConj'

    --update the transition relation
    updateExprConj  <- lift $ andDeref ops trans updateExprConj''

    --TODO why is this commented out?
    {-
    labelPreds           <- gets $ _labelVars . _symbolTable
    consistentMinusCUL'' <- lift $ conj ops $ map (bnot . fst . snd) $ Map.elems $ labelPreds Map.\\ labelPredsPreUpdate
    consistentMinusCUL'  <- lift $ andDeref ops consistentMinusCUL consistentMinusCUL''
    -}

    return rd {
        trans  = updateExprConj
    }

refineConsistency :: (Ord sp, Ord lp, Show sp, Show lp) => Ops s u -> TheorySolver s u sp lp -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) (Maybe (RefineDynamic s u))
refineConsistency ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} win winning fairr = do
    r1 <- refineConsistencyCont ops ts rd rs win winning fairr
    case r1 of
        Just res -> do
            lift $ traceST "refined controllable consistency"
            return $ Just res
        Nothing  -> do
            res <- refineConsistencyUCont ops ts rd rs win winning fairr
            case res of 
                Just _ -> lift $ traceST "refined uncontrollable consistency"
                Nothing -> lift $ traceST "No consistency refinement possible"
            return res

refineConsistencyCont :: (Ord sp, Ord lp, Show sp, Show lp) => Ops s u -> TheorySolver s u sp lp -> RefineDynamic s u -> RefineStatic s u -> DDNode s u -> DDNode s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) (Maybe (RefineDynamic s u))
refineConsistencyCont ops@Ops{..} ts@TheorySolver{..} rd@RefineDynamic{..} rs@RefineStatic{..} win winning fairr = do
    lift $ check "refineConsistencyCont" ops
    syi@SymbolInfo{..} <- gets _symbolTable 
    si@SectionInfo{..} <- gets _sections
    win''              <- lift $ win .& fairr
    win'               <- lift $ win'' .| winning
    lift $ deref win''
    hasOutgoings       <- lift $ bexists _nextCube trans
    winNoConstraint'   <- lift $ cpre' ops si rd hasOutgoings win'
    let lp             =  map (sel1 &&& sel3) $ Map.elems _labelVars
    winNoConstraint    <- lift $ doEnCont ops winNoConstraint' lp
    lift $ deref winNoConstraint'
    winNoConstraint2   <- lift $ cont .& winNoConstraint
    lift $ mapM deref [win', hasOutgoings, winNoConstraint]
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
    winNoConstraint'   <- lift $ liftM bnot $ cpre' ops si rd btrue win'
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
            let groupedState = groupForUnsatCore cStatePreds
                groupedLabel = groupForUnsatCore cLabelPreds
            lift $ traceST $ "state preds for solver: " ++ show groupedState
            lift $ traceST $ "label preds for solver: " ++ show groupedLabel
            case unsatCoreStateLabel groupedState groupedLabel of
                Just (statePairs, labelPairs) -> do
                    --statePairs, labelPairs is inconsistent so subtract this from consistentPlusCUL
                    lift $ traceST "refining consistentPlus"
                    inconsistent       <- lift $ stateLabelInconsistent ops syi statePairs labelPairs
                    consistentPlusCUL' <- lift $ andDeref ops cPlus (bnot inconsistent)
                    lift $ check "refineConsistency4" ops
                    doConsistency ops ts consistentPlusCUL' cMinus winNoConstraint
                Nothing -> do
                    --the (s, u, l) tuple is consistent so add this to consistentMinusCUL
                    lift $ deref winNoConstraint
                    lift $ traceST "predicates are consistent. refining consistentMinus..."
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

--The abstraction-refinement loop
absRefineLoop :: forall s u o sp lp. (Ord sp, Ord lp, Show sp, Show lp) => STDdManager s u -> Abstractor s u sp lp -> TheorySolver s u sp lp -> o -> ST s Bool
absRefineLoop m spec ts abstractorState = let ops@Ops{..} = constructOps m in do
    idb <- initialDB ops
    flip evalStateT idb $ do
        (rd, rs) <- initialAbstraction ops spec
        lift $ debugDo 1 $ traceST "Refinement state after initial abstraction: " 
        lift $ debugDo 1 $ traceST $ "Goal is: " ++ (intercalate ", " $ map (bddSynopsis ops) $ goal rs)
        lift $ debugDo 1 $ traceST $ "Fair is: " ++ (intercalate ", " $ map (bddSynopsis ops) $ fair rs)
        lift $ debugDo 1 $ traceST $ "Init is: " ++ (bddSynopsis ops $ TermiteGame.init rs)
        lift $ ref bfalse
        refineLoop ops rs rd btrue
        where
            refineLoop :: Ops s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) Bool
            refineLoop ops@Ops{..} rs@RefineStatic{..} = refineLoop'
                where 
                refineLoop' :: RefineDynamic s u -> DDNode s u -> StateT (DB s u sp lp) (ST s) Bool
                refineLoop' rd@RefineDynamic{..} lastWin = do
                    si@SectionInfo{..} <- gets _sections
                    lift $ setVarMap _trackedNodes _nextNodes
                    labelPreds <- gets $ _labelVars . _symbolTable
                    let lp = map (sel1 &&& sel3) $ Map.elems labelPreds
                    hasOutgoings <- lift $ bexists _nextCube trans
                    winRegion <- lift $ solveBuchi (cPreOver ops si rs rd hasOutgoings lp) ops rs lastWin
                    lift $ deref lastWin
                    winning <- lift $ bnot winRegion `leq` bnot init
                    --Alive: winRegion, rd, rs, hasOutgoings
                    case winning of
                        False -> lift $ do
                            traceST "Losing"
                            mapM deref [winRegion, hasOutgoings]
                            return False
                        True -> do
                            lift $ traceST "Possibly winning, Confirming with further refinement"
                            res <- mSumMaybe $ flip map goal $ \g -> do
                                overAndGoal <- lift $ winRegion .& g
                                underReach <- lift $ solveReach (cPreUnder ops si rs rd hasOutgoings lp) ops rs overAndGoal
                                urog <- lift $ underReach .| overAndGoal
                                lift $ deref underReach
                                res <- mSumMaybe $ flip map fair $ \fairr -> do
                                    newWin <- lift $ solveFair (cPreOver ops si rs rd hasOutgoings lp) ops rs urog fairr
                                    res <- refineConsistency ops ts rd rs newWin urog fairr
                                    case res of
                                        Just newRD -> do
                                            lift $ traceST "Refined consistency relations. Re-solving..."
                                            lift $ mapM deref [newWin]
                                            return $ Just newRD
                                        Nothing -> do
                                            lift $ traceST "Could not refine consistency relations. Attempting to refine untracked state variables"
                                            res <- lift $ pickUntrackedToPromote ops si rd rs lp newWin urog fairr
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
                                Nothing -> return True
                                Just rd -> refineLoop' rd winRegion
