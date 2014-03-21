{-# LANGUAGE PolymorphicComponents, RecordWildCards, ScopedTypeVariables, TemplateHaskell, FlexibleContexts, NoMonomorphismRestriction #-}
module TermiteGame (
    Abstractor(..),
    absRefineLoop,
    RefineStatic(..),
    RefineDynamic(..),
    RefineInfo(..),
    cex,
    cexLiberalEnv,
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
import Control.Monad.Trans.Cont
import Data.Function

import Safe
import qualified Data.Text.Lazy as T
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
import MTR

import Resource

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
        let doc = text (T.pack $ show name) <$$> indent 4 (text (T.pack $ "size: " ++ show sz) <$$> (list $ map (text . T.pack . show) stateSup ++ map (text . T.pack . show) labelSup))
        traceST $ show $ renderPretty 0.8 100 doc

--Input to the refinement algorithm. Represents the spec.
data Abstractor s u sp lp st = Abstractor {
    initialState            :: st,
    goalAbs                 :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT st (StateT pdb (ST s)) [DDNode s u],
    fairAbs                 :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT st (StateT pdb (ST s)) [DDNode s u],
    initAbs                 :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT st (StateT pdb (ST s)) (DDNode s u),
    contAbs                 :: forall pdb. VarOps pdb (BAVar sp lp) s u -> StateT st (StateT pdb (ST s)) (DDNode s u),
    initialVars             :: [(sp, Int, Maybe String)],
    --Return type is: (variable updates, initial inconsistency relation, next state inconsistency relation that will not be refined)
    updateAbs               :: forall pdb. [(sp, [DDNode s u])] -> VarOps pdb (BAVar sp lp) s u -> StateT st (StateT pdb (ST s)) ([DDNode s u], DDNode s u)
}

-- ===Data structures for keeping track of abstraction state===
data RefineStatic s u = RefineStatic {
    cont  :: DDNode s u,
    goal  :: [DDNode s u],
    fair  :: [DDNode s u],
    init  :: DDNode s u
}

derefStatic :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> RefineStatic s u -> t (ST s) ()
derefStatic Ops{..} RefineStatic{..} = do
    $d deref cont
    mapM ($d deref) goal
    mapM ($d deref) fair
    $d deref init

data RefineDynamic s u = RefineDynamic {
    --relations
    --                         cube, rel
    trans                   :: [(DDNode s u, DDNode s u)],
    consistentMinusCULCont  :: DDNode s u,
    consistentPlusCULCont   :: DDNode s u,
    consistentMinusCULUCont :: DDNode s u,
    consistentPlusCULUCont  :: DDNode s u,
    inconsistentInit        :: DDNode s u,
    consistentNoRefine      :: DDNode s u,
    numConsRef              :: Int,
    numStateRef             :: Int
}

derefDynamic :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> RefineDynamic s u -> t (ST s) ()
derefDynamic Ops{..} RefineDynamic{..} = do
    mapM ($d deref . fst) trans
    mapM ($d deref . snd) trans
    $d deref consistentMinusCULCont
    $d deref consistentPlusCULCont
    $d deref consistentMinusCULUCont
    $d deref consistentPlusCULUCont
    $d deref inconsistentInit
    $d deref consistentNoRefine

type Lab s u = [([DDNode s u], DDNode s u)]

doEnVars :: (MonadResource (DDNode s u) (ST s) t) => 
            (Ops s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)) -> 
            Ops s u -> 
            DDNode s u -> 
            Lab s u -> 
            t (ST s) (DDNode s u)
doEnVars qFunc ops@Ops{..} strat envars = do
    $rp ref strat
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

groupSize = 1000

andLimit2 :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> Int -> DDNode s u -> DDNode s u -> t (ST s) (Maybe (DDNode s u))
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

groupTrels :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> [(DDNode s u, DDNode s u)] -> t (ST s) [(DDNode s u, DDNode s u)]
groupTrels ops@Ops{..} x = do
    groupTrels'' x
    where
    groupTrels'' []       = return []
    groupTrels'' (hd:rst) = groupTrels' ops hd rst

groupTrels' :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> (DDNode s u, DDNode s u) -> [(DDNode s u, DDNode s u)] -> t (ST s) [(DDNode s u, DDNode s u)]
groupTrels' _ accum [] = return [accum]
groupTrels' ops@Ops{..} accum@(accumCube, accumRel) allRels@((hdCube, hdRel):rels) = do
    res <- andLimit2 ops groupSize accumRel hdRel 
    case res of 
        Nothing -> do
            sz <- lift $ dagSize accumRel
            res <- groupTrels ops allRels
            return $ accum : res
        Just res -> do
            mapM ($d deref) [accumRel, hdRel]
            cb <- $r2 band accumCube hdCube
            mapM ($d deref) [accumCube, hdCube]
            groupTrels' ops (cb, res) rels

partitionedThing :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> [(DDNode s u, DDNode s u)] -> DDNode s u -> t (ST s) (DDNode s u)
partitionedThing Ops{..} pairs win = do
    $rp ref win
    forAccumM win pairs $ \win (cube, rel) -> do
        res <- liftM bnot $ $r2 (andAbstract cube) (bnot win) rel
        $d deref win
        return res

doHasOutgoings :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> [(DDNode s u, DDNode s u)] -> t (ST s) (DDNode s u)
doHasOutgoings Ops{..} pairs = do
    $rp ref btrue
    forAccumM btrue pairs $ \has (cube, rel) -> do
        rr <- $r1 (bexists cube) rel
        a <- $r2 band rr has
        $d deref has
        $d deref rr
        return a

--Find the <state, untracked, label> tuples that are guaranteed to lead to the goal for a given transition relation
cpreCont' :: (MonadResource (DDNode s u) (ST s) t) => 
             Ops s u -> 
             SectionInfo s u -> 
             RefineDynamic s u -> 
             Lab s u -> 
             DDNode s u -> 
             DDNode s u -> 
             DDNode s u -> 
             t (ST s) (DDNode s u)
cpreCont' ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} labelPreds cont hasOutgoings target = do
    nextWin' <- $r1 mapVars target
    nextWin  <- $r2 bor nextWin' (bnot cont)
    $d deref nextWin'
    strat'   <- partitionedThing ops trans nextWin
    $d deref nextWin
    hasOutgoingsC <- $r2 band hasOutgoings cont
    strat    <- $r2 band hasOutgoingsC strat'
    $d deref hasOutgoingsC
    $d deref strat'
    stratEn <- doEnCont ops strat labelPreds
    $d deref strat
    return stratEn

cpreUCont' :: (MonadResource (DDNode s u) (ST s) t) => 
              Ops s u -> 
              SectionInfo s u -> 
              RefineDynamic s u -> 
              Lab s u -> 
              DDNode s u -> 
              DDNode s u -> 
              t (ST s) (DDNode s u)
cpreUCont' ops@Ops{..} si@SectionInfo{..} rd@RefineDynamic{..} labelPreds cont target = do
    nextWin' <- $r1 mapVars target
    nextWin  <- $r2 bor nextWin' cont
    $d deref nextWin'
    strat    <- partitionedThing ops trans nextWin
    $d deref nextWin
    stratEn  <- doEnCont ops (bnot strat) labelPreds
    $d deref strat
    return stratEn
   
--Returns the set of <state, untracked> pairs that are winning 
cpre'' :: (MonadResource (DDNode s u) (ST s) t) => 
          Ops s u -> 
          SectionInfo s u -> 
          RefineStatic s u -> 
          RefineDynamic s u -> 
          DDNode s u -> 
          Lab s u -> 
          DDNode s u -> 
          DDNode s u -> 
          DDNode s u -> 
          t (ST s) (DDNode s u)
cpre'' ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} hasOutgoingsCont labelPreds cc cu target = do
    stratCont    <- cpreCont' ops si rd labelPreds cont hasOutgoingsCont target
    winCont      <- $r2 (andAbstract _labelCube) cc stratCont
    $d deref stratCont

    stratUCont   <- cpreUCont' ops si rd labelPreds cont target
    winUCont     <- liftM bnot $ $r2 (andAbstract _labelCube) cu stratUCont
    $d deref stratUCont

    win          <- $r2 band winCont winUCont
    mapM ($d deref) [winCont, winUCont]
    return win

--Returns the set of <state, untracked> pairs that are winning 
cpreOver' :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> t (ST s) (DDNode s u)
cpreOver' ops si rs rd@RefineDynamic{..} hasOutgoingsCont labelPreds = cpre'' ops si rs rd hasOutgoingsCont labelPreds consistentPlusCULCont consistentMinusCULUCont 
    
--Returns the set of <state, untracked> pairs that are winning 
cpreUnder' :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> t (ST s) (DDNode s u)
cpreUnder' ops si rs rd@RefineDynamic{..} hasOutgoingsCont labelPreds = cpre'' ops si rs rd hasOutgoingsCont labelPreds consistentMinusCULCont consistentPlusCULUCont

faqf, eqf :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> DDNode s u -> DDNode s u -> DDNode s u -> t (ST s) (DDNode s u)
faqf Ops{..} cube constraint x = do
    x' <- $r2 bor (bnot constraint) x
    $d deref x
    res <- $r1 (bforall cube) x'
    $d deref x'
    return res
    
eqf  Ops{..} cube constraint x = do
    x' <- $r2 band constraint x
    $d deref x
    res <- $r1 (bexists cube) x'
    $d deref x'
    return res

cPreHelper cpreFunc quantFunc ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} hasOutgoingsCont labelPreds target = do
    su  <- cpreFunc ops si rs rd hasOutgoingsCont labelPreds target

    eqc <- $r1 (bexists _labelCube) consistentPlusCULCont
    equ <- $r1 (bexists _labelCube) consistentPlusCULUCont
    c   <- $r2 bor (bnot eqc) (bnot equ)
    mapM ($d deref) [eqc, equ]

    res <- quantFunc ops _untrackedCube (bnot c) su
    return res

cPreOver :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> t (ST s) (DDNode s u)
cPreOver ops@Ops{..} = cPreHelper cpreOver' eqf ops  

cPreUnder :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> SectionInfo s u -> RefineStatic s u -> RefineDynamic s u -> DDNode s u -> Lab s u -> DDNode s u -> t (ST s) (DDNode s u)
cPreUnder ops@Ops{..} = cPreHelper cpreUnder' faqf ops

fixedPointR :: (MonadResource (DDNode s u) (ST s) t) => 
               Ops s u -> 
               (DDNode s u -> t (ST s) (DDNode s u)) -> 
               DDNode s u -> 
               t (ST s) (DDNode s u)
fixedPointR ops@Ops{..} func start = do
    res <- func start
    $d deref start 
    case (res==start) of --this is safe 
        True -> return start
        False -> fixedPointR ops func res

forCont  CPlus  = RepeatGFP
forCont  CMinus = RepeatLFP

forUCont CPlus  = RepeatLFP
forUCont CMinus = RepeatGFP

data RefineType = 
      CPlus
    | CMinus

data RefineAction = 
      RepeatAll
    | RepeatLFP
    | RepeatGFP
    deriving (Show, Eq)

refineConsistency2 ops ts rd@RefineDynamic{..} rs@RefineStatic{..} si labelPreds hasOutgoings tgt = do
    winNoConstraint <- lift $ cpreCont' ops si rd labelPreds cont hasOutgoings tgt
    res             <- doConsistency ops ts consistentPlusCULCont consistentMinusCULCont winNoConstraint
    case res of
        Just (act, (consistentPlusCULCont', consistentMinusCULCont')) -> do
            let rd' = rd {consistentPlusCULCont = consistentPlusCULCont', consistentMinusCULCont = consistentMinusCULCont', numConsRef = numConsRef + 1}
            return $ Just (forCont act, rd')
        Nothing -> do
            winNoConstraint <- lift $ cpreUCont' ops si rd labelPreds cont tgt
            res             <- doConsistency ops ts consistentPlusCULUCont consistentMinusCULUCont winNoConstraint
            case res of
                Just (act, (consistentPlusCULUCont', consistentMinusCULUCont')) -> do
                    let rd' = rd {consistentPlusCULUCont = consistentPlusCULUCont', consistentMinusCULUCont = consistentMinusCULUCont', numConsRef = numConsRef + 1}
                    return $ Just (forUCont act, rd')
                Nothing -> return Nothing

type CPreFunc   t s u           = DDNode s u -> t (ST s) (DDNode s u)
type RefineFunc t s u sp lp st  = DDNode s u -> DDNode s u -> RefineDynamic s u -> StateT st (StateT (DB s u sp lp) (t (ST s))) (Maybe (RefineAction, RefineDynamic s u))

refineGFP, refineLFP :: (Show lp, Show sp, Ord lv, Ord lp, Ord sp, MonadResource (DDNode s u) (ST s) t) => 
             Ops s u -> 
             Abstractor s u sp lp st -> 
             TheorySolver s u sp lp lv -> 
             RefineStatic s u -> 
             SectionInfo s u -> 
             Lab s u -> 
             DDNode s u -> 
             CPreFunc t s u -> 
             RefineFunc t s u sp lp st
refineGFP ops@Ops{..} spec ts rs si labelPreds hasOutgoingsCont cpreOver tgt mayWin rd = do
    res <- liftIST $ refineConsistency2 ops ts rd rs si labelPreds hasOutgoingsCont tgt
    case res of 
        Just rd' -> do
            return $ Just rd'
        Nothing -> do
            res <- liftBDD $ do
                su      <- cpreOver tgt
                toDrop  <- $r2 band (bnot su) mayWin
                $d deref su
                res     <- lift $ refineStrategy ops si toDrop
                $d deref toDrop
                return res
            case res of 
                Nothing -> return Nothing
                Just vars -> do
                    rd'' <- promoteUntracked ops spec ts rd vars
                    return $ Just (RepeatAll, rd'')

refineLFP ops@Ops{..} spec ts rs si labelPreds hasOutgoingsCont cpreUnder tgt mustWin rd = do
    res <- liftIST $ refineConsistency2 ops ts rd rs si labelPreds hasOutgoingsCont tgt
    case res of 
        Just rd' -> do
            return $ Just rd'
        Nothing -> do
            res <- liftBDD $ do
                su      <- cpreUnder tgt
                toCheck <- $r2 band su (bnot mustWin)
                $d deref su
                res     <- lift $ refineStrategy ops si toCheck
                $d deref toCheck
                return res
            case res of 
                Nothing -> return Nothing
                Just vars -> do
                    rd'' <- promoteUntracked ops spec ts rd vars
                    return $ Just (RepeatAll, rd'')

--TODO: makes more sense to do all consistency refinements then all variable promotions
refine :: (MonadResource (DDNode s u) (ST s) t) => 
              CPreFunc t s u -> 
              CPreFunc t s u -> 
              RefineFunc t s u sp lp st -> 
              RefineFunc t s u sp lp st -> 
              Ops s u -> 
              RefineStatic s u -> 
              DDNode s u -> 
              DDNode s u -> 
              RefineDynamic s u -> 
              StateT st (StateT (DB s u sp lp) (t (ST s))) (Maybe (RefineAction, RefineDynamic s u))
refine cpreOver cpreUnder refineFuncGFP refineFuncLFP ops@Ops{..} rs@RefineStatic{..} buchiWinning lastLFP rd = do
    --TODO try mixing this with synthesis. ie. only refine buchi after
    --solving a safety game at the top level.
    let buchiRefine = do
        res <- refineFuncGFP buchiWinning buchiWinning rd
        case res of 
            Nothing -> return ()
            Just _  -> liftST $ traceST "Refined at buchi level"
        return res 

    let fairRefine  = mSumMaybe $ flip map goal $ \goal -> do
        tgt'       <- liftBDD $ $r2 band goal buchiWinning
        reachUnder <- liftBDD $ solveReach cpreUnder ops rs buchiWinning tgt' lastLFP
        tgt''      <- liftBDD $ $r2 bor tgt' reachUnder
        liftBDD $ $d deref tgt'

        let refineReach = do
            res <- refineFuncLFP reachUnder tgt'' rd
            case res of 
                Nothing -> return ()
                Just _  -> liftST $ traceST "Refined at reachability level"
            return res 

        let fairRefine = mSumMaybe $ flip map fair $ \fair -> do
                (tgt, res) <- liftBDD $ do
                    res     <- solveFair cpreOver ops rs buchiWinning tgt'' fair
                    tgt'''  <- $r2 band res fair
                    tgt     <- $r2 bor tgt'' tgt'''
                    $d deref tgt'''
                    return (tgt, res)

                res' <- refineFuncGFP tgt res rd
                liftBDD $ $d deref tgt
                liftBDD $ $d deref res

                case res' of 
                    Nothing -> return ()
                    Just _  -> liftST $ traceST "Refined at fair level"
                return res'

        res <- mSumMaybe [refineReach, fairRefine]
        liftBDD $ $d deref reachUnder
        liftBDD $ $d deref tgt''
        return res

    let fairRefine2  = mSumMaybe $ flip map goal $ \goal -> do
        let refineReach = do
            res <- refineFuncLFP lastLFP lastLFP rd
            case res of 
                Nothing -> return ()
                Just _  -> liftST $ traceST "Refined at reachability level heuristic"
            return res 

        let fairRefine = mSumMaybe $ flip map fair $ \fair -> do
                (tgt, res) <- liftBDD $ do
                    res     <- solveFair cpreOver ops rs buchiWinning lastLFP fair
                    tgt'''  <- $r2 band res fair
                    tgt     <- $r2 bor lastLFP tgt'''
                    $d deref tgt'''
                    return (tgt, res)

                res' <- refineFuncGFP tgt res rd
                liftBDD $ $d deref tgt
                liftBDD $ $d deref res

                case res' of 
                    Nothing -> return ()
                    Just _  -> liftST $ traceST "Refined at fair level heuristic"
                return res'
        res <- mSumMaybe [refineReach, fairRefine]
        return res

    mSumMaybe [buchiRefine, fairRefine]

--TODO try using a cache 
solveFair :: (MonadResource (DDNode s u) (ST s) t) => 
             (DDNode s u -> t (ST s) (DDNode s u)) -> 
             Ops s u -> 
             RefineStatic s u -> 
             DDNode s u -> 
             DDNode s u -> 
             DDNode s u -> 
             t (ST s) (DDNode s u)
solveFair cpreFunc ops@Ops{..} rs@RefineStatic{..} startPt winning fairr = do
    $rp ref startPt
    fixedPointR ops func startPt
    where
    func target = do
        t1 <- $r2 band target fairr
        t2 <- $r2 bor t1 winning
        $d deref t1
        res <- cpreFunc t2
        $d deref t2
        return res

solveReach :: (MonadResource (DDNode s u) (ST s) t) => 
              (DDNode s u -> t (ST s) (DDNode s u)) -> 
              Ops s u -> 
              RefineStatic s u -> 
              DDNode s u -> 
              DDNode s u -> 
              DDNode s u -> 
              t (ST s) (DDNode s u)
solveReach cpreFunc ops@Ops{..} rs@RefineStatic{..} startPt goall startingLFP = do
    $rp ref startingLFP
    fixedPointR ops func startingLFP
    where
    func target = do
        sz <- lift $ dagSize target
        lift $ traceMsg $ "r(" ++ show sz ++ ")"
        t1 <- $r2 bor target goall
        $rp ref bfalse
        res <- forAccumM bfalse fair $ \accum val -> do
            res' <- solveFair cpreFunc ops rs startPt t1 val
            res  <- $r2 bor res' accum
            $d deref res'
            $d deref accum
            return res
        $d deref t1
        return res

--TODO check if this consumes the initial state on each iteration
solveBuchi :: (MonadResource (DDNode s u) (ST s) t) => 
              (DDNode s u -> t (ST s) (DDNode s u)) -> 
              Ops s u -> 
              RefineStatic s u -> 
              DDNode s u -> 
              DDNode s u -> 
              t (ST s) (DDNode s u)
solveBuchi cpreFunc ops@Ops{..} rs@RefineStatic{..} startingPoint startingLFP = do
    $rp ref startingPoint
    fixedPointR ops func startingPoint
    where
    func reachN = do
        lift $ traceMsg "b"
        $rp ref btrue
        res <- forAccumM btrue goal $ \accum val -> do
            lift $ traceMsg "g"
            t1 <- $r2 band reachN val
            --TODO terminate when t1s are equal
            res' <- solveReach cpreFunc ops rs reachN t1 startingLFP
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

mkInitConsistency :: (MonadResource (DDNode s u) (ST s) t, Ord lv, Ord lp, Show lp) => 
                     Ops s u -> 
                     (lp -> [lv]) -> 
                     Map lv [lp] -> 
                     Map lp (DDNode s u) -> 
                     [(lp, DDNode s u)] -> 
                     DDNode s u -> 
                     t (ST s) (DDNode s u)
mkInitConsistency Ops{..} getVars mp mp2 labs initCons = do
    forAccumM initCons labs $ \accum (lp, en) -> do
        let theOperlappingPreds = concatMap (fromJustNote "mkInitConsistency" . flip Map.lookup mp) (getVars lp)
            theEns              = map (fromJustNote "mkInitConsistency2" . flip Map.lookup mp2) theOperlappingPreds
        lift $ traceST $ show lp ++ " clashes with " ++ show theOperlappingPreds
        forAccumM accum (delete en theEns) $ \accum theEn -> do
            constr <- $r $ bnot en .| bnot theEn
            res <- $r2 band accum constr
            mapM ($d deref) [constr, accum]
            return res

liftST   = lift . lift . lift
liftBDD  = lift . lift
liftIST  = lift
hoistAbs = hoist (hoist lift)
liftAS   = lift . hoist lift

--Create an initial abstraction and set up the data structures
initialAbstraction :: (Show sp, Show lp, Show lv, Ord sp, Ord lp, Ord lv, MonadResource (DDNode s u) (ST s) t) => 
                      Ops s u -> 
                      Abstractor s u sp lp st -> 
                      TheorySolver s u sp lp lv -> 
                      StateT st (StateT (DB s u sp lp) (t (ST s))) (RefineDynamic s u, RefineStatic s u)
initialAbstraction ops@Ops{..} Abstractor{..} TheorySolver{..} = do
    liftST  $ check "InitialAbstraction start" ops
    --abstract init
    initExpr <- hoistAbs $ initAbs (initOps ops)
    liftBDD $ $r $ return initExpr
    liftST  $ check "After compiling init" ops
    --abstract the goal
    (goalExprs, newVarsGoals) <- hoistAbs $ doGoal ops goalAbs
    liftBDD $ mapM ($r . return) goalExprs
    liftST  $ check "After compiling goal" ops
    --abstract the fair region
    (fairExprs, newVarsFairs) <- hoistAbs $ doStateLabel ops fairAbs
    liftBDD $ mapM ($r . return) fairExprs
    liftST  $ check "After compiling fair" ops
    --abstract the controllable condition
    (contExpr, newVarsCont) <- hoistAbs $ doStateLabel ops contAbs
    liftBDD $ $r $ return contExpr
    liftST  $ check "After compiling controllable" ops

    ivs <- liftAS $ sequence $ map (uncurryN $ getStaticVar ops) initialVars

    --get the abstract update functions for the goal predicates and variables
    let toUpdate = nub $ _allocatedStateVars newVarsGoals ++ _allocatedStateVars newVarsFairs ++ _allocatedStateVars newVarsCont ++ zip (map sel1 initialVars) ivs
    liftST  $ traceST $ "Initial transition relation state vars: \n" ++ (intercalate "\n" $ map (('\t' :) . show . fst) $ toUpdate)
    (updateExprs', inconsistent) <- hoistAbs $ doUpdate ops (updateAbs toUpdate)
    liftBDD $ mapM ($r . return) updateExprs'
    outcomeCube <- lift $ gets $ _outcomeCube . _sections
    updateExprs <- liftBDD $ mapM ($r . bexists outcomeCube) updateExprs'
    liftBDD $ mapM ($d deref) updateExprs'
    liftAS $ zipWithM (transSynopsys ops) (map fst toUpdate) updateExprs
    cubes  <- liftBDD $ mapM ($r . nodesToCube . snd) toUpdate
    groups <- liftBDD $ groupTrels ops $ zip cubes updateExprs
    liftST $ traceST $ "Number of transition partitions: " ++ show (length groups)

    --create the consistency constraints
    --TODO: should I also conjunct bnot inconsistent with consistentMinus?
    let consistentPlusCULCont  = bnot inconsistent
        consistentPlusCULUCont = bnot inconsistent
    liftBDD $ $rp ref consistentPlusCULCont
    liftBDD $ $rp ref consistentPlusCULUCont
    let inconsistentInit = bfalse
    liftBDD $ $rp ref inconsistentInit

    --compute the initial consistentMinus being as liberal as possible
    labelPreds <- liftIST $ gets $ _labelVars . _symbolTable
    let theMap = mkVarsMap $ map (id &&& getVarsLabel) $ Map.keys labelPreds
    liftST  $ traceST $ show theMap
    liftBDD $ $rp ref btrue
    consistentMinusCULCont' <- liftBDD $ mkInitConsistency ops getVarsLabel theMap (Map.map sel3 labelPreds) (map (id *** sel3) $ Map.toList labelPreds) btrue
    consistentMinusCULCont <- liftBDD $ $r2 band consistentMinusCULCont' consistentPlusCULCont
    liftBDD $ $d deref consistentMinusCULCont'
    let consistentMinusCULUCont = consistentMinusCULCont
    liftBDD $ $rp ref consistentMinusCULUCont

    --construct the RefineDynamic and RefineStatic
    let rd = RefineDynamic {
            trans       = groups,
            numConsRef  = 0,
            numStateRef = 0,
            ..
        }
        rs = RefineStatic {
            goal  = goalExprs,
            fair  = fairExprs,
            init  = initExpr,
            cont  = contExpr
        }
    return (rd, rs)

refineStrategy = refineFirstPrime

--Promote untracked state variables to full state variables so that we can make progress towards the goal. Does not refine the consistency relations.
promoteUntracked :: (Ord lp, Ord sp, Ord lv, Show sp, Show lp, MonadResource (DDNode s u) (ST s) t) => 
                    Ops s u -> 
                    Abstractor s u sp lp st -> 
                    TheorySolver s u sp lp lv -> 
                    RefineDynamic s u -> 
                    [Int] -> 
                    StateT st (StateT (DB s u sp lp) (t (ST s))) (RefineDynamic s u)
promoteUntracked ops@Ops{..} Abstractor{..} TheorySolver{..} rd@RefineDynamic{..} indices = do
    --look up the predicates to promote
    stateRev             <- liftIST $ gets $ _stateRev . _symbolTable
    let refineVars       =  nub $ map (fromJustNote "promoteUntracked: untracked indices not in stateRev" . flip Map.lookup stateRev) indices
    liftST $ traceST $ "* Promoting: \n" ++ (intercalate "\n" $ map (('\t' :) . show) $ refineVars)

    NewVars{..}          <- lift $ hoist lift $ promoteUntrackedVars ops refineVars
    labelPredsPreUpdate  <- liftIST $ gets $ _labelVars . _symbolTable

    --compute the update functions
    (updateExprs', inconsistent)   <- hoistAbs $ doUpdate ops (updateAbs _allocatedStateVars)
    liftBDD $ $rp ref inconsistent
    liftBDD $ mapM ($r . return) updateExprs'
    outcomeCube <- liftIST $ gets $ _outcomeCube . _sections
    updateExprs  <- liftBDD $ mapM ($r . bexists outcomeCube) updateExprs'
    liftBDD $ mapM ($d deref) updateExprs'
    liftAS $ zipWithM (transSynopsys ops) (map fst _allocatedStateVars) updateExprs
    cubes <- liftBDD $ mapM ($r . nodesToCube . snd) _allocatedStateVars
    groups <- liftBDD $ groupTrels' ops (last trans) $ zip cubes updateExprs
    liftST $ traceST $ "Number of transition partitions: " ++ show (length groups)

    labelPreds              <- liftIST $ gets $ _labelVars . _symbolTable
    let newLabelPreds       = labelPreds Map.\\ labelPredsPreUpdate
    let theMap              = mkVarsMap $ map (id &&& getVarsLabel) $ Map.keys labelPreds
    --TODO does old consistency relation need to be derefed
    consistentMinusCULCont'' <- liftBDD $ mkInitConsistency ops getVarsLabel theMap (Map.map sel3 labelPreds) (map (id *** sel3) $ Map.toList newLabelPreds) consistentMinusCULCont
    consistentMinusCULCont' <- liftBDD $ $r2 band consistentMinusCULCont'' (bnot inconsistent)
    liftBDD $ $d deref consistentMinusCULCont''

    consistentMinusCULUCont'' <- liftBDD $ mkInitConsistency ops getVarsLabel theMap (Map.map sel3 labelPreds) (map (id *** sel3) $ Map.toList newLabelPreds) consistentMinusCULUCont
    consistentMinusCULUCont' <- liftBDD $ $r2 band consistentMinusCULUCont'' (bnot inconsistent)
    liftBDD $ $d deref consistentMinusCULUCont''
    
    consistentPlusCULCont'  <- liftBDD $ $r2 band consistentPlusCULCont  (bnot inconsistent)
    liftBDD $ $d deref consistentPlusCULCont
    consistentPlusCULUCont' <- liftBDD $ $r2 band consistentPlusCULUCont (bnot inconsistent)
    liftBDD $ $d deref inconsistent
    liftBDD $ $d deref consistentPlusCULUCont

    return rd {
        --TODO does this order matter?
        trans  = Data.List.init trans ++ groups,
        consistentMinusCULCont = consistentMinusCULCont',
        consistentMinusCULUCont = consistentMinusCULUCont',
        consistentPlusCULCont = consistentPlusCULCont',
        consistentPlusCULUCont = consistentPlusCULUCont',
        numStateRef = numStateRef + 1
    }

--Calculates strongly connected components of label predicate graph
--Label predicates have an edge between them if they share a label variable
--Graph nodes: (label pred, encoding) pair
--Graph node keys: label pred
--Graph edges: label predicate (a) -> label predicates that share a label variable with label predicate (a) and are in the labelCube argument
sccs :: (Ord lv, Ord lp, Show lp) => SymbolInfo s u sp lp -> TheorySolver s u sp lp lv -> [(lp, a)] -> [[(lp, a)]]
sccs SymbolInfo{..} TheorySolver{..} labelCube = fmap (flatten . fmap (sel1 . func)) $ components theGraph
    where
    list             = map func labelCube
        where
        func pred    = (pred, fst pred, filter (flip elem (map fst labelCube)) $ concatMap (fromJust . flip Map.lookup vMap) $ getVarsLabel (fst pred))
    (theGraph, func) = graphFromEdges' list 
    --Map from label var -> [predicate that has this var in it]
    vMap             = mkVarsMap $ map (id &&& getVarsLabel) $ Map.keys _labelVars

--TODO is it correct to use this for gfp and lfp refinements?
doConsistency :: (Ord sp, Ord lp, Ord lv, Show sp, Show lp, MonadResource (DDNode s u) (ST s) t) => 
                 Ops s u -> 
                 TheorySolver s u sp lp lv -> 
                 DDNode s u -> 
                 DDNode s u -> 
                 DDNode s u -> 
                 StateT (DB s u sp lp) (t (ST s)) (Maybe (RefineType, (DDNode s u, DDNode s u)))
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
            return Nothing
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
                    lift $ lift $ traceST $ "UNSAT"
                    lift $ lift $ traceST $ "Core is" ++ show statePairs ++ " " ++ show labelPairs
                    inconsistent       <- lift $ stateLabelInconsistent ops syi statePairs labelPairs
                    consistentPlusCUL' <- lift $ $r2 band cPlus (bnot inconsistent)
                    lift $ $d deref cPlus
                    lift $ $d deref inconsistent
                    lift $ $d deref winNoConstraint
                    return $ Just (CPlus, (consistentPlusCUL', cMinus))
                    --doConsistency ops ts consistentPlusCUL' cMinus winNoConstraint
                Nothing -> do
                    --the (s, u, l) tuple is consistent so add this to consistentMinusCUL
                    lift $ $d deref winNoConstraint
                    lift $ lift $ traceST "SAT"

                    --groupedLabel :: [label predicate, [encoding]]
                    --return  a list of sub label cubes such that disjoint cubes dont share a label variable
                    let scs = sccs syi ts groupedLabel
                    let labelPreds = _labelVars 
                    --construct a list: [(label predicate, label variables in this predicate)]
                    --construct a Map from label variable -> a lift of predicates the variable occurs in
                    let theMap = mkVarsMap $ map (id &&& getVarsLabel) $ Map.keys labelPreds
                    cMinus' <- forAccumM cMinus scs $ \cons scc_val -> do
                        let scc = map fst scc_val
                        lift $ lift $ traceST $ "CC: " ++ show scc
                        --All predicates are the predicates in the game that share a label variable with one of the predicates in the scc
                        let allPreds = concatMap (fromJustNote "doConsistency" . flip Map.lookup theMap) $ nub $ concatMap getVarsLabel scc
                        lift $ lift $ traceST $ "All preds: " ++ show allPreds
                        --Fringe predicates are the ones that share a label variable with a predicate in the scc but are not in the scc
                        let fringePreds = allPreds \\ scc
                        lift $ lift $ traceST $ "Fringe Preds: " ++ show fringePreds
                        lift $ lift $ traceST ""
                        let labelPreds' = map (first $ fromJustNote "refineConsistency" . flip Map.lookup _labelVars) scc_val
                        let func (l, pol) = [(sel1 l, pol), ([sel3 l], [True])]
                        let allEns = map (sel3 . fromJustNote "refineConsistency" . flip Map.lookup _labelVars) allPreds
                        thisLabelCube <- lift $ $r $ nodesToCube $ map (sel3 . sel1) labelPreds'
                        thisLabel <- lift $ makeCubeInt ops $ concatMap func labelPreds'
                        eQuantExpr <- hoist lift $ doUpdate ops (eQuant scc_val)
                        lift $ $r $ return eQuantExpr
                        allCubeFalse <- lift $ $r $ makeCube ops $ zip allEns (repeat False)
                        cons1 <- lift $ $r2 band cons allCubeFalse
                        lift $ $d deref allCubeFalse
                        cons2 <- lift $ $r2 bexists thisLabelCube cons1
                        lift $ $d deref thisLabelCube
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

                    return $ Just (CMinus, (cPlus, cMinus'))

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

strategy :: forall s u t. (MonadResource (DDNode s u) (ST s) t) => 
            Ops s u -> 
            SectionInfo s u -> 
            RefineStatic s u -> 
            RefineDynamic s u -> 
            Lab s u -> 
            DDNode s u -> 
            t (ST s) ([[DDNode s u]], [[DDNode s u]])
strategy ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} labelPreds win = do
    lift $ traceST "* Computing strategy"
    hasOutgoings <- doHasOutgoings ops trans
    --For each goal
    res <- forM goal $ \goal -> do 
        winAndGoal <- $r2 band goal win
        $rp ref bfalse
        sequence $ replicate (length fair) ($r $ return bfalse)
        --Reachabiliy least fixedpoint
        res <- fixedPoint2R ops bfalse (repeat bfalse, []) $ \soFar (strats, regions) -> do 
            soFarOrWinAndGoal <- $r2 bor soFar winAndGoal
            $rp ref bfalse
            --For each fair
            (res, strats') <- forAccumLM bfalse fair $ \accum fair -> do
                --Fairness greatest fixedpoint
                --TODO optimise: dont use btrue below
                winFair <- solveFair (cPreUnder ops si rs rd hasOutgoings labelPreds) ops rs btrue soFarOrWinAndGoal fair
                thing <- $r2 band winFair fair
                thing2 <- $r2 bor thing soFarOrWinAndGoal
                $d deref thing
                (win', strats) <- cpre hasOutgoings thing2
                $d deref winFair
                $d deref thing2
                win <- $r2 bor win' accum 
                $d deref win'
                when (winFair /= win') (error "wrs not equal")
                $d deref accum
                return (win, strats)
            $d deref soFarOrWinAndGoal
            strats <- zipWithM (combineStrats soFar) strats strats'
            return (res, (strats, res : regions))
        $d deref winAndGoal
        return res
    $d deref hasOutgoings
    let (wins, strats') = unzip res
        (strats, regions) = unzip strats'
    win' <- $r $ conj ops wins
    mapM ($d deref) wins
    $d deref win'
    when (win' /= win) (lift $ traceST "Winning regions are not equal in strategy generation")
    return (strats, regions)
    where
    combineStrats :: (MonadResource (DDNode s u) (ST s) t) => DDNode s u -> DDNode s u -> DDNode s u -> t (ST s) (DDNode s u)
    combineStrats prevWin oldC newC = do
        c <- $r2 band newC (bnot prevWin)
        $d deref newC
        c' <- $r2 bor c oldC
        $d deref oldC
        return c'
    cpre hasOutgoings target = do
        strat        <- cpreCont' ops si rd labelPreds cont hasOutgoings target
        stratUCont   <- cpreUCont' ops si rd labelPreds cont target

        stratCont    <- $r2 band consistentMinusCULCont strat
        $d deref strat
        winCont'      <- $r1 (bexists _labelCube) stratCont

        hasOutgoingsC <- $r2 band hasOutgoings cont
        en'          <- $r2 band hasOutgoingsC consistentMinusCULCont
        en           <- $r1 (bexists _labelCube) en'
        $d deref en'
        $d deref hasOutgoingsC
        
        winCont      <- $r2 bimp en winCont'
        $d deref winCont'
        $d deref en
        winUCont     <- liftM bnot $ $r2 (andAbstract _labelCube) consistentPlusCULUCont stratUCont
        mapM ($d deref) [stratUCont]
        win'         <- $r2 band winCont winUCont
        mapM ($d deref) [winCont, winUCont]

        eqc <- $r1 (bexists _labelCube) consistentPlusCULCont
        equ <- $r1 (bexists _labelCube) consistentPlusCULUCont
        c   <- $r2 bor (bnot eqc) (bnot equ)
        mapM ($d deref) [eqc, equ]

        win          <- faqf ops _untrackedCube (bnot c) win'
        return (win, stratCont)

fixedPoint2R :: (MonadResource (DDNode s u) (ST s) t) => 
                Ops s u -> 
                DDNode s u -> 
                a -> 
                (DDNode s u -> a -> t (ST s) (DDNode s u, a)) -> 
                t (ST s) (DDNode s u, a)
fixedPoint2R ops@Ops{..} start thing func = do
    (res, thing') <- func start thing
    $d deref start 
    case (res==start) of 
        True -> return (start, thing')
        False -> fixedPoint2R ops res thing' func

{-

Game is 
    vX. uY. vZ. cpre_driver( Z .& F .| X .& G .| Y )

Complement is
    uX. vY. uZ. cpre_env((Z .| not F) .& (X .| not G) .& Y)

Inner 2 fixedpoints are: Reach fair region infinitely often staying out of the goal
Outer fixpoint is: as above but (never getting in goal, getting in goal once, getting in goal twice...) i.e. only hit the goal some finite number of times

-}

counterExample :: forall t s u. (MonadResource (DDNode s u) (ST s) t) => 
                  Ops s u -> 
                  SectionInfo s u -> 
                  RefineStatic s u -> 
                  RefineDynamic s u -> 
                  Lab s u -> 
                  DDNode s u -> 
                  t (ST s) [[DDNode s u]]
counterExample ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} labelPreds winGame = do
    lift $ traceST "* Computing counterexample"
    hasOutgoings <- doHasOutgoings ops trans 
    lift $ sequence $ replicate (length goal * length fair) (ref bfalse)
    sequence $ replicate (length goal * length fair + 1) ($r $ return bfalse)
    lift $ ref bfalse
    (win', strat) <- fixedPoint2R ops bfalse (zip goal $ repeat $ zip fair $ repeat bfalse) $ \x strat -> do
        $rp ref bfalse
        res <- forAccumLM bfalse strat $ \tot (goal, strats) -> do
            tgt               <- $r2 bor (bnot goal) x
            --TODO optimise: dont use btrue below
            winBuchi          <- liftM bnot $ solveReach (cPreOver ops si rs rd hasOutgoings labelPreds) ops rs btrue (bnot tgt) bfalse
            (winStrat, strat) <- stratReach si rs rd hasOutgoings strats x winBuchi tgt
            when (winStrat /= winBuchi) (lift $ traceST "Warning: counterexample winning regions are not equal")
            lift $ traceST "CHECK"
            $d deref winStrat
            $d deref tgt
            tot' <- $r2 bor tot winBuchi
            mapM ($d deref) [tot, winBuchi]
            return (tot', (goal, strat))
        return res
    when (winGame /= bnot win') (error "the counterexample winning region is not the complement of the game winning region")
    lift $ traceST $ bddSynopsis ops winGame
    $d deref hasOutgoings
    return $ map (map snd . snd) strat

    where

    target fair nGoalOrX y z = do
        a   <- $r2 bor z (bnot fair)
        b   <- $r2 band a y
        $d deref a
        c   <- $r2 band b nGoalOrX
        $d deref b
        return c

    --Below effectively skipps the middle fixed point
    stratReach si rs rd hasOutgoings stratSoFar x y nGoalOrX = do
        $rp ref x
        fixedPoint2R ops x stratSoFar $ \z strat -> do
            $rp ref btrue
            res <- forAccumLM btrue strat $ \winAccum (fair, strat) -> do
                tgt            <- target fair nGoalOrX y z
                (win', strat') <- strategy si rs rd hasOutgoings tgt
                $d deref tgt
                strat''        <- $r2 band strat' (bnot z)
                $d deref strat'
                --TODO use ite for strat
                strat'''       <- $r2 bor strat'' strat
                $d deref strat''
                $d deref strat

                eqc <- $r1 (bexists _labelCube) consistentPlusCULCont
                equ <- $r1 (bexists _labelCube) consistentPlusCULUCont
                c   <- $r2 band eqc equ
                mapM ($d deref) [eqc, equ]

                win            <- faqf ops _untrackedCube c win'
                -- $d deref win'
                winAccum'      <- $r2 band winAccum win
                mapM ($d deref) [win, winAccum]
                return (winAccum', (fair, strat'''))
            return res

    strategy si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} hasOutgoings target = do
        stratCont     <- cpreCont' ops si rd labelPreds cont hasOutgoings (bnot target)
        winCont'      <- $r2 (andAbstract _labelCube) consistentPlusCULCont stratCont
        $d deref stratCont
        hasOutgoingsC <- $r2 band hasOutgoings cont
        en'           <- $r2 band hasOutgoingsC consistentPlusCULCont
        $d deref hasOutgoingsC
        en            <- $r1 (bexists _labelCube) en'
        $d deref en'
        winCont       <- liftM bnot $ $r2 bimp btrue winCont'
        $d deref winCont'
        $d deref en
        
        stratUCont'   <- cpreUCont' ops si rd labelPreds cont (bnot target)
        stratUCont    <- $r2 band consistentMinusCULUCont stratUCont'
        winUCont      <- $r1 (bexists _labelCube) stratUCont
        mapM ($d deref) [stratUCont']
        win           <- $r2 bor winCont winUCont
        mapM ($d deref) [winCont, winUCont]
        return (win, stratUCont)

counterExampleLiberalEnv :: forall t s u. (MonadResource (DDNode s u) (ST s) t) => 
                  Ops s u -> 
                  SectionInfo s u -> 
                  RefineStatic s u -> 
                  RefineDynamic s u -> 
                  Lab s u -> 
                  DDNode s u -> 
                  t (ST s) [[DDNode s u]]
counterExampleLiberalEnv ops@Ops{..} si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} labelPreds winGame = do
    lift $ traceST "* Computing counterexample"
    hasOutgoings <- doHasOutgoings ops trans 
    lift $ sequence $ replicate (length goal * length fair) (ref bfalse)
    sequence $ replicate (length goal * length fair + 1) ($r $ return bfalse)
    lift $ ref bfalse
    (win', strat) <- fixedPoint2R ops bfalse (zip goal $ repeat $ zip fair $ repeat bfalse) $ \x strat -> do
        $rp ref bfalse
        res <- forAccumLM bfalse strat $ \tot (goal, strats) -> do
            tgt               <- $r2 bor (bnot goal) x
            --TODO optimise: dont use btrue below
            winBuchi          <- liftM bnot $ solveReach (cPreOver ops si rs rd hasOutgoings labelPreds) ops rs btrue (bnot tgt) bfalse
            (winStrat, strat) <- stratReach si rs rd hasOutgoings strats x winBuchi tgt
            when (winStrat /= winBuchi) (lift $ traceST "Warning: counterexample winning regions are not equal")
            $d deref winStrat
            $d deref tgt
            tot' <- $r2 bor tot winBuchi
            mapM ($d deref) [tot, winBuchi]
            return (tot', (goal, strat))
        return res
    when (winGame /= bnot win') (error "the counterexample winning region is not the complement of the game winning region")
    lift $ traceST $ bddSynopsis ops winGame
    $d deref hasOutgoings
    return $ map (map snd . snd) strat

    where

    target fair nGoalOrX y z = do
        a   <- $r2 bor z (bnot fair)
        b   <- $r2 band a y
        $d deref a
        c   <- $r2 band b nGoalOrX
        $d deref b
        return c

    --Below effectively skipps the middle fixed point
    stratReach si rs rd hasOutgoings stratSoFar x y nGoalOrX = do
        $rp ref x
        fixedPoint2R ops x stratSoFar $ \z strat -> do
            $rp ref btrue
            res <- forAccumLM btrue strat $ \winAccum (fair, strat) -> do
                tgt            <- target fair nGoalOrX y z
                (win', strat') <- strategy si rs rd hasOutgoings tgt
                $d deref tgt
                strat''        <- $r2 band strat' (bnot z)
                $d deref strat'
                --TODO use ite for strat
                strat'''       <- $r2 bor strat'' strat
                $d deref strat''
                $d deref strat
                win            <- $r1 (bexists _untrackedCube) win'
                $d deref win'
                winAccum'      <- $r2 band winAccum win
                mapM ($d deref) [win, winAccum]
                return (winAccum', (fair, strat'''))
            return res

    strategy si@SectionInfo{..} rs@RefineStatic{..} rd@RefineDynamic{..} hasOutgoings target = do
        stratCont <- cpreCont' ops si rd labelPreds cont hasOutgoings (bnot target)
        stratUCont' <- cpreUCont' ops si rd labelPreds cont (bnot target)
        winCont'     <- $r2 (andAbstract _labelCube) consistentMinusCULCont stratCont
        hasOutgoingsC <- $r2 band hasOutgoings cont
        en'          <- $r2 band hasOutgoingsC consistentMinusCULCont
        en           <- $r1 (bexists _labelCube) en'
        $d deref en'
        $d deref hasOutgoingsC
        winCont      <- liftM bnot $ $r2 bimp en winCont'
        $d deref winCont'
        $d deref en
        --TODO is below cPlus correct?
        stratUCont   <- $r2 band consistentPlusCULUCont stratUCont'
        winUCont     <- $r1 (bexists _labelCube) stratUCont
        mapM ($d deref) [stratCont, stratUCont']
        win          <- $r2 bor winCont winUCont
        mapM ($d deref) [winCont, winUCont]
        return (win, stratUCont)

data RefineInfo s u sp lp st = RefineInfo {
    si :: SectionInfo s u,
    rs :: RefineStatic s u,
    rd :: RefineDynamic s u,
    db :: DB s u sp lp,
    lp :: Lab s u,
    wu :: DDNode s u,
    wo :: DDNode s u,
    op :: Ops s u,
    st :: st
}

refineInit :: (Ord sp, Show sp, MonadResource (DDNode s u) (ST s) t) => 
              Ops s u -> 
              TheorySolver s u sp lp lv -> 
              RefineStatic s u -> 
              RefineDynamic s u -> 
              SymbolInfo s u sp lp -> 
              DDNode s u -> 
              t (ST s) (RefineDynamic s u, Bool)
refineInit ops@Ops{..} ts@TheorySolver{..} rs@RefineStatic{..} rd@RefineDynamic{..} syi@SymbolInfo{..} winRegion = do
    winning <- lift $ leqUnless (bnot winRegion) (bnot init) inconsistentInit
    case winning of 
        False -> do
            witness' <- $r2 band init (bnot winRegion)
            witness  <- $r2 band witness' (bnot inconsistentInit)
            $d deref witness'
            c <- lift $ presentInLargePrime ops witness
            $d deref witness
            let groupedState = groupForUnsatCore (sel2 . fromJustNote "refineInit1" . flip Map.lookup (_stateVars `Map.union` _initVars)) $ indicesToStatePreds syi c
            case unsatCoreState groupedState of
                Nothing -> do
                    lift $ traceST $ "* Found consistent losing state: " ++ show groupedState
                    return (rd, False)
                Just uc -> do
                    lift $ traceST "* Found inconsistent initial state. Refining..."
                    unsat <- makeCubeInt ops $ map (first (sel1 . fromJustNote "refineInit2" . flip Map.lookup (_stateVars `Map.union` _initVars))) uc
                    inconsistentInit' <- $r2 bor inconsistentInit unsat
                    $d deref inconsistentInit 
                    $d deref unsat
                    refineInit ops ts rs (rd {inconsistentInit = inconsistentInit'}) syi winRegion
        True  -> return (rd, True)

showResources :: Ops s u -> InUse (DDNode s u) -> ST s String
showResources Ops{..} mp = do 
    res <- liftM (intercalate "\n") (mapM (uncurry func) (sortBy sf $ Map.toList mp))
    return $ "\n\nBDDs still referenced: \n" ++ res ++ "\n\n"
    where
    sf = compare `on` (snd . snd)
    func res (locs, numRefs) = do
        sz <- dagSize res
        return $ " refs: " ++ show numRefs ++ "size: " ++ show sz ++ " locations: " ++ show (Set.toList locs)

lift4 = lift . lift . lift . lift
lift3 = lift . lift . lift
lift2 = lift . lift

--The abstraction-refinement loop
absRefineLoop :: forall s u o sp lp lv st t. (Ord sp, Ord lp, Show sp, Show lp, Show lv, Ord lv, MonadResource (DDNode s u) (ST s) t) => 
                 STDdManager s u -> 
                 Abstractor s u sp lp st -> 
                 TheorySolver s u sp lp lv -> 
                 Maybe Int -> 
                 t (ST s) (Maybe Bool, RefineInfo s u sp lp st)
absRefineLoop m spec ts maxIterations = let ops@Ops{..} = constructOps m in do
    idb <- lift $ initialDB ops
    (((winning, (si, rs, rd, lp, wo, wu)), st), db) <- flip runStateT idb $ flip runStateT (initialState spec) $ do
        (rd, rs) <- initialAbstraction ops spec ts
        lift2 $ $rp ref btrue
        lift2 $ $rp ref bfalse
        flip runContT return $ refineLoop ops rs rd btrue bfalse
    lift $ traceST $ "Preds: \n" ++ intercalate "\n" (map show $ extractStatePreds $ _symbolTable db)
    dc <- lift $ debugCheck
    ck <- lift $ checkKeys
    lift $ when (dc /= 0 || ck /= 0) (traceST "########################################################## Cudd inconsistent")

    {-
    derefStatic ops rs
    derefDynamic ops rd
    -}

    {-
    str <- getInUse >>= lift . showResources ops
    lift $ traceST str
    -}

    lift $ do
        let isState x = or $ map (`elem` _trackedInds (_sections db)) (sel2 x)
        traceST "Begin benchmarking stats"
        traceST $ "# state preds: "     ++ show (Map.size $ Map.filter isState $ _stateVars $ _symbolTable db)
        traceST $ "# untracked preds: " ++ show (Map.size $ Map.filter (not . isState) $ _stateVars $ _symbolTable db)
        traceST $ "# label preds: "     ++ show (Map.size $ _labelVars $ _symbolTable db)
        
        ds <- dagSize wu
        traceST $ "# nodes in winning bdd under: " ++ show ds

        ds <- dagSize wo
        traceST $ "# nodes in winning bdd over: " ++ show ds
        
        pnc <- readPeakNodeCount
        traceST $ "# nodes at peak: " ++ show pnc

        traceST $ "# consistency refinements: " ++ show (numConsRef rd)
        traceST $ "# state refinements: "       ++ show (numStateRef rd)

    return $ (winning, RefineInfo{op=ops, ..})
    where
    refineLoop ops@Ops{..} rs@RefineStatic{..} = refineLoop' 0 RepeatAll
        where 
        refineLoop' itr act rd@RefineDynamic{..} lastWin lastUnder = 
            callCC $ \exit  -> 
            callCC $ \exit2 -> 
            callCC $ \exit3 -> do

                si@SectionInfo{..} <- lift2 $ gets _sections
                syi                <- lift2 $ gets _symbolTable
                labelPreds <- lift2 $ gets $ _labelVars . _symbolTable
                let lp = map (sel1 &&& sel3) $ Map.elems labelPreds

                c <- lift3 $ do
                    eqc <- $r1 (bexists _labelCube) consistentPlusCULCont
                    equ <- $r1 (bexists _labelCube) consistentPlusCULUCont
                    c   <- $r2 band eqc equ
                    mapM ($d deref) [eqc, equ]
                    return c

                flip (maybe (return ())) maxIterations $ \val -> when (itr >= val) $ do
                    lift4 $ traceST "Max number of iterations exceeded."
                    exit3 (Nothing, (si, rs, rd, lp, lastWin, lastUnder))

                lift4 $ setVarMap _trackedNodes _nextNodes
                hasOutgoings <- lift3 $ doHasOutgoings ops trans

                (rd, winRegion) <- flip (if' (act == RepeatAll || act == RepeatGFP)) (return (rd, lastWin)) $ do
                    winRegion <- lift3 $ solveBuchi (cPreOver ops si rs rd hasOutgoings lp) ops rs lastWin lastUnder

                    l <- lift4 $ leqUnless winRegion lastWin (bnot c)
                    when (not l) (error "Sanity check 1")

                    lift3 $ $d deref lastWin
                    lift4 $ traceST ""
                    (rd, winning) <- lift3 $ refineInit ops ts rs rd syi winRegion
                    case winning of
                        False -> do
                            lift4 $ traceST "Losing"
                            lift3 $ mapM ($d deref) [hasOutgoings]
                            exit2 (Just False, (si, rs, rd, lp, winRegion, lastUnder))
                        True -> do
                            return (rd, winRegion)

                --Terminate early if must winning
                --TODO: would it be faster to use winRegion, lastUnder, or
                --their conjunction?
                (rd, winRegionUnder) <- flip (if' (act == RepeatAll || act == RepeatLFP)) (return (rd, lastUnder)) $ do
                    winRegionUnder <- lift3 $ solveBuchi (cPreUnder ops si rs rd hasOutgoings lp) ops rs winRegion lastUnder

                    l <- lift4 $ leqUnless lastUnder winRegionUnder (bnot c)
                    when (not l) (error "Sanity check 2")

                    lift3 $ $d deref lastUnder
                    lift4 $ traceST ""
                    (rd, winning) <- lift3 $ refineInit ops ts rs rd syi winRegionUnder
                    case winning of
                        True -> do
                            lift4 $ traceST "Winning: Early termination"
                            lift3 $ mapM ($d deref) [hasOutgoings]
                            exit (Just True, (si, rs, rd, lp, winRegion, winRegionUnder))
                        False -> do
                            return (rd, winRegionUnder)

                l <- lift4 $ leqUnless winRegionUnder winRegion (bnot c)
                when (not l) (error "Sanity check 3")
                lift3 $ $d deref c
                
                --Alive: winRegion, rd, rs, hasOutgoings, winRegionUnder
                --TODO: is it correct to use the same type of consistency
                --refinement for GFP and LFP?
                let cpu  = cPreUnder  ops si rs rd hasOutgoings lp
                    cpo  = cPreOver   ops si rs rd hasOutgoings lp
                    cpo' = cpreOver'  ops si rs rd hasOutgoings lp
                    cpu' = cpreUnder' ops si rs rd hasOutgoings lp
                    rfG  = refineGFP  ops spec ts rs si lp hasOutgoings cpo'
                    rfL  = refineLFP  ops spec ts rs si lp hasOutgoings cpu'

                res <- lift $ refine cpo cpu rfG rfL ops rs winRegion winRegionUnder rd
                lift3 $ $d deref hasOutgoings   
                case res of 
                    Nothing -> do 
                        lift4 $ traceST "No refinements to make. Warning: this should never happen. It is a bug. Please tell Adam"
                        return (Just True, (si, rs, rd, lp, winRegion, winRegionUnder))
                    Just (act, rd) -> do
                        lift4 $ traceST $ show act
                        refineLoop' (itr+1) act rd winRegion winRegionUnder

--An initial state that wasnt may winning was discovered. We therefore must provide a spoiling strategy from any not may winning (== must losing) state.
cex :: (MonadResource (DDNode s u) (ST s) t) => RefineInfo s u sp lp st -> t (ST s) [[DDNode s u]]
cex RefineInfo{..} = counterExample op si rs rd lp wo

--This is pretty meaningless
cexLiberalEnv :: (MonadResource (DDNode s u) (ST s) t) => RefineInfo s u sp lp st -> t (ST s) [[DDNode s u]]
cexLiberalEnv RefineInfo{..} = counterExampleLiberalEnv op si rs rd lp wo

strat :: (MonadResource (DDNode s u) (ST s) t) => RefineInfo s u sp lp st -> t (ST s) ([[DDNode s u]], [[DDNode s u]])
strat RefineInfo{..} = strategy op si rs rd lp wu

