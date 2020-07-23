{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeFamilies #-}

module Futhark.Optimise.ReuseAllocations (reuseAllocations, interference) where

import Control.Monad.Reader
import Data.Function ((&))
import Data.Functor ((<&>))
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromMaybe)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Tuple (swap)
import Debug.Trace
import qualified Futhark.Analysis.Alias as Alias
import qualified Futhark.Analysis.LastUse as LastUse
import Futhark.Analysis.LastUse (LastUseMap)
import Futhark.IR.KernelsMem
import Futhark.IR.Prop.Names
import Futhark.Pass (Pass (..), intraproceduralTransformation)
import Futhark.Pipeline

type InUse = Names

type LastUsed = Names

type Graph = Set (VName, VName)

type Frees = [(VName, SubExp)]

type Allocs = [(VName, SubExp)]

type ReuseAllocsM = Reader (Scope KernelsMem)

traceWith s p a = trace (s ++ " (" ++ pretty p ++ "): " ++ pretty a) a

insertEdge :: VName -> VName -> Graph -> Graph
insertEdge v1 v2 g
  | v1 == v2 = g
  | otherwise = Set.insert (min v1 v2, max v1 v2) g

cartesian :: Names -> Names -> Graph
cartesian ns1 ns2 =
  [(min x y, max x y) | x <- namesToList ns1, y <- namesToList ns2]
    & foldr (uncurry insertEdge) mempty

analyseStm :: LastUseMap -> InUse -> Graph -> Stm KernelsMem -> ReuseAllocsM (InUse, LastUsed, Graph)
analyseStm lumap inuse0 graph0 stm =
  localScope (scopeOf stm) $ do
    mems <-
      stmPattern stm
        & patternValueElements
        & mapM (memInfo . patElemName)
        <&> catMaybes
    let inuse = inuse0 <> namesFromList (mems)
    let graph = graph0 <> (inuse `cartesian` inuse)

    let pat_name = patElemName $ head $ patternValueElements $ stmPattern stm
    let lus0 =
          Map.lookup pat_name lumap
            & fromMaybe mempty

    case stmExp stm of
      If cse then_body else_body dec -> do
        (inuse1, lus1, g1) <- analyseBody lumap then_body
        (inuse2, lus2, g2) <- analyseBody lumap else_body
        let lus = lus0 <> lus1 <> lus2
            inuse' = (inuse <> inuse1 <> inuse2) `namesSubtract` lus
            g =
              graph <> g1 <> g2
                <> ((inuse1 <> lus1) `cartesian` (inuse `namesSubtract` (lus2 `namesSubtract` lus1)))
                <> ((inuse2 <> lus2) `cartesian` (inuse `namesSubtract` (lus1 `namesSubtract` lus2)))
        return $ traceWith "If" pat_name (inuse', lus, g)
      Apply _ _ _ _ -> do
        let inuse' = inuse `namesSubtract` lus0
        return $ traceWith "Apply" pat_name (inuse', lus0, graph)
      BasicOp _ -> do
        let inuse' = inuse `namesSubtract` lus0
        return $ traceWith "BasicOp" pat_name (inuse', lus0, graph)
      DoLoop ctx vals form body -> do
        (inuse', lus, graph') <- analyseBody lumap body
        let lus' = lus <> lus0
        let graph'' = graph <> graph' <> inuse `cartesian` (inuse' <> lus')
        let inuse'' = inuse `namesSubtract` lus <> inuse'
        return $ traceWith "DoLoop" pat_name (inuse'', lus', graph'')
      Op (Inner (SegOp (SegMap lvl _ tps body))) -> do
        (inuse', lus, graph') <- analyseKernelBody lumap body
        let lus' = lus <> lus0
        let graph'' = graph <> graph' <> inuse `cartesian` (inuse' <> lus')
        let inuse'' = inuse `namesSubtract` lus <> inuse'
        return $ traceWith "SegMap" pat_name (inuse'', lus', graph'')
      Op (Inner (SegOp (SegRed lvl _ binops tps body))) -> do
        undefined
      Op (Inner (SegOp (SegScan lvl _ binops tps body))) -> do
        undefined
      Op (Inner (SegOp (SegHist lvl _ histops tps body))) -> do
        undefined
      Op (Inner (SizeOp _)) -> do
        undefined
      Op (Inner (OtherOp _)) -> do
        undefined
      Op (Alloc _ _) -> do
        let inuse' = inuse `namesSubtract` lus0
        return $ traceWith "Alloc" pat_name (inuse', lus0, graph)

analyseKernelBody :: LastUseMap -> KernelBody KernelsMem -> ReuseAllocsM (InUse, LastUsed, Graph)
analyseKernelBody lumap body = analyseStms lumap $ kernelBodyStms body

analyseBody :: LastUseMap -> Body KernelsMem -> ReuseAllocsM (InUse, LastUsed, Graph)
analyseBody lumap body = analyseStms lumap $ bodyStms body

analyseStms :: LastUseMap -> Stms KernelsMem -> ReuseAllocsM (InUse, LastUsed, Graph)
analyseStms lumap stms = do
  foldM
    ( \(inuse, lus, graph) stm -> do
        (inuse', lus', graph') <- analyseStm lumap inuse graph stm
        return (inuse', lus' <> lus, graph')
    )
    (mempty, mempty, mempty)
    $ stmsToList stms

interference :: Action KernelsMem
interference =
  Action
    { actionName = "memory interference graph",
      actionDescription = "Analyse interference",
      actionProcedure = mapM_ helper . progFuns
    }
  where
    helper fun = do
      let fun' = Alias.analyseFun fun
      let lumap = fst $ LastUse.analyseFun mempty mempty fun'
      let (inuse, lastused, graph) = runReader (analyseBody lumap (funDefBody fun)) $ scopeOf fun
      liftIO $ putStrLn ""
      liftIO $ putStrLn $ unlines $ fmap (\(x, y) -> pretty x ++ " <-> " ++ pretty y) $ Set.toList graph
      liftIO $ putStrLn ""
      liftIO $ putStrLn $ unlines $ fmap pretty $ namesToList inuse
      liftIO $ putStrLn ""
      liftIO $ putStrLn $ unlines $ fmap pretty $ namesToList lastused

reuseAllocations :: Pass KernelsMem KernelsMem
reuseAllocations =
  Pass
    { passName = "reuse allocations",
      passDescription = "reuse allocations in all functions",
      passFunction = intraproceduralTransformation helper
    }
  where
    helper scope stms =
      return $ runReader (optimise stms) scope

optimise :: Stms KernelsMem -> ReuseAllocsM (Stms KernelsMem)
optimise stms =
  localScope (scopeOf stms) $ do
    let (aliased_stms, _) = Alias.analyseStms mempty stms
        (lu_map, _) = LastUse.analyseStms mempty mempty aliased_stms
    (allocs, frees, stms') <- optimiseStms lu_map [] [] stms
    return $
      trace
        ( unlines
            [ "allocs: " ++ pretty allocs,
              "frees: " ++ pretty frees
            ]
        )
        stms'

optimiseStms :: LastUseMap -> Allocs -> Frees -> Stms KernelsMem -> ReuseAllocsM (Allocs, Frees, Stms KernelsMem)
optimiseStms lu_map allocs frees stms =
  localScope (scopeOf stms) $ do
    (allocs', frees', stms') <- foldM (walkStms lu_map) (allocs, frees, []) $ stmsToList stms
    return (allocs', frees', stmsFromList $ reverse stms')

walkStms :: LastUseMap -> (Allocs, Frees, [Stm KernelsMem]) -> Stm KernelsMem -> ReuseAllocsM (Allocs, Frees, [Stm KernelsMem])
walkStms _ (allocs, frees, acc) stm@Let {stmExp = Op (Alloc sexp _), stmPattern = Pattern {patternValueElements = [PatElem {patElemName}]}} =
  localScope (scopeOf stm) $ do
    case lookup sexp $ map swap $ trace (unwords [pretty patElemName, "frees", pretty frees]) frees of
      Just mem ->
        return $
          trace
            (pretty patElemName ++ " found a result " ++ show mem)
            ((patElemName, sexp) : allocs, filter ((/=) sexp . snd) frees, stm {stmExp = BasicOp $ SubExp $ Var mem} : acc)
      Nothing ->
        return ((patElemName, sexp) : allocs, frees, stm : acc)
walkStms lu_map (allocs, frees, acc) stm@Let {stmExp = Op (Inner (SegOp (SegMap lvl sp tps body)))} =
  localScope (scopeOfSegSpace sp) $ do
    (allocs', frees', body') <- optimiseKernelBody lu_map allocs frees body
    return (allocs', frees', stm {stmExp = Op $ Inner $ SegOp $ SegMap lvl sp tps body'} : acc)
walkStms lu_map (allocs, frees, acc) stm@Let {stmExp = Op (Inner (SegOp (SegScan lvl sp binops tps body)))} = do
  localScope (scopeOfSegSpace sp) $ do
    (allocs', frees', body') <- optimiseKernelBody lu_map allocs frees body
    (allocs'', frees'', binops') <- foldM (optimiseSegBinOp lu_map) (allocs', frees', []) binops
    return (allocs'', frees'', stm {stmExp = Op $ Inner $ SegOp $ SegScan lvl sp (reverse binops') tps body'} : acc)
walkStms lu_map (allocs, frees, acc) stm@Let {stmExp = Op (Inner (SegOp (SegRed lvl sp binops tps body)))} =
  localScope (scopeOfSegSpace sp) $ do
    (allocs', frees', body') <- optimiseKernelBody lu_map allocs frees body
    (allocs'', frees'', binops') <- foldM (optimiseSegBinOp lu_map) (allocs', frees', []) binops
    return (allocs'', frees'', stm {stmExp = Op $ Inner $ SegOp $ SegRed lvl sp (reverse binops') tps body'} : acc)
walkStms lu_map (allocs, frees, acc) stm@Let {stmExp = Op (Inner (SegOp (SegHist lvl sp histops tps body)))} =
  localScope (scopeOfSegSpace sp) $ do
    (allocs', frees', body') <- optimiseKernelBody lu_map allocs frees body
    (allocs'', frees'', histops') <- foldM (optimiseHistOp lu_map) (allocs', frees', []) histops
    return (allocs'', frees'', stm {stmExp = Op $ Inner $ SegOp $ SegHist lvl sp (reverse histops') tps body'} : acc)
walkStms lu_map (allocs, frees, acc) stm = do
  localScope (scopeOf stm) $ do
    let pat_name = patElemName $ head $ patternValueElements $ stmPattern stm
    let lus = Map.lookup pat_name lu_map
    new_frees <- mapM (memAndSize allocs) $ maybe [] namesToList lus
    let new_frees' = catMaybes new_frees
    return $
      trace
        (unwords [pretty pat_name, " adding new frees: ", pretty new_frees', " to already ", pretty frees, " from lus:", pretty lus, " and allocs: ", pretty allocs])
        (allocs, new_frees' ++ frees, stm : acc)

optimiseKernelBody :: LastUseMap -> Allocs -> Frees -> KernelBody KernelsMem -> ReuseAllocsM (Allocs, Frees, KernelBody KernelsMem)
optimiseKernelBody lu_map allocs frees body@KernelBody {kernelBodyStms} =
  localScope (scopeOf kernelBodyStms) $ do
    (allocs', frees', stms) <-
      foldM (walkStms lu_map) (allocs, frees, []) $ stmsToList kernelBodyStms
    return (allocs', frees', body {kernelBodyStms = stmsFromList $ reverse stms})

optimiseSegBinOp :: LastUseMap -> (Allocs, Frees, [SegBinOp KernelsMem]) -> SegBinOp KernelsMem -> ReuseAllocsM (Allocs, Frees, [SegBinOp KernelsMem])
optimiseSegBinOp lu_map (allocs, frees, acc) binop@SegBinOp {segBinOpLambda} = do
  (allocs', frees', lambda) <- optimiseLambda lu_map allocs frees segBinOpLambda
  return (allocs', frees', binop {segBinOpLambda = lambda} : acc)

optimiseHistOp :: LastUseMap -> (Allocs, Frees, [HistOp KernelsMem]) -> HistOp KernelsMem -> ReuseAllocsM (Allocs, Frees, [HistOp KernelsMem])
optimiseHistOp lu_map (allocs, frees, acc) histop@HistOp {histOp} = do
  (allocs', frees', lambda) <- optimiseLambda lu_map allocs frees histOp
  return (allocs', frees', histop {histOp = lambda} : acc)

optimiseLambda :: LastUseMap -> Allocs -> Frees -> Lambda KernelsMem -> ReuseAllocsM (Allocs, Frees, Lambda KernelsMem)
optimiseLambda lu_map allocs frees lambda =
  localScope (scopeOfLParams $ lambdaParams lambda) $ do
    (allocs', frees', body) <- optimiseBody lu_map allocs frees $ lambdaBody lambda
    return (allocs', frees', lambda {lambdaBody = body})

optimiseBody :: LastUseMap -> Allocs -> Frees -> Body KernelsMem -> ReuseAllocsM (Allocs, Frees, Body KernelsMem)
optimiseBody lu_map allocs frees body =
  localScope (scopeOf $ bodyStms body) $ do
    (allocs', frees', stms') <- optimiseStms lu_map allocs frees $ bodyStms body
    return (allocs', frees', body {bodyStms = stms'})

memAndSize :: Allocs -> VName -> ReuseAllocsM (Maybe (VName, SubExp))
memAndSize allocs vname = do
  summary <- asksScope (fmap nameInfoToMemInfo . Map.lookup vname)
  case summary of
    Just (MemArray _ _ _ (ArrayIn mem _)) ->
      return $ List.find ((== mem) . fst) allocs
    _ ->
      return Nothing

nameInfoToMemInfo :: Mem lore => NameInfo lore -> MemBound NoUniqueness
nameInfoToMemInfo info =
  case info of
    FParamName summary -> noUniquenessReturns summary
    LParamName summary -> summary
    LetName summary -> summary
    IndexName it -> MemPrim $ IntType it

memInfo :: VName -> ReuseAllocsM (Maybe (VName))
memInfo vname = do
  summary <- asksScope (fmap nameInfoToMemInfo . Map.lookup vname)
  case summary of
    Just (MemArray _ _ _ (ArrayIn mem _)) ->
      return $ Just mem
    _ ->
      return Nothing
