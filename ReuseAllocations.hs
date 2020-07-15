{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeFamilies #-}

module ReuseAllocations (reuseAllocationsPass) where

import Control.Monad.Reader
-- import Data.Function ((&))
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import Data.Tuple (swap)
import Debug.Trace
import qualified Futhark.Analysis.Alias as Alias
import Futhark.IR.KernelsMem
import Futhark.Pass (Pass (..), intraproceduralTransformation)
import Futhark.Util.Pretty
import qualified LastUse
import LastUse (LastUseMap)

type Frees = [(VName, SubExp)]

type Allocs = [(VName, SubExp)]

type ReuseAllocsM = Reader (Scope KernelsMem)

traceWith :: Pretty a => String -> a -> a
traceWith s a = trace (s ++ ": " ++ pretty a) a

reuseAllocationsPass :: Pass KernelsMem KernelsMem
reuseAllocationsPass =
  Pass
    { passName = "reuse allocations",
      passDescription = "reuse allocations in all functions",
      passFunction = intraproceduralTransformation optimise
    }
  where
    optimise scope stms =
      return $ runReader (optimiser stms) scope

optimiser :: Stms KernelsMem -> ReuseAllocsM (Stms KernelsMem)
optimiser stms =
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
optimiseStms lu_map allocs frees stms = do
  (allocs', frees', stms') <- foldM (walkStms lu_map) (allocs, frees, []) $ stmsToList stms
  return (allocs', frees', stmsFromList $ reverse stms')

walkStms :: LastUseMap -> (Allocs, Frees, [Stm KernelsMem]) -> Stm KernelsMem -> ReuseAllocsM (Allocs, Frees, [Stm KernelsMem])
walkStms _ (allocs, frees, acc) stm@Let {stmExp = Op (Alloc sexp _), stmPattern = Pattern {patternValueElements = [PatElem {patElemName}]}} =
  localScope (scopeOf stm) $ do
    case lookup (traceWith (pretty patElemName ++ " lookup") sexp) $ map swap $ traceWith "frees" frees of
      Just mem ->
        return $
          trace
            (pretty patElemName ++ " found a result " ++ show mem)
            ((patElemName, sexp) : allocs, filter ((/=) sexp . snd) frees, stm {stmExp = BasicOp $ SubExp $ Var mem} : acc)
      Nothing ->
        return ((patElemName, sexp) : allocs, frees, stm : acc)
walkStms lu_map (allocs, frees, acc) stm@Let {stmExp = Op (Inner (SegOp (SegScan lvl sp binops tps body)))} =
  localScope (scopeOf stm) $ do
    (allocs', frees', body') <- optimiseKernelBody lu_map allocs frees body
    (allocs'', frees'', binops') <- foldM (optimiseSegBinOp lu_map) (allocs', frees', []) binops
    return (allocs'', frees'', stm {stmExp = Op $ Inner $ SegOp $ SegScan lvl sp (reverse binops') tps body'} : acc)
walkStms lu_map (allocs, frees, acc) stm@Let {stmExp = Op (Inner (SegOp (SegRed lvl sp binops tps body)))} =
  localScope (scopeOf stm) $ do
    (allocs', frees', body') <- optimiseKernelBody lu_map allocs frees body
    (allocs'', frees'', binops') <- foldM (optimiseSegBinOp lu_map) (allocs', frees', []) binops
    return (allocs'', frees'', stm {stmExp = Op $ Inner $ SegOp $ SegRed lvl sp (reverse binops') tps body'} : acc)
walkStms lu_map (allocs, frees, acc) stm =
  localScope (scopeOf stm) $ do
    let pat_name = patElemName $ head $ patternValueElements $ stmPattern stm
    let lus = Map.lookup pat_name lu_map
    new_frees <- mapM (memAndSize allocs) $ maybe [] namesToList lus
    let new_frees' = catMaybes new_frees
    return $
      trace
        (pretty pat_name ++ " adding new frees: " ++ pretty new_frees' ++ " to already " ++ pretty frees)
        (allocs, new_frees' ++ frees, stm : acc)

optimiseKernelBody :: LastUseMap -> Allocs -> Frees -> KernelBody KernelsMem -> ReuseAllocsM (Allocs, Frees, KernelBody KernelsMem)
optimiseKernelBody lu_map allocs frees body@KernelBody {kernelBodyStms} = do
  (allocs', frees', stms) <-
    foldM (walkStms lu_map) (allocs, frees, []) $ stmsToList kernelBodyStms
  return (allocs', frees', body {kernelBodyStms = stmsFromList $ reverse stms})

optimiseSegBinOp :: LastUseMap -> (Allocs, Frees, [SegBinOp KernelsMem]) -> SegBinOp KernelsMem -> ReuseAllocsM (Allocs, Frees, [SegBinOp KernelsMem])
optimiseSegBinOp lu_map (allocs, frees, acc) binop@SegBinOp {segBinOpLambda} = do
  (allocs', frees', lambda) <- optimiseLambda lu_map allocs frees segBinOpLambda
  return (allocs', frees', binop {segBinOpLambda = lambda} : acc)

optimiseLambda :: LastUseMap -> Allocs -> Frees -> Lambda KernelsMem -> ReuseAllocsM (Allocs, Frees, Lambda KernelsMem)
optimiseLambda lu_map allocs frees lambda = do
  (allocs', frees', body) <- optimiseBody lu_map allocs frees $ lambdaBody lambda
  return (allocs', frees', lambda {lambdaBody = body})

optimiseBody :: LastUseMap -> Allocs -> Frees -> Body KernelsMem -> ReuseAllocsM (Allocs, Frees, Body KernelsMem)
optimiseBody lu_map allocs frees body = do
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
