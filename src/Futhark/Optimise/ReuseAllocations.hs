{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeFamilies #-}

module Futhark.Optimise.ReuseAllocations (optimise) where

import Control.Arrow (first)
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Function ((&))
import qualified Data.Map as Map
import Data.Map (Map, (!))
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Tuple (swap)
import Debug.Trace
import qualified Futhark.Analysis.Interference as Interference
import qualified Futhark.Analysis.LastUse as LastUse
import Futhark.Binder.Class
import Futhark.Construct
import Futhark.IR.KernelsMem
import qualified Futhark.Optimise.ReuseAllocations.GreedyColoring as GreedyColoring
import qualified Futhark.Pass as Pass
import Futhark.Pass (Pass (..), PassM)

type Allocs = Map VName (SubExp, Space)

-- type ReuseAllocsM = ReaderT (Scope KernelsMem) (Reader VNameSource)

type ReuseAllocsM = Binder KernelsMem

getAllocsStm :: Stm KernelsMem -> Allocs
getAllocsStm (Let (Pattern [] [PatElem name _]) _ (Op (Alloc se sp))) =
  Map.singleton name (se, sp)
getAllocsStm (Let _ _ (Op (Alloc _ _))) = error "impossible"
getAllocsStm (Let _ _ (Op (Inner (SegOp segop)))) = getAllocsSegOp segop
getAllocsStm (Let _ _ (If _ then_body else_body _)) =
  foldMap getAllocsStm (bodyStms then_body) <> foldMap getAllocsStm (bodyStms else_body)
getAllocsStm (Let _ _ (DoLoop _ _ _ body)) =
  foldMap getAllocsStm (bodyStms body)
getAllocsStm _ = mempty

getAllocsLambda :: Lambda KernelsMem -> Allocs
getAllocsLambda (Lambda _ body _) =
  foldMap getAllocsStm $ bodyStms body

getAllocsSegBinOp :: SegBinOp KernelsMem -> Allocs
getAllocsSegBinOp (SegBinOp _ lambda _ _) =
  getAllocsLambda lambda

getAllocsHistOp :: HistOp KernelsMem -> Allocs
getAllocsHistOp (HistOp _ _ _ _ _ histop) =
  getAllocsLambda histop

getAllocsSegOp :: SegOp lvl KernelsMem -> Allocs
getAllocsSegOp (SegMap _ _ _ body) =
  foldMap getAllocsStm (kernelBodyStms body)
getAllocsSegOp (SegRed _ _ segbinops _ body) =
  foldMap getAllocsStm (kernelBodyStms body) <> foldMap getAllocsSegBinOp segbinops
getAllocsSegOp (SegScan _ _ segbinops _ body) =
  foldMap getAllocsStm (kernelBodyStms body) <> foldMap getAllocsSegBinOp segbinops
getAllocsSegOp (SegHist _ _ histops _ body) =
  foldMap getAllocsStm (kernelBodyStms body) <> foldMap getAllocsHistOp histops

setAllocsStm :: Map VName SubExp -> Stm KernelsMem -> Stm KernelsMem
setAllocsStm m stm@(Let (Pattern [] [PatElem name _]) _ (Op (Alloc _ _)))
  | Just s <- Map.lookup name m =
    stm {stmExp = BasicOp $ SubExp s}
setAllocsStm _ (Let _ _ (Op (Alloc _ _))) = error "impossible"
setAllocsStm m stm@(Let _ _ (Op (Inner (SegOp segop)))) =
  stm {stmExp = Op $ Inner $ SegOp $ setAllocsSegOp m segop}
setAllocsStm m stm@(Let _ _ (If cse then_body else_body dec)) =
  stm
    { stmExp =
        If
          cse
          (then_body {bodyStms = fmap (setAllocsStm m) $ bodyStms then_body})
          (else_body {bodyStms = fmap (setAllocsStm m) $ bodyStms else_body})
          dec
    }
setAllocsStm m stm@(Let _ _ (DoLoop ctx vals form body)) =
  stm
    { stmExp =
        DoLoop
          ctx
          vals
          form
          (body {bodyStms = fmap (setAllocsStm m) $ bodyStms body})
    }
setAllocsStm _ stm = stm

setAllocsLambda :: Map VName SubExp -> Lambda KernelsMem -> Lambda KernelsMem
setAllocsLambda m lambda@(Lambda _ body _) =
  lambda {lambdaBody = body {bodyStms = fmap (setAllocsStm m) $ bodyStms body}}

setAllocsSegBinOp :: Map VName SubExp -> SegBinOp KernelsMem -> SegBinOp KernelsMem
setAllocsSegBinOp m segbinop =
  segbinop {segBinOpLambda = setAllocsLambda m $ segBinOpLambda segbinop}

setAllocsHistOp :: Map VName SubExp -> HistOp KernelsMem -> HistOp KernelsMem
setAllocsHistOp m hop =
  hop {histOp = setAllocsLambda m $ histOp hop}

setAllocsSegOp :: Map VName SubExp -> SegOp lvl KernelsMem -> SegOp lvl KernelsMem
setAllocsSegOp m (SegMap lvl sp tps body) =
  SegMap lvl sp tps $ body {kernelBodyStms = fmap (setAllocsStm m) $ kernelBodyStms body}
setAllocsSegOp m (SegRed lvl sp segbinops tps body) =
  SegRed lvl sp (fmap (setAllocsSegBinOp m) segbinops) tps $
    body {kernelBodyStms = fmap (setAllocsStm m) $ kernelBodyStms body}
setAllocsSegOp m (SegScan lvl sp segbinops tps body) =
  SegScan lvl sp (fmap (setAllocsSegBinOp m) segbinops) tps $
    body {kernelBodyStms = fmap (setAllocsStm m) $ kernelBodyStms body}
setAllocsSegOp m (SegHist lvl sp segbinops tps body) =
  SegHist lvl sp (fmap (setAllocsHistOp m) segbinops) tps $
    body {kernelBodyStms = fmap (setAllocsStm m) $ kernelBodyStms body}

invertMap :: (Ord v, Ord k) => Map k v -> Map v (Set k)
invertMap m =
  Map.toList m
    & fmap (swap . first Set.singleton)
    & foldr (uncurry $ Map.insertWith (<>)) mempty

maxSubExp :: Set SubExp -> ReuseAllocsM SubExp
maxSubExp = helper . Set.toList
  where
    helper (s1 : s2 : sexps) = do
      z <- letSubExp "maxSubHelper" $ BasicOp $ BinOp (UMax Int64) s1 s2
      helper (z : sexps)
    helper [s] =
      return s
    helper [] = error "impossible"

traceWith s a = trace (s ++ ": " ++ pretty a) a

optimiseKernel :: Interference.Graph VName -> SegOp lvl KernelsMem -> ReuseAllocsM (SegOp lvl KernelsMem)
optimiseKernel graph segop = do
  let allocs = traceWith "allocs" $ getAllocsSegOp segop
      (colorspaces, coloring) = GreedyColoring.colorGraph (traceWith "spacemap" $ fmap snd allocs) $ traceWith "graph" graph
  maxes <- mapM (maxSubExp . Set.map (fst . (allocs !) . traceWith "look up")) $ Map.elems $ traceWith "inverted coloring" $ invertMap $ traceWith "coloring" coloring
  -- assert (length maxes == Map.size colorspaces)
  (colors, stms) <- collectStms $ mapM (\(i, x) -> letSubExp "color" $ Op $ Alloc x $ colorspaces ! i) $ zip [0 ..] $ traceWith "maxes" maxes
  let segop' = setAllocsSegOp (traceWith "mapping" (fmap (colors !!) coloring)) segop
  return $ case segop' of
    SegMap lvl sp tps body -> SegMap lvl sp tps $ body {kernelBodyStms = stms <> kernelBodyStms body}
    _ -> undefined

onKernels :: (SegOp SegLevel KernelsMem -> ReuseAllocsM (SegOp SegLevel KernelsMem)) -> Stms KernelsMem -> ReuseAllocsM (Stms KernelsMem)
onKernels f stms =
  mapM helper stms
  where
    -- helper :: (LocalScope KernelsMem m, MonadFreshNames m) => Stm KernelsMem -> m (Stm KernelsMem)
    helper stm@Let {stmExp = Op (Inner (SegOp segop))} =
      inScopeOf stm $ do
        exp' <- f segop
        return $ stm {stmExp = Op $ Inner $ SegOp exp'}
    helper stm@Let {stmExp = If c then_body else_body dec} =
      inScopeOf stm $ do
        then_body_stms <- f `onKernels` (bodyStms then_body)
        else_body_stms <- f `onKernels` (bodyStms else_body)
        return $
          stm
            { stmExp =
                If
                  c
                  (then_body {bodyStms = then_body_stms})
                  (else_body {bodyStms = else_body_stms})
                  dec
            }
    helper stm@Let {stmExp = DoLoop ctx vals form body} =
      inScopeOf stm $ do
        bodyStms <- f `onKernels` bodyStms body
        return $ stm {stmExp = DoLoop ctx vals form (body {bodyStms = bodyStms})}
    helper stm =
      inScopeOf stm $ return stm

optimise :: Pass KernelsMem KernelsMem
optimise =
  Pass "reuse allocations" "reuse allocations" $ \prog ->
    let (lumap, _) = LastUse.analyseProg prog
        (_, _, graph) =
          foldMap (\f -> runReader (Interference.analyseKernels lumap (bodyStms $ funDefBody f)) $ scopeOf f) $
            progFuns prog
     in Pass.intraproceduralTransformation (onStms graph) $ trace ("optimise graph: " ++ pretty graph) prog
  where
    onStms :: Interference.Graph VName -> Scope KernelsMem -> Stms KernelsMem -> PassM (Stms KernelsMem)
    onStms graph scope stms = do
      let m = localScope scope $ optimiseKernel graph `onKernels` stms
      res <- fmap fst $ modifyNameSource $ runState (runBinderT m mempty)
      trace ("res:\n" ++ pretty res ++ "\n") $ return res
