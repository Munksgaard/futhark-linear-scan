{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeFamilies #-}

module Futhark.Analysis.Interference (interference, analyse) where

import Control.Monad.Reader
import Data.Foldable (foldlM, toList)
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

type Frees = [(VName, SubExp)]

type Allocs = [(VName, SubExp)]

type InterferenceM = Reader (Scope KernelsMem)

traceWith s p a = trace (s ++ " (" ++ pretty p ++ "): " ++ pretty a) a

type Graph = Set (VName, VName)

insertEdge :: VName -> VName -> Graph -> Graph
insertEdge v1 v2 g
  | v1 == v2 = g
  | otherwise = Set.insert (min v1 v2, max v1 v2) g

cartesian :: Names -> Names -> Graph
cartesian ns1 ns2 =
  [(min x y, max x y) | x <- namesToList ns1, y <- namesToList ns2]
    & foldr (uncurry insertEdge) mempty

analyseStm :: LastUseMap -> InUse -> Stm KernelsMem -> InterferenceM (InUse, LastUsed, Graph)
analyseStm lumap inuse0 stm =
  inScopeOf stm $ do
    let pat_name = patElemName $ head $ patternValueElements $ stmPattern $ stm

    new_mems <-
      stmPattern stm
        & patternValueElements
        & mapM (memInfo . patElemName)
        <&> catMaybes

    -- `new_mems` should interfere with any mems inside the statement expression
    let inuse_inside = inuse0 <> namesFromList new_mems

    (inuse, lus, graph) <- case stmExp stm of
      If cse then_body else_body dec -> do
        -- (inuse_then, lus_then, g_then) <- analyseBody lumap then_body
        -- (inuse_else, lus_else, g_else) <- analyseBody lumap else_body
        -- let lus' = lus_then <> lus_else
        --     inuse' = (inuse_inside <> inuse1 <> inuse2) `namesSubtract` lus'
        --     g =
        --       graph <> g1 <> g2
        --         <> ((inuse1 <> lus1) `cartesian` (inuse0 `namesSubtract` (lus2 `namesSubtract` lus1)))
        --         <> ((inuse2 <> lus2) `cartesian` (inuse0 `namesSubtract` (lus1 `namesSubtract` lus2)))
        -- return $ trace (unwords ["If", pretty pat_name, "inuse':", pretty inuse', "lus:", pretty lus]) (inuse', lus, g)
        undefined
      Apply _ _ _ _ -> do
        -- let inuse' = inuse `namesSubtract` inuse0
        -- return $ traceWith "Apply" pat_name (inuse', lus0, graph)
        undefined
      BasicOp _ -> do
        -- let inuse' = inuse `namesSubtract` lus0
        -- return $ traceWith "BasicOp" pat_name (inuse', lus0, graph)
        return (mempty, mempty, mempty)
      DoLoop ctx vals form body -> do
        -- (inuse', lus, graph') <- analyseBody lumap body
        -- let lus' = lus <> lus0
        -- let graph'' = graph <> graph' <> inuse `cartesian` (inuse' <> lus')
        -- let inuse'' = inuse `namesSubtract` lus <> inuse'
        -- return $ traceWith "DoLoop" pat_name (inuse'', lus', graph'')
        return (mempty, mempty, mempty)
      -- let lus' = lus <> lus0
      -- let graph'' = graph <> graph' <> inuse `cartesian` (inuse' <> lus')
      -- let inuse'' = inuse `namesSubtract` lus <> inuse'
      -- return $ traceWith "SegMap" pat_name (inuse'', lus', graph'')
      -- return (inuse', lus, graph')
      Op (Inner (SegOp segop)) -> do
        analyseSegOp lumap inuse_inside segop
      Op (Inner (OtherOp _)) -> do
        undefined
      Op (Alloc _ _) -> do
        -- let inuse' = inuse `namesSubtract` lus0
        -- return $ traceWith "Alloc" pat_name (inuse', lus0, graph)
        return mempty

    last_use_mems <-
      Map.lookup pat_name lumap
        & fromMaybe mempty
        & namesToList
        & mapM memInfo
        <&> catMaybes
        <&> namesFromList
        <&> namesIntersection inuse_inside

    -- return (inuse `namesSubtract` last_use_mems, lus <> last_use_mems, graph <> (inuse `cartesian` inuse))
    return $
      trace
        ( unwords
            [ pretty pat_name,
              "last_use_mems:",
              pretty last_use_mems,
              "new_mems:",
              pretty new_mems,
              "inuse_inside:",
              pretty inuse_inside,
              "inuse:",
              pretty inuse,
              "lus:",
              pretty lus,
              "graph:",
              pretty graph
            ]
        )
        ( inuse_inside `namesSubtract` last_use_mems `namesSubtract` lus,
          lus <> last_use_mems,
          graph <> (inuse_inside `cartesian` (inuse_inside <> inuse <> lus <> last_use_mems))
        )

analyseKernelBody :: LastUseMap -> InUse -> KernelBody KernelsMem -> InterferenceM (InUse, LastUsed, Graph)
analyseKernelBody lumap inuse body = analyseStms lumap inuse $ kernelBodyStms body

analyseBody :: LastUseMap -> InUse -> Body KernelsMem -> InterferenceM (InUse, LastUsed, Graph)
analyseBody lumap inuse body = analyseStms lumap inuse $ bodyStms body

analyseStms :: LastUseMap -> InUse -> Stms KernelsMem -> InterferenceM (InUse, LastUsed, Graph)
analyseStms lumap inuse stms = do
  inScopeOf stms $ do
    foldM
      ( \(inuse, lus, graph) stm -> do
          (inuse', lus', graph') <- analyseStm lumap inuse stm
          return (inuse', lus' <> lus, graph' <> graph)
      )
      (inuse, mempty, mempty)
      $ stmsToList stms

analyseSegOp :: LastUseMap -> InUse -> SegOp lvl KernelsMem -> InterferenceM (InUse, LastUsed, Graph)
analyseSegOp lumap inuse (SegMap lvl _ tps body) =
  analyseKernelBody lumap inuse body
analyseSegOp lumap inuse (SegScan lvl _ binops tps body) =
  analyseKernelBody lumap inuse body
analyseSegOp _ _ _ = undefined

analyseKernels :: LastUseMap -> Stms KernelsMem -> InterferenceM (InUse, LastUsed, Graph)
analyseKernels lumap stms =
  (mconcat . toList) <$> mapM helper stms
  where
    helper :: Stm KernelsMem -> InterferenceM (InUse, LastUsed, Graph)
    helper stm@Let {stmExp = Op (Inner (SegOp segop))} =
      inScopeOf stm $ analyseSegOp lumap mempty segop
    helper stm@Let {stmExp = If _ then_body else_body _} =
      inScopeOf stm $ do
        res1 <- analyseKernels lumap (bodyStms then_body)
        res2 <- analyseKernels lumap (bodyStms else_body)
        return (res1 <> res2)
    helper stm@Let {stmExp = DoLoop _ _ _ body} =
      inScopeOf stm $
        analyseKernels lumap $ bodyStms body
    helper stm =
      inScopeOf stm $ return mempty

analyse :: Prog KernelsMem -> Graph
analyse prog =
  let (lumap, used) = LastUse.analyseProg prog
      (_, _, graph) = foldMap (\f -> runReader (analyseKernels lumap (bodyStms $ funDefBody f)) $ scopeOf f) $ progFuns prog
   in graph

interference :: Action KernelsMem
interference =
  Action
    { actionName = "memory interference graph",
      actionDescription = "Analyse interference",
      actionProcedure = helper
    }
  where
    helper :: Prog KernelsMem -> FutharkM ()
    helper prog = do
      let (lumap, used) = LastUse.analyseProg prog
      liftIO $ putStrLn ("lumap: " ++ pretty lumap ++ "\n")
      let (inuse, lastused, graph) = foldMap (\f -> runReader (analyseKernels lumap (bodyStms $ funDefBody f)) $ scopeOf f) $ progFuns prog
      liftIO $ putStrLn ("inuse: " ++ pretty inuse ++ "\n")
      liftIO $ putStrLn ("lastused: " ++ pretty lastused ++ "\n")
      liftIO $ putStrLn ("graph: " ++ pretty graph ++ "\n")

memAndSize :: Allocs -> VName -> InterferenceM (Maybe (VName, SubExp))
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

memInfo :: VName -> InterferenceM (Maybe (VName))
memInfo vname = do
  summary <- asksScope (fmap nameInfoToMemInfo . Map.lookup vname)
  case summary of
    Just (MemArray _ _ _ (ArrayIn mem _)) ->
      return $ Just mem
    _ ->
      return Nothing
