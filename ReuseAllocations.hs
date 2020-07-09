{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeFamilies #-}

module ReuseAllocations (memAndSize) where

-- import Futhark.IR.Aliases (CanBeAliased)

import Control.Monad (foldM)
-- import Data.Map (Map)

import Data.Function ((&))
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe (catMaybes, mapMaybe)
import Data.Tuple (swap)
import Debug.Trace
import Futhark.Analysis.Alias (analyseStms)
import qualified Futhark.IR.Aliases as Aliases
import Futhark.IR.Aliases (Aliases)
import Futhark.IR.Kernels (HostOp (..))
import Futhark.IR.KernelsMem (KernelsMem)
import Futhark.IR.Mem (Mem, MemBind (..), MemInfo (..), MemOp (Alloc))
import qualified Futhark.IR.Mem as Mem
import Futhark.IR.Prop (HasScope, Scope, inScopeOf)
import Futhark.IR.Syntax
import Futhark.MonadFreshNames
import Futhark.Pass (Pass (..), PassM, intraproceduralTransformation)
import Futhark.TypeCheck
import LastUse (applyAliases, lastUses)

type Frees = [(VName, SubExp)]

-- type Frees = [(Int, VName)]

type Allocs = [(VName, SubExp)]

type LastUses = [(Int, VName)]

type Blab op inner lore = (Op lore ~ MemOp (HostOp op inner), Mem lore)

reuseAllocationsPass :: Pass KernelsMem KernelsMem
reuseAllocationsPass =
  Pass
    { passName = "reuse allocations",
      passDescription = "reuse allocations in all functions",
      passFunction = intraproceduralTransformation reuseAllocations
    }

reuseAllocations :: MonadFreshNames m => Scope KernelsMem -> Stms KernelsMem -> m (Stms KernelsMem)
reuseAllocations scope stms0 = do
  let (_, (aliases, _)) = analyseStms Map.empty stms0
  let last_uses =
        lastUses stms0
          & applyAliases aliases
          & Map.toList
          & fmap swap
          & List.sort
  (allocs, frees, last_uses', stms') <- foldM walkStatements ([], [], last_uses, []) $ zip [0 ..] $ stmsToList stms0
  let stms = stmsFromList $ reverse stms'
  return $
    trace
      ( unlines
          [ "allocs:",
            show allocs,
            "frees:",
            show frees,
            "last_uses:",
            show last_uses'
          ]
      )
      stms

walkStatements :: (MonadFreshNames m) => (Allocs, Frees, LastUses, [Stm KernelsMem]) -> (Int, Stm KernelsMem) -> m (Allocs, Frees, LastUses, [Stm KernelsMem])
walkStatements (allocs, frees, last_uses, acc) (_, stm@Let {stmExp = Op (Alloc sexp _), stmPattern = Pattern {patternValueElements = [PatElem {patElemName}]}}) =
  -- case lookup sexp frees of
  --   Just mem ->
  --     (allocs, frees, last_uses, stm {stmExp = BasicOp $ SubExp $ Var mem} : acc)
  --   Nothing ->
  return ((patElemName, sexp) : allocs, frees, last_uses, stm : acc)
walkStatements (allocs, frees, last_uses, acc) (i, stm) = do
  let (last_uses_in_this_stm, last_uses') = List.span ((== i) . fst) last_uses
  new_frees <- catMaybes <$> mapM (memAndSize allocs . snd) last_uses_in_this_stm
  return (allocs, new_frees ++ frees, last_uses', stm : acc)

memAndSize :: MonadFreshNames m => Allocs -> VName -> m (Maybe (VName, SubExp))
memAndSize allocs vname = do
  summary <- Mem.lookupMemInfo vname
  case summary of
    MemArray _ _ _ (ArrayIn mem _) ->
      return $ List.find ((== mem) . fst) allocs
    _ ->
      return $ Nothing
