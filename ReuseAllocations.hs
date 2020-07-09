{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeFamilies #-}

module ReuseAllocations (reuseAllocationsPass) where

-- import Futhark.IR.Aliases (CanBeAliased)

import Control.Monad (foldM)
-- import Data.Map (Map)

import Data.Function ((&))
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.Tuple (swap)
import Debug.Trace
import Futhark.Analysis.Alias (analyseStms)
import qualified Futhark.IR.Aliases as Aliases
import Futhark.IR.Aliases (Aliases)
import Futhark.IR.Kernels (HostOp (..))
import Futhark.IR.Mem (Mem, MemBind (..), MemInfo (..), MemOp (Alloc))
import qualified Futhark.IR.Mem as Mem
import Futhark.IR.Prop (Scope, inScopeOf)
import Futhark.IR.Syntax
import Futhark.Pass (Pass (..), PassM, intraproceduralTransformation)
import LastUse (applyAliases, lastUses)

type Frees = [(VName, SubExp)]

-- type Frees = [(Int, VName)]

type Allocs = [(VName, SubExp)]

type LastUses = [(Int, VName)]

type Blab op inner lore = (Op lore ~ MemOp (HostOp op inner), Mem lore)

reuseAllocationsPass :: Blab op inner lore => Pass lore lore
reuseAllocationsPass =
  Pass
    { passName = "reuse allocations",
      passDescription = "reuse allocations in all functions",
      passFunction = intraproceduralTransformation reuseAllocations
    }

reuseAllocations :: Blab op inner lore => Scope lore -> Stms lore -> PassM (Stms lore)
reuseAllocations scope stms0 =
  inScopeOf scope $ do
    let (_, (aliases, _)) = analyseStms Map.empty stms0
    let last_uses =
          lastUses stms0
            & applyAliases aliases
            & Map.toList
            & fmap swap
            & List.sort
    let (allocs, frees, last_uses', stms') = foldl walkStatements ([], [], last_uses, []) $ zip [0 ..] $ stmsToList stms0
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

walkStatements :: Blab op inner lore => (Allocs, Frees, LastUses, [Stm lore]) -> (Int, Stm lore) -> (Allocs, Frees, LastUses, [Stm lore])
walkStatements (allocs, frees, last_uses, acc) (_, stm@Let {stmExp = Op (Alloc sexp _), stmPattern = Pattern {patternValueElements = [PatElem {patElemName}]}}) =
  -- case lookup sexp frees of
  --   Just mem ->
  --     (allocs, frees, last_uses, stm {stmExp = BasicOp $ SubExp $ Var mem} : acc)
  --   Nothing ->
  ((patElemName, sexp) : allocs, frees, last_uses, stm : acc)
walkStatements (allocs, frees, last_uses, acc) (i, stm) =
  let (last_uses_in_this_stm, last_uses') = List.span ((== i) . fst) last_uses
      new_frees = mapMaybe (memAndSize allocs . snd) last_uses_in_this_stm
   in (allocs, new_frees ++ frees, last_uses', stm : acc)

memAndSize :: Allocs -> VName -> Maybe (VName, SubExp)
memAndSize allocs vname = do
  summary <- Mem.lookupMemInfo vname
  case summary of
    MemArray _ _ _ (ArrayIn mem _) ->
      List.find ((== mem) . fst) allocs
    _ ->
      Nothing

-- reuseAllocations :: (Op lore ~ MemOp (HostOp op inner), Mem lore) => Scope lore -> Stms lore -> PassM (Stms lore)
-- reuseAllocations _ stms0 = do
--   let (stms, (aliases, _)) = analyseStms Map.empty stms0
--   let last_uses = List.sort $ fmap swap $ Map.toList $ applyAliases aliases $ lastUses stms
--   (_, allocs, _, stms') <- foldM helper (last_uses, [], [], []) $ zip [0 ..] $ stmsToList $ trace (unwords ["last_uses: ", show last_uses]) stms
--   return $ stmsFromList $ fmap Aliases.removeStmAliases $ trace (unlines ([" allocs: ", show allocs])) $ reverse stms'
--   where
--     helper ::
--       (Op lore ~ MemOp inner, Mem lore) =>
--       (LastUses, AllocList, FreeList, [Stm (Aliases lore)]) ->
--       (Int, Stm (Aliases lore)) ->
--       PassM (LastUses, AllocList, FreeList, [Stm (Aliases lore)])
--     helper (last_uses, allocs, frees, acc) (i, stm) = do
--       let (last_uses_on_this_line, last_uses') = List.span (\(i', _) -> i' == i) last_uses
--       let (frees', allocs') = List.partition (flip elem (fmap snd last_uses_on_this_line) . fst) allocs
--       trace (unwords ["line ", show i, ", stm: ", show stm, ", stmAux: ", show $ stmAux stm, ", freed: ", show last_uses_on_this_line, ", frees': ", show frees', ", allocs': ", show allocs', "\n"]) $ case stm of
--         Let
--           { stmPattern = Pattern {patternValueElements = [PatElem {patElemName}]},
--             stmExp = Op (Alloc sexp _space)
--           } ->
--             return (last_uses', (patElemName, sexp) : allocs', frees' ++ frees, stm : acc)
--         _ ->
--           return (last_uses', allocs', frees' ++ frees, stm : acc)
