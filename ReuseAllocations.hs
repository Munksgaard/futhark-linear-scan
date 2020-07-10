{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeFamilies #-}

module ReuseAllocations (reuseAllocationsPass) where

import Control.Monad.Reader
import Data.Function ((&))
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import Data.Tuple (swap)
import Debug.Trace
import Futhark.Analysis.Alias (analyseStms)
import Futhark.IR.KernelsMem
import Futhark.Pass (Pass (..), intraproceduralTransformation)
import Futhark.Util.Pretty
import LastUse (applyAliases, lastUses)

type Frees = [(VName, SubExp)]

type Allocs = [(VName, SubExp)]

type LastUses = [(Int, VName)]

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
      return $ runReader (optimiseStms stms) scope

optimiseStms :: Stms KernelsMem -> ReuseAllocsM (Stms KernelsMem)
optimiseStms stms0 =
  localScope (scopeOf stms0) $ do
    let (_, (aliases, _)) = analyseStms Map.empty stms0
        last_uses =
          lastUses stms0
            & applyAliases aliases
            & Map.toList
            & fmap swap
            & List.sort
            & traceWith "last_uses?"
    (allocs, frees, last_uses', stms') <- foldM walkStatements ([], [], last_uses, []) $ (\stms -> trace ("stms:\n" ++ unlines (fmap pretty stms)) stms) $ zip [0 ..] $ stmsToList stms0
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

walkStatements :: (Allocs, Frees, LastUses, [Stm KernelsMem]) -> (Int, Stm KernelsMem) -> ReuseAllocsM (Allocs, Frees, LastUses, [Stm KernelsMem])
walkStatements (allocs, frees, last_uses, acc) (i, stm@Let {stmExp = Op (Alloc sexp _), stmPattern = Pattern {patternValueElements = [PatElem {patElemName}]}}) =
  localScope (scopeOf stm) $ do
    case lookup (traceWith (show i ++ " lookup") sexp) $ map swap frees of
      Just mem ->
        return $ trace (show i ++ " found a result: " ++ show mem) (allocs, frees, last_uses, stm {stmExp = BasicOp $ SubExp $ Var mem} : acc)
      Nothing ->
        return ((patElemName, sexp) : allocs, frees, last_uses, stm : acc)
walkStatements (allocs, frees, last_uses, acc) (i, stm) =
  localScope (scopeOf stm) $ do
    let (last_uses_in_this_stm, last_uses') = List.span ((== i) . fst) last_uses
    new_frees <- catMaybes <$> mapM (memAndSize allocs . snd) last_uses_in_this_stm
    return $ trace (show i ++ " adding new frees: " ++ show new_frees) (allocs, new_frees ++ frees, last_uses', stm : acc)

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
