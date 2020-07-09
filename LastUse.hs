{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}

module LastUse (lastUseAction, lastUses, applyAliases) where

import Control.Monad.IO.Class
import Data.Foldable
import Data.Function ((&))
import qualified Data.Map as Map
import Data.Map (Map, (!?))
import Futhark.Analysis.Alias (analyseStms)
import Futhark.IR.Aliases (CanBeAliased)
import Futhark.IR.KernelsMem (freeIn)
import Futhark.IR.Prop (ASTLore)
import Futhark.IR.Prop.Names (FreeIn, Names, namesToList)
import Futhark.IR.Syntax
import Futhark.Pipeline

applyAliases :: Map VName Names -> Map VName Int -> Map VName Int
applyAliases aliases last_uses =
  Map.foldrWithKey helper last_uses last_uses
  where
    helper :: VName -> Int -> Map VName Int -> Map VName Int
    helper vname0 line_num m0 =
      foldr
        (\vname m -> Map.insertWith max vname line_num m)
        m0
        (maybe [] namesToList $ aliases !? vname0)

class LastUses a where
  lastUses :: a -> Map VName Int

instance ASTLore lore => LastUses (Body lore) where
  lastUses (Body {bodyStms, bodyResult}) =
    let last_use_map =
          zip (toList bodyStms) [0 ..]
            & reverse
            & foldr addToLastUseMap Map.empty
     in foldr Map.delete last_use_map (namesToList $ freeIn bodyResult)
    where
      addToLastUseMap :: FreeIn a => (a, Int) -> Map VName Int -> Map VName Int
      addToLastUseMap (stm, i) m =
        freeIn stm
          & namesToList
          & foldr (`Map.insert` i) m

instance ASTLore lore => LastUses (Stms lore) where
  lastUses stms =
    zip (toList stms) [0 ..]
      & reverse
      & foldr addToLastUseMap Map.empty
    where
      addToLastUseMap :: FreeIn a => (a, Int) -> Map VName Int -> Map VName Int
      addToLastUseMap (stm, i) m =
        freeIn stm
          & namesToList
          & foldr (`Map.insert` i) m

lastUseFun :: (ASTLore lore, CanBeAliased (Op lore)) => FunDef lore -> FutharkM ()
lastUseFun
  FunDef
    { funDefName,
      funDefParams,
      funDefBody = body@Body {bodyDec, bodyStms, bodyResult}
    } = do
    liftIO $ putStrLn $ "Analyzing " ++ show funDefName
    liftIO $
      putStrLn $
        unwords
          [ "Params:",
            show funDefParams,
            "\nBodyDec:",
            show bodyDec,
            "\nBodyResult:",
            show bodyResult
          ]

    let (stms, (aliases, _)) = analyseStms Map.empty bodyStms

    zip (toList stms) [0 :: Int ..]
      & fmap (\(stm, i) -> show i ++ ": " ++ show stm)
      & unlines
      & putStrLn
      & liftIO

    pretty aliases
      & putStrLn
      & liftIO

    zip (toList bodyStms) [0 :: Int ..]
      & fmap (\(stm, i) -> show i ++ ": " ++ pretty stm)
      & unlines
      & putStrLn
      & liftIO

    let last_use_map = lastUses body

    last_use_map
      & Map.toList
      & fmap (\(vname, line_num) -> pretty vname ++ ": " ++ show line_num)
      & unlines
      & putStrLn
      & liftIO

    applyAliases aliases last_use_map
      & Map.toList
      & fmap (\(vname, line_num) -> pretty vname ++ ": " ++ show line_num)
      & unlines
      & putStrLn
      & liftIO

lastUseProg :: (ASTLore lore, CanBeAliased (Op lore)) => Prog lore -> FutharkM ()
lastUseProg (Prog _ funs) = mapM_ lastUseFun funs

lastUseAction :: (ASTLore lore, CanBeAliased (Op lore)) => Action lore
lastUseAction =
  Action
    { actionName = "memory allocation lastUse analysis",
      actionDescription = "Perform lastUse analysis on memory allocations",
      actionProcedure = lastUseProg
    }
