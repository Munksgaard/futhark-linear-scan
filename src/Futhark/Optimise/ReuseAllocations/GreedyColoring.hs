module Futhark.Optimise.ReuseAllocations.GreedyColoring (colorGraph, Coloring) where

import Data.Function ((&))
import qualified Data.Map as Map
import Data.Map (Map, (!), (!?))
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Futhark.Analysis.Interference as Interference

type Coloring a = Map a Int

type Neighbors a = Map a (Set a)

neighbors :: Ord a => Interference.Graph a -> Neighbors a
neighbors graph =
  Set.foldr
    ( \(x, y) acc ->
        acc
          & Map.insertWith Set.union x (Set.singleton y)
          & Map.insertWith Set.union y (Set.singleton x)
    )
    Map.empty
    graph

firstAvailable :: Set Int -> Int -> Int
firstAvailable xs i =
  if i `Set.member` xs
    then firstAvailable xs $ i + 1
    else i

colorNode :: Ord a => Neighbors a -> a -> Coloring a -> Coloring a
colorNode nbs x coloring =
  let nb_colors = foldMap (maybe Set.empty Set.singleton . (coloring !?)) $ nbs ! x
   in Map.insert x (firstAvailable nb_colors 0) coloring

colorGraph :: Ord a => Interference.Graph a -> Coloring a
colorGraph graph =
  let nodes = Set.foldr (\(x, y) acc -> Set.insert x $ Set.insert y acc) Set.empty graph
      nbs = neighbors graph
   in Set.foldr (colorNode nbs) Map.empty nodes
