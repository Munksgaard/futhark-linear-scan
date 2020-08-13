module Futhark.Optimise.ReuseAllocations.GreedyColoringTests
  ( tests,
  )
where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Futhark.Optimise.ReuseAllocations.GreedyColoring as GreedyColoring
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "GreedyColoringTests"
    [psumTest]

psumTest :: TestTree
psumTest =
  testCase "psumTest" $ do
    assertEqual
      "Color simple 1-2-3 using two colors"
      [(1 :: Int, 0), (2, 1), (3, 0)]
      $ Map.toList $ GreedyColoring.colorGraph $ Set.fromList [(1, 2), (2, 3)]
