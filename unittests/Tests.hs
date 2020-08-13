module Main (main) where

import qualified Futhark.Analysis.InterferenceTests
import qualified Futhark.Optimise.ReuseAllocations.GreedyColoringTests
import Test.Tasty

allTests :: TestTree
allTests =
  testGroup
    ""
    [ Futhark.Analysis.InterferenceTests.tests,
      Futhark.Optimise.ReuseAllocations.GreedyColoringTests.tests
    ]

main :: IO ()
main = defaultMain allTests
