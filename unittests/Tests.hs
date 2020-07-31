module Main (main) where

import qualified Futhark.Analysis.InterferenceTests
import Test.Tasty

allTests :: TestTree
allTests =
  testGroup
    ""
    [ Futhark.Analysis.InterferenceTests.tests
    ]

main :: IO ()
main = defaultMain allTests
