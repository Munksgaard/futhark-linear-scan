{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Futhark.Analysis.InterferenceTests
  ( tests,
  )
where

import Control.Category ((>>>))
import qualified Data.Set as Set
import qualified Futhark.Analysis.Interference as Interference
import Futhark.Compiler
import Futhark.IR.KernelsMem (KernelsMem)
import Futhark.IR.SOACS
import Futhark.Optimise.CSE
import qualified Futhark.Pass.ExplicitAllocations.Kernels as Kernels
import Futhark.Pass.Simplify
import Futhark.Passes
import Futhark.Pipeline
import System.IO.Temp
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "InterferenceTests"
    [psumTest]

pipeline :: Pipeline SOACS KernelsMem
pipeline =
  kernelsPipeline
    >>> onePass Kernels.explicitAllocations
    >>> passes
      [ simplifyKernelsMem,
        performCSE False
      ]

psumTest :: TestTree
psumTest =
  testCase "psum.fut" $ do
    fp <- writeSystemTempFile "psum.fut" "let psum = scan (+) (0: i32) let main (xss: [][]i32) = #[incremental_flattening(only_intra)] map (psum >-> psum >-> psum) xss"
    prog <- runFutharkM (runPipelineOnProgram newFutharkConfig pipeline fp) NotVerbose
    case prog of
      Right prog' ->
        case Set.toList $ Interference.analyse prog' of
          [(mem1, mem2), (mem2', mem3)] -> do
            assertEqual "Some mems" mem2 mem2'
            assertBool "Only two elements" (mem1 /= mem3)
            assertBool "Only two elements" (mem1 /= mem2)
            assertBool "Only two elements" (mem2 /= mem3)
          _ ->
            assertFailure "Interference graph invalid"
      Left _ ->
        assertFailure "Could not compile"
