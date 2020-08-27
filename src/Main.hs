module Main (main) where

import Control.Category ((>>>))
import Futhark.Actions (printAction)
import Futhark.Compiler
  ( newFutharkConfig,
    runCompilerOnProgram,
  )
import Futhark.IR.KernelsMem (KernelsMem)
import Futhark.IR.SOACS
import Futhark.Optimise.CSE
import qualified Futhark.Optimise.ReuseAllocations as ReuseAllocations
import qualified Futhark.Pass.ExplicitAllocations.Kernels as Kernels
import Futhark.Pass.Simplify
import Futhark.Passes (kernelsPipeline)
import Futhark.Pipeline
import GHC.IO.Encoding (setLocaleEncoding)
import System.Environment (getArgs)
import System.IO

pipeline :: Pipeline SOACS KernelsMem
pipeline =
  kernelsPipeline
    >>> onePass Kernels.explicitAllocations
    >>> passes
      [ simplifyKernelsMem,
        performCSE False,
        ReuseAllocations.optimise,
        simplifyKernelsMem
      ]

-- action :: Action KernelsMem
-- action =
--   Action
--     { actionName = "memory interference graph",
--       actionDescription = "Analyse interference",
--       actionProcedure = helper
--     }
--   where
--     helper :: Prog KernelsMem -> FutharkM ()
--     helper prog = do
--       let (lumap, _) = LastUse.analyseProg prog
--       liftIO $ putStrLn ("lumap: " ++ pretty lumap ++ "\n")
--       let (inuse, lastused, graph) = foldMap (\f -> runReader (Interference.analyseKernels lumap (bodyStms $ funDefBody f)) $ scopeOf f) $ progFuns prog
--       liftIO $ putStrLn ("inuse: " ++ pretty inuse ++ "\n")
--       liftIO $ putStrLn ("lastused: " ++ pretty lastused ++ "\n")
--       liftIO $ putStrLn ("graph: " ++ pretty graph ++ "\n")

--       let coloring = GreedyColoring.colorGraph graph

--       liftIO $ putStrLn ("coloring: " ++ pretty coloring ++ "\n")

-- -- prog' <- ReuseAllocations.optimise prog

-- -- liftIO $ putStrLn ("prog':\n" ++ pretty prog' ++ "\n")

main :: IO ()
main = do
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
  setLocaleEncoding utf8
  args <- getArgs

  runCompilerOnProgram
    newFutharkConfig
    pipeline
    printAction
    (head args)
