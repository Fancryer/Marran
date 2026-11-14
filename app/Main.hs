{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module Main (main) where

import System.Environment (getArgs, withArgs)
import System.Exit (exitFailure)
import Benchmark (runBenchmarks, runEdgeSweepBenchmarks)
import Suite (runSuite, runProgram)
import Control.Monad (unless)

main :: IO ()
main = getArgs >>= \case
  []                     -> runSuite >>= \ok -> unless ok exitFailure
  ("--bench":rest)       -> withArgs (criterionArgs rest) runBenchmarks
  ("--bench-edges":rest) -> withArgs (criterionArgs rest) runEdgeSweepBenchmarks
  ["--run", name] -> runProgram name >>= \case
    Left err -> putStrLn err >> exitFailure
    Right out -> putStr out >> putStrLn "(done)"
  _ -> putStrLn $ unlines
    [ "usage: marran-exe               run the bundled example programs"
    , "       marran-exe --bench [--csv FILE]        the benchmark graphs"
    , "       marran-exe --bench-edges [--csv FILE]  the wider edge sweep"
    , "       marran-exe --run <name>  run one program from app/marr"
    ]

-- | Criterion accepts @--csv@ only as its first argument.
criterionArgs :: [String] -> [String]
criterionArgs args = case break (== "--csv") args of
  (before, "--csv" : file : after) -> "--csv" : file : before <> after
  _                                -> args
