module Main where

import Test.Hspec
import UnifySpec (uSpec)
import UnifyPropertySpec (uPropSpec)
import FreezePropertySpec (fPropSpec)
import GeneralizeSpec (gSpec)
import FreezeSpec (fSpec)
import ExamplesSpec (eSpec)
import SpanSpec (spanSpec)
import DiagnosticSpec (dSpec)
import ParserSpec (pSpec)
import SuggestSpec (sSpec)
import BuiltinSpec (bSpec)
import BenchmarkSpec (benchSpec)

main :: IO ()
main = hspec $ do
  describe "unification" uSpec
  describe "unification properties" uPropSpec
  describe "freezing properties" fPropSpec
  describe "generalisation" gSpec
  describe "freezing" fSpec
  describe "examples" eSpec
  describe "spans" spanSpec
  describe "diagnostics" dSpec
  describe "syntax" pSpec
  describe "suggestions" sSpec
  describe "builtins" bSpec
  describe "benchmark graphs" benchSpec
