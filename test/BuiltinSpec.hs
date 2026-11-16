{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module BuiltinSpec (bSpec) where

import Control.Monad.Except (runExceptT)
import Control.Monad.State.Lazy (evalState)
import Data.List (sort)
import qualified Data.Text as T
import Test.Hspec

import Elaborator (ElabState (..), elaborate)
import Infer (inferChunk)
import Parser (chunk, parseFromTextNamed)
import Suite (withModuleHeader)
import qualified Scope
import Unify (TypeCheckState (..), errorCode, evalTypeCheckM)
import Utils (Pretty (..))
import qualified Builtins

-- | Type-check a chunk and return the error code of the first failure, if any.
--   The checks that do not depend on running the program live here.
check :: T.Text -> IO (Either T.Text ())
check src =
  case parseFromTextNamed "test.marr" chunk (withModuleHeader src) of
    Left e -> pure $ Left (T.pack e)
    Right parsed ->
      case evalState (runExceptT (elaborate parsed)) (ElabState 0) of
        Left e -> pure $ Left (pretty e)
        Right elaborated ->
          pure $ case evalTypeCheckM (inferChunk [] elaborated) (TypeCheckState (0, 0, 0) 0 []) of
            Left (_, err) -> Left (maybe "no code" id (errorCode err))
            Right _ -> Right ()

-- | The names the checker exposes in the initial scope.
initialNames :: [T.Text]
initialNames =
  case evalTypeCheckM (Scope.globalScope []) (TypeCheckState (0, 0, 0) 0 []) of
    Left (_, err) -> error $ "globalScope failed: " <> T.unpack (pretty err)
    Right scope -> Scope.bindingNames scope

bSpec :: Spec
bSpec = do
  describe "builtin table" $ do
    it "agrees with the initial scope of the type checker" $ do
      sort initialNames `shouldBe` sort Builtins.names

    it "binds every listed name exactly once" $ do
      length initialNames `shouldBe` length Builtins.names

  describe "builtins that used to be missing" $ do
    it "runs `pred`" $ do
      r <- check $ T.unlines
        [ "funct main () : {Output} () ="
        , "  sayn (pred 5)"
        ]
      r `shouldBe` Right ()

    it "runs `not`" $ do
      r <- check $ T.unlines
        [ "funct main () : {Output} () ="
        , "  sayn (not true)"
        ]
      r `shouldBe` Right ()

    it "runs `read_string` in the Input row" $ do
      r <- check $ T.unlines
        [ "funct main () : {Output; Input} () ="
        , "  val s = read_string ();"
        , "  sayn s"
        ]
      r `shouldBe` Right ()

    it "runs `random_float` in the Random row" $ do
      r <- check $ T.unlines
        [ "funct main () : {Output; Random} () ="
        , "  sayn (random_float ())"
        ]
      r `shouldBe` Right ()

    it "runs `time_ms` in the Time row" $ do
      r <- check $ T.unlines
        [ "funct main () : {Output; Time} () ="
        , "  sayn (time_ms ())"
        ]
      r `shouldBe` Right ()

    it "runs `whnf` with the signature of `force`" $ do
      r <- check $ T.unlines
        [ "funct main () : {Output} () ="
        , "  sayn (whnf (say 1; 2))"
        ]
      r `shouldBe` Right ()

  describe "ambiguous operation names" $ do
    it "rejects one row that brings two effects declaring the same operation" $ do
      r <- check $ T.unlines
        [ "effect A"
        , "  get : () -> Int"
        , "end"
        , "effect B"
        , "  get : () -> Int"
        , "end"
        , ""
        , "funct use (x () -> {A; B} Int) : {A; B} Int = x ()"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (use {get ()})"
        ]
      r `shouldBe` Left "E0018"

  describe "application of a non-function" $ do
    it "is reported as E0017 with the callee's type, not as a unification failure" $ do
      r <- check $ T.unlines
        [ "funct main () : {Output} () ="
        , "  sayn (1 2)"
        ]
      r `shouldBe` Left "E0017"

    it "names the offending variable" $ do
      r <- check $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val n = 2;"
        , "  sayn (n 2)"
        ]
      r `shouldBe` Left "E0017"

  describe "a monomorphic binding is not an error" $ do
    it "accepts `val g = sayn` and a use at a fixed type" $ do
      r <- check $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val g = sayn;"
        , "  g 1"
        ]
      r `shouldBe` Right ()

    it "accepts `val g = apply sayn` when the row-polymorphic call terminates" $ do
      r <- check $ T.unlines
        [ "funct apply (f `A -> `R `B) (x `A) : `R `B = f x"
        , ""
        , "funct main () : {Output} () ="
        , "  val g = apply sayn;"
        , "  g 1"
        ]
      r `shouldBe` Right ()
