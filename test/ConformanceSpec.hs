{-# LANGUAGE OverloadedStrings #-}

-- | Conformance suite v1: one rule per language rule.
--
--   Each rule carries at least one full module that must parse and one that
--   must not.  The suite is about the surface only: it never elaborates or
--   type-checks, so a positive case may mention a type the checker would later
--   reject.  The rule identifiers and titles are also written to
--   @test/conformance/manifest.tsv@; a test keeps the two lists in step.
module ConformanceSpec (conformanceSpec) where

import Control.Monad (forM_)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (doesFileExist)
import Test.Hspec

import Parser (chunk, parseFromTextNamed)

-- | One frozen rule: an identifier, a short title, and the programs that the
--   rule accepts and rejects.
data Rule = Rule
  { ruleId :: T.Text
  , ruleTitle :: T.Text
  , ruleAccepted :: [T.Text]
  , ruleRejected :: [T.Text]
  }

-- | A rule with one accepted and one rejected program.
rule :: T.Text -> T.Text -> T.Text -> T.Text -> Rule
rule ident title accepted rejected = Rule ident title [accepted] [rejected]

-- | Every rule of the frozen surface.
rules :: [Rule]
rules = [
    rule "SYN-001" "a file starts with a module header"
      (T.unlines [
          "module Main"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "funct main () : () = ()"
        ]),

    rule "SYN-002" "an export list is whitespace-separated"
      (T.unlines [
          "module Lib [funct f funct g as h]"
        , "import @native"
        , ""
        , "funct f () : () = ()"
        , "funct g () : () = ()"
        ])
      (T.unlines [
          "module Lib [funct f, funct g]"
        , "import @native"
        , ""
        , "funct f () : () = ()"
        ]),

    rule "SYN-003" "an import directory has a bracketed unit list"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "import 'lib/'"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-004" "a type alias has an equals sign and a type"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "type PairOf[T] = (T, T)"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "type PairOf[T]"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-005" "an enum declares at least one case"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "enum Colour | Red | Green"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "enum Colour"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-006" "an enum field is parenthesised and qualified"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "enum Maybe[T] | None | Some (val x : T)"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "enum Maybe[T] | None | Some val x : T"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-007" "an effect ends with end"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "effect Math"
        , "  add : Int -> Int -> Int;"
        , "  sub : Int -> Int -> Int;"
        , "end"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "effect Math"
        , "  add : Int -> Int -> Int"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-008" "an effect may declare no operations"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "effect Empty end"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "effect Empty"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-009" "a row alias has an equals sign"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "row Console = {Output; Input}"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "row Console {Output; Input}"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-010" "function arguments are separate parenthesised groups"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct add (x Int) (y Int) : Int = + x y"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct add (x Int, y Int) : Int = + x y"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-011" "the colon before a parameter type is optional"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct add (x Int) (y : Int) : Int = + x y"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct add (x :: Int) : Int = x"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-012" "a result row precedes the result type"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct f () : {Output} Int = 1"
        , ""
        , "funct main () : {Output} () = sayn 1"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct f () : Int {Output} = 1"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-013" "a type application is written with a hash"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "type Box[T] = T"
        , ""
        , "funct main () : Box#[Int] = 1"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "type Box[T] = T"
        , ""
        , "funct main () : Box[Int] = 1"
        ]),

    rule "SYN-014" "an array type is a bare bracket"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : [Int] = [1, 2]"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : [Int = [1]"
        ]),

    rule "SYN-015" "type parameters are whitespace-separated"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "type Map[K V] = (K, V)"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "type Map[K, V] = (K, V)"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-016" "effect parameters are braced and whitespace-separated"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct map[T]{E | R} (f T -> {E | `R} T) (xs [T]) : [T] = xs"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct map[T]{E, R} (x T) : T = x"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-017" "forall is followed by a double arrow"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "type Id = forall [T] ==> T -> T"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "type Id = forall [T] -> T"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-018" "a braced row names its tail with a pipe"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct f () : {Output | `R} Int = 1"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct f () : {Output |} Int = 1"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-019" "record type fields are semicolon-separated"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "type P = #{val x : Int; var y : String;}"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "type P = #{val x : Int var y : String}"
        , ""
        , "funct main () : () = ()"
        ]),

    rule "SYN-020" "with spells type arguments in square brackets"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct id[T] (x T) : T = x"
        , ""
        , "funct main () : Int = id with [Int] 1"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct id[T] (x T) : T = x"
        , ""
        , "funct main () : Int = id with #[Int] 1"
        ]),

    rule "SYN-021" "an array literal is comma-separated"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : [Int] = [1, 2, 3,]"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : [Int] = [, 1]"
        ]),

    rule "SYN-022" "record literal fields are semicolon-separated"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : () = (val r = #{val a = 1; val b = 2;}; ())"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : () = (val r = #{val a = 1 val b = 2}; ())"
        ]),

    rule "SYN-023" "a lambda head is parameters, an optional type and an equals sign"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : Int = (val f = { (x Int) : Int = + x 1 }; f 1)"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : Int = (val f = { (x Int) : = 1 }; f 1)"
        ]),

    rule "SYN-024" "a block binding needs a qualifier"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : Int = (val x = 1; x)"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : Int = (val = 1; 2)"
        ]),

    rule "SYN-025" "assignment uses a colon-equals"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : Int = (var x = 1; x := 2; x)"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : Int = (var x = 1; x = 2; x)"
        ]),

    rule "SYN-026" "only the documented comment forms are comments"
      (T.unlines [
          "module Main"
        , "//| a line comment"
        , "import @native"
        , "/| a block"
        , "comment |\\"
        , ""
        , "funct main () : () = ()"
        ])
      (T.unlines [
          "module Main"
        , "// not a comment"
        , "import @native"
        , ""
        , "funct main () : () = ()"
        ]),

    Rule "SYN-027" "reserved keywords cannot be names"
      [T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : () = ()"
        ]]
      [T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : () = let " <> kw <> " = 1 in ()"
        ]
      | kw <- ["pattern", "demands", "ensures", "unwinds"]],

    Rule "SYN-028" "reserved tokens cannot open an expression"
      [T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : Int = (val f = { x = + x 1 }; f $ 1)"
        ]]
      [ T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : () = (val x = ${ 1 }; ())"
        ]
      , T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : Int = (val x = 1 <- 2; x)"
        ]
      ],

    rule "SYN-029" "an exponent alone makes a float"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : Float = 1e3"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct 1e3 () : () = ()"
        ]),

    rule "SYN-030" "strings have escaped newline, tab and return"
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : () = sayn 'a\\nb\\tc\\rd'"
        ])
      (T.unlines [
          "module Main"
        , "import @native"
        , ""
        , "funct main () : () = sayn 'unterminated"
        ])
  ]

-- | The manifest next to the source tree, whichever directory the tests start
--   in.
manifestPath :: IO (Maybe FilePath)
manifestPath = go candidates
  where
    candidates = [
        "test/conformance/manifest.tsv"
      , "../test/conformance/manifest.tsv"
      , "../../test/conformance/manifest.tsv"
      ]
    go [] = pure Nothing
    go (p : ps) = do
      exists <- doesFileExist p
      if exists then pure (Just p) else go ps

-- | The rows of the manifest, without its header.
readManifest :: T.Text -> [(T.Text, T.Text)]
readManifest src =
  [ (T.strip ident, T.strip title)
  | line <- drop 1 (T.lines src)
  , not (T.null (T.strip line))
  , let (ident, rest) = T.breakOn "\t" line
  , not (T.null rest)
  , let title = T.drop 1 rest
  ]

conformanceSpec :: Spec
conformanceSpec = describe "conformance rules" $ do
  forM_ rules $ \r ->
    it (T.unpack (ruleId r) <> ": " <> T.unpack (ruleTitle r)) $ do
      forM_ (ruleAccepted r) $ \src ->
        case parseFromTextNamed "conformance.marr" chunk src of
          Right _ -> pure ()
          Left err -> expectationFailure $
            "SYN " <> T.unpack (ruleId r) <> " must accept this program:\n"
              <> T.unpack src <> "\nbut it failed:\n" <> err
      forM_ (ruleRejected r) $ \src ->
        case parseFromTextNamed "conformance.marr" chunk src of
          Right _ -> expectationFailure $
            "SYN " <> T.unpack (ruleId r) <> " must reject this program:\n"
              <> T.unpack src
          Left _ -> pure ()

  describe "manifest" $ do
    it "lists every rule once, with the same title" $ do
      path <- manifestPath
      case path of
        Nothing -> expectationFailure
          "test/conformance/manifest.tsv not found from the test directory"
        Just p -> do
          src <- TIO.readFile p
          readManifest src `shouldBe`
            [(ruleId r, ruleTitle r) | r <- rules]
