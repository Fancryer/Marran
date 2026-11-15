{-# LANGUAGE OverloadedStrings #-}

-- | The lexer's treatment of operators and the shape of syntax errors.  Both are
--   about the surface of the language: an operator is a name, and a failure is
--   reported in the same renderer as a type error.
module ParserSpec (pSpec) where

import qualified Data.Text as T
import Test.Hspec

import Lexer (Keyword (..), Token (..))
import Parser (chunk, parseFromTextNamed, parseTokensUnposed)

-- | Parse a program and return the rendered error, failing the test if the
--   program unexpectedly parses.
parseFailure :: T.Text -> IO [T.Text]
parseFailure src = case parseFromTextNamed "demo.marr" chunk src of
  Left e  -> pure (T.lines (T.pack e))
  Right _ -> expectationFailure "the program parsed, but it should not have" >> pure []

-- | The tokens of a line, without their positions.
lexemes :: T.Text -> Either String [Token]
lexemes = parseTokensUnposed

pSpec :: Spec
pSpec = do
  describe "the lexer" $ do
    it "keeps `|` inside a name, so `||`, `|>` and `<|` are operators" $ do
      -- An operator is a name whose letters are punctuation.  Without this the
      -- language had no way to spell `||` or a pipe operator at all: the pipe
      -- was a token of its own, and `a || b` lexed as `a`, `|`, `|`, `b`.
      lexemes "a || b" `shouldBe` Right [TName "a", TName "||", TName "b"]
      lexemes "a |> b" `shouldBe` Right [TName "a", TName "|>", TName "b"]
      lexemes "a <| b" `shouldBe` Right [TName "a", TName "<|", TName "b"]

    it "still reads a lone `|` as the pipe" $ do
      -- A record update and a row tail both separate on a bare `|`, so the one
      -- spelling that means "pipe" must not become a one-letter name.
      lexemes "#{ base | val c = 3 }" `shouldBe` Right
        [TSharpBraceL, TName "base", TPipe, TKW KWVal, TName "c", TAssign, TInt 3, TBraceR]
      lexemes "{Doubt | `R}" `shouldBe` Right
        [TBraceL, TName "Doubt", TPipe, TTVar "R", TBraceR]

    it "does not glue an operator to a following word" $ do
      lexemes "a||b" `shouldBe` Right [TName "a||b"]
      lexemes "| val c = 3" `shouldBe` Right [TPipe, TKW KWVal, TName "c", TAssign, TInt 3]

    it "keeps an underscore out of a name, so `_x` is a wildcard and `x`" $ do
      lexemes "_x" `shouldBe` Right [TUnderscore, TName "x"]
      lexemes "or_else" `shouldBe` Right [TName "or_else"]

  describe "syntax errors" $ do
    it "reports an unexpected token with its code and position" $ do
      ls <- parseFailure $ T.unlines
        [ "funct main () : {Output} ()"
        , "  sayn 1"
        ]
      take 5 ls `shouldBe`
        [ "error[E0013]: unexpected `sayn`"
        , " --> demo.marr:2:3"
        , "  |"
        , "2 |   sayn 1"
        , "  |   ^^^^"
        ]

    it "reports an unexpected keyword where a statement cannot start" $ do
      ls <- parseFailure $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val = 3;"
        , "  sayn 1"
        ]
      take 2 ls `shouldBe`
        [ "error[E0013]: unexpected `val`"
        , " --> demo.marr:2:3"
        ]

    it "reports the end of input when a literal is unterminated" $ do
      ls <- parseFailure $ T.unlines
        [ "funct main () : {Output} () ="
        , "  sayn 'unterminated"
        ]
      take 2 ls `shouldBe`
        [ "error[E0013]: unexpected end of input; expected `'`, `\\'`, `\\\\`"
        , " --> demo.marr:3:1"
        ]
