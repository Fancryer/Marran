{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

-- | The lexer's treatment of operators and the shape of syntax errors.  Both are
--   about the surface of the language: an operator is a name, and a failure is
--   reported in the same renderer as a type error.
module ParserSpec (pSpec) where

import qualified Data.Text as T
import Test.Hspec

import qualified Ast
import Ast (Typ (..), pattern EAnnot, pattern EApply, pattern EName)
import Lexer (Keyword (..), Token (..))
import Parser (chunk, parseFromTextNamed, parseTokensUnposed)
import qualified Parser

-- | The expression parser, for tests that care about the shape of a node
--   rather than about a whole program.
exp_ :: Parser.Parser Ast.Exp
exp_ = Parser.exp

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

    it "reads `==` and `===` as names, not as two assignments" $ do
      -- `==` is a function like `+`: `== 1 1` is an application.  Since `=`
      -- starts an assignment, the longer names have to be tried first.
      lexemes "== 1 1" `shouldBe` Right [TName "==", TInt 1, TInt 1]
      lexemes "=== 1 1" `shouldBe` Right [TName "===", TInt 1, TInt 1]
      lexemes "!= 1 2" `shouldBe` Right [TName "!=", TInt 1, TInt 2]
      lexemes "a = 1" `shouldBe` Right [TName "a", TAssign, TInt 1]

  describe "annotations" $ do
    it "parses `e : T` around the whole expression" $ do
      -- The annotation is looser than application: `f x : Int` is
      -- `(f x) : Int`, so `f` is applied before the type is attached.
      case parseFromTextNamed "demo.marr" exp_ "f x : Int" of
        Left e -> expectationFailure e
        Right (EAnnot (EApply (EName "f") (EName "x")) (TFlat "Int")) -> pure ()
        Right other -> expectationFailure $ "unexpected shape: " ++ show other

    it "parses an annotation on an aggregate literal" $ do
      case parseFromTextNamed "demo.marr" exp_ "[1, 2] : [Int]" of
        Left e -> expectationFailure e
        Right (EAnnot _ (TArray (TFlat "Int"))) -> pure ()
        Right other -> expectationFailure $ "unexpected shape: " ++ show other

    it "needs a type after the colon" $ do
      -- A bare `:` is a syntax error like any other unfinished statement, and
      -- it is reported at the statement, not reinterpreted as something else.
      ls <- parseFailure $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val x = 1 :;"
        , "  sayn x"
        ]
      take 2 ls `shouldBe`
        [ "error[E0013]: unexpected `val`"
        , " --> demo.marr:2:3"
        ]

  describe "match and patterns" $ do
    it "parses the clauses of a match, each with its own block" $ do
      case parseFromTextNamed "demo.marr" chunk $ T.unlines
        [ "funct f (n Int) : Int ="
        , "  match (n) to"
        , "    | 1 => 10"
        , "    | other => other"
        ] of
        Left e -> expectationFailure e
        Right _ -> pure ()

    it "reads a primitive clause as alternatives of one clause" $ do
      -- `| 1 2 3 => ...` is one block for three values, not three clauses, so
      -- the alias after the patterns belongs to all three.
      case parseFromTextNamed "demo.marr" exp_ $ T.unlines
        [ "match (n) to"
        , "  | 1 2 3 as n => n"
        , "  | _ => 0"
        ] of
        Left e -> expectationFailure e
        Right (Ast.EMatch _ (clause : _)) ->
          case clause of
            Ast.MatchClause ps _ _ -> length ps `shouldBe` 3
        Right other -> expectationFailure $ "unexpected shape: " ++ show other

    it "parses the split patterns and `#` constructors" $ do
      case parseFromTextNamed "demo.marr" exp_ $ T.unlines
        [ "match (s) to"
        , "  | 'ab' |-> rest => rest"
        , "  | rest <-| 'yz' => rest"
        , "  | #Some x => x"
        , "  | _ => ''"
        ] of
        Left e -> expectationFailure e
        Right _ -> pure ()

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
