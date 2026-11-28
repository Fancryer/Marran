{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

-- | The lexer's treatment of operators and the shape of syntax errors.  Both are
--   about the surface of the language: an operator is a name, and a failure is
--   reported in the same renderer as a type error.
module ParserSpec (pSpec) where

import qualified Data.Text as T
import Test.Hspec

import qualified Ast
import Ast (Typ (..), TypeArg (..), TypeApps (..), EffApps (..), pattern EAnnot, pattern EApply, pattern EName, pattern EWith)
import Ast (Module(..), ModuleHeader(..), ExportDecl(..), DeclKind(..), headerExportsAll, TopLevelStat(..), EffRow(..))
import Lexer (Keyword (..), Token (..))
import Parser (chunk, parseFromTextNamed, parseTokensUnposed)
import Suite (withModuleHeader)
import qualified Parser

-- | The expression parser, for tests that care about the shape of a node
--   rather than about a whole program.
exp_ :: Parser.Parser Ast.Exp
exp_ = Parser.exp

-- | Parse a program and return the rendered error, failing the test if the
--   program unexpectedly parses.
parseFailure :: T.Text -> IO [T.Text]
parseFailure src = case parseFromTextNamed "demo.marr" chunk (withModuleHeader src) of
  Left e  -> pure (T.lines (T.pack e))
  Right _ -> expectationFailure "the program parsed, but it should not have" >> pure []

-- | Like 'parseFailure', but the source is a whole file, header included.
parseFailureRaw :: T.Text -> IO [T.Text]
parseFailureRaw src = case parseFromTextNamed "demo.marr" chunk src of
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

    it "reads an exponent-only decimal as a float" $ do
      -- `1e3` is a float, not the integer `1` applied to the name `e3`.
      lexemes "1e3" `shouldBe` Right [TFloat 1000]
      lexemes "1.5e2" `shouldBe` Right [TFloat 150]

    it "reads the string escapes" $ do
      -- A string may spell a newline, a tab and a carriage return.
      lexemes "'a\\nb\\tc\\rd'" `shouldBe` Right [TString "a\nb\tc\rd"]

    it "reads `as` as a keyword" $ do
      -- `as` renames in exports, imports and patterns; it is not a name that a
      -- program may bind or apply.
      lexemes "as" `shouldBe` Right [TKW KWAs]
      lexemes "`as" `shouldBe` Right [TTVar "as"]

    it "reads the split-pattern arrows as tokens of their own" $ do
      -- `|->` and `<-|` are not names: a pattern parser must see them as one
      -- token each.  In particular, `<-|` wins over `<-` so it cannot become
      -- `TRevArrow` followed by `TPipe`.
      lexemes "a |-> b" `shouldBe` Right [TName "a", TStartsArrow, TName "b"]
      lexemes "a <-| b" `shouldBe` Right [TName "a", TEndsArrow, TName "b"]
      lexemes "a <- b" `shouldBe` Right [TName "a", TRevArrow, TName "b"]

    it "reserves the future keywords and `${`" $ do
      -- The freeze announces these spellings now; a program may no longer use
      -- them as names.  The lexer, not a warning in the parser, enforces it.
      lexemes "pattern demands ensures unwinds ${" `shouldBe` Right
        [TKW KWPattern, TKW KWDemands, TKW KWEnsures, TKW KWUnwinds, TDollarBraceL]

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

  describe "type arguments of `with`" $ do
    it "binds the argument to the name, not to the application" $ do
      -- `parse with [Int] s` is `(parse with [Int]) s`: the representation
      -- travels with the name, so the interpreter can hand it to the native
      -- before the real argument arrives.
      case parseFromTextNamed "demo.marr" exp_ "parse with [Int] s" of
        Left e -> expectationFailure e
        Right (EApply (EWith (EName "parse") (TypeApps [TAFlat "Int"]) (EffApps [] [])) (EName "s")) ->
          pure ()
        Right other -> expectationFailure $ "unexpected shape: " ++ show other

    it "does not accept the `#[...]` spelling after `with`" $ do
      -- `with` spells its type arguments as a plain `[...]`; `#[...]` is for
      -- an ordinary application.
      case parseFromTextNamed "demo.marr" exp_ "loop with #[Int] 5" of
        Left _ -> pure ()
        Right other -> expectationFailure $ "unexpected shape: " ++ show other

    it "reads a parenthesised pair type inside the brackets" $ do
      -- `nil` consumes `(` before it learns the parentheses are not empty, so
      -- the type atom has to backtrack; without that, every `[(T1, T2)]`
      -- argument failed at the `T1`.
      case parseFromTextNamed "demo.marr" exp_ "parse with [(Int, String)] s" of
        Left e -> expectationFailure e
        Right (EApply (EWith _ (TypeApps [TAParen (TAPair (TAFlat "Int") (TAFlat "String"))]) _) _) ->
          pure ()
        Right other -> expectationFailure $ "unexpected shape: " ++ show other

  describe "record types" $ do
    it "requires a semicolon between fields" $ do
      -- A trailing semicolon is optional, but two fields cannot be separated
      -- by whitespace alone.
      ls <- parseFailure "type T = #{val a : Int val b : String}"
      take 1 ls `shouldBe` ["error[E0013]: unexpected `val`"]

    it "allows a trailing separator in a list" $ do
      -- A trailing `;` or `,` closes the list without another element.
      case parseFromTextNamed "demo.marr" chunk . withModuleHeader $ T.unlines
        [ "type P = #{val x : Int; var y : String;}"
        , "type Box[T] = T"
        , "funct main () : Box#[Int;] ="
        , "  (val xs = [1, 2,]; val r = #{val a = 1;}; ())"
        ] of
        Left e -> expectationFailure e
        Right _ -> pure ()

  describe "match and patterns" $ do
    it "parses the clauses of a match, each with its own block" $ do
      case parseFromTextNamed "demo.marr" chunk . withModuleHeader $ T.unlines
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
        , "  | 'a' <-| x <-| 'c' => x"
        , "  | #Some x => x"
        , "  | (a, b) => a"
        , "  | c, d => c"
        , "  | _ => ''"
        ] of
        Left e -> expectationFailure e
        Right _ -> pure ()

  describe "the module header" $ do
    it "is the first thing a file must have" $ do
      -- The header is where a file says what it is; without one the program
      -- has no name to be reported under, so the failure names the fix.
      ls <- parseFailureRaw $ T.unlines
        [ "funct main () : {Output} () ="
        , "  sayn 1"
        ]
      take 2 ls `shouldBe`
        [ "error[E0013]: a file must start with a module header: `module Main` for a program, `module Name` for a module"
        , " --> demo.marr:1:1"
        ]

    it "records the name of the module" $ do
      case parseFromTextNamed "demo.marr" chunk (T.unlines
        [ "module Demo"
        , ""
        , "funct f () : Int = 1"
        ]) of
        Left e -> expectationFailure e
        Right (Module header _) -> mhName header `shouldBe` "Demo"

    it "has no export list when the module exports everything" $ do
      case parseFromTextNamed "demo.marr" chunk "module Demo\nfunct f () : Int = 1" of
        Left e -> expectationFailure e
        Right (Module header _) -> headerExportsAll header `shouldBe` True

    it "reads kinds and aliases in an export list" $ do
      -- The kind is optional and only disambiguates; `as` renames the name for
      -- everyone who imports the module.
      case parseFromTextNamed "demo.marr" chunk (T.unlines
        [ "module Demo [funct f as g enum E type T]"
        , "funct f () : Int = 1"
        ]) of
        Left e -> expectationFailure e
        Right (Module header _) ->
          fmap (\d -> (edKind d, edName d, edAlias d)) <$> mhExports header
            `shouldBe` Just
              [ (Just KindFunct, "f", Just "g")
              , (Just KindEnum, "E", Nothing)
              , (Just KindType, "T", Nothing)
              ]

    it "does not accept a keyword as a module name" $ do
      ls <- parseFailureRaw "module funct\n"
      take 1 ls `shouldBe` ["error[E0013]: unexpected `funct`"]

  describe "a function's result type" $ do
    it "reads a bare type variable as the result, not as a row" $ do
      -- `: `T = ...` used to take the variable for the effect row and then
      -- demand a result type after it, so a function whose result is a type
      -- variable did not parse without a row in front of it.
      case parseFromTextNamed "demo.marr" chunk . withModuleHeader $ T.unlines
        [ "funct unwrap_or (default `T) (m Maybe#[`T]) : `T ="
        , "  default"
        ] of
        Left e -> expectationFailure e
        Right (Module _ [FunctDef _ _ _ _ _ row out _]) -> do
          row `shouldBe` Nothing
          out `shouldBe` TVar "T"
        Right other -> expectationFailure $ "unexpected shape: " ++ show other

    it "still reads a leading name as a row when a type follows it" $ do
      case parseFromTextNamed "demo.marr" chunk . withModuleHeader $ T.unlines
        [ "funct f () : `R () ="
        , "  ()"
        ] of
        Left e -> expectationFailure e
        Right (Module _ [FunctDef _ _ _ _ _ row out _]) -> do
          row `shouldBe` Just (ERVar "R")
          out `shouldBe` Ast.TNil
        Right other -> expectationFailure $ "unexpected shape: " ++ show other

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
        [ "error[E0013]: unexpected end of input; expected `'`, `\\'`, `\\\\`, `\\n`, or 2 more"
        , " --> demo.marr:3:1"
        ]
