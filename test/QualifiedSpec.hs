{-# LANGUAGE OverloadedStrings #-}

-- | Qualified names, @Module::name@.
--
--   Resolution needs a second file, so most tests here write a small library
--   and a @main.marr@ next to it, the same way 'ImportSpec' does, and run the
--   program through 'runSource'.  The two exceptions are syntactic: the spelling
--   has to survive parsing, 'Pretty' and 'Sexp', and the walk that reports every
--   use has to know every namespace a name can occupy.
module QualifiedSpec (qSpec) where

import Control.Monad (forM_)
import Data.List (isInfixOf, nub, sort)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, getTemporaryDirectory,
                         removePathForcibly)
import System.FilePath (takeDirectory, (</>))
import Test.Hspec

import Parser (chunk, parseFromTextNamed)
import Qualified (UseKind (..), QualUse (..), qualUses)
import Sexp (sexp)
import Suite (runSource)
import Utils (Pretty (..))

-- | Run a program whose files are a map from a relative path to its source.
--   The program is @main.marr@; every fixture gets a fresh directory, so two
--   tests never see each other's modules.
runFiles :: [(FilePath, T.Text)] -> T.Text -> IO (Either String String)
runFiles files src = do
  tmp <- getTemporaryDirectory
  dir <- freshDirectory tmp
  forM_ files $ \(path, text) -> do
    let full = dir </> path
    createDirectoryIfMissing True (takeDirectory full)
    TIO.writeFile full text
  result <- runSource (dir </> "main.marr") "" src
  removePathForcibly dir
  pure result

-- | A directory name that does not exist yet.
freshDirectory :: FilePath -> IO FilePath
freshDirectory tmp = go (0 :: Int)
  where
    go n = do
      let dir = tmp </> ("marran-qualified-" <> show n)
      exists <- doesDirectoryExist dir
      if exists then go (n + 1) else do
        createDirectoryIfMissing True dir
        pure dir

-- | The output of a run that must succeed, without the event reports the
--   interpreter may print.
printed :: Either String String -> Either String [String]
printed = fmap (filter (not . isReport) . lines)
  where
    isReport l = "EVENTS:" `isInfixOf` l || "EVENT-VIOLATION" `isInfixOf` l

-- | A library with a function, a private function, and two enumerations.
library :: T.Text
library = T.unlines
  [ "module Lib [funct identify enum Colour enum Box]"
  , "import @native"
  , ""
  , "funct identify (x Int) : Int = x"
  , ""
  , "funct hidden (x Int) : Int = + x 100"
  , ""
  , "enum Colour | Red | Green"
  , ""
  , "enum Box[a] | Mk (val v : a)"
  ]

-- | A library with an effect and the enumeration its operation takes.
effects :: T.Text
effects = T.unlines
  [ "module EffLib [effect Writer enum Mode]"
  , "import @native"
  , ""
  , "enum Mode | Fast | Slow"
  , ""
  , "effect Writer"
  , "  send : Mode -> ()"
  , "end"
  ]

-- | A library with one row alias.
rows :: T.Text
rows = T.unlines
  [ "module RowLib [row Chatty]"
  , "import @native"
  , ""
  , "row Chatty = {Output}"
  ]

qSpec :: Spec
qSpec = describe "qualified names" $ do

  it "resolves a value under the module header's name and the file's name" $ do
    -- `Lib` is what the file calls itself; `lib` is what `import lib` wrote.
    -- A reader may have either in mind, and both spell the same declaration.
    r <- runFiles [("lib.marr", library)] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import lib"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (Lib::identify 7);"
      , "  sayn (lib::identify 8)"
      ]
    printed r `shouldBe` Right ["7", "8"]

  it "keeps a local let from shadowing a qualified value" $ do
    -- The qualified spelling is a binding of its own, made when the module
    -- starts, so a local name cannot take it away.  The unqualified `identify`
    -- would be the local `sayn`, but this program never asks for it.
    r <- runFiles [("lib.marr", library)] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import lib"
      , ""
      , "funct main () : {Output} () ="
      , "  let identify = sayn in"
      , "  sayn (Lib::identify 9)"
      ]
    printed r `shouldBe` Right ["9"]

  it "reports a module that was not imported" $ do
    r <- runFiles [] $ T.unlines
      [ "module Main"
      , "import @native"
      , ""
      , "funct main () : {Output} () = sayn (Lib::identify 1)"
      ]
    case r of
      Left err -> do
        err `shouldSatisfy` ("the module `Lib` is not imported" `isInfixOf`)
        err `shouldSatisfy` ("the modules this file imports are: @native" `isInfixOf`)
      Right _ -> expectationFailure "an unimported module must be a diagnostic"

  it "suggests the module when its spelling is one edit away" $ do
    r <- runFiles [("lib.marr", library)] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import lib"
      , ""
      , "funct main () : {Output} () = sayn (Libb::identify 1)"
      ]
    case r of
      Left err -> err `shouldSatisfy` ("did you mean `Lib`?" `isInfixOf`)
      Right _ -> expectationFailure "a misspelled module must be a diagnostic"

  it "reports a private name, saying it is not exported" $ do
    r <- runFiles [("lib.marr", library)] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import lib"
      , ""
      , "funct main () : {Output} () = sayn (Lib::hidden 1)"
      ]
    case r of
      Left err -> do
        err `shouldSatisfy` ("`hidden` is declared in `Lib` but not exported" `isInfixOf`)
        err `shouldSatisfy` ("a module offers the names its export list names" `isInfixOf`)
      Right _ -> expectationFailure "a private name must not be reachable"

  it "suggests a name when its spelling is one edit away" $ do
    r <- runFiles [("lib.marr", library)] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import lib"
      , ""
      , "funct main () : {Output} () = sayn (Lib::identif 1)"
      ]
    case r of
      Left err -> err `shouldSatisfy` ("did you mean `Lib::identify`?" `isInfixOf`)
      Right _ -> expectationFailure "a misspelled name must be a diagnostic"

  it "reports an exported name the import list did not bring" $ do
    -- Qualification is disambiguation, not a way around the module system:
    -- `identify` is exported, but this file asked only for `Colour`.
    r <- runFiles [("lib.marr", library)] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import lib [enum Colour]"
      , ""
      , "funct main () : {Output} () = sayn (Lib::identify 3)"
      ]
    case r of
      Left err -> do
        err `shouldSatisfy` ("`identify` is offered by `Lib` but not imported here" `isInfixOf`)
        err `shouldSatisfy` ("name it in the import list of `Lib`" `isInfixOf`)
      Right _ -> expectationFailure "an unimported name must be a diagnostic"

  it "reports a top-level declaration that shadows the import" $ do
    -- A module-level declaration is not a local variable: it really does take
    -- the spelling `identify` away, and reaching through `Lib` would be a way
    -- around the shadowing the loader reports everywhere else.
    r <- runFiles [("lib.marr", library)] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import lib"
      , ""
      , "funct identify (x Int) : Int = x"
      , ""
      , "funct main () : {Output} () = sayn (Lib::identify 1)"
      ]
    case r of
      Left err -> do
        err `shouldSatisfy` ("is shadowed by a declaration of `identify` here" `isInfixOf`)
        err `shouldSatisfy` ("rename the import with `as`" `isInfixOf`)
      Right _ -> expectationFailure "a shadowed import must not be reachable"

  it "resolves the qualified spelling of a renamed import" $ do
    -- `as inc` renames the local spelling, and the qualified spelling still
    -- names the declaration the import brought, under that local name.
    r <- runFiles [("lib.marr", library)] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import lib [funct identify as inc]"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (Lib::identify 3);"
      , "  sayn (inc 4)"
      ]
    printed r `shouldBe` Right ["3", "4"]

  it "reads a qualified type and a qualified type argument" $ do
    r <- runFiles [("lib.marr", library)] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import lib"
      , ""
      , "funct unwrap (b Lib::Box#[Int]) : Int ="
      , "  match b to"
      , "  | #Lib::Mk x => x"
      , ""
      , "funct main () : {Output} () = sayn (unwrap (Lib::Mk 3))"
      ]
    printed r `shouldBe` Right ["3"]

  it "builds and matches a qualified constructor" $ do
    -- The pattern is rewritten to the declared constructor name, because the
    -- tag a value carries is the one the enumeration declared, not the one
    -- this file imported it under.
    r <- runFiles [("lib.marr", library)] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import lib"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (Lib::Red);"
      , "  sayn (match (Lib::Green) to"
      , "  | #Lib::Red => 'red'"
      , "  | #Lib::Green => 'green')"
      ]
    printed r `shouldBe` Right ["Red", "green"]

  it "uses a qualified effect and its operation in a handler" $ do
    r <- runFiles [("efflib.marr", effects)] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import efflib"
      , ""
      , "funct label (m EffLib::Mode) : String ="
      , "  match m to"
      , "  | #Fast => 'fast'"
      , "  | #Slow => 'slow'"
      , ""
      , "funct announce () : {EffLib::Writer} () = EffLib::send Fast"
      , ""
      , "funct main () : {Output} () ="
      , "  under EffLib::Writer to"
      , "    announce ()"
      , "  handle"
      , "  | EffLib::send m => sayn (label m); resume ()"
      , "  | then x => x"
      ]
    printed r `shouldBe` Right ["fast"]

  it "uses a qualified row alias" $ do
    r <- runFiles [("rowlib.marr", rows)] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import rowlib"
      , ""
      , "funct talk () : RowLib::Chatty () = sayn 'hi'"
      , ""
      , "funct main () : {Output} () = talk ()"
      ]
    printed r `shouldBe` Right ["hi"]

  it "works for a native module" $ do
    -- `import @native` is the whole native scope; the module part of the
    -- spelling still has to be the module that offers the name.
    r <- runFiles [] $ T.unlines
      [ "module Main"
      , "import @native"
      , ""
      , "funct main () : {Output; Error} () ="
      , "  Output::sayn (Conv::parse with [Int] '41');"
      , "  sayn (Conv::parse with [Int] '42')"
      ]
    printed r `shouldBe` Right ["41", "42"]

  it "does not let a native module answer for another's name" $ do
    r <- runFiles [] $ T.unlines
      [ "module Main"
      , "import @native"
      , ""
      , "funct main () : {Output} () = Numbers::sayn 'x'"
      ]
    case r of
      Left err -> do
        err `shouldSatisfy` ("`@native Numbers` does not offer `sayn`" `isInfixOf`)
        err `shouldSatisfy` ("it offers:" `isInfixOf`)
      Right _ -> expectationFailure "a native module must offer only its own names"

  it "needs the native module in the import when only one was named" $ do
    -- `import @native Output` is not the whole scope: `Conv` was not asked
    -- for, so its names are not reachable, qualified or not.
    r <- runFiles [] $ T.unlines
      [ "module Main"
      , "import @native Output"
      , ""
      , "funct main () : {Output} () = sayn (Conv::parse with [Int] '1')"
      ]
    case r of
      Left err -> err `shouldSatisfy` ("the module `Conv` is not imported" `isInfixOf`)
      Right _ -> expectationFailure "a module outside the import must be a diagnostic"

  it "keeps a qualified spelling through parsing, Pretty and Sexp" $ do
    -- The loader rewrites a spelling to the local name it denotes, but the
    -- parsed tree is what a dump shows before that, and it must carry the
    -- name as written rather than losing the qualification.
    let src = T.unlines
          [ "module Demo"
          , "import @native"
          , ""
          , "funct f (x Lib::T) : Lib::T = Lib::g x"
          ]
    case parseFromTextNamed "demo.marr" chunk src of
      Left e -> expectationFailure e
      Right m -> do
        T.pack (sexp m) `shouldSatisfy` T.isInfixOf "Lib::T"
        pretty m `shouldSatisfy` T.isInfixOf "Lib::T"
        pretty m `shouldSatisfy` T.isInfixOf "Lib::g"

  it "reports each use in the namespace its position implies" $ do
    -- One name may be a type here and a value there; the walk is the single
    -- place that knows every position, so it is asked for all of them at once.
    let src = T.unlines
          [ "module Demo"
          , "import @native"
          , "import lib"
          , ""
          , "type Alias = Lib::T"
          , ""
          , "row R = {Lib::Eff}"
          , ""
          , "effect F"
          , "  op : Lib::T -> ()"
          , "end"
          , ""
          , "enum E | C (val v : Lib::T)"
          , ""
          , "funct f (x Lib::T#[Lib::U]) : {Lib::Eff} Lib::T ="
          , "  under Lib::Eff to Lib::mk x"
          , "  handle"
          , "  | Lib::op y => resume (Lib::mk y)"
          , "  | then r => r"
          , ""
          , "funct g (x Lib::T) : Lib::T ="
          , "  match x to"
          , "  | #Lib::C y => y"
          , "  | _ => x"
          , ""
          , "funct h () : Lib::Row () = ()"
          ]
    case parseFromTextNamed "demo.marr" chunk src of
      Left e -> expectationFailure e
      Right m -> sort (nub [(quName u, quKind u) | u <- qualUses m])
        `shouldBe` sort
          [ ("Lib::C", UseCtor)
          , ("Lib::Eff", UseEffect)
          , ("Lib::Row", UseRow)
          , ("Lib::T", UseType)
          , ("Lib::U", UseType)
          , ("Lib::mk", UseValue)
          , ("Lib::op", UseOp)
          ]
