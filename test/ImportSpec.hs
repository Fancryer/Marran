{-# LANGUAGE OverloadedStrings #-}

-- | Imports: what a module sees, what it offers, and what it hides.
--
--   The loader is the part of the front end that reads more than one file, so
--   its tests write a small program on disk and run it through 'runSource', the
--   same way @--run@ does.  A fixture is a map from a relative path to its
--   source, written into a fresh directory for every test, so no test can see
--   another's files and the repository keeps no library of its own.
module ImportSpec (iSpec) where

import Control.Monad (forM_)
import Data.List (isInfixOf)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, getTemporaryDirectory,
                         removePathForcibly)
import System.FilePath (takeDirectory, (</>))
import Test.Hspec

import Suite (runSource)

-- | Run a program whose files are given as a map from a relative path to its
--   source.  The program itself is the file called @main.marr@.
--
--   The files are written under a directory of their own in the system
--   temporary directory, which is removed afterwards: a fixture must not leak
--   into the repository, and no two tests may see each other's modules.
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
      let dir = tmp </> ("marran-imports-" <> show n)
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

-- | A fixture module: the names it exports and the names it keeps.
numbers :: T.Text
numbers = T.unlines
  [ "module Numbers [funct one]"
  , "import @native"
  , ""
  , "funct hidden (x Int) : Int = + x 100"
  , ""
  , "funct one (x Int) : Int = hidden x"
  ]

-- | A module that offers an enumeration and nothing else.  Naming a type whose
--   values cannot be written would be an export nobody could use, so the
--   constructors travel with it.
palette :: T.Text
palette = T.unlines
  [ "module Palette [enum Colour]"
  , "import @native"
  , ""
  , "enum Colour | Red | Green"
  ]

-- | A module that imports 'numbers' and offers its own name.
doubler :: T.Text
doubler = T.unlines
  [ "module Doubler [funct two]"
  , "import @native"
  , "import numbers"
  , ""
  , "funct two (x Int) : Int = one (one x)"
  ]

iSpec :: Spec
iSpec = describe "imports" $ do
  it "sees a name the imported module exports" $ do
    r <- runFiles [ ("numbers.marr", numbers) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import numbers"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (one 1)"
      ]
    printed r `shouldBe` Right ["101"]

  it "reports a missing module, naming where it looked" $ do
    r <- runFiles [] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import nowhere"
      ]
    case r of
      Left err -> do
        err `shouldSatisfy` ("cannot find the module `nowhere`" `isInfixOf`)
        err `shouldSatisfy` ("looked for:" `isInfixOf`)
      Right _ -> expectationFailure "a missing module must be a diagnostic"

  it "takes the whole export list when the import lists no names" $ do
    r <- runFiles [ ("numbers.marr", numbers) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import numbers"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (one 1)"
      ]
    printed r `shouldBe` Right ["101"]

  it "hides a name the module did not export" $ do
    -- The loader's table for `numbers` holds `one` and nothing else, so
    -- `hidden` is not absent from a list of candidates: it was never imported.
    r <- runFiles [ ("numbers.marr", numbers) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import numbers #hidden"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (hidden 1)"
      ]
    case r of
      Left err -> err `shouldSatisfy` ("E0007" `isInfixOf`)
      Right out -> expectationFailure $
        "an unexported name must not be importable, got: " ++ take 300 out

  it "imports a single name with `#`" $ do
    r <- runFiles [ ("numbers.marr", numbers) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import numbers #one"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (one 1)"
      ]
    printed r `shouldBe` Right ["101"]

  it "renames an imported name with `as`" $ do
    r <- runFiles [ ("numbers.marr", numbers) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import numbers [funct one as inc]"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (inc 1);"
      , "  sayn (one 1)"
      ]
    case r of
      Left err -> err `shouldSatisfy` ("E0007" `isInfixOf`)
      Right out -> expectationFailure $
        "an alias must replace the declared name, got: " ++ take 300 out

  it "reads a chain of imports in dependency order" $ do
    r <- runFiles
      [ ("numbers.marr", numbers)
      , ("doubler.marr", doubler)
      ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import doubler"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (two 1)"
      ]
    printed r `shouldBe` Right ["201"]

  it "lets a module re-export a name it imported" $ do
    let middle = T.unlines
          [ "module Middle [funct one]"
          , "import numbers [funct one]"
          ]
    r <- runFiles
      [ ("numbers.marr", numbers)
      , ("middle.marr", middle)
      ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import middle"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (one 1)"
      ]
    printed r `shouldBe` Right ["101"]

  it "does not leak a private name through a re-export" $ do
    -- `Middle` re-exports `one` and has a private `hidden` of its own; the name
    -- resolves to the module that declared it, so `hidden` of `Numbers` stays
    -- invisible even though `Middle` imports it.
    let middle = T.unlines
          [ "module Middle [funct one]"
          , "import numbers [funct one]"
          ]
    r <- runFiles
      [ ("numbers.marr", numbers)
      , ("middle.marr", middle)
      ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import middle #hidden"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (hidden 1)"
      ]
    case r of
      Left err -> err `shouldSatisfy` ("E0007" `isInfixOf`)
      Right out -> expectationFailure $
        "a re-export must not carry a name the middle module did not have, got: " ++ take 300 out

  it "reports two imports that bring one name" $ do
    let other = T.unlines
          [ "module Other [funct one]"
          , "import @native"
          , ""
          , "funct one (x Int) : Int = + x 2"
          ]
    r <- runFiles
      [ ("numbers.marr", numbers)
      , ("other.marr", other)
      ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import numbers"
      , "import other"
      ]
    case r of
      Left err -> err `shouldSatisfy` ("two imports bring `one`" `isInfixOf`)
      Right _ -> expectationFailure "a clash of two imports must be a diagnostic"

  it "keeps both names when one of them is renamed" $ do
    let other = T.unlines
          [ "module Other [funct one]"
          , "import @native"
          , ""
          , "funct one (x Int) : Int = + x 2"
          ]
    r <- runFiles
      [ ("numbers.marr", numbers)
      , ("other.marr", other)
      ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import numbers"
      , "import other [funct one as two]"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (one 1);"
      , "  sayn (two 1)"
      ]
    printed r `shouldBe` Right ["101", "3"]

  it "lets the module's own declaration win over an import" $ do
    r <- runFiles [ ("numbers.marr", numbers) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import numbers"
      , ""
      , "funct one (x Int) : Int = x"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (one 1)"
      ]
    printed r `shouldBe` Right ["1"]

  it "keeps two private helpers of two modules apart" $ do
    let left = T.unlines
          [ "module Left [funct left]"
          , "import @native"
          , ""
          , "funct helper (x Int) : Int = + x 1"
          , ""
          , "funct left (x Int) : Int = helper x"
          ]
        right = T.unlines
          [ "module Right [funct right]"
          , "import @native"
          , ""
          , "funct helper (x Int) : Int = + x 100"
          , ""
          , "funct right (x Int) : Int = helper x"
          ]
    r <- runFiles
      [ ("left.marr", left)
      , ("right.marr", right)
      ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import left"
      , "import right"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (left 1);"
      , "  sayn (right 1)"
      ]
    printed r `shouldBe` Right ["2", "101"]

  it "checks a cycle as one block and runs it" $ do
    let x = T.unlines
          [ "module X [funct evenX]"
          , "import @native"
          , "import y"
          , ""
          , "funct evenX (n Int) : Boolean ="
          , "  if ieq n 0 then true else oddY (- n 1)"
          ]
        y = T.unlines
          [ "module Y [funct oddY]"
          , "import @native"
          , "import x"
          , ""
          , "funct oddY (n Int) : Boolean ="
          , "  if ieq n 0 then false else evenX (- n 1)"
          ]
    r <- runFiles
      [ ("x.marr", x)
      , ("y.marr", y)
      ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import x"
      , "import y"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (evenX 4);"
      , "  sayn (oddY 4)"
      ]
    printed r `shouldBe` Right ["true", "false"]

  it "finds the units of a directory import under its path" $ do
    r <- runFiles
      [ ("lib/numbers.marr", numbers) ]
      $ T.unlines
      [ "module Main"
      , "import @native"
      , "import 'lib/' [numbers]"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (one 1)"
      ]
    printed r `shouldBe` Right ["101"]

  it "names the module after its header, not after its file" $ do
    -- The file is `odd_name.marr` and the header says `Renamed`; an import
    -- finds the file by path and the diagnostic would quote the header.  The
    -- check here is that the two need not agree.
    let renamed = T.unlines
          [ "module Renamed [funct one]"
          , "import @native"
          , ""
          , "funct one (x Int) : Int = + x 1"
          ]
    r <- runFiles [ ("odd_name.marr", renamed) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import odd_name"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (one 1)"
      ]
    printed r `shouldBe` Right ["2"]

  it "runs only the entry module's `main`" $ do
    -- A library may have a `main` of its own; importing it must not call it.
    let library = T.unlines
          [ "module Library [funct one]"
          , "import @native Output"
          , "import @native Numbers"
          , ""
          , "funct main () : {Output} () = sayn 'library main'"
          , ""
          , "funct one (x Int) : Int = + x 1"
          ]
    r <- runFiles [ ("library.marr", library) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import library"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (one 1)"
      ]
    printed r `shouldBe` Right ["2"]

  it "reports an export the module does not have" $ do
    let broken = T.unlines
          [ "module Broken [funct missing]"
          , "import @native"
          ]
    r <- runFiles [ ("broken.marr", broken) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import broken"
      , ""
      , "funct main () : () = ()"
      ]
    case r of
      Left err -> err `shouldSatisfy` ("cannot be exported" `isInfixOf`)
      Right _ -> expectationFailure "an export of an unknown name must be a diagnostic"

  it "gives a module the native names only of the modules it imported" $ do
    let narrow = T.unlines
          [ "module Narrow [funct run]"
          , "import @native Output"
          , ""
          , "funct run () : {Output} () = sayn 'ok'"
          ]
    r <- runFiles [ ("narrow.marr", narrow) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import narrow"
      , ""
      , "funct main () : {Output} () = run ()"
      ]
    printed r `shouldBe` Right ["ok"]

  it "brings the constructors of an enumeration with its name" $ do
    -- `Colour` in a signature and `#Red` in a pattern are not enough: an
    -- expression has to be able to write `Red`, so the export list names the
    -- type and the import receives its values too.
    r <- runFiles [ ("palette.marr", palette) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import palette"
      , ""
      , "funct describe (c Colour) : String ="
      , "  match c to"
      , "  | #Red => 'red'"
      , "  | #Green => 'green'"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (describe Green)"
      ]
    printed r `shouldBe` Right ["green"]

  it "brings constructors through an export list that names only the enum" $ do
    -- The module has an export list and `Red` is not in it by name; the type it
    -- belongs to is, and a type arrives with its values.
    let explicit = T.unlines
          [ "module Explicit [enum Colour]"
          , "import @native"
          , ""
          , "enum Colour | Red | Green"
          ]
    r <- runFiles [ ("explicit.marr", explicit) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import explicit [enum Colour]"
      , ""
      , "funct main () : {Output} () = sayn Red"
      ]
    printed r `shouldBe` Right ["Red"]

  it "renames an enumerated type and keeps its constructors" $ do
    -- `as` renames the type this file writes; the constructors keep their
    -- declared names, because a constructor's name is not a type's.
    r <- runFiles [ ("palette.marr", palette) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import palette [enum Colour as Shade]"
      , ""
      , "funct describe (c Shade) : String ="
      , "  match c to"
      , "  | #Red => 'red'"
      , "  | #Green => 'green'"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (describe Red)"
      ]
    printed r `shouldBe` Right ["red"]

  it "takes a constructor named twice in one list as one name" $ do
    -- `Colour` already brings `Red`; naming it again is a second spelling of
    -- one declaration, not a second declaration.
    r <- runFiles [ ("palette.marr", palette) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import palette [enum Colour funct Red]"
      , ""
      , "funct main () : {Output} () = sayn Red"
      ]
    printed r `shouldBe` Right ["Red"]

  it "lets an export list rename one constructor and keep the others" $ do
    -- `enum Colour` alone would export `Red` as well; the explicit entry says
    -- `Crimson` instead, so the list has one spelling per value.
    let renamed = T.unlines
          [ "module Renamed [enum Colour funct Red as Crimson]"
          , "import @native"
          , ""
          , "enum Colour | Red | Green"
          ]
    r <- runFiles [ ("renamed.marr", renamed) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import renamed"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn Crimson;"
      , "  sayn Green"
      ]
    printed r `shouldBe` Right ["Red", "Green"]

  it "reports two enums of one constructor name" $ do
    -- Two enumerations in one namespace cannot both own `Red`: a pattern
    -- `#Red` would name a type the checker cannot decide.
    let other = T.unlines
          [ "module Other [enum Shade]"
          , "import @native"
          , ""
          , "enum Shade | Red | Blue"
          ]
    r <- runFiles
      [ ("palette.marr", palette)
      , ("other.marr", other)
      ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import palette"
      , "import other"
      ]
    case r of
      Left err -> err `shouldSatisfy` ("two imports bring `Red`" `isInfixOf`)
      Right _ -> expectationFailure "two constructors of one name must clash"

  it "keeps two enums of one constructor name apart when it is renamed" $ do
    -- A rename of the *type* leaves the constructor's name alone, and two
    -- `Red`s are still one name in one namespace.  The valve is naming the
    -- constructor itself and renaming it: the enum still arrives, its `Red`
    -- does not.
    let other = T.unlines
          [ "module Other [enum Shade]"
          , "import @native"
          , ""
          , "enum Shade | Red | Blue"
          ]
    r <- runFiles
      [ ("palette.marr", palette)
      , ("other.marr", other)
      ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import palette [enum Colour]"
      , "import other [enum Shade funct Red as Crimson]"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn Red;"
      , "  sayn Blue;"
      , "  sayn Crimson"
      ]
    printed r `shouldBe` Right ["Red", "Blue", "Red"]

  it "renames a type inside the operation of an imported effect" $ do
    -- `effect Writer out : Mode -> ()` names `Mode` in its signature, so a
    -- file that writes `Mode` as `Speed` must see the operation at `Speed`
    -- too; otherwise the handler clause would bind a type the file cannot name.
    let lib = T.unlines
          [ "module Lib [effect Writer enum Mode]"
          , "import @native"
          , ""
          , "enum Mode | Fast | Slow"
          , ""
          , "effect Writer"
          , "  out : Mode -> ()"
          , "end"
          ]
    r <- runFiles [ ("lib.marr", lib) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import lib [effect Writer as Save enum Mode as Speed]"
      , ""
      , "funct label (m Speed) : String ="
      , "  match m to"
      , "  | #Fast => 'fast'"
      , "  | #Slow => 'slow'"
      , ""
      , "funct main () : {Output} () ="
      , "  under Save to"
      , "    out Fast"
      , "  handle"
      , "  | out m => sayn (label m); resume ()"
      , "  | then x => x"
      ]
    printed r `shouldBe` Right ["fast"]

  it "renames a type inside an imported type alias" $ do
    let lib = T.unlines
          [ "module Lib [enum Colour type Colours]"
          , "import @native"
          , ""
          , "enum Colour | Red | Green"
          , ""
          , "type Colours = [Colour]"
          ]
    r <- runFiles [ ("lib.marr", lib) ] $ T.unlines
      [ "module Main"
      , "import @native"
      , "import lib [enum Colour as Shade type Colours as Tones]"
      , ""
      , "funct first (xs Tones) : Shade = head xs"
      , ""
      , "funct main () : {Output} () = sayn (first [Red, Green])"
      ]
    printed r `shouldBe` Right ["Red"]

