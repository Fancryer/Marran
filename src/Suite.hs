{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The executable part of the test suite: every example program of the paper
--   is elaborated, type-checked and interpreted, and the lines it prints are
--   compared with the expected output.  The mutation-event check of the
--   interpreter is enabled for these runs, so an unlicensed event fails the
--   suite as well.  The module is used both by the executable (@marran-exe@)
--   and by the Hspec driver, so @stack test@ covers the examples too.
module Suite (
    Case
  , cases
  , rejectedProgram
  , runSuite
  , runProgram
  , runProgramWithInput
  , runSourceWithInput
  , withModuleHeader
  , programPath
  ) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Control.Exception (bracket, finally, try)
import Control.Monad (filterM)
import Control.Monad.State.Lazy (evalState)
import Control.Monad.Except (runExceptT)
import Data.List (isInfixOf, isPrefixOf, isSuffixOf, intercalate)
import System.Directory (doesFileExist, getTemporaryDirectory, removeFile)
import System.Environment (setEnv)
import System.IO
import GHC.IO.Handle (hDuplicate, hDuplicateTo)

import Elaborator (elaborate, ElabState(..))
import ErrorContext (
    ErrorFrame(..), renderError, insertSource, emptySourceMap,
    renderDiagnostic, diagnostic, Severity(SevError), renderErrorWith, primaryLabel,
    Diagnostic(..), innermost
  )
import Infer (inferChunk)
import IntInterpreter (interpret, InterpError(..), errorCodeOf)
import Parser (parseFromTextNamed, chunk)
import Unify (TypeCheckState(..), evalTypeCheckM, errorCode)
import Utils (Pretty(..))

-- | One runnable program and the lines it must print.
type Case = (FilePath, [String])

-- | The programs that must run, with their expected output.
cases :: [Case]
cases =
  [ ("scoping",           ["1"])
  , ("rebind_shared",     ["2"])
  , ("param_reentrancy",  ["3", "4", "3"])
  , ("counter",           ["1", "2"])
  , ("quote",             ["10", "30", "15", "45"])
  , ("imm_snapshot",      ["6"])
  , ("imm_make",          ["0", "0"])
  , ("imm_recursion",     ["15"])
  , ("row_poly",          ["hello", "42"])
  , ("under",             ["1"])
  , ("effect_in_function", ["3"])
  , ("empty_arrays",      ["[[1], []]", "[[], [1]]", "[]"])
  , ("record_update",     ["#{val a = 1; val b = 2}", "#{val a = 1; val b = 2; val c = 3}", "1", "#{val a = 10; val b = 2}", "1"])
  , ("path_assign",       ["2", "10", "21"])
  , ("lazy_and",          ["false"])
  , ("enums",             ["Some 5", "None", "5", "none", "cdef", "two"])
  , ("long_loop",         ["30000", "0", "300000"])
  , ("collections",       [ "5"
                          , "hello"
                          , "3"
                          , "4"
                          , "6"
                          , "2"
                          , "10"
                          , "1"
                          , "3"
                          , "[2, 3]"
                          , "[1, 2]"
                          , "[2, 3]"
                          , "[2, 4, 6]"
                          , "[2, 3]"
                          , "false"
                          , "true"
                          , "10"
                          , "24"
                          , "[1, 2, 3]"
                          , "[(1, a), (2, b)]"
                          , "20"
                          , "`at`: index 5 is out of range for an array of 1 element"
                          , "9"
                          ])
  , ("stdlib_effects",    [ "ok"
                          , "0"
                          , "true"
                          , "11"
                          , "42"
                          , "-4"
                          , "0"
                          , "false"
                          ])
  , ("stdlib",            [ "3 2 24 3 1"
                          , "3.75 0.25 3 3.0"
                          , "abcd 5 bcd [a, b, c] a-b"
                          , "x ABC abc true heLLo"
                          , "false true false true"
                          , "false true"
                          , "3 5"
                          ])
  ]

-- | The program that the type checker must reject; the error must name @Read@.
rejectedProgram :: FilePath
rejectedProgram = "imm_needs_read"

-- | The file a name refers to, if there is one.
--
--   @--run@ takes either the name of a bundled example (@guess@) or a path to
--   any Mårran file (@scratch/guess.marr@, @D:\scratch\guess.marr@).  A path
--   is tried as given first, so a file outside @app/marr@ -- and a name that
--   is relative to the reader's directory -- works; the bundled directories
--   are tried afterwards, which keeps the short form working from the
--   repository root and from a build directory.
programPath :: FilePath -> IO (Maybe FilePath)
programPath name = do
  let given = programFileName name
      -- A name with a separator is a path the reader wrote on purpose: looking
      -- for it under `app/marr` as well would be guessing.
      hasDir = any (`elem` ("/\\" :: String)) name
      candidates = [ given ]
        <> [ dir <> given | not hasDir
                          , dir <- ["app/marr/", "../app/marr/", "../../app/marr/"] ]
  found <- filterM doesFileExist candidates
  pure $ case found of
    (p:_) -> Just p
    []    -> Nothing

-- | The name a program is reported under when it cannot be found.
programFileName :: FilePath -> FilePath
programFileName name = if ".marr" `isSuffixOf` name then name else name <> ".marr"

-- | Elaborate, type-check and interpret a program.  Everything it prints is
--   captured and returned; the result is 'Left' on a parse, elaboration or
--   type error.
runProgram :: FilePath -> IO (Either String String)
runProgram name = runProgramWithInput name ""

-- | 'runProgram' with a fixed standard input.
--
--   A program that reads input (such as a loop driven by @read_int@) needs a
--   deterministic answer stream; the test harness redirects @stdin@ from a
--   temporary file for the duration of the run.
runProgramWithInput :: FilePath -> String -> IO (Either String String)
runProgramWithInput name input =
  programPath name >>= \case
    Nothing -> pure $ Left $ "program not found: " ++ programFileName name
    Just path -> do
      src <- T.pack <$> readFile path
      runSource path input src

-- | Interpret a source that is already a whole file.
--
--   A file read from disk must declare its module itself: the header is part
--   of the language, and a file without one is a syntax error, not an
--   anonymous program.  Tests build their programs differently -- see
--   'runSourceWithInput'.
runSource :: FilePath -> String -> T.Text -> IO (Either String String)
runSource path input src = do
  -- The source map is what lets the renderer quote the offending lines; the
  -- name of the file in the map must match the one recorded in the spans.
  let sources = insertSource (T.pack path) src emptySourceMap
  case elaborate <$> parseFromTextNamed path chunk src of
    Left e -> pure $ Left e
    Right elabAction ->
      case evalState (runExceptT elabAction) (ElabState 0) of
        Left e -> pure . Left . T.unpack $
          renderDiagnostic sources (diagnostic SevError Nothing (pretty e))
        Right c' ->
          case evalTypeCheckM (inferChunk [] c') (TypeCheckState (0, 0, 0) 0 []) of
            Left (stack, err) ->
              pure . Left . T.unpack $
                renderErrorWith sources (innermost stack) (errorCode err) (pretty err) stack
            Right ic -> do
              r <- captureStdoutWith (withStdin input (interpret ic []))
              case r of
                (Left err, _) -> pure . Left . T.unpack $
                  renderDiagnostic sources ((diagnostic SevError (errorCodeOf err) (pretty err)) {
                    diagLabels = [primaryLabel (ieSpan err) ""]
                  })
                (Right _, out) -> pure $ Right out

-- | 'runSource' for a program written inside a test.
--
--   The header is added when the source has none, so a test shows only the
--   part it is about; the preamble goes on the first line, which keeps the
--   line numbers of the test's own body as written.
runSourceWithInput :: FilePath -> String -> T.Text -> IO (Either String String)
runSourceWithInput path input src = runSource path input (withModuleHeader src)

-- | Put @module Main@ in front of a source that has no header.
--
--   A test keeps a small program next to its assertion, and repeating the
--   header in every one of them would hide the program under boilerplate.  The
--   header goes on the first line and the program follows on the same line, so
--   the line numbers a test quotes for its own body do not move.
withModuleHeader :: T.Text -> T.Text
withModuleHeader src
  | startsWithHeader src = src
  | otherwise = T.concat ["module Main ", src]

-- | Does the source already declare its module?  Leading blank lines and the
--   @//|@ comments the examples start with are skipped, because the header is
--   the first thing the grammar wants to see, not the first line.
startsWithHeader :: T.Text -> Bool
startsWithHeader src = "module" `T.isPrefixOf` T.stripStart (stripLeadComments src)

-- | Drop the whole-line @//|@ comments at the top of a source.
stripLeadComments :: T.Text -> T.Text
stripLeadComments src =
  case T.lines src of
    [] -> src
    ls -> T.intercalate "\n" (go ls)
  where
    go (l : rest)
      | "//|" `T.isPrefixOf` T.stripStart l = go rest
      | T.null (T.strip l) = go rest
      | otherwise = l : rest
    go [] = []

-- | Run an action with @stdin@ reading from the given string.
withStdin :: String -> IO a -> IO a
withStdin input action
  | null input = action
  | otherwise = do
      tmp <- getTemporaryDirectory
      (path, h) <- openTempFile tmp "marran-in.txt"
      hPutStr h input
      hClose h
      hin <- openFile path ReadMode
      saved <- hDuplicate stdin
      hDuplicateTo hin stdin
      -- Windows will not delete the file while a duplicate of it is still the
      -- process's standard input, so the console is restored before cleanup.
      result <- action `finally` hDuplicateTo saved stdin
      hClose saved
      hClose hin
      removeFile path
      pure result

-- | Run an action with @stdout@ redirected to a temporary file and return what
--   was written to it.
captureStdout :: IO a -> IO String
captureStdout action = snd <$> captureStdoutWith action

-- | 'captureStdout' that also keeps the action's result.
captureStdoutWith :: IO a -> IO (a, String)
captureStdoutWith action = do
  tmp <- getTemporaryDirectory
  (path, h) <- openTempFile tmp "marran-out.txt"
  let cleanup = do
        hClose h
        r <- try (removeFile path) :: IO (Either IOError ())
        either (const (pure ())) pure r
  bracket (hDuplicate stdout) (\saved -> hDuplicateTo saved stdout >> hClose saved) $ \saved ->
    (do hDuplicateTo h stdout
        hSetBuffering stdout LineBuffering
        result <- action
        hFlush stdout
        hDuplicateTo saved stdout
        hSeek h AbsoluteSeek 0
        out <- T.unpack <$> TIO.hGetContents h
        pure (result, out))
      `finally` cleanup

-- | Run the whole suite; returns 'True' when every check passes.
runSuite :: IO Bool
runSuite = do
  setEnv "MARRAN_CHECK_EVENTS" "1"
  putStrLn "Programs:"
  results <- mapM check cases
  rejectedOk <- checkRejected
  let failures = [ n | (n, ok) <- results, not ok ]
                  ++ [ rejectedProgram | not rejectedOk ]
      total = length cases + 1
  putStrLn ""
  if null failures
    then putStrLn $ "All " ++ show total ++ " programs behave as expected."
    else putStrLn $ "FAILED: " ++ intercalate ", " failures
  pure (null failures)

check :: Case -> IO (FilePath, Bool)
check (name, expected) = do
  r <- runProgram name
  let (ok, printed, note) = case r of
        Left err  -> (False, [] :: [String], take 300 err)
        Right out ->
          let ls = lines out
              violations = filter ("EVENT-VIOLATION" `isPrefixOf`) ls
              printed' = filter (not . isReportLine) ls
          in (null violations && printed' == expected, printed', intercalate "; " violations)
  putStrLn $ concat
    [ "  ", pad name
    , if ok then "ok  " else "FAILED"
    , " expected " ++ show expected
    , ", got " ++ show printed
    ]
  if null note then pure () else putStrLn $ "    " ++ note
  pure (name, ok)

checkRejected :: IO Bool
checkRejected = do
  r <- runProgram rejectedProgram
  let ok = case r of
        Left err -> "Read" `isInfixOf` err
        Right _  -> False
  putStrLn $ "  " ++ pad rejectedProgram
    ++ (if ok then "rejected, as intended" else "FAILED")
  case r of
    Left err | not ok -> putStrLn $ "    " ++ take 400 err
    Right out         -> putStrLn $ "    output: " ++ take 400 out
    _                 -> pure ()
  pure ok

-- | Lines of the interpreter's own report, not of the program.
isReportLine :: String -> Bool
isReportLine l = "EVENTS:" `isPrefixOf` l || "EVENT-VIOLATION" `isPrefixOf` l

pad :: String -> String
pad s = s ++ replicate (max 1 (18 - length s)) ' '
