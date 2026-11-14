-- | A small front-end driver: parse, elaborate and type-check one source file,
--   then print the typed IR or the first diagnostic.
--
--   Build it against the library while developing:
--
--   > stack ghc -- -package Marran -o tools/dbg.exe tools/Dbg.hs
--   > ./tools/dbg.exe path/to/program.marr
--
--   Unlike @marran-exe --run@ it accepts a path with directories and does not
--   interpret the result, which makes it the quickest way to look at what
--   inference produced for a snippet.
module Main (main) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Control.Monad.State.Lazy (evalState)
import Control.Monad.Except (runExceptT)
import Elaborator (elaborate, ElabState(..))
import Parser (chunk, parseFromTextNamed)
import Infer (inferChunk)
import Unify (evalTypeCheckM, TypeCheckState(..))
import TypedIR (Chunk(..))
import qualified Scope
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath (takeFileName)
import Utils (Pretty(..))

main :: IO ()
main = do
  args <- getArgs
  path <- case args of
    (p : _) -> pure p
    [] -> do
      putStrLn "usage: dbg <file.marr>"
      exitFailure
  src <- TIO.readFile path
  case parseFromTextNamed (takeFileName path) chunk src of
    Left e -> putStrLn e
    Right parsed ->
      case evalState (runExceptT (elaborate parsed)) (ElabState 0) of
        Left e -> putStrLn (T.unpack (pretty e))
        Right elab ->
          case evalTypeCheckM (inferChunk [] elab) (TypeCheckState (0,0,0) 0 []) of
            Left e -> print e
            Right ir -> putStrLn (T.unpack (pretty ir))
