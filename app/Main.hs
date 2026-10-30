{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import qualified Data.Text as T
import System.IO (readFile')
import Elaborator (elaborate, ElabM, ElaborationError, ElabState (..))
import Parser (parseFromText, chunk)
import Control.Monad.State.Lazy (evalState)
import Control.Monad.Except (runExceptT)
import Utils (Pretty(..))
import Text.Printf (printf)
import Sexp (Sexp(..))
import System.Environment (getArgs)
import Unify (TypeCheckState(..), evalTypeCheckM)
import Infer (inferChunk)
import Interpreter (interpret)
import Config (resolveConfig)
import ErrorContext (toErrorText)
import Data.List (intercalate)

main :: IO ()
main = do
  runProg "scoping"
  runProg "rebind_shared"
  runProg "param_reentrancy"
  runProg "counter"
  runProg "imm_snapshot"
  runProg "imm_make"
  runProg "imm_recursion"
  runProg "imm_needs_read"
  runProg "compare"
  runProg "random_range"
  runProg "row_poly"
  runProg "under"

runProg :: String -> IO ()
runProg name = do
  printf "===[%s]===\n" name
  f <- T.pack <$> readFile' ("app/marr/" <> name <> ".marr")
  let c = elaborate <$> parseFromText chunk f
  case c of
    Left e -> putStrLn $ "Error infer " <> name <> ": " <> e
    Right elabAction -> do
      mapElabM 0 elabAction
        (\elabError -> putStrLn $ "748 | Elaboration error: " <> show elabError)
        (\c' -> do
          let pc  = pretty c'
          -- printf "Elaborated chunk pretty: \n%s\n" $ T.unpack pc
          -- printf "Elaborated chunk sexp: \n%s\n" $ sexp c'
          -- writeFile ("app/" <> name <> "/el.marr") $ T.unpack pc
          args <- getArgs
          let args' = map T.pack args
          -- Получаем начальный scope (тоже в TypeCheckM)
          let initState = TypeCheckState (0, 0, 0) 0 []
          case evalTypeCheckM (inferChunk args' c') initState of
            Left (stack, err) -> do
              putStrLn $ T.unpack $ T.concat [pretty err, "\n\n",
                  "Error stack: [", T.intercalate "\n" $ map toErrorText stack, "]"
                ]
            Right ic -> do
              -- writeFile ("app/" <> name <> "/ic.marr") $ printf $ T.unpack $ pretty ic
              ec <- interpret ic args
              printf "Interpreted %s.marr: \n\n%s\n" name $ T.unpack $ pretty ec
              -- writeFile ("app/" <> name <> "/ec.marr") $ T.unpack $ pretty ec
          pure ())

mapElabM :: Int -> ElabM a -> (ElaborationError -> b) -> (a -> b) -> b
mapElabM counter elabAction onError onSuccess = do
  let result = evalState (runExceptT elabAction) $ ElabState counter
  case result of
    Left elabError -> onError elabError
    Right elabSuccess -> onSuccess elabSuccess