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
  -- config <- resolveConfig
  f <- T.pack <$> readFile' "app/main.marr"
  let c = elaborate <$> parseFromText chunk f
  case c of
    Left e -> putStrLn $ "Error infer main: " <> e
    Right elabAction -> do
      mapElabM 0 elabAction
        (\elabError -> putStrLn $ "748 | Elaboration error: " <> show elabError)
        (\c' -> do
          let pc  = pretty c'
          printf "Elaborated chunk pretty: \n%s\n" $ T.unpack pc
          printf "Elaborated chunk sexp: \n%s\n" $ sexp c'
          writeFile "app/main_el.marr" $ T.unpack pc
          args <- getArgs
          let args' = map T.pack args
          -- Получаем начальный scope (тоже в TypeCheckM)
          let initState = TypeCheckState (0, 0, 0) 0 []
          case evalTypeCheckM (inferChunk args' c') initState of
            Left (stack, err) -> do
              putStrLn $ concat ["Type inference error: ", show err, "\n\n",
                  "Error stack: [", intercalate "\n" $ map (T.unpack . toErrorText) stack, "]"
                ]
            Right ic -> do
              writeFile "app/main_ic.marr" $ printf $ T.unpack $ pretty ic
              ec <- interpret ic args
              printf "Interpreted main.marr: \n\n%s\n" $ T.unpack $ pretty ec
              writeFile "app/main_ec.marr" $ T.unpack $ pretty ec
          pure ())

mapElabM :: Int -> ElabM a -> (ElaborationError -> b) -> (a -> b) -> b
mapElabM counter elabAction onError onSuccess = do
  let result = evalState (runExceptT elabAction) $ ElabState counter
  case result of
    Left elabError -> onError elabError
    Right elabSuccess -> onSuccess elabSuccess