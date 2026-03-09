{-# LANGUAGE LambdaCase #-}

module Eff (
  empty,
  label,
  labels,
  closedOfFlat,
  isEmpty,
  extractEffects,
  pureFunc,
  unionEffRows,
  pureEffDeclWithOps,
  fxAssignment,
  fxInput,
  fxOutput,
  fxIo,
  effInput,
  effOutput,
  effRandom,
  effTime,
  effIo,
  globalHandlerSig,
  globalHandler
) where
import Types
import Data.List (nub, sort)
import System.Random
import Numeric.Limits (minValue, maxValue)
import Text.Read (readEither)
import System.IO (hPutStrLn)
import GHC.IO.Handle.FD (stderr)
import GHC.IO (throwIO)
import Data.Char (chr)
import Control.Monad (replicateM)

empty :: EffRow
empty = EClosed []

label :: String -> EffCons
label l = (l, [])

labels :: [String] -> [EffCons]
labels = map label

closedOfFlat :: String -> EffRow
closedOfFlat l = EClosed [label l]

isEmpty :: EffRow -> Bool
isEmpty = \case EClosed [] -> True; _ -> False

extractEffects :: EffRow -> [EffCons]
extractEffects = \case
    EVar _ -> []
    EClosed fxs' -> fxs'
    EOpen fxs' _ -> fxs'

pureFunc :: Typ -> Typ -> Typ
pureFunc i o = TFunc (i, o, EClosed [])

unionEffRows :: EffRow -> EffRow -> EffRow
unionEffRows r1 r2 =
  let effects1 = extractEffects r1 in
  let effects2 = extractEffects r2 in

  let combinedEffects = sort $ nub $ effects1 ++ effects2 in

  case (r1, r2) of
    -- Если хотя бы один ряд открытый - результат открытый
    (EOpen _ v, _) -> EOpen combinedEffects v
    (_, EOpen _ v) -> EOpen combinedEffects v
    -- Если есть переменная, но нет открытого ряда
    (EVar _, _) -> r1
    (_, EVar _) -> r2
    -- Оба закрытые
    (EClosed _, EClosed _) -> EClosed combinedEffects

pureEffDeclWithOps :: String -> [(String, Func)] -> EffDecl
pureEffDeclWithOps name = EffDecl name []

fxAssignment, fxInput, fxOutput, fxIo :: EffRow
fxAssignment = closedOfFlat "Assignment"
fxInput = closedOfFlat "Input"
fxOutput = closedOfFlat "Output"
fxIo = unionEffRows fxInput fxOutput

effInput, effOutput, effRandom, effTime, effIo :: EffDecl
effInput = pureEffDeclWithOps "Input" [
    ("read_int", (TNil, TInt, EClosed [])),
    ("read_string", (TNil, TString, EClosed []))
  ]

effOutput = pureEffDeclWithOps "Output" [
    ("sayn", (TString, TNil, EClosed [])),
    ("say", (TString, TNil, EClosed []))
  ]

effRandom = pureEffDeclWithOps "Random" [
    ("random_int", (TNil, TInt, EClosed [])),
    ("random_float", (TNil, TFloat, EClosed [])),
    ("random_boolean", (TNil, TBoolean, EClosed [])),
    ("random_string", (TInt, TString, EClosed [])) -- N given random printable ASCII-characters
  ]

effTime = pureEffDeclWithOps "Time" [
    ("get_time_ms", (TNil, TInt, EClosed []))
  ]

effIo = EffAlias "Io" (EClosed [label "Input", label "Output", label "Random"])

globalHandlerSig :: HandlerSig
globalHandlerSig =
  let inp = closedOfFlat "Input"
      out = closedOfFlat "Output"
      rand = closedOfFlat "Random" in
  HandlerSig (label "Io") [
    ("read_int", (TNil, TInt, inp)),
    ("read_string", (TNil, TInt, inp)),
    ("sayn", (TString, TNil, out)),
    ("say", (TString, TNil, out )),
    ("random_int", (TNil, TInt, rand)),
    ("random_float", (TNil, TFloat, rand)),
    ("random_boolean", (TNil, TBoolean, rand)),
    ("random_string", (TInt, TString, rand))
  ]

globalHandler :: NativeBlock -> (Expr -> String) -> IO Handler
globalHandler bl exprToString =
  pure $ NativeHandler
    (label "Io")
    bl
    [
      ("read_int", -- read_int : () -> {Input} Int
        NativeLambda
          (NativeLambdaSign "_" (Just TNil) (Just TInt) $ closedOfFlat "Input")
          $ \_ -> do
            input <- getLine
            case readEither input of
              Left err -> do
                hPutStrLn stderr $ "Error reading Int: " ++ err
                error "Invalid Int input"
              Right n -> pure $ Int n),
      ("read_string", -- read_string : () -> {Input} String
        NativeLambda
          (NativeLambdaSign "_" (Just TNil) (Just TString) $ closedOfFlat "Input")
          $ \_ -> do
            input <- getLine
            case readEither input of
              Left err -> do
                hPutStrLn stderr $ "Error reading String: " ++ err
                error "Invalid String input"
              Right n -> pure $ String n),
      ("sayn", -- sayn : String -> {Output} ())
        NativeLambda
          (NativeLambdaSign "s" (Just TString) (Just TNil) $ closedOfFlat "Output")
          $ \s -> do
            print s
            pure Nil),
      ("say", -- say : String -> {Output} ())
        NativeLambda
          (NativeLambdaSign "s" (Just TString) (Just TNil) $ closedOfFlat "Output")
          $ \s -> do
            putStr $ show s
            pure Nil),
      ("random_int", -- random_int : () -> {Random} Int)
        NativeLambda
          (NativeLambdaSign "_" (Just TNil) (Just TInt) $ closedOfFlat "Random")
          $ \_ -> do Int <$> randomInt),
      ("random_float", -- random_float : () -> {Random} Float)
        NativeLambda
          (NativeLambdaSign "_" (Just TNil) (Just TFloat) $ closedOfFlat "Random")
          $ \_ -> do Float <$> randomFloat),
      ("random_boolean", -- random_boolean : () -> {Random} Boolean)
        NativeLambda
          (NativeLambdaSign "_" (Just TNil) (Just TBoolean) $ closedOfFlat "Random")
          $ \_ -> do Boolean <$> randomBool),
      ("random_string", -- random_string : () -> {Random} String)
        NativeLambda
          (NativeLambdaSign "n" (Just TInt) (Just TString) $ closedOfFlat "Random")
          $ \n -> do
              case n of
                Int n' -> do
                  chars <- replicateM n' (do
                    j <- randomIntFromTo 0 94
                    pure $ chr (33 + j))
                  pure $ String chars
                _ -> throwIO $ userError "Type error: random_string must accept Int parameter")
    ]
    Nothing
  where
    randomInt :: IO Int
    randomInt = randomRIO (minBound, maxBound)

    randomIntFromTo :: Int -> Int -> IO Int
    randomIntFromTo from to = randomRIO (from, to)

    -- Случайное Float в диапазоне [-maxFloat/2, maxFloat/2]
    randomFloat :: IO Float
    randomFloat = randomRIO (minValue, maxValue)

    -- Случайный Bool
    randomBool :: IO Bool
    randomBool = randomIO  -- или randomRIO (False, True)