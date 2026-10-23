{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unused-top-binds -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}

module Spec (
  spec,
  printExps
) where

import Parser (parseTokens, Parser, exp, parseTokensUnposed, effCons, effRow, chunk, typ, block, parseFromText)
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)
import Test.QuickCheck (
    Positive (Positive),
    Property,
    Gen,
    forAll,
    Testable (property),
    listOf1,
    elements,
    sized,
    oneof,
    listOf,
    frequency,
    choose,
    counterexample,
    vectorOf
  )
import qualified Data.Text as T
import Lexer(Token(..), Keyword (..), LToken)
import Numeric(showHex)
import Test.QuickCheck.Arbitrary (Arbitrary(arbitrary))
import Data.Scientific(toRealFloat, Scientific, scientific)
import Text.Megaparsec(MonadParsec (eof), runParser, errorBundlePretty)
import Data.Text(Text)
import Ast(
    Literal(..),
    Exp(..),
    Atom(..),
    Number(NInt, NFloat),
    ArrayLiteral(ArrayLiteral),
    ArrayEntry(AEExp, AEBlock),
    Block(Block),
    BlockStat(BExp, BAssign, BBindDef),
    Assign(Assign),
    PathExp(PathExp),
    BindDef(BindDef),
    ConstantQualifier(Val, Var, Imm),
    LambdaParam(LambdaParam),
    Typ(..),
    EffRow(ERAlias, ERSugar),
    RecordTyp(RecordTyp),
    EffRowEntry(EREEffCons, EREEffRow),
    EffCons(EffCons),
    RecordTypProp(RecordTypProp),
    TypeParams (..),
    TypeApps(TypeApps),
    EffApps(EffApps),
    TypeArg(..),
    RecordTypeArg (RecordTypeArg),
    RecordTypeArgProp(RecordTypeArgProp),
    EffArg(EACons, EARow),
    LetPattern(LPATom, LPParam),
    AtomLetPattern(..),
    AtomLetPatternRecordProp(AtomLetPatternRecordProp),
    HandlerClause(HandlerClause),
    EffParams (EffParams),
    Under(..),
    LambdaLiteral(LambdaLiteral),
    RecordLiteral(RecordLiteral),
    LambdaHead(LambdaHead), Funct (Funct), ECons (..)
  )
import Utils (Pretty(pretty))
import Data.Int (Int64)
import Control.Monad (foldM)
import Data.List ((\\))
import Text.Printf (printf)
import Sexp (Sexp (..))
import Elaborator (elaborate, elaborateEffRow, ElabState (..), ElabM, ElaborationError, elaborateExpr, ElabEnv (..), elaborateBlock)
import System.IO (readFile')
import Control.Monad.State.Lazy (runState, evalState)
import Control.Monad.Except (runExceptT)
import Types (TopLevelStat(SFunctDef), Expr (..), Lambda (..))
import Scope (globalScope)
import Infer (inferExpr, inferBlock, inferChunk, InferResult (..))
import qualified Data.Map as Map
import qualified System.Environment as IO
import System.Environment (getArgs)
import Unify (TypeCheckState(..), evalTypeCheckM)
import Interpreter (interpret)

genName :: Gen Text
genName = do
  len <- frequency [
      (5, choose (1, 3)),   -- короткие имена (1-3 буквы) - часто
      (3, choose (4, 7)),   -- средние (4-7) - реже
      (1, choose (8, 12)),  -- длинные (8-12) - ещё реже
      (1, choose (13, 20))  -- очень длинные - совсем редко
    ]
  let genChar :: Gen Char
      genChar = frequency [
          (99, elements ['a'..'z']),        -- 70% - буквы
          (1, elements "_+/%|&^~<=>.*!?-") -- 30% - операторы (все вместе)
        ]
  T.pack <$> vectorOf len genChar

genText :: Gen Text
genText = do
  let allowedChars = ['\0'..'\127'] \\ ['\'']
  let escapeSeq = elements ["\\\\", "\\'"]
  let regularChar = elements $ allowedChars \\ ['\\']
  T.concat <$> listOf (oneof [T.singleton <$> regularChar, escapeSeq])

maybeGen :: Gen a -> Gen (Maybe a)
maybeGen gen = frequency [
    (1, pure Nothing),
    (1, Just <$> gen)
  ]

instance Arbitrary Literal where arbitrary = sized genLiteral

genLiteral :: Int -> Gen Literal
genLiteral 0 =  LAtom <$> arbitrary
genLiteral n = oneof [
    LAtom <$> arbitrary,
    LArray <$> sub genArray,
    LLambda <$> sub genLambda,
    LRecord <$> sub genRecord
  ]
  where sub f = f $ n `div` 2

instance Arbitrary LambdaLiteral where arbitrary = sized genLambda

-- LambdaLiteral (Maybe TypeParams) (Maybe EffParams) (Maybe LambdaHead) Block
genLambda :: Int -> Gen LambdaLiteral
genLambda 0 = LambdaLiteral <$> arbitrary <*> arbitrary <*> maybeGen (genLambdaHead 0) <*> genBlock 0
genLambda n =
  LambdaLiteral <$> arbitrary <*> arbitrary <*> maybeGen (genLambdaHead $ n `div` 2) <*> genBlock (n `div` 2)

instance Arbitrary LambdaHead where arbitrary = sized genLambdaHead

genLambdaHead :: Int -> Gen LambdaHead
genLambdaHead 0 = LambdaHead [] <$> maybeGen (genTopTyp 0)
genLambdaHead n =
  LambdaHead <$> listOf (genLambdaParam $ n `div` 2) <*> maybeGen (genTopTyp $ n `div` 2)

instance Arbitrary RecordLiteral where arbitrary = sized genRecord

-- RecordLiteral (Maybe Exp) [BindDef]
genRecord :: Int -> Gen RecordLiteral
genRecord 0 = RecordLiteral <$> maybeGen (genTopExp 0) <*> listOf1 arbitrary
genRecord n = RecordLiteral <$> maybeGen (genTopExp $ n `div` 2) <*> listOf1 (genBindDef $ n `div` 2)

instance Arbitrary ArrayLiteral where arbitrary = sized genArray

genArray :: Int -> Gen ArrayLiteral
genArray n = ArrayLiteral <$> listOf (case n of 0 -> genArrayEntry 0; _ -> genArrayEntry $ n `div` 2)

instance Arbitrary ArrayEntry where arbitrary = sized genArrayEntry

genArrayEntry :: Int -> Gen ArrayEntry
genArrayEntry 0 = oneof [AEExp <$> genTopExp 0, AEBlock <$> genBlock 0]
genArrayEntry n = oneof [
    AEExp <$> genTopExp (n `div` 2),
    AEBlock <$> genBlock (n `div` 2)
  ]

instance Arbitrary Block where arbitrary = sized genBlock

genBlock :: Int -> Gen Block
genBlock 0 = Block [] <$> genTopExp 0
genBlock n = do
  stats <- listOf $ genBlockStat (n `div` 2)
  Block stats <$> genTopExp (n `div` 2)

instance Arbitrary BlockStat where arbitrary = sized genBlockStat

genBlockStat :: Int -> Gen BlockStat
genBlockStat 0 = oneof [
    BExp <$> genTopExp 0,
    BAssign <$> genAssign 0,
    BBindDef <$> genBindDef 0
  ]
genBlockStat n = oneof [
    BExp <$> sub genTopExp,
    BAssign <$> sub genAssign,
    BBindDef <$> sub genBindDef
  ]
  where sub f = f $ n `div` 2

instance Arbitrary Assign where arbitrary = sized genAssign

genAssign :: Int -> Gen Assign
genAssign 0 = (Assign {-. Left -}<$> genName) <*> genTopExp 0
genAssign n =
  Assign
    <$> genName {-oneof [
      Left <$> genName,
      Right <$> genPathExp (n `div` 2)
    ]-}
    <*> genTopExp (n `div` 2)

instance Arbitrary PathExp where arbitrary = sized genPathExp

genPathExp :: Int -> Gen PathExp
genPathExp 0 = PathExp <$> genTopExp 0 <*> listOf1 genName
genPathExp n = PathExp <$> genTopExp (n `div` 2) <*> listOf1 genName

instance Arbitrary BindDef where arbitrary = sized genBindDef

genBindDef :: Int -> Gen BindDef
genBindDef 0 = BindDef <$> arbitrary <*> genLambdaParam 0 <*> genTopExp 0
genBindDef n = BindDef <$> arbitrary <*> genLambdaParam (n `div` 2) <*> genTopExp (n `div` 2)

instance Arbitrary ConstantQualifier where
  arbitrary = oneof [pure Val, pure Var, pure Imm]

genTypAtom :: Int -> Gen Typ
genTypAtom 0 = oneof [TFlat <$> genName, pure Ast.TNil, TVar <$> genName]
genTypAtom n = oneof [
    TFlat <$> genName,
    pure Ast.TNil,
    TVar <$> genName,
    TArray <$> sub genTopTyp,
    TRecord <$> sub genRecordTyp,
    TGenericAlias <$> genName <*> sub genTypeApps,
    TParen <$> sub genTopTyp
  ]
  where sub f = f $ n `div` 2

genTypComma :: Int -> Gen Typ
genTypComma 0 = genTypAtom 0
genTypComma n = frequency [
    (3, genTypAtom n),
    (1, TPair <$> genTypAtom (n `div` 2) <*> genTypComma (n `div` 2))
  ]

genTypArrow :: Int -> Gen Typ
genTypArrow 0 = genTypComma 0
genTypArrow n = frequency [
    (3, genTypComma n),
    (1, TFunct <$> (Funct <$> sub genTypComma <*> sub genTypArrow <*> sub genEffRow))
  ]
  where sub f = f $ n `div` 2

genTopTyp :: Int -> Gen Typ
genTopTyp 0 = genTypArrow 0
genTopTyp n = frequency [
    (4, genTypArrow n),
    (1, TForall <$> arbitrary <*> arbitrary <*> genTopTyp (n `div` 2))
  ]

instance Arbitrary Typ where arbitrary = sized genTopTyp

instance Arbitrary EffRow where arbitrary = sized genEffRow

genEffRow :: Int -> Gen EffRow
genEffRow 0 = ERAlias <$> genName
genEffRow n = ERSugar <$> listOf (genEffRowEntry $ n `div` 2) <*> maybeGen genName

instance Arbitrary EffRowEntry where arbitrary = sized genEffRowEntry

genEffRowEntry :: Int -> Gen EffRowEntry
genEffRowEntry 0 = EREEffCons <$> arbitrary
genEffRowEntry n = oneof [
    EREEffCons <$> arbitrary,
    EREEffRow <$> genEffRow (n `div` 2)
  ]

instance Arbitrary EffCons where
  arbitrary = EffCons <$> arbitrary

instance Arbitrary ECons where
  arbitrary = ECons <$> genName <*> maybeGen arbitrary

instance Arbitrary RecordTyp where arbitrary = sized genRecordTyp

genRecordTyp :: Int -> Gen RecordTyp
genRecordTyp 0 = pure $ RecordTyp []
genRecordTyp n = RecordTyp <$> listOf1 (genRecordTypProp $ n `div` 2)

instance Arbitrary RecordTypProp where arbitrary = sized genRecordTypProp

genRecordTypProp :: Int -> Gen RecordTypProp
genRecordTypProp n =
  RecordTypProp <$> arbitrary <*> genName <*> genTopTyp (if n == 0 then 0 else n `div` 2)

instance Arbitrary TypeParams where
  arbitrary = do
    n <- frequency [
        (4, choose (1, 3)),
        (2, choose (4, 5)),
        (1, choose (6, 8))
      ]
    TypeParams <$> vectorOf n genName

instance Arbitrary EffParams where
  arbitrary = do
    n <- frequency [
        (4, choose (1, 3)),
        (2, choose (4, 5)),
        (1, choose (6, 8))
      ]
    EffParams <$> vectorOf n genName

instance Arbitrary TypeApps where arbitrary = sized genTypeApps

genTypeApps :: Int -> Gen TypeApps
genTypeApps n = TypeApps <$> listOf (genTopTypeArg $ n `div` 2)

instance Arbitrary EffApps where arbitrary = sized genEffApps

genEffApps :: Int -> Gen EffApps
genEffApps n = EffApps <$> listOf (genEffArg $ n `div` 2)

instance Arbitrary EffArg where arbitrary = sized genEffArg

genEffArg :: Int -> Gen EffArg
genEffArg 0 = EACons <$> arbitrary
genEffArg n = oneof [
    EACons <$> arbitrary,
    EARow <$> genEffRow (n `div` 2)
  ]

genTypeArgAtom :: Int -> Gen TypeArg
genTypeArgAtom 0 = oneof [TAFlat <$> genName, pure TANil, TAMeta <$> genName]
genTypeArgAtom n = oneof [
    TAFlat <$> genName,
    pure TANil,
    TAMeta <$> genName,
    TAArray <$> sub genTopTypeArg,
    TARecord <$> sub genRecordTypeArg,
    TAGenericAlias <$> genName <*> sub genTypeApps,
    TAParen <$> sub genTopTypeArg
  ]
  where sub f = f $ n `div` 2

genTypeArgComma :: Int -> Gen TypeArg
genTypeArgComma 0 = genTypeArgAtom 0
genTypeArgComma n = frequency [
    (3, genTypeArgAtom $ n `div` 2),
    (1, TAPair <$> genTypeArgAtom (n `div` 2) <*> genTypeArgComma (n `div` 2))
  ]

genTopTypeArg :: Int -> Gen TypeArg
genTopTypeArg 0 = genTypeArgComma 0
genTopTypeArg n = frequency [
    (3, sub genTypeArgComma),
    (1, TAFunct <$> sub genTypeArgComma <*> sub genTopTypeArg)
  ]
  where sub f = f $ n `div` 2

instance Arbitrary TypeArg where arbitrary = sized genTopTypeArg

-- genTypeArg :: Int -> Gen TypeArg
-- genTypeArg 0 = oneof [
--     TAFlat <$> genName,
--     pure TANil,
--     TAMeta <$> genName
--   ]

-- genTypeArg n = oneof [
--     TAArray <$> subT,
--     TAPair <$> subT <*> subT,
--     TAFunct <$> subT <*> subT,
--     TARecord <$> sub genRecordTypeArg,
--     TAGenericAlias <$> genName <*> sub genTypeApps
--   ]
--   where
--     sub f = f $ n `div` 2
--     subT = sub genTypeArg

instance Arbitrary RecordTypeArg where arbitrary = sized genRecordTypeArg

genRecordTypeArg :: Int -> Gen RecordTypeArg
genRecordTypeArg 0 = pure $ RecordTypeArg []
genRecordTypeArg n = RecordTypeArg <$> listOf1 (genRecordTypeArgProp $ n `div` 2)

instance Arbitrary RecordTypeArgProp where arbitrary = sized genRecordTypeArgProp

genRecordTypeArgProp :: Int -> Gen RecordTypeArgProp
genRecordTypeArgProp n =
  RecordTypeArgProp <$> arbitrary <*> genName <*> genTopTypeArg (if n == 0 then 0 else n `div` 2)

instance Arbitrary Atom where
  arbitrary = oneof [
      AString <$> genText,
      ANumber <$> arbitrary,
      pure ANil,
      ABoolean <$> arbitrary
    ]

instance Arbitrary Number where
  arbitrary = oneof [
      NInt <$> choose (0, toInteger (maxBound :: Int64)),
      NFloat <$> arbitrary
    ]

instance Arbitrary Scientific where
  arbitrary = scientific <$> choose (0, 10 ^ (6 :: Integer)) <*> choose (-10, 10)

instance Arbitrary Exp where arbitrary = sized genTopExp

genAtomExp :: Int -> Gen Exp
genAtomExp 0 = oneof [ELiteral <$> genLiteral 0, EName <$> genName]

genAtomExp n =
  oneof [
    ELiteral <$> sub genLiteral,
    EName <$> genName,
    EPair <$> subAtom <*> subAtom,
    EParen <$> sub genBlock
  ]
  where
    sub f = f $ n `div` 2
    subAtom = sub genAtomExp

genApplyExp :: Int -> Gen Exp
genApplyExp n = do
  k <- choose (0, 2)
  foldl EApply <$> subA <*> vectorOf k subA
  where subA = genAtomExp (n `div` 2)

genPostfixExp :: Int -> Gen Exp
genPostfixExp n = do
  base <- sub genApplyExp
  k <- choose (0, 2)
  foldM addPostfix base [1..k :: Integer]
  where
    addPostfix e _ =
      oneof [
        EPropAccess e <$> genName,
        EWith e <$> sub genTypeApps <*> sub genEffApps
      ]
    sub f = f $ n `div` 2

genInfixExp :: Int -> Gen Exp
genInfixExp 0 = genPostfixExp 0
genInfixExp n =
  oneof [
    genPostfixExp $ n `div` 2,
    EBacktick <$> genName <*> sub <*> sub,
    EDollar <$> sub <*> sub
  ]
  where sub = genPostfixExp $ n `div` 2

genPrefixExp :: Int -> Gen Exp
genPrefixExp 0 = genInfixExp 0
genPrefixExp n =
  frequency [
    (8, genInfixExp n),
    (1, EResume <$> genPrefixExp (n `div` 2))
  ]

genTopExp :: Int -> Gen Exp
genTopExp 0 = genPrefixExp 0
genTopExp n =
  frequency [
    (4, genPrefixExp $ n `div` 2),
    (1, EIfThenElse <$> subE <*> subE <*> subE),
    (1, ELet <$> sub genLetPattern <*> subE <*> subE),
    (1, EUnder <$> sub genUnder)
  ]
  where
    sub f = f $ n `div` 2
    subE = sub genTopExp

-- genExp :: Int -> Gen Exp
-- genExp 0 = oneof [ELiteral <$> genLiteral 0, EName <$> genName]
-- genExp n =
--   oneof [
--     ELiteral <$> sub genLiteral,
--     EName <$> genName,
--     EApply <$> subE <*> subE,
--     EPair <$> subE <*> subE,
--     EDollar <$> subE <*> subE,
--     ELet <$> sub genLetPattern <*> subE <*> subE,
--     EBacktick <$> genName <*> subE <*> subE,
--     EPropAccess <$> subE <*> genName,
--     EIfThenElse <$> subE <*> subE <*> subE,
--     EUnder <$> sub genUnder,
--     EResume <$> subE,
--     EParen <$> sub genBlock,
--     EWith <$> subE <*> sub genTypeApps <*> sub genEffApps
--   ]
--   where
--     sub f = f $ n `div` 2
--     subE = sub genExp

instance Arbitrary HandlerClause where arbitrary = sized genHandlerClause

genHandlerClause :: Int -> Gen HandlerClause
genHandlerClause n =
  HandlerClause <$> genName <*> listOf1 genName <*> genBlock (case n of 0 -> 0; _ -> n `div` 2)

instance Arbitrary Under where arbitrary = sized genUnder

genUnder :: Int -> Gen Under
genUnder 0 = Under <$> arbitrary <*> genBlock 0 <*> pure [] <*> genName <*> genBlock 0
genUnder n = do
      a <- arbitrary
      b <- subB
      hc <- subHC
      cs <- listOf subHC
      let cs' = [hc] <> cs
      Under a b cs' <$> genName <*> subB
  where
    sub f = f $ n `div` 2
    subB = sub genBlock
    subHC = sub genHandlerClause


instance Arbitrary LetPattern where arbitrary = sized genLetPattern

genLetPattern :: Int -> Gen LetPattern
genLetPattern n = oneof [
    LPATom <$> sub genAtomLetPattern,
    LPParam <$> sub genLambdaParam
  ]
  where sub f = f $ n `div` 2

instance Arbitrary AtomLetPattern where arbitrary = sized genAtomLetPattern

genAtomLetPattern :: Int -> Gen AtomLetPattern
genAtomLetPattern 0 = oneof [pure ALPNil, pure ALPUnderscore]
genAtomLetPattern n = oneof [
    pure ALPNil,
    pure ALPUnderscore,
    ALPPair <$> subLP <*> subLP,
    ALPParen <$> subLP,
    ALPRecord <$> listOf1 (genAtomLetPatternRecordProp $ n `div` 2)
  ]
  where subLP = genLetPattern $ n `div` 2

instance Arbitrary AtomLetPatternRecordProp where arbitrary = sized genAtomLetPatternRecordProp

genAtomLetPatternRecordProp :: Int -> Gen AtomLetPatternRecordProp
genAtomLetPatternRecordProp n = do
  cq <- arbitrary
  lp <- genLambdaParam $ n `div` 2
  AtomLetPatternRecordProp cq lp <$> maybeGen (genAtomLetPattern $ n `div` 2)

instance Arbitrary LambdaParam where arbitrary = sized genLambdaParam

genLambdaParam :: Int -> Gen LambdaParam
genLambdaParam n = LambdaParam <$> genName <*> maybeGen (genTopTyp $ n `div` 2)

parseExpFromText :: Text -> Either String Exp
parseExpFromText = parseFromText Parser.exp

prop_roundTripExp :: Exp -> Property
prop_roundTripExp e =
  case parseExpFromText (pretty e) of
    Left err ->
      counterexample err False
    Right e' ->
      counterexample ("input show:  " <> show e) $
      counterexample ("got show:    " <> show e') $
      counterexample ("expect show: " <> show e) $

      counterexample ("input pretty:  " <> T.unpack (pretty e)) $
      counterexample ("got pretty:    " <> T.unpack (pretty e')) $
      counterexample ("expect pretty: " <> T.unpack (pretty e)) $

      counterexample ("input sexp:  " <> sexp e) $
      counterexample ("got sexp:    " <> sexp e') $
      counterexample ("expect sexp: " <> sexp e) $

      property (e' == e)

replaces :: [(Text, Text)] -> Text -> Text
replaces = flip $ foldl' $ flip $ uncurry T.replace

spec :: Spec
spec = do
  describe "Lexer" $ do
    it "parses arbitrary positive decimal integers" $ property prop_decInt
    it "parses decimal integer" $ parseTokensUnposed "123" `shouldBe` Right [TInt 123]
    it "parses decimal with underscores" $ parseTokensUnposed "1_000_000" `shouldBe` Right [TInt 1000000]
    it "parses hex integer" $ parseTokensUnposed "0xFF" `shouldBe` Right [THexInt 255]

    it "parses float" $
      let isRightFloat :: Double -> Either String [Token] -> Bool
          isRightFloat x (Right [TFloat s]) = toRealFloat s == x
          isRightFloat _ _ = False
      in
      parseTokensUnposed "12.34" `shouldSatisfy` isRightFloat 12.34

    it "does not split keywordX into keyword + name" $ property $ do
      n <- genName
      kw <- elements $ map pretty [
          KWEffect,
          KWElse,
          KWEnd,
          KWFalse,
          KWForall,
          KWFunct,
          KWHandle,
          KWIf,
          KWIn,
          KWImm,
          KWLet,
          KWMatch,
          KWResume,
          KWRow,
          KWThen,
          KWTo,
          KWTrue,
          KWType,
          KWUnder,
          KWVal,
          KWVar,
          KWWith
        ]
      pure $ parseTokensUnposed (kw <> n) `shouldBe` Right [TName $ kw <> n]

    it "parses simple string" $ property $ do
      n <- T.concat <$> listOf genName
      pure $ parseTokensUnposed ("'" <> n <> "'") `shouldBe` Right [TString n]

    it "parses escaped quote" $ property $ do
      l <- genName
      r <- genName
      pure $ parseTokensUnposed (T.concat ["'", l, "\\'", r, "'"]) `shouldBe`
        Right [TString $ l <> "'" <> r]

    it "parses escaped backslash" $ property $ do
      l <- genName
      r <- genName
      pure $ parseTokensUnposed (T.concat ["'", l, "\\\\", r, "'"]) `shouldBe`
        Right [TString $ l <> "\\" <> r]

    it "parses complex string" $ property $ do
      n <- genText
      let input = "'" <> n <> "'"
      pure $ parseTokensUnposed input `shouldBe`
        Right [TString $ T.replace "\\\\" "\\" (T.replace "\\'" "'" n)]

    it "parses arbitrary positive decimal integers with underscores" $ property prop_decIntUnderscore
    it "parses arbitrary positive hex integers" $ property prop_hexInt
    it "not crashes" $ property prop_noCrash
  -- describe "Parser" $ do it "goes roundtrip exp" $ property prop_roundTripExp

prop_decInt :: Positive Integer -> Bool
prop_decInt (Positive n) =
  case parseTokensUnposed (T.pack $ show n) of
    Right [TInt n'] | n' == n -> True; _ -> False

prop_decIntUnderscore :: Positive Integer -> Property
prop_decIntUnderscore (Positive n) =
  forAll (insertUnderscores $ show n) $ \txt ->
    case parseTokensUnposed $ T.pack txt of
      Right [TInt m]  -> m == n
      _               -> False

prop_hexInt :: Positive Integer -> Bool
prop_hexInt (Positive n) =
  let hex = showHex n ""; txt = "0x" <> hex
  in case parseTokensUnposed $ T.pack txt of
      Right [THexInt m]  -> m == n
      _                  -> False

prop_noCrash :: String -> Bool
prop_noCrash s =
  case parseTokens $ T.pack s of
    Left _  -> True
    Right _ -> True

insertUnderscores :: String -> Gen String
insertUnderscores = \case
  [] -> pure []
  [x] -> pure [x]
  (x:xs) -> do
    rest <- insertUnderscores xs
    insert <- arbitrary
    pure $ x : (if insert then '_' : rest else rest)

printExps :: IO ()
printExps = do
--   _ <- parseAndPrint "record" parseExpFromText "#{val x    : Int = 5  }@   x"
--   _ <- parseAndPrint "array" parseExpFromText "[1, 2, 3]"
--   _ <- parseAndPrint "triple" parseExpFromText "(1, 2, 3)"
--   _ <- parseAndPrint "if-then-else" parseExpFromText "if pred x y then 42 else if f z 4 then 5 else 0"

--   _ <- parseAndPrint "tuple2" (parseFromText Parser.tupleOrExp) "(1, 2)"
--   _ <- parseAndPrint "tuple2paren" (parseFromText Parser.tupleOrExp) "(1, (2, 3))"
--   _ <- parseAndPrint "tuple3" (parseFromText Parser.tupleOrExp) "(1, 2, 3)"

--   _ <- parseAndPrint "tuple2 exp" (parseFromText Parser.exp) "(1, 2)"
--   _ <- parseAndPrint "tuple2paren exp" (parseFromText Parser.exp) "(1, (2, 3))"
--   _ <- parseAndPrint "tuple3 exp" (parseFromText Parser.exp) "(1, 2, 3)"

--   _ <- parseAndPrint "bindDef stat" (parseFromText Parser.blockStat) "val x = 5"
--   _ <- parseAndPrint "exp stat" (parseFromText Parser.blockStat) "+ x x"
--   _ <- parseAndPrint "just exp" (parseFromText Parser.exp) "+ x x"
--   _ <- parseAndPrint "block" (parseFromText Parser.block) "val x = 5; + x x"
--   _ <- parseAndPrint "tuple with lambda" (parseFromText Parser.tupleOrExp) "(1, (1, 2), {* it it})"
--   _ <- parseAndPrint "tuple with block" (parseFromText Parser.tupleOrExp) "(1, (1, 2), (val x = 5; + x x))"
--   _ <- parseAndPrint "full tuple with block" (parseFromText Parser.tupleOrExp) "(1, (1, 2), (val x = 5; + x x), {* it it})"

--   _ <- parseAndPrint "mul exp" (parseFromText Parser.exp) "* it it"
--   _ <- parseAndPrint "mul block" (parseFromText Parser.block) "* it it"
--   _ <- parseAndPrint "lambda" (parseFromText Parser.lambda) "{* it it}"
--   _ <- parseAndPrint "lambda exp" (parseFromText Parser.exp) "{* it it}"

--   _ <- parseAndPrint "block in parens" (parseFromText $ parens Parser.block) "(val x = 5; + x x)"
--   _ <- parseAndPrint "paren exp1" (parseFromText $ Parser.parens Parser.exp) "(123)"
--   _ <- parseAndPrint "paren exp2" (parseFromText $ Parser.parens Parser.exp) "(+ x x)"
--   _ <- parseAndPrint "paren exp3" (parseFromText $ Parser.parens Parser.exp) "([])"

--   _ <- parseAndPrint "exp1 in parens" (parseFromText Parser.exp) "(123)"
--   _ <- parseAndPrint "exp2 in parens" (parseFromText Parser.exp) "(+ x x)"
--   _ <- parseAndPrint "exp2 out parens" (parseFromText Parser.exp) "+ x x"
--   _ <- parseAndPrint "exp3 in parens" (parseFromText Parser.exp) "([])"
--   _ <- parseAndPrint "let exp" (parseFromText Parser.exp) "let a = 5 in a"
--   _ <- parseAndPrint "if exp" (parseFromText Parser.exp) "if true then 3 else 2"
--   _ <- parseAndPrint "exp in parens" (parseFromText Parser.exp) "(if true then 3 else 2)"
--   _ <- parseAndPrint "exp in explicit parens" (parseFromText $ parens Parser.exp) "(if true then 3 else 2)"
--   _ <- parseAndPrint "triple with comma" (parseFromText Parser.exp) "(1, 2, 3,)"
--   _ <- parseAndPrint "triple with comma + space" (parseFromText Parser.exp) "(1, 2, 3, )"
--   _ <- parseAndPrint "triple with comma - space" (parseFromText Parser.exp) "(1, 2, 3 ,)"
--   _ <- parseAndPrint "triple with comma -+ space" (parseFromText Parser.exp) "(1, 2, 3 , )"
--   _ <- parseAndPrint "triple no comma" (parseFromText Parser.exp) "(1, 2, 3)"
--   _ <- parseAndPrint "simple chunk" (parseFromText Parser.chunk) $
--       T.intercalate "\n" [
--         "funct ++ [T] (l [T]) (r [T]) : [T] =",
--         "  concat l r",
--         "",
--         "funct main ) : Main () =",
--         "  say $ ++ [1, 2, 3] [4, 5, 6]"
--       ]
  _ <- parseAndPrint "eff cons 1" (parseFromText Parser.effCons) "List"
  _ <- parseAndPrint "eff cons 2" (parseFromText Parser.effCons) "List [Int]"
  _ <- parseAndPrint "eff cons 3" (parseFromText Parser.effCons) "Tuple [Int; Float]"
  _ <- parseAndPrint "eff cons 4" (parseFromText Parser.effCons) "Tuple [Int; Float; Tuple [Int; String]]"

  _ <- parseAndPrint "eff row 1" (parseFromText Parser.effRow) "Mutation"
  _ <- parseAndPrint "eff row 2" (parseFromText Parser.effRow) "{Var; Rebind; Cell}"
  _ <- parseAndPrint "eff row 3" (parseFromText Parser.effRow) "{Var; Rebind; Cell | e}"

  _ <- parseAndPrint "resume 1" (parseFromText Parser.exp) "resume + x x"

  _ <- parseAndPrint "type 1" (parseFromText Parser.typ) "Int"
  _ <- parseAndPrint "type 2" (parseFromText Parser.typ) "Int -> Int"
  _ <- parseAndPrint "type 3" (parseFromText Parser.typ) "Int -> Int -> Int"
  pure ()


mapElabM :: Int -> ElabM a -> (ElaborationError -> b) -> (a -> b) -> b
mapElabM counter elabAction onError onSuccess = do
  let result = evalState (runExceptT elabAction) $ ElabState counter
  case result of
    Left elabError -> onError elabError
    Right elabSuccess -> onSuccess elabSuccess

onElabSuccess :: Int -> ElabM a -> (a -> IO ()) -> IO ()
onElabSuccess counter =
  mapElabM counter `flip` (\elabError -> putStrLn $ "Elaboration error: " <> show elabError)

-- | Debug parsing with nice output.
--
-- Takes:
-- * rule name (for prefix in output)
-- * parser ('Text' -> 'Either' 'String' 'a')
-- * input text
--
-- Outputs either error, or two result visualizations: 'pretty' and 'show'.
parseAndPrint :: (Show a, Pretty a, Sexp a) => Text -> (Text -> Either String a) -> Text -> IO ()
parseAndPrint s f t = either
  (\e -> do
    printf "Error '[[%s]]'\n" s
    printf "  input: %s\n" t
    printf "  details: %s\n" e)
  (\e -> do
    printf "Success '[[%s]]'\n" s
    printf "  pretty: %s\n" $ T.unpack $ pretty e
    printf "  details: %s\n" $ show e
    printf "  sexp: %s\n" $ sexp e)
  $ f t