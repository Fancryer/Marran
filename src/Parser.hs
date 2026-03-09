{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Parser(
  Parser,
  parseTokens,
  Parser.exp,
  number,
  tupleExp,
  block,
  blockStat
)
where
import Data.Void
import Data.Text(Text)

import Text.Megaparsec(
    Parsec,
    errorBundlePretty,
    runParser,
    many,
    MonadParsec (eof, try, notFollowedBy),
    choice,
    optional,
    some, sepBy1, sepBy, (<|>), satisfy, ParseErrorBundle, lookAhead, between
  )
import Lexer (
    Token (
      TKW,
      TName,
      TInt,
      TAssign,
      TSquareL,
      TSquareR,
      TBraceL,
      TBraceR,
      TColon,
      TParenL,
      TParenR, TComma, TArrow, TTVar, TSemi, THRPArrow, TEllipsis, TPipe, TRebind, TAt, TSharpBraceL, TString, THexInt, TFloat, THexFloat, TUnderscore, TDollar, TMatchArrow, TInfixName
    ),
    tokens,
    Keyword (..)
  )
import Data.Scientific (Scientific)
import Data.Maybe (fromMaybe, isJust, fromJust)
import Control.Monad.Combinators.Expr (makeExprParser, Operator (InfixR, Postfix, Prefix, InfixL))
import Data.Functor (($>))
import Ast

type Parser = Parsec Void [Token]

parseTokens :: Text -> Either String [Token]
parseTokens input = case runParser tokens "<test>" input of
  Left err -> Left $ errorBundlePretty err
  Right ts -> Right ts

parseExp :: [Token] -> Either (ParseErrorBundle [Token] Void) Exp
parseExp input = case runParser Parser.exp "<exp>" input of
  Left err -> Left err
  Right e -> Right e

tok :: (Token -> Maybe a) -> Parser a
tok = satisfyMap
  where
    satisfyMap :: (Token -> Maybe a) -> Parser a
    satisfyMap f = do
      t <- satisfy (isJust . f)
      pure $ fromJust $ f t

keyword :: Keyword -> Parser ()
keyword kw = tok test
  where
    test (TKW k) | k == kw = Just ()
    test _ = Nothing

name, infixName, meta :: Parser Text
name = tok test
  where
    test (TName t) = Just t
    test _ = Nothing

infixName = tok test
  where
    test (TInfixName t) = Just t
    test _ = Nothing

meta = tok test
  where
    test (TTVar t) = Just t
    test _ = Nothing

constantQualifier :: Parser ConstantQualifier
constantQualifier = tok test
  where
    test = \case
      (TKW KWVal) -> Just Val
      (TKW KWVar) -> Just Var
      (TKW KWImm) -> Just Imm
      _ -> Nothing

symbol :: Token -> Parser ()
symbol t = tok test
  where
    test x | x == t = Just ()
    test _ = Nothing

intLiteral :: Parser Integer
intLiteral = tok test
  where
    test (TInt n) = Just n
    test (THexInt n) = Just n
    test _ = Nothing

floatLiteral :: Parser Scientific
floatLiteral = tok test
  where
    test (TFloat n) = Just n
    test (THexFloat n) = Just n
    test _ = Nothing

stringLiteral :: Parser Text
stringLiteral = tok test
  where
    test (TString s) = Just s
    test _ = Nothing

bool :: Parser Bool
bool = tok test
  where
    test (TKW KWTrue) = Just True
    test (TKW KWFalse) = Just False
    test _ = Nothing

betweenSymbols :: Token -> Token -> Parser a -> Parser a
betweenSymbols l = between (symbol l) . symbol

brackets, braces, sharpBraces, parens :: Parser a -> Parser a
brackets = betweenSymbols TSquareL TSquareR
braces = betweenSymbols TBraceL TBraceR
sharpBraces = betweenSymbols TSharpBraceL TBraceR
parens = betweenSymbols TParenL TParenR

semisym, colonsym, pipesym, commasym :: Parser ()
semisym = symbol TSemi
colonsym = symbol TColon
pipesym = symbol TPipe
commasym = symbol TComma

chunk :: Parser Chunk
chunk = Chunk <$> many topLevelStat <* eof

topLevelStat :: Parser TopLevelStat
topLevelStat = choice [typeDef, effDef, rowDef, functDef]

typeDef :: Parser TopLevelStat
typeDef = do
  keyword KWType
  n <- name
  ts <- fromMaybe mempty <$> optional typeParams
  es <- fromMaybe mempty <$> optional effParams
  symbol TAssign
  TypeDef n ts es <$> typ

typeParams :: Parser TypeParams
typeParams = TParams . Params <$> brackets (some name)

effParams :: Parser EffParams
effParams = EParams . Params <$> braces (some name)

typ :: Parser Typ
typ = makeExprParser typAtom table
  where
    table = [[InfixR $ TPair <$ commasym], [InfixR functionOp]]
    functionOp = do
      symbol TArrow
      eff <- optional effRow
      pure $ \from to -> TFunct from to eff

typAtom :: Parser Typ
typAtom =
  choice [
    try $ TGenericAlias <$> name <*> typeApps,
    TFlat <$> name,
    TNil <$ nil,
    TArray <$> brackets typ,
    try $ TParen <$> parens typ,
    TVar <$> meta,
    TRecord <$> recordType,
    forallType
  ]

recordType :: Parser RecordTyp
recordType = sharpBraces $
  RecordTyp <$> sepBy1 recordTProp (optional semisym) <* optional semisym

forallType :: Parser Typ
forallType = do
  keyword KWForall
  (ts, es) <- choice [
      -- ts es
      try $ (,) <$> typeParams <*> effParams,
      -- ts
      (, mempty) <$> typeParams,
      -- es
      (mempty, ) <$> effParams
    ]
  symbol THRPArrow
  TForall ts es <$> typ

recordTProp :: Parser RecordTypProp
recordTProp = do
  q <- constantQualifier
  n <- name
  _ <- optional colonsym
  RecordTypProp q n <$> typ

nil :: Parser ()
nil = do
  symbol TParenL
  symbol TParenR
  pure ()

effDef :: Parser TopLevelStat
effDef = do
  keyword KWEffect
  n <- name
  ts <- fromMaybe mempty <$> optional typeParams
  es <- fromMaybe mempty <$> optional effParams
  ops <- many effectOp
  keyword KWEnd
  pure $ EffectDef n ts es ops

effectOp :: Parser EffectOp
effectOp = EffectOp <$> name <* colonsym <*> typ

rowDef :: Parser TopLevelStat
rowDef = do
  keyword KWRow
  n <- name
  ts <- fromMaybe mempty <$> optional typeParams
  symbol TAssign
  RowDef n ts <$> effRow

functDef :: Parser TopLevelStat
functDef = do
  keyword KWFunct
  n <- name
  ts <- fromMaybe mempty <$> optional typeParams
  es <- fromMaybe mempty <$> optional effParams
  args <- functArgs
  colonsym
  fx <- optional effRow
  out <- typ
  symbol TAssign
  FunctDef n ts es args fx out <$> block

functArgs :: Parser [FunctArg]
functArgs = some functArg

effRow :: Parser EffRow
effRow =
  choice [
    EREvar <$> meta,
    ERAlias <$> name,
    braces $ ERSugar <$> sepBy effRowEntry semisym <*> optional (pipesym *> name)
  ]

effRowEntry :: Parser EffRowEntry
effRowEntry =
  choice [
    EREEffCons <$> effCons,
    EREEffRow <$> (symbol TEllipsis *> effRow)
  ]


effCons :: Parser EffCons
effCons = EffCons <$> name <*> optional typeParams

block :: Parser Block
block = choice [
    try (Block [] <$> Parser.exp <* notFollowedBy semisym),
    Block <$> some (try $ blockStat <* semisym) <*> Parser.exp
  ]
  -- bs <- choice [
  --     try (many (blockStat <* semisym)),
  --     pure []
  --   ]
  -- Block bs <$> Parser.exp

blockStat :: Parser BlockStat
blockStat =
  choice [
    try $ BBindDef <$> bindDef,
    try $ BAssign <$> assign,
    BExp <$> Parser.exp
  ]

bindDef :: Parser BindDef
bindDef = do
  cq <- constantQualifier
  lp <- lambdaParam
  symbol TAssign
  BindDef cq lp <$> Parser.exp

lambdaParam :: Parser LambdaParam
lambdaParam = do
  n <- name
  LambdaParam n <$> optional (optional colonsym *> typ)

assign :: Parser Assign
assign = Assign <$> name <* symbol TRebind <*> Parser.exp

{-pathExp :: Parser PathExp
pathExp = do
  e <- Parser.exp
  symbol TAt
  PathExp e <$> choice [(: []) <$> name, parens $ some name]-}

letPattern :: Parser LetPattern
letPattern = choice [LPATom <$> atomLetPattern, LPParam <$> lambdaParam]

atomLetPattern :: Parser AtomLetPattern
atomLetPattern = choice [
    ALPNil <$ nil,
    ALPUnderscore <$ symbol TUnderscore,
    ALPParen <$> parens letPattern,
    ALPPair <$> letPattern <* commasym <*> letPattern,
    recordLetPattern
  ]

recordLetPattern :: Parser AtomLetPattern
recordLetPattern = sharpBraces $
  ALPRecord <$> sepBy1 atomLetPatternRecordProp semisym <* optional semisym

atomLetPatternRecordProp :: Parser AtomLetPatternRecordProp
atomLetPatternRecordProp = do
  cq <- constantQualifier
  lp <- lambdaParam
  symbol TAssign
  AtomLetPatternRecordProp cq lp <$> atomLetPattern

functArg :: Parser FunctArg
functArg = parens $ do
  arg <- optional $
    NamedFunctArg <$> name <* optional colonsym <*> typ
  pure $ fromMaybe NilArg arg

typeApps :: Parser TypeApps
typeApps = TypeApps <$> brackets (sepBy typeArg semisym <* optional semisym)

typeArg :: Parser TypeArg
typeArg = makeExprParser typeArgAtom table
  where
    table = [
        [InfixR $ TAPair <$ commasym],
        [InfixR $ TAFunct <$ symbol TArrow]
      ]

typeArgAtom :: Parser TypeArg
typeArgAtom =
  choice [
    try $ TAGenericAlias <$> name <*> typeApps,
    TAFlat <$> name,
    TANil <$ nil,
    try $ TAParen <$> parens typeArg,
    TAArray <$> brackets typeArg,
    TAMeta <$> meta,
    TARecord <$> recordTypeArg
  ]

recordTypeArg :: Parser RecordTypeArg
recordTypeArg = sharpBraces $
  RecordTypeArg <$> sepBy1 recordTypeArgProp (optional semisym) <* optional semisym

recordTypeArgProp :: Parser RecordTypeArgProp
recordTypeArgProp = do
  q <- constantQualifier
  n <- name
  _ <- optional colonsym
  RecordTypeArgProp q n <$> typeArg

effApps :: Parser EffApps
effApps = EffApps <$> braces (sepBy effArg semisym <* optional semisym)

effArg :: Parser EffArg
effArg = choice [EACons <$> effCons, EARow <$> (symbol TEllipsis *> effRow)]

exp :: Parser Exp
exp = choice [
    try ifExp,
    try letExp,
    try under,
    makeExprParser term operatorTable
  ]
  where
    operatorTable :: [[Operator Parser Exp]]
    operatorTable = [
        [postfixProp, postfixWith],
        [backtickOp],
        [dollarOp],
        [resumeOp]
      ]

term :: Parser Exp
term = foldl EApply <$> simpleTerm <*> many simpleTerm

-- simpleTerm :: Parser Exp
-- simpleTerm = choice [
--     ELiteral <$> literal,
--     try tupleExp,
--     try (EParen <$> parens block),
--     EName <$> name
--   ]

simpleTerm :: Parser Exp
simpleTerm = choice [
    ELiteral <$> literal,
    -- Специальная обработка скобок
    parens $ choice [
      try tupleContent,  -- пробуем как кортеж
      EParen <$> block   -- иначе как выражение в скобках
    ],
    EName <$> name
  ]
  where
    tupleContent = do
      e1 <- Parser.exp
      commasym  
      es <- sepBy1 Parser.exp commasym <* optional commasym
      pure $ foldr1 EPair (e1 : es)


ifExp, letExp, tupleExp :: Parser Exp
ifExp = do
  keyword KWIf
  p <- Parser.exp
  keyword KWThen
  t <- Parser.exp
  keyword KWElse
  EIfThenElse p t <$> Parser.exp

letExp = do
  keyword KWLet
  lp <- letPattern
  symbol TAssign
  e <- Parser.exp
  keyword KWIn
  ELet lp e <$> Parser.exp

under :: Parser Exp
under = do
  keyword KWUnder
  ec <- effCons
  keyword KWTo
  b <- block
  keyword KWHandle
  f <- optional handlerClause
  cs <- many handlerClause
  EUnder <$> case f of
    Just f' -> do
      t <- optional $ pipesym *> keyword KWThen *> symbol TMatchArrow *> block
      pure $ UFull ec b f' cs t
    Nothing -> do
      t <- pipesym *> keyword KWThen *> symbol TMatchArrow *> block
      pure $ UThen ec b cs t

handlerClause :: Parser HandlerClause
handlerClause = do
  pipesym
  n <- name
  args <- many name
  symbol TMatchArrow
  HandlerClause n args <$> block

tupleExp = parens $ do
  e1 <- Parser.exp
  commasym
  es <- sepBy1 (try Parser.exp) commasym <* optional commasym
  pure $ foldr1 EPair (e1 : es)

resumeOp :: Operator Parser Exp
resumeOp = Prefix $ keyword KWResume $> EResume

postfixProp :: Operator Parser Exp
postfixProp =
  Postfix $
    symbol TAt *> do
      n <- name
      pure $ \e -> EPropAccess e n

postfixWith :: Operator Parser Exp
postfixWith =
  Postfix $
    keyword KWWith *> do
      ts <- typeApps
      es <- effApps
      pure $ \e -> EWith e ts es

backtickOp :: Operator Parser Exp
backtickOp = InfixL $ EBacktick <$> infixName

dollarOp :: Operator Parser Exp
dollarOp = InfixR $ symbol TDollar $> EDollar

literal :: Parser Literal
literal = choice [
    LAtom <$> atom,
    LArray <$> array,
    LLambda <$> lambda,
    LRecord <$> record
  ]

atom :: Parser Atom
atom = choice [
    AString <$> stringLiteral,
    ANumber <$> number,
    ANil <$ nil,
    ABoolean <$> bool
  ]

number :: Parser Number
number = try (NFloat <$> floatLiteral) <|> NInt <$> intLiteral

array :: Parser ArrayLiteral
array = brackets $
  ArrayLiteral <$> sepBy arrayEntry commasym <* optional commasym

arrayEntry :: Parser ArrayEntry
arrayEntry = try (AEBlock <$> block <* semisym) <|> (AEExp <$> Parser.exp)

lambda :: Parser LambdaLiteral
lambda = braces $ do
  ts <- optional typeParams
  es <- optional effParams
  lh <- optional lambdaHead
  LambdaLiteral ts es lh <$> block


lambdaHead :: Parser LambdaHead
lambdaHead = do
  ps <- lambdaParams
  out <- optional $ colonsym *> typ
  symbol TAssign
  pure $ LambdaHead ps out

lambdaParams :: Parser [LambdaParam]
lambdaParams =
  choice [
    some $ choice [
      parens lambdaParam,
      nil $> LambdaParam "_" Nothing,
      (`LambdaParam` Nothing) <$> name
    ],
    parens $ sepBy1 lambdaParam semisym
  ]

record :: Parser RecordLiteral
record = sharpBraces $
  RecordLiteral <$> optional (Parser.exp <* pipesym) <*> sepBy1 bindDef semisym <* optional semisym