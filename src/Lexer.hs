{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Lexer (
  Token(..),
  LToken(..),
  Keyword(..),
  tokens,
  token
)
where
import Data.Void
import Data.Text(Text)
import qualified Data.Text as T

import Text.Megaparsec(Parsec, choice, some, MonadParsec (notFollowedBy, try, eof), satisfy, oneOf, between, optional, many, SourcePos, getSourcePos)
import Text.Megaparsec.Char(space1, char, string)
import qualified Text.Megaparsec.Char.Lexer as L
import GHC.Unicode (isAlphaNum, isDigit, isHexDigit)
import Data.Maybe (fromMaybe)
import Data.Scientific (Scientific, scientific)
import Data.Char (digitToInt)
import Data.Functor (($>))
import Utils (Pretty (..))

type Lexer = Parsec Void Text

tokens :: Lexer [LToken]
tokens = between sc eof $ many locatedToken

sc :: Lexer ()
sc = L.space
  space1
  (L.skipLineComment "//|")
  (L.skipBlockComment "/|" "|\\")

lexeme :: Lexer a -> Lexer a
lexeme = L.lexeme sc

sym :: Text -> Token -> Lexer Token
sym s t = t <$ L.symbol sc s

kw :: Text -> Keyword -> Lexer Token
kw s k = lexeme $ TKW k <$ try (string s <* notFollowedBy wordChar)

digit, hexDigit :: Lexer Char

digit = satisfy isDigit
hexDigit = satisfy isHexDigit

stripUnderscore :: String -> String
stripUnderscore = filter (/= '_')

parseDecInt :: String -> Integer
parseDecInt =
  foldl (\acc d -> acc * 10 + fromIntegral (digitToInt d)) 0
  . stripUnderscore

parseHexInt :: String -> Integer
parseHexInt =
  foldl (\acc d -> acc * 16 + fromIntegral (digitToInt d)) 0
  . stripUnderscore

intDigitPart :: Lexer String
intDigitPart = do
  prefix <- some digit
  suffix <- many $ char '_' *> some digit
  pure $ prefix <> concat suffix

hexIntDigitPart :: Lexer String
hexIntDigitPart = do
  prefix <- some hexDigit
  suffix <- many $ char '_' *> some hexDigit
  pure $ prefix <> concat suffix

exponentPart :: Lexer String
exponentPart = do
  e <- oneOf ['e', 'E']
  s <- optional $ oneOf ['+', '-']
  ds <- some digit
  pure $ e : maybe "" pure s <> ds

hexExponentPart :: Lexer String
hexExponentPart = do
  p <- oneOf ['p','P']
  s <- optional $ oneOf ['+', '-']
  ds <- some digit
  pure $ p : maybe "" pure s <> ds

parseExponent :: String -> Int
parseExponent [] = 0
parseExponent (_:rest) =
  case rest of
    '-':ds -> negate (parseDecDigits ds)
    '+':ds -> parseDecDigits ds
    ds     -> parseDecDigits ds

-- | The digits of an exponent.  They are produced by @some digit@, so the input
--   is known to be decimal; reading them with a fold keeps the function total
--   instead of relying on 'read'.
parseDecDigits :: String -> Int
parseDecDigits = foldl (\acc d -> acc * 10 + digitToInt d) 0

intLiteral :: Lexer Integer
intLiteral = lexeme $ parseDecInt <$> intDigitPart

hexIntLiteral :: Lexer Integer
hexIntLiteral = lexeme $ char '0' *> oneOf ['x', 'X'] *> (parseHexInt <$> hexIntDigitPart)

floatLiteral :: Lexer Scientific
floatLiteral = lexeme $ do
  a <- intDigitPart
  choice [
    do
      _ <- char '.'
      b <- intDigitPart
      e <- optional exponentPart

      let mantissa = parseDecInt $ a <> b
          scale    = negate $ length $ stripUnderscore b
          base     = scientific mantissa scale

      pure $ maybe base (\ex -> base * (10 ^^ parseExponent ex)) e,
    do
      e <- exponentPart
      pure $ scientific (parseDecInt a) 0 * (10 ^^ parseExponent e)
    ]

hexFloatLiteral :: Lexer Scientific
hexFloatLiteral = lexeme $ do
  _ <- char '0'
  _ <- oneOf ['x', 'X']
  (a, b) <- choice [
    do
      a <- optional hexIntDigitPart
      _ <- char '.'
      (,) (fromMaybe "" a) <$> hexIntDigitPart,
    do (, "") <$> hexIntDigitPart
    ]
  e <- hexExponentPart

  let
    mantissa = parseHexInt $ a <> b
    fracLen  = length $ stripUnderscore b
    base     = scientific mantissa $ (-4) * fracLen
    exp2     = parseExponent e

  pure $ base * (2 ^^ exp2)


-- | Characters that may occur in a name.  An operator is just a name whose
--   characters come from this set, so @+@, @<=@, @|>@ and @<|@ are names, and
--   the lexer needs no special case for any of them.  A name that starts with
--   an operator character consists of operator characters only, so @|val@ is
--   the pipe followed by @val@, not one name.  A lone @|@ is not a name: it is
--   the pipe that separates a record from its base and a row from its tail, so
--   'name' maps exactly that one back to 'TPipe'.
operatorChar :: Char -> Bool
operatorChar = (`elem` ("+/%|&^~<=>.*!?-" :: String))

normalChar :: Char -> Bool
normalChar c = isAlphaNum c || c == '_' || operatorChar c

wordChar :: Lexer Char
wordChar = satisfy normalChar

nameText :: Lexer Text
nameText = do
  c <- wordChar
  rest <-
    if isAlphaNum c || c == '_'
      then many wordChar
      else many (satisfy operatorChar)
  pure $ T.pack (c : rest)

name :: Lexer Token
name = lexeme $ do
  t <- nameText
  pure $ if t == "|" then TPipe else TName t

tvar :: Lexer Token
tvar = lexeme $ TTVar <$> (char '`' *> nameText)

infixName :: Lexer Token
infixName = lexeme $ TInfixName <$> between (char '`') (char '`') nameText

locatedToken :: Lexer LToken
locatedToken = LToken <$> getSourcePos <*> token

token :: Lexer Token
token = choice [
    try infixName,
    tvar,
    sym "@" TAt,
    sym "#[" TSharpSquareL, sym "[" TSquareL, sym "]" TSquareR,
    sym "#{" TSharpBraceL,  sym "{" TBraceL,  sym "}" TBraceR,
    sym "${" TDollarBraceL,
    sym "$" TDollar,
    -- A constructor pattern writes `#Some x`.  The two long forms above are
    -- tried first, so `#[` and `#{` never reach this.
    sym "#" TSharp,
    sym "(" TParenL,        sym ")" TParenR,
    sym ":=" TRebind,
    -- `::` is one token: it separates a module from a name and never appears
    -- inside a name, because a name ends before a colon.
    sym "::" TColonColon,
    sym ":" TColon,
    sym ";" TSemi,
    sym "," TComma,
    sym "..." TEllipsis,
    sym "=>" TMatchArrow,
    sym "==>" THRPArrow,
    -- `==` and `===` are ordinary names, like `+` or `!=`: `== 1 1` applies
    -- the function `==`.  `sym "="` below would otherwise split them into two
    -- assignments, so the longer names are tried first.  `==>` is matched
    -- above and never reaches here.
    try $ lexeme $ TName <$> L.symbol sc "===",
    try $ lexeme $ TName <$> L.symbol sc "==",
    sym "=" TAssign,
    sym "_" TUnderscore,
    sym "->" TArrow,
    -- The split-pattern arrows are tokens of their own, and they are tried
    -- before `<-` so that `<-|` never becomes `<-` followed by `|`.
    sym "|->" TStartsArrow,
    sym "<-|" TEndsArrow,
    sym "<-" TRevArrow,
    kw "as" KWAs,
    kw "effect" KWEffect,
    kw "else" KWElse,
    kw "end" KWEnd,
    kw "enum" KWEnum,
    choice $ map (`kw` KWFalse) ["false", "⊥"],
    choice $ map (`kw` KWForall) ["forall", "∀"],
    kw "funct" KWFunct,
    kw "handle" KWHandle,
    kw "if" KWIf,
    choice $ map (`kw` KWIn) ["in", "∈"],
    kw "imm" KWImm,
    kw "let" KWLet,
    kw "match" KWMatch,
    kw "module" KWModule,
    kw "import" KWImport,
    kw "resume" KWResume,
    kw "row" KWRow,
    kw "then" KWThen,
    kw "to" KWTo,
    choice $ map (`kw` KWTrue) ["true", "⊤"],
    kw "type" KWType,
    kw "under" KWUnder,
    kw "val" KWVal,
    kw "var" KWVar,
    kw "with" KWWith,
    kw "pattern" KWPattern,
    kw "demands" KWDemands,
    kw "ensures" KWEnsures,
    kw "unwinds" KWUnwinds,
    THexFloat <$> try hexFloatLiteral,
    TFloat <$> try floatLiteral,
    THexInt <$> try hexIntLiteral,
    TInt <$> intLiteral,
    charString,
    name
  ]

stringChar :: Lexer Char
stringChar =
  choice [
    string "\\n" $> '\n',
    string "\\t" $> '\t',
    string "\\r" $> '\r',
    string "\\\\" $> '\\',
    string "\\'" $> '\'',
    satisfy (/= '\'')
  ]


charString :: Lexer Token
charString = lexeme $ TString . T.pack <$> between (char '\'') (char '\'') (many stringChar)

data LToken = LToken {ltPos :: SourcePos, ltToken :: Token} deriving (Eq, Show, Ord)

data Token =
  TDollar
  | TAt
  | TColon
  | TColonColon
  | TComma
  | TSemi
  | TEllipsis

  | TParenL       | TParenR
  | TBraceL       | TBraceR
  | TSquareL      | TSquareR
  | TSharpBraceL  | TSharpSquareL | TDollarBraceL
  | TSharp

  | TAssign
  | TRebind
  | TPipe

  | TUnderscore
  | TArrow
  | TStartsArrow
  | TEndsArrow
  | TRevArrow
  | TMatchArrow
  | THRPArrow

  | TKW Keyword        -- ключевые слова
  | TName Text
  | TInfixName Text
  | TTVar Text

  | TInt Integer
  | TFloat Scientific
  | THexInt Integer
  | THexFloat Scientific

  | TString Text
  | TNil
  deriving (Show, Eq, Ord)

instance Pretty Token where
  pretty = \case
    TDollar   -> "$"
    TAt       -> "@"
    TColon    -> ":"
    TColonColon -> "::"
    TComma    -> ","
    TSemi     -> ";"
    TEllipsis -> "..."

    TParenL       -> "("
    TParenR       -> ")"
    TBraceL       -> "{"
    TBraceR       -> "}"
    TSquareL      -> "["
    TSquareR      -> "]"
    TSharpBraceL  -> "#{"
    TSharpSquareL -> "#["
    TDollarBraceL -> "${"
    TSharp        -> "#"

    TAssign -> "="
    TRebind -> ":="
    TPipe   -> "|"

    TUnderscore -> "_"
    TArrow      -> "->"
    TStartsArrow -> "|->"
    TEndsArrow  -> "<-|"
    TRevArrow   -> "<-"
    TMatchArrow -> "=>"
    THRPArrow   -> "==>"

    TKW k         -> pretty k
    TName n       -> n
    TInfixName n  -> "`" <> n <> "`"
    TTVar v       -> "`" <> v

    TInt i      -> T.pack $ show i
    TFloat f    -> T.pack $ show f
    THexInt i   -> T.pack $ show i
    THexFloat f -> T.pack $ show f

    TString s -> "'" <> s <> "'"
    TNil      -> "()"

data Keyword =
  KWAs
  | KWDemands
  | KWEffect
  | KWElse
  | KWEnd
  | KWEnsures
  | KWEnum
  | KWFalse
  | KWForall
  | KWFunct
  | KWHandle
  | KWIf
  | KWIn
  | KWImm
  | KWLet
  | KWMatch
  | KWModule
  | KWImport
  | KWPattern
  | KWResume
  | KWRow
  | KWThen
  | KWTo
  | KWTrue
  | KWType
  | KWUnder
  | KWUnwinds
  | KWVal
  | KWVar
  | KWWith
  deriving (Show, Eq, Ord)

instance Pretty Keyword where
  pretty = \case
    KWAs      -> "as"
    KWEffect  -> "effect"
    KWElse    -> "else"
    KWEnd     -> "end"
    KWEnum    -> "enum"
    KWFalse   -> "false"
    KWForall  -> "forall"
    KWFunct   -> "funct"
    KWHandle  -> "handle"
    KWIf      -> "if"
    KWIn      -> "in"
    KWImm     -> "imm"
    KWLet     -> "let"
    KWMatch   -> "match"
    KWModule  -> "module"
    KWImport  -> "import"
    KWResume  -> "resume"
    KWRow     -> "row"
    KWThen    -> "then"
    KWTo      -> "to"
    KWTrue    -> "true"
    KWType    -> "type"
    KWUnder   -> "under"
    KWVal     -> "val"
    KWVar     -> "var"
    KWWith    -> "with"
    KWDemands -> "demands"
    KWEnsures -> "ensures"
    KWPattern -> "pattern"
    KWUnwinds -> "unwinds"