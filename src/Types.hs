{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Types (
  Taste(..),
  Typ(..),
  EffRow(..),
  EffCons(..),
  ECons(..),
  EffDef(..),
  Expr(..),
  ExprNode(..),
  pattern Int,
  pattern Float,
  pattern Boolean,
  pattern String,
  pattern Nil,
  pattern XVar,
  pattern Array,
  pattern Pair,
  pattern XLambda,
  pattern NLambda,
  pattern Apply,
  pattern Record,
  pattern With,
  pattern Handle,
  pattern Paren,
  pattern Resume,
  pattern Let,
  pattern PropAccess,
  pattern IfElse,
  pattern Annot,
  pattern Match,
  atSpan,
  -- Scope(..),
  Block,
  blockSpan,
  -- NativeBlock,
  Stat(..),
  StatNode(..),
  pattern Bind,
  pattern Assign,
  pattern Expr,
  atStatSpan,
  statSpan,
  Lambda(..),
  -- NativeLambda(..),
  TopLevelStat(..),
  topLevelSpan,
  FunctDecl(..),
  Handler(..),
  HandlerSig(..),
  Chunk,
  Mutability(..),
  -- NativeHandlerClause,
  NativeLambdaSign(..),
  AtomLetPattern(..),
  TRecordProp(..),
  ERecordProp(..),
  Scheme(..),
  TypeScheme,
  EffScheme,
  TypeArg(..),
  TARecordProp(..),
  Funct(..),
  RowDef(..),
  LambdaParam(..),
  LetPattern(..),
  LetPatternRecordProp(..),
  HandlerClause,
  Pattern(..),
  PatternNode(..),
  MatchClause(..),
  EnumDef(..),
  EnumCase(..),
  enumName,
  enumParams,
  enumCases,
  enumCaseName,
  enumCaseFields,
  constructorTyp,
  TasteMap,
  tasteName,
  metaLevel,
  isSkolem,
  tfunc,
  pureFunct,
  pureTFunc,
  handlerCons,
  effName,
  countArgs,
  monoScheme,
  typeArgToTyp,
  typToTypeArg
) where
import Data.List (intercalate)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Scientific (Scientific)
import Utils (Pretty (..))
import GHC.Generics (Generic)
import Sexp (Sexp (..))
import Text.Printf (PrintfArg (formatArg))
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Control.Applicative as Set
import qualified Data.Set as Set
import Span (Span, noSpan, mergeSpan, mergeSpans)
import Module (Module(..))

-- TODO: replace name-based reachability with binding-identity-based analysis;
-- reduce false positives caused by shadowing.
data Taste =
  Meta Text Int Int     -- name id lvl
  | Skolem Text Int Int -- name id lvl
  | Bound Text Int      -- name id
  deriving (Show, Generic)

instance Sexp Taste

instance Pretty Taste where
  pretty = \case
    Meta m _ _ -> "`" <> m
    Skolem s _ _ -> "`" <> s
    Bound b _ -> "`" <> b

instance Eq Taste where
  Meta _ lid _ == Meta _ rid _ = lid == rid
  Skolem _ lid _ == Skolem _ rid _ = lid == rid
  Bound _ lid == Bound _ rid = lid == rid
  _ == _ = False

instance Ord Taste where
  Meta _ lid _ `compare` Meta _ rid _ = lid `compare` rid
  Skolem _ lid _ `compare` Skolem _ rid _ = lid `compare` rid
  Bound _ lid `compare` Bound _ rid = lid `compare` rid
  Meta {} `compare` _ = GT
  Skolem {} `compare` Meta {} = LT
  Skolem {} `compare` Bound {} = GT
  Bound {} `compare` _ = LT


type TasteMap = Map Taste

data Typ =
  TInt
  | TFloat
  | TBoolean
  | TString
  | TNil
  | TNothing
  | TFlat Text
  | TArray Typ EffRow
  | TPair Typ Typ EffRow
  | TFunct Funct                -- arg -> row ret
  | TRecord [TRecordProp] EffRow
  -- | A declared enumeration: its name and the arguments of its parameters.
  --   The type is nominal -- two enums that happen to have the same cases are
  --   still two types -- so the name is compared before the arguments.
  | TEnum Text [TypeArg]
  | TForall
    [Taste] [Taste] [Taste]
    (TasteMap (Set Text))
    (TasteMap (Set Text))
    Typ -- forall [a1 ... an] {e1 ... en | r1 ... rn} to {el1; ...; eln | rl1; ...; rln} ==> type
  | TVar Taste
  deriving (Show, Ord, Eq)

instance Pretty Typ where
  pretty = \case
    TInt -> "Int"
    TFloat -> "Float"
    TBoolean -> "Boolean"
    TString -> "String"
    TNil -> "()"
    TNothing -> "Nothing"
    TFlat n -> n
    TArray t r -> "[" <> pretty t <> "]" <> prettyPending r
    TPair l r fx ->
      "(" <> pretty l <> ", " <> pretty r <> ")" <> prettyPending fx
    TFunct f -> pretty f
    TRecord props r ->
      "#{" <> T.intercalate "; " (map pretty props) <>  "}" <> prettyPending r
    TEnum n args ->
      n <> if null args then "" else T.concat ["#[", T.intercalate "; " (map pretty args), "]"]
    TForall ts es rs els rls t -> T.concat [
        "forall ",
        "[", T.unwords $ map tasteName ts, "]",
        "{", T.unwords $ map tasteName es, if null rs then "" else " | " <> T.unwords (map tasteName rs), "}",
        lacks,
        " ==> ", pretty t
      ]
      where
        lacks = case (Map.elems els, Map.elems rls) of
          ([], []) -> ""
          (els', []) -> T.concat [" to {", T.pack $ show els', "}"]
          ([], rls') -> T.concat [" to {|", T.pack $ show rls', "}"]
          (els', rls') -> T.concat [" to {|", T.pack $ show els', " | ", T.pack $ show rls', "}"]

    TVar n -> "`" <> tasteName n

-- | The pending row of an aggregate type, printed only when it is not empty.
--
--   The paper writes it as @[T]@R@; the empty row is omitted to keep messages
--   short, and a row variable or an open row is always visible because it may
--   still grow.
prettyPending :: EffRow -> Text
prettyPending = \case
  RClosed [] -> ""
  r -> "@" <> pretty r

data Funct = Funct Typ Typ EffRow deriving (Show, Ord, Eq)
instance Pretty Funct where
  pretty (Funct i o fxs) = pretty i <> " -> " <> pretty fxs <> " " <> pretty o

data RowLacks = RowLacks {
  rowVariable :: Taste,
  forbiddenEffects :: Set EffCons
}

data Scheme a = Scheme {
  _ts :: [Taste],
  _es :: [Taste],
  _rs :: [Taste],
  _effLacks :: TasteMap (Set Text),
  _rowLacks :: TasteMap (Set Text),
  _a :: a
} deriving Show

type TypeScheme = Scheme Typ
-- unused, but potentitally could be implemented for row aliases
type EffScheme = Scheme EffRow

monoScheme :: Typ -> TypeScheme
monoScheme = Scheme [] [] [] Map.empty Map.empty

data TRecordProp = TRecordProp {
    tMut :: Mutability,
    tName :: Text,
    tTyp :: Typ
  }
  deriving (Show, Eq, Ord)

instance Pretty TRecordProp where
  pretty (TRecordProp m n t) =
    T.unwords [pretty m, n, ":", pretty t]

data EffRow =
  RClosed [EffCons]       -- Закрытый ряд: {Console; File}
  | ROpen [EffCons] Taste -- Открытый ряд: {console; file | `e}
  | RVar Taste            -- Переменная ряда: `e
  deriving (Show, Ord, Eq, Generic)

instance Sexp EffRow

instance Pretty EffRow where
  pretty = \case
    RClosed cons -> "{" <> T.intercalate "; " (map pretty cons) <> "}"
    ROpen cons t -> "{" <> T.intercalate "; " (map pretty cons) <> " | `" <> tasteName t <> "}"
    RVar n -> "`" <> tasteName n

data EffCons = EffCons ECons | EVar Taste deriving (Ord, Eq, Generic)

data ECons = ECons Text [TypeArg] deriving (Ord, Eq, Generic)

instance Show ECons where
  show (ECons n []) = T.unpack n
  show (ECons n tas) = T.unpack n <> " " <> show tas

instance Pretty ECons where
  pretty (ECons n args) = case args of
    [] -> n
    _ -> n <> "[" <> T.intercalate "; " (map pretty args) <> "]"

instance Sexp ECons
instance Sexp EffCons

instance Show EffCons where
  show = \case
    EffCons (ECons n []) -> "EffCons " <> T.unpack n
    EffCons (ECons n tas) -> "EffCons " <> T.unpack n <> " " <> show tas
    EVar n -> "EVar " <> show n

instance Pretty EffCons where
  pretty = \case
    EffCons e -> pretty e
    EVar n -> "`" <> tasteName n

-- | A declared effect: its name, the type parameters it abstracts over, and
--   its operations.
--
--   The parameters are kept as 'Taste's, not as names, because the operations
--   of the effect mention them by taste: a use site @Loop[Int]@ has to
--   replace exactly the variables the declaration bound, and two different
--   declarations may well use the same parameter name.
data EffDef = EffDef Text [Taste] [(Text, Funct)] deriving Show

effName :: EffDef -> Text
effName (EffDef n _ _) = n

instance Pretty EffDef where
  pretty (EffDef n ts ops) =
    T.concat [
      "effect ",
      n,
      if null ts then " " else "[" <> T.intercalate "; " (map tasteName ts) <> "] ",
      T.intercalate "; " $ map (\(n', f) -> n' <> " : " <> pretty f) ops,
      " end"
    ]

data RowDef = RowDef Text [Text] EffRow deriving (Show, Generic)

instance Pretty RowDef where
  pretty (RowDef n ts row) = T.concat [
      "row ", n,
      if null ts then "" else T.concat ["[", T.intercalate "; " ts, "]"],
      " = ", pretty row
    ]

-- | An expression together with the region of source it came from.  The
--   elaborator copies the position of the AST node it came from; nodes that
--   have no corresponding source text get 'noSpan'.
data Expr = MkExpr {
    exprSpan :: Span
  , exprNode :: ExprNode
  } deriving (Eq, Ord, Show)

-- | The shape of an expression, without its position.
data ExprNode =
    IntNode Integer
  | FloatNode Scientific
  | BooleanNode Bool
  | StringNode Text
  | NilNode
  | XVarNode Text
  | ArrayNode [Expr]
  | PairNode Expr Expr
  | XLambdaNode Lambda
  | NLambdaNode NativeLambdaSign
  | ApplyNode Expr Expr
  | RecordNode (Maybe Expr) [ERecordProp]
  | WithNode Expr [TypeArg] [EffCons] [EffRow]
  | HandleNode Handler
  | ParenNode Block
  | ResumeNode Expr
  | LetNode LetPattern Expr Expr
  | PropAccessNode Expr Text
  | IfElseNode Expr Expr Expr
  -- | @e : T@: the type the reader claims for an expression.
  | AnnotNode Expr Typ
  -- | @match e to clauses@.
  | MatchNode Expr [MatchClause]
  deriving (Eq, Ord, Show)

pattern Int :: Integer -> Expr
pattern Int i <- MkExpr _ (IntNode i) where
  Int i = MkExpr noSpan (IntNode i)

pattern Float :: Scientific -> Expr
pattern Float f <- MkExpr _ (FloatNode f) where
  Float f = MkExpr noSpan (FloatNode f)

pattern Boolean :: Bool -> Expr
pattern Boolean b <- MkExpr _ (BooleanNode b) where
  Boolean b = MkExpr noSpan (BooleanNode b)

pattern String :: Text -> Expr
pattern String s <- MkExpr _ (StringNode s) where
  String s = MkExpr noSpan (StringNode s)

pattern Nil :: Expr
pattern Nil <- MkExpr _ NilNode where
  Nil = MkExpr noSpan NilNode

pattern XVar :: Text -> Expr
pattern XVar n <- MkExpr _ (XVarNode n) where
  XVar n = MkExpr noSpan (XVarNode n)

pattern Array :: [Expr] -> Expr
pattern Array es <- MkExpr _ (ArrayNode es) where
  Array es = MkExpr (mergeSpans (map exprSpan es)) (ArrayNode es)

pattern Pair :: Expr -> Expr -> Expr
pattern Pair l r <- MkExpr _ (PairNode l r) where
  Pair l r = MkExpr (mergeSpan (exprSpan l) (exprSpan r)) (PairNode l r)

pattern XLambda :: Lambda -> Expr
pattern XLambda l <- MkExpr _ (XLambdaNode l) where
  XLambda l = MkExpr noSpan (XLambdaNode l)

pattern NLambda :: NativeLambdaSign -> Expr
pattern NLambda n <- MkExpr _ (NLambdaNode n) where
  NLambda n = MkExpr noSpan (NLambdaNode n)

pattern Apply :: Expr -> Expr -> Expr
pattern Apply f x <- MkExpr _ (ApplyNode f x) where
  Apply f x = MkExpr (mergeSpan (exprSpan f) (exprSpan x)) (ApplyNode f x)

pattern Record :: Maybe Expr -> [ERecordProp] -> Expr
pattern Record a ps <- MkExpr _ (RecordNode a ps) where
  Record a ps =
    MkExpr (mergeSpans (maybe [] (\x -> [exprSpan x]) a <> map (exprSpan . erExpr) ps)) (RecordNode a ps)

pattern With :: Expr -> [TypeArg] -> [EffCons] -> [EffRow] -> Expr
pattern With e ts es rs <- MkExpr _ (WithNode e ts es rs) where
  With e ts es rs = MkExpr (exprSpan e) (WithNode e ts es rs)

pattern Handle :: Handler -> Expr
pattern Handle h <- MkExpr _ (HandleNode h) where
  Handle h = MkExpr noSpan (HandleNode h)

pattern Paren :: Block -> Expr
pattern Paren b <- MkExpr _ (ParenNode b) where
  Paren b = MkExpr noSpan (ParenNode b)

pattern Resume :: Expr -> Expr
pattern Resume e <- MkExpr _ (ResumeNode e) where
  Resume e = MkExpr (exprSpan e) (ResumeNode e)

pattern Let :: LetPattern -> Expr -> Expr -> Expr
pattern Let p w b <- MkExpr _ (LetNode p w b) where
  Let p w b = MkExpr (mergeSpan (exprSpan w) (exprSpan b)) (LetNode p w b)

pattern PropAccess :: Expr -> Text -> Expr
pattern PropAccess e n <- MkExpr _ (PropAccessNode e n) where
  PropAccess e n = MkExpr (exprSpan e) (PropAccessNode e n)

pattern IfElse :: Expr -> Expr -> Expr -> Expr
pattern IfElse p t f <- MkExpr _ (IfElseNode p t f) where
  IfElse p t f =
    MkExpr (mergeSpan (exprSpan p) (mergeSpan (exprSpan t) (exprSpan f))) (IfElseNode p t f)

pattern Annot :: Expr -> Typ -> Expr
pattern Annot e t <- MkExpr _ (AnnotNode e t) where
  Annot e t = MkExpr (exprSpan e) (AnnotNode e t)

pattern Match :: Expr -> [MatchClause] -> Expr
pattern Match e cs <- MkExpr _ (MatchNode e cs) where
  Match e cs = MkExpr (exprSpan e) (MatchNode e cs)

{-# COMPLETE Int, Float, Boolean, String, Nil, XVar, Array, Pair, XLambda
   , NLambda, Apply, Record, With, Handle, Paren, Resume, Let, PropAccess
   , IfElse, Annot, Match #-}

-- | Move an expression to a different span.  Used by the elaborator, which
--   knows the span of the AST node a node came from.
atSpan :: Span -> Expr -> Expr
atSpan s e = e {exprSpan = s}

instance Pretty Expr where
  pretty (MkExpr _ n) = pretty n

instance Pretty ExprNode where
  pretty = \case
    IntNode i -> T.pack $ show i
    FloatNode f -> T.pack $ show f
    BooleanNode b -> if b then "true" else "false"
    StringNode s -> "'" <> s <> "'"
    NilNode -> "()"
    XVarNode n -> n
    ArrayNode es -> "[" <> T.intercalate " " (map pretty es) <> "]"
    PairNode l r -> "(" <> pretty l <> ", " <> pretty r <> ")"
    XLambdaNode l -> pretty l
    NLambdaNode (NativeLambdaSign n t r fxs) ->
      n <> " : " <> pretty t <> " -> " <> prettyFxs fxs <> pretty r
    ApplyNode f e -> pretty f <> " " <> pretty e
    RecordNode ext props ->
      "#{" <> maybe "" ((<> " | ") . pretty) ext
          <> T.intercalate "; " (map prettyERecordProp props) <> "}"
    WithNode e ts es rs ->
      pretty e <> " with [" <> T.intercalate "; " (map pretty ts) <> "]"
        <> (if null es then "" else " {" <> T.intercalate "; " (map pretty es) <> "}")
        <> (if null rs then "" else " " <> T.intercalate " " (map pretty rs))
    HandleNode h -> pretty h
    ParenNode b -> "(" <> pretty b <> ")"
    ResumeNode e -> "resume " <> pretty e
    LetNode p w b -> "let " <> prettyLetPattern p <> " = " <> pretty w <> " in " <> pretty b
    PropAccessNode e n -> pretty e <> "@" <> n
    IfElseNode p t f -> "if " <> pretty p <> " then " <> pretty t <> " else " <> pretty f
    AnnotNode e t -> pretty e <> " : " <> pretty t
    MatchNode e cs -> T.concat [
        "match ", pretty e, " to ", T.concat (map ((" " <>) . pretty) cs)
      ]

prettyERecordProp :: ERecordProp -> Text
prettyERecordProp p = T.concat [
    pretty (erMut p), " ", erName p,
    maybe "" ((" : " <>) . pretty) (erType p),
    " = ", pretty (erExpr p)
  ]

prettyLetPattern :: LetPattern -> Text
prettyLetPattern = \case
  LPATom a -> prettyAtomLetPattern a
  LPParam (LambdaParam n mt) ->
    "(" <> n <> maybe "" ((" : " <>) . pretty) mt <> ")"

prettyAtomLetPattern :: AtomLetPattern -> Text
prettyAtomLetPattern = \case
  ALPNil -> "()"
  ALPUnderscore -> "_"
  ALPPair a b -> "(" <> prettyLetPattern a <> ", " <> prettyLetPattern b <> ")"
  ALPRecord ps ->
    "#{" <> T.intercalate "; " (map prettyLetPatternRecordProp ps) <> "}"

prettyLetPatternRecordProp :: LetPatternRecordProp -> Text
prettyLetPatternRecordProp (LetPatternRecordProp m (LambdaParam n mt) pat) = T.concat [
    pretty m, " ", n,
    maybe "" ((" : " <>) . pretty) mt,
    maybe "" ((" = " <>) . prettyAtomLetPattern) pat
  ]

data TypeArg =
  TAInt
  | TAFloat
  | TABoolean
  | TAString
  | TANil
  | TANothing
  | TAFlat Text
  | TAArray TypeArg
  | TAPair TypeArg TypeArg
  | TAFunct TypeArg TypeArg
  | TARecord [TARecordProp]
  -- | A declared enumeration used as a type argument, @Maybe[Int]@.
  | TAEnum Text [TypeArg]
  | TAVar Taste
  deriving (Eq, Ord, Show, Generic)

instance Sexp TypeArg

instance Pretty TypeArg where
  pretty = \case
    TAInt -> "Int"
    TAFloat -> "Float"
    TABoolean -> "Boolean"
    TANil -> "()"
    TANothing -> "Nothing"
    TAString -> "String"
    TAFlat n -> n
    TAArray t -> T.concat ["[", pretty t, "]"]
    TAPair l r -> T.concat ["(", pretty l, ", ", pretty r, ")"]
    TAFunct i o -> T.concat [pretty i, " -> ", pretty o]
    TARecord props -> T.concat [
        "#{",
        T.intercalate "; " [T.unwords [pretty m, n, ":", pretty t] | TARecordProp m n t <- props],
        "}"
      ]
    TAEnum n args ->
      n <> if null args then "" else T.concat ["#[", T.intercalate "; " (map pretty args), "]"]
    TAVar v -> tasteName v

data TARecordProp = TARecordProp Mutability Text TypeArg deriving (Eq, Ord, Show, Generic)
instance Sexp TARecordProp

data LetPattern = LPATom AtomLetPattern | LPParam LambdaParam deriving (Eq, Ord, Show)

data AtomLetPattern =
  ALPNil
  | ALPUnderscore
  | ALPPair LetPattern LetPattern
  | ALPRecord [LetPatternRecordProp]
  deriving (Eq, Ord, Show)

data LetPatternRecordProp =
  LetPatternRecordProp Mutability LambdaParam (Maybe AtomLetPattern) deriving (Eq, Ord, Show)

data LambdaParam = LambdaParam Text (Maybe Typ) deriving (Eq, Ord, Show)
data ERecordProp = ERecordProp {
  erMut :: Mutability,
  erName :: Text,
  erType :: Maybe Typ,
  erExpr :: Expr
} deriving (Show, Eq, Ord)

data NativeLambdaSign = NativeLambdaSign Text Typ Typ EffRow deriving (Eq, Ord, Show)

prettyTvars :: [Taste] -> Bool -> Text
prettyTvars ts skipBrackets =
  if null ts then
    if skipBrackets then "" else "[]"
  else
    "[" <> T.intercalate "; " (map tasteName ts) <> "] "

data Lambda = Lambda {
  lTvars :: [Taste],
  lEvars :: [Taste],
  lArg   ::  Text,
  lArgT  ::  Maybe Typ,
  lRetT  ::  Maybe Typ,
  lFxs   ::  EffRow,
  lBlock ::  Block
} deriving (Eq, Ord)

instance Pretty Lambda where
  pretty (Lambda ts es n t r fxs b) = T.concat [
      "{",
      prettyTvars ts True,
      if null es then "" else "{" <> T.intercalate "; " (map tasteName es) <> "} ",
      "(", n, maybe "" ((" : " <>) . pretty) t, ")",
      " : ",
      prettyFxs fxs,
      maybe "" pretty r,
      " = ",
      pretty b,
      "}"
    ]

-- | A latent effect row in a function type: compact, and omitted when empty,
--   because @{}Int@ reads as if the type were mangled.
prettyFxs :: EffRow -> Text
prettyFxs = \case
  RClosed [] -> ""
  fxs -> pretty fxs <> " "

instance Show Lambda where
  show (Lambda ts es arg argT retT fxs block) =
    concat [
      "{",
      concat ["[", intercalate "; " $ map show ts, "]"],
      concat ["{", intercalate "; " $ map show es, "}"],
      T.unpack arg,
      maybe "" ((<> " ") . show) argT,
      show fxs,
      maybe "" ((<> " ") . show) retT,
      " = ",
      show block,
      "}"
    ]

-- type NativeBlock  = (Typ, Expr)
type Block        = ([Stat], Expr)

-- | The region a block covers: from its first statement to its result
--   expression.  Blocks are a pair rather than a record, so the span is
--   derived from the parts that have one.
blockSpan :: Block -> Span
blockSpan (stats, e) = mergeSpans (map statSpan stats <> [exprSpan e])

instance Pretty Block where
  pretty (stats, e) = T.concat [
      T.intercalate "; " $ map pretty stats,
      if null stats then "" else "; ",
      pretty e
    ]

-- | A statement of the IR, with the source region it came from.
data Stat = MkStat {
    statSpan :: Span
  , statNode :: StatNode
  } deriving (Eq, Ord)

-- | The shape of a statement, without its position.
data StatNode =
    BindNode Mutability Text (Maybe Typ) Expr
  | AssignNode Text [Text] Expr
  | ExprNode Expr
  deriving (Eq, Ord, Show)

pattern Bind :: Mutability -> Text -> Maybe Typ -> Expr -> Stat
pattern Bind m n t e <- MkStat _ (BindNode m n t e) where
  Bind m n t e = MkStat (exprSpan e) (BindNode m n t e)

-- | @x := e@ and @r@a@b := e@: the name, the fields leading to the assigned
--   field (empty for a plain rebinding), and the right-hand side.
pattern Assign :: Text -> [Text] -> Expr -> Stat
pattern Assign n path e <- MkStat _ (AssignNode n path e) where
  Assign n path e = MkStat (exprSpan e) (AssignNode n path e)

pattern Expr :: Expr -> Stat
pattern Expr e <- MkStat _ (ExprNode e) where
  Expr e = MkStat (exprSpan e) (ExprNode e)

{-# COMPLETE Bind, Assign, Expr #-}

-- | Move a statement to the given span.
atStatSpan :: Span -> Stat -> Stat
atStatSpan s st = st {statSpan = s}

instance Pretty Stat where
  pretty = pretty . statNode

instance Pretty StatNode where
  pretty = \case
    BindNode m n t e -> T.concat [pretty m, " ", n, maybe "" ((" " <>) . pretty) t, " = ", pretty e]
    AssignNode n path e -> T.concat [n, T.concat (map (T.append "@") path), " := ", pretty e]
    ExprNode e -> pretty e

instance Show Stat where
  show = \case
    Bind m name typ expr ->
      show m <> " " <> T.unpack name <> maybe "" ((" " <>) . show) typ <> " = " <> show expr
    Assign name path expr ->
      T.unpack name <> concatMap ('@' :) (map T.unpack path) <> " := " <> show expr
    Expr expr -> show expr

-- | A pattern of a @match@ clause, after elaboration.
--
--   The elaborator resolves the types a @val@ pattern walks and the type of a
--   cast, so a pattern carries no syntax of its own that the checker would
--   have to look up again.
data Pattern = MkPattern {
    patSpan :: Span
  , patNode :: PatternNode
  } deriving (Eq, Ord, Show)

data PatternNode =
    PInt Integer
  | PFloat Scientific
  | PString Text
  | PNil
  | PBoolean Bool
  -- | A bare name binds the component it stands for.
  | PName Text
  -- | @val r@a@b@: the value must equal the one the path already holds.
  | PVal Expr [Text]
  | PArray [Pattern] (Maybe Pattern)
  | PTuple [Pattern]
  | PCon Text [Pattern]
  | PAs Pattern Text
  | PCast Pattern Typ
  | PWildcard
  | PStarts Pattern Pattern
  | PEnds Pattern Pattern
  deriving (Eq, Ord, Show)

instance Pretty Pattern where
  pretty (MkPattern _ n) = pretty n

instance Pretty PatternNode where
  pretty = \case
    PInt i -> T.pack $ show i
    PFloat f -> T.pack $ show f
    PString s -> T.concat ["'", s, "'"]
    PNil -> "()"
    PBoolean b -> if b then "true" else "false"
    PName n -> n
    PVal e ns -> T.concat ["val ", pretty e, T.concat (map ("@" <>) ns)]
    PArray ps t ->
      T.concat ["[", T.unwords $ map pretty ps, maybe "" (("; " <>) . pretty) t, "]"]
    PTuple ps -> T.intercalate ", " $ map pretty ps
    PCon n ps -> T.unwords $ ("#" <> n) : map pretty ps
    PAs p n -> T.concat [pretty p, " as ", n]
    PCast p t -> T.concat [pretty p, " : ", pretty t]
    PWildcard -> "_"
    PStarts l r -> T.concat [pretty l, " |-> ", pretty r]
    PEnds l r -> T.concat [pretty l, " <-| ", pretty r]

-- | A clause of a @match@: the patterns it accepts (more than one for a
--   primitive clause), an optional guard and the block it selects.
data MatchClause = MatchClause [Pattern] (Maybe Expr) Block
  deriving (Eq, Ord, Show)

instance Pretty MatchClause where
  pretty (MatchClause ps g b) = T.concat [
      "| ", T.unwords $ map pretty ps,
      maybe "" ((" if " <>) . pretty) g,
      " => ", pretty b
    ]

-- | One case of a declared enumeration: the constructor and its fields.
--
--   A field is a name, a mutability and a type.  The mutability is how the
--   value the field holds is reached: @val@ is a value, @var@ is a cell the
--   constructor creates, and @imm@ is a snapshot.
data EnumCase = EnumCase Text [(Mutability, Text, Typ)]
  deriving (Eq, Ord, Show)

instance Pretty EnumCase where
  pretty (EnumCase n fs) = T.concat [
      "| ", n,
      T.concat [T.concat [" (", pretty m, " ", f, " : ", pretty t, ")"]
               | (m, f, t) <- fs]
    ]

-- | A declared enumeration after elaboration.
--
--   The type parameters are the rigid variables their fields mention, so a
--   constructor's scheme quantifies exactly them and `Maybe[Int]` substitutes
--   the argument for the variable in every field at once.
data EnumDef = EnumDef Text [Taste] [EnumCase]
  deriving (Eq, Ord, Show)

enumName :: EnumDef -> Text
enumName (EnumDef n _ _) = n

enumParams :: EnumDef -> [Taste]
enumParams (EnumDef _ ps _) = ps

enumCases :: EnumDef -> [EnumCase]
enumCases (EnumDef _ _ cs) = cs

enumCaseName :: EnumCase -> Text
enumCaseName (EnumCase n _) = n

enumCaseFields :: EnumCase -> [(Mutability, Text, Typ)]
enumCaseFields (EnumCase _ fs) = fs

-- | The type of a constructor: one arrow per field, ending in the enum
--   applied to the declaration's parameters.
constructorTyp :: EnumDef -> EnumCase -> Typ
constructorTyp def c =
  buildCurriedEnum
    [t | (_, _, t) <- enumCaseFields c]
    (TEnum (enumName def) (map TAVar (enumParams def)))
  where
    -- A constructor with a `var` field allocates that field's cell, so its
    -- last arrow performs `Var` (a mutable binding is created) and carries
    -- `Cell` (the value owns storage the block did not have before).  The row
    -- is on the type rather than on the application so that the charge cannot
    -- be lost: an aliased constructor (`val c = MkBox; c 1`) or one passed to
    -- a function (`apply2 MkBox`) pays the same row as a direct `MkBox 1`.
    createsCell = any (\(m, _, _) -> m == Var) (enumCaseFields c)
    outRow
      | createsCell = RClosed [EffCons $ ECons "Var" [], EffCons $ ECons "Cell" []]
      | otherwise = RClosed []
    buildCurriedEnum fs out = case fs of
      [] -> out
      [t] -> TFunct (Funct t out outRow)
      (t:ts) -> tfunc t (buildCurriedEnum ts out)

instance Pretty EnumDef where
  pretty (EnumDef n ps cs) = T.concat [
      "enum ", n,
      if null ps then "" else T.concat ["[", T.unwords (map tasteName ps), "]"],
      T.concat (map ((" " <>) . pretty) cs)
    ]

-- | A top-level declaration with the region of source it came from.  The
--   type checker reports duplicates, which are found after elaboration has
--   thrown the syntax away, so the position has to travel with the node.
data TopLevelStat =
  SFunctDef Span FunctDecl
  | STypeDef Span Text [Text] {-[String]-} Typ
  | SEffDef Span EffDef
  | SRowDef Span RowDef
  | SEnumDef Span EnumDef
  deriving (Show, Generic)
instance Sexp TopLevelStat where sexp = show

-- | The position of a declaration, whatever its kind.
topLevelSpan :: TopLevelStat -> Span
topLevelSpan = \case
  SFunctDef s _ -> s
  STypeDef s _ _ _ -> s
  SEffDef s _ -> s
  SRowDef s _ -> s
  SEnumDef s _ -> s

instance Pretty TopLevelStat where
  pretty = \case
    SFunctDef _ f -> pretty f
    SRowDef _ r -> pretty r
    SEffDef _ e -> pretty e
    SEnumDef _ e -> pretty e
    s -> T.pack $ show s

data FunctDecl = FunctDecl {
  fName  :: Text,
  fTvars  :: [Text],
  fEvars  :: [Text],
  fRvars  :: [Text],
  fArgs   :: [(Text, Typ)],
  fRet    :: (Maybe EffRow, Typ),
  fBlock :: Block
}  deriving (Show, Generic)

instance Pretty FunctDecl where
  pretty (FunctDecl n ts es rs args (fx, t) b) =
    T.concat [
      "funct ", n,
      "[" <> T.unwords ts <> "]",
      "{" <> T.unwords es <> (if null rs then "" else " | " <> T.unwords rs) <> "}",
      T.unwords $ map (\(n', t') -> "(" <> n' <> " : " <> pretty t' <> ")") args,
      " : ", maybe "" ((<> " ") . pretty) fx, pretty t, " = ", pretty b
    ]

instance Sexp FunctDecl where sexp = show

--eff block clauses then
data Handler = Handler EffCons Block [HandlerClause] Lambda
  deriving (Eq, Ord, Show)

instance Pretty Handler where
  pretty = \case
    -- NativeHandler _eff _block _clauses _then -> ""
    Handler eff block clauses _then -> T.concat [
        "under ", pretty eff, " to ", pretty block,
        " handle ", T.unwords $ map pretty clauses,
        pretty _then
      ]

-- type NativeHandlerClause  = (Text, NativeLambdaSign)
type HandlerClause = (Text, Lambda)

instance Pretty HandlerClause where
  pretty (n, Lambda _ _ n' _ _ _ b) = T.concat [
      " | ", n, " ", n', " => ", pretty b
    ]


-- eff clauses
data HandlerSig = HandlerSig EffCons [(Text, Funct)] deriving Show

type Chunk = Module TopLevelStat

data Mutability = Val | Var | Imm deriving (Eq, Ord, Generic)

instance Sexp Mutability
instance Pretty Mutability
instance Show Mutability where show = \case Val -> "val"; Var -> "var"; Imm -> "imm"
instance PrintfArg Mutability where formatArg = formatArg . show


tfunc :: Typ -> Typ -> Typ
tfunc i = TFunct . pureFunct i

pureFunct :: Typ -> Typ -> Funct
pureFunct i o = Funct i o $ RClosed []

pureTFunc :: [Typ] -> Maybe Typ
pureTFunc = \case
  [] -> Nothing
  [i, o] -> Just $ tfunc i o
  (i : o) -> tfunc i <$> pureTFunc o

tasteName :: Taste -> Text
tasteName = \case
  Skolem s _ _ -> s
  Meta m _ _ -> m
  Bound b _ -> b

metaLevel :: Taste -> Maybe Int
metaLevel = \case
  Meta _ _ lvl -> Just lvl
  Skolem _ _ lvl -> Just lvl
  _ -> Nothing

isSkolem :: Taste -> Bool
isSkolem Skolem {} = True
isSkolem _ = False

-- | A type argument seen as a type.
--
--   A parameter of a parameterised effect, @effect Loop[T] ... break : T -> ()@,
--   is a type in the operation signatures but a type argument in the effect
--   row @Loop[T]@.  The two live in different constructors ('T'Var' against
--   @TAVar@), so a substitution has to cross between them; these two functions
--   are that crossing.
typeArgToTyp :: TypeArg -> Typ
typeArgToTyp = \case
  TAInt -> TInt
  TAFloat -> TFloat
  TABoolean -> TBoolean
  TAString -> TString
  TANil -> TNil
  TANothing -> TNothing
  TAFlat n -> TFlat n
  TAArray t -> TArray (typeArgToTyp t) (RClosed [])
  TAPair l r -> TPair (typeArgToTyp l) (typeArgToTyp r) (RClosed [])
  TAFunct i o -> TFunct (Funct (typeArgToTyp i) (typeArgToTyp o) (RClosed []))
  TARecord props -> TRecord [TRecordProp m n (typeArgToTyp t) | TARecordProp m n t <- props] (RClosed [])
  TAEnum n args -> TEnum n args
  TAVar v -> TVar v

-- | A type seen as a type argument, when it has a type-argument shape.
--   A function type with an effect row has none: effect arguments carry
--   pure arrows only, so such a type cannot appear in an effect row.  An
--   aggregate with a non-empty pending row has none either, for the same
--   reason.
typToTypeArg :: Typ -> Maybe TypeArg
typToTypeArg = \case
  TInt -> Just TAInt
  TFloat -> Just TAFloat
  TBoolean -> Just TABoolean
  TString -> Just TAString
  TNil -> Just TANil
  TNothing -> Just TANothing
  TFlat n -> Just (TAFlat n)
  TArray t (RClosed []) -> TAArray <$> typToTypeArg t
  TPair l r (RClosed []) -> TAPair <$> typToTypeArg l <*> typToTypeArg r
  TFunct (Funct i o (RClosed [])) -> TAFunct <$> typToTypeArg i <*> typToTypeArg o
  TRecord props (RClosed []) ->
    TARecord <$> traverse (\(TRecordProp m n t) -> TARecordProp m n <$> typToTypeArg t) props
  TEnum n args -> Just (TAEnum n args)
  TVar v -> Just (TAVar v)
  _ -> Nothing

handlerCons :: Handler -> EffCons
-- handlerCons (NativeHandler cons _ _ _) = cons
handlerCons (Handler cons _ _ _) = cons

-- Funct Typ Typ EffRow
countArgs :: Funct -> Int
countArgs (Funct _ tf _) = case tf of
  TFunct f -> 1 + countArgs f
  _ -> 1