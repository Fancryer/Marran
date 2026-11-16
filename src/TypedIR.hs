{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PatternSynonyms #-}

module TypedIR(
  TypedExpr(..),
  TypedExprNode(..),
  pattern TEInt, pattern TEFloat, pattern TEBoolean, pattern TEString,
  pattern TENil, pattern TEXVar, pattern TEArray, pattern TEPair,
  pattern TEXLambda, pattern TENLambda, pattern TEApply, pattern TERecord,
  pattern TEHandle, pattern TEParen, pattern TEResume, pattern TELet,
  pattern TEPropAccess, pattern TEIfElse,
  pattern TEAnnot,
  pattern TEMatch,
  Pattern(..),
  PatternNode(..),
  MatchClause(..),
  TPattern(..),
  TPatternNode(..),
  TMatchClause(..),
  EnumDef(..),
  EnumCase(..),
  atTypedSpan,
  teSpan,
  Block,
  Lambda(..),
  Stat(..),
  StatNode(..),
  pattern Bind, pattern Rebind, pattern Expr,
  atTypedStatSpan, tStatSpan, blockSpan,
  FunctDecl(..),
  Handler(..),
  Scope(..),
  ValueBinding(..),
  TERecordProp(..),
  TopLevelStat(..),
  HandlerClause,
  typeOfTypedExpr,
  typeOfTypedBlock,
  Chunk
)
where
import Types (
    Typ(..),
    EffRow(..),
    ECons(..),
    Expr,
    Taste,
    Mutability,
    TypeArg,
    LetPattern,
    EffRow,
    TypeScheme,
    EffDef,
    HandlerSig,
    -- NativeHandlerClause,
    TRecordProp(..),
    Funct(..),
    -- NativeLambdaSign(NativeLambdaSign),
    RowDef,
    EffCons, NativeLambdaSign (..), TasteMap,
    Pattern(..), PatternNode(..), MatchClause(..), EnumDef(..), EnumCase(..)
  )
import Data.Scientific (Scientific)
import qualified Data.Text as T
import Data.Text (Text)
import Utils (Pretty (..), TextMap)
import Data.Map (Map)
import Data.List (find)
import Resume (ResumeInfo)
import Span (Span, noSpan, mergeSpan, mergeSpans)
import Module (Module(..))
import Data.Set (Set)

type TypeScope  = TextMap Typ

-- | A value binding in the scope.  The pending row is the effect of forcing
--   the delayed computation the name stands for (T-Var in the paper): the
--   declaration row plus the mention row for a @val@ binding, the row variable
--   that bounds every assignment for a @var@ binding, and the frozen row for
--   an @imm@ binding.  It is kept next to the scheme rather than inside it
--   because a function declaration has no pending row of its own: calling the
--   function is what pays its latent row.
data ValueBinding = ValueBinding {
    vbScheme :: TypeScheme,
    vbExpr   :: Expr,
    vbMut    :: Mutability,
    vbRow    :: EffRow
  } deriving Show

type ValueScope = TextMap ValueBinding
type EffScope   = TextMap EffDef

type TypeSubst    = TasteMap Typ
type TypeArgSubst = TasteMap TypeArg
type EffSubst     = TasteMap EffCons
type RowSubst     = TasteMap EffRow

data Scope = Scope {
  types         :: TypeScope,
  values        :: ValueScope,
  effects       :: EffScope,
  -- | The declarations of the enumerations in scope.  A type is enough to
  --   name an enum, but a @match@ has to know its cases to be checked for
  --   exhaustiveness, so the declaration is kept next to the type.
  enums         :: TextMap EnumDef,

  handlerSig    :: Maybe HandlerSig,

  typeSubst     :: TypeSubst,
  typeArgSubst  :: TypeArgSubst,
  effSubst      :: EffSubst,
  rowSubst      :: RowSubst,

  effLacks      :: TasteMap (Set Text),
  rowLacks      :: TasteMap (Set Text),

  parent        :: Maybe Scope
} deriving (Show)

data TypedExpr = MkTypedExpr {
    teSpan :: Span
  , teNode :: TypedExprNode
  }

-- | The shape of a typed expression, without its position.
data TypedExprNode =
    TEIntNode Integer
  | TEFloatNode Scientific
  | TEBooleanNode Bool
  | TEStringNode Text
  | TENilNode
  | TEXVarNode Text Typ
  | TEArrayNode Typ EffRow [TypedExpr]
  | TEPairNode EffRow TypedExpr TypedExpr
  | TEXLambdaNode Lambda
  | TENLambdaNode NativeLambdaSign
  | TEApplyNode TypedExpr TypedExpr
  | TERecordNode (Maybe TypedExpr) [TERecordProp] EffRow
  | TEHandleNode Handler Typ
  | TEParenNode Block
  | TEResumeNode TypedExpr Typ
  | TELetNode LetPattern TypedExpr TypedExpr
  | TEPropAccessNode TypedExpr Text
  | TEIfElseNode TypedExpr TypedExpr TypedExpr
  -- | @e : T@.  The annotation is transparent at run time: the expression is
  --   evaluated as if it were written alone.
  | TEAnnotNode TypedExpr Typ
  -- | @match e to clauses@: the subject, the type the whole form has, and the
  --   clauses, each with the patterns it accepts, an optional guard and the
  --   block it selects.
  | TEMatchNode TypedExpr Typ [TMatchClause]
  deriving (Show)

pattern TEInt :: Integer -> TypedExpr
pattern TEInt i <- MkTypedExpr _ (TEIntNode i) where
  TEInt i = MkTypedExpr noSpan (TEIntNode i)

pattern TEFloat :: Scientific -> TypedExpr
pattern TEFloat f <- MkTypedExpr _ (TEFloatNode f) where
  TEFloat f = MkTypedExpr noSpan (TEFloatNode f)

pattern TEBoolean :: Bool -> TypedExpr
pattern TEBoolean b <- MkTypedExpr _ (TEBooleanNode b) where
  TEBoolean b = MkTypedExpr noSpan (TEBooleanNode b)

pattern TEString :: Text -> TypedExpr
pattern TEString s <- MkTypedExpr _ (TEStringNode s) where
  TEString s = MkTypedExpr noSpan (TEStringNode s)

pattern TENil :: TypedExpr
pattern TENil <- MkTypedExpr _ TENilNode where
  TENil = MkTypedExpr noSpan TENilNode

pattern TEXVar :: Text -> Typ -> TypedExpr
pattern TEXVar n t <- MkTypedExpr _ (TEXVarNode n t) where
  TEXVar n t = MkTypedExpr noSpan (TEXVarNode n t)

pattern TEArray :: Typ -> EffRow -> [TypedExpr] -> TypedExpr
pattern TEArray t r es <- MkTypedExpr _ (TEArrayNode t r es) where
  TEArray t r es = MkTypedExpr noSpan (TEArrayNode t r es)

pattern TEPair :: EffRow -> TypedExpr -> TypedExpr -> TypedExpr
pattern TEPair r l e <- MkTypedExpr _ (TEPairNode r l e) where
  TEPair r l e = MkTypedExpr (mergeSpan (teSpan l) (teSpan e)) (TEPairNode r l e)

pattern TEXLambda :: Lambda -> TypedExpr
pattern TEXLambda l <- MkTypedExpr _ (TEXLambdaNode l) where
  TEXLambda l = MkTypedExpr noSpan (TEXLambdaNode l)

pattern TENLambda :: NativeLambdaSign -> TypedExpr
pattern TENLambda l <- MkTypedExpr _ (TENLambdaNode l) where
  TENLambda l = MkTypedExpr noSpan (TENLambdaNode l)

pattern TEApply :: TypedExpr -> TypedExpr -> TypedExpr
pattern TEApply f x <- MkTypedExpr _ (TEApplyNode f x) where
  TEApply f x = MkTypedExpr (mergeSpan (teSpan f) (teSpan x)) (TEApplyNode f x)

pattern TERecord :: Maybe TypedExpr -> [TERecordProp] -> EffRow -> TypedExpr
pattern TERecord a ps r <- MkTypedExpr _ (TERecordNode a ps r) where
  TERecord a ps r =
    MkTypedExpr (mergeSpans (maybe [] (\x -> [teSpan x]) a <> map (teSpan . terExpr) ps)) (TERecordNode a ps r)

pattern TEHandle :: Handler -> Typ -> TypedExpr
pattern TEHandle h t <- MkTypedExpr _ (TEHandleNode h t) where
  TEHandle h t = MkTypedExpr noSpan (TEHandleNode h t)

pattern TEParen :: Block -> TypedExpr
pattern TEParen b <- MkTypedExpr _ (TEParenNode b) where
  TEParen b = MkTypedExpr noSpan (TEParenNode b)

pattern TEResume :: TypedExpr -> Typ -> TypedExpr
pattern TEResume e t <- MkTypedExpr _ (TEResumeNode e t) where
  TEResume e t = MkTypedExpr (teSpan e) (TEResumeNode e t)

pattern TELet :: LetPattern -> TypedExpr -> TypedExpr -> TypedExpr
pattern TELet p w b <- MkTypedExpr _ (TELetNode p w b) where
  TELet p w b = MkTypedExpr (mergeSpan (teSpan w) (teSpan b)) (TELetNode p w b)

pattern TEPropAccess :: TypedExpr -> Text -> TypedExpr
pattern TEPropAccess e n <- MkTypedExpr _ (TEPropAccessNode e n) where
  TEPropAccess e n = MkTypedExpr (teSpan e) (TEPropAccessNode e n)

pattern TEIfElse :: TypedExpr -> TypedExpr -> TypedExpr -> TypedExpr
pattern TEIfElse p t f <- MkTypedExpr _ (TEIfElseNode p t f) where
  TEIfElse p t f =
    MkTypedExpr (mergeSpan (teSpan p) (mergeSpan (teSpan t) (teSpan f))) (TEIfElseNode p t f)

-- | @e : T@.  The span is the one of the annotated expression, so an error
--   inside the annotation is reported where the reader reads it.
pattern TEAnnot :: TypedExpr -> Typ -> TypedExpr
pattern TEAnnot e t <- MkTypedExpr _ (TEAnnotNode e t) where
  TEAnnot e t = MkTypedExpr (teSpan e) (TEAnnotNode e t)

pattern TEMatch :: TypedExpr -> Typ -> [TMatchClause] -> TypedExpr
pattern TEMatch e t cs <- MkTypedExpr _ (TEMatchNode e t cs) where
  TEMatch e t cs = MkTypedExpr (teSpan e) (TEMatchNode e t cs)

{-# COMPLETE TEInt, TEFloat, TEBoolean, TEString, TENil, TEXVar, TEArray
   , TEPair, TEXLambda, TENLambda, TEApply, TERecord, TEHandle, TEParen
   , TEResume, TELet, TEPropAccess, TEIfElse, TEAnnot, TEMatch #-}

-- | Move a typed expression to the given span.
atTypedSpan :: Span -> TypedExpr -> TypedExpr
atTypedSpan s e = e {teSpan = s}

instance Show TypedExpr where
  show = \case
    TEInt i -> show i
    TEFloat f -> show f
    TEBoolean b -> show b
    TEString s -> show s
    TENil -> "Nil"
    TEXVar v t -> "(XVar " <> show v <> " " <> show t <> ")"
    TEArray t r entries -> "(Array " <> show t <> " " <> show r <> " (" <> unwords (map show entries) <> "))"
    TEPair r l e -> "(Pair " <> show r <> " " <> show l <> " " <> show e <> ")"
    TEXLambda lam -> "(XLambda " <> show lam <> ")"
    TENLambda lam -> "(NLambda " <> show lam <> ")"
    TEApply f x -> "(Apply " <> show f <> " " <> show x <> ")"
    TERecord Nothing props _ -> "(Record " <> show props <> ")"
    TERecord (Just anchor) props r -> "(Record-extend " <> show r <> " " <> show anchor <> " | " <> show props <> ")"
    TEHandle handler t -> "(Handle " <> show handler <> " " <> show t <> ")"
    TEParen (stats, expr) -> "(Paren " <> unwords (map show stats) <> " " <> show expr <> ")"
    TEResume expr t -> "(Resume " <> show expr <> " " <> show t <> ")"
    TELet pat bound body -> "(Let " <> show pat <> " " <> show bound <> " " <> show body <> ")"
    TEPropAccess expr field -> "(Prop " <> show expr <> " " <> show field <> ")"
    TEIfElse cond thenExpr elseExpr -> "(If " <> show cond <> " " <> show thenExpr <> " " <> show elseExpr <> ")"
    TEAnnot e t -> "(Annot " <> show e <> " " <> show t <> ")"
    TEMatch e t cs -> "(Match " <> show e <> " " <> show t <> " " <> show (length cs) <> ")"

instance Pretty TypedExpr where
  pretty = \case
    TEInt i -> T.pack $ show i
    TEFloat f -> T.pack $ show f
    TEBoolean b -> if b then "true" else "false"
    TEString s -> "'" <> s <> "'"
    TENil -> "()"
    TEXVar n _ -> n
    TEArray _ _ es -> T.concat ["[", T.concat $ map pretty es ,"]"]
    TEPair _ l r -> T.concat ["(", pretty l, ", ", pretty r, ")"]
    TEXLambda l -> pretty l
    TENLambda _ -> "!closure!"
    TEApply f e -> pretty f <> " " <> pretty e
    TERecord Nothing ps _ -> T.concat ["${", T.intercalate "; " $ map pretty ps, "}"]
    TERecord (Just anchor) ps _ -> T.concat ["${", pretty anchor, " | ", T.intercalate "; " $ map pretty ps, "}"]
    TEHandle h _ -> pretty h
    TEParen b -> "(" <> pretty b <> ")"
    TEResume e t -> "resume " <> pretty e
    -- -- Let LetPattern TypedExpr TypedExpr
    -- PropAccess e n -> pretty e <> "@" <> n
    TEIfElse p t f -> "if " <> pretty p <> " then " <> pretty t <> " else " <> pretty f
    TEAnnot e t -> pretty e <> " : " <> pretty t
    TEMatch e _ cs -> T.concat [
        "match ", pretty e, " to ", T.concat (map ((" " <>) . pretty) cs)
      ]
    e -> T.pack $ show e

data TERecordProp = TERecordProp {
    terMut :: Mutability,
    terName :: Text,
    terType :: Typ,
    terExpr :: TypedExpr
  } deriving Show

instance Pretty TERecordProp

data Lambda = Lambda {
    lTvars :: [Taste],
    lEvars :: [Taste],
    lArg   ::  Text,
    lArgT  ::  Typ,
    lRetT  ::  Typ,
    lFxs   ::  EffRow,
    lBlock ::  Block
  }

instance Show Lambda where
  show (Lambda ts es arg argT retT fxs block) =
    concat [
      "(Lambda",
      if null ts then "" else " [" <> unwords (map show ts) <> "]",
      if null es then "" else " {" <> unwords (map show es) <> "}",
      " (", show arg, " : ", show argT, ") : ",
      show fxs, " ", show retT,
      " ", show block,
      ")"
    ]

instance Pretty Lambda where
  pretty (Lambda ts es arg argT retT fxs block) =
    T.concat [
      "{",
      if null ts then "" else " [" <> T.unwords (map pretty ts) <> "]",
      if null es then "" else " {" <> T.unwords (map pretty es) <> "}",
      " (", pretty arg, " : ", pretty argT, ")",
      case fxs of
        RClosed [] -> " : "
        _ -> " : " <> pretty fxs <> " ",
      pretty retT,
      " = ", pretty block, "}"
    ]

type Block = ([Stat], TypedExpr)

-- | The region a block covers, derived from its parts.
blockSpan :: Block -> Span
blockSpan (stats, e) = mergeSpans (map tStatSpan stats <> [teSpan e])

instance Pretty Block where
  pretty (stats, e) = T.concat [
      T.intercalate "; " $ map pretty stats,
      if null stats then "" else "; ",
      pretty e
    ]

-- | A statement of the typed IR, with the source region it came from.
data Stat = MkStat {
    tStatSpan :: Span
  , tStatNode :: StatNode
  }

-- | The shape of a typed statement, without its position.
data StatNode =
    BindNode Mutability Text TypedExpr
  -- | @x := e@ or @r@a@b := e@: the leading name, the fields walked from it,
  --   and the right-hand side.
  | RebindNode Text [Text] TypedExpr
  | ExprNode TypedExpr
  deriving (Show)

pattern Bind :: Mutability -> Text -> TypedExpr -> Stat
pattern Bind m n e <- MkStat _ (BindNode m n e) where
  Bind m n e = MkStat (teSpan e) (BindNode m n e)

pattern Rebind :: Text -> [Text] -> TypedExpr -> Stat
pattern Rebind n path e <- MkStat _ (RebindNode n path e) where
  Rebind n path e = MkStat (teSpan e) (RebindNode n path e)

pattern Expr :: TypedExpr -> Stat
pattern Expr e <- MkStat _ (ExprNode e) where
  Expr e = MkStat (teSpan e) (ExprNode e)

{-# COMPLETE Bind, Rebind, Expr #-}

-- | Move a statement to the given span.
atTypedStatSpan :: Span -> Stat -> Stat
atTypedStatSpan s st = st {tStatSpan = s}

instance Show Stat where
  show (MkStat _ n) = show n

instance Pretty Stat where
  pretty = pretty . tStatNode

instance Pretty StatNode where
  pretty = \case
    BindNode m n e -> T.concat [pretty m, " ", n, " = ", pretty e]
    RebindNode n path e -> T.concat [n, T.concat (map (T.append "@") path), " := ", pretty e]
    ExprNode e -> pretty e

data FunctDecl = FunctDecl {
    fName  :: Text,
    fTvars  :: [Text],
    fEvars  :: [Text],
    fArgs  :: [(Text, Typ)],
    fRet    :: (Maybe EffRow, Typ),
    fBlock :: Block
  }

instance Show FunctDecl where
  show (FunctDecl n ts es args (retR, retT) block) =
    concat [
      "(FunctDecl ", show n,
      if null ts then "" else " [" <> unwords (map show ts) <> "]",
      if null es then "" else " {" <> unwords (map show es) <> "}",
      if null args then "()" else unwords (map show args),
      maybe "" ((" " <>) . show) retR,
      show retT,
      show block,
      ")"
    ]

instance Pretty FunctDecl where
  pretty (FunctDecl n ts es args (retR, retT) block) =
    T.concat [
      "funct ", n,
      if null ts then "" else " [" <> T.unwords ts <> "]",
      if null es then "" else " {" <> T.unwords es <> "}",
      if null args then "()" else T.unwords $
        flip map args $ \(n', t) ->
          T.concat ["(", n', " : ", pretty t,")"],
      " : ",
      maybe "" ((<> " ") . pretty) retR,
      pretty retT, " = ", pretty block
    ]

--eff block clauses then
data Handler =
  -- NativeHandler ECons TypedExpr [NativeHandlerClause] (Maybe NativeLambdaSign)
  -- |
  Handler ECons Block [HandlerClause] Lambda

instance Show Handler where
  show (Handler eff block clauses mThen) =
    concat [
      "(handler (effect ",
      show eff,
      ") (block ",
      show block,
      ") (clauses ", unwords (map show clauses), ")",
      " (then " <> show mThen <> ")",
      ")"
    ]

instance Pretty Handler where
  pretty (Handler eff block clauses _then) =
    T.concat [
      "under ", pretty eff, " to ", pretty block,
      "handle ",
        if null clauses then "" else T.unwords $ map pretty clauses,
      " | then ", pretty _then
    ]

-- op name, lambda, resume amount, args amount
type HandlerClause = (Text, Lambda, ResumeInfo, Int)

instance Pretty HandlerClause where
  pretty (n, lam, _, _) =
    T.concat [
      "| ", n, "(", lam.lArg, " : ", pretty lam.lArgT,
      ") => ", pretty lam.lBlock
    ]

data TopLevelStat =
  SFunctDef FunctDecl
  | STypeDef Text [Text] {-[String]-} Typ
  | SEffDef EffDef
  | SRowDef RowDef
  | SEnumDef EnumDef
  deriving (Show)

instance Pretty TopLevelStat where
  pretty = \case
    SFunctDef f -> pretty f
    STypeDef n ts t ->
      let ts' = if null ts then "" else T.concat ["[", T.concat ts, "]"] in
      T.concat ["type ", n, ts', " = ", pretty t]
    SEffDef e -> pretty e
    SRowDef r -> pretty r
    SEnumDef e -> pretty e

type Chunk = Module TopLevelStat

-- | A pattern of a @match@ clause, after checking.
--
--   The checker resolves what a name binds and what a @val@ pattern compares
--   against, so the interpreter never has to look anything up: the comparison
--   is already a typed expression, and every name carries the type it binds.
data TPattern = MkTPattern {
    tpSpan :: Span
  , tpNode :: TPatternNode
  } deriving (Show)

data TPatternNode =
    TPInt Integer
  | TPFloat Scientific
  | TPString Text
  | TPBoolean Bool
  | TPNil
  -- | A name binds the component it stands for, at the type it has there.
  | TPName Text Typ
  -- | @val e@a@: the value must equal the one the path holds, by @==@.
  | TPValue TypedExpr
  | TPArray [TPattern] (Maybe TPattern)
  | TPTuple [TPattern]
  | TPCon Text [TPattern]
  | TPAs TPattern Text Typ
  | TPCast TPattern Typ
  | TPWildcard
  | TPStarts TPattern TPattern
  | TPEnds TPattern TPattern
  deriving (Show)

instance Pretty TPattern where
  pretty (MkTPattern _ n) = pretty n

instance Pretty TPatternNode where
  pretty = \case
    TPInt i -> T.pack $ show i
    TPFloat f -> T.pack $ show f
    TPString s -> T.concat ["'", s, "'"]
    TPBoolean b -> if b then "true" else "false"
    TPNil -> "()"
    TPName n _ -> n
    TPValue e -> T.concat ["val ", pretty e]
    TPArray ps t ->
      T.concat ["[", T.unwords (map pretty ps), maybe "" (("; " <>) . pretty) t, "]"]
    TPTuple ps -> T.intercalate ", " $ map pretty ps
    TPCon n ps -> T.unwords $ ("#" <> n) : map pretty ps
    TPAs p n _ -> T.concat [pretty p, " as ", n]
    TPCast p t -> T.concat [pretty p, " : ", pretty t]
    TPWildcard -> "_"
    TPStarts l r -> T.concat [pretty l, " |-> ", pretty r]
    TPEnds l r -> T.concat [pretty l, " <-| ", pretty r]

-- | One clause of a @match@: the patterns it accepts, an optional guard and
--   the block it selects.
data TMatchClause = TMatchClause [TPattern] (Maybe TypedExpr) Block
  deriving (Show)

instance Pretty TMatchClause where
  pretty (TMatchClause ps g b) = T.concat [
      "| ", T.unwords $ map pretty ps,
      maybe "" ((" if " <>) . pretty) g,
      " => ", pretty b
    ]

typeOfTypedExpr :: TypedExpr -> Either Text Typ
typeOfTypedExpr = \case
  TEInt _ -> Right TInt
  TEFloat _ -> Right TFloat
  TEBoolean _ -> Right TBoolean
  TEString _ -> Right TString
  TENil -> Right TNil
  TEXVar _ t -> Right t
  -- The payload of the node is the element type, not the type of the array.
  -- Returning it directly made `[5]` have type `Int`, so no array could be
  -- given the annotation `[Int]`; only the empty array slipped through,
  -- because its element type `Nothing` unifies with anything.
  TEArray t r _ -> Right (TArray t r)
  TEPair r l e -> TPair <$> typeOfTypedExpr l <*> typeOfTypedExpr e <*> pure r
  TEXLambda (TypedIR.Lambda _ _ _ argT retT fxs _) -> Right . TFunct $ Funct argT retT fxs
  TENLambda (NativeLambdaSign _ argT retT fxs) -> Right . TFunct $ Funct argT retT fxs
  TEApply f _ ->
    typeOfTypedExpr f >>= \case
      TFunct (Funct _ ret' _) -> pure ret'
      r -> Left $ "typeOfTypedExpr [TEApply]| Apply of non-function: " <> T.pack (show r)
  TERecord _ props r -> Right $ TRecord [TRecordProp mut name t | TERecordProp mut name t _ <- props] r
  -- TEWith _ _ _ t -> t
  TEHandle _ t -> Right t
  TEParen block -> typeOfTypedBlock block
  TEResume _ t -> Right t
  TELet _ _ body -> typeOfTypedExpr body
  TEPropAccess expr field ->
    typeOfTypedExpr expr >>= \case
      TRecord props _ ->
        case find ((field ==) . tName) props of
          Just (TRecordProp _ _ t) -> Right t
          Nothing -> Left $ "Field " <> field <> " not found"
      r -> Left $ "PropAccess on non-record: " <> T.pack (show r)
  TEIfElse _ thenExpr _ -> typeOfTypedExpr thenExpr
  TEAnnot _ t -> Right t
  -- The checker stores the type of the whole form in the node: every clause
  -- has that type already, and the clauses may be empty of a common subject.
  TEMatch _ t _ -> Right t

typeOfTypedBlock :: TypedIR.Block -> Either Text Typ
typeOfTypedBlock = typeOfTypedExpr . snd