{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module Ast (
  Chunk(..),
  TopLevelStat(..),
  EffectOp(..),
  FunctArg(..),
  Typ(..),
  RecordTyp(..),
  RecordTypProp(..),
  EffRow(..),
  EffRowEntry(..),
  EffCons(..),
  Block(..),
  BindDef(..),
  ConstantQualifier(..),
  BlockStat(..),
  Assign(..),
  PathExp(..),
  LetPattern(..),
  AtomLetPattern(..),
  TypeApps(..),
  EffApps(..),
  EffArg(..),
  TypeArg(..),
  RecordTypeArg(..),
  RecordTypeArgProp(..),
  Exp(..),
  HandlerClause(..),
  Literal(..),
  Atom(..),
  Number(..),
  ArrayLiteral(..),
  ArrayEntry(..),
  LambdaLiteral(..),
  LambdaHead(..),
  LambdaParam(..),
  RecordLiteral(..),
  TypeParams(..),
  EffParams(..),
  Params(..),
  AtomLetPatternRecordProp(..),
  Under(..)
) where
import Data.Text (Text)
import Data.Scientific (Scientific)
import qualified Data.Set as Set
import Utils (Pretty (pretty))
import qualified Data.Text as T
import qualified Data.List as String

newtype Chunk = Chunk [TopLevelStat]

newtype (Ord a, Show a) => Params a = Params [a] deriving (Eq, Show)

newtype TypeParams = TParams (Params Text) deriving (Eq, Show)

instance Semigroup TypeParams where (TParams l) <> (TParams r) = TParams $ l <> r
instance Monoid TypeParams where mempty = TParams mempty

instance Pretty TypeParams where
  pretty (TParams (Params ts)) = T.concat ["[", T.unwords ts, "]"]


newtype EffParams = EParams (Params Text) deriving (Eq, Show)
instance Semigroup EffParams where (EParams l) <> (EParams r) = EParams $ l <> r
instance Monoid EffParams where mempty = EParams mempty

instance Pretty EffParams where
  pretty (EParams (Params ts)) = T.concat ["{", T.unwords ts, "}"]

instance (Ord a, Show a) => Semigroup (Params a) where
  (Params ts1) <> (Params ts2) =
    Params (Set.toList $ Set.union (Set.fromList ts1) (Set.fromList ts2))

instance (Ord a, Show a) => Monoid (Params a) where mempty = Params []

data TopLevelStat =
  TypeDef Text TypeParams EffParams Typ
  | EffectDef Text TypeParams EffParams [EffectOp]
  | RowDef Text TypeParams EffRow
  | FunctDef Text TypeParams EffParams [FunctArg] (Maybe EffRow) Typ Block

data EffectOp = EffectOp Text Typ

data FunctArg = NamedFunctArg Text Typ | NilArg

data Typ =
  TFlat Text
  | TNil
  | TArray Typ
  | TParen Typ
  | TPair Typ Typ
  | TFunct Typ Typ (Maybe EffRow)
  | TRecord RecordTyp
  | TForall TypeParams EffParams Typ
  | TVar Text
  | TGenericAlias Text TypeApps
  deriving (Eq, Show)

instance Pretty Typ where
  pretty = \case
    TFlat t -> t
    TNil -> "()"
    TParen t -> T.concat ["(", pretty t, ")"]
    TArray t -> T.concat ["[", pretty t, "]"]
    TPair l r -> T.concat [pretty l, ", ", pretty r]
    TFunct i o r -> T.concat [pretty i, " -> ", pretty r, pretty o]
    TRecord r -> pretty r
    TForall ts es t -> T.concat ["forall ", pretty ts, pretty es, " ==> ", pretty t]
    TVar v -> T.append "`" v
    TGenericAlias t tas -> T.append t $ pretty tas

newtype RecordTyp = RecordTyp [RecordTypProp] deriving (Eq, Show)
instance Pretty RecordTyp where
  pretty (RecordTyp ps) = T.concat ["#{", T.intercalate "; " $ map pretty ps, "}"]

data RecordTypProp = RecordTypProp ConstantQualifier Text Typ deriving (Eq, Show)
instance Pretty RecordTypProp where
  pretty (RecordTypProp cq n t) = T.concat [pretty cq, " ", n, " : ", pretty t]

data EffRow =
  EREvar Text
  | ERAlias Text
  | ERSugar [EffRowEntry] (Maybe Text)
  deriving (Eq, Show)

instance Pretty EffRow where
  pretty = \case
    EREvar v -> T.append "`" v
    ERAlias a -> a
    ERSugar res t -> T.concat [T.intercalate "; " $ map pretty res, maybe T.empty (T.append "| ") t]

data EffRowEntry = EREEffCons EffCons | EREEffRow EffRow deriving (Eq, Show)

instance Pretty EffRowEntry where
  pretty (EREEffCons ec) = pretty ec
  pretty (EREEffRow er) = T.append "..." $ pretty er

data EffCons = EffCons Text (Maybe TypeParams) deriving (Eq, Show)

instance Pretty EffCons where
  pretty (EffCons n tps) = T.append n $ pretty tps

data Block = Block [BlockStat] Exp deriving (Eq)

instance Pretty Block where
  pretty (Block sts e) = T.intercalate "; " $ map pretty sts ++ [pretty e]

instance Show Block where
  show (Block sts e) =
    concat ["(Block [", String.intercalate "; " (map show sts), "] ", show e, ")"]

data BindDef = BindDef ConstantQualifier LambdaParam Exp deriving (Eq, Show)

instance Pretty BindDef where
  pretty (BindDef cq lp e) =
    T.concat [pretty cq, " ", pretty lp, " = ", pretty e]

data ConstantQualifier = Var | Val | Imm deriving (Eq, Show)

instance Pretty ConstantQualifier where
  pretty = \case
    Var -> "var"
    Val -> "val"
    Imm -> "imm"

data BlockStat =
  BExp Exp
  | BBindDef BindDef
  | BAssign Assign
  deriving (Eq, Show)

instance Pretty BlockStat where
  pretty = \case
    BExp e -> pretty e
    BBindDef b -> pretty b
    BAssign a -> pretty a

data Assign = Assign Text Exp deriving (Eq, Show)

instance Pretty Assign where
  pretty (Assign anchor e) = T.append anchor $ pretty e

data PathExp = PathExp Exp [Text] deriving (Eq, Show)

instance Pretty PathExp where
  pretty (PathExp e ns) =
    T.concat [
      pretty e,
      "@",
      case ns of [n] -> n; _ -> T.concat ["(", T.unwords ns, ")"]
    ]

data LetPattern = LPATom AtomLetPattern | LPParam LambdaParam deriving (Eq, Show)

instance Pretty LetPattern where
  pretty (LPATom a) = pretty a
  pretty (LPParam lp) = pretty lp

data AtomLetPattern =
  ALPNil
  | ALPUnderscore
  | ALPPair LetPattern LetPattern
  | ALPParen LetPattern
  | ALPRecord [AtomLetPatternRecordProp]
  deriving (Eq, Show)

instance Pretty AtomLetPattern where
  pretty = \case
    ALPNil -> "()"
    ALPUnderscore -> "_"
    ALPPair l r -> T.concat [pretty l, ", ", pretty r]
    ALPParen lp -> T.concat ["(", pretty lp, ")"]
    ALPRecord ps -> T.concat ["#{", T.intercalate "; " $ map pretty ps, "}"]

data AtomLetPatternRecordProp =
  AtomLetPatternRecordProp ConstantQualifier LambdaParam AtomLetPattern
  deriving (Eq, Show)

instance Pretty AtomLetPatternRecordProp where
  pretty (AtomLetPatternRecordProp cq lp alp) = T.concat [pretty cq, " ", pretty lp, " ", pretty alp]

newtype TypeApps = TypeApps [TypeArg] deriving (Eq, Show)
instance Pretty TypeApps where
  pretty (TypeApps tas) = T.concat ["[", T.intercalate "; " $ map pretty tas, "]"]

newtype EffApps = EffApps [EffArg] deriving (Eq, Show)
instance Pretty EffApps where
  pretty (EffApps eas) = T.concat ["{", T.intercalate "; " $ map pretty eas, "}"]

data EffArg = EACons EffCons | EARow EffRow deriving (Eq, Show)

instance Pretty EffArg where
  pretty = \case EACons c -> pretty c; EARow r -> T.append "..." $ pretty r

data TypeArg =
  TAFlat Text
  | TANil
  | TAArray TypeArg
  | TAParen TypeArg
  | TAPair TypeArg TypeArg
  | TAFunct TypeArg TypeArg
  | TARecord RecordTypeArg
  | TAMeta Text
  | TAGenericAlias Text TypeApps
  deriving (Eq, Show)

instance Pretty TypeArg where
  pretty = \case
    TAFlat t -> t
    TANil -> "()"
    TAArray t -> T.concat ["[", pretty t, "]"]
    TAParen t -> T.concat ["(", pretty t, ")"]
    TAPair l r -> T.concat [pretty l, ", ", pretty r]
    TAFunct i o -> T.concat [pretty i, " -> ", pretty o]
    TARecord r -> pretty r
    TAMeta v -> T.append "`" v
    TAGenericAlias t tas -> T.append t $ pretty tas

newtype RecordTypeArg = RecordTypeArg [RecordTypeArgProp] deriving (Eq, Show)
instance Pretty RecordTypeArg where
  pretty (RecordTypeArg ps) = T.concat ["#{", T.intercalate "; " $ map pretty ps, "}"]

data RecordTypeArgProp = RecordTypeArgProp ConstantQualifier Text TypeArg deriving (Eq, Show)
instance Pretty RecordTypeArgProp where
  pretty (RecordTypeArgProp cq n t) = T.concat [pretty cq, " ", n, " : ", pretty t]

data Exp =
  EName Text
  | EApply Exp Exp
  | EDollar Exp Exp
  | ELiteral Literal
  | EPair Exp Exp
  | ELet LetPattern Exp Exp
  | EBacktick Text Exp Exp
  | EPropAccess Exp Text
  | EIfThenElse Exp Exp Exp
  | EUnder Under
  | EResume Exp
  | EParen Block
  | EWith Exp TypeApps EffApps
  deriving (Eq, Show)



instance Pretty Exp where
  pretty = \case
    EName n -> n
    EApply c e -> T.concat [pretty c, " ", pretty e]
    EDollar c e -> T.concat [pretty c, " $ ", pretty e]
    ELiteral l -> pretty l
    EPair l r -> T.concat ["(", pretty l, ", ", pretty r, ")"]
    ELet p w e -> T.concat ["let ", pretty p, " = ", pretty w, " in ", pretty e]
    EBacktick op l r -> T.concat [pretty l, "`", op, "`", pretty r]
    EPropAccess e n -> T.concat [pretty e, "@", n]
    EIfThenElse p t f -> T.concat ["if ", pretty p, " then ", pretty t, " else ", pretty f]
    EUnder u -> pretty u
    EResume e -> T.append "resume " $ pretty e
    EParen b -> T.concat ["(", pretty b, ")"]
    EWith e tas eas -> T.concat [pretty e, " with ", pretty tas, pretty eas]

data ExpPrecedence =
  PrecResume
  | PrecDollar
  | PrecBacktick
  | PrecPostfix      -- @, with
  | PrecApply
  | PrecAtom
  deriving (Eq, Ord, Show, Enum, Bounded)

precExp :: Exp -> ExpPrecedence
precExp = \case
  -- атомы
  EPair {}        -> PrecAtom
  ELiteral _      -> PrecAtom
  EName _         -> PrecAtom
  EParen _        -> PrecAtom  -- если есть

  -- apply
  EApply {}       -> PrecApply

  -- постфиксы
  EPropAccess {}  -> PrecPostfix
  EWith {}        -> PrecPostfix

  -- инфиксы
  EBacktick {}    -> PrecBacktick
  EDollar {}      -> PrecDollar

  -- слабый префикс
  EResume _       -> PrecResume

  -- структурные формы считаем самыми слабыми
  EIfThenElse {}  -> PrecResume
  ELet {}         -> PrecResume
  EUnder {}       -> PrecResume

data Under =
  UFull EffCons Block HandlerClause [HandlerClause] (Maybe Block)
  | UThen EffCons Block [HandlerClause] Block
  deriving (Eq, Show)

instance Pretty Under where
  pretty (UFull ec b f hcs t) =
    T.concat [
      "under ",
      pretty ec,
      " to ",
      pretty b,
      " handle ",
      pretty f,
      T.unwords $ map pretty hcs,
      maybe "" (T.append "| then => " . pretty) t
    ]
  pretty (UThen ec b hcs t) =
    T.concat [
      "under ",
      pretty ec,
      " to ",
      pretty b,
      " handle ",
      T.unwords $ map pretty hcs,
      T.append "| then => " $ pretty t
    ]


data HandlerClause = HandlerClause Text [Text] Block deriving (Eq, Show)

instance Pretty HandlerClause where
  pretty (HandlerClause op ns b) =
    T.concat [
      "| ",
      op,
      " ",
      T.unwords ns,
      " => ",
      pretty b
    ]

data Literal =
  LAtom Atom
  | LArray ArrayLiteral
  | LLambda LambdaLiteral
  | LRecord RecordLiteral
  deriving (Eq, Show)

instance Pretty Literal where
  pretty = \case
    LAtom a -> pretty a
    LArray ar -> pretty ar
    LLambda l -> pretty l
    LRecord r -> pretty r

data Atom =
  AString Text
  | ANumber Number
  | ANil
  | ABoolean Bool
  deriving (Eq, Show)

instance Pretty Atom where
  pretty = \case
    AString s -> T.concat ["'", s, "'"]
    ANumber n -> pretty n
    ANil -> "()"
    ABoolean b -> if b then "true" else "false"

data Number = NInt Integer | NFloat Scientific deriving (Eq, Show)

instance Pretty Number where
  pretty = \case
    NInt n -> T.pack $ show n
    NFloat f -> T.pack $ show f

newtype ArrayLiteral = ArrayLiteral [ArrayEntry] deriving (Eq, Show)

instance Pretty ArrayLiteral where
  pretty (ArrayLiteral ar) = T.concat ["[", T.intercalate ", " (map pretty ar), "]"]

data ArrayEntry = AEExp Exp | AEBlock Block deriving (Eq, Show)

instance Pretty ArrayEntry where
  pretty = \case AEExp e -> pretty e; AEBlock b -> pretty b

data LambdaLiteral =
  LambdaLiteral (Maybe TypeParams) (Maybe EffParams) (Maybe LambdaHead) Block
  deriving (Eq, Show)

instance Pretty LambdaLiteral where
  pretty (LambdaLiteral tps eps lh b) =
    T.concat ["{", pretty tps, pretty eps, pretty lh, pretty b, "}"]

data LambdaHead = LambdaHead [LambdaParam] (Maybe Typ) deriving (Eq, Show)

instance Pretty LambdaHead where
  pretty (LambdaHead lps t) =
    T.concat [
      "(",
      T.intercalate "; " $ map pretty lps,
      ")",
      maybe "" (T.append " : " . pretty) t,
      " = "
    ]

data LambdaParam = LambdaParam Text (Maybe Typ) deriving (Eq, Show)

instance Pretty LambdaParam where
  pretty (LambdaParam n t) = T.append n $ maybe "" (T.append " : " . pretty) t

data RecordLiteral = RecordLiteral (Maybe Exp) [BindDef] deriving (Eq, Show)

instance Pretty RecordLiteral where
  pretty (RecordLiteral e bs) =
    T.concat [
      "#{",
      maybe "" ((`T.append` " | ") . pretty) e,
      T.intercalate "; " $ map pretty bs,
      "}"
    ]