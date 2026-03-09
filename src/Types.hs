{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OrPatterns #-}

module Types (
  Taste(..),
  Typ(..),
  Func,
  EffRow(..),
  EffCons,
  TypConstraint(..),
  EffDecl(..),
  Expr(..),
  Scope(..),
  Block,
  NativeBlock,
  Stat(..),
  Lambda(..),
  NativeLambda(..),
  TopLevelStat(..),
  FunctDecl(..),
  Handler(..),
  HandlerSig(..),
  Chunk,
  Mutability(..),
  NativeLambdaSign(NativeLambdaSign),
  TRecordProp(..),
  ERecordProp(..),
  Scheme(..),
  TypeScheme,
  EffScheme,
  tasteName,
  isSkolem,
  tfunc,
  pureTFunc,
  handlerCons
) where
import Data.Map (Map)
import Data.List (intercalate)
import Text.Printf (printf)

data Taste =
  Meta String Int
  | Skolem String
  | Bound String
  deriving (Show, Ord, Eq)

data Typ =
  TInt
  | TFloat
  | TBoolean
  | TString
  | TNil
  | TNothing
  | TFlat String
  | TList Typ
  | TPair Typ Typ
  | TFunc Func                  -- arg -> row ret
  | TRecord [TRecordProp]
  | TForall [Taste] [Taste] Typ -- forall [a1, ..., an] {e1, ..., en} ==> type
  | TVar Taste
  deriving (Show, Ord, Eq)

type Func = (Typ, Typ, EffRow)

data Scheme a = Scheme [Taste] [Taste] a
type TypeScheme = Scheme Typ
type EffScheme = Scheme EffRow

data TRecordProp = TRecordProp Mutability String Typ deriving (Show, Eq, Ord)

data EffRow =
  EClosed [EffCons]       -- Закрытый ряд: {Console; File}
  | EOpen [EffCons] Taste -- Открытый ряд: {console; file | `e}
  | EVar Taste            -- Переменная ряда: `e
  deriving (Show, Ord, Eq)

type EffCons = (String, [Typ])

data TypConstraint =
  CInt
  | CFloat
  | CBoolean
  | CString
  | CNil
  | CNothing
  | CFlat String
  | CList TypConstraint
  | CPair TypConstraint TypConstraint
  | CFunc TypConstraint TypConstraint  -- arg -> ret, NO effects
  | CVar Taste

data EffDecl =
  -- name params ops
  EffDecl String [TypConstraint] [(String, Func)]
  | EffAlias String EffRow

data Expr =
  Int Int
  | Float Float
  | Boolean Bool
  | String String
  | Nil
  | XVar String
  | List [Expr]
  | Pair Expr Expr
  | XLambda Lambda
  | NLambda NativeLambda
  | Apply Expr Expr
  | Record [ERecordProp]
  | With Expr [Typ] [EffRow] -- expr with [ts] {fxs}
  | Handle Handler
  | Resume Expr
  deriving (Eq, Ord)

{-

-}

data ERecordProp = ERecordProp Mutability String Typ Expr deriving (Show, Eq, Ord)

instance Show Expr where
  show = \case
    Int i -> show i
    Float f -> show f
    Boolean b -> show b
    String s -> s
    Nil -> "()"
    XVar v -> v
    List es -> "[" ++ intercalate ", " (map show es) ++ "]"
    Pair l r -> printf "(%s, %s)" (show l) (show r)
    XLambda lam -> show lam
    _ -> "#TODO#"

data NativeLambda = NativeLambda NativeLambdaSign (Expr -> IO Expr)

instance Eq NativeLambda where
  (NativeLambda sign1 _) == (NativeLambda sign2 _) = sign1 == sign2

instance Ord NativeLambda where
  (NativeLambda sign1 _) `compare` (NativeLambda sign2 _) = sign1 `compare` sign2
-- arg argT retT fxs
data NativeLambdaSign = NativeLambdaSign String (Maybe Typ) (Maybe Typ) EffRow deriving (Eq, Ord)

data Lambda = Lambda {
  arg   ::  String,
  argT ::  Maybe Typ,
  retT ::  Maybe Typ,
  fxs   ::  EffRow,
  block ::  Block
} deriving (Eq, Ord)

instance Show Lambda where
  show (Lambda arg argT retT fxs block) =
    "{"
    ++ arg
    ++ maybe "" (\t -> " " ++ show t) argT
    ++ show fxs
    ++ maybe "" (\t -> " " ++ show t) retT
    ++ "= "
    ++ show block
    ++ "}"

type NativeBlock  = (Typ, Expr)
type Block        = ([Stat], Expr)

data Stat =
  Bind Mutability String (Maybe Typ) Expr
  | Assign String Expr
  | Expr Expr
  deriving (Eq, Ord)

instance Show Stat where
  show = \case
    Bind mut name typ expr ->
      show mut ++ " " ++ name ++ maybe "" (\t -> " " ++ show t) typ ++ " = " ++ show expr
    Assign name expr ->
      name ++ " := " ++ show expr
    Expr expr -> show expr

data TopLevelStat =
  SFunctDecl FunctDecl
  | STypeDecl String Typ
  | SEffDecl EffDecl

data FunctDecl = FunctDecl {
  fname  :: String,
  tvars  :: [String],
  evars  :: [String],
  args   :: [(String, Maybe Typ)],
  ret    :: (Maybe EffRow, Typ),
  fBlock :: Block
}

--eff block clauses then
data Handler =
  NativeHandler EffCons NativeBlock [NativeHandlerClause] (Maybe NativeLambda)
  | Handler     EffCons Block       [HandlerClause]       (Maybe Lambda)
  deriving (Eq, Ord)

type NativeHandlerClause  = (String, NativeLambda)
type HandlerClause        = (String, Lambda)

-- eff clauses
data HandlerSig = HandlerSig EffCons [(String, Func)]

type Chunk = [TopLevelStat]

data Mutability = Val | Var | Imm deriving (Eq, Ord)

instance Show Mutability where show = \case Val -> "val"; Var -> "var"; Imm -> "imm"

type StringMap  = Map String
type TypeScope  = StringMap Typ
type ValueScope = StringMap (TypeScheme, Expr, Mutability)
type EffScope   = StringMap EffDecl

type TypeSubst  = Map Taste Typ
type EffSubst   = Map Taste EffRow

data Scope = Scope {
  types       :: TypeScope,
  values      :: ValueScope,
  effects     :: EffScope,

  handlerSig  :: Maybe HandlerSig,

  typeSubst   :: TypeSubst,
  effSubst    :: EffSubst,

  parent      :: Maybe Scope
}

tfunc :: Typ -> Typ -> Typ
tfunc i o = TFunc (i, o, EClosed [])

pureTFunc :: [Typ] -> Maybe Typ
pureTFunc = \case
  [] -> Nothing
  [i, o] -> Just $ tfunc i o
  (i : o) -> tfunc i <$> pureTFunc o

tasteName :: Taste -> String
tasteName = \case
  Skolem s -> s
  Meta s _ -> s
  Bound s -> s

isSkolem :: Taste -> Bool
isSkolem (Skolem _) = True
isSkolem _ = False

{-
data Handler =
  NativeHandler EffCons NativeBlock [NativeHandlerClause] (Maybe NativeLambda)
  | Handler     EffCons Block       [HandlerClause]       (Maybe Lambda)
-}
handlerCons :: Handler -> EffCons
handlerCons (NativeHandler cons _ _ _) = cons
handlerCons (Handler cons _ _ _) = cons