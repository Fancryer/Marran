{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Property-based tests for unification and substitution.
--
--   The unit tests in "UnifySpec" pin down individual rules; the properties
--   here state the invariants those rules must add up to — most importantly
--   that a successful unification really makes the two types (or rows) equal
--   under the resulting substitution, that unification is symmetric, that it
--   can be replayed, and that the occurs check rejects exactly the cyclic
--   bindings.
--
--   The generators avoid two constructs on purpose.  'TNothing' and 'TANothing'
--   are the element types of an empty array literal and unify with anything
--   without being rewritten, so they have no place in an equality property.
--   'TForall' is never unified directly: polymorphism is instantiated before
--   unification, and the checker has no rule for a quantified type.
module UnifyPropertySpec (uPropSpec) where

import Control.Monad (replicateM)
import Control.Monad.State.Strict (StateT, evalStateT, get, put, runStateT)
import Control.Monad.Trans.Class (lift)
import Data.List (nub, sort, sortOn)
import qualified Data.Set as Set
import qualified Data.Text as T
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (
    Gen, elements, forAll, oneof, property, sublistOf, (===)
  )

import ErrorContext (ErrorStack)
import Scope (globalScope)
import Types
import Unify
import TypedIR (Scope)

uPropSpec :: Spec
uPropSpec = do

  describe "types" $ do
    prop "a successful unification makes the two types equal" $
      forAll genTypePair $ \(a, b) ->
        case withScopeAndState (\sc -> unifyTypes sc a b) of
          (Left _, _) -> property True
          (Right sc', st) ->
            case evalTypeCheckM
                ((,) <$> applyTypeSubst sc' a <*> applyTypeSubst sc' b) st of
              Left _ -> property False
              Right (a', b') -> canonType a' === canonType b'

    prop "unification succeeds in both directions or in neither" $
      forAll genTypePair $ \(a, b) ->
        let forward = succeeds (withScope (\sc -> unifyTypes sc a b))
            backward = succeeds (withScope (\sc -> unifyTypes sc b a))
        in forward === backward

    prop "a type unifies with itself without being changed" $
      forAll (runGen (genTyp typDepth)) $ \t ->
        case withScopeAndState (\sc -> unifyTypes sc t t) of
          (Left _, _) -> property False
          (Right sc', st) ->
            case evalTypeCheckM (applyTypeSubst sc' t) st of
              Left _ -> property False
              Right t' -> canonType t' === canonType t

    prop "a successful unification can be replayed" $
      forAll genTypePair $ \(a, b) ->
        case withScopeAndState (\sc -> unifyTypes sc a b) of
          (Left _, _) -> property True
          (Right sc', st) ->
            succeeds (evalTypeCheckM (unifyTypes sc' a b) st) === True

    prop "a meta does not unify with a type that contains it" $
      forAll (runGen genOccurring) $ \(v, t) ->
        succeeds (withScope (\sc -> unifyTypes sc (TVar v) t)) === False

    prop "a fresh meta unifies with any type that does not contain it" $
      forAll (runGen ((,) <$> genTyp typDepth <*> freshVar)) $ \(t, v) ->
        succeeds (withScope (\sc -> unifyTypes sc (TVar v) t)) === True

    prop "a sequence of type bindings cannot form a cycle" $
      forAll (runGen ((,) <$> freshVar <*> freshVar)) $ \(v, w) ->
        let outcome = withScope $ \sc -> do
              sc1 <- unifyTypes sc (TVar v) (TArray (TVar w) nilRow)
              unifyTypes sc1 (TVar w) (TArray (TVar v) nilRow)
        in succeeds outcome === False

  describe "effect rows" $ do
    prop "a successful unification makes the two rows equal" $
      forAll genRowPair $ \(r1, r2) ->
        case withScopeAndState (\sc -> unifyEffRows sc r1 r2) of
          (Left _, _) -> property True
          (Right sc', st) ->
            case evalTypeCheckM
                ((,) <$> applyEffRowSubst sc' r1 <*> applyEffRowSubst sc' r2) st of
              Left _ -> property False
              Right (r1', r2') -> canonRow r1' === canonRow r2'

    prop "row unification succeeds in both directions or in neither" $
      forAll genRowPair $ \(r1, r2) ->
        let forward = succeeds (withScope (\sc -> unifyEffRows sc r1 r2))
            backward = succeeds (withScope (\sc -> unifyEffRows sc r2 r1))
        in forward === backward

    prop "a successful row unification can be replayed" $
      forAll genRowPair $ \(r1, r2) ->
        case withScopeAndState (\sc -> unifyEffRows sc r1 r2) of
          (Left _, _) -> property True
          (Right sc', st) ->
            succeeds (evalTypeCheckM (unifyEffRows sc' r1 r2) st) === True

    prop "a closed row is subsumed exactly when its effects are a subset" $
      forAll ((,) <$> sublistOf effectNames <*> sublistOf effectNames) $ \(as, bs) ->
        let outcome = succeeds $
              withScope (\sc -> subsumesEffRow sc
                (RClosed (map eff as))
                (RClosed (map eff bs)))
            expected = Set.fromList as `Set.isSubsetOf` Set.fromList bs
        in outcome === expected

    prop "two open rows with a shared tail are subsumed by growing the tail" $
      forAll genSharedTailRows $ \(r1, r2) ->
        succeeds (withScope (\sc -> subsumesEffRow sc r1 r2)) === True

    prop "two open rows with a shared tail must agree on their explicit effects" $
      forAll genSharedTailRows $ \(r1, r2) ->
        let outcome = succeeds (withScope (\sc -> unifyEffRows sc r1 r2))
            expected = case (r1, r2) of
              (ROpen as _, ROpen bs _) -> Set.fromList as == Set.fromList bs
              _ -> False
        in outcome === expected

    prop "a row variable does not unify with a row that contains it" $
      forAll genOccurringRow $ \(v, cs) ->
        succeeds (withScope $ \sc ->
          unifyEffRows sc (RVar v) (ROpen cs v)) === False

    prop "a sequence of row bindings cannot form a cycle" $
      forAll genIndirectRow $ \(v, w, cs, ds) ->
        let outcome = withScope $ \sc -> do
              sc1 <- unifyEffRows sc (RVar v) (ROpen cs w)
              unifyEffRows sc1 (RVar w) (ROpen ds v)
        in succeeds outcome === False

  describe "effect constructors" $ do
    prop "a successful effect unification makes the arguments equal" $
      forAll genEffectArgs $ \(as, bs) ->
        case withScopeAndState (\sc -> unifyEffCons sc (loop as) (loop bs)) of
          (Left _, _) -> property True
          (Right sc', st) ->
            case evalTypeCheckM
                ((,) <$> applyEffConsSubst sc' (loop as)
                     <*> applyEffConsSubst sc' (loop bs)) st of
              Left _ -> property False
              Right (e1, e2) -> canonEff e1 === canonEff e2

--------------------------------------------------------------------------------
-- Running a check
--------------------------------------------------------------------------------

initialState :: TypeCheckState
initialState = TypeCheckState (100, 100, 100) 0 []

-- | Run an action against the initial scope.
withScope :: (Scope -> TypeCheckM a) -> Either (ErrorStack, TypeCheckError) a
withScope action = fst (withScopeAndState action)

-- | 'withScope', but the final state is kept: a property that replays a
--   unification must continue from the counter the first run stopped at, or a
--   fresh variable could collide with one the first run created.
withScopeAndState
  :: (Scope -> TypeCheckM a)
  -> (Either (ErrorStack, TypeCheckError) a, TypeCheckState)
withScopeAndState action =
  runTypeCheckM (globalScope [] >>= action) initialState

succeeds :: Either e a -> Bool
succeeds = either (const False) (const True)

-- | The empty pending row, @{}@.  An aggregate writes it when the property
--   under test is not about its row.
nilRow :: EffRow
nilRow = RClosed []

--------------------------------------------------------------------------------
-- Canonical forms
--------------------------------------------------------------------------------

-- | Rows are compared up to the order and repetition of their explicit
--   effects, and an open row with no explicit effects is the same thing as its
--   tail: @{| `r}@ and @`r@ are two spellings of one row.
canonRow :: EffRow -> EffRow
canonRow = \case
  RClosed cs -> RClosed (sort (nub cs))
  ROpen cs v
    | null cs -> RVar v
    | otherwise -> ROpen (sort (nub cs)) v
  RVar v -> RVar v

-- | Types are compared in the same spirit.  Unification sorts records by field
--   name and rows by effect name, but the types themselves keep the order they
--   were written in, so the comparison must ignore it.
canonType :: Typ -> Typ
canonType = \case
  TArray t r -> TArray (canonType t) (canonRow r)
  TPair l r fx -> TPair (canonType l) (canonType r) (canonRow fx)
  TFunct (Funct i o r) -> TFunct (Funct (canonType i) (canonType o) (canonRow r))
  TRecord props r ->
    TRecord (sortOn tName [p {tTyp = canonType (tTyp p)} | p <- props]) (canonRow r)
  t -> t

canonArg :: TypeArg -> TypeArg
canonArg = \case
  TAArray t -> TAArray (canonArg t)
  TAPair l r -> TAPair (canonArg l) (canonArg r)
  TAFunct i o -> TAFunct (canonArg i) (canonArg o)
  TARecord props ->
    TARecord (sortOn taRecordName
      [TARecordProp m n (canonArg t) | TARecordProp m n t <- props])
  t -> t

taRecordName :: TARecordProp -> T.Text
taRecordName (TARecordProp _ n _) = n

canonEff :: EffCons -> EffCons
canonEff = \case
  EffCons (ECons n args) -> EffCons (ECons n (map canonArg args))
  e -> e

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

-- | A generator with a supply of variable identifiers.  'Taste' equality is by
--   identifier, so every variable the generator introduces gets a fresh one;
--   sharing a variable between two positions has to be explicit.
type GenM = StateT Int Gen

runGen :: GenM a -> Gen a
runGen = flip evalStateT 0

-- | 'oneof' for actions that also thread the variable supply.  QuickCheck's
--   'oneof' only chooses between 'Gen' values, so each branch is run from the
--   current state here and the state of the chosen branch is kept.
oneofM :: [GenM a] -> GenM a
oneofM choices = do
  s <- get
  (a, s') <- lift $ oneof [runStateT c s | c <- choices]
  put s'
  pure a

freshVar :: GenM Taste
freshVar = do
  n <- get
  put (n + 1)
  pure $ Meta ("m" <> T.pack (show n)) n 0

typDepth :: Int
typDepth = 3

genTyp :: Int -> GenM Typ
genTyp depth
  | depth <= 0 = genGround
  | otherwise = oneofM
      [ genGround
      , TVar <$> freshVar
      , TArray <$> genTyp (depth - 1) <*> genRow depth
      , TPair <$> genTyp (depth - 1) <*> genTyp (depth - 1) <*> genRow depth
      , do
          i <- genTyp (depth - 1)
          o <- genTyp (depth - 1)
          r <- genRow depth
          pure $ TFunct (Funct i o r)
      , genRecord (depth - 1)
      ]

genGround :: GenM Typ
genGround = lift $ elements
  [TInt, TFloat, TBoolean, TString, TNil, TFlat "Price", TFlat "Food"]

genRecord :: Int -> GenM Typ
genRecord depth = do
  names <- lift $ sublistOf ["x", "y", "z"]
  props <- traverse
    (\n -> TRecordProp
      <$> lift (elements [Val, Var, Imm])
      <*> pure (T.pack n)
      <*> genTyp depth)
    names
  row <- genRow depth
  pure $ TRecord props row

genRow :: Int -> GenM EffRow
genRow depth
  | depth <= 0 = oneofM
      [ RClosed <$> genEffects
      , RVar <$> freshVar
      ]
  | otherwise = oneofM
      [ RClosed <$> genEffects
      , ROpen <$> genEffects <*> freshVar
      , RVar <$> freshVar
      ]

-- | A subset of a fixed set of effect names.  Names never repeat, so the
--   subset relation is a plain set relation and a match by name is unambiguous.
effectNames :: [T.Text]
effectNames = ["Input", "Output", "Random", "Time", "System"]

eff :: T.Text -> EffCons
eff n = EffCons (ECons n [])

genEffects :: GenM [EffCons]
genEffects = map eff <$> lift (sublistOf effectNames)

genTypePair :: Gen (Typ, Typ)
genTypePair = runGen ((,) <$> genTyp typDepth <*> genTyp typDepth)

genRowPair :: Gen (EffRow, EffRow)
genRowPair = runGen ((,) <$> genRow 2 <*> genRow 2)

genSharedTailRows :: Gen (EffRow, EffRow)
genSharedTailRows = runGen $ do
  v <- freshVar
  as <- genEffects
  bs <- genEffects
  pure (ROpen as v, ROpen bs v)

genOccurringRow :: Gen (Taste, [EffCons])
genOccurringRow = runGen $ do
  v <- freshVar
  cs <- genEffects
  pure (v, cs)

genIndirectRow :: Gen (Taste, Taste, [EffCons], [EffCons])
genIndirectRow = runGen $ do
  v <- freshVar
  w <- freshVar
  cs <- genEffects
  ds <- genEffects
  pure (v, w, cs, ds)

-- | A variable and a type that contains it under at least one constructor.
--   The outermost constructor is never a variable, so this is never the
--   harmless @`a ~ `a@ case.
genOccurring :: GenM (Taste, Typ)
genOccurring = do
  v <- freshVar
  t <- TArray <$> genWithVar v 2 <*> pure nilRow
  pure (v, t)

genWithVar :: Taste -> Int -> GenM Typ
genWithVar v depth
  | depth <= 0 = pure (TVar v)
  | otherwise = oneofM
      [ pure (TVar v)
      , do
          t <- genWithVar v (depth - 1)
          r <- genRow (depth - 1)
          pure $ TArray t r
      , do
          l <- genWithVar v (depth - 1)
          r <- genTyp (depth - 1)
          fx <- genRow (depth - 1)
          pure $ TPair l r fx
      , do
          l <- genTyp (depth - 1)
          r <- genWithVar v (depth - 1)
          fx <- genRow (depth - 1)
          pure $ TPair l r fx
      , do
          i <- genTyp (depth - 1)
          r <- genRow (depth - 1)
          pure $ TFunct (Funct i (TVar v) r)
      , do
          t <- genWithVar v (depth - 1)
          r <- genRow (depth - 1)
          pure $ TRecord [TRecordProp Val "x" t] r
      ]

genTypeArg :: Int -> GenM TypeArg
genTypeArg depth
  | depth <= 0 = lift $ elements
      [TAInt, TAFloat, TABoolean, TAString, TANil, TAFlat "Price"]
  | otherwise = oneofM
      [ lift $ elements
          [TAInt, TAFloat, TABoolean, TAString, TANil, TAFlat "Price"]
      , TAVar <$> freshVar
      , TAArray <$> genTypeArg (depth - 1)
      , TAPair <$> genTypeArg (depth - 1) <*> genTypeArg (depth - 1)
      ]

genEffectArgs :: Gen ([TypeArg], [TypeArg])
genEffectArgs = runGen ((,) <$> genArgList <*> genArgList)

genArgList :: GenM [TypeArg]
genArgList = do
  n <- lift $ elements [0 .. 3 :: Int]
  replicateM n (genTypeArg 1)

loop :: [TypeArg] -> EffCons
loop args = EffCons (ECons "Loop" args)
