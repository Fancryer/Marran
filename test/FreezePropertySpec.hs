{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Property-based tests for freezing.
--
--   Freezing is the operation that turns a value into an immutable snapshot.
--   The unit tests in "FreezeSpec" pin down individual cases; the properties
--   here state what must hold for every type and expression:
--
--     * a frozen type has no mutation effect left in any row, and every row
--       tail or effect variable that survives is constrained to stay free of
--       mutation effects;
--     * a frozen type has no @var@ record field;
--     * freezing removes exactly the mutation effects and nothing else;
--     * freezing twice is the same as freezing once;
--     * a tail that is already bound to a mutation effect is rejected, not
--       silently accepted;
--     * two rows that share a tail keep sharing it, and the one constraint is
--       enough for both;
--     * the constraints on a forall's quantified variables end up in the
--       forall's own constraint maps, while constraints on free variables
--       stay in the surrounding scope.
--
--   Expression freezing is checked separately: it must remove every @var@
--   binding, every rebind and every @var@ record field, and it must be
--   idempotent.
module FreezePropertySpec (fPropSpec) where

import Control.Monad (replicateM)
import Control.Monad.State.Strict (StateT, evalStateT, get, put, runStateT)
import Control.Monad.Trans.Class (lift)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (
    Gen, conjoin, counterexample, elements, forAll, listOf, oneof, property,
    sublistOf, (===), (.&&.)
  )

import ErrorContext (ErrorStack)
import qualified Infer
import Scope (globalScope)
import Types (
    AtomLetPattern (..),
    ECons (..),
    EffCons (..),
    EffRow (..),
    Funct (..),
    LetPattern (..),
    Mutability (..),
    Taste (..),
    TRecordProp (..),
    Typ (..)
  )
import TypedIR
import Unify

fPropSpec :: Spec
fPropSpec = do

  describe "freezeTyp" $ do
    prop "leaves no mutation effect and constrains every surviving variable" $
      forAll (runGen (genTyp 3)) $ \t ->
        case freezeType t of
          Left err ->
            counterexample ("freezing failed: " <> show err) (property False)
          Right (scope', frozen) ->
            case resolve scope' frozen of
              Left err ->
                counterexample ("substitution failed: " <> show err) (property False)
              Right frozen' -> conjoin
                [ counterexample "mutation effect left in a row"
                    (null (badRows frozen') === True)
                , counterexample "unconstrained row tail"
                    (null (badRowTails scope' frozen') === True)
                , counterexample "unconstrained effect variable"
                    (null (badEffVars scope' frozen') === True)
                , counterexample "var record field left"
                    (null (varFields frozen') === True)
                ]

    prop "only removes mutation effects and changes var fields" $
      forAll (runGen (genTyp 3)) $ \t ->
        case freezeType t of
          Left err ->
            counterexample ("freezing failed: " <> show err) (property False)
          Right (scope', frozen) ->
            case resolve scope' frozen of
              Left err ->
                counterexample ("substitution failed: " <> show err) (property False)
              Right frozen' -> conjoin
                [ counterexample "rows changed beyond mutation removal"
                    (map stripRow (rowsOf t)
                      === map stripRow (rowsOf frozen'))
                , counterexample "record fields changed beyond var to val"
                    (fieldShape t === fieldShape frozen')
                ]

    prop "is idempotent" $
      forAll (runGen (genTyp 3)) $ \t ->
        case freezeTypeWithState t of
          (Left err, _) ->
            counterexample ("freezing failed: " <> show err) (property False)
          (Right (scope1, frozen1), st1) ->
            case evalTypeCheckM (Infer.freezeTyp scope1 frozen1) st1 of
              Left err ->
                counterexample ("second freezing failed: " <> show err) (property False)
              Right (scope2, frozen2) -> conjoin
                [ counterexample "type changed" (frozen2 === frozen1)
                , counterexample "row constraints changed"
                    (rowLacks scope2 === rowLacks scope1)
                , counterexample "effect constraints changed"
                    (effLacks scope2 === effLacks scope1)
                ]

    prop "rejects a row tail already bound to a mutation effect" $
      forAll genHiddenMutation $ \(v, cs) ->
        let scope = (emptyScope) { rowSubst = Map.singleton v (RClosed cs) }
        in counterexample ("accepted: " <> show cs)
             (succeeds (evalTypeCheckM (Infer.freezeRowMutIn scope (RVar v)) initialState)
                === False)

    prop "rejects an effect variable already bound to a mutation effect" $
      forAll ((,) <$> runGen freshVar <*> elements mutationNames) $ \(e, m) ->
        let scope = (emptyScope) { effSubst = Map.singleton e (eff m) }
        in counterexample ("accepted: " <> show m)
             (succeeds
                (evalTypeCheckM
                  (Infer.freezeRowMutIn scope (RClosed [EVar e]))
                  initialState)
                === False)

    prop "keeps a shared tail shared and constrains it once" $
      forAll genSharedTail $ \(v, as, bs) ->
        let t = TArray
              (TPair
                (TFunct (Funct TInt TInt (ROpen as v)))
                (TFunct (Funct TInt TInt (ROpen bs v)))
                (RClosed []))
              (RClosed [])
        in case freezeType t of
          Left err ->
            counterexample ("freezing failed: " <> show err) (property False)
          Right (scope', frozen) ->
            case resolve scope' frozen of
              Left err ->
                counterexample ("substitution failed: " <> show err) (property False)
              Right frozen' -> conjoin
                [ counterexample "tail was duplicated or replaced"
                    (rowsOf frozen' ===
                      [ ROpen (filter (not . isMutation) as) v
                      , ROpen (filter (not . isMutation) bs) v
                      , RClosed []
                      , RClosed []
                      ])
                , counterexample "shared tail is not constrained"
                    (constrainedRow scope' v === True)
                ]

    prop "a frozen constraint survives aliasing the row afterwards" $
      forAll (elements mutationNames) $ \m ->
        let outcome = runWithScope $ \scope -> do
              r1 <- freshMetaM
              r2 <- freshMetaM
              (scope1, _) <- Infer.freezeRowMutIn scope (RVar r1)
              scope2 <- unifyEffRows scope1 (RVar r1) (RVar r2)
              unifyEffRows scope2 (RVar r2) (RClosed [eff m])
        in counterexample ("accepted " <> show m)
             (succeeds outcome === False)

    prop "a frozen constraint survives an alias made before freezing" $
      forAll (elements mutationNames) $ \m ->
        let outcome = runWithScope $ \scope -> do
              r1 <- freshMetaM
              r2 <- freshMetaM
              scope1 <- unifyEffRows scope (RVar r1) (RVar r2)
              (scope2, _) <- Infer.freezeRowMutIn scope1 (RVar r1)
              unifyEffRows scope2 (RVar r2) (RClosed [eff m])
        in counterexample ("accepted " <> show m)
             (succeeds outcome === False)

    prop "freezes a forall's quantified variables into the forall" $
      forAll genForallType $ \(e, r, els0, rls0, body) ->
        let t = TForall [] [e] [r] (Map.singleton e els0)
                  (Map.singleton r rls0) body
        in case freezeTypeWithState t of
          (Left err, _) ->
            counterexample ("freezing failed: " <> show err) (property False)
          (Right (scope', frozen), _) ->
            case frozen of
              TForall _ _ _ els rls body' -> conjoin
                [ counterexample "quantified effect is not constrained"
                    (Map.lookup e els
                      === Just (Set.union els0 mutationEffects))
                , counterexample "quantified row is not constrained"
                    (Map.lookup r rls
                      === Just (Set.union rls0 mutationEffects))
                , counterexample "bound constraint leaked into the scope"
                    (Map.lookup e (effLacks scope') === Nothing
                      .&&. Map.lookup r (rowLacks scope') === Nothing)
                , counterexample "mutation effect left in the body"
                    (null (badRows body') === True)
                ]
              other ->
                counterexample ("not a forall: " <> show other) (property False)

    prop "keeps constraints on variables free in a forall body" $
      forAll genForallWithFreeTail $ \(e, rq, freeRow, freeEff, body) ->
        let t = TForall [] [e] [rq] Map.empty Map.empty body
        in case freezeTypeWithState t of
          (Left err, _) ->
            counterexample ("freezing failed: " <> show err) (property False)
          (Right (scope', frozen), _) ->
            case frozen of
              TForall _ _ _ els rls body' -> conjoin
                [ counterexample "quantified effect is not constrained"
                    (Map.lookup e els === Just mutationEffects)
                , counterexample "quantified row is not constrained"
                    (Map.lookup rq rls === Just mutationEffects)
                , counterexample "free effect variable is not constrained"
                    (constrainedEff scope' freeEff === True)
                , counterexample "free row tail is not constrained"
                    (constrainedRow scope' freeRow === True)
                , counterexample "mutation effect left in the body"
                    (null (badRows body') === True)
                ]
              other ->
                counterexample ("not a forall: " <> show other) (property False)

  describe "freeze (expressions)" $ do
    prop "removes var bindings, rebinds and var record fields" $
      forAll (genExpr 3) $ \e ->
        let frozen = Infer.freeze e
        in counterexample (show frozen)
             (hasVarOrRebind frozen === False)

    prop "is idempotent" $
      forAll (genExpr 3) $ \e ->
        let once = Infer.freeze e
            twice = Infer.freeze once
        in counterexample (show twice) (show twice === show once)

--------------------------------------------------------------------------------
-- Running the checker
--------------------------------------------------------------------------------

initialState :: TypeCheckState
initialState = TypeCheckState (100, 100, 100) 0 []

emptyScope :: Scope
emptyScope = Scope
  { types = Map.empty
  , values = Map.empty
  , effects = Map.empty
  , enums = Map.empty
  , handlerSig = Nothing
  , typeSubst = Map.empty
  , typeArgSubst = Map.empty
  , effSubst = Map.empty
  , rowSubst = Map.empty
  , effLacks = Map.empty
  , rowLacks = Map.empty
  , parent = Nothing
  }

runWithScope :: (Scope -> TypeCheckM a) -> Either (ErrorStack, TypeCheckError) a
runWithScope action = fst (freezeWithState action)

freezeWithState
  :: (Scope -> TypeCheckM a)
  -> (Either (ErrorStack, TypeCheckError) a, TypeCheckState)
freezeWithState action =
  runTypeCheckM (globalScope [] >>= action) initialState

succeeds :: Either e a -> Bool
succeeds = either (const False) (const True)

-- | Freeze a type the way the checker does: resolve the current substitution
--   first, because a type variable may already stand for a function type with
--   latent effects.
freezeType :: Typ -> Either (ErrorStack, TypeCheckError) (Scope, Typ)
freezeType t = runWithScope $ \scope -> do
  t' <- applyTypeSubst scope t
  Infer.freezeTyp scope t'

freezeTypeWithState
  :: Typ
  -> (Either (ErrorStack, TypeCheckError) (Scope, Typ), TypeCheckState)
freezeTypeWithState t = freezeWithState $ \scope -> do
  t' <- applyTypeSubst scope t
  Infer.freezeTyp scope t'

resolve :: Scope -> Typ -> Either (ErrorStack, TypeCheckError) Typ
resolve scope t = evalTypeCheckM (applyTypeSubst scope t) initialState

--------------------------------------------------------------------------------
-- Reading a frozen type
--------------------------------------------------------------------------------

rowsOf :: Typ -> [EffRow]
rowsOf = \case
  TArray t r -> rowsOf t <> [r]
  TPair l r fx -> rowsOf l <> rowsOf r <> [fx]
  TFunct (Funct i o row) -> rowsOf i <> rowsOf o <> [row]
  TRecord props r -> concatMap (rowsOf . tTyp) props <> [r]
  TForall _ _ _ _ _ body -> rowsOf body
  _ -> []

varFields :: Typ -> [TRecordProp]
varFields = \case
  TArray t _ -> varFields t
  TPair l r _ -> varFields l <> varFields r
  TFunct (Funct i o _) -> varFields i <> varFields o
  TRecord props _ ->
    [p | p <- props, tMut p == Var]
      <> concatMap (varFields . tTyp) props
  TForall _ _ _ _ _ body -> varFields body
  _ -> []

-- | The names and (already frozen) mutabilities of every record field, in the
--   order they appear.  Freezing may change a field's type, but it must not
--   drop, rename or reorder the field, and it must not touch @val@ and @imm@.
fieldShape :: Typ -> [(T.Text, Mutability)]
fieldShape = \case
  TArray t _ -> fieldShape t
  TPair l r _ -> fieldShape l <> fieldShape r
  TFunct (Funct i o _) -> fieldShape i <> fieldShape o
  TRecord props _ ->
    [(tName p, freezeMutability (tMut p)) | p <- props]
      <> concatMap (fieldShape . tTyp) props
  TForall _ _ _ _ _ body -> fieldShape body
  _ -> []

-- | Kept here rather than imported: it is a one-line semantic decision, and
--   the test should fail if the checker changes it.
freezeMutability :: Mutability -> Mutability
freezeMutability = \case
  Var -> Val
  m -> m

explicit :: EffRow -> [EffCons]
explicit = \case
  RClosed cs -> cs
  ROpen cs _ -> cs
  RVar _ -> []

rowTailVar :: EffRow -> Maybe Taste
rowTailVar = \case
  RClosed _ -> Nothing
  ROpen _ v -> Just v
  RVar v -> Just v

badRows :: Typ -> [EffRow]
badRows t = [r | r <- rowsOf t, any isMutation (explicit r)]

badRowTails :: Scope -> Typ -> [Taste]
badRowTails scope t =
  [v | r <- rowsOf t, Just v <- [rowTailVar r], not (constrainedRow scope v)]

badEffVars :: Scope -> Typ -> [Taste]
badEffVars scope t =
  [e | r <- rowsOf t, EVar e <- explicit r, not (constrainedEff scope e)]

constrainedRow :: Scope -> Taste -> Bool
constrainedRow scope v =
  mutationEffects `Set.isSubsetOf`
    Map.findWithDefault Set.empty v (rowLacks scope)

constrainedEff :: Scope -> Taste -> Bool
constrainedEff scope v =
  mutationEffects `Set.isSubsetOf`
    Map.findWithDefault Set.empty v (effLacks scope)

-- | What a row looks like once the mutation effects are gone.  Freezing may
--   change mutability and constraints, but it must not reorder or rename the
--   ordinary effects, and it must not replace a tail.
stripRow :: EffRow -> EffRow
stripRow = \case
  RClosed cs -> RClosed (filter (not . isMutation) cs)
  ROpen cs v -> ROpen (filter (not . isMutation) cs) v
  RVar v -> RVar v

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

-- | The invariants of a frozen expression, checked by walking it.
hasVarOrRebind :: TypedExpr -> Bool
hasVarOrRebind = \case
  TEArray _ _ es -> any hasVarOrRebind es
  TEPair _ l r -> hasVarOrRebind l || hasVarOrRebind r
  TEXLambda lam -> blockHasVar (lBlock lam)
  TEApply f x -> hasVarOrRebind f || hasVarOrRebind x
  TERecord anchor props _ ->
    maybe False hasVarOrRebind anchor || any propHasVar props
  TEHandle handler _ ->
    blockHasVar (handlerBlock handler)
      || any clauseHasVar (handlerClauses handler)
      || blockHasVar (lBlock (handlerThen handler))
  TEParen block -> blockHasVar block
  TEResume e _ -> hasVarOrRebind e
  TELet _ bound body -> hasVarOrRebind bound || hasVarOrRebind body
  TEPropAccess e _ -> hasVarOrRebind e
  TEIfElse p t f -> any hasVarOrRebind [p, t, f]
  TEAnnot e _ -> hasVarOrRebind e
  TEWith e _ _ -> hasVarOrRebind e
  _ -> False

propHasVar :: TERecordProp -> Bool
propHasVar p = terMut p == Var || hasVarOrRebind (terExpr p)

blockHasVar :: Block -> Bool
blockHasVar (stats, result) = any statHasVar stats || hasVarOrRebind result

statHasVar :: Stat -> Bool
statHasVar = \case
  Bind m _ e -> m == Var || hasVarOrRebind e
  Rebind _ _ _ -> True
  Expr e -> hasVarOrRebind e

-- The accessors below avoid depending on the positional constructor of
-- 'Handler': its shape is an implementation detail, the frozen expression is
-- not.
handlerBlock :: Handler -> Block
handlerBlock = \case
  Handler _ block _ _ -> block

handlerClauses :: Handler -> [HandlerClause]
handlerClauses = \case
  Handler _ _ clauses _ -> clauses

handlerThen :: Handler -> Lambda
handlerThen = \case
  Handler _ _ _ lam -> lam

clauseHasVar :: HandlerClause -> Bool
clauseHasVar (_, lam, _, _) = blockHasVar (lBlock lam)

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

type GenM = StateT Int Gen

runGen :: GenM a -> Gen a
runGen = flip evalStateT 0

freshVar :: GenM Taste
freshVar = do
  n <- get
  put (n + 1)
  pure $ Meta ("m" <> T.pack (show n)) n 0

oneofM :: [GenM a] -> GenM a
oneofM choices = do
  s <- get
  (a, s') <- lift $ oneof [runStateT c s | c <- choices]
  put s'
  pure a

mutationNames :: [T.Text]
mutationNames = ["Var", "Read", "Rebind", "Cell"]

ordinaryNames :: [T.Text]
ordinaryNames = ["IO", "Output", "Random", "Time", "System"]

mutationEffects :: Set.Set T.Text
mutationEffects = Set.fromList mutationNames

eff :: T.Text -> EffCons
eff n = EffCons (ECons n [])

isMutation :: EffCons -> Bool
isMutation = \case
  EffCons (ECons n _) -> n `Set.member` mutationEffects
  EVar _ -> False

allNames :: [T.Text]
allNames = mutationNames <> ordinaryNames

genEffect :: GenM EffCons
genEffect = oneofM
  [ eff <$> lift (elements allNames)
  , EVar <$> freshVar
  ]

genEffects :: GenM [EffCons]
genEffects = do
  n <- lift (elements [0 .. 4 :: Int])
  replicateM n genEffect

genTyp :: Int -> GenM Typ
genTyp depth
  | depth <= 0 = genGround
  | otherwise = oneofM
      [ genGround
      , TVar <$> freshVar
      , TArray <$> genTyp (depth - 1) <*> genRow
      , TPair <$> genTyp (depth - 1) <*> genTyp (depth - 1) <*> genRow
      , do
          i <- genTyp (depth - 1)
          o <- genTyp (depth - 1)
          row <- genRow
          pure $ TFunct (Funct i o row)
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
  row <- genRow
  pure $ TRecord props row

genRow :: GenM EffRow
genRow = oneofM
  [ RClosed <$> genEffects
  , ROpen <$> genEffects <*> freshVar
  , RVar <$> freshVar
  ]

genHiddenMutation :: Gen (Taste, [EffCons])
genHiddenMutation = runGen $ do
  v <- freshVar
  ordinary <- genEffects
  m <- lift $ elements mutationNames
  pure (v, eff m : ordinary)

genSharedTail :: Gen (Taste, [EffCons], [EffCons])
genSharedTail = runGen $ do
  v <- freshVar
  as <- genEffects
  bs <- genEffects
  pure (v, as, bs)

genForallType
  :: Gen (Taste, Taste, Set.Set T.Text, Set.Set T.Text, Typ)
genForallType = runGen $ do
  e <- freshVar
  r <- freshVar
  els0 <- Set.fromList <$> lift (sublistOf ordinaryNames)
  rls0 <- Set.fromList <$> lift (sublistOf ordinaryNames)
  m1 <- lift $ elements mutationNames
  m2 <- lift $ elements mutationNames
  ordinary <- lift $ sublistOf ordinaryNames
  let row = ROpen (EVar e : eff m1 : eff m2 : map eff ordinary) r
  pure (e, r, els0, rls0, TFunct (Funct TInt TInt row))

genForallWithFreeTail :: Gen (Taste, Taste, Taste, Taste, Typ)
genForallWithFreeTail = runGen $ do
  e <- freshVar
  rq <- freshVar
  freeRow <- freshVar
  freeEff <- freshVar
  m <- lift $ elements mutationNames
  let quantifiedRow = ROpen [EVar e, eff m, eff "IO"] rq
      freeTailRow = ROpen [EVar freeEff, eff "Output"] freeRow
      body = TArray
        (TPair
          (TFunct (Funct TInt TInt quantifiedRow))
          (TFunct (Funct TInt TInt freeTailRow))
          (RClosed []))
        (RClosed [])
  pure (e, rq, freeRow, freeEff, body)

-- | A generator for typed expressions.  It does not try to be well typed:
--   freezing is a syntactic operation, and its invariants are syntactic too.
genExpr :: Int -> Gen TypedExpr
genExpr depth
  | depth <= 0 = oneof
      [ TEInt <$> elements [0, 1, 2]
      , TEBoolean <$> elements [True, False]
      , TEString <$> elements ["a", "b"]
      , pure TENil
      , TEXVar <$> elements ["x", "y"] <*> pure TInt
      ]
  | otherwise = oneof
      [ TEInt <$> elements [0, 1, 2]
      , TEBoolean <$> elements [True, False]
      , TEString <$> elements ["a", "b"]
      , pure TENil
      , TEXVar <$> elements ["x", "y"] <*> pure TInt
      , TEArray TInt (RClosed []) <$> listOf (genExpr (depth - 1))
      , TEPair (RClosed []) <$> genExpr (depth - 1) <*> genExpr (depth - 1)
      , TEXLambda <$> genLambda (depth - 1)
      , TEApply <$> genExpr (depth - 1) <*> genExpr (depth - 1)
      , TERecord Nothing <$> genProps (depth - 1) <*> pure (RClosed [])
      , do
          anchor <- Just <$> genExpr (depth - 1)
          props <- genProps (depth - 1)
          pure (TERecord anchor props (RClosed []))
      , TEHandle <$> genHandler (depth - 1) <*> pure TInt
      , TEParen <$> genBlock (depth - 1)
      , TEResume <$> genExpr (depth - 1) <*> pure TInt
      , TELet (LPATom ALPUnderscore)
          <$> genExpr (depth - 1) <*> genExpr (depth - 1)
      , TEPropAccess <$> genExpr (depth - 1) <*> elements ["x", "y"]
      , TEIfElse
          <$> genExpr (depth - 1)
          <*> genExpr (depth - 1)
          <*> genExpr (depth - 1)
      , TEAnnot <$> genExpr (depth - 1) <*> pure TInt
      , TEWith <$> genExpr (depth - 1) <*> pure [] <*> pure False
      ]

genLambda :: Int -> Gen Lambda
genLambda depth =
  Lambda [] [] "x" TInt TInt (RClosed []) <$> genBlock depth

genBlock :: Int -> Gen Block
genBlock depth = do
  stats <- listOf (genStat depth)
  result <- genExpr depth
  pure (stats, result)

genStat :: Int -> Gen Stat
genStat depth = oneof
  [ Bind <$> elements [Val, Var, Imm]
      <*> elements ["a", "b"] <*> genExpr depth
  , Rebind <$> elements ["a", "b"] <*> pure [] <*> genExpr depth
  , Rebind <$> elements ["a", "b"] <*> listOf (elements ["x", "y"]) <*> genExpr depth
  , Expr <$> genExpr depth
  ]

genProps :: Int -> Gen [TERecordProp]
genProps depth = listOf $
  TERecordProp
    <$> elements [Val, Var, Imm]
    <*> elements ["x", "y"]
    <*> pure TInt
    <*> genExpr depth

genHandler :: Int -> Gen Handler
genHandler depth =
  Handler (ECons "Op" []) <$> genBlock depth <*> pure [] <*> genLambda depth
