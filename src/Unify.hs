
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
module Unify (
  freshMetaM,
  freshSkolemM,
  freshBoundM,
  freshMetaTypeM, freshSkolemTypeM, freshBoundTypeM,
  freshMetaTypeArgM, freshSkolemTypeArgM, freshBoundTypeArgM,
  freshMetaEffM, freshSkolemEffM, freshBoundEffM,
  freshMetaRowM, freshSkolemRowM, freshBoundRowM,
  applyTypeSubst,
  applyTypeArgSubst,
  applyEffRowSubst,
  applyEffConsSubst,
  unifyTypes,
  unifyArgType,
  subsumesType,
  unifyTypeArgs,
  unifyTypeArgLists,
  subsumesEffRow,
  unifyEffCons,
  unifyEffRows,
  addRowLacks,
  addEffLacks,
  addEffLacksForArg,
  addRowLacksToRow,
  TypeCheckM,
  TypeCheckError(..),
  errorCode,
  runTypeCheckM,
  evalTypeCheckM,
  execTypeCheckM,
  removeConsFromRow,
  retTypeOf,
  TypeCheckState(..),
  withNewLevel,
  withErrorStack,
  currentLevel,
  errorStack,
  throwTypeCheckError,
  throwTypeCheckErrorWithNotes,
  bindRowVar,
  bindEffVar
) where

import Control.Monad.State (State)
import Types (
    Taste(..),
    Typ(..),
    EffRow(..),
    EffCons (..),
    TRecordProp(..),
    Funct(..),
    TypeArg(..),
    typeArgToTyp,
    typToTypeArg,
    TARecordProp(TARecordProp), ECons (..), tasteName
  )
import qualified Data.Map as Map hiding (map)
import qualified Data.IntMap ()
import Data.List (find, nubBy, sortOn, (\\))
import GHC.OldList (sort)
import Eff (unionEffRows)
import Occurs (typeOccursInType, typeOccursInTypeArg)
import Control.Monad (foldM, when)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.State.Lazy (runState)
import Control.Monad.Error.Class (throwError)
import Record (taName, taMut, taTypeArg)
import Data.Bifunctor (bimap)
import Text.Printf (printf)
import qualified Data.Text as T
import Data.Text (Text)
import Control.Lens (makeLenses, use, Field1 (_1), Field2 (_2), Field3 (_3), (-=), (+=), (.=))
import TypedIR (Scope(..))
import Utils (Pretty(..))
import ErrorContext (ErrorStack, ErrorFrame (..))
import Data.Set (Set)
import qualified Data.Set as Set

data TypeCheckError =
  TypeError Text
  | DuplicateDefinition Text
  | RecordError Text
  | HandlerError Text
  | ApplicationError Text
  | InferenceError Text
  | TypeArgError Text
  | TypeUnificationError Typ Typ
  | TypeArgUnificationError TypeArg TypeArg
  | EffectRowsUnificationError Text EffRow EffRow
  | EffectConsUnificationError EffCons EffCons
  | UndefinedVariable Text
  | ImmutableVariableAssignment Text
  | SameScopeBindingShadowing Text
  | EffectError Text
  | MultipleResumeError Text Int
  | TodoError Text
  deriving (Show, Eq)

data TypeCheckState = TypeCheckState {
  _counter :: (Int, Int, Int),
  _currentLevel :: Int,
  _errorStack :: ErrorStack
}

makeLenses ''TypeCheckState

withNewLevel :: TypeCheckM a -> TypeCheckM a
withNewLevel action = do
  currentLevel += 1
  result <- action
  currentLevel -= 1
  pure result

-- | Run an action with one more frame on the stack.  The stack is a scope, not
--   an accumulator: on the successful path the previous stack is restored, so
--   frames of sibling expressions never leak into one another.  On the error
--   path the exception carries the stack as it was at 'throwTypeCheckError',
--   which is exactly the path to the failing node.
withErrorStack :: ErrorFrame -> TypeCheckM a -> TypeCheckM a
withErrorStack frame action = do
  saved <- use errorStack
  errorStack .= (frame : saved)
  result <- action
  errorStack .= saved
  pure result

type TypeCheckM a = ExceptT (ErrorStack, TypeCheckError) (State TypeCheckState) a

runTypeCheckM :: TypeCheckM a -> TypeCheckState -> (Either (ErrorStack, TypeCheckError) a, TypeCheckState)
runTypeCheckM comp = runState (runExceptT comp)

evalTypeCheckM :: TypeCheckM a -> TypeCheckState -> Either (ErrorStack, TypeCheckError) a
evalTypeCheckM comp = fst . runTypeCheckM comp

execTypeCheckM :: TypeCheckM a -> TypeCheckState -> TypeCheckState
execTypeCheckM comp = snd . runTypeCheckM comp

throwTypeCheckError :: TypeCheckError -> TypeCheckM a
throwTypeCheckError err = throwError . (, err) =<< use errorStack

-- | Report an error together with notes that are not part of the frame
--   stack: a "did you mean" suggestion, for instance.  They are carried
--   as 'EFMessage' frames, which the renderer prints after the trace,
--   uncapped and never merged with a neighbour.
throwTypeCheckErrorWithNotes :: TypeCheckError -> [Text] -> TypeCheckM a
throwTypeCheckErrorWithNotes err notes = do
  stack <- use errorStack
  throwError (stack <> map EFMessage notes, err)

freshMetaM, freshSkolemM, freshBoundM :: TypeCheckM Taste
freshMetaM = do
  counter . _1 += 1
  m <- use $ counter . _1
  Meta ("m" <> pretty m) m <$> use currentLevel

freshSkolemM = do
  counter . _2 += 1
  s <- use $ counter . _2
  Skolem ("s" <> pretty s) s <$> use currentLevel

freshBoundM = do
  counter . _3 += 1
  b <- use $ counter . _3
  -- Bound vars are rigid; they don't participate in level-lowering like metas do.
  pure $ Bound ("b" <> pretty b) b

freshMetaTypeM, freshSkolemTypeM, freshBoundTypeM :: TypeCheckM Typ
freshMetaTypeM = TVar <$> freshMetaM
freshSkolemTypeM = TVar <$> freshSkolemM
freshBoundTypeM = TVar <$> freshBoundM

freshMetaTypeArgM, freshSkolemTypeArgM, freshBoundTypeArgM :: TypeCheckM TypeArg
freshMetaTypeArgM = TAVar <$> freshMetaM
freshSkolemTypeArgM = TAVar <$> freshSkolemM
freshBoundTypeArgM = TAVar <$> freshBoundM

freshMetaEffM, freshSkolemEffM, freshBoundEffM :: TypeCheckM EffCons
freshMetaEffM = EVar <$> freshMetaM
freshSkolemEffM = EVar <$> freshSkolemM
freshBoundEffM = EVar <$> freshBoundM

freshMetaRowM, freshSkolemRowM, freshBoundRowM :: TypeCheckM EffRow
freshMetaRowM = RVar <$> freshMetaM
freshSkolemRowM = RVar <$> freshSkolemM
freshBoundRowM = RVar <$> freshBoundM

lowerTasteTo :: Int -> Taste -> Taste
lowerTasteTo target = \case
  Meta n i lvl | lvl > target -> Meta n i target
  t -> t

skolemEscapesType :: Int -> Typ -> Bool
skolemEscapesType target = \case
  TVar (Skolem _ _ lvl) -> lvl > target
  TArray t r -> skolemEscapesType target t || skolemEscapesRow target r
  TPair l r fx ->
    any (skolemEscapesType target) [l, r] || skolemEscapesRow target fx
  TFunct (Funct i o row) ->
    skolemEscapesType target i || skolemEscapesType target o || skolemEscapesRow target row
  TRecord props r ->
    any (\(TRecordProp _ _ t) -> skolemEscapesType target t) props
      || skolemEscapesRow target r
  TForall _ _ _ _ _ t -> skolemEscapesType target t
  _ -> False

skolemEscapesTypeArg :: Int -> TypeArg -> Bool
skolemEscapesTypeArg target = \case
  TAVar (Skolem _ _ lvl) -> lvl > target
  TAArray t -> skolemEscapesTypeArg target t
  TAPair l r -> skolemEscapesTypeArg target l || skolemEscapesTypeArg target r
  TAFunct i o -> skolemEscapesTypeArg target i || skolemEscapesTypeArg target o
  TARecord props -> any (\(TARecordProp _ _ t) -> skolemEscapesTypeArg target t) props
  _ -> False

skolemEscapesEffCons :: Int -> EffCons -> Bool
skolemEscapesEffCons target = \case
  EffCons (ECons _ args) -> any (skolemEscapesTypeArg target) args
  EVar (Skolem _ _ lvl) -> lvl > target
  _ -> False

skolemEscapesRow :: Int -> EffRow -> Bool
skolemEscapesRow target = \case
  RClosed cs -> any (skolemEscapesEffCons target) cs
  ROpen cs t -> any (skolemEscapesEffCons target) cs || case t of
    Skolem _ _ lvl -> lvl > target
    _ -> False
  RVar t -> case t of
    Skolem _ _ lvl -> lvl > target
    _ -> False

lowerTypeTo :: Int -> Typ -> Typ
lowerTypeTo target = \case
  TVar t -> TVar $ lowerTasteTo target t
  TArray t r -> TArray (lowerTypeTo target t) $ lowerRowTo target r
  TPair l r fx -> TPair (lowerTypeTo target l) (lowerTypeTo target r) $ lowerRowTo target fx
  TFunct (Funct i o row) ->
    TFunct $ Funct (lowerTypeTo target i) (lowerTypeTo target o) $ lowerRowTo target row
  TRecord props r ->
      TRecord [TRecordProp m n $ lowerTypeTo target t | TRecordProp m n t <- props] $ lowerRowTo target r
  TForall ts es rs els rls t -> TForall ts es rs els rls $ lowerTypeTo target t
  t -> t

lowerTypeArgTo :: Int -> TypeArg -> TypeArg
lowerTypeArgTo target = \case
  TAVar t -> TAVar $ lowerTasteTo target t
  TAArray t -> TAArray $ lowerTypeArgTo target t
  TAPair l r -> TAPair (lowerTypeArgTo target l) $ lowerTypeArgTo target r
  TAFunct i o ->
    TAFunct (lowerTypeArgTo target i) $ lowerTypeArgTo target o
  TARecord props ->
      TARecord [TARecordProp m n $ lowerTypeArgTo target t | TARecordProp m n t <- props]
  t -> t

lowerEffConsTo :: Int -> EffCons -> EffCons
lowerEffConsTo target = \case
  EffCons (ECons n args) -> EffCons . ECons n $ map (lowerTypeArgTo target) args
  EVar t -> EVar $ lowerTasteTo target t

lowerRowTo :: Int -> EffRow -> EffRow
lowerRowTo target = \case
  RClosed cs -> RClosed $ map (lowerEffConsTo target) cs
  ROpen cs t -> ROpen (map (lowerEffConsTo target) cs) $ lowerTasteTo target t
  RVar t -> RVar $ lowerTasteTo target t

bindMetaType :: Scope -> Taste -> Typ -> TypeCheckM Scope
bindMetaType scope m@(Meta _ _ lvlM) t = do
  let t' = lowerTypeTo lvlM t
  if t' == TVar m
    -- Unifying a variable with itself is a no-op; inserting it would also make
    -- 'applyTypeSubst' loop, so the substitution stays acyclic here.
    then pure scope
  else if skolemEscapesType lvlM t' then throwTypeCheckError $ InferenceError "a rigid type variable would escape its scope; add a type annotation"
  else pure scope{typeSubst = Map.insert m t' $ typeSubst scope}
bindMetaType _ Skolem{} _ = throwTypeCheckError $ InferenceError "this type involves a rigid type variable and cannot be inferred; add a type annotation"
bindMetaType _ b@Bound{} _ =
  throwTypeCheckError $ InferenceError $ "bindMetaType | Cannot solve a bound variable " <> tasteName b

bindMetaTypeArg :: Scope -> Taste -> TypeArg -> TypeCheckM Scope
bindMetaTypeArg scope m@(Meta _ _ lvlM) t = do
  let t' = lowerTypeArgTo lvlM t
  if skolemEscapesTypeArg lvlM t' then
    throwTypeCheckError $ InferenceError "Skolem escapes type arg"
  else pure scope{typeArgSubst = Map.insert m t' $ typeArgSubst scope}
bindMetaTypeArg _ Skolem{} _ = throwTypeCheckError $ InferenceError "Cannot solve a skolem variable"
bindMetaTypeArg _ b@Bound{} _ =
  throwTypeCheckError $ InferenceError $ "bindMetaTypeArg | Cannot solve a bound variable " <> tasteName b

bindRowVar :: Scope -> Taste -> EffRow -> TypeCheckM Scope
bindRowVar scope m@(Meta _ _ lvlM) row = do
  let row' = lowerRowTo lvlM row

  resolved <- applyEffRowSubst scope row'

  case resolved of
    RVar n | n == m -> pure scope
    ROpen _ n | n == m ->
      throwTypeCheckError $
        InferenceError "Occurs check: a row variable occurs in its own binding"

    _ -> do
      if skolemEscapesRow lvlM row' then
        throwTypeCheckError $ InferenceError "Skolem escapes row"
      else do
        let forbidden = Map.findWithDefault Set.empty m scope.rowLacks
        scope' <- addRowLacksToRow scope resolved forbidden
        pure scope' {rowSubst = Map.insert m row' scope'.rowSubst}

bindRowVar _ s@Skolem{} _ =
  throwTypeCheckError $
    InferenceError $ "Cannot solve a skolem variable " <> tasteName s

bindRowVar _ b@Bound{} _ =
  throwTypeCheckError $
    InferenceError $ "Cannot solve a bound variable " <> tasteName b

bindEffVar :: Scope -> Taste -> EffCons -> TypeCheckM Scope
bindEffVar scope m@(Meta _ _ lvlM) e = do
  e' <- applyEffConsSubst scope e
  case e' of
    EVar n | n == m -> pure scope
    _ -> do
      let lowered = lowerEffConsTo lvlM e'
          forbidden = Map.findWithDefault Set.empty m scope.effLacks
      if skolemEscapesEffCons lvlM lowered then
        throwTypeCheckError $ InferenceError "Skolem escapes eff cons"
      else do
        scope' <- case lowered of
          EVar n -> addEffLacks scope n forbidden
          EffCons (ECons name _) -> do
            checkEffectNameLacks forbidden name
            pure scope
        pure scope' {effSubst = Map.insert m lowered scope'.effSubst}

bindEffVar _ s@Skolem{} _ =
  throwTypeCheckError $
    InferenceError $ "Cannot solve a skolem variable " <> tasteName s

bindEffVar _ b@Bound{} _ =
  throwTypeCheckError $
    InferenceError $ "Cannot solve a bound variable " <> tasteName b

-- | Resolve a type through the current substitution.
--
--   The substitution is acyclic by construction ('bindMetaType' refuses to bind
--   a variable to itself), but it is a chain, so the walk is bounded: a cycle
--   that slipped through would otherwise hang the checker rather than being
--   reported.
applyTypeSubst :: Scope -> Typ -> TypeCheckM Typ
applyTypeSubst scope = go (0 :: Int)
 where
  go fuel ty = case ty of
   TVar m -> do
    -- A type variable can reach a type position through an effect row: a
    -- parameter of a parameterised effect is a `TVar` in the operation
    -- signatures and a `TAVar` in the row, and the two substitutions are
    -- separate.  Looking in the other one keeps a single variable
    -- consistently instantiated on both sides.
    let resolved = case Map.lookup m (typeSubst scope) of
          Just t' -> Just t'
          Nothing -> typeArgToTyp <$> Map.lookup m (typeArgSubst scope)
    case resolved of
      Just t' -> if fuel > 200
        then throwTypeCheckError $ InferenceError
            (T.concat ["the type substitution does not terminate at `", tasteName m, "`"])
        else go (fuel + 1) t'
      Nothing -> pure ty
   TArray t r -> do
     t' <- go fuel t
     TArray t' <$> applyEffRowSubst scope r
   TPair l r fx -> do
     l' <- go fuel l
     r' <- go fuel r
     TPair l' r' <$> applyEffRowSubst scope fx
   TFunct (Funct i o fxs) ->
     TFunct <$> (Funct <$> go fuel i <*> go fuel o <*> applyEffRowSubst scope fxs)
   TRecord props r -> do
     props' <- traverse (\(TRecordProp mut name typ) ->
         TRecordProp mut name <$> go fuel typ
       ) props
     r' <- applyEffRowSubst scope r
     pure $ TRecord props' r'
   TForall ts es rs els rls t -> do
     let scope' = scope {
         typeSubst = foldr Map.delete scope.typeSubst ts,
         effSubst = foldr Map.delete scope.effSubst es,
         rowSubst = foldr Map.delete scope.rowSubst rs
       }
     TForall ts es rs els rls <$> applyTypeSubst scope' t
   t -> pure t

applyTypeArgSubst :: Scope -> TypeArg -> TypeCheckM TypeArg
applyTypeArgSubst scope = \case
  t@(TAVar m) -> do
    -- Mirrors 'applyTypeSubst': a variable bound as a type is still the same
    -- variable when it appears in an effect row as a type argument.
    let fromType = Map.lookup m (typeSubst scope) >>= typToTypeArg
        bound = case Map.lookup m (typeArgSubst scope) of
          Just t' -> Just t'
          Nothing -> fromType
    case bound of
      Just t'
        | t' /= t -> applyTypeArgSubst scope t'
      _ -> pure t
  TAArray t -> TAArray <$> applyTypeArgSubst scope t
  TAPair l r -> TAPair <$> applyTypeArgSubst scope l <*> applyTypeArgSubst scope r
  TAFunct i o -> TAFunct <$> applyTypeArgSubst scope i <*> applyTypeArgSubst scope o
  TARecord props -> do
    props' <- traverse (\(TARecordProp mut name typ) ->
        TARecordProp mut name <$> applyTypeArgSubst scope typ
      ) props
    pure $ TARecord props'
  t -> pure t

-- | Unify the type of an argument with the type its parameter expects.
--
--   T-App requires the row of the argument to be *included* in the latent row
--   of the parameter (@R2 ∪ Men(Γ, t2) ⊆ R@), not equal to it: the row of a
--   lambda whose body observes a mutable binding contains `Read`, and such a
--   lambda is a valid argument wherever a computation of the enclosing row is
--   expected.  Equality would reject it, so the two latent rows are related by
--   inclusion and everything else is unified as usual.
unifyArgType :: Scope -> Typ -> Typ -> TypeCheckM Scope
unifyArgType scope actual expected = do
  a <- applyTypeSubst scope actual
  e <- applyTypeSubst scope expected
  case (a, e) of
    (TFunct (Funct i1 o1 r1), TFunct (Funct i2 o2 r2)) -> do
      s1 <- unifyTypes scope i1 i2
      s2 <- unifyTypes s1 o1 o2
      subsumesEffRow s2 r1 r2
    _ -> subsumesType scope actual expected

-- | Check that a value of type @actual@ fits a declared type @declared@.
--
--   The pending row of an aggregate is an upper bound of the rows of its
--   components (T-Pair and T-Rec say so explicitly, and an array is read the
--   same way): a value whose row is smaller than the annotation fits, because
--   every use of the aggregate charges the declared row and therefore charges
--   enough.  A larger row would charge too little at use and is rejected.
--
--   Everything else is an ordinary unification.  The paper has no subtyping,
--   so a parameter type, a field type and the latent row of an arrow must
--   match exactly; only an aggregate's own annotation is relaxed.  The
--   relaxation is recursive, because a component may itself be an aggregate
--   with its own annotation: @[[Int]@{Read}]@ accepts @[[1]]@.
subsumesType :: Scope -> Typ -> Typ -> TypeCheckM Scope
subsumesType scope actual declared = do
  a <- applyTypeSubst scope actual
  d <- applyTypeSubst scope declared
  case (a, d) of
    (TArray ta ra, TArray td rd) -> do
      s <- subsumesType scope ta td
      subsumesEffRow s ra rd
    (TPair la ra fa, TPair ld rd fd) -> do
      s1 <- subsumesType scope la ld
      s2 <- subsumesType s1 ra rd
      subsumesEffRow s2 fa fd
    (TRecord pa fa, TRecord pd fd) -> do
      s <- subsumesRecords scope pa pd
      subsumesEffRow s fa fd
    _ -> unifyTypes scope actual declared

-- | 'unifyRecords' with the component types related by 'subsumesType'.
--
--   The structural checks are the ones of 'unifyRecords': the two records must
--   have the same fields, with the same mutability and no duplicates.  Only
--   the field types are relaxed, because a field may itself be an aggregate
--   with its own pending row.
subsumesRecords :: Scope -> [TRecordProp] -> [TRecordProp] -> TypeCheckM Scope
subsumesRecords scope props1 props2 = do
  let byName = sortOn tName
      zipped = zip (byName props1) (byName props2)
  if wellFormed props1 && wellFormed props2 && sameShape zipped
    then foldM (\sc (p1, p2) -> subsumesType sc (tTyp p1) (tTyp p2)) scope zipped
    else throwTypeCheckError $ TypeUnificationError
      (TRecord props1 (RClosed [])) (TRecord props2 (RClosed []))
  where
    -- No duplicate field names, which 'unifyRecords' also rejects.
    wellFormed props = length (nubBy sameName props) == length props
    sameName p q = tName p == tName q
    -- The two records name the same fields, in the same order once sorted,
    -- with the same mutability.
    sameShape zipped =
      length props1 == length props2
        && all (\(p1, p2) -> tName p1 == tName p2 && tMut p1 == tMut p2) zipped

unifyTypes :: Scope -> Typ -> Typ -> TypeCheckM Scope
unifyTypes scope t1 t2 = do
  t1' <- applyTypeSubst scope t1
  t2' <- applyTypeSubst scope t2
  case (t1', t2') of
    (TNothing, _); (TInt, TInt); (TFloat, TFloat);
      (TBoolean, TBoolean); (TString, TString); (TNil, TNil) ->
      pure scope
    (TVar x, TVar y) | x == y -> pure scope
    (TVar x@Meta{}, t) -> do
      t' <- applyTypeSubst scope t
      if typeOccursInType x t' then
        throwTypeCheckError $ TypeUnificationError t1' t'
      else
        bindMetaType scope x t'
    -- A meta on either side is solvable, so this comes before the failure
    -- case: `unifyTypes s (TVar bound) (TVar meta)` must bind the meta, not
    -- reject a rigid variable that merely happens to be on the left.  The
    -- swap is guarded by `Meta`: swapping two rigid variables would match
    -- this branch again and loop.
    (_, TVar Meta{}) -> unifyTypes scope t2' t1'
    (TVar _, _) -> throwTypeCheckError $ TypeUnificationError t1' t2'
    (TFlat x, TFlat y) | x == y -> pure scope
    (TArray l1 r1, TArray l2 r2) -> do
      scope' <- unifyTypes scope l1 l2
      unifyEffRows scope' r1 r2
    (TPair l1 r1 f1, TPair l2 r2 f2) -> do
      scope' <- unifyTypes scope l1 l2
      scope'' <- unifyTypes scope' r1 r2
      unifyEffRows scope'' f1 f2
    (TFunct (Funct i1 o1 e1), TFunct (Funct i2 o2 e2)) -> do
      scope' <- unifyTypes scope i2 i1
      scope'' <- unifyTypes scope' o1 o2
      unifyEffRows scope'' e1 e2
    (TRecord props1 f1, TRecord props2 f2) -> do
      scope' <- unifyRecords scope props1 props2
      unifyEffRows scope' f1 f2
    _ -> throwTypeCheckError $ TypeUnificationError t1' t2'

unifyRecords :: Scope -> [TRecordProp] -> [TRecordProp] -> TypeCheckM Scope
unifyRecords scope props1 props2 = if length props1 /= length props2 then
  throwTypeCheckError $ TypeUnificationError (TRecord props1 (RClosed [])) (TRecord props2 (RClosed []))
else
  let props1' = sort $ nubBy (\p1 p2 -> tName p1 == tName p2) props1 in
  let props2' = sort $ nubBy (\p1 p2 -> tName p1 == tName p2) props2 in
  if length props1 /= length props1' || length props2 /= length props2' then
    throwTypeCheckError $ TypeUnificationError (TRecord props1 (RClosed [])) (TRecord props2 (RClosed []))
  else
    let zipped = zip props1' props2' in
    if any (\(p1, p2) -> tMut p1 /= tMut p2 || tName p1 /= tName p2) zipped then
      throwTypeCheckError $ TypeUnificationError (TRecord props1 (RClosed [])) (TRecord props2 (RClosed []))
    else do
      foldM (
        \sc (typ1, typ2) -> do
          unifyTypes sc typ1 typ2
        ) scope (map (bimap tTyp tTyp) zipped)

applyEffRowSubst :: Scope -> EffRow -> TypeCheckM EffRow
applyEffRowSubst scope = \case
  r@(RVar m) -> case m of
    Meta{} ->
      case Map.lookup m (rowSubst scope) of
        Just r' -> applyEffRowSubst scope r'
        Nothing -> pure r
    Skolem{}; Bound{} -> pure r
  RClosed cs -> RClosed <$> traverse (applyEffConsSubst scope) cs
  ROpen cs t -> do
    cs' <- traverse (applyEffConsSubst scope) cs
    t' <- applyEffRowSubst scope $ RVar t
    pure $ unionEffRows (RClosed cs') t'

applyEffConsSubst :: Scope -> EffCons -> TypeCheckM EffCons
applyEffConsSubst scope = \case
  e@(EVar m) -> case m of
    Meta{} ->
      case Map.lookup m (effSubst scope) of
        Just e' -> applyEffConsSubst scope e'
        Nothing -> pure e
    Skolem{}; Bound{} -> pure e
  EffCons (ECons n args) -> EffCons . ECons n <$> traverse (applyTypeArgSubst scope) args

normalizeEffRow :: EffRow -> EffRow
normalizeEffRow = \case
  RClosed cs -> RClosed $ sort cs
  ROpen cs v -> ROpen (sort cs) v
  r -> r

-- | Split the effects of a row into those the required row provides and those
--   it does not.
--
--   An effect is matched by name, and its type arguments are unified: two
--   occurrences of `Loop` are the same effect only after their arguments have
--   been made equal.  A syntactic comparison is wrong here — `Loop[m22]` in a
--   recursive call and `Loop[T]` in the signature are the same effect, but they
--   are not the same syntax, so comparing them reports a spurious "performs
--   effects that the declared row does not allow".
matchEffCons :: Scope -> [EffCons] -> [EffCons] -> TypeCheckM (Scope, [EffCons])
matchEffCons = go []
  where
    go acc sc [] _required = pure (sc, reverse acc)
    go acc sc (cons : rest) required =
      case break (sameName cons) required of
        (_, []) -> go (cons : acc) sc rest required
        (_, found : _) -> do
          -- The required row is a set of effects: two occurrences of the same
          -- effect in the actual row (one per recursive call, say) match the
          -- same entry, so a matched entry stays available.
          sc' <- unifyEffCons sc cons found
          go acc sc' rest required

    sameName a b = case (a, b) of
      (EffCons (ECons n _), EffCons (ECons m _)) -> n == m
      (EVar v, EVar w) -> v == w
      _ -> False

subsumesEffRow :: Scope -> EffRow -> EffRow -> TypeCheckM Scope
subsumesEffRow scope r1 r2 = do
  r1' <- normalizeEffRow <$> applyEffRowSubst scope r1
  r2' <- normalizeEffRow <$> applyEffRowSubst scope r2
  case (r1', r2') of
    (RClosed cs1, RClosed cs2) -> do
      (scope', extra) <- matchEffCons scope cs1 cs2
      if null extra
        then pure scope'
        else throwTypeCheckError $ EffectRowsUnificationError
          (T.concat [
            "the body performs effects that the declared row does not allow: ",
            T.intercalate ", " $ map pretty extra])
          r1' r2'

    (RClosed cs1, ROpen cs2 v) -> do
      (scope', extra) <- matchEffCons scope cs1 cs2
      if null extra
        then pure scope'
        else do
          r <- freshMetaM
          bindRowVar scope' v (ROpen extra r)

    (ROpen cs1 v1, RClosed cs2) -> do
      if null cs1 then
        bindRowVar scope v1 (RClosed cs2)
      else do
        (scope', extra) <- matchEffCons scope cs1 cs2
        if not (null extra) then
          throwTypeCheckError $ EffectRowsUnificationError
            (T.concat [
              "this effect row is open but performs effects that the required row does not allow: ",
              T.intercalate ", " $ map pretty extra])
            (ROpen cs1 v1)
            (RClosed cs2)
        else
          bindRowVar scope' v1 (RClosed [])

    (ROpen cs1 v1, ROpen cs2 v2) -> subsumesOpenOpen scope cs1 v1 cs2 v2

    -- A bare tail is already contained in the same tail with any explicit
    -- effects: v ⊆ {cs | v}.  Conversely, {cs | v} ⊆ v forces v to grow.
    (RVar v1, ROpen _ v2) | v1 == v2 -> pure scope
    (ROpen cs1 v1, RVar v2) | v1 == v2 ->
      case cs1 of
        [] -> pure scope
        extra -> do
          r <- freshMetaM
          bindRowVar scope v1 (mkOpenRow extra r)

    (RVar v, row) -> bindRowVar scope v row
    (row, RVar v) -> bindRowVar scope v row


unifyEffRows :: Scope -> EffRow -> EffRow -> TypeCheckM Scope
unifyEffRows scope r1 r2 = do
  r1' <- normalizeEffRow <$> applyEffRowSubst scope r1
  r2' <- normalizeEffRow <$> applyEffRowSubst scope r2
  case (r1', r2') of
    (RClosed c1, RClosed c2) -> unifyClosedEffConsLists scope c1 c2
    (RClosed cl, ROpen op v) -> unifyClosedEffRowWithOpen scope cl op v
    (ROpen op v, RClosed cl) -> unifyOpenEffRowWithClosed scope op v cl
    (ROpen l1 v1, ROpen l2 v2) -> unifyOpenEffConsLists scope l1 v1 l2 v2

    (RVar e1, RVar e2) | e1 == e2 -> pure scope
    (RVar e, row) -> unifyRowVarWithEffRow scope e row
    (row, RVar e) -> unifyRowVarWithEffRow scope e row

unifyClosedEffConsLists :: Scope -> [EffCons] -> [EffCons] -> TypeCheckM Scope
unifyClosedEffConsLists scope l1 l2
  | length l1 /= length l2 =
    throwTypeCheckError $
      EffectRowsUnificationError
        (T.concat [
          "these two effect rows have different numbers of effects (",
          pretty (length l1), " and ", pretty (length l2), ")"])
        (RClosed l1)
        (RClosed l2)
  | otherwise = foldM (\scope' (e1, e2) -> unifyEffCons scope' e1 e2) scope (zip l1 l2)

unifyOpenEffConsLists :: Scope -> [EffCons] -> Taste -> [EffCons] -> Taste -> TypeCheckM Scope
unifyOpenEffConsLists scope l1 v1 l2 v2 = do
  -- Унифицируем общие эффекты
  let commonEffects = filter (`elem` l2) l1
  -- 'commonEffects' is a subset of 'l2' by construction, so the lookup never
  -- fails; skipping instead of panicking keeps the checker total.
  scope' <- foldM (\sc cons1 ->
          case find (cons1 ==) l2 of
            Nothing -> pure sc
            Just cons2 -> unifyEffCons sc cons1 cons2
        ) scope commonEffects
  unifyOpenOpen scope' l1 v1 l2 v2

-- | Ряд из явных эффектов и хвоста (пустой список эффектов даёт просто переменную)
mkOpenRow :: [EffCons] -> Taste -> EffRow
mkOpenRow [] t = RVar t
mkOpenRow cs t = ROpen cs t

-- | Унификация двух открытых рядов (по Реми): у обоих рядов общий свежий хвост r,
--   v1 := (l2 \ l1 | r), v2 := (l1 \ l2 | r). Хвост не теряется, поэтому
--   эффектная полиморфность функций высшего порядка сохраняется.
unifyOpenOpen :: Scope -> [EffCons] -> Taste -> [EffCons] -> Taste -> TypeCheckM Scope
unifyOpenOpen scope l1 v1 l2 v2
  | v1 == v2 =
      if null (l1 \\ l2) && null (l2 \\ l1)
        then pure scope
        else throwTypeCheckError $ EffectRowsUnificationError
          "these two open effect rows share a tail but disagree on their explicit effects"
          (ROpen l1 v1) (ROpen l2 v2)
  | otherwise = do
      r <- freshMetaM
      scope1 <- bindRowVar scope v1 (mkOpenRow (l2 \\ l1) r)
      bindRowVar scope1 v2 (mkOpenRow (l1 \\ l2) r)

-- | Subsumption of two open rows that may share a tail.
--
--   @{cs1 | v} ⊆ {cs2 | v}@ cannot hold for a fixed @v@ unless
--   @cs1 \\ cs2@ is empty.  The row variable of a @var@ binding, however, is
--   an upper bound that every assignment may extend, so the right solution is
--   to grow the shared tail: @v := {cs1 \\ cs2 | v'}@.  Afterwards both sides
--   denote @{cs1 ∪ cs2 | v'}@, as required.
--
--   This is deliberately separate from 'unifyOpenOpen': there the two rows
--   must denote the same set, so a shared tail with different explicit
--   effects is a genuine unification failure.  Here it is a constraint that
--   the variable is allowed to satisfy by absorbing the new effects.
subsumesOpenOpen :: Scope -> [EffCons] -> Taste -> [EffCons] -> Taste -> TypeCheckM Scope
subsumesOpenOpen scope cs1 v1 cs2 v2
  | v1 == v2 =
      case cs1 \\ cs2 of
        [] -> pure scope
        extra -> do
          r <- freshMetaM
          bindRowVar scope v1 (mkOpenRow extra r)
  | otherwise = unifyOpenOpen scope cs1 v1 cs2 v2

unifyRowVarWithEffRow :: Scope -> Taste -> EffRow -> TypeCheckM Scope
unifyRowVarWithEffRow scope v = \case
  RVar n | n == v -> pure scope
  row -> bindRowVar scope v row

unifyClosedEffRowWithOpen :: Scope -> [EffCons] -> [EffCons] -> Taste -> TypeCheckM Scope
unifyClosedEffRowWithOpen scope closed open v = do
  -- явная часть открытого ряда должна содержаться в закрытом ряду
  let missing = open \\ closed
  if not (null missing) then
    throwTypeCheckError $ EffectRowsUnificationError
      (T.concat [
        "the effect row requires effects that the closed row does not provide: ",
        T.intercalate ", " $ map pretty missing])
      (RClosed closed)
      (ROpen open v)
  else do
    -- унифицируем общие эффекты (для проверки аргументов)
    -- 'open' is a subset of 'closed' here, checked just above.
    scope' <- foldM (\sc cons1 ->
          case find (== cons1) closed of
            Nothing -> pure sc
            Just cons2 -> unifyEffCons sc cons1 cons2
        ) scope open
    -- хвост получает остаток закрытого ряда
    bindRowVar scope' v (RClosed $ closed \\ open)

unifyOpenEffRowWithClosed :: Scope -> [EffCons] -> Taste -> [EffCons] -> TypeCheckM Scope
unifyOpenEffRowWithClosed scope open v closed = unifyClosedEffRowWithOpen scope closed open v

unifyEffCons :: Scope -> EffCons -> EffCons -> TypeCheckM Scope
unifyEffCons scope c1 c2 = do
  c1' <- applyEffConsSubst scope c1
  c2' <- applyEffConsSubst scope c2

  case (c1', c2') of
    (EVar v1, EVar v2)
      | v1 == v2 -> pure scope
      | otherwise -> bindEffVar scope v1 (EVar v2)
    (EffCons (ECons name1 params1), EffCons (ECons name2 params2))
      | name1 /= name2 -> throwTypeCheckError $ EffectConsUnificationError c1' c2'
      | otherwise -> unifyTypeArgLists scope params1 params2
    (EVar t, e@EffCons{}) -> bindEffVar scope t e
    (e@EffCons{}, EVar t) -> bindEffVar scope t e
    -- (EVar _, EVar _) -> throwTypeCheckError $ EffectConsUnificationError c1' c2'

unifyTypeArgLists :: Scope -> [TypeArg] -> [TypeArg] -> TypeCheckM Scope
unifyTypeArgLists scope l1 l2 =
  let s1 = length l1; s2 = length l2
  in if length l1 /= length l2 then
    throwTypeCheckError $ ApplicationError $ T.pack $ printf "Effect parameter lists length mismatch: %d /= %d" s1 s2
  else
    foldM (\scope' (t1, t2) -> unifyTypeArgs scope' t1 t2) scope (zip l1 l2)

unifyTypeArgs :: Scope -> TypeArg -> TypeArg -> TypeCheckM Scope
unifyTypeArgs scope t1 t2 = do
  t1' <- applyTypeArgSubst scope t1
  t2' <- applyTypeArgSubst scope t2
  case (t1', t2') of
    (TANothing, _) -> pure scope
    (TAVar x, TAVar y) | x == y -> pure scope

    (TAVar x@Meta{}, t) -> do
      t' <- applyTypeArgSubst scope t
      if typeOccursInTypeArg x t' then
        throwTypeCheckError $ TypeArgUnificationError t1' t'
      else
        bindMetaTypeArg scope x t'

    -- Mirrors 'unifyTypes': a meta is solvable on either side.
    (_, TAVar Meta{}) -> unifyTypeArgs scope t2' t1'
    (TAVar _, _) -> throwTypeCheckError $ TypeArgUnificationError t1' t2'
    (TAInt, TAInt) -> pure scope
    (TAFloat, TAFloat) -> pure scope
    (TABoolean, TABoolean) -> pure scope
    (TAString, TAString) -> pure scope
    (TANil, TANil) -> pure scope
    (TAFlat x, TAFlat y) | x == y -> pure scope
    (TAArray l1, TAArray l2) -> unifyTypeArgs scope l1 l2
    (TAPair l1 r1, TAPair l2 r2) -> do
      scope' <- unifyTypeArgs scope l1 l2
      unifyTypeArgs scope' r1 r2
    (TAFunct i1 o1, TAFunct i2 o2) -> do
      scope' <- unifyTypeArgs scope i2 i1
      unifyTypeArgs scope' o1 o2
    (TARecord props1, TARecord props2) -> unifyRecordArgs scope props1 props2
    _ -> throwTypeCheckError $ TypeArgUnificationError t1' t2'

unifyRecordArgs :: Scope -> [TARecordProp] -> [TARecordProp] -> TypeCheckM Scope
unifyRecordArgs scope props1 props2 = if length props1 /= length props2 then
  throwTypeCheckError $ TypeArgUnificationError (TARecord props1) (TARecord props2)
else
  let props1' = sort $ nubBy (\p1 p2 -> taName p1 == taName p2) props1 in
  let props2' = sort $ nubBy (\p1 p2 -> taName p1 == taName p2) props2 in
  if length props1 /= length props1' || length props2 /= length props2' then
    throwTypeCheckError $ TypeArgUnificationError (TARecord props1) (TARecord props2)
  else
    let zipped = zip props1' props2' in
    if any (\(p1, p2) -> taMut p1 /= taMut p2 || taName p1 /= taName p2) zipped then
      throwTypeCheckError $ TypeArgUnificationError (TARecord props1) (TARecord props2)
    else do
      foldM (
        \sc (typ1, typ2) -> do
          unifyTypeArgs sc typ1 typ2
        ) scope (map (bimap taTypeArg taTypeArg) zipped)

removeConsFromRow :: EffCons -> EffRow -> EffRow
removeConsFromRow cons = \case
  RClosed lst -> RClosed $ filter (cons /=) lst
  ROpen lst var -> ROpen (filter (cons /=) lst) var
  r@(RVar _) -> r

retTypeOf :: Typ -> Maybe Typ
retTypeOf (TFunct (Funct _ o _)) = go o
  where
    go (TFunct (Funct _ o' _)) = go o'
    go t = Just t

retTypeOf _ = Nothing

checkEffectNameLacks :: Set Text -> Text -> TypeCheckM ()
checkEffectNameLacks forbidden name =
  when (name `Set.member` forbidden) $
    throwTypeCheckError $
      InferenceError $ "Forbidden effect in constrained row: " <> name

addEffLacks :: Scope -> Taste -> Set Text -> TypeCheckM Scope
addEffLacks scope variable forbidden = do
  resolved <- applyEffConsSubst scope (EVar variable)

  case resolved of
    EVar variable' ->
      pure scope {
        effLacks = Map.insertWith Set.union variable' forbidden scope.effLacks
      }

    EffCons (ECons name _) -> do
      checkEffectNameLacks forbidden name
      pure scope

addRowLacks :: Scope -> Taste -> Set Text -> TypeCheckM Scope
addRowLacks scope variable forbidden = do
  resolved <- applyEffRowSubst scope (RVar variable)

  case resolved of
    RVar variable' ->
      pure scope {
        rowLacks = Map.insertWith Set.union
          variable' forbidden scope.rowLacks
      }

    row ->
      addRowLacksToRow scope row forbidden

addEffLacksForArg :: Scope -> EffCons -> Set Text -> TypeCheckM Scope
addEffLacksForArg scope effect = addRowLacksToRow scope $ RClosed [effect]

addRowLacksToRow :: Scope -> EffRow -> Set Text -> TypeCheckM Scope
addRowLacksToRow scope row forbidden =
  case row of
    RClosed effects -> foldM addEffectLacks scope effects
    ROpen effects tailVar -> do
      scope' <- foldM addEffectLacks scope effects
      addRowLacks scope' tailVar forbidden

    RVar variable -> addRowLacks scope variable forbidden
  where
    addEffectLacks sc effect =
      case effect of
        EffCons (ECons name _) -> do
          checkEffectNameLacks forbidden name
          pure sc
        EVar variable -> addEffLacks sc variable forbidden

-- | How an error reads in a diagnostic.  The messages are prose because they
--   are shown to the user; the constructor names are an implementation detail
--   of the checker.  'errorCode' supplies the stable identifier that goes in
--   the square brackets of the header line.
instance Pretty TypeCheckError where
  pretty = \case
    TypeError e -> e
    DuplicateDefinition e -> e
    RecordError e -> e
    HandlerError e -> e
    ApplicationError e -> e
    InferenceError e -> e
    TypeArgError e -> e
    TypeUnificationError l r ->
      T.concat ["cannot unify the type `", pretty l, "` with the type `", pretty r, "`"]
    TypeArgUnificationError l r ->
      T.concat ["cannot unify the type argument `", pretty l, "` with `", pretty r, "`"]
    EffectRowsUnificationError t _ _ -> t
    EffectConsUnificationError l r ->
      T.concat ["cannot unify the effects `", pretty l, "` and `", pretty r, "`"]
    UndefinedVariable e ->
      T.concat ["`", e, "` is not in scope"]
    ImmutableVariableAssignment e ->
      T.concat ["cannot assign to `", e, "`, which is bound with `val` or `imm`"]
    SameScopeBindingShadowing e ->
      T.concat ["`", e, "` is already bound in this scope; use a different name"]
    EffectError e -> e
    MultipleResumeError e n ->
      T.concat ["`", e, "` resumes ", pretty n, " times; a handler clause may resume at most once"]
    TodoError e -> e

-- | The stable code a diagnostic carries.  Users can search for it, and it
--   does not change when the wording of the message does.
errorCode :: TypeCheckError -> Maybe Text
errorCode = \case
  TypeError _ -> Just "E0001"
  DuplicateDefinition _ -> Just "E0014"
  RecordError _ -> Just "E0015"
  HandlerError _ -> Just "E0016"
  ApplicationError _ -> Just "E0017"
  InferenceError _ -> Just "E0018"
  TypeArgError _ -> Just "E0002"
  TypeUnificationError _ _ -> Just "E0003"
  TypeArgUnificationError _ _ -> Just "E0004"
  EffectRowsUnificationError {} -> Just "E0005"
  EffectConsUnificationError _ _ -> Just "E0006"
  UndefinedVariable _ -> Just "E0007"
  ImmutableVariableAssignment _ -> Just "E0008"
  SameScopeBindingShadowing _ -> Just "E0009"
  EffectError _ -> Just "E0010"
  MultipleResumeError _ _ -> Just "E0011"
  TodoError _ -> Just "E0012"