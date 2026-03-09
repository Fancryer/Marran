{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module Unify (
  freshMetaM,
  freshSkolemM,
  freshBoundM,
  freshMetaTypeM,
  freshSkolemTypeM,
  freshBoundTypeM,
  freshMetaEffM,
  freshSkolemEffM,
  freshBoundEffM,
  applyTypeSubst,
  applyEffRowSubst,
  unifyTypes,
  TypeCheckM,
  TypeCheckError(..),
  runTypeCheckM,
  evalTypeCheckM,
  execTypeCheckM,
  removeConsFromRow,
  retTypeOf
) where

import Control.Monad.State (State)
import Control.Monad.State.Class
import Types (Taste(..), Typ (..), EffRow(..), Scope(..), EffCons, TRecordProp (TRecordProp))
import qualified Data.Map as Map hiding (map)
import qualified Data.IntMap ()
import Data.List (nub, find, nubBy)
import GHC.OldList (sort)
import Eff (extractEffects)
import Occurs (effConsContainsEffects,typeOccursInType, effOccursInEffRow)
import Control.Monad (foldM)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.State.Lazy (runState)
import Control.Monad.Error.Class (throwError)
import Record (tMut, tName, tTyp)
import Data.Bifunctor (bimap)

data TypeCheckError =
  TypeError String
  | TypeUnificationError Typ Typ
  | EffectUnificationError EffRow EffRow
  | EffectConsUnificationError EffCons EffCons
  | EffectConsContainsEffect EffCons  -- ваша ошибка
  | UndefinedVariable String
  | ImmutableVariableAssignment String
  | SameScopeBindingShadowing String
  | EffectError String
  deriving (Show, Eq)

type Counter = (Int, Int) -- Meta, Skolem

type TypeCheckM a = ExceptT TypeCheckError (State Counter) a

runTypeCheckM :: TypeCheckM a -> Counter -> (Either TypeCheckError a, Counter)
runTypeCheckM comp = runState (runExceptT comp)

evalTypeCheckM :: TypeCheckM a -> Counter -> Either TypeCheckError a
evalTypeCheckM comp = fst . runTypeCheckM comp

execTypeCheckM :: TypeCheckM a -> Counter -> Counter
execTypeCheckM comp = snd . runTypeCheckM comp

newtype Gen a = Gen {runGen :: State Counter a}
  deriving (Functor, Applicative, Monad, MonadState Counter)

freshMetaM, freshSkolemM, freshBoundM :: TypeCheckM Taste
freshMetaM = do
  (m, s) <- get
  let m' = m + 1
  put (m', s)
  pure $ Meta ("m" ++ show m') m'

freshSkolemM = do
  (m, s) <- get
  put (m, s + 1)
  pure $ Skolem ("s" ++ show (s + 1))

freshBoundM = do
  (m, s) <- get
  put (m, s + 1)
  pure $ Bound ("b" ++ show (s + 1))

freshMetaTypeM, freshSkolemTypeM, freshBoundTypeM :: TypeCheckM Typ
freshMetaTypeM = TVar <$> freshMetaM
freshSkolemTypeM = TVar <$> freshSkolemM
freshBoundTypeM = TVar <$> freshBoundM

freshMetaEffM, freshSkolemEffM, freshBoundEffM :: TypeCheckM EffRow
freshMetaEffM = EVar <$> freshMetaM
freshSkolemEffM = EVar <$> freshSkolemM
freshBoundEffM = EVar <$> freshBoundM

applyTypeSubst :: Scope -> Typ -> TypeCheckM Typ
applyTypeSubst scope = \case
  t@(TVar m@(Meta _ lvl)) ->
    case Map.lookup m (typeSubst scope) of
      Just t' -> applyTypeSubst scope t'
      Nothing -> pure t
  t@(TVar (Skolem _)) -> pure t
  TList t -> TList <$> applyTypeSubst scope t
  TPair l r -> TPair <$> applyTypeSubst scope l <*> applyTypeSubst scope r
  TFunc (i, o, fxs) -> do
    i' <- applyTypeSubst scope i
    o' <- applyTypeSubst scope o
    fxs' <- applyEffRowSubst scope fxs
    pure $ TFunc (i', o', fxs')
  TRecord props -> do
    props' <- traverse (\(TRecordProp mut name typ) ->
        TRecordProp mut name <$> applyTypeSubst scope typ
      ) props
    pure $ TRecord props'
  t -> pure t

applyEffRowSubst :: Scope -> EffRow -> TypeCheckM EffRow
applyEffRowSubst scope row =
  let newEffRowOrError = case row of
        EVar (Skolem _) -> pure row
        EVar (Bound _) -> pure row
        EVar v@(Meta _ lvl) ->
          case Map.lookup v (effSubst scope) of
            Just substitutedRow -> applyEffRowSubst scope substitutedRow
            Nothing -> pure row
        EClosed cons -> do
          cons' <- traverse processEffCons cons
          pure $ EClosed cons'
        EOpen cons v -> do
          cons' <- traverse processEffCons cons
          case Map.lookup v (effSubst scope) of
            Just (EVar newV) -> pure $ EOpen cons' newV
            Just (EClosed extraCons) -> do
              extraCons' <- traverse processEffCons extraCons
              pure $ EClosed $ sort $ nub $ cons' ++ extraCons' -- Хвост стал конкретным
            Just (EOpen extraCons newV) -> do
              extraCons' <- traverse processEffCons extraCons
              pure $ EOpen (sort $ nub $ cons' ++ extraCons') newV
            Nothing -> pure $ EOpen cons' v
  in newEffRowOrError >>= (\newRow ->
    case find effConsContainsEffects $ extractEffects newRow of
      Just c -> throwError $ EffectConsContainsEffect c
      _ -> pure newRow
  )
  where
    -- Функция для обработки одного эффекта
    processEffCons :: EffCons -> TypeCheckM EffCons
    processEffCons (name, params) = do
      params' <- traverse (applyTypeSubst scope) params  -- traverse вместо map
      pure (name, params')

unifyTypes :: Scope -> Typ -> Typ -> TypeCheckM Scope
unifyTypes scope t1 t2 = do
  t1' <- applyTypeSubst scope t1
  t2' <- applyTypeSubst scope t2
  case (t1', t2') of
    (TNothing, _) -> pure scope
    (TVar x, TVar y) | x == y -> pure scope
    (TVar x@(Meta _ lvl), t) -> do
      t' <- applyTypeSubst scope t
      if typeOccursInType x t' then
        throwError $ TypeUnificationError t1' t'
      else
        let newSubst = Map.insert x t' (typeSubst scope) in
        pure $ scope {typeSubst = newSubst}
    (t, TVar _) -> unifyTypes scope t2' t
    (TInt, TInt) -> pure scope
    (TFloat, TFloat) -> pure scope
    (TBoolean, TBoolean) -> pure scope
    (TString, TString) -> pure scope
    (TNil, TNil) -> pure scope
    (TFlat x, TFlat y) | x == y -> pure scope
    (TList l1, TList l2) -> unifyTypes scope l1 l2
    (TPair l1 r1, TPair l2 r2) -> do
      scope' <- unifyTypes scope l1 l2
      unifyTypes scope' r1 r2
    (TFunc (i1, o1, e1), TFunc (i2, o2, e2)) -> do
      scope' <- unifyTypes scope i2 i1
      scope'' <- unifyTypes scope' o1 o2
      unifyEffRows scope'' e1 e2
    (TRecord props1, TRecord props2) -> unifyRecords scope props1 props2
    _ -> throwError $ TypeUnificationError t1' t2'

unifyRecords :: Scope -> [TRecordProp] -> [TRecordProp] -> TypeCheckM Scope
unifyRecords scope props1 props2 = do
  if length props1 /= length props2 then
    throwError $ TypeUnificationError (TRecord props1) (TRecord props2)
  else
    let props1' = sort $ nubBy (\p1 p2 -> tName p1 == tName p2) props1 in
    let props2' = sort $ nubBy (\p1 p2 -> tName p1 == tName p2) props2 in
    if length props1 /= length props1' || length props2 /= length props2' then
      throwError $ TypeUnificationError (TRecord props1) (TRecord props2)
    else
      let zipped = zip props1' props2' in
      if any (\(p1, p2) -> tMut p1 /= tMut p2 || tName p1 /= tName p2) zipped then
        throwError $ TypeUnificationError (TRecord props1) (TRecord props2)
      else do
        foldM (
          \sc (typ1, typ2) -> do
            unifyTypes sc typ1 typ2
          ) scope (map (bimap tTyp tTyp) zipped)

unifyEffRows :: Scope -> EffRow -> EffRow -> TypeCheckM Scope
unifyEffRows scope r1 r2 = do
  r1' <- applyEffRowSubst scope r1
  r2' <- applyEffRowSubst scope r2
  case (r1', r2') of
    (EVar e1, EVar e2) | e1 == e2 -> pure scope
    (EVar e, row) -> unifyEffVarWithRow scope e row
    (row, EVar e) -> unifyEffVarWithRow scope e row
    (EClosed c1, EClosed c2) -> unifyClosedEffConsLists scope c1 c2
    (EOpen l1 v1, EOpen l2 v2) -> unifyOpenEffConsLists scope l1 v1 l2 v2
    (EClosed cl, EOpen op v) -> unifyClosedEffRowWithOpen scope cl op v
    (EOpen op v, EClosed cl) -> unifyClosedEffRowWithOpen scope cl op v

unifyEffVarWithRow :: Scope -> Taste -> EffRow -> TypeCheckM Scope
unifyEffVarWithRow scope v row = case v of
  Skolem _ -> throwError $ EffectUnificationError (EVar v) row
  m@(Meta _ lvl) ->
    if effOccursInEffRow v row then
      throwError $ EffectUnificationError (EVar v) row
    else
      pure $ scope {effSubst = Map.insert m row (effSubst scope)}

unifyClosedEffConsLists :: Scope -> [EffCons] -> [EffCons] -> TypeCheckM Scope
unifyClosedEffConsLists scope l1 l2
  | length l1 /= length l2 = throwError $ EffectUnificationError (EClosed l1) (EClosed l2)
  | otherwise = foldM unifyPair scope (zip l1 l2)
  where
    unifyPair scope' ((name1, params1), (name2, params2))
      | name1 /= name2 = throwError $ EffectUnificationError (EClosed l1) (EClosed l2)
      | otherwise = unifyTypeLists scope' params1 params2


unifyOpenEffConsLists :: Scope -> [EffCons] -> Taste -> [EffCons] -> Taste -> TypeCheckM Scope
unifyOpenEffConsLists scope l1 v1 l2 v2 =
  -- Унифицируем общие эффекты
  let commonEffects = filter (`elem` l2) l1 in
  let scope' = foldM (\sc cons1 ->
          case find (cons1 ==) l2 of
            Nothing -> throwError $ EffectConsUnificationError cons1 (error "Shall not happen")
            Just cons2 -> unifyEffCons sc cons1 cons2
        ) scope commonEffects in
  -- Находим эффекты, уникальные для каждого ряда
  let uniqueToL1 = filter (`notElem` l2) l1 in
  let uniqueToL2 = filter (`notElem` l1) l2 in
  let allEffects = commonEffects ++ uniqueToL1 ++ uniqueToL2 in
  let combinedEffects = sort $ nub allEffects in do
    -- Создаём новую переменную для объединённого хвоста
    freshTail <- freshMetaM
  -- Унифицируем исходные переменные с новым объединённым рядом
    let combinedRow = EOpen combinedEffects freshTail
    scope'' <- scope'
    scope''' <- unifyEffVarWithRow scope'' v1 combinedRow
    unifyEffVarWithRow scope''' v2 combinedRow

unifyClosedEffRowWithOpen :: Scope -> [EffCons] -> [EffCons] -> Taste -> TypeCheckM Scope
unifyClosedEffRowWithOpen scope closed open v =
  -- Проверяем, что все open_labels есть в closed_labels
  let allPresent = all (`elem` closed) open in
  if not allPresent then
    throwError $ EffectUnificationError (EClosed closed) (EOpen open v)
  else do
    -- Унифицируем общие эффекты
    scope' <- foldM (\sc cons1 ->
          case find (== cons1) closed of
            Nothing ->
              -- Этот случай теоретически невозможен, так как allPresent
              throwError $ EffectConsUnificationError cons1 (error "Should not happen")
            Just cons2 ->
              unifyEffCons sc cons1 cons2
          ) scope open
    -- Находим эффекты в closed_labels, которых нет в open_labels
    let extraEffects = filter (`notElem` open) closed
    unifyEffVarWithRow scope' v
      $ EClosed
      $ if extraEffects /= [] then
        -- Extra effects должны быть учтены в переменной v
        extraEffects
      else
        -- Нет extra effects - переменная v должна быть пустой
        []

unifyEffCons :: Scope -> EffCons -> EffCons -> TypeCheckM Scope
unifyEffCons scope c1@(name1, params1) c2@(name2, params2)
  | name1 /= name2 = throwError $ EffectConsUnificationError c1 c2
  | otherwise = unifyTypeLists scope params1 params2

unifyTypeLists :: Scope -> [Typ] -> [Typ] -> TypeCheckM Scope
unifyTypeLists scope l1 l2
  | length l1 /= length l2 = throwError $ TypeError "Effect parameter lists length mismatch" -- TODO: add lengths
  | otherwise = foldM (\scope' (t1, t2) -> unifyTypes scope' t1 t2) scope (zip l1 l2)

removeConsFromRow :: EffCons -> EffRow -> EffRow
removeConsFromRow cons = \case
  EClosed lst -> EClosed $ filter (cons /=) lst
  EOpen lst var -> EOpen (filter (cons /=) lst) var
  r@(EVar _) -> r

retTypeOf :: Typ -> Maybe Typ
retTypeOf (TFunc (_, o, _)) = go o
  where
    go (TFunc (_, o', _)) = go o'
    go t = Just t

retTypeOf _ = Nothing