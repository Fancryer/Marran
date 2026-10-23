{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
module Infer (
  isTypeMonomorphic,
  countResumeInBlock,
  countResumeInStat,
  countResumeInExpr,
  countResumeInLambda,
  inferExpr,
  inferStat,
  inferBlock,
  inferChunk,
  freezeMutability,
  freeze,
  freezeBlock,
  freezeLambda,
  InferResult(..)
) where
import Types(
    Typ(..),
    Funct(Funct),
    EffRow(..),
    TypeArg(..),
    Block,
    Stat(..),
    Expr(..),
    Handler(..),
    Lambda,
    Lambda(..),
    Taste(..),
    Mutability(..),
    tasteName,
    EffCons(..),
    TypeScheme,
    Scheme(..),
    NativeLambdaSign(..),
    handlerCons,

    HandlerSig(HandlerSig),
    ERecordProp(..),
    TRecordProp(..),
    LetPattern(..),
    TRecordProp(..),
    LetPattern(LPParam),
    LambdaParam(LambdaParam),
    AtomLetPattern(ALPNil, ALPUnderscore, ALPPair, ALPRecord),
    LetPatternRecordProp(LetPatternRecordProp),
    Chunk,
    TopLevelStat(..),
    effName,
    FunctDecl(..),
    pureTFunc, tfunc, ECons (..), countArgs
  )
import qualified Data.Map as Map
import Record (taTypeArg, eExp)
import Resume (ResumeInfo(..))
import Unify (
    TypeCheckM,
    TypeCheckError(..),
    unifyTypes,
    applyTypeSubst,
    freshMetaTypeM,
    unifyEffRows,
    freshMetaM,
    removeConsFromRow,
    retTypeOf,
    applyEffRowSubst,
    withNewLevel,
    currentLevel, subsumesEffRow, errorStack, throwTypeCheckError, withErrorStack
  )
import qualified Eff
import qualified Scope
import Control.Monad.Except (MonadError(throwError))
import Control.Monad (foldM, when, forM)
import Scope (enterScope)
import Utils (uniqPreserveOrder, mapFst, Pretty (pretty))
import qualified Data.Text as T
import Data.List (sort, nub, find, nubBy)
import Text.Printf (printf)
import Data.Maybe (isNothing, fromMaybe, catMaybes)
import TypedIR (
    Scope(..),
    TypedExpr(..),
    Block,
    Lambda(..),
    TERecordProp(..),
    Stat(..),
    Handler(..),
    typeOfTypedExpr,
    typeOfTypedBlock,
    Chunk,
    TopLevelStat(..),
    FunctDecl(..), HandlerClause
  )
import Data.Text (Text)
import Control.Lens (use, (^.))
import Eff (rowHasEffect)
import Control.Monad.IO.Class (liftIO)
import Debug.Trace (trace, traceM)
import ErrorContext (withFrame, IrFrame (IrFrame), ErrorFrame (..))

data InferResult a = InferResult {
    irResult :: a,
    irRow :: EffRow,
    irScope :: Scope
  }

type InferM a = TypeCheckM (InferResult a)

isTypeMonomorphic :: Scope -> Typ -> Bool
isTypeMonomorphic scope = \case
  TForall{} -> False
  TVar v -> maybe False (isTypeMonomorphic scope) $ Map.lookup v $ typeSubst scope
  TArray t -> isTypeMonomorphic scope t
  TPair l r -> isTypeMonomorphic scope l && isTypeMonomorphic scope r
  TFunct (Funct i o fxs) -> all (isTypeMonomorphic scope) [i, o] && isEffRowMonomorphic scope fxs
  TRecord props -> all (isTypeMonomorphic scope . tTyp) props
  _ -> True

isTypeArgMonomorphic :: Scope -> TypeArg -> Bool
isTypeArgMonomorphic scope = \case
  TAVar v -> maybe False (isTypeMonomorphic scope) $ Map.lookup v $ typeSubst scope
  TAArray t -> isTypeArgMonomorphic scope t
  TAPair l r -> isTypeArgMonomorphic scope l && isTypeArgMonomorphic scope r
  TAFunct i o -> isTypeArgMonomorphic scope i && isTypeArgMonomorphic scope o
  TARecord props -> all (isTypeArgMonomorphic scope . taTypeArg) props
  _ -> True

isEffConsMonomorphic :: Scope -> EffCons -> Bool
isEffConsMonomorphic scope = \case
  EVar e -> maybe False (isEffRowMonomorphic scope) $ Map.lookup e $ rowSubst scope
  -- check scope[name]??
  EffCons (ECons _ ts) -> isTypeArgMonomorphic scope `all` ts

isEffRowMonomorphic :: Scope -> EffRow -> Bool
isEffRowMonomorphic scope = \case
  RClosed cons -> isEffConsMonomorphic scope `all` cons
  ROpen cons t -> isEffConsMonomorphic scope `all` cons && isEffRowMonomorphic scope (RVar t)
  RVar _ -> True -- or False??

substituteTypedExpr :: Scope -> TypedExpr -> TypeCheckM TypedExpr
substituteTypedExpr scope = \case
  TEInt i -> pure $ TEInt i
  TEFloat f -> pure $ TEFloat f
  TEBoolean b -> pure $ TEBoolean b
  TEString s -> pure $ TEString s
  TENil -> pure TENil
  TEXVar v t -> TEXVar v <$> applyTypeSubst scope t
  TEArray t es -> do
    t' <- applyTypeSubst scope t
    es' <- mapM (substituteTypedExpr scope) es
    pure $ TEArray t' es'
  TEPair l r -> TEPair <$> substituteTypedExpr scope l <*> substituteTypedExpr scope r
  TEXLambda lam -> do
    argT' <- applyTypeSubst scope lam.lArgT
    retT' <- applyTypeSubst scope lam.lRetT
    fxs' <- applyEffRowSubst scope lam.lFxs
    block' <- substituteBlock scope lam.lBlock
    pure $ TEXLambda (lam {TypedIR.lArgT = argT', TypedIR.lRetT = retT', TypedIR.lFxs = fxs', TypedIR.lBlock = block'})
  TEApply f x -> TEApply <$> substituteTypedExpr scope f <*> substituteTypedExpr scope x
  TERecord m props -> do
    m' <- mapM (substituteTypedExpr scope) m
    props' <- mapM (substituteRecordProp scope) props
    pure $ TERecord m' props'
  TEParen block -> TEParen <$> substituteBlock scope block
  TEResume e t -> TEResume <$> substituteTypedExpr scope e <*> applyTypeSubst scope t
  TELet pat bound body -> do
    bound' <- substituteTypedExpr scope bound
    body' <- substituteTypedExpr scope body
    pure $ TELet pat bound' body'
  TEPropAccess e f -> TEPropAccess <$> substituteTypedExpr scope e <*> pure f
  TEIfElse p t f -> TEIfElse <$> substituteTypedExpr scope p <*> substituteTypedExpr scope t <*> substituteTypedExpr scope f
  TEHandle handler t -> do
    t' <- applyTypeSubst scope t
    handler' <- substituteHandler scope handler
    pure $ TEHandle handler' t'
  TENLambda (NativeLambdaSign n i o r) ->
    TENLambda <$> (NativeLambdaSign n
      <$> applyTypeSubst scope i
      <*> applyTypeSubst scope o
      <*> applyEffRowSubst scope r)

substituteRecordProp :: Scope -> TERecordProp -> TypeCheckM TERecordProp
substituteRecordProp scope (TERecordProp mut name t e) = do
  t' <- applyTypeSubst scope t
  e' <- substituteTypedExpr scope e
  pure $ TERecordProp mut name t' e'

substituteBlock :: Scope -> TypedIR.Block -> TypeCheckM TypedIR.Block
substituteBlock scope (stats, expr) = do
  stats' <- mapM (substituteStat scope) stats
  expr' <- substituteTypedExpr scope expr
  pure (stats', expr')

substituteStat :: Scope -> TypedIR.Stat -> TypeCheckM TypedIR.Stat
substituteStat scope = \case
  TypedIR.Bind mut n e -> TypedIR.Bind mut n <$> substituteTypedExpr scope e
  TypedIR.Rebind n e -> TypedIR.Rebind n <$> substituteTypedExpr scope e
  TypedIR.Expr e -> TypedIR.Expr <$> substituteTypedExpr scope e

substituteHandler :: Scope -> TypedIR.Handler -> TypeCheckM TypedIR.Handler
substituteHandler scope = \case
  TypedIR.Handler eff block clauses mThen -> do
    TypedIR.Handler eff
      <$> substituteBlock scope block
      <*> mapM (\(name, lam, r, i) -> (name, , r, i) <$> substituteLambda scope lam) clauses
      <*> substituteLambda scope mThen

substituteLambda :: Scope -> TypedIR.Lambda -> TypeCheckM TypedIR.Lambda
substituteLambda scope lam = do
  argT' <- applyTypeSubst scope lam.lArgT
  retT' <- applyTypeSubst scope lam.lRetT
  fxs' <- applyEffRowSubst scope lam.lFxs
  block' <- substituteBlock scope lam.lBlock
  pure $ lam {TypedIR.lArgT = argT', TypedIR.lRetT = retT', TypedIR.lFxs = fxs', TypedIR.lBlock = block'}

countResumeInBlock :: Types.Block -> ResumeInfo
countResumeInBlock (stats, e) =
  foldl (\acc stat -> acc <> countResumeInStat stat) NoResume (stats <> [Types.Expr e])

countResumeInStat :: Types.Stat -> ResumeInfo
countResumeInStat = \case
  Types.Expr e -> countResumeInExpr e
  Types.Assign _ e -> countResumeInExpr e
  Types.Bind _ _ _ e -> countResumeInExpr e

countResumeInExpr :: Expr -> ResumeInfo
countResumeInExpr = \case
  Array es -> foldl (<>) NoResume $ map countResumeInExpr es
  Pair l r -> countResumeInExpr l <> countResumeInExpr r
  XLambda l -> countResumeInLambda l
  Apply f x -> countResumeInExpr f <> countResumeInExpr x
  With e _ _ _ -> countResumeInExpr e
  Handle (Types.Handler _ block' cs then_) ->
    countResumeInBlock block'
    <> foldl (<>) NoResume (map (countResumeInBlock . Types.lBlock . snd) cs)
    <> countResumeInLambda then_
  Resume e -> OneResume <> countResumeInExpr e
  Record e props ->
    foldl (<>) (maybe NoResume countResumeInExpr e) $ map (countResumeInExpr . eExp) props
  Paren b -> countResumeInBlock b
  Let _ wht whr -> countResumeInExpr wht <> countResumeInExpr whr
  PropAccess e _ -> countResumeInExpr e
  IfElse p t f -> countResumeInExpr p <> countResumeInExpr t <> countResumeInExpr f
  _ -> NoResume

countResumeInLambda :: Types.Lambda -> ResumeInfo
countResumeInLambda l = countResumeInBlock l.lBlock

substituteType :: Scope -> Taste -> TypeArg -> Scope
substituteType scope taste typ = scope {typeArgSubst = Map.insert taste typ scope.typeArgSubst}

substituteEffRow :: Scope -> Taste -> EffRow -> Scope
substituteEffRow scope taste eff = scope {rowSubst = Map.insert taste eff scope.rowSubst}

substituteEffCons :: Scope -> Taste -> EffCons -> Scope
substituteEffCons scope taste eff = scope {effSubst = Map.insert taste eff scope.effSubst}

buildCurried :: [Typ] -> Maybe EffRow -> Typ -> Typ
buildCurried []     fxs ret = TFunct $ Funct TNil ret $ fromMaybe (RClosed []) fxs
buildCurried [a]    fxs ret = TFunct $ Funct a ret $ fromMaybe (RClosed []) fxs
buildCurried (a:as) fxs ret = tfunc a $ buildCurried as fxs ret

typeOfTypedExprUnsafe :: TypedExpr -> TypeCheckM Typ
typeOfTypedExprUnsafe e = do
  case typeOfTypedExpr e of
    Left l -> throwTypeCheckError $ TypeError l
    Right r -> pure r

typeOfTypedBlockUnsafe :: TypedIR.Block -> TypeCheckM Typ
typeOfTypedBlockUnsafe b = do
  case typeOfTypedBlock b of
    Left l -> throwTypeCheckError $ TypeError l
    Right r -> pure r

-- most important
inferChunk :: [Text] -> Types.Chunk -> TypeCheckM TypedIR.Chunk
inferChunk args chunk = do
  globalScope <- Scope.globalScope args
  eStack <- use errorStack
  let _ = withFrame (EFIr $ IrFrame "" Nothing) eStack $ \stack ->
        stack
  -- Первый проход: регистрируем только эффекты и функции (с предварительными схемами)
  (scope1, funSigs) <- foldM (\(sc, sigs) stat -> case stat of
      Types.SEffDef effDef -> do
        when (Scope.hasEff False sc (effName effDef)) $
          throwTypeCheckError $ TypeError $ "Duplicate effect definition: " <> effName effDef
        sc' <- Scope.addEffect effDef sc
        pure (sc', sigs)

      Types.SFunctDef functDecl -> do
        let (retFxs, retTyp) = functDecl.fRet
            argTypes = map snd functDecl.fArgs
            -- fullTyp = buildCurried argTypes retFxs retTyp
            -- tvars = map (`Bound` 0) functDecl.fTvars
            -- evars = map (`Bound` 0) functDecl.fEvars
            -- rvars = map (`Bound` 0) functDecl.fRvars
            -- scheme = Scheme tvars evars rvars fullTyp
        let fullTyp = buildCurried argTypes retFxs retTyp
        let allTvars = collectTvarsFromType [] fullTyp
        let allEvars = collectEvarsFromType [] fullTyp
        let allRvars = collectRvarsFromType [] fullTyp

        -- Превращаем все собранные переменные в параметры схемы (Bound)
        -- Но мы должны сохранить явные параметры, если они есть, и объединить с неявными, убрав дубликаты.
        let explicitTvars = map (`Bound` 0) functDecl.fTvars
        let explicitEvars = map (`Bound` 0) functDecl.fEvars
        let explicitRvars = map (`Bound` 0) functDecl.fRvars

        -- Убираем дубликаты по идентификатору
        let tvars = uniqPreserveOrder $ explicitTvars <> allTvars
        let evars = uniqPreserveOrder $ explicitEvars <> allEvars
        let rvars = uniqPreserveOrder $ explicitRvars <> allRvars

        let scheme = Scheme tvars evars rvars fullTyp

        when (Scope.hasBinding False sc functDecl.fName) $
          throwTypeCheckError $ TypeError $ "Duplicate function definition: " <> functDecl.fName

        sc' <- Scope.addBinding functDecl.fName scheme (XVar functDecl.fName) Val sc
        pure (sc', sigs <> [(functDecl, retFxs, retTyp)])

      _ -> pure (sc, sigs)
    ) (globalScope, []) chunk

  -- Второй проход: типизируем тела функций и обновляем схемы
  (scope2, typedFuns) <- foldM (\(sc, acc) (functDecl, retFxs, retTyp) -> do
      let funScope = enterScope sc
      scopeWithArgs <- foldM (\sc' (argName, argTyp) ->
          Scope.addBinding argName (Scheme [] [] [] argTyp) (XVar argName) Val sc'
        ) funScope functDecl.fArgs

      InferResult typedBlock blockFxs finalScope <- inferBlock scopeWithArgs functDecl.fBlock
      blockTyp <- typeOfTypedBlockUnsafe typedBlock

      -- Унифицируем тип результата
      scopeUnified <- unifyTypes finalScope blockTyp retTyp
      trace ("retTyp before zonk: " <> show retTyp) $ pure ()
      -- debugPrintType "retTyp before zonk" retTyp
      -- debugPrintType "retTyp zonked" =<< applySubst scopeUnified retTyp
      applyTypeSubst scopeUnified retTyp >>= \r ->
        trace ("retTyp zonked: " <> show r) $ pure ()

      -- Унифицируем эффекты
      let actualFxs = blockFxs
          expectedFxs = fromMaybe (RClosed []) retFxs
      scopeUnified' <- subsumesEffRow scopeUnified actualFxs expectedFxs

      -- Строим полный тип функции и обобщаем его
      let finalArgTypes = map snd functDecl.fArgs
          finalRetFxs = retFxs  -- уже унифицирован с actualFxs
          finalRetTyp = retTyp
          fullTypFinal = buildCurried finalArgTypes finalRetFxs finalRetTyp

      -- Применяем все подстановки
      fullTypFinal' <- applyTypeSubst scopeUnified' fullTypFinal

      -- Собираем все свободные переменные (улучшенные функции должны игнорировать связанные)
      let implicitTvars = collectTvarsFromType (map (`Bound` 0) functDecl.fTvars) fullTypFinal'
          implicitEvars = collectEvarsFromType (map (`Bound` 0) functDecl.fEvars) fullTypFinal'
          implicitRvars = collectRvarsFromType (map (`Bound` 0) functDecl.fRvars) fullTypFinal'

      -- Объединяем с явными, убираем дубликаты (uniqPreserveOrder уже работает по идентификатору)
          tvars = uniqPreserveOrder $ map (`Bound` 0) functDecl.fTvars <> implicitTvars
          evars = uniqPreserveOrder $ map (`Bound` 0) functDecl.fEvars <> implicitEvars
          rvars = uniqPreserveOrder $ map (`Bound` 0) functDecl.fRvars <> implicitRvars

          finalScheme = Scheme tvars evars rvars fullTypFinal'

      -- Обновляем привязку функции в scope1
          updatedValues = Map.insert functDecl.fName (finalScheme, XVar functDecl.fName, Val) (values scope1)
          typedFunctDecl = TypedIR.FunctDecl
            functDecl.fName
            functDecl.fTvars
            functDecl.fEvars
            functDecl.fArgs
            (retFxs, retTyp)
            typedBlock

      pure (scope1 {values = updatedValues}, acc <> [TypedIR.SFunctDef typedFunctDecl])
    ) (scope1, []) funSigs

  -- Собираем остальные топ-левел статы
  otherStats <- forM chunk $ \case
    Types.STypeDef name params typ -> pure $ Just $ TypedIR.STypeDef name params typ
    Types.SEffDef effDef -> pure $ Just $ TypedIR.SEffDef effDef
    Types.SRowDef rowDef -> pure $ Just $ TypedIR.SRowDef rowDef
    Types.SFunctDef _ -> pure Nothing

  pure $ catMaybes (otherStats <> map Just typedFuns)

wrapTypedExprWithCell :: TypedExpr -> EffRow -> EffRow
wrapTypedExprWithCell e r =
  if createsCell e then Eff.appendEff r $ EffCons $ ECons "Cell" [] else r

wrapInferResultWithCell :: InferResult TypedExpr -> InferM TypedExpr
wrapInferResultWithCell (InferResult res fxs scope) =
  pure $ InferResult res (wrapTypedExprWithCell res fxs) scope

inferExpr :: Scope -> Expr -> InferM TypedExpr
inferExpr scope expr = withErrorStack (EFIr $ IrFrame (pretty expr) Nothing) $ case expr of
  Int i -> pure $ InferResult (TEInt i) Eff.empty scope
  Float f -> pure $ InferResult (TEFloat f) Eff.empty scope
  Boolean b -> pure  $ InferResult (TEBoolean b) Eff.empty scope
  String s -> pure  $ InferResult (TEString s) Eff.empty scope
  Nil -> pure  $ InferResult TENil Eff.empty scope
  XVar v -> do
    (bindingT, scope', mut) <- case Scope.findBinding True scope v of
      Nothing -> throwTypeCheckError $ UndefinedVariable v
      Just (scheme, _, mut') -> do
        (t, sc) <- instantiateTypeScheme scope scheme
        pure (t, sc, mut')
    let finalFxs = if mut == Var then Eff.closedOfFlat "Read" else Eff.empty
    pure  $ InferResult (TEXVar v bindingT) finalFxs scope'
  Array [] -> pure $ InferResult (TEArray TNothing []) Eff.empty scope
  Array (x:xs) -> do
    -- Типизируем первый элемент
    InferResult hEntry fxs scope1 <- inferExpr scope x
    hType <- typeOfTypedExprUnsafe hEntry

    -- Типизируем остальные элементы и одновременно унифицируем типы
    (typedEntries, finalFxs, finalScope) <- foldM
      (\(accEntries, accFxs, sc) ae -> do
        InferResult tEntry tFxs sc' <- inferExpr sc ae
        tEntryTyp <- typeOfTypedExprUnsafe tEntry
        sc'' <- unifyTypes sc' hType tEntryTyp
        pure (accEntries <> [tEntry], Eff.unionEffRows accFxs tFxs, sc''))
      ([hEntry], fxs, scope1)
      xs
    wrapInferResultWithCell $ InferResult (TEArray hType typedEntries) finalFxs finalScope
  Pair l r -> do
    InferResult l' lRow scope' <- inferExpr scope l
    InferResult r' rRow scope'' <- inferExpr scope' r
    let pair = TEPair l' r'
    pure $
      InferResult
        pair
        (wrapTypedExprWithCell pair $ Eff.unionEffRows lRow rRow)
        scope''
  XLambda lam -> do
    InferResult lam' fxs scope' <- inferLambda scope lam
    wrapInferResultWithCell $ InferResult (TEXLambda lam') fxs scope'
  Apply callee arg -> do
    InferResult calleeT calleeFxs calleeScope <- inferExpr scope callee
    calleeT' <- typeOfTypedExprUnsafe calleeT
    expectedFromT <- freshMetaTypeM
    expectedToT <- freshMetaTypeM
    expectedCalleeT <- TFunct . Funct expectedFromT expectedToT . ROpen [] <$> freshMetaM
    scope' <- unifyTypes calleeScope calleeT' expectedCalleeT
    InferResult argT argFxs argScope <- inferExpr scope' arg
    argT' <- typeOfTypedExprUnsafe argT
    scope'' <- unifyTypes argScope argT' expectedFromT

    -- Эффект вызова (T-App): латентный ряд callee ПОСЛЕ унификации
    resultRow <- case expectedCalleeT of
      TFunct (Funct _ _ row) -> applyEffRowSubst scope'' row
      _ -> throwTypeCheckError $ TypeError "Apply: callee must be a function"

    -- Объединяем все эффекты: вычисление callee, вычисление arg, и эффект из типа функции
    let finalFxs = Eff.unionEffRowsList [argFxs, resultRow, calleeFxs]

    wrapInferResultWithCell $ InferResult (TEApply calleeT argT) finalFxs scope''
  NLambda n@(NativeLambdaSign{}) -> wrapInferResultWithCell $
    InferResult
      (TENLambda n)
      Eff.empty
      scope
  With expr ts es rs -> do
    InferResult exprExpr exprFxs exprScope <- inferExpr scope expr
    typeOfTypedExprUnsafe exprExpr >>= \case
      TForall tvars evars rvars _ -> do
        let typesLength = length ts
            tvarsLength = length tvars
            fxsLength = length es
            evarsLength = length evars
            rowsLength = length rs
            rvarsLength = length rvars

        when (typesLength /= tvarsLength) $
          throwTypeCheckError $ TypeError $ T.pack $
            printf "Wrong type args amount in with: expected %d, given %d" tvarsLength typesLength

        when (fxsLength /= evarsLength) $
          throwTypeCheckError $ TypeError $ T.pack $
            printf "Wrong effect args amount in with: expected %d, given %d" evarsLength fxsLength

        when (rowsLength /= rvarsLength) $
          throwTypeCheckError $ TypeError $ T.pack $
            printf "Wrong row args amount in with: expected %d, given %d" rvarsLength rowsLength

        -- Создаём новый scope для подстановок
        let scope1 = enterScope exprScope
        -- Применяем подстановки типов
            scope2 = foldl (\sc (tvar, typArg) -> substituteType sc tvar typArg) scope1 (zip tvars ts)
        -- Применяем подстановки эффектов
            scope3 = foldl (\sc (evar, fxArg) -> substituteEffCons sc evar fxArg) scope2 (zip evars es)
        -- Применяем подстановки рядов
            scope4 = foldl (\sc (evar, rowArg) -> substituteEffRow sc evar rowArg) scope3 (zip rvars rs)
        exprExpr' <- substituteTypedExpr scope4 exprExpr
        -- Вычисляем результирующие эффекты (из выражения после подстановок)
        row <- applyEffRowSubst scope4 exprFxs
        -- Возвращаем TEWith с исходным выражением, но тип результата — instantiatedTyp
        wrapInferResultWithCell $ InferResult exprExpr' row scope4

      t -> throwTypeCheckError $ TypeError $ T.concat
        ["with: expression type `", T.pack $ show t, "` is not forall"]
  Handle handler -> inferHandler scope handler
  Record a ps -> inferRecord scope a ps
  Paren b -> do
    InferResult b' fxs scope' <- inferBlock scope b
    wrapInferResultWithCell $ InferResult (TypedIR.TEParen b') fxs scope'
  Resume expr ->
    case Scope.findBinding True scope "resume" of
      Nothing -> throwTypeCheckError $ EffectError "Resume used outside of a handler clause!"
      Just (resumeTypScheme, _, _) -> do
        (resumeTyp, scope') <- instantiateTypeScheme scope resumeTypScheme
        case resumeTyp of
          TFunct (Funct expectedI expectedO expectedFxs) -> do
            InferResult argExpr argFxs argScope <- inferExpr scope' expr
            argT <- typeOfTypedExprUnsafe argExpr
            scope'' <- unifyTypes argScope argT expectedI
            wrapInferResultWithCell $
              InferResult
                (TEResume argExpr expectedO)
                (Eff.unionEffRows argFxs expectedFxs)
                scope''
          _ -> throwTypeCheckError $ EffectError "Invalid resume binding: not a function"
  Let lp wht whr -> do
    (lpT, scope1) <- inferLetPattern scope lp
    InferResult whtT whtFxs scope2 <- inferExpr scope1 wht
    whT' <- typeOfTypedExprUnsafe whtT
    scope3 <- unifyTypes scope2 lpT whT'
    InferResult whrT whrFxs scope4 <- inferExpr scope3 whr
    wrapInferResultWithCell $
      InferResult
        (TypedIR.TELet lp whtT whrT)
        (Eff.unionEffRows whtFxs whrFxs)
        scope4
  PropAccess e n -> do
    InferResult t fxs scope' <- inferExpr scope e
    -- T-Prop: чтение изменяемого поля (var) даёт Read
    let readIf m = if m == Var then Eff.closedOfFlat "Read" else Eff.empty
    case t of
      TERecord _ props ->
        case find (\(TERecordProp _ n' _ _) -> n == n') props of
          Just (TERecordProp mutP _ _ e') ->
            wrapInferResultWithCell $ InferResult e' (Eff.unionEffRows fxs (readIf mutP)) scope'
          Nothing -> throwTypeCheckError $ TypeError $ "Record doesn't have binding '" <> n <> "'"
      _ -> do
        recT <- typeOfTypedExprUnsafe t
        case recT of
          TRecord rprops ->
            case find ((n ==) . tName) rprops of
              Just rp ->
                wrapInferResultWithCell $
                  InferResult (TEPropAccess t n) (Eff.unionEffRows fxs (readIf (tMut rp))) scope'
              Nothing -> throwTypeCheckError $ TypeError $ "Record doesn't have binding '" <> n <> "'"
          _ ->
            throwTypeCheckError $ TypeError $ T.pack
            $ printf "Cannot access property '%s' of expression: expected record, got: %s" n $ pretty recT
  IfElse p t f -> do
    InferResult typP pFxs pScope <- inferExpr scope p
    typP' <- typeOfTypedExprUnsafe typP
    scope' <- unifyTypes pScope TBoolean typP'
    InferResult typT tFxs tScope <- inferExpr scope' t
    InferResult typF fFxs fScope <- inferExpr tScope f
    typT' <- typeOfTypedExprUnsafe typT
    typF' <- typeOfTypedExprUnsafe typF
    iScope <- unifyTypes fScope typT' typF'
    wrapInferResultWithCell $ InferResult
      (TEIfElse typP typT typF)
      (Eff.unionEffRows pFxs $ Eff.unionEffRows tFxs fFxs)
      iScope

inferLetPattern :: Scope -> LetPattern -> TypeCheckM (Typ, Scope)
inferLetPattern scope = \case
  LPATom a ->
    case a of
      ALPNil -> pure (TNil, scope)
      ALPUnderscore -> (, scope) <$> freshMetaTypeM
      ALPPair l r -> do
        (l', scope') <- inferLetPattern scope l
        (r', scope'') <- inferLetPattern scope' r
        pure (TPair l' r', scope'')
      ALPRecord props -> do
        mapFst TRecord <$> foldM go ([], scope) props
        where
          go :: ([TRecordProp], Scope) -> LetPatternRecordProp -> TypeCheckM ([TRecordProp], Scope)
          go (accProps, scope') (LetPatternRecordProp m (LambdaParam n t) alp) = do
            t' <- maybe freshMetaTypeM pure t
            let props' = accProps <> [TRecordProp m n t']
            let scope'' = case alp of
                  Just a' -> do
                    (t'', scope''') <- inferLetPattern scope' $ LPATom a'
                    unifyTypes scope''' t' t''
                  _ -> pure scope'
            (props', ) <$> scope''

  LPParam (LambdaParam _ t) -> (, scope) <$> maybe freshMetaTypeM pure t

inferRecord :: Scope -> Maybe Expr -> [ERecordProp] -> InferM TypedExpr
inferRecord scope Nothing props = withNewLevel $ do
  (recProps, finalFxs, finalScope) <- foldM
    (\(accProps, accFxs, sc) (ERecordProp mut name typOpt expr) -> do
      InferResult exprT exprFxs sc' <- inferExpr sc expr
      exprT' <- typeOfTypedExprUnsafe exprT
      (propT, sc'') <- case typOpt of
        Just annot -> (annot, ) <$> unifyTypes sc' exprT' annot
        Nothing -> pure (exprT', sc')
      pure (accProps <> [TERecordProp mut name propT exprT], Eff.unionEffRows accFxs exprFxs, sc'')
    ) ([], Eff.empty, scope) props
  wrapInferResultWithCell $ InferResult (TERecord Nothing recProps) finalFxs finalScope

inferRecord scope (Just anchor) props = withNewLevel $ do
  InferResult anchorExpr anchorFxs scope1 <- inferExpr scope anchor
  anchorTyp <- typeOfTypedExprUnsafe anchorExpr
  case anchorTyp of
    TRecord baseProps -> do
      -- Накапливаем TERecordProp в отдельном аккумуляторе
      (recProps, propFxs, finalScope) <- foldM
        (\(accProps, accFxs, sc) (ERecordProp mut name typOpt expr) -> do
          InferResult exprExpr exprFxs sc' <- inferExpr sc expr
          exprTyp <- typeOfTypedExprUnsafe exprExpr
          (propT, sc'') <- case typOpt of
            Just annot -> (annot,) <$> unifyTypes sc' exprTyp annot
            Nothing -> pure (exprTyp, sc')
          -- Проверяем мутабельность и существование поля в скоупе
          case find ((name ==) . tName) baseProps of
            Just (TRecordProp baseMut _ _) ->
              if baseMut /= mut then
                throwTypeCheckError $ TypeError $ T.pack
                $ printf "Cannot change mutability of field '%s' from %s to %s" name baseMut mut
              else do
                -- Удаляем старое TERecordProp с таким же именем, если есть
                let accProps' = filter (\(TERecordProp _ n _ _) -> n /= name) accProps
                pure (
                    accProps' <> [TERecordProp mut name propT exprExpr],
                    Eff.unionEffRows accFxs exprFxs,
                    sc''
                  )
            Nothing ->
              -- Новое поле
              pure (accProps <> [TERecordProp mut name propT exprExpr], Eff.unionEffRows accFxs exprFxs, sc'')
        ) ([], anchorFxs, scope1) props
      wrapInferResultWithCell $ InferResult (TERecord (Just anchorExpr) recProps) propFxs finalScope
    _ -> throwTypeCheckError $ TypeError "Record anchor must be a record type"

inferHandler :: Scope -> Types.Handler -> InferM TypedExpr
inferHandler scope handler = withNewLevel $
  -- 1. Получаем сигнатуру эффекта
  case handlerCons handler of
    EVar v -> throwTypeCheckError $ TypeError $ T.concat ["Cannot use effect variable `", tasteName v, "` as handler cons"]
    eff@(EffCons eff'@(ECons n _)) -> do
      ops <- case Scope.findEffOps True scope n of
        Nothing -> throwTypeCheckError $ TypeError $ "Effect '" <> n <> "' is not presented in this scope"
        Just ops -> pure ops
      let opNames = map fst ops
      -- 2. Создаём подскоуп с операциями
      let blockScope = enterScope scope
      scope' <- foldM (\sc (name, typ) -> do
        opT <- generalize sc $ TFunct typ
        Scope.addBinding name opT (XVar name) Val sc) blockScope ops
      -- 3. Теперь можно типизировать сам блок — операции видимы
      (blockStatements, blockExpr, blockFxs, blockScope') <-
        case handler of
          Types.Handler _ block _ _ -> do
            InferResult (stats, expr) fxs sc <- inferBlock scope' block
            pure (stats, expr, fxs, sc)
      blockT' <- typeOfTypedExprUnsafe blockExpr
      -- 4. Далее всё как прежде — проверяем и типизируем handler clauses
      let handlerRow = Unify.removeConsFromRow eff blockFxs
      case handler of
        Types.Handler _ _ clauses _then -> do
          let uniqueClauses = sort $ nub clauses
          if length clauses /= length uniqueClauses then
            throwTypeCheckError $ TypeError "Duplicate handler clause names"
          else do
            let clauseNames = map fst uniqueClauses
                missing = filter (`notElem` clauseNames) opNames
                extra = filter (`notElem` opNames) clauseNames

            when (missing /= []) $ throwTypeCheckError $ TypeError $ "Handler missing operations: " <> T.intercalate ", " missing
            when (extra /= []) $ throwTypeCheckError $ TypeError $ "Handler defines unknown operations: " <> T.intercalate ", " extra
            (typedClauses, finalScope) <-
                  foldM
                    (\(acc, sc) ((name, opTyp), (_, lam)) -> do
                      -- opTyp = тип операции, например Int -> Int -> Int
                      -- Разворачиваем его до формы TFunct $ Funct args ret fxs
                      let opTyp' = TFunct opTyp
                          replaceRetWithBlockT :: Scope -> Typ -> TypeCheckM (Typ, Scope)
                          replaceRetWithBlockT sc' typ = do
                              case typ of
                                TFunct (Funct i o fxs) -> do
                                  (o', sc''') <- replaceRetWithBlockT sc' o
                                  pure (TFunct $ Funct i o' fxs, sc''')
                                _ -> pure (blockT', sc')
                      (opTypForClause, opScopeForClause) <- replaceRetWithBlockT sc opTyp'

                      case countResumeInLambda lam of
                        MultipleResume m -> throwTypeCheckError $ MultipleResumeError name m
                        OneResume -> do
                          -- Добавляем resume: retT -> blockT
                          let clauseScope = enterScope opScopeForClause
                          sc1 <- Scope.addHandler (HandlerSig eff ops) clauseScope
                          r' <- case retTypeOf opTyp' of
                            Just r -> pure r
                            Nothing -> throwTypeCheckError $ TypeError "Cannot happen"
                          t <- generalize sc1 $ TFunct $ Funct r' blockT' handlerRow
                          sc2 <- Scope.addBinding "resume" t (XVar "resume") Val sc1

                          -- Теперь типизируем лямбду, где resume уже известен
                          InferResult typedLambda lamFxs sc3 <- inferLambda sc2 lam
                          let lamFunct = Funct typedLambda.lArgT typedLambda.lRetT typedLambda.lFxs
                          let lamTyp = TFunct lamFunct
                          -- Проверяем, что лямбда совместима с типом операции
                          sc4 <- unifyTypes sc3 lamTyp opTypForClause
                          (acc <> [(name, typedLambda, OneResume, countArgs lamFunct)], ) <$> unifyEffRows sc4 lamFxs handlerRow
                        NoResume -> do
                          -- Добавляем resume: ret_t -> block_t
                          let clauseScope = enterScope opScopeForClause
                          InferResult typedLam lamFxs sc1 <- inferLambda clauseScope lam
                          let lamFunct = Funct typedLam.lArgT typedLam.lRetT typedLam.lFxs
                          let lamTyp = TFunct lamFunct

                          -- Проверяем, что лямбда совместима с типом операции
                          sc2 <- unifyTypes sc1 lamTyp opTypForClause
                          (acc <> [(name, typedLam, NoResume, countArgs lamFunct)], ) <$> unifyEffRows sc2 lamFxs handlerRow
                    )
                    ([], blockScope')
                    $ zip ops uniqueClauses

            -- Типизируем then (реальную лямбду из AST)
            InferResult typedThen thenFxs thenScope <- inferLambda finalScope _then
            let finalHandlerRow = Eff.unionEffRows handlerRow thenFxs
                typedHandler = TypedIR.Handler eff' (blockStatements, blockExpr) typedClauses typedThen
            wrapInferResultWithCell $ InferResult
              (TypedIR.TEHandle typedHandler blockT')
              finalHandlerRow
              thenScope

inferLambda :: Scope -> Types.Lambda -> InferM TypedIR.Lambda
inferLambda scope lam = withNewLevel $ do
  let scope1 = enterScope scope
  argT' <- maybe freshMetaTypeM pure lam.lArgT
  scope2 <- Scope.addBinding lam.lArg (Scheme [] [] [] argT') (XVar lam.lArg) Val scope1
  retT' <- maybe freshMetaTypeM pure lam.lRetT
  InferResult blockT blockFxs scope3 <- inferBlock scope2 lam.lBlock
  blockT' <- typeOfTypedBlockUnsafe blockT
  scope4 <- unifyTypes scope3 retT' blockT'

  rowFxs <- if lam.lFxs == RClosed [] then ROpen [] <$> freshMetaM else pure lam.lFxs

  -- Сначала унифицируем эффекты лямбды с эффектами тела
  _ <- trace ("lam.lFxs: " <> show lam.lFxs) $ pure ()
  _ <- trace ("blockFxs: " <> show blockFxs) $ pure ()
  _ <- trace ("rowFxs: " <> show rowFxs) $ pure ()

  -- Затем применяем подстановки
  scope5 <- unifyEffRows scope4 rowFxs blockFxs
  fxs'' <- applyEffRowSubst scope5 rowFxs

  argT'' <- applyTypeSubst scope5 argT'
  retT'' <- applyTypeSubst scope5 retT'

  pure $ InferResult
    (TypedIR.Lambda
      lam.lTvars
      lam.lEvars
      lam.lArg
      argT''
      retT''
      fxs''
      blockT)
    Eff.empty
    -- модель: лямбда открывает область, выход из неё сохраняет только подстановки
    (Scope.keepSubst scope5 scope)

instantiateTypeScheme :: Scope -> TypeScheme -> TypeCheckM (Typ, Scope)
instantiateTypeScheme scope (Scheme tvars evars rvars typ) = do
  freshTypes <- mapM (const freshMetaM) tvars
  freshEffects <- mapM (const freshMetaM) evars
  freshRows <- mapM (const freshMetaM) rvars

  let typeMapping = Map.fromList [(tv, TVar mv) | (tv, mv) <- zip tvars freshTypes]
      effMapping = Map.fromList [(ev, EVar mv) | (ev, mv) <- zip evars freshEffects]
      rowMapping = Map.fromList [(rv, RVar mv) | (rv, mv) <- zip rvars freshRows]
      scope' = scope {
    typeSubst = Map.union typeMapping scope.typeSubst,
    effSubst = Map.union effMapping scope.effSubst,
    rowSubst = Map.union rowMapping scope.rowSubst
  }

  (, scope') <$> applyTypeSubst scope' typ

inferBlock :: Scope -> Types.Block -> InferM TypedIR.Block
inferBlock outer (stats, expr) = withNewLevel $ do
  -- модель (E-Block): блок открывает область видимости;
  -- привязки блока не видны снаружи, подстановки сохраняются
  let scope = enterScope outer
  (scopeAfterStats, statFxs, stats') <- foldM (\(sc, accFxs, accStats) stat -> do
      InferResult stat' fxs sc' <- inferStat sc stat
      pure (sc', Eff.unionEffRows accFxs fxs, accStats <> [stat'])
    ) (scope, Eff.empty, []) stats
  InferResult exprT exprFxs scope' <- inferExpr scopeAfterStats expr
  pure $ InferResult (stats', exprT) (Eff.unionEffRows statFxs exprFxs) (Scope.keepSubst scope' outer)

inferStat :: Scope -> Types.Stat -> InferM TypedIR.Stat
inferStat scope = \case
  Types.Expr e -> do
    InferResult e' fxs scope' <- inferExpr scope e
    _ <- trace (T.unpack $ T.concat [
          "inferStat | Expr type: ", pretty $ typeOfTypedExpr e', "; expr = ", pretty e'
        ]) (pure ())
    pure $ InferResult
      (TypedIR.Expr e')
      (trace ("inferStat | Expr fxs: " <> T.unpack (pretty fxs)) fxs)
      scope'
  Types.Bind m n typOpt e -> do
    when (Scope.hasBinding False scope n) $ throwTypeCheckError $ SameScopeBindingShadowing n
    --  1. Infer expr
    InferResult inferredTypedExpr inferredFxs scope1 <- inferExpr scope e
    inferredTyp <- typeOfTypedExprUnsafe inferredTypedExpr

    -- Определяем замороженные версии, если нужно
    (exprForBinding, typForBinding, fxsForBinding) <-
      case m of
        Imm -> do
          let frozenExpr = freeze inferredTypedExpr
          frozenTyp <- typeOfTypedExprUnsafe frozenExpr
          -- Удаляем эффекты Read, Var, Rebind, Cell
          let removedFxs = foldl (flip removeConsFromRow) inferredFxs $
                map Eff.label ["Read", "Var", "Rebind", "Cell"]
          pure (frozenExpr, frozenTyp, removedFxs)
        _ -> pure (inferredTypedExpr, inferredTyp, inferredFxs)

    -- 2. Handle annotation (используем typForBinding)
    (expectedTyp, schemeForScope, scope2) <- case typOpt of
      Just anno -> do
        let scheme = Scheme [] [] [] anno
        (annoInst, scope2) <- instantiateTypeScheme scope1 scheme
        scope3 <- unifyTypes scope2 typForBinding annoInst
        (annoInst, , scope3) <$> generalize scope3 anno
      _ -> do
        typForBinding' <- applyTypeSubst scope1 typForBinding
        pure (typForBinding', Scheme [] [] [] typForBinding', scope1)

    -- 3. Unification
    scope3 <- if isNothing typOpt
      then unifyTypes scope2 typForBinding expectedTyp
      else pure scope2

    -- 4. Generalize (только для val/imm)
    finalScheme <- if m /= Var
      then generalize scope3 schemeForScope._a
      else pure schemeForScope

    -- 5. Добавляем биндинг в Scope с исходным нетипизированным выражением
    --    (для использования в выводе типов, но тип уже есть в finalScheme)
    scope4 <- Scope.addBinding n finalScheme (XVar n) m scope3

    -- 6. Финальные эффекты
    let finalFxs = if m == Var then
          Eff.unionEffRows fxsForBinding $ Eff.closedOfFlat "Var"
        else fxsForBinding

    -- 7. Возвращаем типизированный биндинг с замороженным выражением (для Imm) или исходным
    pure $ InferResult (TypedIR.Bind m n exprForBinding) finalFxs scope4
  Types.Assign n e -> do
    (scheme, _, mut) <- case Scope.findBinding True scope n of
      Nothing -> throwTypeCheckError $ UndefinedVariable n
      Just found -> pure found
    when (mut /= Var) $ throwTypeCheckError $ ImmutableVariableAssignment n
    (varT, scope') <- instantiateTypeScheme scope scheme
    InferResult eT eFxs scope'' <- inferExpr scope' e
    let finalFxs = Eff.unionEffRows eFxs $ Eff.closedOfFlat "Rebind"
    eT' <- typeOfTypedExprUnsafe eT
    InferResult (TypedIR.Rebind n eT) finalFxs <$> unifyTypes scope'' varT eT'

generalize :: Scope -> Typ -> TypeCheckM TypeScheme
generalize scope typ = do
  currentLevel' <- use currentLevel
  let isGeneralizable (Meta _ _ lvl) = lvl > currentLevel' || lvl == -1
      isGeneralizable _ = False

      allTvars = filter (`Map.notMember` scope.typeSubst) $ collectTvarsFromType [] typ
      allEvars = filter (`Map.notMember` scope.effSubst) $ collectEvarsFromType [] typ
      allRvars = filter (`Map.notMember` scope.rowSubst) $ collectRvarsFromType [] typ

      tvars = filter isGeneralizable allTvars
      evars = filter isGeneralizable allEvars
      rvars = filter isGeneralizable allRvars

      -- Проверка: если есть необобщаемые переменные, они должны остаться в типе
      -- (они будут связаны внешним forall или будут ошибкой)
      nonGeneralizableTvars = filter (not . isGeneralizable) allTvars
      nonGeneralizableEvars = filter (not . isGeneralizable) allEvars
      nonGeneralizableRvars = filter (not . isGeneralizable) allRvars

  -- Опционально: предупреждение или ошибка о необобщаемых переменных
  when (any (/= []) [nonGeneralizableTvars, nonGeneralizableEvars, nonGeneralizableRvars]) $
    throwTypeCheckError $ TypeError $
      "Cannot generalize: " <> T.pack (show (nonGeneralizableTvars, nonGeneralizableEvars, nonGeneralizableRvars))

  typ' <- applyTypeSubst scope typ
  pure $ Scheme tvars evars rvars typ'

collectTvarsFromType :: [Taste] -> Typ -> [Taste]
collectTvarsFromType except typ =
  uniqPreserveOrder $ case typ of
    TArray t -> collectTvarsFromType except t
    TPair l r -> collectTvarsFromType except l <> collectTvarsFromType except r
    TFunct (Funct i o fxs) ->
      collectTvarsFromType except i
      <> collectTvarsFromType except o
      <> collectTvarsFromEffRow except fxs
    TForall vars _ _ t -> collectTvarsFromType (uniqPreserveOrder $ vars <> except) t
    TRecord props ->
      concatMap (collectTvarsFromType except . tTyp) props
    TVar v -> ([v | v `notElem` except])
    _ -> []

collectTvarsFromTypeArg :: [Taste] -> TypeArg -> [Taste]
collectTvarsFromTypeArg except typ =
  uniqPreserveOrder $ case typ of
    TAArray t -> collectTvarsFromTypeArg except t
    TAPair l r -> collectTvarsFromTypeArg except l <> collectTvarsFromTypeArg except r
    TAFunct i o -> collectTvarsFromTypeArg except i <> collectTvarsFromTypeArg except o
    TARecord props -> concatMap (collectTvarsFromTypeArg except . taTypeArg) props
    TAVar v -> ([v | v `notElem` except])
    _ -> []

collectTvarsFromEffRow :: [Taste] -> EffRow -> [Taste]
collectTvarsFromEffRow except fx =
  uniqPreserveOrder $ case fx of
    RVar _ -> []
    RClosed cons -> concatMap (collectTvarsFromEffCons except) cons
    ROpen cons _ -> concatMap (collectTvarsFromEffCons except) cons

collectTvarsFromEffCons :: [Taste] -> EffCons -> [Taste]
collectTvarsFromEffCons except e =
  uniqPreserveOrder $ case e of
    EffCons (ECons _ ts) -> concatMap (collectTvarsFromTypeArg except) ts
    EVar _ -> []

collectEvarsFromType :: [Taste] -> Typ -> [Taste]
collectEvarsFromType except typ =
  uniqPreserveOrder $ case typ of
    TArray t -> collectEvarsFromType except t
    TPair l r -> collectEvarsFromType except l <> collectEvarsFromType except r
    TFunct (Funct i o fxs) -> collectEvarsFromType except i <> collectEvarsFromType except o <> collectEvarsFromEffRow except fxs
    TForall _ fxs _ t -> collectEvarsFromType (uniqPreserveOrder $ fxs <> except) t
    TRecord props -> concatMap (collectEvarsFromType except . tTyp) props
    _ -> []

collectEvarsFromEffRow :: [Taste] -> EffRow -> [Taste]
collectEvarsFromEffRow except fx =
  uniqPreserveOrder $ case fx of
    RVar _ -> []
    RClosed cons -> concatMap (collectEvarsFromEffCons except) cons
    ROpen cons _ -> concatMap (collectEvarsFromEffCons except) cons

collectEvarsFromEffCons :: [Taste] -> EffCons -> [Taste]
collectEvarsFromEffCons except e =
  uniqPreserveOrder $ case e of
    EVar t -> [t | t `notElem` except]
    EffCons _ -> []

collectRvarsFromType :: [Taste] -> Typ -> [Taste]
collectRvarsFromType except typ =
  uniqPreserveOrder $ case typ of
    TArray t -> collectRvarsFromType except t
    TPair l r -> collectRvarsFromType except l <> collectRvarsFromType except r
    TFunct (Funct i o fxs) ->
      concatMap (collectRvarsFromType except) [i, o] <>
      collectRvarsFromEffRow except fxs
    TForall _ _ rows t -> collectRvarsFromType (uniqPreserveOrder $ rows <> except) t
    TRecord props -> concatMap (collectRvarsFromType except . tTyp) props
    _ -> []

collectRvarsFromEffRow :: [Taste] -> EffRow -> [Taste]
collectRvarsFromEffRow except fx =
  uniqPreserveOrder $ case fx of
    RVar v -> [v | v `notElem` except]
    ROpen _ v -> [v | v `notElem` except]
    _ -> []

introducesLocalState :: TypedIR.Block -> Bool
introducesLocalState (stats, _) = any (\case TypedIR.Bind Var _ _ -> True; _ -> False) stats

createsCell :: TypedExpr -> Bool
createsCell = \case
  TEParen b -> introducesLocalState b
  TEArray _ es -> any createsCell es
  TEPair l r -> createsCell l || createsCell r
  TEXLambda lam -> introducesLocalState lam.lBlock
  TERecord me props ->
    maybe False createsCell me ||
    any (\(TERecordProp m _ _ e) -> m == Var || createsCell e) props
  TEHandle h _ -> handlerCreatesCell h
  TEResume e _ -> createsCell e
  TELet _ wht whr -> any createsCell [wht, whr]
  TEIfElse p t f -> any createsCell [p, t, f]
  TEPropAccess e _ -> createsCell e
  _ -> False

handlerCreatesCell :: TypedIR.Handler -> Bool
handlerCreatesCell = \case
  TypedIR.Handler _ block clauses mlam ->
    introducesLocalState block ||
    any (\(_, l, _, _) -> introducesLocalState l.lBlock) clauses ||
    introducesLocalState mlam.lBlock

freeze :: TypedExpr -> TypedExpr
freeze = \case
  TEArray t es -> TEArray t $ map freeze es
  TEPair l r -> TEPair (freeze l) $ freeze r
  TEXLambda l -> TEXLambda l {TypedIR.lBlock = freezeBlock l.lBlock}
  TEApply c e -> TEApply (freeze c) $ freeze e
  TERecord a ps ->
    let a' = freeze <$> a
        mapTERecordProp :: TERecordProp -> TERecordProp
        mapTERecordProp p = p {terExpr = freeze p.terExpr, terMut = freezeMutability p.terMut}
        ps' = map mapTERecordProp ps
    in
    TERecord a' ps'
  TEHandle h t -> TEHandle (freezeHandler h) t
  TEParen b -> TEParen $ freezeBlock b
  TEResume e t -> TEResume (freeze e) t
  TELet lp wht whr -> TELet lp (freeze wht) (freeze whr)
  TEPropAccess t x -> TEPropAccess (freeze t) x
  TEIfElse p t f -> TEIfElse (freeze p) (freeze t) (freeze f)
  e -> e

freezeMutability :: Mutability -> Mutability
freezeMutability = \case Var -> Val; m -> m

freezeBlock :: TypedIR.Block -> TypedIR.Block
freezeBlock (st, e) = (map freezeStat st, freeze e)

freezeStat :: TypedIR.Stat -> TypedIR.Stat
freezeStat = \case
  TypedIR.Bind m n t -> TypedIR.Bind (freezeMutability m) n $ freeze t
  TypedIR.Rebind _ t -> TypedIR.Expr $ freeze t
  TypedIR.Expr t -> TypedIR.Expr $ freeze t

freezeHandler :: TypedIR.Handler -> TypedIR.Handler
freezeHandler = \case
  TypedIR.Handler e b cs l ->
    TypedIR.Handler
      e
      (freezeBlock b)
      (map freezeHandlerClause cs)
      $ freezeLambda l

freezeHandlerClause :: TypedIR.HandlerClause -> TypedIR.HandlerClause
freezeHandlerClause (n, l, r, i) = (n, freezeLambda l, r, i)

freezeLambda :: TypedIR.Lambda -> TypedIR.Lambda
freezeLambda l = l {TypedIR.lBlock = freezeBlock l.lBlock}