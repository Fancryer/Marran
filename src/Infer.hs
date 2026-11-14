{-# LANGUAGE PatternSynonyms #-}
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
  freezeTyp,
  freezeBlock,
  freezeLambda,
  freezeRowMutIn,
  isFrozenExpr,
  isFrozenBlock,
  instantiateTypeScheme,
  generalize,
  typeOfTypedExprUnsafe,
  InferResult(..)
) where
import Types(
    Typ(..),
    Funct(Funct),
    EffRow(..),
    TypeArg(..),
    Block,
    Stat(..),
    pattern Bind, pattern Assign, pattern Expr,
    statSpan,
    Expr(..),
    blockSpan,
    pattern Int, pattern Float, pattern Boolean, pattern String, pattern Nil,
    pattern XVar, pattern Array, pattern Pair, pattern XLambda, pattern NLambda,
    pattern Apply, pattern Record, pattern With, pattern Handle, pattern Paren,
    pattern Resume, pattern Let, pattern PropAccess, pattern IfElse,
    exprSpan,
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
    LetPattern(LPParam),
    LambdaParam(LambdaParam),
    AtomLetPattern(ALPNil, ALPUnderscore, ALPPair, ALPRecord),
    LetPatternRecordProp(LetPatternRecordProp),
    Chunk,
    TopLevelStat(..),
    effName,
    FunctDecl(..),
    tfunc, ECons (..), countArgs, monoScheme, EffDef(..),
    TARecordProp(TARecordProp),
    typeArgToTyp
  )
import qualified Data.Map as Map
import qualified Data.Set as Set
import Record (taTypeArg, eExp)
import Resume (ResumeInfo(..))
import Unify (
    TypeCheckM,
    TypeCheckError(..),
    unifyTypes,
    unifyArgType,
    subsumesType,
    applyTypeSubst,
    freshMetaTypeM,
    freshMetaM,
    freshMetaRowM,
    removeConsFromRow,
    retTypeOf,
    applyEffRowSubst,
    withNewLevel,
    currentLevel, subsumesEffRow, throwTypeCheckError, throwTypeCheckErrorWithNotes, withErrorStack, applyEffConsSubst, addEffLacks, addRowLacks, addRowLacksToRow, unifyTypeArgLists
  )
import qualified Eff
import qualified Scope
import Control.Monad (foldM, when, forM)
import Scope (enterScope)
import Utils (uniqPreserveOrder, Pretty (pretty))
import qualified Data.Text as T
import Data.List (nub, find)
import Text.Printf (printf)
import Data.Maybe (isNothing, fromMaybe, catMaybes)
import TypedIR (
    Scope(..),
    ValueBinding(..),
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
    FunctDecl(..), HandlerClause,
    pattern TEInt, pattern TEFloat, pattern TEBoolean, pattern TEString,
    pattern TENil, pattern TEXVar, pattern TEArray, pattern TEPair,
    pattern TEXLambda, pattern TENLambda, pattern TEApply, pattern TERecord,
    pattern TEHandle, pattern TEParen, pattern TEResume, pattern TELet,
    pattern TEPropAccess, pattern TEIfElse,
    atTypedSpan,
    pattern Bind, pattern Rebind, pattern Expr,
    atTypedStatSpan
  )
import Data.Text (Text)
import Control.Lens (use)
import ErrorContext (IrFrame (IrFrame), ErrorFrame (..))
import Suggest (suggestionNote)
import Span (Span)
import Data.Set (Set)

data InferResult a = InferResult {
    irResult :: a,
    irRow :: EffRow,
    irScope :: Scope
  } deriving Show

type InferM a = TypeCheckM (InferResult a)

isTypeMonomorphic :: Scope -> Typ -> Bool
isTypeMonomorphic scope = \case
  TForall{} -> False
  TVar v -> maybe False (isTypeMonomorphic scope) $ Map.lookup v $ typeSubst scope
  TArray t r -> isTypeMonomorphic scope t && isEffRowMonomorphic scope r
  TPair l r fx ->
    isTypeMonomorphic scope l && isTypeMonomorphic scope r && isEffRowMonomorphic scope fx
  TFunct (Funct i o fxs) -> all (isTypeMonomorphic scope) [i, o] && isEffRowMonomorphic scope fxs
  TRecord props r ->
    all (isTypeMonomorphic scope . tTyp) props && isEffRowMonomorphic scope r
  _ -> True

isTypeArgMonomorphic :: Scope -> TypeArg -> Bool
isTypeArgMonomorphic scope = \case
  TAVar v -> maybe False (isTypeArgMonomorphic scope) $ Map.lookup v $ typeArgSubst scope
  TAArray t -> isTypeArgMonomorphic scope t
  TAPair l r -> isTypeArgMonomorphic scope l && isTypeArgMonomorphic scope r
  TAFunct i o -> isTypeArgMonomorphic scope i && isTypeArgMonomorphic scope o
  TARecord props -> all (isTypeArgMonomorphic scope . taTypeArg) props
  _ -> True

isEffConsMonomorphic :: Scope -> EffCons -> Bool
isEffConsMonomorphic scope = \case
  EVar e -> maybe False (isEffConsMonomorphic scope) $ Map.lookup e $ effSubst scope
  EffCons (ECons _ ts) -> isTypeArgMonomorphic scope `all` ts

isEffRowMonomorphic :: Scope -> EffRow -> Bool
isEffRowMonomorphic scope = \case
  RClosed cons -> isEffConsMonomorphic scope `all` cons
  ROpen cons t -> isEffConsMonomorphic scope `all` cons && isEffRowMonomorphic scope (RVar t)
  RVar _ -> True

substituteTypedExpr :: Scope -> TypedExpr -> TypeCheckM TypedExpr
substituteTypedExpr scope = \case
  TEInt i -> pure $ TEInt i
  TEFloat f -> pure $ TEFloat f
  TEBoolean b -> pure $ TEBoolean b
  TEString s -> pure $ TEString s
  TENil -> pure TENil
  TEXVar v t -> TEXVar v <$> applyTypeSubst scope t
  TEArray t r es -> do
    t' <- applyTypeSubst scope t
    r' <- applyEffRowSubst scope r
    es' <- mapM (substituteTypedExpr scope) es
    pure $ TEArray t' r' es'
  TEPair r l e -> do
    r' <- applyEffRowSubst scope r
    TEPair r' <$> substituteTypedExpr scope l <*> substituteTypedExpr scope e
  TEXLambda lam -> do
    argT' <- applyTypeSubst scope lam.lArgT
    retT' <- applyTypeSubst scope lam.lRetT
    fxs' <- applyEffRowSubst scope lam.lFxs
    block' <- substituteBlock scope lam.lBlock
    pure $ TEXLambda (lam {TypedIR.lArgT = argT', TypedIR.lRetT = retT', TypedIR.lFxs = fxs', TypedIR.lBlock = block'})
  TEApply f x -> TEApply <$> substituteTypedExpr scope f <*> substituteTypedExpr scope x
  TERecord m props r -> do
    m' <- mapM (substituteTypedExpr scope) m
    props' <- mapM (substituteRecordProp scope) props
    r' <- applyEffRowSubst scope r
    pure $ TERecord m' props' r'
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
    eff' <- applyEffConsSubst scope (EffCons eff)
    case eff' of
      EVar e -> throwTypeCheckError $
        EffectError $ "Handler cannot handle effect variable `" <> tasteName e <> "`"
      EffCons e@ECons{} -> do
        block' <- substituteBlock scope block
        clauses' <-
          mapM
            (\(name, lam, r, i) ->
              (name, , r, i) <$> substituteLambda scope lam
            )
            clauses
        then' <- substituteLambda scope mThen
        pure $ TypedIR.Handler e block' clauses' then'

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

-- | The effect declared by this name, with its parameters and operations.
--   'Scope.findEffOps' returns the operations with the effect's own type
--   parameters still in them; a use site such as @Loop[Int]@ must replace
--   those with the arguments it supplies.
effectDeclaration :: Scope -> Text -> Maybe EffDef
effectDeclaration = Scope.findEff True

-- | Replace the type parameters of an effect with the arguments of one use.
--
--   The declaration records the variables themselves, so the substitution is
--   by identity and not by name: two effects that both call a parameter @T@
--   stay apart.  The parameters also occur in the latent rows of the
--   operations (the operation performs its own effect), so rows and effect
--   constructors are rewritten too.
instantiateOps :: [Taste] -> [(Text, Funct)] -> [TypeArg] -> [(Text, Funct)]
instantiateOps params ops args
  | null params && null args = ops
  | length params /= length args = ops
  | otherwise =
      let subst = Map.fromList (zip params args)
          goArg :: TypeArg -> TypeArg
          goArg = \case
            TAVar v -> Map.findWithDefault (TAVar v) v subst
            TAArray t -> TAArray (goArg t)
            TAPair l r -> TAPair (goArg l) (goArg r)
            TAFunct i o -> TAFunct (goArg i) (goArg o)
            TARecord ps -> TARecord [TARecordProp m n (goArg t) | TARecordProp m n t <- ps]
            a -> a
          goCons :: EffCons -> EffCons
          goCons = \case
            EffCons (ECons n as) -> EffCons (ECons n (map goArg as))
            e@(EVar _) -> e
          goRow :: EffRow -> EffRow
          goRow = \case
            RClosed cs -> RClosed (map goCons cs)
            ROpen cs v -> ROpen (map goCons cs) v
            RVar v -> RVar v
          go :: Typ -> Typ
          go = \case
            TVar v -> maybe (TVar v) typeArgToTyp (Map.lookup v subst)
            TArray t r -> TArray (go t) (goRow r)
            TPair l r fx -> TPair (go l) (go r) (goRow fx)
            TFunct (Funct i o fxs) -> TFunct (Funct (go i) (go o) (goRow fxs))
            TRecord props fx -> TRecord [TRecordProp m n (go t) | TRecordProp m n t <- props] (goRow fx)
            TForall ts es rs els rls t -> TForall ts es rs els rls (go t)
            t -> t
      in [ (n, Funct (go i) (go o) (goRow fxs)) | (n, Funct i o fxs) <- ops ]

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

-- | Тип выражения с предварительной подстановкой решений унификации.
--   typeOfTypedExpr чистая и не знает подстановок: без этого вызов функции,
--   результат которой ещё метапеременная (apply + 3 2), даёт "Apply of non-function".
typeOfTypedExprIn :: Scope -> TypedExpr -> TypeCheckM Typ
typeOfTypedExprIn scope e = substituteTypedExpr scope e >>= typeOfTypedExprUnsafe

typeOfTypedBlockIn :: Scope -> TypedIR.Block -> TypeCheckM Typ
typeOfTypedBlockIn scope b = substituteBlock scope b >>= typeOfTypedBlockUnsafe

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

-- | Run a top-level declaration check with a frame naming the declaration, so
--   that an error about the declaration itself (a duplicate, say) points at
--   its line instead of having no location at all.
withDeclFrame :: Text -> Span -> TypeCheckM a -> TypeCheckM a
withDeclFrame name sp = withErrorStack (EFIr $ IrFrame name sp)

-- most important
inferChunk :: [Text] -> Types.Chunk -> TypeCheckM TypedIR.Chunk
inferChunk args chunk = do
  globalScope <- Scope.globalScope args
  -- Первый проход: регистрируем только эффекты и функции (с предварительными схемами)
  (scope1, funSigs) <- foldM (\(sc, sigs) stat -> case stat of
      Types.SEffDef sp effDef -> withDeclFrame ("effect " <> effName effDef) sp $ do
        when (Scope.hasEff False sc (effName effDef)) $
          throwTypeCheckError $ DuplicateDefinition $ "the effect `" <> effName effDef <> "` is defined twice"
        sc' <- Scope.addEffect effDef sc
        pure (sc', sigs)

      Types.SFunctDef sp functDecl -> withDeclFrame ("funct " <> functDecl.fName) sp $ do
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

        let scheme =
              Scheme tvars evars rvars Map.empty Map.empty fullTyp

        when (Scope.hasBinding False sc functDecl.fName) $
          throwTypeCheckError $ DuplicateDefinition $ "the function `" <> functDecl.fName <> "` is defined twice"

        sc' <- Scope.addBinding functDecl.fName scheme (XVar functDecl.fName) Val sc
        pure (sc', sigs <> [(functDecl, retFxs, retTyp)])

      _ -> pure (sc, sigs)
    ) (globalScope, []) chunk

  -- Второй проход: типизируем тела функций и обновляем схемы
  (_scope2, typedFuns) <- foldM (\(sc, acc) (functDecl, retFxs, retTyp) -> do
      let funScope = enterScope sc
      scopeWithArgs <- foldM (\sc' (argName, argTyp) ->
          Scope.addBinding argName (monoScheme argTyp) (XVar argName) Val sc'
        ) funScope functDecl.fArgs

      -- Errors about the signature as a whole (the body does not have the
      -- declared type, or performs effects the row does not allow) belong to
      -- the function, so they get a frame of their own.
      let bodySpan = blockSpan functDecl.fBlock
          funFrame = EFIr $ IrFrame ("funct " <> functDecl.fName) bodySpan

      (typedBlock, scopeUnified') <-
        withErrorStack funFrame $ do
          InferResult typedBlock blockFxs finalScope <- inferBlock scopeWithArgs functDecl.fBlock
          blockTyp <- typeOfTypedBlockIn finalScope typedBlock

          -- Унифицируем тип результата.  The annotation of an aggregate is an
          -- upper bound, so a value with a smaller pending row fits.
          scopeUnified <- subsumesType finalScope blockTyp retTyp

          -- Унифицируем эффекты
          let actualFxs = blockFxs
              expectedFxs = fromMaybe (RClosed []) retFxs
          scopeUnified' <- subsumesEffRow scopeUnified actualFxs expectedFxs

          pure (typedBlock, scopeUnified')

      -- Строим окончательный тип функции.
      -- Сначала применяем все подстановки к аргументам и результату.
      finalArgTypes <-
        mapM (applyTypeSubst scopeUnified' . snd) functDecl.fArgs

      finalRetTyp <-
        applyTypeSubst scopeUnified' retTyp

      finalRetFxs <-
        traverse (applyEffRowSubst scopeUnified') retFxs

      let fullTypFinal =
            buildCurried finalArgTypes finalRetFxs finalRetTyp

      fullTypFinal' <-
        applyTypeSubst scopeUnified' fullTypFinal

      -- Собираем свободные переменные.
      let implicitTvars = collectTvarsFromType (map (`Bound` 0) functDecl.fTvars) fullTypFinal'
          implicitEvars = collectEvarsFromType (map (`Bound` 0) functDecl.fEvars) fullTypFinal'
          implicitRvars = collectRvarsFromType (map (`Bound` 0) functDecl.fRvars) fullTypFinal'

          tvars = uniqPreserveOrder $ map (`Bound` 0) functDecl.fTvars <> implicitTvars
          evars = uniqPreserveOrder $ map (`Bound` 0) functDecl.fEvars <> implicitEvars
          rvars = uniqPreserveOrder $ map (`Bound` 0) functDecl.fRvars <> implicitRvars

          finalRowLacks = Map.filterWithKey (\k _ -> k `elem` rvars) (rowLacks scopeUnified')
          finalEffLacks = Map.filterWithKey (\k _ -> k `elem` evars) (effLacks scopeUnified')

          finalScheme =
            Scheme tvars evars rvars
              finalRowLacks
              finalEffLacks
              fullTypFinal'

          -- A function name is not a delayed computation: its latent row is
          -- paid at application, not by looking the name up.  Its pending row
          -- is therefore empty.
          updatedValues = Map.insert functDecl.fName (ValueBinding finalScheme (XVar functDecl.fName) Val Eff.empty) (values sc)

          finalArgs = zip (map fst functDecl.fArgs) finalArgTypes

          typedFunctDecl =
            TypedIR.FunctDecl
              functDecl.fName
              functDecl.fTvars
              functDecl.fEvars
              finalArgs
              (finalRetFxs, finalRetTyp)
              typedBlock

      pure (sc {values = updatedValues}, acc <> [TypedIR.SFunctDef typedFunctDecl])
    ) (scope1, []) funSigs

  -- Собираем остальные топ-левел статы
  otherStats <- forM chunk $ \case
    Types.STypeDef _ name params typ -> pure $ Just $ TypedIR.STypeDef name params typ
    Types.SEffDef _ effDef -> pure $ Just $ TypedIR.SEffDef effDef
    Types.SRowDef _ rowDef -> pure $ Just $ TypedIR.SRowDef rowDef
    Types.SFunctDef _ _ -> pure Nothing

  pure $ catMaybes (otherStats <> map Just typedFuns)

wrapTypedExprWithCell :: TypedExpr -> EffRow -> EffRow
wrapTypedExprWithCell e r =
  if createsCell e then Eff.appendEff r $ EffCons $ ECons "Cell" [] else r

wrapInferResultWithCell :: InferResult TypedExpr -> InferM TypedExpr
wrapInferResultWithCell (InferResult res fxs scope) =
  pure $ InferResult res (wrapTypedExprWithCell res fxs) scope

-- | Type-check one expression.  The resulting typed node carries the span of
--   the AST node it came from, and the frame pushed for the duration of the
--   check is the one a diagnostic will point at.
inferExpr :: Scope -> Expr -> InferM TypedExpr
inferExpr scope expr = do
  InferResult res fxs sc <- inferNode scope expr
  pure $ InferResult (atTypedSpan (exprSpan expr) res) fxs sc

inferNode :: Scope -> Expr -> InferM TypedExpr
inferNode scope expr = withErrorStack (EFIr $ IrFrame (pretty expr) (exprSpan expr)) $ case expr of
  Int i -> pure $ InferResult (TEInt i) Eff.empty scope
  Float f -> pure $ InferResult (TEFloat f) Eff.empty scope
  Boolean b -> pure  $ InferResult (TEBoolean b) Eff.empty scope
  String s -> pure  $ InferResult (TEString s) Eff.empty scope
  Nil -> pure  $ InferResult TENil Eff.empty scope
  XVar v -> do
    (bindingT, pending, scope', mut) <- case Scope.findBindingWithRow True scope v of
      Nothing -> case Scope.findOperations True scope v of
        -- An operation of a declared effect.  Using it is performing its
        -- effect, so the use charges that effect (just as reading a `var`
        -- charges `Read`); the operation's declared type says nothing about
        -- it, because `effect Doubt ask : Int -> Int` reads as "a call takes
        -- an Int and gives an Int", not as "and does nothing else".  That is
        -- what lets a function declare the effect in its row and what `under`
        -- removes from the body it handles.
        [] -> throwTypeCheckErrorWithNotes (UndefinedVariable v)
          (maybe [] pure (suggestionNote (Scope.bindingNames scope <> Scope.operationNames scope) v))
        [(eff, params, opTyp)] -> do
          let scheme = Scheme params [] [] Map.empty Map.empty (TFunct opTyp)
          (t, sc) <- instantiateTypeScheme scope scheme
          pure (t, Eff.closedOfFlat eff, sc, Val)
        candidates -> throwTypeCheckError $ InferenceError $ T.concat [
            "the operation `", v, "` is declared by more than one effect ("
          , T.intercalate ", " [ "`" <> n <> "`" | (n, _, _) <- candidates ]
          , "), so a use of it is ambiguous: name its effect in a row, or handle it"
          ]
      Just (ValueBinding scheme _ mut' row) -> do
        -- The pending row belongs to the delayed computation, so it must be
        -- instantiated together with the scheme: a @val@ binding can be
        -- polymorphic in the row of the thunk it stores.
        (t, row', sc) <- instantiateTypeSchemeWithRow scope scheme row
        pure (t, row', sc, mut')
    let finalFxs =
          if mut == Var
            then Eff.unionEffRows pending (Eff.closedOfFlat "Read")
            else pending
    pure  $ InferResult (TEXVar v bindingT) finalFxs scope'
  -- T-Array (the paper gives no separate rule; the annotation is an upper
  -- bound of the component rows, like T-Pair and T-Rec).  The row is a fresh
  -- variable so that the annotation is as permissive as possible: it is only
  -- required to bound the rows of the components and their mentions.
  Array [] -> pure $ InferResult (TEArray TNothing (RClosed []) []) Eff.empty scope
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
    -- Men(Γ,tᵢ): a snapshot of a component reaches whatever its code mentions.
    men <- mentionRow finalScope (Set.unions (map fvTyped typedEntries))
    pending <- freshMetaRowM
    finalScope' <- subsumesEffRow finalScope (Eff.unionEffRows finalFxs men) pending
    wrapInferResultWithCell $
      InferResult (TEArray hType pending typedEntries) finalFxs finalScope'
  Pair l r -> do
    InferResult l' lRow scope' <- inferExpr scope l
    InferResult r' rRow scope'' <- inferExpr scope' r
    men <- mentionRow scope'' (Set.union (fvTyped l') (fvTyped r'))
    pending <- applyEffRowSubst scope'' =<< freshMetaRowM
    scope''' <- subsumesEffRow scope'' (Eff.unionEffRows (Eff.unionEffRows lRow rRow) men) pending
    let pair = TEPair pending l' r'
    pure $
      InferResult
        pair
        (wrapTypedExprWithCell pair $ Eff.unionEffRows lRow rRow)
        scope'''
  XLambda lam -> do
    InferResult lam' fxs scope' <- inferLambda scope lam
    wrapInferResultWithCell $ InferResult (TEXLambda lam') fxs scope'
  Apply callee arg -> do
    InferResult calleeT calleeFxs calleeScope <- inferExpr scope callee
    calleeT' <- typeOfTypedExprIn calleeScope calleeT

    -- A callee whose type is already known and is not a function is an
    -- application error, not a unification error: reporting it as a failed
    -- unification would leak inference variables (`m6 -> { | `m8} `m7`) into
    -- a message about `n 2` where `n : Int`.
    calleeResolved0 <- applyTypeSubst calleeScope calleeT'
    case calleeResolved0 of
      TFunct _ -> pure ()
      TForall{} -> pure ()
      TVar{} -> pure ()
      other -> throwTypeCheckError $ ApplicationError $ T.concat [
          "`", pretty callee, "` has type `", pretty other,
          "`, which is not a function, so it cannot be applied"
        ]

    expectedFromT <- freshMetaTypeM
    expectedToT <- freshMetaTypeM
    expectedCalleeT <- TFunct . Funct expectedFromT expectedToT . ROpen [] <$> freshMetaM
    scope' <- unifyTypes calleeScope calleeT' expectedCalleeT
    -- T-App: the parameter's row names the effects the argument may perform,
    -- so their operations are in scope while the argument is checked.
    argScope0 <- withRowOperations scope' expectedFromT
    InferResult argT argFxs argScope <- inferExpr argScope0 arg
    argT' <- typeOfTypedExprIn argScope argT
    -- T-App: the argument's row must be included in the parameter's latent
    -- row, not equal to it.
    scope'' <- unifyArgType argScope argT' expectedFromT

    -- Эффект вызова (T-App): латентный ряд callee ПОСЛЕ унификации
    -- берётся собственный ряд callee (а не ожидаемый: унификация открытых рядов
    -- привязывает хвост ожидаемого к разности и теряет эффекты)
    calleeResolved <- applyTypeSubst scope'' calleeT'
    resultRow <- case calleeResolved of
      TFunct (Funct _ _ row) -> applyEffRowSubst scope'' row
      _ -> throwTypeCheckError $ ApplicationError "the left side of an application is not a function"

    -- T-App (paper): @R₂ ∪ Men(Γ,t₂) ⊆ R@.  The row of the argument is
    -- charged right here -- it is part of 'finalFxs' below -- so the call site
    -- already pays for it, and the parameter's latent row need not be widened
    -- to a bound of the *variable* the argument reads: for `line unit q`, where
    -- `unit` is a `var`, requiring `ρ_unit ∪ {Read} ⊆ {Read}` would close the
    -- variable's pending row and make the later `unit := ...` illegal.  What
    -- the callee must be able to pay for, though, is an argument it may force
    -- later, and that is exactly what 'unifyArgType' checks: if the argument is
    -- itself a delayed computation, its latent row is included in the
    -- parameter's arrow row.
    let finalFxs = Eff.unionEffRowsList [argFxs, resultRow, calleeFxs]

    wrapInferResultWithCell $ InferResult (TEApply calleeT argT) finalFxs scope''
  NLambda n@(NativeLambdaSign{}) -> wrapInferResultWithCell $
    InferResult
      (TENLambda n)
      Eff.empty
      scope
  With withExpr ts es rs -> do
    InferResult exprExpr exprFxs exprScope <- inferExpr scope withExpr

    typeOfTypedExprUnsafe exprExpr >>= \case
      TForall tvars evars rvars boundEffLacks boundRowLacks _ -> do
        let typesLength = length ts
            tvarsLength = length tvars
            fxsLength = length es
            evarsLength = length evars
            rowsLength = length rs
            rvarsLength = length rvars

        when (typesLength /= tvarsLength) $
          throwTypeCheckError $ ApplicationError $ T.pack $
            printf "`with` applied %d type argument(s) to an expression that abstracts over %d" typesLength tvarsLength

        when (fxsLength /= evarsLength) $
          throwTypeCheckError $ ApplicationError $ T.pack $
            printf "`with` applied %d effect argument(s) to an expression that abstracts over %d" fxsLength evarsLength

        when (rowsLength /= rvarsLength) $
          throwTypeCheckError $ ApplicationError $ T.pack $
            printf "`with` applied %d row argument(s) to an expression that abstracts over %d" rowsLength rvarsLength

        let scope1 = enterScope exprScope

        -- Переносим ограничения на аргументы эффектов.
        scope2 <- foldM
          (\sc (evar, fxArg) ->
            maybe (pure sc)
              (addRowLacksToRow sc (RClosed [fxArg]))
              (Map.lookup evar boundEffLacks))
          scope1
          (zip evars es)

        -- Переносим ограничения на аргументы строк эффектов.
        scope3 <- foldM
          (\sc (rvar, rowArg) ->
            maybe (pure sc)
              (addRowLacksToRow sc rowArg)
              (Map.lookup rvar boundRowLacks))
          scope2
          (zip rvars rs)

        let scope4 = foldl (\sc (tvar, typArg) -> substituteType sc tvar typArg) scope3 (zip tvars ts)
            scope5 = foldl (\sc (evar, fxArg) -> substituteEffCons sc evar fxArg) scope4 (zip evars es)
            scope6 = foldl (\sc (rvar, rowArg) -> substituteEffRow sc rvar rowArg) scope5 (zip rvars rs)

        exprExpr' <- substituteTypedExpr scope6 exprExpr
        row <- applyEffRowSubst scope6 exprFxs

        wrapInferResultWithCell $
          InferResult exprExpr' row scope6

      t -> throwTypeCheckError $ ApplicationError $ T.concat
        ["`with` needs a polymorphic expression, but this one has the type `", pretty t, "`"]
  Handle handler -> inferHandler scope handler
  Record a ps -> inferRecord scope a ps
  Paren b -> do
    InferResult b' fxs scope' <- inferBlock scope b
    wrapInferResultWithCell $ InferResult (TypedIR.TEParen b') fxs scope'
  Resume resumeExpr ->
    case Scope.findBinding True scope "resume" of
      Nothing -> throwTypeCheckError $ EffectError "Resume used outside of a handler clause!"
      Just (resumeTypScheme, _, _) -> do
        (resumeTyp, scope') <- instantiateTypeScheme scope resumeTypScheme
        case resumeTyp of
          TFunct (Funct expectedI expectedO expectedFxs) -> do
            InferResult argExpr argFxs argScope <- inferExpr scope' resumeExpr
            argT <- typeOfTypedExprUnsafe argExpr
            scope'' <- unifyTypes argScope argT expectedI
            wrapInferResultWithCell $
              InferResult
                (TEResume argExpr expectedO)
                (Eff.unionEffRows argFxs expectedFxs)
                scope''
          _ -> throwTypeCheckError $ EffectError "Invalid resume binding: not a function"
  Let lp wht whr -> do
    -- 1. Сначала типизируем RHS в исходном Scope.
    InferResult whtT whtFxs scope1 <- inferExpr scope wht
    -- 2. Получаем тип вычисленного выражения.
    whT' <- typeOfTypedExprIn scope1 whtT
    -- 3. Создаём bindings из паттерна.  Every name of the pattern is an alias
    -- of the value the right-hand side computes — the interpreter hands out
    -- its address — so forcing such a name costs the row of the right-hand
    -- side, exactly like forcing a `val` binding.  Without this a closure over
    -- a `let` name claimed `{}` while forcing it read a `var` through the
    -- alias.
    men <- mentionRow scope1 (fvTyped whtT)
    (lpT, scope2) <- inferLetPattern (Eff.unionEffRows whtFxs men) scope1 lp
    -- 4. Проверяем соответствие типа паттерна типу RHS.
    scope3 <- unifyTypes scope2 lpT whT'
    -- 5. Типизируем тело с уже доступными bindings.
    InferResult whrT whrFxs scope4 <- inferExpr scope3 whr
    wrapInferResultWithCell $
      InferResult
        (TypedIR.TELet lp whtT whrT)
        (Eff.unionEffRows whtFxs whrFxs)
        scope4
  PropAccess e n -> do
    InferResult t fxs scope' <- inferExpr scope e
    -- T-Prop: the pending row of the record is what forcing a field may do, so
    -- reading a field charges it; a `var` field additionally performs `Read`.
    let readIf m = if m == Var then Eff.closedOfFlat "Read" else Eff.empty
        withPending pending row = Eff.unionEffRows row pending
    case t of
      TERecord _ props pending ->
        case find (\(TERecordProp _ n' _ _) -> n == n') props of
          Just (TERecordProp mutP _ _ e') -> do
            pending' <- applyEffRowSubst scope' pending
            wrapInferResultWithCell $ InferResult e'
              (withPending pending' (Eff.unionEffRows fxs (readIf mutP))) scope'
          Nothing -> throwTypeCheckErrorWithNotes
            (RecordError $ "this record has no field `" <> n <> "`")
            (maybe [] pure (suggestionNote (map (\(TERecordProp _ n' _ _) -> n') props) n))
      _ -> do
        recT <- typeOfTypedExprUnsafe t
        case recT of
          TRecord rprops pending -> do
            pending' <- applyEffRowSubst scope' pending
            case find ((n ==) . tName) rprops of
              Just rp ->
                wrapInferResultWithCell $
                  InferResult (TEPropAccess t n) (withPending pending' (Eff.unionEffRows fxs (readIf (tMut rp)))) scope'
              Nothing -> throwTypeCheckErrorWithNotes
                (RecordError $ "this record has no field `" <> n <> "`")
                (maybe [] pure (suggestionNote (map tName rprops) n))
          _ ->
            throwTypeCheckError $ RecordError $ T.pack
            $ printf "cannot read the field `%s` of a value of type `%s`; only records have fields" n $ pretty recT
  IfElse p t f -> do
    InferResult typP pFxs pScope <- inferExpr scope p
    typP' <- typeOfTypedExprIn pScope typP
    scope' <- unifyTypes pScope TBoolean typP'
    InferResult typT tFxs tScope <- inferExpr scope' t
    InferResult typF fFxs fScope <- inferExpr tScope f
    typT' <- typeOfTypedExprIn fScope typT
    typF' <- typeOfTypedExprIn fScope typF
    iScope <- unifyTypes fScope typT' typF'
    wrapInferResultWithCell $ InferResult
      (TEIfElse typP typT typF)
      (Eff.unionEffRows pFxs $ Eff.unionEffRows tFxs fFxs)
      iScope

-- | Bind the names of a @let@ pattern at the type they must have.
--
--   The first argument is the pending row of the right-hand side: a @let@ name
--   is an alias of the value the right-hand side computes (the interpreter
--   binds the same address), so forcing it costs that row, just as forcing a
--   @val@ costs the row stored in its binding.
inferLetPattern :: EffRow -> Scope -> LetPattern -> TypeCheckM (Typ, Scope)
inferLetPattern row scope = \case
  LPParam (LambdaParam name t) -> do
    t' <- maybe freshMetaTypeM pure t
    scope' <- Scope.addBindingWithRow name (monoScheme t') (XVar name) Val row scope
    pure (t', scope')

  LPATom a ->
    case a of
      ALPNil -> pure (TNil, scope)
      ALPUnderscore -> (, scope) <$> freshMetaTypeM
      ALPPair l r -> do
        (l', scope') <- inferLetPattern row scope l
        (r', scope'') <- inferLetPattern row scope' r
        -- The pattern type is unified with the right-hand side, so its
        -- annotation must not force an empty row: a pair whose components
        -- read a `var` has a non-empty one.
        pending <- freshMetaRowM
        pure (TPair l' r' pending, scope'')
      ALPRecord props -> do
        (recordProps, scope') <- foldM inferProp ([], scope) props
        pending <- freshMetaRowM
        pure (TRecord recordProps pending, scope')
        where
          inferProp :: ([TRecordProp], Scope) -> LetPatternRecordProp -> TypeCheckM ([TRecordProp], Scope)
          inferProp (accProps, scope') (LetPatternRecordProp m (LambdaParam name t) alp) = do
            t' <- maybe freshMetaTypeM pure t
            -- Имя свойства становится доступным в текущем Scope.
            scope'' <- Scope.addBindingWithRow name (monoScheme t') (XVar name) m row scope'
            -- При наличии вложенного паттерна проверяем его
            -- совместимость с типом свойства.
            scope''' <-
              case alp of
                Nothing -> pure scope''
                Just nested -> do
                  (nestedT, nestedScope) <- inferLetPattern row scope'' (LPATom nested)
                  unifyTypes nestedScope t' nestedT

            pure (accProps <> [TRecordProp m name t'], scope''')

inferRecord :: Scope -> Maybe Expr -> [ERecordProp] -> InferM TypedExpr
inferRecord scope Nothing props = withNewLevel $ do
  (recProps, finalFxs, finalScope) <- foldM
    (\(accProps, accFxs, sc) (ERecordProp mut name typOpt expr) -> do
      InferResult exprT exprFxs sc' <- inferExpr sc expr
      exprT' <- typeOfTypedExprUnsafe exprT
      (propT, sc'') <- case typOpt of
        -- A field annotation may be an aggregate with its own pending row,
        -- which is an upper bound like every other annotation of an aggregate.
        Just annot -> (annot, ) <$> subsumesType sc' exprT' annot
        Nothing -> pure (exprT', sc')
      pure (accProps <> [TERecordProp mut name propT exprT], Eff.unionEffRows accFxs exprFxs, sc'')
    ) ([], Eff.empty, scope) props
  -- T-Rec: the annotation bounds the component rows and their mentions; a
  -- `var` field additionally makes the construction create a cell.
  men <- mentionRow finalScope (Set.unions (map (fvTyped . terExpr) recProps))
  pending <- freshMetaRowM
  finalScope' <- subsumesEffRow finalScope (Eff.unionEffRows finalFxs men) pending
  wrapInferResultWithCell $ InferResult (TERecord Nothing recProps pending) finalFxs finalScope'

inferRecord scope (Just anchor) props = withNewLevel $ do
  InferResult anchorExpr anchorFxs scope1 <- inferExpr scope anchor
  anchorTyp <- typeOfTypedExprUnsafe anchorExpr
  case anchorTyp of
    TRecord baseProps basePending -> do
      -- Накапливаем TERecordProp в отдельном аккумуляторе
      (recProps, propFxs, finalScope) <- foldM
        (\(accProps, accFxs, sc) (ERecordProp mut name typOpt expr) -> do
          InferResult exprExpr exprFxs sc' <- inferExpr sc expr
          exprTyp <- typeOfTypedExprUnsafe exprExpr
          (propT, sc'') <- case typOpt of
            Just annot -> (annot,) <$> subsumesType sc' exprTyp annot
            Nothing -> pure (exprTyp, sc')
          -- Проверяем мутабельность и существование поля в скоупе
          case find ((name ==) . tName) baseProps of
            Just (TRecordProp baseMut _ _) ->
              if baseMut /= mut then
                throwTypeCheckError $ RecordError $ T.pack
                $ printf "the field `%s` is %s in the record being extended, so it cannot become %s" name baseMut mut
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
      -- T-Rec: the record being built gets its own annotation; the base's
      -- pending row is a bound too, since the new record still shares the
      -- base's fields.
      men <- mentionRow finalScope (Set.unions (map (fvTyped . terExpr) recProps))
      basePending' <- applyEffRowSubst finalScope basePending
      pending <- freshMetaRowM
      finalScope' <- subsumesEffRow finalScope
        (Eff.unionEffRows (Eff.unionEffRows propFxs men) basePending') pending
      wrapInferResultWithCell $
        InferResult (TERecord (Just anchorExpr) recProps pending) propFxs finalScope'
    _ -> throwTypeCheckError $ RecordError "a record can only be built from another record, but this base is not one"

inferHandler :: Scope -> Types.Handler -> InferM TypedExpr
inferHandler scope handler = withNewLevel $
  -- 1. Получаем сигнатуру эффекта
  case handlerCons handler of
    EVar v ->
      throwTypeCheckError $
        HandlerError $
          T.concat ["`", tasteName v, "` is an effect variable, not an effect, so it cannot be handled"]
    eff@(EffCons eff'@(ECons n effArgs)) -> do
      decl@(EffDef _ params declaredOps) <- case effectDeclaration scope n of
        Nothing -> throwTypeCheckError $ HandlerError $ "there is no effect named `" <> n <> "` in scope"
        Just d -> pure d
      let ops = instantiateOps params declaredOps effArgs
      let opNames = map fst ops
      -- 2. Создаём подскоуп с операциями
      let blockScope = enterScope scope

      scope' <-
        foldM
          (\sc (name, typ) -> do
            opT <- generalize sc $ TFunct typ
            pure $ Scope.bindLocal name opT (XVar name) Val sc
          )
          blockScope
          ops

      -- 3. Типизируем блок — операции видимы
      (blockStatements, blockExpr, blockFxs, blockScope') <-
        case handler of
          Types.Handler _ block _ _ -> do
            InferResult (stats, expr) fxs sc <- inferBlock scope' block
            pure (stats, expr, fxs, sc)

      blockT' <- typeOfTypedExprUnsafe blockExpr

      -- 4. Проверяем и типизируем handler clauses
      --
      --   The row of the body is removed of the handled effect, but its
      --   occurrences are still inference variables here: a recursive call
      --   instantiates `Loop[`T]` with a fresh argument and only unification
      --   binds it back to the enclosing `T`.  Comparing the unresolved row
      --   with the handled effect would therefore miss the occurrence and leave
      --   the effect in the handler's row.
      blockFxsResolved <- applyEffRowSubst blockScope' blockFxs
      (_handlerScope, handlerRow) <- removeHandledEffect blockScope' eff blockFxsResolved

      case handler of
        Types.Handler _ _ clauses _then -> do

          -- Проверяем дубликаты по именам операций,
          -- а не по полному содержимому HandlerClause.
          let clauseNames = map fst clauses
              missing = filter (`notElem` clauseNames) opNames
              extra = filter (`notElem` opNames) clauseNames

          when (length clauseNames /= length (nub clauseNames)) $
            throwTypeCheckError $ DuplicateDefinition "the same operation is handled twice"

          when (missing /= []) $
            throwTypeCheckError $
              HandlerError $ "this handler does not handle: " <> T.intercalate ", " missing

          when (extra /= []) $
            throwTypeCheckError $
              HandlerError $ "this handler handles operations that the effect does not declare: " <> T.intercalate ", " extra

          -- Обрабатываем операции в порядке их объявления,
          -- но находим соответствующую clause по имени.
          (typedClauses, finalScope) <-
            foldM
              (\(acc, sc) (name, opTyp) ->
                case find ((== name) . fst) clauses of
                  Nothing -> throwTypeCheckError $ HandlerError $ "this handler does not handle `" <> name <> "`"

                  Just (_, lam) -> do

                    -- opTyp = тип операции, например Int -> Int -> Int
                    -- Разворачиваем его до формы TFunct $ Funct args ret fxs
                    let opTyp' = TFunct opTyp

                        replaceRetWithBlockT :: Scope -> Typ -> TypeCheckM (Typ, Scope)
                        replaceRetWithBlockT sc' typ =
                          case typ of
                            TFunct (Funct i o fxs) -> do
                              (o', sc''') <-
                                replaceRetWithBlockT sc' o

                              pure (TFunct $ Funct i o' fxs, sc''')

                            _ ->
                              pure (blockT', sc')

                    (opTypForClause, opScopeForClause) <-
                      replaceRetWithBlockT sc opTyp'

                    case countResumeInLambda lam of

                      MultipleResume m -> throwTypeCheckError $ MultipleResumeError name m

                      OneResume -> do
                        -- Добавляем resume: retT -> blockT
                        let clauseScope = enterScope opScopeForClause
                        sc1 <- Scope.addHandler (HandlerSig eff ops) clauseScope
                        r' <-
                          case retTypeOf opTyp' of
                            Just r -> pure r
                            Nothing -> throwTypeCheckError $ HandlerError "the operation type is not a function, so it has no result to resume with"

                        t <- generalize sc1 $ TFunct $ Funct r' blockT' handlerRow
                        sc2 <- Scope.addBinding "resume" t (XVar "resume") Val sc1
                        -- Типизируем lambda, где resume уже известен
                        InferResult typedLambda _lamFxs sc3 <- inferLambda sc2 lam

                        -- The clause's own row is checked below against the
                        -- row of the whole handler, not against the latent row
                        -- of the operation: a clause of `Loop` may perform
                        -- `Loop` again (a recursive call, or `break` from
                        -- inside `continue`).  A fresh row variable keeps
                        -- 'unifyTypes' from forcing the clause to be pure.
                        freeRow <- freshMetaM
                        let lamFunct = Funct typedLambda.lArgT typedLambda.lRetT (RVar freeRow)
                            lamTyp = TFunct lamFunct

                        -- Проверяем совместимость с типом операции
                        sc4 <- unifyTypes sc3 lamTyp opTypForClause

                        pure (acc <> [(name, typedLambda, OneResume, countArgs lamFunct)], sc4)

                      NoResume -> do
                        -- Типизируем lambda без resume
                        let clauseScope = enterScope opScopeForClause

                        InferResult typedLam _lamFxs sc1 <-
                          inferLambda clauseScope lam

                        freeRow <- freshMetaM
                        let lamFunct = Funct typedLam.lArgT typedLam.lRetT (RVar freeRow)
                            lamTyp = TFunct lamFunct
                        -- Проверяем совместимость с типом операции
                        sc2 <- unifyTypes sc1 lamTyp opTypForClause
                        pure (acc <> [(name, typedLam, NoResume, countArgs lamFunct)], sc2)
              )
              ([], blockScope')
              ops

          -- 5. Типизируем then
          InferResult typedThen _thenFxs thenScope0 <-
            inferLambda finalScope _then

          -- The `then` clause receives the value of the body and produces the
          -- value of the whole handler expression, so both sides must agree
          -- with the body's type.  Without these unifications the clause could
          -- return a value of any type and its parameter could be used at any
          -- type; the handler is statically typed as the body, so the runtime
          -- would then carry a value that its type does not describe.
          thenScope1 <- unifyTypes thenScope0 typedThen.lArgT blockT'
          thenScope2 <- unifyTypes thenScope1 typedThen.lRetT blockT'

          -- A clause runs when its operation is performed, so its effects
          -- belong to the handler expression.  Checking them here against the
          -- *body's* row would reject every clause that does more than the
          -- body; the function's own declared row is the right bound, and it
          -- is checked once, at the end of the body.
          --
          -- `inferLambda` returns the empty evaluation row (T-Lam); the
          -- effects of running the clause are in its latent row.  The row of
          -- `then` was previously taken from the former, so a handler whose
          -- `then` read, rebound or created state reported none of it.
          thenRow <- applyEffRowSubst thenScope2 typedThen.lFxs
          clauseRows <- mapM
            (applyEffRowSubst thenScope2)
            [row | (_, lam, _, _) <- typedClauses, let row = lam.lFxs]
          let finalHandlerRow =
                Eff.unionEffRowsList (handlerRow : thenRow : clauseRows)

              typedHandler =
                TypedIR.Handler
                  eff'
                  (blockStatements, blockExpr)
                  typedClauses
                  typedThen

          wrapInferResultWithCell $
            InferResult
              (TypedIR.TEHandle typedHandler blockT')
              finalHandlerRow
              thenScope2

-- | Remove the effect a handler handles from the row of its body.
--
--   The occurrence in the body is matched by name and then unified with the
--   handled effect, not compared with it: @Loop[`T]@ in the signature and
--   @Loop[`m11]@ in a recursive call are the same effect only after @`m11@ has
--   been bound to @`T@.  A syntactic comparison leaves the effect in the
--   handler's row, so a recursive handler does not terminate its own effect.
removeHandledEffect :: Scope -> EffCons -> EffRow -> TypeCheckM (Scope, EffRow)
removeHandledEffect scope handled row = case handled of
  EVar _ -> pure (scope, Unify.removeConsFromRow handled row)
  EffCons (ECons name args) -> go scope row
    where
      go sc = \case
        RClosed cons -> do
          (sc', kept) <- foldM step (sc, []) cons
          pure (sc', RClosed kept)
        ROpen cons v -> do
          (sc', kept) <- foldM step (sc, []) cons
          pure (sc', ROpen kept v)
        r@(RVar _) -> pure (sc, r)

      step (sc, kept) cons@(EffCons (ECons name' args'))
        | name' == name = do
            sc' <- unifyTypeArgLists sc args' args
            pure (sc', kept)
        | otherwise = pure (sc, kept <> [cons])
      step (sc, kept) cons = pure (sc, kept <> [cons])

-- | Bind the operations of the effects named in a type's latent row.
--
--   A parameter such as @do () -> {Loop[`T]; ...Main} `T@ tells the caller that
--   its argument may perform @Loop@, so @break@ and @continue@ must be visible
--   while that argument is checked.  The effect is declared at the top level,
--   but its operations are only bound inside an `under` block, and the argument
--   is not inside one; the expected type is what licenses the names here.
withRowOperations :: Scope -> Typ -> TypeCheckM Scope
withRowOperations scope typ = do
  t <- applyTypeSubst scope typ
  case t of
    TFunct (Funct _ _ row) -> do
      row' <- applyEffRowSubst scope row
      fst <$> foldM addEffectOps (scope, Map.empty) (rowEffects row')
    _ -> pure scope
 where
  rowEffects = \case
    RClosed cs -> cs
    ROpen cs _ -> cs
    RVar _ -> []

  -- The second component remembers which effect declared each operation bound
  -- for this row.  Two effects of one row may declare the same operation name;
  -- binding the first silently and then running whichever handler is innermost
  -- would check the call against one effect and run it in the other, so the
  -- duplicate is reported here.
  addEffectOps (sc, seen) = \case
    EffCons (ECons name args) -> case effectDeclaration sc name of
      Nothing -> pure (sc, seen)
      Just (EffDef _ params ops) ->
        foldM (bindOp name) (sc, seen) (instantiateOps params ops args)
    EVar _ -> pure (sc, seen)

  bindOp opEff (sc, seen) (opName, opTyp)
    | Just other <- Map.lookup opName seen
    , other /= opEff =
        throwTypeCheckError $ InferenceError $ T.concat
          [ "the operation `", opName, "` is provided by both effects `", other
          , "` and `", opEff, "`, so a use of it is ambiguous"
          ]
    | Scope.hasBinding False sc opName = pure (sc, Map.insert opName opEff seen)
    | otherwise = do
        opT <- generalize sc (TFunct opTyp)
        sc' <- Scope.addBinding opName opT (XVar opName) Val sc
        pure (sc', Map.insert opName opEff seen)

inferLambda :: Scope -> Types.Lambda -> InferM TypedIR.Lambda
inferLambda scope lam = withNewLevel $ do
  let scope1 = enterScope scope
  argT' <- maybe freshMetaTypeM pure lam.lArgT
  retT' <- maybe freshMetaTypeM pure lam.lRetT

  -- T-Lam binds the parameter as (Val, T_1, R): forcing the argument costs
  -- whatever the arrow's latent row licenses, because at a call site the
  -- argument cell is created with exactly that row (W1 in the paper).  A use
  -- of the parameter inside the body therefore pays R, and the body's row must
  -- stay inside R.
  rowFxs <- if lam.lFxs == RClosed [] then ROpen [] <$> freshMetaM else pure lam.lFxs
  scope2 <- Scope.addBindingWithRow lam.lArg (monoScheme argT') (XVar lam.lArg) Val rowFxs scope1

  InferResult blockT blockFxs0 scope3 <- inferBlock scope2 lam.lBlock
  -- модель (T-Lam): упоминание переменной, несущей состояние, попадает в латентный ряд
  men <- mentionRow scope3 (Set.delete lam.lArg (fvTypedBlock blockT))
  let blockFxs = Eff.unionEffRows blockFxs0 men
  blockT' <- typeOfTypedBlockIn scope3 blockT
  -- The annotated result type is a promise; an aggregate body with a smaller
  -- pending row keeps it.
  scope4 <- subsumesType scope3 blockT' retT'

  -- T-Lam: R' ∪ Men ⊆ R.  Inclusion, not equality: an annotated row may be
  -- wider than the body needs, and the parameter's pending row is that same R.
  scope5 <- subsumesEffRow scope4 blockFxs rowFxs
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
instantiateTypeScheme scope scheme =
  (\(typ, _, scope') -> (typ, scope')) <$>
    instantiateTypeSchemeWithRow scope scheme Eff.empty

-- | Instantiate a scheme and, at the same time, a row that belongs to the
--   binding but is not part of its type (the pending row of a @val@ binding).
--   The row shares the scheme's row variables, so it has to be freshened with
--   the same mapping; otherwise a postponed effect would stay attached to the
--   definition-site variable after every use of a polymorphic binding.
instantiateTypeSchemeWithRow :: Scope -> TypeScheme -> EffRow -> TypeCheckM (Typ, EffRow, Scope)
instantiateTypeSchemeWithRow scope scheme extraRow = do
  let tvars = _ts scheme
      evars = _es scheme
      rvars = _rs scheme
      typ = _a scheme

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

  scope'' <- foldM
    (\sc (old, new) ->
      case Map.lookup old (_rowLacks scheme) of
        Nothing -> pure sc
        Just forbidden -> addRowLacks sc new forbidden)
    scope'
    (zip rvars freshRows)

  scope''' <- foldM
    (\sc (old, new) ->
      case Map.lookup old (_effLacks scheme) of
        Nothing -> pure sc
        Just forbidden -> addEffLacks sc new forbidden)
    scope''
    (zip evars freshEffects)

  typ' <- applyTypeSubst scope''' typ
  row' <- applyEffRowSubst scope''' extraRow

  pure (typ', row', scope''')

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
  -- модель (T-Block): Cell, если локальный var достижим из результата блока (состояние
  -- уходит наружу, например в замыкании); иначе Var, если var есть; иначе ничего
  exprTyp <- typeOfTypedExprIn scope' exprT
  let varNames = [n | TypedIR.Bind Var n _ <- stats']
      escapes = canHoldState exprTyp && any (`Set.member` reachNames stats' exprT) varNames
      phi
        | null varNames = Eff.empty
        | escapes = Eff.closedOfFlat "Cell"
        | otherwise = Eff.closedOfFlat "Var"
  pure $ InferResult
    (stats', exprT)
    (Eff.unionEffRows phi $ Eff.unionEffRows statFxs exprFxs)
    (Scope.keepSubst scope' outer)

inferStat :: Scope -> Types.Stat -> InferM TypedIR.Stat
inferStat scope stat = do
  res <- inferStatNode scope stat
  -- The statement's own span wins over the span of its right-hand side: an
  -- error about the statement should point at the statement.
  let InferResult st' fxs sc' = res
  pure $ InferResult (atTypedStatSpan (statSpan stat) st') fxs sc'

inferStatNode :: Scope -> Types.Stat -> InferM TypedIR.Stat
inferStatNode scope stat =
  withErrorStack (EFIr $ IrFrame (pretty stat) (statSpan stat)) $ case stat of
  Types.Expr e -> do
    InferResult e' fxs scope' <- inferExpr scope e
    pure $ InferResult
      (TypedIR.Expr e')
      fxs
      scope'
  Types.Bind m n typOpt e -> do
    when (Scope.hasBinding False scope n) $
      throwTypeCheckError $ SameScopeBindingShadowing n

    -- 1. Infer expr
    InferResult inferredTypedExpr inferredFxs scope1 <- inferExpr scope e
    inferredTyp <- typeOfTypedExprUnsafe inferredTypedExpr

    -- 2. Prepare binding
    (exprForBinding, typForBinding, fxsForBinding, bindingRow, scope2) <-
      case m of
        Imm -> do
          let frozenExpr = freeze inferredTypedExpr

          -- The snapshot copies the current values of the free variables.  A
          -- later assignment may extend their pending rows, so freezing must
          -- not constrain those rows (see 'environmentRowVars'); otherwise
          -- `var x = 5; imm y = ... x ...; x := + x 1` would be rejected.
          excluded <- environmentRowVars scope1

          -- Freeze the inferred type, including latent function effects.
          inferredTyp' <- applyTypeSubst scope1 inferredTyp
          (scope', frozenTyp) <- freezeTypExcept excluded scope1 inferredTyp'

          -- Remove explicit mutation effects and constrain the remaining
          -- effect variables and row tails that belong to the frozen value.
          inferredFxs' <- applyEffRowSubst scope' inferredFxs
          (scope'', frozenFxs) <- freezeRowMutInExcept excluded scope' inferredFxs'

          -- The snapshot itself reads the state of captured variables.  The
          -- frozen binding itself no longer reads anything, so its pending
          -- row is the frozen row, not the row of the snapshot statement.
          men <- mentionRow scope'' (fvTyped inferredTypedExpr)
          pure (frozenExpr, frozenTyp, Eff.unionEffRows frozenFxs men, frozenFxs, scope'')
        Val -> do
          -- T-ValBind: the binding remembers what forcing its thunk may do.
          -- It is not paid here; every use of the name pays it (T-Var).
          men <- mentionRow scope1 (fvTyped inferredTypedExpr)
          pure (inferredTypedExpr, inferredTyp, inferredFxs, Eff.unionEffRows inferredFxs men, scope1)
        Var -> do
          -- T-VarBind: the row variable bounds the declaration and every
          -- later assignment.  It starts open so that a rebinding may extend
          -- it; the declaration itself only adds a lower bound.
          men <- mentionRow scope1 (fvTyped inferredTypedExpr)
          rho <- ROpen [] <$> freshMetaM
          scope' <- subsumesEffRow scope1 (Eff.unionEffRows inferredFxs men) rho
          pure (inferredTypedExpr, inferredTyp, inferredFxs, rho, scope')

    -- 3. Handle annotation
    (expectedTyp, schemeForScope, scope3) <-
      case typOpt of
        Just anno -> do
          let scheme = monoScheme anno
          (annoInst, scope') <- instantiateTypeScheme scope2 scheme
          -- An annotation on an aggregate is an upper bound, just as it is in
          -- the return type of a function.
          scope'' <- subsumesType scope' typForBinding annoInst
          (annoInst, , scope'') <$> generalize scope'' anno

        Nothing -> do
          typForBinding' <- applyTypeSubst scope2 typForBinding
          pure (typForBinding', monoScheme typForBinding', scope2)

    -- 4. Unification
    scope4 <-
      if isNothing typOpt
        then unifyTypes scope3 typForBinding expectedTyp
        else pure scope3

    -- 5. Generalize (only for val/imm)
    finalScheme <-
      if m /= Var
        then generalize scope4 schemeForScope._a
        else pure schemeForScope

    -- 6. Add binding to Scope
    scope5 <- Scope.addBindingWithRow n finalScheme (XVar n) m bindingRow scope4

    -- 7. Final effects
    let finalFxs = fxsForBinding

    pure $
      InferResult
        (TypedIR.Bind m n exprForBinding)
        finalFxs
        scope5
  Types.Assign n e -> do
    (scheme, mut, pending) <- case Scope.findBindingWithRow True scope n of
      Nothing -> throwTypeCheckErrorWithNotes (UndefinedVariable n)
        (maybe [] pure (suggestionNote (Scope.bindingNames scope) n))
      Just (ValueBinding scheme _ mut' row) -> pure (scheme, mut', row)
    when (mut /= Var) $ throwTypeCheckError $ ImmutableVariableAssignment n
    (varT, scope') <- instantiateTypeScheme scope scheme
    InferResult eT eFxs scope'' <- inferExpr scope' e
    eT' <- typeOfTypedExprUnsafe eT
    -- T-Rebind: the right-hand side is delayed, so its row and its mention row
    -- must fit into the pending row chosen for the variable.
    men <- mentionRow scope'' (fvTyped eT)
    scopeRow <- subsumesEffRow scope'' (Eff.unionEffRows eFxs men) pending
    let finalFxs = Eff.unionEffRows eFxs $ Eff.closedOfFlat "Rebind"
    InferResult (TypedIR.Rebind n eT) finalFxs <$> unifyTypes scopeRow varT eT'

generalize :: Scope -> Typ -> TypeCheckM TypeScheme
generalize scope typ = do
  currentLevel' <- use currentLevel

  -- Сначала полностью разрешаем подстановки.
  typ' <- applyTypeSubst scope typ

  let isGeneralizable (Meta _ _ lvl) = lvl > currentLevel' || lvl == -1
      isGeneralizable _ = False

      allTvars = collectTvarsFromType [] typ'
      allEvars = collectEvarsFromType [] typ'
      allRvars = collectRvarsFromType [] typ'

      tvars = filter isGeneralizable allTvars
      evars = filter isGeneralizable allEvars
      rvars = filter isGeneralizable allRvars

      generalizedRows = Map.filterWithKey (\k _ -> k `elem` rvars) scope.rowLacks
      generalizedEffects = Map.filterWithKey (\k _ -> k `elem` evars) scope.effLacks

  pure Scheme {
    _ts = tvars,
    _es = evars,
    _rs = rvars,
    _rowLacks = generalizedRows,
    _effLacks = generalizedEffects,
    _a = typ'
  }

collectTvarsFromType :: [Taste] -> Typ -> [Taste]
collectTvarsFromType except typ =
  uniqPreserveOrder $ case typ of
    TArray t r -> collectTvarsFromType except t <> collectTvarsFromEffRow except r
    TPair l r fx ->
      collectTvarsFromType except l
        <> collectTvarsFromType except r
        <> collectTvarsFromEffRow except fx
    TFunct (Funct i o fxs) ->
      collectTvarsFromType except i
      <> collectTvarsFromType except o
      <> collectTvarsFromEffRow except fxs
    TForall vars _ _ _ _ t -> collectTvarsFromType (uniqPreserveOrder $ vars <> except) t
    TRecord props fx ->
      concatMap (collectTvarsFromType except . tTyp) props
        <> collectTvarsFromEffRow except fx
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
    TArray t r -> collectEvarsFromType except t <> collectEvarsFromEffRow except r
    TPair l r fx ->
      collectEvarsFromType except l
        <> collectEvarsFromType except r
        <> collectEvarsFromEffRow except fx
    TFunct (Funct i o fxs) -> collectEvarsFromType except i <> collectEvarsFromType except o <> collectEvarsFromEffRow except fxs
    TForall _ fxs _ _ _ t -> collectEvarsFromType (uniqPreserveOrder $ fxs <> except) t
    TRecord props fx ->
      concatMap (collectEvarsFromType except . tTyp) props
        <> collectEvarsFromEffRow except fx
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
    TArray t r ->
      collectRvarsFromType except t <> collectRvarsFromEffRow except r
    TPair l r fx ->
      collectRvarsFromType except l
        <> collectRvarsFromType except r
        <> collectRvarsFromEffRow except fx
    TFunct (Funct i o fxs) ->
      concatMap (collectRvarsFromType except) [i, o] <>
      collectRvarsFromEffRow except fxs
    TForall _ _ rows _ _ t -> collectRvarsFromType (uniqPreserveOrder $ rows <> except) t
    TRecord props fx ->
      concatMap (collectRvarsFromType except . tTyp) props
        <> collectRvarsFromEffRow except fx
    _ -> []

collectRvarsFromEffRow :: [Taste] -> EffRow -> [Taste]
collectRvarsFromEffRow except fx =
  uniqPreserveOrder $ case fx of
    RVar v -> [v | v `notElem` except]
    ROpen _ v -> [v | v `notElem` except]
    _ -> []

-- | Свободные переменные типизированного выражения (для анализа выхода состояния из блока).
--   Привязки let учитываются консервативно (не вычитаются).
-- | Тип несёт изменяемое состояние (модель: St_T): var-поле записи, латентный ряд стрелки
--   с Read/Rebind, pending row агрегата с Read/Rebind или хвост ряда, не обобщённый схемой
--   (неизвестные эффекты).
--   У стрелки учитывается только её собственный ряд, а не тип результата: функция,
--   которая создаёт состояние (make), само состояние не держит.
bearsState :: [Taste] -> Typ -> Bool
bearsState quantified = go
  where
    go = \case
      TArray t r -> go t || effRowBearsState quantified r
      TPair l r fx -> go l || go r || effRowBearsState quantified fx
      TFunct (Funct _ _ row) -> effRowBearsState quantified row
      TRecord props fx ->
        any (\p -> tMut p == Var || go (tTyp p)) props
          || effRowBearsState quantified fx
      -- An inference variable may still be instantiated with a type that
      -- carries state, so it is assumed to.  A rigid variable (bound by a
      -- signature, or a skolem) cannot: nothing can make it a state type, so
      -- it does not make its user perform `Read`.
      TVar Meta{} -> True
      TVar _ -> False
      _ -> False

-- | Does this row name a read or a rebind?
--
--   Only an explicit effect counts.  An unresolved tail is not evidence: a
--   parameter's pending row *is* the latent row of the arrow being inferred
--   (T-Lam), so reading openness as "may still become Read" would make every
--   parameter of every lambda state-bearing on its own account, and a pure
--   `{(n) = + n 1}` would be forced to declare `Read`.  A row that a later
--   assignment extends belongs to a @var@ binding, which is already
--   state-bearing through its mutability.
effRowBearsState :: [Taste] -> EffRow -> Bool
effRowBearsState _quantified = \case
  RClosed cs -> any isUse cs
  ROpen cs _ -> any isUse cs
  RVar _ -> False
  where
    isUse = \case
      EffCons (ECons n _) -> n == "Read" || n == "Rebind"
      _ -> False

-- | The row tails the current substitution has produced for a scheme's row
--   variables.
--
--   Instantiation replaces every quantified tail with a fresh metavariable, so
--   a type read back through the scope mentions the copies, not the variables
--   the scheme still records.  Without this translation a row-polymorphic
--   builtin (`sayn : a -> {Output | ρ} ()`) would look like it carried an
--   unknown, possibly state-bearing tail.
instantiatedRowTails :: Scope -> [Taste] -> TypeCheckM [Taste]
instantiatedRowTails scope = fmap concat . mapM tails
  where
    tails v = do
      r <- applyEffRowSubst scope (RVar v)
      pure $ case r of
        RVar w -> [w]
        ROpen _ w -> [w]
        _ -> []

-- | Несёт ли переменная состояние (модель: St): var-привязка, тип, несущий
--   состояние, или pending row, в котором есть Read/Rebind.
varBearsState :: Scope -> Text -> TypeCheckM Bool
varBearsState scope n =
  case Scope.findBindingWithRow True scope n of
    Nothing -> pure False
    Just (ValueBinding (Scheme _ _ rvs _ _ t) _ m row) -> do
      t' <- applyTypeSubst scope t
      row' <- applyEffRowSubst scope row
      freshTails <- instantiatedRowTails scope rvs
      let quantified = rvs <> freshTails
      pure $ m == Var || bearsState quantified t' || effRowBearsState quantified row'

-- | Выражение не создаёт и не меняет состояние: freeze на нём тождествен
--   (нет var-операторов, присваиваний и var-полей)
isFrozenExpr :: TypedExpr -> Bool
isFrozenExpr = \case
  TEArray _ _ es -> all isFrozenExpr es
  TEPair _ l r -> isFrozenExpr l && isFrozenExpr r
  TEXLambda lam -> isFrozenBlock lam.lBlock
  TEApply f x -> isFrozenExpr f && isFrozenExpr x
  TERecord me props _ ->
    maybe True isFrozenExpr me
      && all (\(TERecordProp m _ _ e) -> m /= Var && isFrozenExpr e) props
  TEHandle (TypedIR.Handler _ block clauses mlam) _ ->
    isFrozenBlock block && isFrozenBlock mlam.lBlock
      && all (\(_, l, _, _) -> isFrozenBlock l.lBlock) clauses
  TEParen b -> isFrozenBlock b
  TEResume e _ -> isFrozenExpr e
  TELet _ bound body -> isFrozenExpr bound && isFrozenExpr body
  TEPropAccess e _ -> isFrozenExpr e
  TEIfElse p t f -> isFrozenExpr p && isFrozenExpr t && isFrozenExpr f
  _ -> True

isFrozenBlock :: TypedIR.Block -> Bool
isFrozenBlock (stats, expr) = all stat stats && isFrozenExpr expr
  where
    stat = \case
      TypedIR.Bind m _ e -> m /= Var && isFrozenExpr e
      TypedIR.Rebind _ _ -> False
      TypedIR.Expr e -> isFrozenExpr e

-- | Упоминание (модель: Men): Read, если среди переменных есть несущая состояние.
--   Снимок такой переменной прочитал бы изменяемое состояние, даже если переменная
--   только упомянута и не используется.
mentionRow :: Scope -> Set.Set Text -> TypeCheckM EffRow
mentionRow scope names = do
  flags <- mapM (varBearsState scope) (Set.toList names)
  pure $ if or flags then Eff.closedOfFlat "Read" else Eff.empty

fvTyped :: TypedExpr -> Set.Set Text
fvTyped = \case
  TEXVar n _ -> Set.singleton n
  TEArray _ _ es -> Set.unions (map fvTyped es)
  TEPair _ l r -> Set.union (fvTyped l) (fvTyped r)
  TEXLambda lam -> Set.delete lam.lArg (fvTypedBlock lam.lBlock)
  TEApply f x -> Set.union (fvTyped f) (fvTyped x)
  TERecord me props _ ->
    Set.unions $ maybe [] (pure . fvTyped) me <> [fvTyped e | TERecordProp _ _ _ e <- props]
  TEHandle (TypedIR.Handler _ block clauses mlam) _ ->
    Set.unions $ [fvTypedBlock block, fvTypedBlock mlam.lBlock]
      <> map (\(_, l, _, _) -> fvTypedBlock l.lBlock) clauses
  TEParen b -> fvTypedBlock b
  TEResume e _ -> fvTyped e
  TELet _ bound body -> Set.union (fvTyped bound) (fvTyped body)
  TEPropAccess e _ -> fvTyped e
  TEIfElse p t f -> Set.unions [fvTyped p, fvTyped t, fvTyped f]
  _ -> Set.empty

fvTypedBlock :: TypedIR.Block -> Set.Set Text
fvTypedBlock (stats, expr) = go Set.empty stats
  where
    go bound [] = Set.difference (fvTyped expr) bound
    go bound (s : ss) =
      let (fvS, bound') = stat bound s
      in Set.union fvS (go bound' ss)
    stat bound = \case
      TypedIR.Bind _ n e -> (Set.difference (fvTyped e) bound, Set.insert n bound)
      TypedIR.Rebind n e -> (Set.difference (Set.insert n (fvTyped e)) bound, bound)
      TypedIR.Expr e -> (Set.difference (fvTyped e) bound, bound)

-- | Может ли значение этого типа держать изменяемое состояние (замыкание, запись,
--   структура с такими компонентами). Значения базовых типов состояния не держат,
--   поэтому из блока с результатом Int или () состояние наружу не уходит.
--
--   This is @St_T@ of the paper: an aggregate holds state when a component does
--   or when its pending row names `Read`/`Rebind`, a record also when it has a
--   `var` field, and an arrow only through its own latent row (a function that
--   *creates* state holds none).  Every type variable counts, because it may be
--   instantiated by a type that does; 'bearsState' can be more generous about a
--   parameter, whose row is the arrow's latent row, but the capture rule of a
--   block result must stay conservative.
canHoldState :: Typ -> Bool
canHoldState = \case
  TInt -> False
  TFloat -> False
  TBoolean -> False
  TString -> False
  TNil -> False
  TNothing -> False
  TArray t r -> canHoldState t || effRowBearsState [] r
  TPair l r fx -> canHoldState l || canHoldState r || effRowBearsState [] fx
  TRecord props r ->
    any (\p -> tMut p == Var || canHoldState (tTyp p)) props
      || effRowBearsState [] r
  TFunct (Funct _ _ row) -> effRowBearsState [] row
  TVar _ -> True
  _ -> True

-- | Имена, достижимые из результата блока (модель: reach): свободные переменные результата,
--   замкнутые относительно привязок и присваиваний блока.
reachNames :: [TypedIR.Stat] -> TypedExpr -> Set.Set Text
reachNames stats result = grow (fvTyped result)
  where
    grow acc =
      let acc' = foldl step acc stats
      in if acc' == acc then acc else grow acc'
    step acc = \case
      TypedIR.Bind m n e | m /= Imm, Set.member n acc -> Set.union acc (fvTyped e)
      TypedIR.Rebind n e | Set.member n acc -> Set.union acc (fvTyped e)
      _ -> acc

createsCell :: TypedExpr -> Bool
createsCell = \case
  TEParen _ -> False  -- Var/Cell блока учитывает inferBlock (phi)
  TEArray _ _ es -> any createsCell es
  TEPair _ l r -> createsCell l || createsCell r
  TEXLambda _ -> False  -- латентный ряд тела несёт Var/Cell
  TERecord me props _ ->
    maybe False createsCell me ||
    any (\(TERecordProp m _ _ e) -> m == Var || createsCell e) props
  TEHandle _ _ -> False
  TEResume e _ -> createsCell e
  TELet _ wht whr -> any createsCell [wht, whr]
  TEIfElse p t f -> any createsCell [p, t, f]
  TEPropAccess e _ -> createsCell e
  _ -> False

freeze :: TypedExpr -> TypedExpr
freeze = \case
  TEArray t r es -> TEArray t r $ map freeze es
  TEPair r l e -> TEPair r (freeze l) $ freeze e
  TEXLambda l -> TEXLambda l {TypedIR.lBlock = freezeBlock l.lBlock}
  TEApply c e -> TEApply (freeze c) $ freeze e
  TERecord a ps r ->
    let a' = freeze <$> a
        mapTERecordProp :: TERecordProp -> TERecordProp
        mapTERecordProp p = p {terExpr = freeze p.terExpr, terMut = freezeMutability p.terMut}
        ps' = map mapTERecordProp ps
    in
    TERecord a' ps' r
  TEHandle h t -> TEHandle (freezeHandler h) t
  TEParen b -> TEParen $ freezeBlock b
  TEResume e t -> TEResume (freeze e) t
  TELet lp wht whr -> TELet lp (freeze wht) (freeze whr)
  TEPropAccess t x -> TEPropAccess (freeze t) x
  TEIfElse p t f -> TEIfElse (freeze p) (freeze t) (freeze f)
  e -> e

-- | Заморозка типа: var-поля записей становятся val, из рядов стрелок убираются
--   Var, Read, Rebind, Cell (модель: freeze на типах)
freezeTyp :: Scope -> Typ -> TypeCheckM (Scope, Typ)
freezeTyp = freezeTypExcept Set.empty

-- | Freeze a type without constraining the row variables in @excluded@.
--
--   A snapshot copies the current values of its free variables; it does not
--   promise anything about their future assignments.  The pending row of a
--   live @var@ is an upper bound that a later rebinding may extend, so
--   constraining such a variable to lack @Mut@ would make the snapshot reject
--   a program whose later assignment is perfectly legal.  The caller therefore
--   excludes the row and effect variables that the environment controls (see
--   'environmentRowVars'); their rows are kept as upper bounds in the frozen
--   type, which is conservative but sound.  Variables that the frozen value
--   owns (quantified tails, rows created inside the expression) are still
--   constrained.
freezeTypExcept :: Set Taste -> Scope -> Typ -> TypeCheckM (Scope, Typ)
freezeTypExcept excluded scope = \case
  TArray t r -> do
    (scope', t') <- freezeTypExcept excluded scope t
    (scope'', r') <- freezeRowMutInExcept excluded scope' r
    pure (scope'', TArray t' r')

  TPair l r fx -> do
    (scope', l') <- freezeTypExcept excluded scope l
    (scope'', r') <- freezeTypExcept excluded scope' r
    (scope''', fx') <- freezeRowMutInExcept excluded scope'' fx
    pure (scope''', TPair l' r' fx')

  TFunct (Funct i o fxs) -> do
    (scope', i') <- freezeTypExcept excluded scope i
    (scope'', o') <- freezeTypExcept excluded scope' o
    (scope''', fxs') <- freezeRowMutInExcept excluded scope'' fxs
    pure (scope''', TFunct (Funct i' o' fxs'))

  TRecord props r -> do
    (scope', props') <- foldM freezeProp (scope, []) props
    (scope'', r') <- freezeRowMutInExcept excluded scope' r
    pure (scope'', TRecord props' r')

  TForall ts es rs els rls t -> do
    let scope' = scope {
      effLacks = foldr Map.delete scope.effLacks es,
      rowLacks = foldr Map.delete scope.rowLacks rs
    }
    (scope'', t') <- freezeTypExcept excluded scope' t
    let quantifiedEs = Set.fromList es
        quantifiedRs = Set.fromList rs
        els' = Map.unionWith Set.union els $
          Map.restrictKeys scope''.effLacks quantifiedEs
        rls' = Map.unionWith Set.union rls $
          Map.restrictKeys scope''.rowLacks quantifiedRs
        -- Constraints on variables that this forall does not bind belong to
        -- the surrounding scope.  Dropping them would leave a tail in the
        -- frozen body free to be instantiated with `Read` later, so they are
        -- kept; the constraints on the quantified variables have already
        -- moved into 'els'' and 'rls''.
        scopeOut = scope'' {
          effLacks = Map.withoutKeys scope''.effLacks quantifiedEs,
          rowLacks = Map.withoutKeys scope''.rowLacks quantifiedRs
        }
    pure (scopeOut, TForall ts es rs els' rls' t')

  t -> pure (scope, t)
  where
    freezeProp (sc, acc) p = do
      (sc', typ') <- freezeTypExcept excluded sc (tTyp p)
      pure (sc', acc <> [p {tMut = freezeMutability (tMut p), tTyp = typ'}])

freezeRowMutIn :: Scope -> EffRow -> TypeCheckM (Scope, EffRow)
freezeRowMutIn = freezeRowMutInExcept Set.empty

freezeRowMutInExcept :: Set Taste -> Scope -> EffRow -> TypeCheckM (Scope, EffRow)
freezeRowMutInExcept excluded scope row = do
  let frozenRow = foldl (flip removeConsFromRow) row $ map Eff.label (Set.toList mutationEffects)
  (, frozenRow) <$> addRowLacksToRowExcept excluded scope frozenRow mutationEffects

-- | The row and effect variables whose instantiation the environment controls:
--   they occur in the pending rows or in the types of the bindings currently
--   in scope.  A rebinding may extend those rows after a snapshot, so freezing
--   must treat them as upper bounds rather than as tails it can constrain.
environmentRowVars :: Scope -> TypeCheckM (Set Taste)
environmentRowVars scope = do
  rows <- mapM (applyEffRowSubst scope) (visibleRows scope)
  let typVars = concatMap (rowVarsInTyp . _a . vbScheme) (visibleBindings scope)
  pure $ Set.fromList $ filter isMeta $ concatMap rowVarsInRow rows <> typVars
  where
    isMeta Meta{} = True
    isMeta _ = False

    visibleBindings :: Scope -> [ValueBinding]
    visibleBindings sc =
      Map.elems sc.values <> maybe [] visibleBindings sc.parent

    visibleRows :: Scope -> [EffRow]
    visibleRows sc =
      [vbRow b | b <- visibleBindings sc]

rowVarsInRow :: EffRow -> [Taste]
rowVarsInRow = \case
  RClosed cs -> concatMap rowVarsInCons cs
  ROpen cs v -> v : concatMap rowVarsInCons cs
  RVar v -> [v]

rowVarsInCons :: EffCons -> [Taste]
rowVarsInCons = \case
  EVar v -> [v]
  EffCons (ECons _ _) -> []

rowVarsInTyp :: Typ -> [Taste]
rowVarsInTyp = \case
  TArray t r -> rowVarsInTyp t <> rowVarsInRow r
  TPair l r fx -> rowVarsInTyp l <> rowVarsInTyp r <> rowVarsInRow fx
  TFunct (Funct i o row) -> rowVarsInTyp i <> rowVarsInTyp o <> rowVarsInRow row
  TRecord props r -> concatMap (rowVarsInTyp . tTyp) props <> rowVarsInRow r
  TForall _ _ _ _ _ t -> rowVarsInTyp t
  _ -> []

addRowLacksToRowExcept :: Set Taste -> Scope -> EffRow -> Set Text -> TypeCheckM Scope
addRowLacksToRowExcept excluded scope row forbidden =
  case row of
    RClosed cons -> foldM addEffectLacks scope cons
    ROpen cons tailVar -> do
      scope' <- foldM addEffectLacks scope cons
      if tailVar `Set.member` excluded
        then pure scope'
        else addRowLacks scope' tailVar forbidden
    RVar variable ->
      if variable `Set.member` excluded
        then pure scope
        else addRowLacks scope variable forbidden
  where
    addEffectLacks sc effect =
      case effect of
        -- Explicit mutation effects have already been removed from the row;
        -- any other label is ordinary and does not need a lacks constraint.
        EffCons (ECons _ _) -> pure sc
        EVar variable
          | variable `Set.member` excluded -> pure sc
          | otherwise -> addEffLacks sc variable forbidden

mutationEffects :: Set Text
mutationEffects = Set.fromList ["Read", "Var", "Rebind", "Cell"]

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