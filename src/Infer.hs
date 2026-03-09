{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
module Infer (
  -- isTypeMonomorphic,
  -- isEffMonomorphic,
  -- countResumeInBlock,
  -- countResumeInStat,
  -- countResumeInExpr,
  -- countResumeInLambda,
  -- inferExpr
) where
{-
import Types (
    Typ (..),
    Scope,
    typeSubst,
    EffRow (..),
    effSubst,
    Block,
    Stat (..),
    Expr(..),
    Lambda (..),
    block,
    Handler (..),
    Mutability (Val),
    TRecordProp (..), Taste, NativeLambda (..), NativeLambdaSign (..), handlerCons, NativeBlock, TypeScheme, Scheme (..)
  )
import qualified Data.Map as Map
import Resume (ResumeInfo(NoResume, OneResume))
import Unify (TypeCheckM, TypeCheckError (..), freshSkolemM, unifyTypes, freshMetaTypeM, freshMetaM, applyTypeSubst, applyEffRowSubst, removeConsFromRow, freshMetaEffM)
import Control.Monad.Error.Class (MonadError(throwError))
import Record (tTyp, eExp)
import qualified Eff
import qualified Scope
import Scope (enterScope)
import Control.Monad (foldM, join)
import Utils (mapAccumM, uniqPreserveOrder)
import Data.List (sort, nub, intercalate)

isTypeMonomorphic :: Scope -> Typ -> Bool
isTypeMonomorphic scope = \case
  TForall {} -> False
  TVar v -> case Map.lookup v (typeSubst scope) of
    Just t -> isTypeMonomorphic scope t
    _ -> False
  TList t -> isTypeMonomorphic scope t
  TPair l r -> isTypeMonomorphic scope l && isTypeMonomorphic scope r
  TFunc (i, o, fxs) ->
    isTypeMonomorphic scope i
    && isTypeMonomorphic scope o
    && isEffMonomorphic scope fxs
  TRecord props -> all (isTypeMonomorphic scope . tTyp) props
  _ -> True

isEffMonomorphic :: Scope -> EffRow -> Bool
isEffMonomorphic scope = \case
  EVar e -> case Map.lookup e $ effSubst scope of
    Just e' -> isEffMonomorphic scope e'
    _ -> False
  EClosed cons ->
    all (all (isTypeMonomorphic scope) . snd) cons
  EOpen cons t ->
    all (all (isTypeMonomorphic scope) . snd) cons
    && isEffMonomorphic scope (EVar t)

countResumeInBlock :: Block -> ResumeInfo
countResumeInBlock (stats, e) =
  foldl (\acc stat -> acc <> countResumeInStat stat) NoResume (stats ++ [Expr e])

countResumeInStat :: Stat -> ResumeInfo
countResumeInStat = \case
  Expr e -> countResumeInExpr e
  Assign _ e -> countResumeInExpr e
  Bind _ _ _ e -> countResumeInExpr e

countResumeInExpr :: Expr -> ResumeInfo
countResumeInExpr = \case
  List es -> foldl (<>) NoResume $ map countResumeInExpr es
  Pair l r -> countResumeInExpr l <> countResumeInExpr r
  XLambda l -> countResumeInLambda l
  Apply f x -> countResumeInExpr f <> countResumeInExpr x
  With e _ _ -> countResumeInExpr e
  Handle (Handler _ block' _ then_) ->
    countResumeInBlock block' <> maybe NoResume countResumeInLambda then_
  Resume _ -> OneResume
  Record props ->
    foldl (<>) NoResume $ map (countResumeInExpr . eExp) props
  _ -> NoResume

countResumeInLambda :: Lambda -> ResumeInfo
countResumeInLambda l = countResumeInBlock l.block

substituteType :: Scope -> Taste -> Typ -> Scope
substituteType scope taste typ = scope{typeSubst = Map.insert taste typ scope.typeSubst}

substituteEff :: Scope -> Taste -> EffRow -> Scope
substituteEff scope taste eff = scope{effSubst = Map.insert taste eff scope.effSubst}

inferExpr :: Scope -> Expr -> TypeCheckM (Typ, EffRow, Scope)
inferExpr scope = \case
  Int _ -> pure (TInt, Eff.empty, scope)
  Float _ -> pure (TFloat, Eff.empty, scope)
  Boolean _ -> pure (TBoolean, Eff.empty, scope)
  String _ -> pure (TString, Eff.empty, scope)
  Nil -> pure (TNil, Eff.empty, scope)
  XVar v -> do
    (bindingT, scope') <- case Scope.findBinding True scope v of
      Nothing -> throwError $ UndefinedVariable v
      Just (typ, _, _) -> instantiate scope typ
    pure (bindingT, Eff.empty, scope')
  List [] -> pure (TList TNothing, Eff.empty, scope)
  List (x:xs) -> do
    (hType, fxs, scope') <- inferExpr scope x
    (_, finalFxs, finalScope) <- foldM
      (\(tExpected, accFxs, sc) e -> do
          (tElem, tFxs, sc') <- inferExpr sc e
          sc'' <- unifyTypes sc' tExpected tElem
          pure (tExpected, Eff.unionEffRows accFxs tFxs, sc'')
      )
      (hType, fxs, scope')
      xs
    pure (TList hType, finalFxs, finalScope)
  Pair l r -> do
    (lTyp, lFxs, scope') <- inferExpr scope l
    (rTyp, rFxs, scope'') <- inferExpr scope' r
    pure (TPair lTyp rTyp, Eff.unionEffRows lFxs rFxs, scope'')
  XLambda lam -> inferLambda scope lam
  Apply callee arg -> do
    (calleeT, calleeFxs, calleeScope) <- inferExpr scope callee
    (calleeT', calleeScope') <- instantiate calleeScope calleeT
    expectedFromT <- freshMetaTypeM
    expectedToT <- freshMetaTypeM
    expectedCalleeT <- do
      fxs <- freshMetaM
      pure $ TFunc (expectedFromT, expectedToT, EOpen [] fxs)
    scope' <- unifyTypes calleeScope' calleeT' expectedCalleeT
    (argT, argFxs, argScope) <- inferExpr scope' arg
    scope'' <- unifyTypes argScope argT expectedFromT
    pure (expectedToT, Eff.unionEffRows calleeFxs argFxs, scope'')
  With expr types fxs -> do
    (exprT, exprFxs, exprScope) <- inferExpr scope expr
    case exprT of
      TForall tvars evars typ ->
        let typesLength = length types in
        let tvarsLength = length tvars in
        let fxsLength = length fxs in
        let evarsLength = length evars in
        if typesLength /= tvarsLength then
          throwError
          $ TypeError
          $ "Wrong type args amount in with: expected "
            ++ show tvarsLength
            ++ ", given "
            ++ show typesLength
        else if fxsLength /= evarsLength then
          throwError
          $ TypeError
          $ "Wrong effect args amount in with: expected "
            ++ show evarsLength
            ++ ", given "
            ++ show fxsLength
        else do
          let scope1 = enterScope Nothing exprScope
          let scope2 = foldl (\sc (tvar, typ) -> substituteType sc tvar typ) scope1 (zip tvars types)
          let scope3 = foldl (\sc (evar, fx) -> substituteEff sc evar fx) scope2 (zip evars fxs)
          instantiated <- applyTypeSubst scope3 typ
          row <- applyEffRowSubst scope3 exprFxs
          pure (instantiated, row, scope3)
      t -> throwError $ TypeError $ "with: expression type `" ++ show t ++ "` is not forall"
  NLambda (NativeLambda (NativeLambdaSign arg argT retT fxs) fun) -> do
    lamT <- case (argT, retT) of
          (Nothing, Nothing) -> do
            argName <- freshSkolemM
            retName <- freshSkolemM
            pure $ TForall [argName, retName] [] $ TFunc (TVar argName, TVar retName, fxs)
          (Nothing, Just retT) -> do
            argName <- freshSkolemM
            pure $ TForall [argName] [] $ TFunc (TVar argName, retT, fxs)
          (Just argT, Nothing) -> do
            retName <- freshSkolemM
            pure $ TForall [retName] [] $ TFunc (argT, TVar retName, fxs)
          (Just argT, Just retT) -> pure $ TFunc (argT, retT, fxs)
    pure (lamT, Eff.empty, scope)
  Handle handler -> inferHandler scope handler
  _ -> throwError $ TypeError ""

inferHandler :: Scope -> Handler -> TypeCheckM (Typ, EffRow, Scope)
inferHandler scope handler = do
  -- 1. Получаем сигнатуру эффекта
  let eff = handlerCons handler
  ops <- case Scope.findEffOps True scope eff of
    Nothing -> throwError $ TypeError ""
    Just ops -> pure ops
  -- 2. Создаём подскоуп с операциями
  let blockScope = enterScope Nothing scope
  scope' <- foldM (\sc (name, typ) -> Scope.addBinding name (TFunc typ) (XVar name) Val sc) blockScope ops
  -- 3. Теперь можно типизировать сам блок — операции видимы
  (blockT, blockFxs, blockScope) <-
    case handler of
      {-
      eff block clauses then
        NativeHandler EffCons NativeBlock [NativeHandlerClause] (Maybe NativeLambda)
        | Handler     EffCons Block       [HandlerClause]       (Maybe Lambda)
      -}
      Handler _ block _ _ -> inferBlock scope' block
      NativeHandler _ block _ _ -> inferNativeBlock scope' block
  -- 4. Далее всё как прежде — проверяем и типизируем handler clauses
  let handlerRow = Unify.removeConsFromRow eff blockFxs
  case handler of
    Handler _ _ clauses _ -> do
      let uniqueClauses = sort $ nub clauses
      if length clauses /= length uniqueClauses then
        throwError $ TypeError "Duplicate handler clause names"
      else
        let opNames = map fst ops in
        let clauseNames = map fst uniqueClauses in
        let missing = filter (`notElem` clauseNames) opNames in
        let extra = filter (`notElem` opNames) clauseNames in
        if missing /= [] then
          throwError $ TypeError $ "Handler missing operations: " ++ intercalate ", " missing
        else if extra /= [] then
          throwError $ TypeError $ "Handler defines unknown operations: " ++ intercalate ", " extra
        else
          -- TODO
          pure (TInt, EClosed [], scope)
    NativeHandler _ _ clauses _ -> do
      let uniqueClauses = sort $ nub clauses
      if length clauses /= length uniqueClauses then
        throwError $ TypeError "Duplicate handler clause names"
      else
        let opNames = map fst ops in
        let clauseNames = map fst uniqueClauses in
        let missing = filter (`notElem` clauseNames) opNames in
        let extra = filter (`notElem` opNames) clauseNames in
        if missing /= [] then
          throwError $ TypeError $ "Handler missing operations: " ++ intercalate ", " missing
        else if extra /= [] then
          throwError $ TypeError $ "Handler defines unknown operations: " ++ intercalate ", " extra
        else
          pure (TInt, EClosed [], scope)
{-
    let scope =
      List.fold_left2
        (fun sc (name, op_typ) (_, lam) ->
          (* op_typ = тип операции, например Int -> Int -> Int *)
          (* Разворачиваем его до формы TFunc(args, ret, fxs) *)
          let op_typ = TFunc op_typ in

          let rec replace_ret_with_block_t typ =
            match instantiate sc typ with
            | TFunc (i, o, fxs) -> TFunc (i, replace_ret_with_block_t o, fxs)
            | _ -> block_t
          in

          let op_typ_for_clause = replace_ret_with_block_t op_typ in

          let n_resume = count_resume_in_lambda lam in

          match n_resume with
          | MultipleResume n -> failwith @@ Printf.sprintf "Handler clause `%s` has multiple (%d) resume calls" name n
          | OneResume ->
            (* Добавляем resume: ret_t -> block_t *)
            let clause_scope = Scope.enter_scope sc in

            Scope.add_handler {eff; clauses = ops} clause_scope;
            Scope.add_binding "resume" (tfunc (ret_type_of op_typ) block_t) (Var "resume") true clause_scope;

            (* Теперь типизируем лямбду, где resume уже известен *)
            let lam_t, lam_fxs, lam_scope = infer_lambda lam clause_scope in

            (* Проверяем, что лямбда совместима с типом операции *)
            let sc = unify_types lam_t op_typ_for_clause lam_scope in
            unify_eff_rows lam_fxs (EClosed []) sc
          | NoResume ->
            (* Добавляем resume: ret_t -> block_t *)
            let clause_scope = Scope.enter_scope sc in
            let lam_t, lam_fxs, lam_scope = infer_lambda lam clause_scope in

            (* Проверяем, что лямбда совместима с типом операции *)
            let sc = unify_types lam_t block_t lam_scope in
            unify_eff_rows lam_fxs (EClosed []) sc
        )
        block_scope
        ops
        unique_clauses
    in

    let handler_row, scope =
      match then_ with
      | None -> handler_row, scope
      | Some then_ ->
        let then_t, then_fxs, then_scope = infer_lambda then_ scope in
        match instantiate then_scope then_t with
        | TFunc (i, o, _) ->
          let scope = unify_types i block_t then_scope in
          let handler_row = Eff.union_eff_rows handler_row then_fxs in
          handler_row, scope
        | _ -> failwith "then_ must be a function"
    in

    block_t, handler_row, scope

  | Resume expr ->
    (match Scope.find_binding ~uptop:true scope "resume" with
    | None -> raise @@ EffectError "Resume used outside of a handler clause!"
    | Some (resume_typ, _, _) ->
      match resume_typ with
      | TFunc (expected_i, expected_o, expected_fxs) ->
        let arg_t, arg_fxs, arg_scope = infer_expr scope expr in
        let scope' = unify_types arg_t expected_i arg_scope in
        expected_o, Eff.union_eff_rows arg_fxs expected_fxs, scope'
      | _ -> raise @@ EffectError "Invalid resume binding: not a function")
-}

inferLambda :: Scope -> Lambda -> TypeCheckM (Typ, EffRow, Scope)
inferLambda scope lam = do
  let scope1 = enterScope Nothing scope
  argT' <- maybe freshMetaTypeM pure lam.argT
  scope2 <- Scope.addBinding lam.arg argT' (XVar lam.arg) Val scope1
  retT' <- maybe freshMetaTypeM pure lam.retT
  (blockT, blockFxs, scope3) <- inferBlock scope2 lam.block
  scope4 <- unifyTypes scope3 retT' blockT
  scope5 <- unifyEffRows scope4 lam.fxs blockFxs
  pure (TFunc (argT', retT', lam.fxs), Eff.empty, scope5)

instantiateTypeScheme :: Scope -> TypeScheme -> TypeCheckM (Typ, Scope)
instantiateTypeScheme scope (Scheme tvars evars typ) = do
  -- 1. fresh meta vars
  freshTypes <- mapM (const freshMetaM) tvars
  freshEffects <- mapM (const freshMetaM) evars

  -- 2. extend scope with substitutions
  let scope' = scope {
    typeSubst = Map.union
      (Map.fromList [(tv, TVar mv) | (tv, mv) <- zip tvars freshTypes])
      (typeSubst scope),
    effSubst = Map.union
      (Map.fromList [(tv, EVar mv) | (tv, mv) <- zip evars freshEffects])
      (effSubst scope)
  }

  -- 3. applying
  typ' <- applyTypeSubst scope' typ
  pure (typ', scope')

-- instantiate :: Scope -> TypeScheme -> TypeCheckM (Typ, Scope)
-- instantiate scope (Scheme tvars evars typ) = do
--   let scope' = enterScope Nothing scope
--   freshTys <- mapM (const freshMetaM) tvars
--   freshEffs <- mapM (const freshMetaM) evars
--   scope'' <- foldM
--           (\sc t -> do
--             freshTyp <- freshSkolemM
--             pure sc {typeSubst = Map.insert t (TVar freshTyp) sc.typeSubst})
--           scope'
--           freshTys
--   scope''' <- foldM
--           (\sc t -> do
--             freshEff <- freshSkolemM
--             pure sc {effSubst = Map.insert t (EVar freshEff) sc.effSubst})
--           scope''
--           freshEffs
--   typ' <- applyTypeSubst scope typ
--   pure (typ', scope''')
  {-TForall types fxs typ -> do
    let scope' = enterScope Nothing scope

    freshTypes <- mapM (\_ -> do freshSkolemM) types
    freshEffects <- mapM (\_ -> do freshSkolemM) fxs

    scope'' <- foldM
          (\sc t -> do
            freshTyp <- freshSkolemM
            pure sc {typeSubst = Map.insert t (TVar freshTyp) sc.typeSubst})
          scope'
          freshTypes

    scope''' <- foldM
          (\sc t -> do
            freshEff <- freshSkolemM
            pure sc {effSubst = Map.insert t (EVar freshEff) sc.effSubst})
          scope''
          freshEffects
    instantiate scope''' typ
  TFunc (arg, ret, fxs) -> do
    (arg', scope1) <- instantiate scope arg
    (ret', scope2) <- instantiate scope1 ret
    (fxs', scope3) <- instantiateEff scope2 fxs
    pure (TFunc (arg', ret', fxs'), scope3)
  TList t -> do
    (t', scope') <- instantiate scope t
    pure (TList t', scope')
  TPair l r -> do
    (l', scope') <- instantiate scope l
    (r', scope'') <- instantiate scope' r
    pure (TPair l' r', scope'')
  TRecord props -> do
    (props', scope') <- foldM (
      \(props'', sc) (TRecordProp mut name typ) -> do
        (typ', sc') <- instantiate sc typ
        pure (TRecordProp mut name typ' : props'', sc')
      ) ([] :: [TRecordProp], scope) props
    pure (TRecord (sort props'), scope')
  t -> pure (t, scope)
  -}

instantiateEff :: Scope -> EffRow -> TypeCheckM (EffRow, Scope)
instantiateEff scope = \case
  EVar e -> case Map.lookup e scope.effSubst of
    Just eff -> instantiateEff scope eff
    Nothing -> pure (EVar e, scope)
  EClosed cons -> do
    (cons', scope') <- foldM processOne ([], scope) cons
    pure (EClosed $ reverse cons', scope')
  EOpen cons tail' -> do
    (cons', scope') <- foldM processOne ([], scope) cons
    let cons'' = reverse cons'

    case Map.lookup tail' scope'.effSubst of
      Just substEff -> instantiateEff scope' substEff
      Nothing -> pure (EOpen cons'' tail', scope')
  where
    processOne (acc, sc) (name, params) = do
      (params', sc') <- mapAccumM instantiate sc params
      pure ((name, params') : acc, sc')

inferNativeBlock :: Scope -> NativeBlock -> TypeCheckM (Typ, EffRow, Scope)
inferNativeBlock scope (typ, expr) = do
  (exprT, exprFxs, scope') <- inferExpr scope expr
  scope'' <- unifyTypes scope' typ exprT
  pure (exprT, exprFxs, scope'')

inferBlock :: Scope -> Block -> TypeCheckM (Typ, EffRow, Scope)
inferBlock scope (stats, expr) = do
  (scopeAfterStats, statFxs) <- foldM (\(sc, accFxs) stat -> do
      (_, fxs, sc') <- inferStat sc stat
      pure (sc', Eff.unionEffRows accFxs fxs)
    ) (scope, Eff.empty) stats
  (exprT, exprFxs, scope') <- inferExpr scopeAfterStats expr
  pure (exprT, Eff.unionEffRows statFxs exprFxs, scope')

inferStat :: Scope -> Stat -> TypeCheckM (Typ, EffRow, Scope)
inferStat scope stat = throwError $ TypeError "TODO: inferStat"

unifyEffRows :: Scope -> EffRow -> EffRow -> TypeCheckM Scope
unifyEffRows scope e1 e2 = throwError $ TypeError "TODO: unifyEffRows"

{-
and infer_stat (scope : scope) : stat -> typ * eff_row * scope = function
  | Bind (is_val, name, typ_opt, expr) ->
    (* 1) вывести тип expr *)
    let inferred_t, inferred_fxs, inferred_scope = infer_expr scope expr in
    print_endline ("INFERRED : " ^ Debug.type_to_string inferred_t);

    (* 2) подготовить expected_t для проверки:
        - если пользователь дал аннотацию typ_opt:
            * если это полиморфная аннотация (TForall), то для проверки
              мы сначала INSTANTIATE её (получаем монотипную версию),
              затем унифицируем с inferred_t;
            * после успешной проверки в scope кладём именно ОРИГИНАЛЬНУЮ
              аннотацию (annot), а не инстанцированный вариант.
        - если аннотации нет — создаём fresh tv для унификации и
          позже, при is_val = true, generalize result.
    *)
    let (expected_for_unify, binding_t_for_scope) =
      match typ_opt with
      | Some annot ->
          (* для проверки инстанцируем аннотацию *)
          let annot_inst = instantiate inferred_scope annot in
          annot_inst, annot (* в scope кладём саму аннотацию *)
      | None ->
          let tv = fresh_type_var () in
          (tv, tv)
    in

    Printf.printf "DEBUG Bind %s: inferred=%s expected_for_unify=%s\n"
      name (Debug.type_to_string inferred_t) (Debug.type_to_string expected_for_unify);


    (* 3) унифицируем *)
    let scope_after_unify = unify_types inferred_t expected_for_unify inferred_scope in

    (* 4) если это значение и не было явной аннотации — generalize *)
    let final_binding_t =
      if typ_opt = None && is_val then
        generalize scope_after_unify binding_t_for_scope
      else
        (* либо — оставляем аннотацию (если она дана), либо монотип tv *)
        binding_t_for_scope
    in

    (* 5) добавляем binding (final_binding_t — уже либо forall, либо монотип) *)
    Scope.add_binding name final_binding_t expr is_val scope_after_unify;

    final_binding_t, inferred_fxs, scope_after_unify

  | Assign (name, expr) ->
    let var_t = match Scope.find_binding ~uptop:true scope name with
      | Some (t, _, false) -> t
      | Some (_, _, true) -> raise (ImmutableVariableAssignment name)
      | _ -> raise (UndefinedVariable name)
    in
    let inferred_t, inferred_fxs, inferred_scope = infer_expr scope expr in
    var_t, inferred_fxs, unify_types var_t inferred_t inferred_scope
  | Expr e -> infer_expr scope e
-}

-- converts a function type with free type variables to forall type
generalize :: Scope -> Typ -> TypeCheckM Typ
generalize scope = \case
  f@(TFunc _) ->
    let tvars = filter (\v -> v `Map.notMember` scope.typeSubst) $ collectTvarsFromType [] f in
    let evars = filter (\v -> v `Map.notMember` scope.effSubst) $ collectEvarsFromType [] f in
    if null tvars && null evars then
      pure f
    else
      TForall tvars evars <$> applyTypeSubst scope f
  TForall tv ev t -> TForall tv ev <$> generalize (enterScope Nothing scope) t
  t -> pure t

{-
  | TForall (tv, ev, t) -> TForall (tv, ev, generalize (Scope.enter_scope scope) t)
  | t ->
    let tvars = collect_tvars_from_type t in
    let evars = collect_evars_from_type t in
    match tvars, evars with
    | [], [] -> t
    | [], es ->
      Printf.sprintf "Unbound eff vars {%s} in type `%s`"
      (String.concat "; " es)
      (Debug.type_to_string t)
      |> failwith
    | ts, [] ->
      Printf.sprintf "Unbound type vars [%s] in type `%s`"
      (String.concat " " ts)
      (Debug.type_to_string t)
      |> failwith
    | ts, es ->
      Printf.sprintf "Unbound eff vars [%s] and type vars {%s} in type `%s`"
      (String.concat " " ts)
      (String.concat "; " es)
      (Debug.type_to_string t)
      |> failwith
-}

collectTvarsFromType :: [Taste] -> Typ -> [Taste]
collectTvarsFromType except typ =
  uniqPreserveOrder $ case typ of
    TList t -> collectTvarsFromType except t
    TPair l r -> collectTvarsFromType except l ++ collectTvarsFromType except r
    TFunc (i, o, fxs) ->
      collectTvarsFromType except i
      ++ collectTvarsFromType except o
      ++ collectTvarsFromFx except fxs
    TForall vars _ t -> collectTvarsFromType (uniqPreserveOrder $ vars ++ except) t
    TRecord props ->
      concatMap (collectTvarsFromType except . tTyp) props
    TVar v -> ([v | v `notElem` except])
    _ -> []

collectTvarsFromFx :: [Taste] -> EffRow -> [Taste]
collectTvarsFromFx except fx =
  uniqPreserveOrder $ case fx of
    EVar _ -> []
    EClosed cons ->
      concatMap (concatMap (collectTvarsFromType except) . snd) cons
    EOpen cons _ ->
      concatMap (concatMap (collectTvarsFromType except) . snd) cons

collectEvarsFromType :: [Taste] -> Typ -> [Taste]
collectEvarsFromType except typ =
  uniqPreserveOrder $ case typ of
    TList t -> collectEvarsFromType except t
    TPair l r -> collectEvarsFromType except l ++ collectEvarsFromType except r
    TFunc (i, o, fxs) ->
      collectEvarsFromType except i
      ++ collectEvarsFromType except o
      ++ collectEvarsFromFx except fxs
    TForall _ fxs t -> collectEvarsFromType (uniqPreserveOrder $ fxs ++ except) t
    TRecord props ->
      concatMap (collectEvarsFromType except . tTyp) props
    _ -> []

collectEvarsFromFx :: [Taste] -> EffRow -> [Taste]
collectEvarsFromFx except fx =
  uniqPreserveOrder $ case fx of
    EVar e -> [e | e `notElem` except]
    EClosed cons ->
      concatMap (concatMap (collectEvarsFromType except) . snd) cons
    EOpen cons tail ->
      (\l -> l ++ [tail | tail `notElem` except]) $
      concatMap (concatMap (collectEvarsFromType except) . snd) cons
-}