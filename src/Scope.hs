{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OrPatterns #-}

module Scope (
  enterScope,
  leaveScope,
  isTopLevel,
  findBinding,
  findType,
  findEff,
  findHandler,
  findEffOps,
  hasBinding,
  hasType,
  hasEff,
  hasHandler,
  addBinding,
  addType,
  addEffect,
  addHandler
)

where
import Types (HandlerSig, Scope(..), Mutability, Expr, Typ, EffDecl (EffDecl, EffAlias), EffCons, Func, TypeScheme)
import qualified Data.Map as Map
import Control.Monad.Except (Except, MonadError (throwError))
import Unify (TypeCheckM, TypeCheckError (SameScopeBindingShadowing))
import qualified Data.Maybe as Maybe

enterScope :: Maybe HandlerSig -> Scope -> Scope
enterScope sig scope = Scope
  Map.empty
  Map.empty
  Map.empty
  sig
  scope.typeSubst
  scope.effSubst
  (Just scope)

leaveScope :: Scope -> Except String Scope
leaveScope sc = case sc.parent of
  Nothing -> throwError "Cannot leave empty scope"
  Just p -> pure p

isTopLevel :: Bool -> Scope -> Bool
isTopLevel canBeGlobal sc = case sc.parent of
  Nothing -> canBeGlobal
  Just p -> isTopLevel False p

findBinding :: Bool -> Scope -> String -> Maybe (TypeScheme, Expr, Mutability)
findBinding uptop sc name =
  case (Map.lookup name sc.values, uptop, sc.parent) of
    (s@(Just _), _, _) -> s
    (Nothing, True, Just p) -> findBinding True p name
    _ -> Nothing

findType :: Bool -> Scope -> String -> Maybe Typ
findType uptop sc name =
  case (Map.lookup name sc.types, uptop, sc.parent) of
    (s@(Just _), _, _) -> s
    (Nothing, True, Just p) -> findType True p name
    _ -> Nothing

findEff :: Bool -> Scope -> String -> Maybe EffDecl
findEff uptop sc name =
  case (Map.lookup name sc.effects, uptop, sc.parent) of
    (s@(Just _), _, _) -> s
    (Nothing, True, Just p) -> findEff True p name
    _ -> Nothing

findHandler :: Bool -> Scope -> Maybe HandlerSig
findHandler uptop sc =
  case (sc.handlerSig, uptop, sc.parent) of
    (s@(Just _), _, _) -> s
    (Nothing, True, Just p) -> findHandler True p
    _ -> Nothing

findEffOps :: Bool -> Scope -> EffCons -> Maybe [(String, Func)]
findEffOps uptop sc (name, _) =
  case findEff uptop sc name of
    (Nothing; Just (EffAlias _ _)) -> Nothing
    Just (EffDecl _ _ ops) -> Just ops

hasBinding :: Bool -> Scope -> String -> Bool
hasBinding uptop scope name = Maybe.isJust $ findBinding uptop scope name

hasType :: Bool -> Scope -> String -> Bool
hasType uptop scope name = Maybe.isJust $ findType uptop scope name

hasEff :: Bool -> Scope -> String -> Bool
hasEff uptop scope name = Maybe.isJust $ findEff uptop scope name

hasHandler :: Bool -> Scope -> Bool
hasHandler uptop scope = Maybe.isJust $ findHandler uptop scope

addBinding :: String -> TypeScheme -> Expr -> Mutability -> Scope -> TypeCheckM Scope
addBinding name typ expr mut scope =
  if hasBinding False scope name then
    throwError $ SameScopeBindingShadowing $ "Cannot shadow a `" ++ name ++"` binding in the same scope!"
  else
    pure $ scope {values = Map.insert name (typ, expr, mut) scope.values}

addType :: String -> Typ -> Scope -> TypeCheckM Scope
addType name typ scope =
  if hasType False scope name then
    throwError $ SameScopeBindingShadowing $ "Cannot shadow a `" ++ name ++"` type in the same scope!"
  else
    pure $ scope {types = Map.insert name typ scope.types}

addEffect :: EffDecl -> Scope -> TypeCheckM Scope
addEffect effDecl scope =
  let name = case effDecl of
        EffDecl name' _ _-> name'
        EffAlias name' _ -> name'
  in
  if hasEff False scope name then
    throwError $ SameScopeBindingShadowing $ "Cannot shadow an `" ++ name ++"` effect in the same scope!"
  else
    pure $ scope {effects = Map.insert name effDecl scope.effects}

addHandler :: HandlerSig -> Scope -> TypeCheckM Scope
addHandler sig scope =
  if hasHandler False scope then
    throwError $ SameScopeBindingShadowing "Cannot shadow an effect handler in the same scope!"
  else
    pure $ scope {handlerSig = Just sig}


{-
let global_scope =
  let scope = let open Hashtbl in ref {
    types = create 16;
    values = create 16;
    effects = create 16;
    handler_sig = Some Eff.global_handler_sig;
    type_subst = create 16;
    eff_subst = create 16;
    parent = None
  } in
  let (pred_name, pred_type, pred_value, pred_is_val) =
    "pred",
    TFunc (TInt, TInt, Eff.empty_eff_row),
    (* (string * typ option) * typ option * eff_row *)
    NativeLambda {
      sign = (("x", Some TInt), Some TInt, EClosed []);
      lam = fun x ->
        match x with
        | Int i -> Int (i - 1)
        | _ -> raise (TypeError "Cannot happen")
    },
    true
  in
  add_binding pred_name pred_type pred_value pred_is_val !scope;
  add_binding
    "say"
    (TForall (["a"], [], TFunc (TVar (Skolem "a"), TNil,  Eff.fx_output)))
    (NativeLambda {
      sign = ("x", Some (TVar (Skolem "a"))), Some TNil, EClosed [];
      lam = fun x -> print_endline (Debug.expr_to_string x); Nil
    })
    true
    !scope;
  add_binding
    "args"
    (TList TString)
    (List (Sys.argv |> Array.to_list |> List.map (fun s -> String s)))
    true
    !scope;
  add_binding
    "+"
    (pure_func [TInt; TInt; TInt])
    (NativeLambda {
      sign =
        ("a", Some TInt),
        Some (tfunc TInt TInt),
        EClosed [];
      lam = fun a -> NativeLambda {
        sign = ("b", Some TInt), Some TInt, EClosed [];
        lam = fun b -> match a, b with
        | Int a, Int b -> Int (a + b)
        | _ -> raise (TypeError "Cannot happen")
      }
    })
    true
    !scope;
  add_binding
    "-"
    (pure_func [TInt; TInt; TInt])
    (NativeLambda {
      sign =
        ("a", Some TInt),
        Some (tfunc TInt TInt),
        EClosed [];
      lam = fun a -> NativeLambda {
        sign = ("b", Some TInt), Some TInt, EClosed [];
        lam = fun b -> match a, b with
        | Int a, Int b -> Int (a - b)
        | _ -> raise (TypeError "Cannot happen")
      }
    })
    true
    !scope;
  !scope
-}