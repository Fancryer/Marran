{-# LANGUAGE LambdaCase #-}

module Occurs (
  typeOccursInType,
  typeOccursInEffRow,
  effOccursInEffRow,
  effRowContainsEffects,
  effConsContainsEffects
) where
import Types (Typ(..), EffRow(..), Taste, EffRow, EffCons, TRecordProp (..))

typeOccursInType :: Taste -> Typ -> Bool
typeOccursInType x = \case
  TVar y -> x == y
  TList t -> typeOccursInType x t
  TPair l r -> any (typeOccursInType x) [l, r]
  TFunc (i, o, fx) -> any (typeOccursInType x) [i, o] || typeOccursInEffRow x fx
  TForall ts _ typ -> notElem x ts && typeOccursInType x typ
  TRecord props -> any (\(TRecordProp _ _ typ) -> typeOccursInType x typ) props
  _ -> False

typeOccursInEffRow :: Taste -> EffRow -> Bool
typeOccursInEffRow x = \case
  EOpen labels _ -> any (any (typeOccursInType x) . snd) labels
  EClosed labels -> any (any (typeOccursInType x) . snd) labels
  _ -> False

effOccursInEffRow :: Taste -> EffRow -> Bool
effOccursInEffRow x = \case
  EVar y -> x == y
  EOpen _ t -> x == t
  _ -> False -- Closed row doesn't contain evar

effRowContainsEffects :: EffRow -> Bool
effRowContainsEffects = \case
  EOpen labels _ -> any effConsContainsEffects labels
  EClosed labels -> any effConsContainsEffects labels
  _ -> False

effConsContainsEffects :: EffCons -> Bool
effConsContainsEffects (_, params) = flip any params $
  \case
    TFunc (i, o, EClosed []) -> any typeContainsEffects [i, o]
    TFunc (_, _, EOpen [] _) -> False
    TFunc (_, _, _) -> True
    _ -> False

typeContainsEffects :: Typ -> Bool
typeContainsEffects = \case
  TFunc (i, o, fxs) ->
    any typeContainsEffects [i, o] || effRowContainsEffects fxs
  TList t -> typeContainsEffects t
  TPair l r -> any typeContainsEffects [l, r]
  TForall _ es t -> es /= [] || typeContainsEffects t
  TRecord props -> any (\(TRecordProp _ _ typ) -> typeContainsEffects typ) props
  _ -> False


{-
and eff_cons_in_eff_row cons = function
  | EClosed fxs | EOpen (fxs, _) -> List.exists (Compare.eq_eff_cons cons) fxs
  | EVar _ -> false
-}