{-# LANGUAGE LambdaCase #-}

module Occurs (
  typeOccursInType,
  typeOccursInTypeArg,
  typeOccursInEffRow,
  rowOccursInEffRow,
  typeContainsEffects
) where
import Types (Typ(..), EffRow(..), Taste, EffRow, TRecordProp (..), Funct (..), TypeArg (..), TARecordProp (TARecordProp), EffCons (..), ECons (..), typeArgToTyp)

-- | Does the type (or the pending row of an aggregate) mention this type
--   variable?
typeOccursInType :: Taste -> Typ -> Bool
typeOccursInType x = \case
  TVar y -> x == y
  TArray t r -> typeOccursInType x t || typeOccursInEffRow x r
  TPair l r fx ->
    any (typeOccursInType x) [l, r] || typeOccursInEffRow x fx
  TFunct (Funct i o fx) -> any (typeOccursInType x) [i, o] || typeOccursInEffRow x fx
  TForall ts _ _ _ _ typ -> notElem x ts && typeOccursInType x typ
  TRecord props r ->
    any (\(TRecordProp _ _ typ) -> typeOccursInType x typ) props
      || typeOccursInEffRow x r
  TEnum _ args -> any (typeOccursInTypeArg x) args
  _ -> False

typeOccursInTypeArg :: Taste -> TypeArg -> Bool
typeOccursInTypeArg x = \case
  TAVar y -> x == y
  TAArray t -> typeOccursInTypeArg x t
  TAPair l r -> any (typeOccursInTypeArg x) [l, r]
  TAFunct i o -> any (typeOccursInTypeArg x) [i, o]
  TARecord props -> any (\(TARecordProp _ _ typ) -> typeOccursInTypeArg x typ) props
  TAEnum _ args -> any (typeOccursInTypeArg x) args
  _ -> False

typeOccursInEffRow :: Taste -> EffRow -> Bool
typeOccursInEffRow x = \case
  ROpen labels _ -> any (\case
    EffCons (ECons _ args) -> any (typeOccursInTypeArg x) args
    EVar _ -> False) labels
  RClosed labels -> any (\case
    EffCons (ECons _ args) -> any (typeOccursInTypeArg x) args
    EVar _ -> False) labels
  RVar _ -> False

rowOccursInEffRow :: Taste -> EffRow -> Bool
rowOccursInEffRow x = \case
  ROpen _ t -> x == t
  _ -> False -- Closed row doesn't contain evar

typeContainsEffects :: Typ -> Bool
typeContainsEffects = \case
  TFunct (Funct i o _) -> any typeContainsEffects [i, o]
  TArray t _ -> typeContainsEffects t
  TPair l r _ -> any typeContainsEffects [l, r]
  TForall _ es rs _ _ t -> es /= [] || rs /= [] || typeContainsEffects t
  TRecord props _ -> any (\(TRecordProp _ _ typ) -> typeContainsEffects typ) props
  TEnum _ args -> any (typeContainsEffects . typeArgToTyp) args
  _ -> False
