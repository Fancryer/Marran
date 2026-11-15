{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Scope (
  enterScope,
  leaveScope,
  keepSubst,
  isTopLevel,
  findBinding,
  findBindingWithRow,
  findType,
  findEff,
  findHandler,
  findEffOps,
  hasBinding,
  hasType,
  hasEff,
  hasHandler,
  addBinding,
  addBindingWithRow,
  bindLocal,
  findOperations,
  operationNames,
  addType,
  addEffect,
  addHandler,
  bindingNames,
  typeNames,
  effectNames,
  globalScope
)
where

import Types (
    HandlerSig,
    Mutability(..),
    Typ(..),
    TRecordProp(..),
    EffDef(..),
    Funct(..),
    TypeScheme,

    EffRow(RClosed, ROpen, RVar),
    Scheme(Scheme),
    Expr(..), NativeLambdaSign (..), tfunc, _a,
    Taste,
    pattern NLambda
  )
import TypedIR (Scope(..), ValueBinding(..))
import Control.Monad (foldM, unless)
import qualified Data.Text as T
import qualified Builtins
import qualified Data.Map as Map
import Control.Monad.Except (Except, throwError)
import Unify (TypeCheckM, TypeCheckError (SameScopeBindingShadowing, InferenceError), freshBoundM, freshMetaM, throwTypeCheckError)
import qualified Data.Maybe as Maybe
import Data.Text (Text)
import qualified Eff
import Eff (label)

enterScope :: Scope -> Scope
enterScope scope = Scope
  Map.empty
  Map.empty
  Map.empty
  Nothing
  scope.typeSubst
  scope.typeArgSubst
  scope.effSubst
  scope.rowSubst
  scope.rowLacks
  scope.effLacks
  (Just scope)

leaveScope :: Scope -> Except String Scope
leaveScope sc = case sc.parent of
  Nothing -> throwError "Cannot leave empty scope"
  Just p -> pure p

-- | Выйти из внутренней области: вернуть внешнюю, сохранив накопленные подстановки.
--   Унификация записывает результат в Scope, поэтому при выходе из области
--   нельзя просто взять родителя: подстановки были бы потеряны.
keepSubst :: Scope -> Scope -> Scope
keepSubst inner outer = outer {
    typeSubst    = inner.typeSubst,
    typeArgSubst = inner.typeArgSubst,
    effSubst     = inner.effSubst,
    rowSubst     = inner.rowSubst
  }

isTopLevel :: Bool -> Scope -> Bool
isTopLevel canBeGlobal sc = case sc.parent of
  Nothing -> canBeGlobal
  Just p -> isTopLevel False p

findBinding :: Bool -> Scope -> Text -> Maybe (TypeScheme, Expr, Mutability)
findBinding uptop sc name =
  (\(ValueBinding scheme expr mut _) -> (scheme, expr, mut)) <$>
    findBindingWithRow uptop sc name

-- | Like 'findBinding', but also returns the pending row of the binding.
findBindingWithRow :: Bool -> Scope -> Text -> Maybe ValueBinding
findBindingWithRow uptop sc name =
  case (Map.lookup name sc.values, uptop, sc.parent) of
    (s@(Just _), _, _) -> s
    (Nothing, True, Just p) -> findBindingWithRow True p name
    _ -> Nothing

findType :: Bool -> Scope -> Text -> Maybe Typ
findType uptop sc name =
  case (Map.lookup name sc.types, uptop, sc.parent) of
    (s@(Just _), _, _) -> s
    (Nothing, True, Just p) -> findType True p name
    _ -> Nothing

findEff :: Bool -> Scope -> Text -> Maybe EffDef
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

findEffOps :: Bool -> Scope -> Text -> Maybe [(Text, Funct)]
findEffOps uptop sc name =
  case findEff uptop sc name of
    Just (EffDef _ _ ops) -> Just ops
    Nothing -> Nothing

hasBinding :: Bool -> Scope -> Text -> Bool
hasBinding uptop scope name = Maybe.isJust $ findBinding uptop scope name

hasType :: Bool -> Scope -> Text -> Bool
hasType uptop scope name = Maybe.isJust $ findType uptop scope name

hasEff :: Bool -> Scope -> Text -> Bool
hasEff uptop scope name = Maybe.isJust $ findEff uptop scope name

hasHandler :: Bool -> Scope -> Bool
hasHandler uptop scope = Maybe.isJust $ findHandler uptop scope

-- | All value names visible from here, nearest scope first and without
--   duplicates.  This is what a "did you mean?" suggestion searches: a name
--   bound in an inner scope must not be suggested twice, and it must win over
--   an outer binding of the same name.
bindingNames :: Scope -> [Text]
bindingNames = namesOf values

-- | All type names visible from here, for a suggestion about a type.
typeNames :: Scope -> [Text]
typeNames = namesOf types

-- | All effect names visible from here.
effectNames :: Scope -> [Text]
effectNames = namesOf effects

-- | The keys of one of the three maps, walking the chain of enclosing scopes
--   and keeping the first occurrence of every name.
namesOf :: (Scope -> Map.Map Text a) -> Scope -> [Text]
namesOf field = go
  where
    go scope =
      let here = Map.keys (field scope)
          outer = maybe [] go scope.parent
      in here <> filter (`notElem` here) outer

addBinding :: Text -> TypeScheme -> Expr -> Mutability -> Scope -> TypeCheckM Scope
addBinding name typ expr mut = addBindingWithRow name typ expr mut Eff.empty

-- | Add a binding together with its pending row.  Most callers (declarations,
--   builtins, operation names) have no delayed computation to force and use
--   'addBinding'; the statement checker uses this one for @val@, @var@ and
--   @imm@ bindings.
addBindingWithRow :: Text -> TypeScheme -> Expr -> Mutability -> EffRow -> Scope -> TypeCheckM Scope
addBindingWithRow name typ expr mut row scope =
  if hasBinding False scope name then
    throwTypeCheckError $ SameScopeBindingShadowing $ "Cannot shadow a `" <> name <> "` binding in the same scope!"
  else
    pure $ scope {values = Map.insert name (ValueBinding typ expr mut row) scope.values}

-- | Insert a binding, shadowing whatever the current scope already has under
--   that name.
--
--   The checker's own bookkeeping uses this, not programs: an operation name
--   is a legitimate collision (two effects may declare the same operation, and
--   a row then decides which one a use means), while a user declaration that
--   repeats a name in one scope is a mistake 'addBinding' reports.
bindLocal :: Text -> TypeScheme -> Expr -> Mutability -> Scope -> Scope
bindLocal name typ expr mut scope =
  scope {values = Map.insert name (ValueBinding typ expr mut Eff.empty) scope.values}

-- | The operations this name denotes, from the innermost scope that declares
--   any.
--
--   An operation is not a value binding: `effect A` and `effect B` may both
--   declare `ping`, and which one a use means is decided by the row, not by the
--   order of declarations.  A real binding of the same name — an argument, or
--   the operation a row licensed — shadows this, and callers look in
--   'findBinding' first.
findOperations :: Bool -> Scope -> Text -> [(Text, [Taste], Funct)]
findOperations uptop scope name = go scope
  where
    go :: Scope -> [(Text, [Taste], Funct)]
    go sc = case here sc of
      [] -> case (uptop, sc.parent) of
        (True, Just p) -> go p
        _ -> []
      found -> found

    here :: Scope -> [(Text, [Taste], Funct)]
    here sc =
      [ (effN, params, opType)
      | (effN, EffDef _ params ops) <- Map.toList sc.effects
      , (opN, opType) <- ops
      , opN == name
      ]

-- | Every operation name the declared effects in scope provide, for a "did you
--   mean?" hint when a name is not bound.
operationNames :: Scope -> [Text]
operationNames = go
  where
    go :: Scope -> [Text]
    go sc =
      let here' =
            [ opN
            | EffDef _ _ ops <- Map.elems sc.effects
            , (opN, _) <- ops
            ]
          outer = maybe [] go sc.parent
      in here' <> filter (`notElem` here') outer

addType :: Text -> Typ -> Scope -> TypeCheckM Scope
addType name typ scope =
  if hasType False scope name then
    throwTypeCheckError $ SameScopeBindingShadowing $ "Cannot shadow a `" <> name <> "` type in the same scope!"
  else
    pure $ scope {types = Map.insert name typ scope.types}

addEffect :: EffDef -> Scope -> TypeCheckM Scope
addEffect effDef@(EffDef name _ _) scope =
  if hasEff False scope name then
    throwTypeCheckError $ SameScopeBindingShadowing $ "Cannot shadow an `" <> name <> "` effect in the same scope!"
  else
    pure $ scope {effects = Map.insert name effDef scope.effects}

addHandler :: HandlerSig -> Scope -> TypeCheckM Scope
addHandler sig scope =
  if hasHandler False scope then
    throwTypeCheckError $ SameScopeBindingShadowing "Cannot shadow an effect handler in the same scope!"
  else
    pure $ scope {handlerSig = Just sig}

-- | The initial scope.
--
--   The type of every builtin lives here; the interpreter gives the same
--   names their values and operations.  'Builtins.builtins' is the list the
--   two sides are checked against, so a name that is added on one side only is
--   reported while the scope is built rather than when a program first calls
--   it.
globalScope :: [Text] -> TypeCheckM Scope
globalScope _args = do
  boundSay <- freshBoundM
  boundSayn <- freshBoundM
  boundTrace <- freshBoundM
  boundForce <- freshBoundM
  boundWhnf <- freshBoundM

  boundError <- freshBoundM
  -- `exit` never returns, so its result is the bottom of every type.
  boundExit <- freshBoundM

  -- The polymorphic groups of `app/std.marr`, unpacked into the native scope.
  --
  -- A record's fields are inferred at a single type ('Infer.inferRecord'), so
  -- a field cannot be quantified; these names are therefore plain functions.
  -- Every variable below is a meta that the scheme quantifies, so each use
  -- gets fresh ones.  A row variable is a meta for the same reason, and also
  -- because 'Unify.applyEffRowSubst' resolves rows through 'rowSubst' only for
  -- metas: a rigid row variable in a scheme would never be freshened.
  polyEntries <- do
    -- `Functions`
    idT <- freshMetaM
    constA <- freshMetaM
    constB <- freshMetaM
    flipA <- freshMetaM
    flipB <- freshMetaM
    flipC <- freshMetaM
    flipR <- freshMetaM
    compA <- freshMetaM
    compB <- freshMetaM
    compC <- freshMetaM
    compR <- freshMetaM
    appA <- freshMetaM
    appB <- freshMetaM
    appR <- freshMetaM
    curryA <- freshMetaM
    curryB <- freshMetaM
    curryC <- freshMetaM
    curryR <- freshMetaM
    uncurryA <- freshMetaM
    uncurryB <- freshMetaM
    uncurryC <- freshMetaM
    uncurryR <- freshMetaM

    -- `Arrays`
    headT <- freshMetaM
    headR <- freshMetaM
    tailT <- freshMetaM
    tailR <- freshMetaM
    emptyT <- freshMetaM
    emptyR <- freshMetaM
    alenT <- freshMetaM
    alenR <- freshMetaM
    mapA <- freshMetaM
    mapB <- freshMetaM
    mapR <- freshMetaM
    mapR0 <- freshMetaM
    filterT <- freshMetaM
    filterR <- freshMetaM
    filterR0 <- freshMetaM
    anyT <- freshMetaM
    anyR <- freshMetaM
    anyR0 <- freshMetaM
    allT <- freshMetaM
    allR <- freshMetaM
    allR0 <- freshMetaM
    foldlA <- freshMetaM
    foldlB <- freshMetaM
    foldlR <- freshMetaM
    foldlR0 <- freshMetaM
    foldrA <- freshMetaM
    foldrB <- freshMetaM
    foldrR <- freshMetaM
    foldrR0 <- freshMetaM
    concatT <- freshMetaM
    concatR0 <- freshMetaM
    concatR1 <- freshMetaM
    zipA <- freshMetaM
    zipB <- freshMetaM
    zipR0 <- freshMetaM
    zipR1 <- freshMetaM
    zipR2 <- freshMetaM
    atT <- freshMetaM
    atR <- freshMetaM
    takeT <- freshMetaM
    takeR <- freshMetaM
    dropT <- freshMetaM
    dropR <- freshMetaM

    -- `Pairs`, `Conv`
    fstL <- freshMetaM
    fstR <- freshMetaM
    sndL <- freshMetaM
    sndR <- freshMetaM
    fstRow <- freshMetaM
    sndRow <- freshMetaM
    showT <- freshMetaM

    -- `Error@try`
    tryA <- freshMetaM
    tryR <- freshMetaM

    let t = TVar
        -- a function whose latent row is `rw`; an empty row is a pure one
        fn = tfunc
        fnR i o rw = TFunct (Funct i o (RVar rw))
        -- an array of `x` whose elements may cost `rw`
        arr x rw = TArray (TVar x) (RVar rw)
        arrT ty rw = TArray ty (RVar rw)
        -- a builtin whose types and rows are both quantified
        poly name tvs rvs typ = (name, tvs, rvs, typ)

        functions =
          [ poly "id" [idT] [] $ fn (t idT) (t idT)
          , poly "const" [constA, constB] [] $ fn (t constA) (fn (t constB) (t constA))
          -- `flip` applies the function it is given, so its row is `R`; the
          -- two arrows of the result are pure, because building the closures
          -- performs nothing.
          , poly "flip" [flipA, flipB, flipC] [flipR] $
              fn (fnR (t flipA) (fnR (t flipB) (t flipC) flipR) flipR)
                 (fn (t flipB) (fnR (t flipA) (t flipC) flipR))
          , poly "compose" [compA, compB, compC] [compR] $
              fn (fnR (t compB) (t compC) compR)
                 (fn (fnR (t compA) (t compB) compR)
                     (fnR (t compA) (t compC) compR))
          -- `apply` is the opposite: it applies at once, so the row of the
          -- returned function is paid by the call.
          , poly "apply" [appA, appB] [appR] $
              fn (fnR (t appA) (t appB) appR) (fnR (t appA) (t appB) appR)
          , poly "curry" [curryA, curryB, curryC] [curryR] $
              fn (fnR (TPair (t curryA) (t curryB) (RClosed [])) (t curryC) curryR) $
                fn (t curryA) (fnR (t curryB) (t curryC) curryR)
          , poly "uncurry" [uncurryA, uncurryB, uncurryC] [uncurryR] $
              fn (fnR (t uncurryA) (fnR (t uncurryB) (t uncurryC) uncurryR) uncurryR)
                 (fnR (TPair (t uncurryA) (t uncurryB) (RClosed [])) (t uncurryC) uncurryR)
          ]

        arrays =
          [ poly "head" [headT] [headR] $ fn (arr headT headR) (t headT)
          , poly "tail" [tailT] [tailR] $ fn (arr tailT tailR) (arr tailT tailR)
          , poly "empty" [emptyT] [emptyR] $ fn (arr emptyT emptyR) TBoolean
          , poly "alen" [alenT] [alenR] $ fn (arr alenT alenR) TInt
          -- The element row of the input is its own variable, not the row the
          -- function costs: tying them together would make the result of
          -- `map sayn []` depend on the order the two are unified in.
          , poly "map" [mapA, mapB] [mapR, mapR0] $
              fn (fnR (t mapA) (t mapB) mapR)
                 (fnR (arr mapA mapR0) (arr mapB mapR) mapR)
          , poly "filter" [filterT] [filterR, filterR0] $
              fn (fnR (t filterT) TBoolean filterR)
                 (fnR (arr filterT filterR0) (arr filterT filterR0) filterR)
          , poly "any" [anyT] [anyR, anyR0] $
              fn (fnR (t anyT) TBoolean anyR)
                 (fnR (arr anyT anyR0) TBoolean anyR)
          , poly "all" [allT] [allR, allR0] $
              fn (fnR (t allT) TBoolean allR)
                 (fnR (arr allT allR0) TBoolean allR)
          , poly "foldl" [foldlA, foldlB] [foldlR, foldlR0] $
              fn (fn (t foldlB) (fnR (t foldlA) (t foldlB) foldlR))
                 (fn (t foldlB) (fnR (arr foldlA foldlR0) (t foldlB) foldlR))
          , poly "foldr" [foldrA, foldrB] [foldrR, foldrR0] $
              fn (fn (t foldrA) (fnR (t foldrB) (t foldrB) foldrR))
                 (fn (t foldrB) (fnR (arr foldrA foldrR0) (t foldrB) foldrR))
          , poly "concat" [concatT] [concatR0, concatR1] $
              fn (arrT (TArray (TVar concatT) (RVar concatR1)) concatR0) (arr concatT concatR1)
          , poly "zip" [zipA, zipB] [zipR0, zipR1, zipR2] $
              fn (arr zipA zipR0) (fn (arr zipB zipR1) (TPair (TVar zipA) (TVar zipB) (RVar zipR2)))
          -- `at` reports an out-of-range index through `Error`, as the
          -- standard library says.
          , poly "at" [atT] [atR] $ fn (arr atT atR) (TFunct $ Funct TInt (TVar atT) Eff.fxError)
          , poly "take" [takeT] [takeR] $ fn TInt (fn (arr takeT takeR) (arr takeT takeR))
          , poly "drop" [dropT] [dropR] $ fn TInt (fn (arr dropT dropR) (arr dropT dropR))
          ]

        pairs =
          [ poly "fst" [fstL, fstR] [fstRow] $ fn (TPair (TVar fstL) (TVar fstR) (RVar fstRow)) (TVar fstL)
          , poly "snd" [sndL, sndR] [sndRow] $ fn (TPair (TVar sndL) (TVar sndR) (RVar sndRow)) (TVar sndR)
          ]

        convs =
          [ poly "show" [showT] [] $ fn (t showT) TString
          -- `try` runs its body with an `Error` handler installed and hands a
          -- caught message to the second function; the row it costs is the row
          -- of the body without `Error`, which is the same row the handler
          -- calls.  Both arguments are functions and the result is evaluated,
          -- so the row sits on the arrow that returns the result:
          -- `(() -> {Error | R} A) -> (String -> R A) -> R A`.
          , poly "try" [tryA] [tryR] $
              fn (TFunct (Funct TNil (t tryA) (ROpen [Eff.label "Error"] tryR)))
                 (TFunct $ Funct
                    (TFunct (Funct TString (t tryA) (RVar tryR)))
                    (t tryA)
                    (RVar tryR))
          ]

    pure (functions <> arrays <> pairs <> convs)

  let emptyScope = Scope
        Map.empty
        Map.empty
        Map.empty
        Nothing
        Map.empty
        Map.empty
        Map.empty
        Map.empty
        Map.empty
        Map.empty
        Nothing

      tSay = TVar boundSay
      tSayn = TVar boundSayn
      tTrace = TVar boundTrace
      tForce = TVar boundForce
      tWhnf = TVar boundWhnf

      -- Curried shapes, spelled once so that a field of a library record and
      -- the flat name next to it cannot drift apart: both are built from this
      -- one table.
      i2i = tfunc TInt (tfunc TInt TInt)
      i2b = tfunc TInt (tfunc TInt TBoolean)
      i1i = tfunc TInt TInt
      f2f = tfunc TFloat (tfunc TFloat TFloat)
      f2b = tfunc TFloat (tfunc TFloat TBoolean)
      f1f = tfunc TFloat TFloat
      b2b = tfunc TBoolean TBoolean
      s2s = tfunc TString TString
      s2b = tfunc TString (tfunc TString TBoolean)
      s3s = tfunc TString (tfunc TString (tfunc TString TString))

      strings = TArray TString (RClosed [])

      -- The arithmetic, the strings and the booleans: monomorphic, so a field
      -- of a record is exactly the type of the flat name.
      fieldTypes =
        [ ("pred", i1i)
        -- `/` reports a zero divisor through `Error`, so its latent row names
        -- the effect: a caller pays for it, exactly as `app/std.marr` says.
        , ("+", i2i), ("-", i2i), ("*", i2i), ("%", i2i)
        , ("/", TFunct $ Funct TInt (tfunc TInt TInt) Eff.fxError)
        , ("neg", i1i), ("abs", i1i), ("max", i2i), ("min", i2i)
        , ("ieq", i2b), ("ineq", i2b)
        , (">", i2b), ("<", i2b), ("<=", i2b), (">=", i2b)
        , ("+.", f2f), ("-.", f2f), ("*.", f2f), ("/.", f2f), ("%.", f2f)
        , ("fneg", f1f), ("fabs", f1f), ("fmax", f2f), ("fmin", f2f)
        , ("feq", f2b), ("fneq", f2b)
        , ("<.", f2b), (">.", f2b), ("<=.", f2b), (">=.", f2b)
        , ("to_int", tfunc TFloat TInt), ("to_float", tfunc TInt TFloat)
        , ("++", tfunc TString s2s)
        , ("slen", tfunc TString TInt)
        -- start, length, string
        , ("sub", tfunc TInt (tfunc TInt (tfunc TString TString)))
        -- separator, string
        , ("split", tfunc TString (tfunc TString strings))
        , ("join", tfunc TString (tfunc strings TString))
        , ("trim", s2s), ("upper", s2s), ("lower", s2s)
        , ("contains", s2b), ("replace", s3s)
        , ("seq", s2b), ("sneq", s2b)
        , ("not", b2b)
        , ("||", tfunc TBoolean b2b), ("&&", tfunc TBoolean b2b)
        , ("^", tfunc TBoolean b2b), ("nor", tfunc TBoolean b2b)
        , ("nand", tfunc TBoolean b2b)
        , ("and", tfunc TBoolean b2b)
        ]

      -- A value the interpreter builds directly.  Its arrows are opened below,
      -- so the row of the argument is charged at the call site.
      native name typ = (name, [], [], typ)

      -- A parameterised builtin: its type variables are quantified by the
      -- scheme, so every instantiation gets fresh ones.
      quantified name tvs typ = (name, tvs, [], typ)

      -- An operation of a built-in effect.  The program sees it as a function
      -- whose latent row names the effects it may perform.
      operation name input output effects =
        (name, [], [], TFunct $ Funct input output $ RClosed (map Eff.label effects))

      entries =
        [ native n t | (n, t) <- fieldTypes ] <>
        [ quantified "force" [boundForce] $ TFunct $ Funct tForce tForce Eff.empty
        , quantified "whnf" [boundWhnf] $ TFunct $ Funct tWhnf tWhnf Eff.empty
        , quantified "say" [boundSay] $ TFunct $ Funct tSay TNil Eff.fxOutput
        , quantified "sayn" [boundSayn] $ TFunct $ Funct tSayn TNil Eff.fxOutput
        -- `trace 'label' v`: the label is ordinary text, the value comes back
        -- unchanged, so `app/std.marr` declares it `String -> `A -> {Output} `A`.
        , quantified "trace" [boundTrace] $
            TFunct $ Funct TString (TFunct $ Funct tTrace tTrace Eff.fxOutput) Eff.empty
        , operation "read_int" TNil TInt ["Input"]
        , operation "read_string" TNil TString ["Input"]
        , operation "read_float" TNil TFloat ["Input"]
        , operation "read_boolean" TNil TBoolean ["Input"]
        , ( "random_int"
          , []
          , []
          , TFunct $ Funct TInt (TFunct $ Funct TInt TInt Eff.fxRandom) Eff.empty
          )
        , operation "random_float" TNil TFloat ["Random"]
        , operation "random_boolean" TNil TBoolean ["Random"]
        , operation "random_string" TInt TString ["Random"]
        , operation "time_ms" TNil TInt ["Time"]
        , operation "sleep" TInt TNil ["Time"]
        -- `Env`, `File` and `System` of `app/std.marr`.  A file operation that
        -- can fail names `Error` in its row as well, so a handler for it is
        -- optional but a `try` or `under Error` can catch the failure.
        , operation "get_env" TString TString ["Env"]
        , operation "set_env" TString (tfunc TString TNil) ["Env"]
        , operation "read_file" TString TString ["File", "Error"]
        , operation "write_file" TString (tfunc TString TNil) ["File", "Error"]
        , operation "append_file" TString (tfunc TString TNil) ["File", "Error"]
        , operation "file_exists" TString TBoolean ["File"]
        , operation "delete_file" TString TNil ["File", "Error"]
        , operation "list_directory" TString strings ["File", "Error"]
        -- `args` is an operation, not a constant: the command line is read when
        -- the program asks for it, and a program that does not name `System`
        -- cannot see it.
        , operation "args" TNil strings ["System"]
        , operation "hostname" TNil TString ["System"]
        , operation "system" TString TInt ["System"]
        -- `exit` never returns, like `error`: its result is the bottom type.
        , quantified "exit" [boundExit] $
            TFunct $ Funct TInt (TVar boundExit) (Eff.closedOfFlat "System")
        -- `error` never returns, so its result is the bottom of every type: a
        -- use reads as whatever the surrounding expression needs.  It is also
        -- an operation of the built-in effect `Error` below, which is what
        -- makes a use charge `Error` and lets `under Error to ...` catch it.
        , quantified "error" [boundError] $
            TFunct $ Funct TString (TVar boundError) (Eff.closedOfFlat "Error")
        -- `assert` performs `Error` only when the condition fails, which the
        -- type cannot express: the call is charged as if it may, and a program
        -- that asserts inside `under Error to ...` pays for the handler.
        , native "assert" (TFunct $ Funct TBoolean (TFunct $ Funct TString TNil Eff.fxError) Eff.empty)
        ]

      flatNames = map (\(n, _, _, _) -> n) (entries <> polyEntries)
      recordNames = Builtins.namesOfKind isRecord
      declared = flatNames <> recordNames
      undocumented = filter (`notElem` declared) Builtins.names
      unimplemented = filter (`notElem` Builtins.names) declared

  unless (null undocumented && null unimplemented) $
    throwTypeCheckError $ InferenceError $ T.concat [
        "internal error: the builtin table and the type checker disagree",
        report "the table lists but the checker lacks" undocumented,
        report "the checker binds but the table lacks" unimplemented
      ]

  -- The flat names first: a record is built out of their types, so
  -- `Numbers@+` and `+` are the same scheme, not two that happen to agree.
  -- `Error` is the one effect a program may name without declaring it: the
  -- interpreter keeps a bottom handler for it that turns an unhandled `error`
  -- into a diagnostic, and `/` reports a zero divisor through it.  A program
  -- that writes `under Error to ... handle | error e => ...` catches it
  -- instead of letting it reach the bottom.
  --
  -- It lives in its own outer scope, so a program is still free to declare
  -- `effect Error` itself (`app/std.marr` does): a declaration shadows a
  -- built-in, and `addEffect` only looks at the scope it adds to.
  let errorScope = emptyScope {effects = Map.singleton "Error" errorEff}
      builtinScope = emptyScope {parent = Just errorScope}

      errorEff = EffDef "Error" [] [
          -- The result is the bottom type: `error` never returns, so its use
          -- reads as whatever the surrounding expression needs.  The latent
          -- row is empty like every declared operation's: an effect is charged
          -- at the use site ('Scope.findOperations'), not by the operation's
          -- own type.
          ("error", Funct TString TNothing Eff.empty)
        ]

  -- The flat names first: a record is built out of their types, so
  -- `Numbers@+` and `+` are the same scheme, not two that happen to agree.
  withFlat <- foldM
    (\sc (name, tvs, rvs, typ) -> do
        (openedTyp, rowVars) <- openArrows typ
        let scheme = Scheme tvs [] (rvs <> rowVars) Map.empty Map.empty openedTyp
        addBinding name scheme (valueOf name scheme) Val sc)
    builtinScope
    (entries <> polyEntries)

  foldM addRecord withFlat (Builtins.builtins >>= asRecord)

  where
    isRecord (Builtins.Record _) = True
    isRecord _ = False

    asRecord (Builtins.Builtin name (Builtins.Record fields)) = [(name, fields)]
    asRecord _ = []

    -- A library record.  Its fields keep the open rows of the flat names: the
    -- record is a view of the library, not a second copy of it, and a field
    -- read through the record must be as permissive as the name itself.
    addRecord sc (name, fields) = do
      let fieldOf n =
            case Scope.findBinding True sc n of
              Just (scheme, _, _) -> scheme._a
              Nothing -> TInt -- unreachable: the flat pass bound every field
      (props, rowVars) <- foldM
        (\(acc, rs) n -> do
            (t, rs') <- openArrows (fieldOf n)
            pure (acc <> [TRecordProp Val n t], rs <> rs'))
        ([], [])
        fields
      let typ = TRecord props (RClosed [])
          scheme = Scheme [] [] rowVars Map.empty Map.empty typ
      addBinding name scheme (valueOf name scheme) Val sc

    report what ns =
      if null ns then "" else "; " <> what <> ": " <> T.intercalate ", " ns

    -- | Give every arrow of a builtin's curried spine a fresh row tail.
    --
    --   A builtin performs its own effect and nothing else, but its argument
    --   is a delayed computation whose forcing may cost more (T-App: the row
    --   of the argument must be included in the latent row of the parameter).
    --   With a closed latent row the inclusion can never be satisfied, so
    --   `sayn (f ())` was rejected whenever `f` read state.  The tail makes a
    --   builtin polymorphic in the effects of its argument, exactly as an
    --   inferred row has it; the effects are still charged, so a function that
    --   declares `{Output}` and passes a reading thunk to `sayn` is rejected
    --   because `Read` ends up in the call row.
    openArrows :: Typ -> TypeCheckM (Typ, [Taste])
    openArrows = go
      where
        go ty = case ty of
          TFunct (Funct i o fxs) -> do
            -- A meta, not a bound variable: 'applyEffRowSubst' resolves metas
            -- through 'rowSubst', which is how a scheme's row variables are
            -- freshened on every instantiation.  A bound variable is rigid and
            -- would stay in the type, so the tail could never be solved.
            r <- freshMetaM
            (o', rs) <- go o
            -- A row that is an explicit variable belongs to the signature and
            -- must be kept, not replaced: `apply` says its result costs the
            -- same row as the function it applies, and `try` says it costs the
            -- row its body may perform.  Replacing such a row with a fresh
            -- tail would cut the link and let a call claim the argument costs
            -- nothing.  Only a closed row is opened.
            let (fxs', rs') = case fxs of
                  RClosed cs -> (ROpen cs r, r : rs)
                  _ -> (fxs, rs)
            pure (TFunct (Funct i o' fxs'), rs')
          _ -> pure (ty, [])

    -- The scope keeps a value only so that the checker can tell what a name
    -- refers to; the interpreter has its own table.  A native signature is
    -- enough to describe it.
    valueOf :: Text -> TypeScheme -> Expr
    valueOf name scheme = case scheme._a of
      TFunct (Funct i o fxs) -> NLambda (NativeLambdaSign name i o fxs)
      t -> NLambda (NativeLambdaSign name t t Eff.empty)
