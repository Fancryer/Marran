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
  inferProgram,
  freezeMutability,
  touches,
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
    pattern Annot,
    pattern Match,
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
    enumName, enumParams, enumCases, enumCaseName, enumCaseFields, constructorTyp,
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
    joinTypes,
    subsumesType,
    applyTypeSubst,
    freshMetaTypeM,
    freshMetaTypeArgM,
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
import Control.Monad (foldM, when, forM, unless)
import Scope (enterScope)
import qualified Builtins
import Utils (uniqPreserveOrder, Pretty (pretty))
import qualified Data.Text as T
import Data.List (nub, find)
import Text.Printf (printf)
import Data.Maybe (isNothing, fromMaybe, catMaybes, listToMaybe)
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
    pattern TEAnnot,
    pattern TEMatch,
    pattern TEWith,
    TypeRep(..),
    TypeShape(..),
    TypeRepProp(..),
    typeRepOfTyp,
    Pattern(..),
    PatternNode(..),
    MatchClause(..),
    TPattern(..),
    TPatternNode(..),
    TMatchClause(..),
    EnumDef(..),
    EnumCase(..),
    atTypedSpan,
    pattern Bind, pattern Rebind, pattern Expr,
    atTypedStatSpan
  )
import Data.Text (Text)
import Control.Lens (use)
import ErrorContext (IrFrame (IrFrame), ErrorFrame (..))
import Suggest (suggestionNote)
import Module (Module(..), ModuleHeader(..), Imported(..), ImportOrigin(..), DeclKind(..), Unit(..), Program(..), tableEntries, QualifiedAlias(..), qualifiedAliases)
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
  TEnum _ args -> all (isTypeArgMonomorphic scope) args
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
  TAEnum _ args -> all (isTypeArgMonomorphic scope) args
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
  TEAnnot e t -> TEAnnot <$> substituteTypedExpr scope e <*> applyTypeSubst scope t
  TEWith e reps passed -> TEWith <$> substituteTypedExpr scope e <*> pure reps <*> pure passed
  TEMatch e t cs -> do
    e' <- substituteTypedExpr scope e
    t' <- applyTypeSubst scope t
    cs' <- mapM (substituteMatchClause scope) cs
    pure $ TEMatch e' t' cs'
  TEHandle handler t -> do
    t' <- applyTypeSubst scope t
    handler' <- substituteHandler scope handler
    pure $ TEHandle handler' t'
  TENLambda (NativeLambdaSign n i o r) ->
    TENLambda <$> (NativeLambdaSign n
      <$> applyTypeSubst scope i
      <*> applyTypeSubst scope o
      <*> applyEffRowSubst scope r)

-- | Apply the substitution to the types a checked pattern carries.
substituteTPattern :: Scope -> TPattern -> TypeCheckM TPattern
substituteTPattern scope (MkTPattern sp node) = MkTPattern sp <$> go node
  where
    go = \case
      TPInt i -> pure (TPInt i)
      TPFloat f -> pure (TPFloat f)
      TPString s -> pure (TPString s)
      TPBoolean b -> pure (TPBoolean b)
      TPNil -> pure TPNil
      TPName n t -> TPName n <$> applyTypeSubst scope t
      TPValue e -> TPValue <$> substituteTypedExpr scope e
      TPArray ps t -> TPArray <$> mapM (substituteTPattern scope) ps <*> mapM (substituteTPattern scope) t
      TPTuple ps -> TPTuple <$> mapM (substituteTPattern scope) ps
      TPCon n ps -> TPCon n <$> mapM (substituteTPattern scope) ps
      TPAs p n t -> TPAs <$> substituteTPattern scope p <*> pure n <*> applyTypeSubst scope t
      TPCast p t -> TPCast <$> substituteTPattern scope p <*> applyTypeSubst scope t
      TPWildcard -> pure TPWildcard
      TPStarts l r -> TPStarts <$> substituteTPattern scope l <*> substituteTPattern scope r
      TPEnds l r -> TPEnds <$> substituteTPattern scope l <*> substituteTPattern scope r

substituteMatchClause :: Scope -> TMatchClause -> TypeCheckM TMatchClause
substituteMatchClause scope (TMatchClause ps g b) = do
  ps' <- mapM (substituteTPattern scope) ps
  g' <- mapM (substituteTypedExpr scope) g
  b' <- substituteBlock scope b
  pure $ TMatchClause ps' g' b'

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
  TypedIR.Rebind n path e -> TypedIR.Rebind n path <$> substituteTypedExpr scope e
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
  Types.Assign _ _ e -> countResumeInExpr e
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
  Annot e _ -> countResumeInExpr e
  Match e cs ->
    countResumeInExpr e
      <> foldr (\(MatchClause _ g b) acc ->
                  (maybe NoResume countResumeInExpr g <> countResumeInBlock b) <> acc
               ) NoResume cs
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
--
-- | Check one file against the whole native scope.
--
--   This is what a test harness or a tool wants when it hands the checker a
--   chunk and no program around it: every native name is in scope, as it was
--   before native modules became importable.  'inferProgram' is the form a
--   program takes, where a module sees only what it imported.
inferChunk :: [Text] -> Types.Chunk -> TypeCheckM TypedIR.Chunk
inferChunk args chunk = do
  base <- Scope.globalScope args
  fst <$> inferModule base chunk

-- | Check a whole program, one module at a time.
--
--   The units arrive in dependency order, so every interface a module imports
--   is already known.  Within a unit the interfaces are taken from the
--   declarations themselves rather than from the checked modules: a cycle has
--   no first module, and a declared signature is all an importer needs to see.
--
--   Each module is checked against a scope of its own -- the native names of
--   the modules it imported, then the modules it imported, then its own
--   declarations -- so an unexported name of another file is not merely absent
--   from its table, it was never put in scope.
inferProgram :: [Text] -> Program Types.TopLevelStat -> TypeCheckM (Program TypedIR.TopLevelStat)
inferProgram args (Program units sources entry) = do
  (_, units') <- foldM step (Map.empty, []) units
  pure $ Program units' sources entry
  where
    step (known, acc) (Unit paths mods) = do
      -- A cycle is checked as one step, so its members see each other's
      -- declared interfaces; a settled module keeps the interface of its own
      -- declarations, which is the same thing an importer would have computed.
      let declared = Map.fromList [ (p, declaredInterface m) | (p, m) <- mods ]
          tables = Map.union declared known
      checked <- forM mods $ \(p, m) -> do
        base <- moduleScope args tables (modHeader m)
        (chunk', face) <- inferModule base m
        pure ((p, chunk'), (p, face))
      pure (Map.union (Map.fromList (map snd checked)) known
           , acc <> [Unit paths (map fst checked)])

-- | What one module offers to the modules that import it.
data Interface = Interface {
    inValues  :: Map.Map Text TypeScheme
  , inEnums   :: Map.Map Text EnumDef
  , inEffects :: Map.Map Text EffDef
  }

-- | The interface a module's declarations describe, without checking them.
--
--   A function's signature is mandatory, so the scheme an importer uses is the
--   one written in the file.  The first pass of 'inferModule' builds exactly
--   this scheme, and 'inferModule' reports it back, so the two cannot drift
--   apart.
declaredInterface :: Types.Chunk -> Interface
declaredInterface (Module _ stats) =
  Interface
    { inValues = Map.fromList $
        [ (d.fName, functScheme d) | Types.SFunctDef _ d <- stats ]
        <> concatMap constructors [ d | Types.SEnumDef _ d <- stats ]
    , inEnums = Map.fromList
        [ (enumName d, d) | Types.SEnumDef _ d <- stats ]
    , inEffects = Map.fromList
        [ (effName d, d) | Types.SEffDef _ d <- stats ]
    }

-- | The constructors of an enumeration, as the schemes of ordinary functions.
--
--   A constructor is a value of the module's scope, so an importer gets it the
--   same way it gets a function: by name, with the declaration's parameters
--   quantified.  The declaration's own table lists the constructors as
--   'KindFunct', which is what makes this lookup possible.
constructors :: EnumDef -> [(Text, TypeScheme)]
constructors def =
  [ (enumCaseName c, Scheme (enumParams def) [] [] Map.empty Map.empty (constructorTyp def c))
  | c <- enumCases def
  ]

-- | The scheme a function declaration states.
functScheme :: Types.FunctDecl -> TypeScheme
functScheme functDecl =
  let (retFxs, retTyp) = functDecl.fRet
      fullTyp = buildCurried (map snd functDecl.fArgs) retFxs retTyp
      tvars = uniqPreserveOrder $
        map (`Bound` 0) functDecl.fTvars <> collectTvarsFromType [] fullTyp
      evars = uniqPreserveOrder $
        map (`Bound` 0) functDecl.fEvars <> collectEvarsFromType [] fullTyp
      rvars = uniqPreserveOrder $
        map (`Bound` 0) functDecl.fRvars <> collectRvarsFromType [] fullTyp
  in Scheme tvars evars rvars Map.empty Map.empty fullTyp

-- | The scope a module starts from: the native names it imported, and the
--   names its imports bring under the local spelling this file writes.
moduleScope ::
     [Text]
  -> Map.Map FilePath Interface
  -> ModuleHeader
  -> TypeCheckM Scope
moduleScope args tables header = do
  let resolved = tableEntries (mhResolved header)
      natives = [ imName imp | (_, imp) <- resolved, FromNative _ <- [imOrigin imp] ]
      -- An import may rename a type-level declaration: the enumeration of
      -- `enum Colour as Shade`, or the effect of `effect Write as Save`.  Every
      -- declaration named beside it mentions those names -- a constructor says
      -- `Colour`, an operation says `{Write}` -- so the rename has to reach
      -- inside the schemes, or an importer would receive a name in a spelling
      -- this file does not have.
      renames =
        [ (imName imp, local)
        | (local, imp) <- resolved
        , imKind imp /= KindFunct
        , local /= imName imp
        ]
  base <- Scope.nativeScope (`elem` natives) args
  scoped <- foldM (addImport renames base) base resolved
  -- A qualified spelling is a binding of its own, next to the name the import
  -- brought it under.  Copying the binding rather than rebuilding it keeps a
  -- type-directed native recognisable under either spelling.
  foldM addAlias scoped (qualifiedAliases header)
  where
    addAlias sc (qualified, alias) =
      case Scope.findBindingWithRow False sc (qaLocal alias) of
        Just (ValueBinding scheme expr mut row) ->
          Scope.addBindingWithRow qualified scheme expr mut row sc
        Nothing -> pure sc

    addImport renames base sc (local, imp) = case imOrigin imp of
      FromNative _
        -- A native name renamed by `as`: the scheme is the declared one, the
        -- spelling in this file is the alias.  The expression is copied too,
        -- because it is what marks a type-directed native.
        | local /= imName imp ->
            case Scope.findBindingWithRow False base (imName imp) of
              Just (ValueBinding scheme expr mut row) ->
                Scope.addBindingWithRow local (renameScheme renames scheme) expr mut row sc
              Nothing -> pure sc
        | otherwise -> pure sc
      FromModule path -> case Map.lookup path tables of
        Nothing -> pure sc
        Just face -> addFrom face sc
      where
        addFrom face s = case imKind imp of
          KindFunct -> case Map.lookup (imName imp) (inValues face) of
            Just scheme -> Scope.addBinding local (renameScheme renames scheme) (XVar local) Val s
            Nothing -> pure s
          KindEnum -> case Map.lookup (imName imp) (inEnums face) of
            Just def -> Scope.addEnum (renameEnum renames local def) s
            Nothing -> pure s
          KindEffect -> case Map.lookup (imName imp) (inEffects face) of
            Just def -> Scope.addEffect (renameEffect renames local def) s
            Nothing -> pure s
          -- A type or row alias lives in the elaborator, not in the checker.
          _ -> pure s

    -- An import may rename a declaration.  The declaration's own parameters and
    -- operations are unchanged; only the name a use writes is the local one,
    -- and the enumerations its types mention take their local spelling too.
    renameEnum renames local (EnumDef _ params cases) =
      EnumDef local params
        [ EnumCase (enumCaseName c)
            [ (m, n, renameTypeName renames t) | (m, n, t) <- enumCaseFields c ]
        | c <- cases
        ]
    renameEffect renames local (EffDef _ params ops) =
      EffDef local params
        [ (n, Funct (renameTypeName renames i) (renameTypeName renames o)
                    (renameEffRow renames fxs))
        | (n, Funct i o fxs) <- ops
        ]

    renameScheme renames (Scheme ts es rs els rls t) =
      Scheme ts es rs els rls (renameTypeName renames t)

-- | Rewrite the enumerated types a set of aliases renames.
--
--   A rename applies in one file only, and it is a name substitution: the
--   declaration's cases, fields and parameters keep their shapes.
renameTypeName :: [(Text, Text)] -> Typ -> Typ
renameTypeName renames = go
  where
    rename n = fromMaybe n (lookup n renames)

    go = \case
      TArray t r -> TArray (go t) (renameEffRow renames r)
      TPair l r fx -> TPair (go l) (go r) (renameEffRow renames fx)
      TFunct (Funct i o fxs) -> TFunct (Funct (go i) (go o) (renameEffRow renames fxs))
      TRecord props r -> TRecord [p {tTyp = go (tTyp p)} | p <- props] (renameEffRow renames r)
      TEnum n args -> TEnum (rename n) (map goArg args)
      TForall ts es rs els rls t -> TForall ts es rs els rls (go t)
      t -> t

    goArg = \case
      TAArray t -> TAArray (goArg t)
      TAPair l r -> TAPair (goArg l) (goArg r)
      TAFunct i o -> TAFunct (goArg i) (goArg o)
      TARecord props -> TARecord [TARecordProp m n (goArg t) | TARecordProp m n t <- props]
      TAEnum n args -> TAEnum (rename n) (map goArg args)
      t -> t

-- | Rewrite the effect names a set of aliases renames, in a row and in the
--   types its parameters carry.
renameEffRow :: [(Text, Text)] -> EffRow -> EffRow
renameEffRow renames = go
  where
    renameEff = \case
      EffCons (ECons n args) -> EffCons (ECons (rename n) (map goArg args))
      v -> v
    rename n = fromMaybe n (lookup n renames)

    go = \case
      RClosed cons -> RClosed (map renameEff cons)
      ROpen cons tailVar -> ROpen (map renameEff cons) tailVar
      r -> r

    goArg = \case
      TAArray t -> TAArray (goArg t)
      TAPair l r -> TAPair (goArg l) (goArg r)
      TAFunct i o -> TAFunct (goArg i) (goArg o)
      TARecord props -> TARecord [TARecordProp m n (goArg t) | TARecordProp m n t <- props]
      TAEnum n args -> TAEnum (rename n) (map goArg args)
      t -> t

-- | Check one module against the scope it starts from, and report what it
--   offers.
inferModule :: Scope -> Types.Chunk -> TypeCheckM (TypedIR.Chunk, Interface)
inferModule globalScope (Module header chunk) = do
  -- The builtins live in the outer scope, so a program declaration shadows
  -- one: `funct apply ...` in a program is the program's `apply`, and the
  -- library's is still reachable from a scope that does not rebind it.  It is
  -- also why a user name only has to be added to the program's scope, not
  -- merged with the builtin table.
  let programScope = enterScope globalScope
  -- Первый проход: регистрируем только эффекты и функции (с предварительными схемами)
  (scope1, funSigs) <- foldM (\(sc, sigs) stat -> case stat of
      Types.SEnumDef sp enumDef -> withDeclFrame ("enum " <> enumName enumDef) sp $ do
        sc' <- Scope.addEnum enumDef sc
        -- The constructors are ordinary functions of the program's scope: a
        -- value is built as `Some 5`, and nothing marks it as an enum at the
        -- use site.  Each one is polymorphic in the declaration's parameters.
        foldM (\sc'' c -> do
            let name = enumCaseName c
            when (Scope.hasBinding False sc'' name) $
              throwTypeCheckError $ DuplicateDefinition $
                "the constructor `" <> name <> "` of `" <> enumName enumDef
                  <> "` collides with another definition"
            let typ = constructorTyp enumDef c
                scheme = Scheme (enumParams enumDef) [] [] Map.empty Map.empty typ
            Scope.addBinding name scheme (XVar name) Val sc''
          ) sc' (enumCases enumDef)
        >>= \sc'' -> pure (sc'', sigs)

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
    ) (programScope, []) chunk

  -- Второй проход: типизируем тела функций и обновляем схемы
  (finalScope, typedFuns) <- foldM (\(sc, acc) (functDecl, retFxs, retTyp) -> do
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
    Types.SEnumDef _ enumDef -> pure $ Just $ TypedIR.SEnumDef enumDef
    Types.SFunctDef _ _ -> pure Nothing

  -- What the module offers: the schemes the bodies were given, the enums and
  -- the effects.  A signature is mandatory, so this is the same interface
  -- 'declaredInterface' reads off the declarations, now with the rows the
  -- checker solved.
  let funNames = [ n | TypedIR.SFunctDef (TypedIR.FunctDecl n _ _ _ _ _) <- typedFuns ]
      enumDefs = [ d | Types.SEnumDef _ d <- chunk ]
      face = Interface
        { inValues = Map.fromList $
            [ (name, scheme)
            | name <- funNames
            , Just (ValueBinding scheme _ _ _) <- [Map.lookup name (values finalScope)]
            ]
            <> concatMap constructors enumDefs
        , inEnums = Map.fromList [ (enumName d, d) | d <- enumDefs ]
        , inEffects = Map.fromList
            [ (effName d, d) | Types.SEffDef _ d <- chunk ]
        }

  pure (Module header $ catMaybes (otherStats <> map Just typedFuns), face)

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
  XVar v
    -- A type-directed builtin has no run-time meaning without its type
    -- argument: `parse` alone would have to guess the type of the value it
    -- builds.  The `with` path below constructs the node directly, so this
    -- branch only sees a bare use.
    | Just binding <- Scope.findBindingWithRow True scope v
    , isTypeDirectedBinding binding ->
        throwTypeCheckError $ ApplicationError $ T.concat [
            "`", v, "` needs a type argument: write `", v, " with [T] ...`"
          ]
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
          -- A use of an operation performs its effect, and a parameterised
          -- effect is performed with arguments: `ask` of `effect Ask[T]`
          -- performs `Ask[`m]`, and the row its caller declares (`Ask[Int]`)
          -- binds that variable.  The arguments are the same fresh variables
          -- the operation's own type mentions, so the value the operation
          -- produces and the occurrence it charges stay in step.
          args <- mapM (const freshMetaTypeArgM) params
          let opTyp' = case instantiateOps params [(v, opTyp)] args of
                ((_, t') : _) -> t'
                [] -> opTyp
          (t, sc) <- instantiateTypeScheme scope $ monoScheme (TFunct opTyp')
          pure (t, Eff.closedOfFlatWith eff args, sc, Val)
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

    -- Типизируем остальные элементы и одновременно сводим их типы к общему.
    -- `Nothing` — нижний тип, поэтому сведение, а не унификация: `[[1], []]`
    -- и `[[], [1]]` должны иметь один и тот же тип `[[Int]]`, в каком бы
    -- порядке компоненты ни стояли.
    (typedEntries, finalFxs, elemType, finalScope) <- foldM
      (\(accEntries, accFxs, accT, sc) ae -> do
        InferResult tEntry tFxs sc' <- inferExpr sc ae
        tEntryTyp <- typeOfTypedExprUnsafe tEntry
        (joined, sc'') <- joinTypes sc' accT tEntryTyp
        pure (accEntries <> [tEntry], Eff.unionEffRows accFxs tFxs, joined, sc''))
      ([hEntry], fxs, hType, scope1)
      xs
    -- Men(Γ,tᵢ): a snapshot of a component reaches whatever its code mentions.
    men <- mentionRow finalScope (Set.unions (map fvTyped typedEntries))
    pending <- freshMetaRowM
    finalScope' <- subsumesEffRow finalScope (Eff.unionEffRows finalFxs men) pending
    wrapInferResultWithCell $
      InferResult (TEArray elemType pending typedEntries) finalFxs finalScope'
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
  Apply callee arg -> inferApply scope callee arg
  NLambda n@(NativeLambdaSign{}) -> wrapInferResultWithCell $
    InferResult
      (TENLambda n)
      Eff.empty
      scope
  With withExpr ts es rs -> do
    -- `with` on a *name* works from the name's scheme, not from the type the
    -- name happens to have: `XVar` instantiates a scheme at once, so the
    -- abstraction over the type variables is already gone by the time the
    -- ordinary inference would see it.  Non-names keep the old `TForall`
    -- path.
    let binding = case withExpr of
          XVar v -> Scope.findBindingWithRow True scope v
          _ -> Nothing
        operations = case withExpr of
          XVar v -> Scope.findOperations True scope v
          _ -> []
    case (withExpr, binding, operations) of
      (XVar v, Just b, _)
        | isTypeDirectedBinding b ->
            inferWithTypeDirected scope v b ts es rs
      (XVar v, Just b, _)
        | not (null ts && null es && null rs) ->
            inferWithBinding scope v b ts es rs
      (XVar v, Nothing, [(eff, params, opTyp)])
        | not (null ts) ->
            inferWithOperation scope v eff params opTyp ts es rs
      _ -> inferWithForall scope withExpr ts es rs
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
    -- The two branches must have a common type, and `Nothing` (the type of an
    -- empty array) is bottom: `if c then [] else xs` is as well typed as
    -- `if c then xs else []`.
    (_, iScope) <- joinTypes fScope typT' typF'
    wrapInferResultWithCell $ InferResult
      (TEIfElse typP typT typF)
      (Eff.unionEffRows pFxs $ Eff.unionEffRows tFxs fFxs)
      iScope
  Annot e t -> do
    InferResult eT eFxs scope1 <- inferExpr scope e
    actual <- typeOfTypedExprIn scope1 eT
    -- An annotation on an aggregate is an upper bound, as it is for the return
    -- type of a function and for the type of a binding: a value whose pending
    -- row is smaller fits, and `[] : [Int]` refines the empty array.  The
    -- declared type is what the expression has afterwards, so a later use sees
    -- the refinement rather than the type inference would have guessed.
    scope2 <- subsumesType scope1 actual t
    declared <- applyTypeSubst scope2 t
    pure $ InferResult (TEAnnot eT declared) eFxs scope2
  Match subject clauses -> do
    InferResult subjectT subjectFxs scope1 <- inferExpr scope subject
    subjectTyp <- typeOfTypedExprIn scope1 subjectT
    -- Every clause opens a scope of its own: the names its patterns bind are
    -- visible to its guard and its block, and a later clause starts from the
    -- subject again.  Substitutions are carried between clauses, because the
    -- first clause may be what pins the subject's type down (`Some x` says a
    -- type variable is an enum).
    (clauses', clauseFxs, resultTyp, scope') <-
      inferClauses scope1 subjectTyp [] Eff.empty Nothing clauses
    -- A value with no clause to take it is a mistake the checker can prove, so
    -- it is reported here rather than as a stuck interpreter later.
    subjectResolved <- applyTypeSubst scope' subjectTyp
    let rows = [ps | TMatchClause ps g _ <- clauses', isNothing g]
    exhaustive <- matchIsExhaustive scope' subjectResolved rows
    unless exhaustive $
      throwTypeCheckError $ NonExhaustiveMatch $ pretty subjectResolved
    finalTyp <- applyTypeSubst scope' resultTyp
    pure $ InferResult (TEMatch subjectT finalTyp clauses')
        (Eff.unionEffRows subjectFxs clauseFxs) scope'

-- | Check the clauses of a @match@ one after another.
--
--   The result type starts as `Nothing`: an empty array is the bottom of every
--   aggregate, so `match ... to | 0 => [] | _ => [1]` gets `[Int]` whichever
--   clause comes first.  The row is the union of the rows of the clauses,
--   because any of them may be the one that runs.
inferClauses
  :: Scope
  -> Typ
  -> [TMatchClause]
  -> EffRow
  -> Maybe Typ
  -> [MatchClause]
  -> TypeCheckM ([TMatchClause], EffRow, Typ, Scope)
inferClauses scope _ acc rowAcc typAcc [] =
  pure (acc, rowAcc, fromMaybe TNothing typAcc, scope)
inferClauses scope subject acc rowAcc typAcc (MatchClause ps guard body : rest) = do
  -- A clause opens a scope of its own: the names its patterns bind are visible
  -- to its guard and its block, and they shadow an outer name of the same
  -- name instead of clashing with it.
  let clauseScope = enterScope scope
  (patterns, patternRow, scope1) <- checkClausePatterns clauseScope subject ps
  (guardT, guardFxs, guardScope) <- case guard of
    Nothing -> pure (Nothing, Eff.empty, scope1)
    Just g -> do
      InferResult gT gFxs gScope <- inferExpr scope1 g
      gTyp <- typeOfTypedExprIn gScope gT
      gScope' <- unifyTypes gScope TBoolean gTyp
      pure (Just gT, gFxs, gScope')
  -- The block is checked in the clause's scope, and its bindings do not
  -- escape: `inferBlock` opens a scope of its own and keeps the substitutions.
  InferResult bodyT bodyFxs bodyScope <- inferBlock guardScope body
  bodyTyp <- typeOfTypedBlockIn bodyScope bodyT
  (resultTyp, scope2) <- case typAcc of
    Nothing -> pure (bodyTyp, bodyScope)
    Just accT -> do
      accT' <- applyTypeSubst bodyScope accT
      (joined, sc) <- joinTypes bodyScope accT' bodyTyp
      pure (joined, sc)
  let clauseRow = Eff.unionEffRows patternRow (Eff.unionEffRows guardFxs bodyFxs)
      -- Back to the scope the clause started in, with what it decided.  The
      -- next clause is checked at the same level, not one nesting deeper.
      resumed = Scope.keepSubst scope2 scope
  inferClauses resumed subject
    (acc <> [TMatchClause patterns guardT bodyT])
    (Eff.unionEffRows rowAcc clauseRow)
    (Just resultTyp)
    rest

-- | Check the patterns of one clause and bind the names they introduce.
--
--   Every alternative of a primitive clause must bind the same names at the
--   same types: the clause has one block, so a name that only one alternative
--   bound would be missing in the other.
checkClausePatterns
  :: Scope
  -> Typ
  -> [Pattern]
  -> TypeCheckM ([TPattern], EffRow, Scope)
checkClausePatterns scope subject ps = do
  checked <- mapM (inferPattern scope subject) ps
  let names = [map fst bs | (_, bs, _, _) <- checked]
      firstNames = case names of
        (n:_) -> n
        [] -> []
  when (any (/= firstNames) names) $
    throwTypeCheckError $ TypeError
      "the alternatives of one `match` clause must bind the same names"
  -- The alternatives are independent readings of the same value, so a name
  -- they share is bound at one type: `| #A x #B x` needs both fields to have
  -- the subject's type.
  scope1 <- case checked of
    [] -> pure scope
    ((_, firstBs, _, _):alternatives) ->
      foldM (\sc (_, bs, _, _) ->
          foldM (\sc' ((_, t), (_, t')) -> unifyTypes sc' t t')
            sc (zip firstBs bs)
        ) scope alternatives
  let patterns = [p | (p, _, _, _) <- checked]
      bindings = case checked of
        ((_, bs, _, _):_) -> bs
        [] -> []
      boundNames = map fst bindings
      rows = foldl Eff.unionEffRows Eff.empty [r | (_, _, r, _) <- checked]
  when (length (nub boundNames) /= length boundNames) $
    throwTypeCheckError $ TypeError
      "a pattern binds the same name twice"
  scope2 <- foldM (\sc (n, t) -> do
      t' <- applyTypeSubst sc t
      pure $ Scope.bindLocal n (monoScheme t') (XVar n) Val sc
    ) scope1 bindings
  pure (patterns, rows, scope2)

-- | Check one pattern against the type of the subject it inspects.
--
--   The names the pattern binds are returned rather than inserted: the clause
--   owns the scope its block sees, so it can require every alternative to
--   agree on them first.  The row is what deciding the pattern costs: reading a
--   cell to look inside it, and whatever the expression of a @val@ pattern
--   costs to compute.
inferPattern :: Scope -> Typ -> Pattern -> TypeCheckM (TPattern, [(Text, Typ)], EffRow, Scope)
inferPattern scope subject (MkPattern sp node) = do
  subject' <- applyTypeSubst scope subject
  go scope subject' node
  where
    finish sc node' bs row = pure (MkTPattern sp node', bs, row, sc)

    -- Check a list of sub-patterns against the types they must have, threading
    -- the substitutions through the list.
    checkAll sc0 pairs = foldM (\(done, bs, row, sc) (t, p) -> do
        (p', bs', row', sc') <- inferPattern sc t p
        pure (done <> [p'], bs <> bs', Eff.unionEffRows row row', sc')
      ) ([], [], Eff.empty, sc0) pairs

    go :: Scope -> Typ -> PatternNode -> TypeCheckM (TPattern, [(Text, Typ)], EffRow, Scope)
    go sc0 t = \case
      PInt i -> do
        sc <- unifyTypes sc0 t TInt
        finish sc (TPInt i) [] Eff.empty
      PFloat f -> do
        sc <- unifyTypes sc0 t TFloat
        finish sc (TPFloat f) [] Eff.empty
      PString s -> do
        sc <- unifyTypes sc0 t TString
        finish sc (TPString s) [] Eff.empty
      PBoolean b -> do
        sc <- unifyTypes sc0 t TBoolean
        finish sc (TPBoolean b) [] Eff.empty
      PNil -> do
        sc <- unifyTypes sc0 t TNil
        finish sc TPNil [] Eff.empty
      PWildcard -> finish sc0 TPWildcard [] Eff.empty
      -- A bare name binds the component it stands for.  The value is not
      -- inspected, so nothing is read; a `var` component reached through the
      -- name is read only when the block reads it.
      PName n -> do
        when (Scope.hasBinding False sc0 n) $
          throwTypeCheckError $ SameScopeBindingShadowing n
        finish sc0 (TPName n t) [(n, t)] Eff.empty
      PVal e path -> do
        -- The path names the value the pattern compares against, so the
        -- comparison is an ordinary field access from a name the program
        -- already has.
        InferResult eT eFxs sc1 <- inferExpr sc0 e
        let eT' = foldl
              (\typed field -> atTypedSpan (teSpan typed) (TEPropAccess typed field))
              eT path
        eTyp <- typeOfTypedExprIn sc1 eT'
        sc2 <- unifyTypes sc1 t eTyp
        -- Comparing two values of a type that holds cells reads those cells.
        reads <- typeHoldsCell sc2 t
        let row = if reads then Eff.unionEffRows eFxs (Eff.closedOfFlat "Read") else eFxs
        finish sc2 (TPValue eT') [] row
      -- @[a b]@ is exactly two elements, @[a; rest]@ is a head and a tail, and
      -- @[a b; rest]@ is at least two; the parser records which of the three
      -- was written, and the shapes agree on inspection.
      PArray ps tailP -> do
        elemT <- freshMetaTypeM
        elemRow <- freshMetaRowM
        sc1 <- unifyTypes sc0 t (TArray elemT elemRow)
        (inspected, bs, rows, sc2) <- checkAll sc1 [(elemT, p) | p <- ps]
        (tailChecked, tailBs, tailRow, sc3) <- case tailP of
          Nothing -> pure (Nothing, [], Eff.empty, sc2)
          Just p -> do
            (p', bs', row', sc') <- inferPattern sc2 (TArray elemT elemRow) p
            pure (Just p', bs', row', sc')
        finish sc3 (TPArray inspected tailChecked) (bs <> tailBs)
          (Eff.unionEffRows rows tailRow)
      PTuple [l, r] -> do
        lT <- freshMetaTypeM
        rT <- freshMetaTypeM
        pairRow <- freshMetaRowM
        sc1 <- unifyTypes sc0 t (TPair lT rT pairRow)
        (l', lbs, lRow, sc2) <- inferPattern sc1 lT l
        (r', rbs, rRow, sc3) <- inferPattern sc2 rT r
        finish sc3 (TPTuple [l', r']) (lbs <> rbs) (Eff.unionEffRows lRow rRow)
      PTuple _ -> throwTypeCheckError $ TypeError
        "a tuple pattern must name exactly two components: pairs have two"
      PCon n ps -> do
        (def, enumCase) <- case Scope.enumOfConstructor True sc0 n of
          Nothing -> throwTypeCheckError $ TypeError $ T.concat [
              "there is no constructor `", n, "` in scope"
            ]
          Just found -> pure found
        -- The expected type may still be a variable: the constructor then
        -- decides it is this enum, and fresh arguments stand for the
        -- declaration's parameters.
        args <- case t of
          TEnum name given | name == enumName def -> pure given
          _ -> do
            freshArgs <- mapM (const freshMetaTypeArgM) (enumParams def)
            _ <- unifyTypes sc0 t (TEnum (enumName def) freshArgs)
            pure freshArgs
        let fieldTypes = [ substTypeArgs (zip (enumParams def) args) ft
                         | (_, _, ft) <- enumCaseFields enumCase]
        when (length ps /= length fieldTypes) $
          throwTypeCheckError $ TypeError $ T.concat [
              "the constructor `", n, "` takes ", T.pack (show (length fieldTypes)),
              " field(s), but the pattern names ", T.pack (show (length ps))
            ]
        (checked, bs, rows, sc1) <- checkAll sc0 (zip fieldTypes ps)
        -- A `var` field of an enum is a cell, and the pattern is the access to
        -- it: taking the field out is what reads it, exactly as `r@a` reads a
        -- `var` field of a record.  A wildcard asks for nothing and costs
        -- nothing; every other sub-pattern reaches the field, even a plain
        -- name, which hands the cell on to the block.
        let muts = [m | (m, _, _) <- enumCaseFields enumCase]
            readRow =
              if or (zipWith (\m p -> m == Var && touches p) muts checked)
                then Eff.closedOfFlat "Read"
                else Eff.empty
        finish sc1 (TPCon n checked) bs (Eff.unionEffRows rows readRow)
      PAs p n -> do
        (p', bs, row, sc1) <- inferPattern sc0 t p
        when (Scope.hasBinding False sc0 n) $
          throwTypeCheckError $ SameScopeBindingShadowing n
        t' <- applyTypeSubst sc1 t
        finish sc1 (TPAs p' n t') (bs <> [(n, t')]) row
      PCast p declared -> do
        sc1 <- unifyTypes sc0 t declared
        finish' <- inferPattern sc1 declared p
        let (p', bs, row, sc2) = finish'
        declared' <- applyTypeSubst sc2 declared
        finish sc2 (TPCast p' declared') bs row
      PStarts l r -> do
        sc1 <- unifyTypes sc0 t TString
        (l', lbs, lRow, sc2) <- inferPattern sc1 TString l
        (r', rbs, rRow, sc3) <- inferPattern sc2 TString r
        finish sc3 (TPStarts l' r') (lbs <> rbs) (Eff.unionEffRows lRow rRow)
      PEnds l r -> do
        sc1 <- unifyTypes sc0 t TString
        (l', lbs, lRow, sc2) <- inferPattern sc1 TString l
        (r', rbs, rRow, sc3) <- inferPattern sc2 TString r
        finish sc3 (TPEnds l' r') (lbs <> rbs) (Eff.unionEffRows lRow rRow)

-- | Does the pattern reach the component at all?
--
--   A `var` field of an enum is a cell, and a pattern that takes the field out
--   reads it: `#Box x` hands the value to the block, which is a read of the
--   cell the same way `r@a` is.  Only `_` declines the component, so only a
--   wildcard costs nothing.
touches :: TPattern -> Bool
touches (MkTPattern _ node) = case node of
  TPWildcard -> False
  TPAs p _ _ -> touches p
  TPCast p _ -> touches p
  _ -> True

-- | Substitute type arguments for the parameters of a declaration.
substTypeArgs :: [(Taste, TypeArg)] -> Typ -> Typ
substTypeArgs su = go
  where
    go = \case
      TVar v -> maybe (TVar v) typeArgToTyp (lookup v su)
      TArray t r -> TArray (go t) r
      TPair l r fx -> TPair (go l) (go r) fx
      TFunct (Funct i o fxs) -> TFunct (Funct (go i) (go o) fxs)
      TRecord props r -> TRecord [p {tTyp = go (tTyp p)} | p <- props] r
      TEnum n args -> TEnum n (map goArg args)
      TForall ts es rs els rls t -> TForall ts es rs els rls (go t)
      t -> t
    goArg = \case
      TAVar v -> maybe (TAVar v) id (lookup v su)
      TAArray t -> TAArray (goArg t)
      TAPair l r -> TAPair (goArg l) (goArg r)
      TAFunct i o -> TAFunct (goArg i) (goArg o)
      TARecord props -> TARecord [TARecordProp m n (goArg t) | TARecordProp m n t <- props]
      TAEnum n args -> TAEnum n (map goArg args)
      t -> t

-- | Does the value of this type hold a cell that inspecting it would read?
--
--   An enum is nominal, so its fields come from the declaration.  The visited
--   set stops a recursive enum (`enum Nat | Succ (val n : Nat)`) from asking
--   about itself forever: a cycle without a `var` field holds no cell.
typeHoldsCell :: Scope -> Typ -> TypeCheckM Bool
typeHoldsCell scope = go Set.empty
  where
    go seen = \case
      TEnum n args
        | Set.member n seen -> pure False
        | otherwise -> case Scope.findEnum True scope n of
            Nothing -> pure False
            Just def -> do
              let fieldTypes =
                    [ substTypeArgs (zip (enumParams def) args) ft
                    | c <- enumCases def
                    , (_, _, ft) <- enumCaseFields c
                    ]
                  hasVarField =
                    any (any (\(m, _, _) -> m == Var) . enumCaseFields) (enumCases def)
              if hasVarField
                then pure True
                else or <$> mapM (go (Set.insert n seen)) fieldTypes
      TRecord props _ -> or <$> mapM (\(TRecordProp m _ t) ->
          if m == Var then pure True else go seen t) props
      TArray t _ -> go seen t
      TPair l r _ -> (||) <$> go seen l <*> go seen r
      _ -> pure False

-- | Check that the clauses without a guard accept every value of the subject
--   type.
--
--   An enum is covered when every constructor appears with irrefutable fields,
--   or when one clause accepts anything at all.  A Boolean needs both
--   literals.  Every other type has no literals to enumerate, so only a
--   catch-all clause covers it.
matchIsExhaustive :: Scope -> Typ -> [[TPattern]] -> TypeCheckM Bool
matchIsExhaustive scope subject rows =
  if any (any irrefutable) rows
    then pure True
    else case subject of
      TEnum n _ -> case Scope.findEnum True scope n of
        Nothing -> pure False
        Just def -> do
          let constructors = map enumCaseName (enumCases def)
              covered c = any (any (coversConstructor c)) rows
          pure $ all covered constructors
      TBoolean -> pure $ any (any (isBoolean True)) rows && any (any (isBoolean False)) rows
      TNil -> pure $ any (any isNil) rows
      TArray _ _ -> pure $ coversAllLengths [p | row <- rows, p <- row]
      _ -> pure False
  where
    -- An array is covered when some pattern accepts every length from some
    -- point on, and every shorter length has a pattern that accepts it whole:
    -- `[]`, `[a; rest]` together accept every array, and `[a b]` fills the one
    -- length in between.
    coversAllLengths ps =
      let exact = [length xs | MkTPattern _ (TPArray xs Nothing) <- ps, all irrefutable xs]
          fromAt = [length xs | MkTPattern _ (TPArray xs (Just t)) <- ps,
                               all irrefutable xs, irrefutable t]
      in case fromAt of
           [] -> False
           ms -> any (\m -> all (`elem` exact) [0 .. m - 1]) ms

    irrefutable (MkTPattern _ node) = case node of
      TPName {} -> True
      TPWildcard -> True
      TPTuple ps -> all irrefutable ps
      TPAs p _ _ -> irrefutable p
      TPCast p _ -> irrefutable p
      _ -> False

    -- A constructor whose every field is a binder accepts every value of that
    -- constructor, but not the other constructors.  An alias and a cast add
    -- names or a type, not a condition, so they are looked through.
    coversConstructor c p = case strip p of
      MkTPattern _ (TPCon n ps) -> n == c && all irrefutable ps
      _ -> False

    isBoolean b (MkTPattern _ node) = case node of
      TPBoolean b' -> b == b'
      _ -> False

    isNil (MkTPattern _ node) = case node of
      TPNil -> True
      _ -> False

    -- An alias (`p as n`) and a cast (`p : T`) add a name or a type to what a
    -- pattern accepts; they do not change which values it takes.
    strip (MkTPattern sp node) = case node of
      TPAs p _ _ -> strip p
      TPCast p _ -> strip (MkTPattern sp (nodeOf p))
      _ -> MkTPattern sp node
      where
        nodeOf (MkTPattern _ n) = n

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

-- | Is this binding a type-directed native?
--
--   The name it is bound under is not the test: an import may rename the native
--   or reach it through a qualified spelling, and both spellings still denote
--   the same builtin.  The binding's expression keeps the declared name, which
--   is what the builtin table knows.
isTypeDirectedBinding :: ValueBinding -> Bool
isTypeDirectedBinding (ValueBinding _ expr _ _) =
  case expr of
    NLambda (NativeLambdaSign n _ _ _) -> Builtins.isTypeDirected n
    _ -> False

-- | The first part of a type that a type-directed native cannot build.
--   Enums are not expanded: their fields are known per constructor, and a
--   value that never reaches an unsupported field is still buildable.
firstUnsupported :: TypeRep -> Maybe Text
firstUnsupported rep = case trShape rep of
  ShapeUnsupported what -> Just what
  ShapeArray t -> firstUnsupported t
  ShapePair a b -> case firstUnsupported a of
    Just what -> Just what
    Nothing -> firstUnsupported b
  ShapeRecord props ->
    listToMaybe (catMaybes [firstUnsupported (trpTyp p) | p <- props])
  _ -> Nothing

-- | `name with [T]`: a type-directed builtin, whose value is the parsed one.
inferWithTypeDirected
  :: Scope -> Text -> ValueBinding -> [TypeArg] -> [EffCons] -> [EffRow]
  -> InferM TypedExpr
inferWithTypeDirected scope v (ValueBinding scheme _ _ _) ts es rs = do
  unless (null es && null rs) $
    throwTypeCheckError $ ApplicationError $ T.concat [
        "`", v, "` takes no effect or row arguments"
      ]
  case (_ts scheme, ts) of
    ([_], [ta]) -> do
      let ty = typeArgToTyp ta
          rep = typeRepOfTyp (Scope.findEnum True scope) ty
      case firstUnsupported rep of
        Just what -> throwTypeCheckError $ ApplicationError $ T.concat [
            "`", v, "` cannot build a value of ", what,
            "; it supports Int, Float, Boolean, String, (), arrays, pairs, records and enums"
          ]
        Nothing -> pure ()
      (t, _, sc) <- instantiateTypeSchemeExplicit scope scheme [ty] [] [] Eff.empty
      pure $ InferResult (TEWith (TEXVar v t) [rep] True) Eff.empty sc
    (tvars, args) ->
      throwTypeCheckError $ ApplicationError $ T.concat [
          "`", v, "` needs exactly ", T.pack (show (length tvars)),
          " type argument(s), but `with` supplied ", T.pack (show (length args))
        ]

-- | `name with [T]` for an ordinary polymorphic binding.  The explicit
--   arguments go to the first type variables of the scheme, the rest are
--   instantiated with fresh metas, and the run-time types are erased.
inferWithBinding
  :: Scope -> Text -> ValueBinding -> [TypeArg] -> [EffCons] -> [EffRow]
  -> InferM TypedExpr
inferWithBinding scope v (ValueBinding scheme _ mut row) ts es rs = do
  let tys = map typeArgToTyp ts
  when (length tys > length (_ts scheme)) $
    throwTypeCheckError $ ApplicationError $ T.concat [
        "`with` applied ", T.pack (show (length tys)),
        " type argument(s) to `", v, "`, which abstracts over ",
        T.pack (show (length (_ts scheme)))
      ]
  when (length es > length (_es scheme)) $
    throwTypeCheckError $ ApplicationError $ T.concat [
        "`with` applied ", T.pack (show (length es)),
        " effect argument(s) to `", v, "`, which abstracts over ",
        T.pack (show (length (_es scheme)))
      ]
  when (length rs > length (_rs scheme)) $
    throwTypeCheckError $ ApplicationError $ T.concat [
        "`with` applied ", T.pack (show (length rs)),
        " row argument(s) to `", v, "`, which abstracts over ",
        T.pack (show (length (_rs scheme)))
      ]
  (t, row', sc) <- instantiateTypeSchemeExplicit scope scheme tys es rs row
  let reps = map (typeRepOfTyp (Scope.findEnum True scope) . typeArgToTyp) ts
      finalRow =
        if mut == Var
          then Eff.unionEffRows row' (Eff.closedOfFlat "Read")
          else row'
  pure $ InferResult (TEWith (TEXVar v t) reps False) finalRow sc

-- | `loop with [Int]`: an operation of a parameterised effect.  The
--   arguments substitute the effect's parameters in the operation's type and
--   in the effect its use charges.
inferWithOperation
  :: Scope -> Text -> Text -> [Taste] -> Funct -> [TypeArg] -> [EffCons] -> [EffRow]
  -> InferM TypedExpr
inferWithOperation scope v eff params opTyp ts es rs = do
  unless (null es && null rs) $
    throwTypeCheckError $ ApplicationError $ T.concat [
        "`", v, "` takes no effect or row arguments"
      ]
  when (length ts /= length params) $
    throwTypeCheckError $ ApplicationError $ T.concat [
        "`with` applied ", T.pack (show (length ts)),
        " type argument(s) to `", v, "`, which abstracts over ",
        T.pack (show (length params))
      ]
  let opTyp' = case instantiateOps params [(v, opTyp)] ts of
        ((_, t') : _) -> t'
        [] -> opTyp
  (t, sc) <- instantiateTypeScheme scope (monoScheme (TFunct opTyp'))
  pure $ InferResult (TEXVar v t) (Eff.closedOfFlatWith eff ts) sc

-- | The old path: `with` on an expression whose type is a `TForall`.
inferWithForall
  :: Scope -> Expr -> [TypeArg] -> [EffCons] -> [EffRow]
  -> InferM TypedExpr
inferWithForall scope withExpr ts es rs = do
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
                $ printf "the field `%s` is %s in the record being updated, so it cannot become %s" name baseMut mut
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
      -- `#{ base | ... }` is an update, not an extension: the result has every
      -- field of the base, and the listed ones replace the base's.  An
      -- inherited field is read through the base (the interpreter shares the
      -- value, since a `val` field never changes), so its typed expression is
      -- the field access on the base.
      let inherited =
            [ TERecordProp m n t (TEPropAccess anchorExpr n)
            | TRecordProp m n t <- baseProps
            , not (any (\(ERecordProp _ n' _ _) -> n' == n) props)
            ]
          allProps = inherited <> recProps
      -- T-Rec: the record being built gets its own annotation; the base's
      -- pending row is a bound too, since the new record still shares the
      -- base's fields.
      men <- mentionRow finalScope (Set.unions (map (fvTyped . terExpr) allProps))
      basePending' <- applyEffRowSubst finalScope basePending
      pending <- freshMetaRowM
      finalScope' <- subsumesEffRow finalScope
        (Eff.unionEffRows (Eff.unionEffRows propFxs men) basePending') pending
      wrapInferResultWithCell $
        InferResult (TERecord (Just anchorExpr) allProps pending) propFxs finalScope'
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
      -- `Var`, `Read`, `Rebind` and `Cell` are not declarations: the checker
      -- adds them when a mutable binding is created, read or rebound, and no
      -- operation performs them.  A handler works by intercepting a performed
      -- operation, so there is nothing for it to intercept here, and saying so
      -- is better than "there is no effect named `Var`".
      when (n `Set.member` Eff.markerEffects) $
        throwTypeCheckError $ HandlerError $ T.concat [
            "`", n, "` is not an effect a handler can handle"
          , ": it marks a mutable binding, it has no operations to intercept"
          ]
      decl@(EffDef _ params declaredOps) <- case effectDeclaration scope n of
        Nothing -> throwTypeCheckError $ HandlerError $ "there is no effect named `" <> n <> "` in scope"
        Just d -> pure d
      -- A parameterised effect is applied to as many arguments as it declares.
      -- `instantiateOps` would otherwise leave the parameters rigid, and the
      -- first operation call would report a unification failure against a
      -- variable the reader never wrote.
      when (length params /= length effArgs) $
        throwTypeCheckError $ HandlerError $ T.concat [
            "the effect `", n, "` declares ", T.pack (show (length params))
          , " type argument(s), but this handler supplies "
          , T.pack (show (length effArgs))
          ]
      -- A handler runs the clause of an operation it intercepts, and a
      -- declaration with no operations gives it no clause to run.  An `effect
      -- Empty end` written to mark a computation is therefore not handleable
      -- either, and the declaration is the place to say why.
      when (null declaredOps) $
        throwTypeCheckError $ HandlerError $ T.concat [
            "the effect `", n, "` declares no operations, so a handler has nothing to handle"
          , ": an operation is what a handler intercepts"
          ]
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

-- | Apply a callee to the arguments of one application spine.
--
--   `f a b` is two nested applications, but its arguments are read together:
--   a later argument may be what tells an earlier lambda what its parameter is.
--   `map {i = i@price} items` has no type for `i` until `items` says the
--   element is an `Item`, and a field access on an unknown type is an error.
--   So a bare lambda whose parameter type is still an inference variable waits
--   until the rest of the spine has settled it, and is then checked against
--   the type it must have ('checkExpr').
--
--   The arguments are otherwise checked left to right, exactly as before, and
--   each one is checked against the arrow the callee must have at that step:
--   the shape of the spine is fixed by the callee, the arguments only fill it
--   in.
inferApply :: Scope -> Expr -> Expr -> InferM TypedExpr
inferApply scope callee0 arg0 = do
  let (callee, args) = applicationSpine callee0 [arg0]

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

  -- One arrow per argument.  `chain` keeps the callee type of every step:
  -- each step is a call of its own, and the row it charges is the latent row of
  -- the arrow it used.
  (scope1, chain, inputs) <- foldM addStep (calleeScope, [calleeT'], []) args

  (scope2, slots, waiting, argFxs) <-
    foldM checkOne (scope1, [], [], Eff.empty) (zip3 [0 ..] args inputs)

  -- The lambdas that waited are read now, against the parameter type the other
  -- arguments have settled.
  (scope3, slots', lateFxs) <- foldM checkWaiting (scope2, slots, Eff.empty) waiting

  args' <- case sequence slots' of
    Just ts -> pure ts
    Nothing -> throwTypeCheckError $
      InferenceError "an application left an argument unchecked"

  -- T-App: every step of the spine is a call of its own, and each charges the
  -- latent row of the arrow it used.  The row is read after the arguments have
  -- been checked, because checking one may extend a row variable.  The callee's
  -- own row after unification is what the call charges, not the fresh one the
  -- step introduced: unifying two open rows binds the tail of the expected one
  -- to the difference and would lose the callee's effects.
  rows <- mapM (arrowRow scope3) (init chain)

  -- T-App (paper): @R₂ ∪ Men(Γ,t₂) ⊆ R@.  The row of every argument is
  -- charged right here -- it is part of 'finalFxs' -- so the call site already
  -- pays for it, and the parameter's latent row need not be widened to a bound
  -- of the *variable* an argument reads: for `line unit q`, where `unit` is a
  -- `var`, requiring `ρ_unit ∪ {Read} ⊆ {Read}` would close the variable's
  -- pending row and make the later `unit := ...` illegal.  What the callee must
  -- be able to pay for, though, is an argument it may force later, and that is
  -- exactly what 'unifyArgType' checks: if the argument is itself a delayed
  -- computation, its latent row is included in the parameter's arrow row.
  let finalFxs = Eff.unionEffRowsList
        ([Eff.unionEffRows argFxs lateFxs, calleeFxs] <> rows)

  pure $ InferResult
    (foldl TEApply calleeT args')
    finalFxs
    scope3
  where
    arrowRow sc ct = do
      t <- applyTypeSubst sc ct
      case t of
        TFunct (Funct _ _ row) -> applyEffRowSubst sc row
        _ -> throwTypeCheckError $
          ApplicationError "the left side of an application is not a function"

    addStep (sc, cts, is) _ = do
      from <- freshMetaTypeM
      to <- freshMetaTypeM
      arrow <- TFunct . Funct from to . ROpen [] <$> freshMetaM
      sc' <- unifyTypes sc (last cts) arrow
      pure (sc', cts <> [to], is <> [from])

    checkOne (sc, slots, waiting, fxs) (i, arg, input) = do
      waits <- bareLambdaWaits sc arg input
      if waits
        then pure (sc, slots <> [Nothing], waiting <> [(i, arg, input)], fxs)
        else do
          -- T-App: the parameter's row names the effects the argument may
          -- perform, so their operations are in scope while it is checked.
          argScope <- withRowOperations sc input
          InferResult t afxs sc' <- checkExpr argScope input arg
          pure (sc', slots <> [Just t], waiting, Eff.unionEffRows fxs afxs)

    checkWaiting (sc, slots, fxs) (i, arg, input) = do
      argScope <- withRowOperations sc input
      InferResult t afxs sc' <- checkExpr argScope input arg
      pure (sc', setAt i t slots, Eff.unionEffRows fxs afxs)

    setAt i x xs = [ if j == i then Just x else y | (j, y) <- zip [0 ..] xs ]

-- | `f a b` as the callee and its arguments, in order.
applicationSpine :: Expr -> [Expr] -> (Expr, [Expr])
applicationSpine (Apply f a) acc = applicationSpine f (a : acc)
applicationSpine f acc = (f, acc)

-- | Does this argument have to wait for the ones after it?
--
--   Only a bare lambda can: every type it knows is the one the expectation
--   supplies, and its body cannot be read before the parameter's type is a
--   shape rather than a variable.  An annotated lambda and every other
--   expression carry their own type and are checked at once.
bareLambdaWaits :: Scope -> Expr -> Typ -> TypeCheckM Bool
bareLambdaWaits scope (XLambda lam) input
  | isBareLambda lam = unknownInput scope input
bareLambdaWaits _ _ _ = pure False

-- | A lambda that names no type of its own.
isBareLambda :: Types.Lambda -> Bool
isBareLambda lam = case (lam.lArgT, lam.lRetT, lam.lFxs) of
  (Nothing, Nothing, RClosed []) -> True
  _ -> False

-- | Is the type of the parameter still an inference variable?
--
--   A lambda can be checked against an arrow whose parameter is a metavariable
--   -- `map`'s `a -{r}-> b` is one -- but not against `a` alone: `i@price`
--   needs to know that `i` is a record.  The second case is the one a spine
--   waits on.
unknownInput :: Scope -> Typ -> TypeCheckM Bool
unknownInput scope typ = do
  t <- applyTypeSubst scope typ
  case t of
    TVar Meta{} -> pure True
    TFunct (Funct i _ _) -> do
      i' <- applyTypeSubst scope i
      pure $ case i' of
        TVar Meta{} -> True
        _ -> False
    _ -> pure False

-- | Check an expression against the type it must have.
--
--   Inferring first and unifying afterwards is wrong for a lambda: its body may
--   need the parameter's type to be readable at all.  A bare lambda checked
--   against an arrow is therefore read with the arrow's parameter and result in
--   scope -- the one place where the information flows from the expectation
--   into the expression -- and everything else falls back to inference
--   followed by the inclusion check of 'unifyArgType'.
checkExpr :: Scope -> Typ -> Expr -> InferM TypedExpr
checkExpr scope expected expr = do
  expectedT <- applyTypeSubst scope expected
  case (expr, expectedT) of
    (XLambda lam, TFunct (Funct i o fxs))
      | isBareLambda lam -> checkLambdaAgainst scope lam i o fxs
    _ -> do
      InferResult t fxs sc <- inferExpr scope expr
      t' <- typeOfTypedExprIn sc t
      -- T-App: the argument's row must be included in the parameter's latent
      -- row, not equal to it.
      sc' <- unifyArgType sc t' expected
      pure (InferResult t fxs sc')

-- | A bare lambda read against the arrow it must have.
checkLambdaAgainst :: Scope -> Types.Lambda -> Typ -> Typ -> EffRow -> InferM TypedExpr
checkLambdaAgainst scope lam argT retT fxs =
  withErrorStack (EFIr $ IrFrame (pretty (XLambda lam)) (blockSpan lam.lBlock)) $ do
    -- Only the parameter and the result come from the expectation.  The row
    -- stays the lambda's own fresh variable and is related to the arrow's row
    -- by 'unifyArgType' at the end: binding the arrow's row to the body's
    -- effects here would commit a row two arguments may share before the other
    -- one has been read.
    InferResult lam' lamFxs sc0 <- inferLambda scope lam {
        Types.lArgT = Just argT, Types.lRetT = Just retT
      }
    let typed = TEXLambda lam'
    actual <- typeOfTypedExprIn sc0 typed
    sc' <- unifyArgType sc0 actual (TFunct (Funct argT retT fxs))
    pure (InferResult typed lamFxs sc')

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
instantiateTypeSchemeWithRow scope scheme extraRow =
  instantiateTypeSchemeExplicit scope scheme [] [] [] extraRow

-- | Instantiate a scheme, giving the first type, effect and row variables the
--   arguments written after `with` and freshening the rest.
--
--   The explicit arguments are not unified with fresh metas: a use such as
--   `id with [Int]` must know that the result is an `Int` before the argument
--   arrives, and `parse with [Int]` passes that very type to the interpreter.
--   A scheme may have more variables than the reader names; those stay
--   inferable, which is what makes `with` optional for an ordinary call.
instantiateTypeSchemeExplicit
  :: Scope -> TypeScheme -> [Typ] -> [EffCons] -> [EffRow] -> EffRow
  -> TypeCheckM (Typ, EffRow, Scope)
instantiateTypeSchemeExplicit scope scheme explicitTypes explicitEffects explicitRows extraRow = do
  let tvars = _ts scheme
      evars = _es scheme
      rvars = _rs scheme
      typ = _a scheme
      (exTvars, restTvars) = splitAt (length explicitTypes) tvars
      (exEvars, restEvars) = splitAt (length explicitEffects) evars
      (exRvars, restRvars) = splitAt (length explicitRows) rvars

  freshTypes <- mapM (const freshMetaM) restTvars
  freshEffects <- mapM (const freshMetaM) restEvars
  freshRows <- mapM (const freshMetaM) restRvars

  let typeMapping = Map.fromList $
        zip exTvars explicitTypes
          ++ [(tv, TVar mv) | (tv, mv) <- zip restTvars freshTypes]
      effMapping = Map.fromList $
        zip exEvars explicitEffects
          ++ [(ev, EVar mv) | (ev, mv) <- zip restEvars freshEffects]
      rowMapping = Map.fromList $
        zip exRvars explicitRows
          ++ [(rv, RVar mv) | (rv, mv) <- zip restRvars freshRows]

      scope' = scope {
        typeSubst = Map.union typeMapping scope.typeSubst,
        effSubst = Map.union effMapping scope.effSubst,
        rowSubst = Map.union rowMapping scope.rowSubst
      }

  -- The lacks constraints of the scheme travel to the argument the reader
  -- supplied, exactly as they travel to a fresh variable.
  scopeR1 <- foldM
    (\sc (old, row) ->
      maybe (pure sc) (addRowLacksToRow sc row) (Map.lookup old (_rowLacks scheme)))
    scope'
    (zip exRvars explicitRows)

  scopeR2 <- foldM
    (\sc (old, new) ->
      case Map.lookup old (_rowLacks scheme) of
        Nothing -> pure sc
        Just forbidden -> addRowLacks sc new forbidden)
    scopeR1
    (zip restRvars freshRows)

  scopeE1 <- foldM
    (\sc (old, fx) ->
      maybe (pure sc) (addRowLacksToRow sc (RClosed [fx])) (Map.lookup old (_effLacks scheme)))
    scopeR2
    (zip exEvars explicitEffects)

  scopeE2 <- foldM
    (\sc (old, new) ->
      case Map.lookup old (_effLacks scheme) of
        Nothing -> pure sc
        Just forbidden -> addEffLacks sc new forbidden)
    scopeE1
    (zip restEvars freshEffects)

  typ' <- applyTypeSubst scopeE2 typ
  row' <- applyEffRowSubst scopeE2 extraRow

  pure (typ', row', scopeE2)

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
  -- The result's type decides whether the block can carry state out at all.
  -- An enum is nominal, so its fields are not in the type: they are looked up
  -- in the declaration, which is why this question has to be asked inside the
  -- checker rather than by a pure function on `Typ`.
  holdsState <- canHoldStateIn scope' exprTyp
  let varNames = [n | TypedIR.Bind Var n _ <- stats']
      escapes = holdsState && any (`Set.member` reachNames stats' exprT) varNames
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

          -- Freezing rewrites the `var` bindings of the code it captures into
          -- `val`, so the only storage a frozen function can still create is
          -- the `var` field of a constructor: a constructor is a native and is
          -- not rewritten.  Such a function would allocate on every call while
          -- its frozen row promises nothing.  A value built before the
          -- snapshot is a different matter: 'freezeCell' copies it.
          when (mentionsVarCtor scope1 inferredTypedExpr && isFunctionTyp frozenTyp) $
            throwTypeCheckError $ TypeError $ T.concat [
                "a snapshot cannot hold a function that applies a constructor ",
                "with a `var` field: the constructor allocates storage each ",
                "time it is applied"
              ]

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
  Types.Assign n path e -> do
    (scheme, mut, pending) <- case Scope.findBindingWithRow True scope n of
      Nothing -> throwTypeCheckErrorWithNotes (UndefinedVariable n)
        (maybe [] pure (suggestionNote (Scope.bindingNames scope) n))
      Just (ValueBinding scheme _ mut' row) -> pure (scheme, mut', row)
    (varT, pending', scope') <- instantiateTypeSchemeWithRow scope scheme pending
    -- A plain `x := e` rebinds `x` without reading it (T-Rebind).  A path
    -- assignment has to reach the record first, so the name and the fields on
    -- the way are read like any other use: their pending row is charged, and a
    -- `var` one costs `Read`.
    (scopeW, fieldT, fieldMut, walkedFxs) <- case path of
      [] -> pure (scope', varT, mut, Eff.empty)
      _ -> walkAssignmentPath scope' varT path
            (Eff.unionEffRows pending' (readIfVar mut))
    when (fieldMut /= Var) $ throwTypeCheckError $
      ImmutableVariableAssignment (prettyPath n path)
    InferResult eT eFxs scope'' <- inferExpr scopeW e
    eT' <- typeOfTypedExprUnsafe eT
    -- T-Rebind: the right-hand side is delayed, so its row and its mention row
    -- must fit into the row that will run it.  For `x := e` that is the pending
    -- row of the variable, which a `var` binding leaves open and grows with
    -- every assignment.  For `r@a := e` it is the row the walk already paid: the
    -- right-hand side runs against the copies the walk made, so reaching the
    -- field -- the owner's pending row, `Read` for the `var` fields on the way
    -- and whatever forcing the record itself costs -- is a cost of the
    -- assignment, not of the delayed value.  That is why `+ r@a 1` needs no
    -- annotation on `r` beyond what reaching the field already required.
    men <- mentionRow scope'' (fvTyped eT)
    let allowed = if null path then pending' else walkedFxs
    scopeRow <- subsumesEffRow scope'' (Eff.unionEffRows eFxs men) allowed
    let finalFxs = Eff.unionEffRows
          (Eff.unionEffRows eFxs walkedFxs)
          (Eff.closedOfFlat "Rebind")
    scopeU <- unifyTypes scopeRow fieldT eT'
    pure $ InferResult (TypedIR.Rebind n path eT) finalFxs scopeU

-- | Walk the fields of a path assignment and return the slot that is written:
--   its type, its mutability and the row the walk costs.
--
--   Every field on the way is read, so each step charges the pending row of the
--   record and, for a `var` field, `Read`.  The assigned field itself is written
--   without being read, just as `x := e` does not read `x`; the row therefore
--   ends with the pending row of the record that owns it, because that is what
--   forces the field the right-hand side is about to replace.
walkAssignmentPath :: Scope -> Typ -> [Text] -> EffRow -> TypeCheckM (Scope, Typ, Mutability, EffRow)
walkAssignmentPath scope typ names fxs = case names of
  [] -> throwTypeCheckError $ InferenceError "internal error: an empty assignment path"
  [field] -> do
    (scope', pending, prop) <- fieldSlot scope typ field
    pure (scope', tTyp prop, tMut prop, Eff.unionEffRows fxs pending)
  (field : rest) -> do
    (scope', pending, prop) <- fieldSlot scope typ field
    walkAssignmentPath scope' (tTyp prop) rest
      (Eff.unionEffRows (Eff.unionEffRows fxs pending) (readIfVar (tMut prop)))

-- | Resolve one field of a record type: the substituted scope, the record's
--   pending row and the field itself.
fieldSlot :: Scope -> Typ -> Text -> TypeCheckM (Scope, EffRow, TRecordProp)
fieldSlot scope typ field = do
  typ' <- applyTypeSubst scope typ
  case typ' of
    TRecord props pending -> do
      pending' <- applyEffRowSubst scope pending
      case find ((field ==) . tName) props of
        Just prop -> pure (scope, pending', prop)
        Nothing -> throwTypeCheckErrorWithNotes
          (RecordError $ "this record has no field `" <> field <> "`")
          (maybe [] pure (suggestionNote (map tName props) field))
    _ -> throwTypeCheckError $ RecordError $ T.pack
      $ printf "cannot assign to the field `%s` of a value of type `%s`; only records have fields"
          field (pretty typ')

readIfVar :: Mutability -> EffRow
readIfVar m = if m == Var then Eff.closedOfFlat "Read" else Eff.empty

-- | @r@a@b@ for diagnostics: the name and every field, in the spelling the
--   program used.
prettyPath :: Text -> [Text] -> Text
prettyPath n path = T.concat [n, T.concat (map (T.append "@") path)]

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
    TEnum _ args -> concatMap (collectTvarsFromTypeArg except) args
    TVar v -> ([v | v `notElem` except])
    _ -> []

collectTvarsFromTypeArg :: [Taste] -> TypeArg -> [Taste]
collectTvarsFromTypeArg except typ =
  uniqPreserveOrder $ case typ of
    TAArray t -> collectTvarsFromTypeArg except t
    TAPair l r -> collectTvarsFromTypeArg except l <> collectTvarsFromTypeArg except r
    TAFunct i o -> collectTvarsFromTypeArg except i <> collectTvarsFromTypeArg except o
    TARecord props -> concatMap (collectTvarsFromTypeArg except . taTypeArg) props
    TAEnum _ args -> concatMap (collectTvarsFromTypeArg except) args
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
    TEnum _ args -> concatMap (collectEvarsFromTypeArg except) args
    _ -> []

collectEvarsFromTypeArg :: [Taste] -> TypeArg -> [Taste]
collectEvarsFromTypeArg except typ =
  uniqPreserveOrder $ case typ of
    TAArray t -> collectEvarsFromTypeArg except t
    TAPair l r -> collectEvarsFromTypeArg except l <> collectEvarsFromTypeArg except r
    TAFunct i o -> collectEvarsFromTypeArg except i <> collectEvarsFromTypeArg except o
    TARecord props -> concatMap (collectEvarsFromTypeArg except . taTypeArg) props
    TAEnum _ args -> concatMap (collectEvarsFromTypeArg except) args
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
    TEnum _ args -> concatMap (collectRvarsFromTypeArg except) args
    _ -> []

collectRvarsFromTypeArg :: [Taste] -> TypeArg -> [Taste]
collectRvarsFromTypeArg except typ =
  uniqPreserveOrder $ case typ of
    TAArray t -> collectRvarsFromTypeArg except t
    TAPair l r -> collectRvarsFromTypeArg except l <> collectRvarsFromTypeArg except r
    TAFunct i o -> collectRvarsFromTypeArg except i <> collectRvarsFromTypeArg except o
    TARecord props -> concatMap (collectRvarsFromTypeArg except . taTypeArg) props
    TAEnum _ args -> concatMap (collectRvarsFromTypeArg except) args
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
  TEAnnot e _ -> isFrozenExpr e
  TEWith e _ _ -> isFrozenExpr e
  TEMatch e _ cs ->
    isFrozenExpr e && all clauseFrozen cs
  _ -> True
  where
    clauseFrozen (TMatchClause ps g b) =
      all patternFrozen ps && maybe True isFrozenExpr g && isFrozenBlock b

    patternFrozen (MkTPattern _ node) = case node of
      TPValue e -> isFrozenExpr e
      TPArray ps t -> all patternFrozen ps && maybe True patternFrozen t
      TPTuple ps -> all patternFrozen ps
      TPCon _ ps -> all patternFrozen ps
      TPAs p _ _ -> patternFrozen p
      TPCast p _ -> patternFrozen p
      TPStarts l r -> patternFrozen l && patternFrozen r
      TPEnds l r -> patternFrozen l && patternFrozen r
      _ -> True

isFrozenBlock :: TypedIR.Block -> Bool
isFrozenBlock (stats, expr) = all stat stats && isFrozenExpr expr
  where
    stat = \case
      TypedIR.Bind m _ e -> m /= Var && isFrozenExpr e
      TypedIR.Rebind _ _ _ -> False
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
  TEAnnot e _ -> fvTyped e
  TEWith e _ _ -> fvTyped e
  TEMatch e _ cs ->
    Set.unions $ fvTyped e : map clauseVars cs
  _ -> Set.empty
  where
    clauseVars (TMatchClause ps g b) =
      Set.unions $
        map patternVars ps
          <> [fvTyped g' | Just g' <- [g]]
          <> [fvTypedBlock b]

    patternVars (MkTPattern _ node) = case node of
      TPValue e -> fvTyped e
      TPArray ps t -> Set.unions (map patternVars ps <> maybe [] (pure . patternVars) t)
      TPTuple ps -> Set.unions (map patternVars ps)
      TPCon _ ps -> Set.unions (map patternVars ps)
      TPAs p _ _ -> patternVars p
      TPCast p _ -> patternVars p
      TPStarts l r -> Set.union (patternVars l) (patternVars r)
      TPEnds l r -> Set.union (patternVars l) (patternVars r)
      _ -> Set.empty

-- | Does the expression mention a constructor whose declaration has a `var`
--   field?  The occurrence may be a direct application, a name stored for a
--   later one, or a use inside a lambda the snapshot would keep.
mentionsVarCtor :: Scope -> TypedExpr -> Bool
mentionsVarCtor scope e = any isVarCtor (Set.toList (fvTyped e))
  where
    isVarCtor n = case Scope.enumOfConstructor True scope n of
      Just (_, c) -> any (\(m, _, _) -> m == Var) (enumCaseFields c)
      Nothing -> False

-- | Is the value of this type a function?  Only such a snapshot can do
--   something when it is used later; a function inside a record or a pair is
--   covered by the run-time check, which sees the constructor in the
--   environment the snapshot copies.
isFunctionTyp :: Typ -> Bool
isFunctionTyp = \case
  TFunct _ -> True
  TForall _ _ _ _ _ t -> isFunctionTyp t
  _ -> False

fvTypedBlock :: TypedIR.Block -> Set.Set Text
fvTypedBlock (stats, expr) = go Set.empty stats
  where
    go bound [] = Set.difference (fvTyped expr) bound
    go bound (s : ss) =
      let (fvS, bound') = stat bound s
      in Set.union fvS (go bound' ss)
    stat bound = \case
      TypedIR.Bind _ n e -> (Set.difference (fvTyped e) bound, Set.insert n bound)
      TypedIR.Rebind n _ e -> (Set.difference (Set.insert n (fvTyped e)) bound, bound)
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
canHoldStateIn :: Scope -> Typ -> TypeCheckM Bool
canHoldStateIn scope = go Set.empty
  where
    go seen = \case
      TInt -> pure False
      TFloat -> pure False
      TBoolean -> pure False
      TString -> pure False
      TNil -> pure False
      TNothing -> pure False
      TArray t r -> (|| effRowBearsState [] r) <$> go seen t
      TPair l r fx ->
        (\ls rs -> ls || rs || effRowBearsState [] fx)
          <$> go seen l <*> go seen r
      TRecord props r -> do
        fields <- or <$> mapM (go seen . tTyp) props
        pure $ any (\p -> tMut p == Var) props
          || fields
          || effRowBearsState [] r
      -- An enum's fields are values a constructor holds, but the type names
      -- only the enum: the fields come from the declaration, with the type
      -- arguments substituted for its parameters.  A `var` field is a cell
      -- the constructor allocated, so such an enum always carries state.
      -- Recursion terminates by not asking about an enum already being
      -- expanded: a cycle that has no `var` field anywhere holds no cell.
      TEnum n args
        | Set.member n seen -> pure False
        | otherwise -> case Scope.findEnum True scope n of
            Nothing -> pure True
            Just def ->
              let cases' = enumCases def
                  hasVarField =
                    any (any (\(m, _, _) -> m == Var) . enumCaseFields) cases'
                  fieldTypes =
                    [ substTypeArgs (zip (enumParams def) args) ft
                    | c <- cases'
                    , (_, _, ft) <- enumCaseFields c
                    ]
              in
              if hasVarField
                then pure True
                else or <$> mapM (go (Set.insert n seen)) fieldTypes
      TFunct (Funct _ _ row) -> pure (effRowBearsState [] row)
      TVar _ -> pure True
      _ -> pure True

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
      TypedIR.Rebind n _ e | Set.member n acc -> Set.union acc (fvTyped e)
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
  TEAnnot e _ -> createsCell e
  TEWith e _ _ -> createsCell e
  TEMatch e _ cs ->
    createsCell e || any (\(TMatchClause ps _ b) ->
      any patternCreatesCell ps || blockCreatesCell b) cs
  _ -> False
  where
    patternCreatesCell (MkTPattern _ node) = case node of
      TPValue e -> createsCell e
      TPArray ps t -> any patternCreatesCell ps || maybe False patternCreatesCell t
      TPTuple ps -> any patternCreatesCell ps
      TPCon _ ps -> any patternCreatesCell ps
      TPAs p _ _ -> patternCreatesCell p
      TPCast p _ -> patternCreatesCell p
      TPStarts l r -> patternCreatesCell l || patternCreatesCell r
      TPEnds l r -> patternCreatesCell l || patternCreatesCell r
      _ -> False

    blockCreatesCell (stats, e) = any statCreatesCell stats || createsCell e

    statCreatesCell = \case
      TypedIR.Bind _ _ e -> createsCell e
      TypedIR.Rebind _ _ e -> createsCell e
      TypedIR.Expr e -> createsCell e

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
  -- The annotation is a check at its source site, not part of the value: the
  -- frozen binding records the frozen type its scheme has, and the type stored
  -- in the node would describe the state the snapshot no longer carries.
  TEAnnot e _ -> freeze e
  TEWith e reps passed -> TEWith (freeze e) reps passed
  TEMatch e t cs -> TEMatch (freeze e) t (map freezeClause cs)
  e -> e
  where
    freezeClause (TMatchClause ps g b) =
      TMatchClause (map freezePattern ps) (freeze <$> g) (freezeBlock b)

    freezePattern (MkTPattern sp node) = MkTPattern sp $ case node of
      TPValue e -> TPValue (freeze e)
      TPArray ps t -> TPArray (map freezePattern ps) (freezePattern <$> t)
      TPTuple ps -> TPTuple (map freezePattern ps)
      TPCon n ps -> TPCon n (map freezePattern ps)
      TPAs p n t -> TPAs (freezePattern p) n t
      TPCast p t -> TPCast (freezePattern p) t
      TPStarts l r -> TPStarts (freezePattern l) (freezePattern r)
      TPEnds l r -> TPEnds (freezePattern l) (freezePattern r)
      node' -> node'

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

  TEnum n args -> do
    (scope', args') <- foldM freezeArg (scope, []) args
    pure (scope', TEnum n args')

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

    freezeArg (sc, acc) t = do
      (sc', t') <- freezeTypeArgExcept excluded sc t
      pure (sc', acc <> [t'])

-- | Freeze a type argument.
--
--   An enum is nominal, so `Wrap[#{ var n : Int }]` carries the field type
--   only through its argument.  Freezing the argument is what makes the
--   snapshot of an enum value immutable: without it the checker would still
--   see a `var` field and let the program assign to it.
freezeTypeArgExcept :: Set Taste -> Scope -> TypeArg -> TypeCheckM (Scope, TypeArg)
freezeTypeArgExcept excluded = go
  where
    go scope = \case
      TAArray t -> do
        (scope', t') <- go scope t
        pure (scope', TAArray t')

      TAPair l r -> do
        (scope', l') <- go scope l
        (scope'', r') <- go scope' r
        pure (scope'', TAPair l' r')

      TAFunct i o -> do
        (scope', i') <- go scope i
        (scope'', o') <- go scope' o
        pure (scope'', TAFunct i' o')

      TARecord props -> do
        (scope', props') <- foldM freezeProp (scope, []) props
        pure (scope', TARecord props')

      TAEnum n args -> do
        (scope', args') <- foldM freezeArg (scope, []) args
        pure (scope', TAEnum n args')

      other -> pure (scope, other)

    freezeProp (sc, acc) (TARecordProp m name t) = do
      (sc', t') <- go sc t
      pure (sc', acc <> [TARecordProp (freezeMutability m) name t'])

    freezeArg (sc, acc) t = do
      (sc', t') <- go sc t
      pure (sc', acc <> [t'])

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

rowVarsInTypeArg :: TypeArg -> [Taste]
rowVarsInTypeArg = \case
  TAArray t -> rowVarsInTypeArg t
  TAPair l r -> rowVarsInTypeArg l <> rowVarsInTypeArg r
  TAFunct i o -> rowVarsInTypeArg i <> rowVarsInTypeArg o
  TARecord props -> concatMap (rowVarsInTypeArg . taTypeArg) props
  TAEnum _ args -> concatMap rowVarsInTypeArg args
  _ -> []

rowVarsInTyp :: Typ -> [Taste]
rowVarsInTyp = \case
  TArray t r -> rowVarsInTyp t <> rowVarsInRow r
  TPair l r fx -> rowVarsInTyp l <> rowVarsInTyp r <> rowVarsInRow fx
  TFunct (Funct i o row) -> rowVarsInTyp i <> rowVarsInTyp o <> rowVarsInRow row
  TRecord props r -> concatMap (rowVarsInTyp . tTyp) props <> rowVarsInRow r
  TEnum _ args -> concatMap rowVarsInTypeArg args
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
mutationEffects = Eff.markerEffects

freezeMutability :: Mutability -> Mutability
freezeMutability = \case Var -> Val; m -> m

freezeBlock :: TypedIR.Block -> TypedIR.Block
freezeBlock (st, e) = (map freezeStat st, freeze e)

freezeStat :: TypedIR.Stat -> TypedIR.Stat
freezeStat = \case
  TypedIR.Bind m n t -> TypedIR.Bind (freezeMutability m) n $ freeze t
  TypedIR.Rebind _ _ t -> TypedIR.Expr $ freeze t
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