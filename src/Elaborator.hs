{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE RankNTypes #-}

module Elaborator (
  elaborate,
  elaborateProgram,
  elaborateTopLevelStat,
  elaborateEffRow,
  elaborateExpr,
  elaborateBlock,
  ElabState(..),
  ElabM,
  ElaborationError(..),
  ElabEnv(..)
)
where

import qualified Ast
import qualified Types
import Module (Module(..), ModuleHeader(..), Imported(..), ImportOrigin(..),
               Unit(..), Program(..), DeclKind(..), tableEntries)
import qualified Data.Text as T
import Utils (uniqPreserveOrder, TextMap, Pretty(..))
import Data.Coerce (coerce)
import Data.Text (Text)
import Text.Printf (printf)
import qualified Data.Map as Map
import Control.Monad.State (State)
import Control.Lens (makeLenses, (%~), (^.), Lens')
import Control.Lens.Lens ((&))
import Control.Monad (foldM, when, forM)
import Control.Monad.Except (ExceptT)
import Control.Lens.Getter (use)
import Control.Lens.Setter ((+=))
import Control.Monad.Error.Class (throwError)
import Types (Mutability, Taste, EffRow(RClosed))
import Data.Traversable (for)
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe)
import Data.Map (Map)
import qualified Suggest

data FlatRow = FlatRow [Types.EffCons] (Maybe Taste)
-- | What a declared type name stands for: an alias, or an enumeration.
--
--   Both are looked up in the same environment, because a program writes the
--   two the same way: `Box[Int]` and `Maybe[Int]` are both a name applied to
--   arguments, and only the declaration says which one it is.
data TypeAliasDef = TypeAliasDef [Text] Ast.Typ | TypeEnumDef [Text]

-- | The rows and effects a chunk declares.
--
--   The effect names are kept next to the row aliases so that a name used in
--   row position can be told apart from a misspelled alias: `{Doubt}` names a
--   row that contains the effect @Doubt@, while a bare @Doubt@ is not a row at
--   all, because an effect is not a row.
data RowEnv = RowEnv {
  rowAliases :: [(String, Ast.EffRow)],
  declaredEffects :: [String]
}

type TypEnv = [(String, TypeAliasDef)]
data ElabEnv = ElabEnv {
  _typBounds :: TextMap Taste,
  _effBounds :: TextMap Taste,
  _rowBounds :: TextMap Taste,
  _iTypVars :: TextMap Taste,
  _iEffVars :: TextMap Taste,
  _iRowVars :: TextMap Taste
}

makeLenses ''ElabEnv

emptyEnv :: ElabEnv
emptyEnv = ElabEnv
  mempty
  mempty
  mempty
  mempty
  mempty
  mempty

-- | An error raised while turning the AST into the IR.
--
--   The elaborate is the second phase of the front end and has no more
--   information than the AST has, so these errors carry a message and nothing
--   else; they are rendered by the same code as the type errors.
data ElaborationError =
  ElaborationError Text
  | UnboundVarError Text
  deriving (Eq)

instance Pretty ElaborationError where
  pretty = \case
    ElaborationError m -> m
    UnboundVarError m -> m

-- | An elaboration error is a message: rendering it with 'show' should give
--   the text the user is meant to read, not a constructor application.
instance Show ElaborationError where
  show = T.unpack . pretty

newtype ElabState = ElabState {_counter :: Int}

makeLenses ''ElabState

type ElabM a = ExceptT ElaborationError (State ElabState) a

-- | Raise an elaboration error from a plain message.
elabError :: String -> ElabM a
elabError = throwError . ElaborationError . T.pack

-- | Type variables the elaborator invents.
--
--   'Taste' equality compares the numeric id and ignores the name and the
--   level, so ids must be unique across the two components that invent them.
--   The type checker numbers its own variables from 1 upwards; the elaborator
--   therefore uses negative ids, which cannot collide with them.  Without this
--   separation an elaborator variable and a checker variable could share an id
--   and be mistaken for one another: the substitution would then hold
--   `m := m`, and resolving it would not terminate.
freshBound, freshMeta :: Text -> ElabM Taste
freshBound name = do
  counter += 1
  ident <- use counter
  pure $ Types.Bound name (-ident)

freshMeta name = do
  counter += 1
  ident <- use counter
  pure $ Types.Meta name (-ident) (-1)

lookupMap :: Lens' ElabEnv (TextMap Taste) -> ElabEnv -> Text -> Maybe Taste
lookupMap m env x = Map.lookup x $ env ^. m

getBoundOrMakeMeta ::
  Lens' ElabEnv (TextMap Taste)
  -> Lens' ElabEnv (TextMap Taste)
  -> ElabEnv
  -> Text
  -> ElabM Taste
getBoundOrMakeMeta m im env x =
  case lookupMap m env x of
    Just x' -> pure x'
    _ -> case lookupMap im env x of
      Just x' -> pure x'
      _ -> do
        meta <- freshMeta x
        let _ = extendMap im [(x, meta)] env
        pure meta    

extendMap :: Lens' ElabEnv (TextMap Taste) -> [(Text, Taste)] -> ElabEnv -> ElabEnv
extendMap m bs env = env & m %~ Map.union (Map.fromList bs)

lookupTyp, lookupEff, lookupRow, lookupITyp, lookupIEff, lookupIRow ::
  ElabEnv -> Text -> Maybe Taste
lookupTyp  = lookupMap typBounds
lookupEff  = lookupMap effBounds
lookupRow  = lookupMap rowBounds
lookupITyp = lookupMap iTypVars
lookupIEff = lookupMap iEffVars
lookupIRow = lookupMap iRowVars

extendTyp, extendEff, extendRow, extendITyp, extendIEff, extendIRow ::
  [(Text, Taste)] -> ElabEnv -> ElabEnv
extendTyp  = extendMap typBounds
extendEff  = extendMap effBounds
extendRow  = extendMap rowBounds
extendITyp = extendMap iTypVars
extendIEff = extendMap iEffVars
extendIRow = extendMap iRowVars

resolveTypTaste, resolveEffTaste, resolveRowTaste :: ElabEnv -> Text -> ElabM Taste
resolveTypTaste env n =
  case lookupTyp env n of
    Just t -> pure t
    Nothing -> throwError $ UnboundVarError $ "Unbound type variable: " <> n

resolveEffTaste env n =
  case lookupEff env n of
    Just t -> pure t
    Nothing -> throwError $ UnboundVarError $ "Unbound eff variable: " <> n

resolveRowTaste env n =
  case lookupRow env n of
    Just t -> pure t
    Nothing -> throwError $ UnboundVarError $ "Unbound row variable: " <> n

elaborate :: Ast.Chunk -> ElabM Types.Chunk
elaborate (Module header stats) = do
  rowEnv <- collectRowEnv stats
  typEnv <- collectTypEnv stats
  Module header <$> mapM (elaborateTopLevelStat rowEnv typEnv) stats

-- | Elaborate a whole program.
--
--   Every module is elaborated on its own, against a type and row environment
--   built from what it declares and what it imports.  Where the declarations
--   come from is the loader's answer: a resolved name points at the module that
--   declares it, so an unexported alias of one module is simply absent from
--   another's environment, and a private alias cannot be reached even by
--   guessing its name.
elaborateProgram :: Ast.Program Ast.TopLevelStat -> ElabM (Program Types.TopLevelStat)
elaborateProgram (Program units sources entry) = do
  let chunks = Map.fromList [ (p, m) | u <- units, (p, m) <- unitModules u ]
  units' <- forM units $ \(Unit paths mods) ->
    Unit paths <$> forM mods (\(p, m) -> (p,) <$> elaborateModule chunks p m)
  pure $ Program units' sources entry

-- | One module of a program, elaborated with the declarations it can see.
elaborateModule :: Map FilePath Ast.Chunk -> FilePath -> Ast.Chunk -> ElabM Types.Chunk
elaborateModule chunks _ (Module header stats) = do
  ownRows <- collectRowEnv stats
  ownTyps <- collectTypEnv stats
  let imported = importedDecls chunks header
      -- The module's own declarations come first: an alias of the same name
      -- wins over an imported one, exactly as a value declaration does.
      rowEnv = ownRows {
          rowAliases = rowAliases ownRows <> importedRows imported
        , declaredEffects = declaredEffects ownRows <> importedEffects imported
        }
      typEnv = ownTyps <> importedTyps imported
  Module header <$> mapM (elaborateTopLevelStat rowEnv typEnv) stats

-- | A declaration of another module, as the tables of a module name it.
data ImportedDecl =
    ImportedType (Text, TypeAliasDef)
  | ImportedRow (Text, Ast.EffRow)
  | ImportedEffect Text

-- | The declarations a module's imports give it.
--
--   A name is looked up in the chunk of the module that declares it, which is
--   what 'mhResolved' records; a re-export therefore travels to the declaring
--   module and not to the middle one, so a name a middle module did not export
--   stays invisible.
--
--   The declaration keeps its body but takes the local name, because an import
--   may rename it: `import a [type Pair as Couple]` must make `Couple` elaborate
--   to the same alias `Pair` names in `a`, and the type environment is keyed by
--   the spelling this file writes.
importedDecls :: Map FilePath Ast.Chunk -> ModuleHeader -> [ImportedDecl]
importedDecls chunks header =
  [ rename renames local decl
  | (local, imp) <- tableEntries (mhResolved header)
  , Just path <- [case imOrigin imp of
        FromModule p -> Just p
        FromNative _ -> Nothing]
  , Just chunk <- [Map.lookup path chunks]
  , Just decl <- [lookupDecl chunk (imName imp) (imKind imp)]
  ]
  where
    -- A declaration's body is written in the vocabulary of the module that
    -- declares it.  A file that renames `Colour` to `Shade` also renames the
    -- `Colour` inside `type Colours = [Colour]`, or the alias would expand to
    -- a name this file does not have.
    renames =
      [ (imName imp, local)
      | (local, imp) <- tableEntries (mhResolved header)
      , imKind imp /= KindFunct
      , local /= imName imp
      ]

    rename renames local = \case
      ImportedType (_, d) -> ImportedType (local, renameAlias renames d)
      ImportedRow (_, r) -> ImportedRow (local, renameRow renames r)
      ImportedEffect _ -> ImportedEffect local

-- | Rewrite the names a file renames inside an alias' body.
renameAlias :: [(Text, Text)] -> TypeAliasDef -> TypeAliasDef
renameAlias renames = \case
  TypeAliasDef params body -> TypeAliasDef params (renameAstTyp renames body)
  TypeEnumDef params -> TypeEnumDef params

-- | Rewrite the names a file renames inside a row alias.
renameRow :: [(Text, Text)] -> Ast.EffRow -> Ast.EffRow
renameRow = renameAstRow

-- | A type with the renamed type and enum names substituted.
--
--   Type *variables* are not names of declarations and are left alone; only a
--   plain name or an applied generic alias is a reference to something the
--   other file declared.
renameAstTyp :: [(Text, Text)] -> Ast.Typ -> Ast.Typ
renameAstTyp renames = go
  where
    rename n = fromMaybe n (lookup n renames)

    go = \case
      Ast.TFlat n -> Ast.TFlat (rename n)
      Ast.TArray t -> Ast.TArray (go t)
      Ast.TParen t -> Ast.TParen (go t)
      Ast.TPair l r -> Ast.TPair (go l) (go r)
      Ast.TFunct (Ast.Funct i o r) -> Ast.TFunct (Ast.Funct (go i) (go o) (renameAstRow renames r))
      Ast.TRecord (Ast.RecordTyp props) ->
        Ast.TRecord $ Ast.RecordTyp
          [ Ast.RecordTypProp c n (go t) | Ast.RecordTypProp c n t <- props ]
      Ast.TPending t r -> Ast.TPending (go t) (renameAstRow renames r)
      Ast.TForall ts es t -> Ast.TForall ts es (go t)
      Ast.TVar n -> Ast.TVar n
      Ast.TGenericAlias n apps -> Ast.TGenericAlias (rename n) (renameAstApps renames apps)

renameAstApps :: [(Text, Text)] -> Ast.TypeApps -> Ast.TypeApps
renameAstApps renames (Ast.TypeApps args) = Ast.TypeApps (map goArg args)
  where
    goArg = \case
      Ast.TAFlat n -> Ast.TAFlat (fromMaybe n (lookup n renames))
      Ast.TAArray t -> Ast.TAArray (goArg t)
      Ast.TAParen t -> Ast.TAParen (goArg t)
      Ast.TAPair l r -> Ast.TAPair (goArg l) (goArg r)
      Ast.TAFunct i o -> Ast.TAFunct (goArg i) (goArg o)
      Ast.TARecord (Ast.RecordTypeArg props) ->
        Ast.TARecord $ Ast.RecordTypeArg
          [ Ast.RecordTypeArgProp c n (goArg t) | Ast.RecordTypeArgProp c n t <- props ]
      Ast.TAMeta n -> Ast.TAMeta n
      Ast.TAGenericAlias n apps ->
        Ast.TAGenericAlias (fromMaybe n (lookup n renames)) (renameAstApps renames apps)

-- | A row with the renamed effect and row names substituted.
renameAstRow :: [(Text, Text)] -> Ast.EffRow -> Ast.EffRow
renameAstRow renames = \case
  Ast.ERVar n -> Ast.ERVar n
  Ast.ERAlias n -> Ast.ERAlias (fromMaybe n (lookup n renames))
  Ast.ERSugar entries tailVar ->
    Ast.ERSugar (map entry entries) tailVar
  where
    entry = \case
      Ast.EREEffCons (Ast.EffCons ec) -> Ast.EREEffCons (Ast.EffCons (cons ec))
      Ast.EREEffCons (Ast.EVar n) -> Ast.EREEffCons (Ast.EVar n)
      Ast.EREEffRow r -> Ast.EREEffRow (renameAstRow renames r)

    cons (Ast.ECons n apps) =
      Ast.ECons (fromMaybe n (lookup n renames)) (renameAstApps renames <$> apps)


lookupDecl :: Ast.Chunk -> Text -> DeclKind -> Maybe ImportedDecl
lookupDecl chunk name kind = listToMaybe $ mapMaybe one (Ast.modDecls chunk)
  where
    one stat
      | Ast.topLevelName stat /= name = Nothing
      | Ast.declKindOf stat /= kind = Nothing
      | otherwise = case stat of
          Ast.TypeDef _ _ ts body -> Just $ ImportedType (name, TypeAliasDef (coerce ts) body)
          Ast.EnumDef _ _ ts _ -> Just $ ImportedType (name, TypeEnumDef (coerce ts))
          Ast.RowDef _ _ row -> Just $ ImportedRow (name, row)
          Ast.EffectDef {} -> Just $ ImportedEffect name
          Ast.FunctDef {} -> Nothing

importedTyps :: [ImportedDecl] -> TypEnv
importedTyps ds = [ (T.unpack n, d) | ImportedType (n, d) <- ds ]

importedRows :: [ImportedDecl] -> [(String, Ast.EffRow)]
importedRows ds = [ (T.unpack n, r) | ImportedRow (n, r) <- ds ]

importedEffects :: [ImportedDecl] -> [String]
importedEffects ds = [ T.unpack n | ImportedEffect n <- ds ]

collectRowEnv :: [Ast.TopLevelStat] -> ElabM RowEnv
collectRowEnv stats = RowEnv <$> foldM addRow [] stats <*> pure effectNames
  where
    effectNames = [ T.unpack n | Ast.EffectDef _ n _ _ <- stats ]

    addRow :: [(String, Ast.EffRow)] -> Ast.TopLevelStat -> ElabM [(String, Ast.EffRow)]
    addRow acc stat = case stat of
      Ast.RowDef _ n row -> do
        let name = T.unpack n
        when (any ((name ==) . fst) acc) $
          throwError $ ElaborationError $ "Duplicate row definition: " <> n
        pure ((name, row) : acc)
      _ -> pure acc

collectTypEnv :: [Ast.TopLevelStat] -> ElabM TypEnv
collectTypEnv = foldM go []
  where
    go :: TypEnv -> Ast.TopLevelStat -> ElabM TypEnv
    go acc stat = case stat of
      Ast.TypeDef _ n ts body -> do
        let name = T.unpack n
        when (any ((name ==) . fst) acc) $
          throwError $ ElaborationError $ "Duplicate type definition: " <> n
        pure ((name, TypeAliasDef (coerce ts) body) : acc)
      Ast.EnumDef _ n ts _ -> do
        let name = T.unpack n
        when (any ((name ==) . fst) acc) $
          throwError $ ElaborationError $ "Duplicate type definition: " <> n
        pure ((name, TypeEnumDef (coerce ts)) : acc)
      _ -> pure acc

elaborateTopLevelStat :: RowEnv -> TypEnv -> Ast.TopLevelStat -> ElabM Types.TopLevelStat
elaborateTopLevelStat = elaborateTopLevelStat' emptyEnv

elaborateTopLevelStat' :: ElabEnv -> RowEnv -> TypEnv -> Ast.TopLevelStat -> ElabM Types.TopLevelStat
elaborateTopLevelStat' env renv tenv = \case
  Ast.TypeDef sp n ts t -> do
    ts' <- for (coerce ts) $ \nm -> (nm,) <$> freshBound nm
    let env' = extendTyp ts' env
    Types.STypeDef sp n (coerce ts) <$> elaborateType' renv tenv env' [] t
  Ast.EffectDef sp n ts ops -> do
    -- The effect's parameters become rigid variables of its operations, so the
    -- declaration records the variables themselves: a use `Loop[Int]` has to
    -- substitute exactly these, and matching them by name would confuse two
    -- effects that both call a parameter `T`.
    ts' <- for (coerce ts) $ \nm -> (nm,) <$> freshBound nm
    let env' = extendTyp ts' env
    Types.SEffDef sp . Types.EffDef n (map snd ts')
      <$> forM ops (\(Ast.EffectOp n' t) -> (n',) <$> elaborateFunct renv tenv env' t)
  Ast.RowDef sp n fxs ->
    Types.SRowDef sp . Types.RowDef n <$> elaborateEffRow' renv tenv env fxs
  Ast.EnumDef sp n ts cases -> do
    -- The parameters are rigid variables of the fields, so the declaration
    -- records the variables themselves: a use `Maybe[Int]` substitutes the
    -- argument for exactly that variable, and matching parameters by name
    -- would confuse two enums that both call a parameter `T`.
    ts' <- for (coerce ts) $ \nm -> (nm,) <$> freshBound nm
    let env' = extendTyp ts' env
    Types.SEnumDef sp . Types.EnumDef n (map snd ts')
      <$> forM cases (\(Ast.EnumCase cn fields) ->
            Types.EnumCase cn <$> forM fields
              (\(q, fn, ft) ->
                (elaborateMutability q, fn,) <$> elaborateType' renv tenv env' [] ft))
  Ast.FunctDef sp n ts (Ast.EffParams es rs) args fxs t b -> do
    ts' <- for (coerce ts) $ \nm -> (nm,) <$> freshBound nm
    es' <- for es $ \nm -> (nm,) <$> freshBound nm
    rs' <- for rs $ \nm -> (nm,) <$> freshBound nm
    let env' = extendRow rs' $ extendEff es' $ extendTyp ts' env
    args' <- forM args $ \case
      Ast.NamedFunctArg n' t' -> (n',) <$> elaborateType' renv tenv env' [] t'
      Ast.NilArg -> pure (".", Types.TNil)
    fxs' <- for fxs $ elaborateEffRow' renv tenv env'
    t' <- elaborateType' renv tenv env' [] t
    Types.SFunctDef sp . Types.FunctDecl
      n
      (coerce ts)
      es
      rs
      args'
      (fxs', t')
      <$> elaborateBlock renv tenv env' b

elaborateBlock :: RowEnv -> TypEnv -> ElabEnv -> Ast.Block -> ElabM Types.Block
elaborateBlock renv tenv env (Ast.Block stats e) = do
  stats' <- forM stats $ elaborateBlockStat renv tenv env
  e' <- elaborateExpr renv tenv env e
  pure (stats', e')

elaborateBlockStat :: RowEnv -> TypEnv -> ElabEnv -> Ast.BlockStat -> ElabM Types.Stat
elaborateBlockStat renv tenv env st =
  Types.atStatSpan (Ast.bsSpan st) <$> elaborateStatNode renv tenv env (Ast.bsNode st)

elaborateStatNode :: RowEnv -> TypEnv -> ElabEnv -> Ast.BlockStatNode -> ElabM Types.Stat
elaborateStatNode renv tenv env = \case
  Ast.BExpNode e -> Types.Expr <$> elaborateExpr renv tenv env e
  Ast.BAssignNode (Ast.Assign n path e) ->
    Types.Assign n path <$> elaborateExpr renv tenv env e
  Ast.BBindDefNode (Ast.BindDef c (Ast.LambdaParam n t) e) ->
    Types.Bind (elaborateMutability c) n <$> for t (elaborateType' renv tenv env []) <*> elaborateExpr renv tenv env e

elaborateApply :: RowEnv -> TypEnv -> ElabEnv -> Bool -> Ast.Exp -> Ast.Exp -> ElabM Types.Expr
elaborateApply renv tenv env wrapInParens f e = do
  f' <- elaborateExpr renv tenv env f
  e' <- elaborateExpr renv tenv env e
  let e'' = if wrapInParens then Types.Paren ([], e') else e'
  pure $ Types.Apply f' e''

-- | Elaborate an expression, keeping the position of its AST node.  The span of
--   the AST node is authoritative: it is the region the user wrote.
elaborateExpr :: RowEnv -> TypEnv -> ElabEnv -> Ast.Exp -> ElabM Types.Expr
elaborateExpr renv tenv env e =
  Types.atSpan (Ast.expSpan e) <$> elaborateNode renv tenv env e

elaborateNode :: RowEnv -> TypEnv -> ElabEnv -> Ast.Exp -> ElabM Types.Expr
elaborateNode renv tenv env = \case
  Ast.EName n -> pure $ Types.XVar n
  Ast.EApply f e -> elaborateApply renv tenv env False f e
  Ast.EDollar f e -> elaborateApply renv tenv env True f e
  Ast.ELiteral l -> case l of
    Ast.LAtom a -> case a of
      Ast.AString s -> pure $ Types.String s
      Ast.ANumber (Ast.NInt i) -> pure $ Types.Int i
      Ast.ANumber (Ast.NFloat f) -> pure $ Types.Float f
      Ast.ANil -> pure Types.Nil
      Ast.ABoolean b -> pure $ Types.Boolean b
    Ast.LArray (Ast.ArrayLiteral es) ->
      Types.Array <$> traverse (\case
        Ast.AEExp e -> elaborateExpr renv tenv env e
        Ast.AEBlock b -> Types.Paren <$> elaborateBlock renv tenv env b) es
    Ast.LLambda l' -> elaborateLambdaLiteral renv tenv env l'
    Ast.LRecord (Ast.RecordLiteral e props) -> do
      e' <- mapM (elaborateExpr renv tenv env) e
      Types.Record e' <$> mapM go props
      where
        go :: Ast.BindDef -> ElabM Types.ERecordProp
        go (Ast.BindDef c (Ast.LambdaParam n t) e') =
          Types.ERecordProp (elaborateMutability c) n <$> mapM (elaborateType' renv tenv env []) t <*> elaborateExpr renv tenv env e'
  Ast.EPair l r -> Types.Pair <$> elaborateExpr renv tenv env l <*> elaborateExpr renv tenv env r
  Ast.ELet lp wht whr ->
    Types.Let <$> elaborateLetPattern renv tenv env lp <*> elaborateExpr renv tenv env wht <*> elaborateExpr renv tenv env whr
  Ast.EBacktick op l r ->
    Types.Apply . Types.Apply (Types.XVar op)
      <$> elaborateExpr renv tenv env l
      <*> elaborateExpr renv tenv env r
  Ast.EPropAccess e n -> (`Types.PropAccess` n) <$> elaborateExpr renv tenv env e
  Ast.EIfThenElse p t f ->
    Types.IfElse
      <$> elaborateExpr renv tenv env p
      <*> elaborateExpr renv tenv env t
      <*> elaborateExpr renv tenv env f
  Ast.EResume e -> Types.Resume <$> elaborateExpr renv tenv env e
  Ast.EWith e tas (Ast.EffApps eas ras) -> do
    Types.With
      <$> elaborateExpr renv tenv env e
      <*> mapM (elaborateTypeArg tenv env) (coerce tas)
      <*> (concat <$> mapM (elaborateEffArg renv tenv env) eas)
      <*> forM ras (elaborateEffRow' renv tenv env)
  Ast.EUnder u -> elaborateUnder renv tenv env u
  Ast.EParen b -> Types.Paren <$> elaborateBlock renv tenv env b
  Ast.EAnnot e t ->
    Types.Annot
      <$> elaborateExpr renv tenv env e
      <*> elaborateType' renv tenv env [] t
  Ast.EMatch e cs ->
    Types.Match
      <$> elaborateExpr renv tenv env e
      <*> mapM (elaborateMatchClause renv tenv env) cs

elaborateMatchClause :: RowEnv -> TypEnv -> ElabEnv -> Ast.MatchClause -> ElabM Types.MatchClause
elaborateMatchClause renv tenv env (Ast.MatchClause ps g b) =
  Types.MatchClause
    <$> mapM (elaboratePattern renv tenv env) ps
    <*> mapM (elaborateExpr renv tenv env) g
    <*> elaborateBlock renv tenv env b

elaboratePattern :: RowEnv -> TypEnv -> ElabEnv -> Ast.Pattern -> ElabM Types.Pattern
elaboratePattern renv tenv env (Ast.MkPattern sp node) =
  Types.MkPattern sp <$> go node
  where
    recur = elaboratePattern renv tenv env

    go = \case
      Ast.PInt i -> pure $ Types.PInt i
      Ast.PFloat f -> pure $ Types.PFloat f
      Ast.PString t -> pure $ Types.PString t
      Ast.PNil -> pure Types.PNil
      Ast.PBoolean b -> pure $ Types.PBoolean b
      Ast.PName n -> pure $ Types.PName n
      Ast.PVal e path -> Types.PVal <$> elaborateExpr renv tenv env e <*> pure path
      Ast.PArray ps t -> Types.PArray <$> mapM recur ps <*> mapM recur t
      Ast.PTuple ps -> Types.PTuple <$> mapM recur ps
      Ast.PCon n ps -> Types.PCon n <$> mapM recur ps
      Ast.PAs p n -> Types.PAs <$> recur p <*> pure n
      Ast.PCast p t -> Types.PCast <$> recur p <*> elaborateType' renv tenv env [] t
      Ast.PWildcard -> pure Types.PWildcard
      -- Parentheses group a pattern; the grouping has no meaning once the
      -- tree is built, so the node is dropped rather than kept as a wrapper.
      Ast.PParen p -> Types.patNode <$> recur p
      Ast.PStarts l r -> Types.PStarts <$> recur l <*> recur r
      Ast.PEnds l r -> Types.PEnds <$> recur l <*> recur r

elaborateUnder :: RowEnv -> TypEnv -> ElabEnv -> Ast.Under -> ElabM Types.Expr
elaborateUnder renv tenv env = \case
  Ast.Under eff blk clauses thenN thenB ->
    Types.Handle
      <$> (Types.Handler
            <$> elaborateEffCons tenv env (Ast.EffCons eff)
            <*> elaborateBlock renv tenv env blk
            <*> mapM (elaborateHandlerClause renv tenv env) clauses
            <*> elaborateThenClause renv tenv env thenN thenB)

elaborateThenClause :: RowEnv -> TypEnv -> ElabEnv -> Text -> Ast.Block -> ElabM Types.Lambda
elaborateThenClause renv tenv env n = elaboratePlainLambda renv tenv env [n]

elaboratePlainLambda :: RowEnv -> TypEnv -> ElabEnv -> [Text] -> Ast.Block -> ElabM Types.Lambda
elaboratePlainLambda renv tenv env params body =
  case params of
    [] ->
      Types.Lambda [] [] "." Nothing Nothing
        (Types.RClosed [])
        <$> elaborateBlock renv tenv env body
    [n] ->
      Types.Lambda [] [] n Nothing Nothing
        (Types.RClosed [])
        <$> elaborateBlock renv tenv env body
    n : rest ->
      Types.Lambda [] [] n Nothing Nothing
        (Types.RClosed []) . ([] , ) . Types.XLambda <$> elaboratePlainLambda renv tenv env rest body

elaborateHandlerClause :: RowEnv -> TypEnv -> ElabEnv -> Ast.HandlerClause -> ElabM Types.HandlerClause
elaborateHandlerClause renv tenv env (Ast.HandlerClause op ns b) =
  (op, ) <$> elaboratePlainLambda renv tenv env ns b

elaborateEffArg :: RowEnv -> TypEnv -> ElabEnv -> Ast.EffArg -> ElabM [Types.EffCons]
elaborateEffArg renv tenv env = \case
  Ast.EACons c -> do
    c' <- elaborateEffCons tenv env c
    pure [c']
  Ast.EARow row -> do
    row' <- elaborateEffRow' renv tenv env row
    case row' of
      Types.RClosed cs -> pure cs
      Types.ROpen {} -> elabError "Open effect rows are not allowed in with effect arguments"
      Types.RVar _ -> elabError "Bare effect row variable is not allowed in with effect arguments"

elaborateLetPatternRecordProp :: RowEnv -> TypEnv -> ElabEnv -> Ast.AtomLetPatternRecordProp -> ElabM Types.LetPatternRecordProp
elaborateLetPatternRecordProp renv tenv env (Ast.AtomLetPatternRecordProp q lp alp) = do
  lp' <- elaborateLambdaParam renv tenv env lp
  alp' <- case alp of
    Just a -> Just <$> elaborateAtomLetPattern renv tenv env a
    _ -> pure Nothing
  pure $ Types.LetPatternRecordProp (elaborateMutability q) lp' alp'

elaborateLambdaParam :: RowEnv -> TypEnv -> ElabEnv -> Ast.LambdaParam -> ElabM Types.LambdaParam
elaborateLambdaParam renv tenv env (Ast.LambdaParam n mt) = do
  Types.LambdaParam n <$> mapM (elaborateType' renv tenv env []) mt

elaborateLetPattern :: RowEnv -> TypEnv -> ElabEnv -> Ast.LetPattern -> ElabM Types.LetPattern
elaborateLetPattern renv tenv env = \case
  Ast.LPATom (Ast.ALPParen lp) -> elaborateLetPattern renv tenv env lp
  Ast.LPATom alp -> Types.LPATom <$> elaborateAtomLetPattern renv tenv env alp
  Ast.LPParam lp -> Types.LPParam <$> elaborateLambdaParam renv tenv env lp

stripParenLetPattern :: Ast.LetPattern -> Ast.LetPattern
stripParenLetPattern = \case
  Ast.LPATom (Ast.ALPParen lp) -> stripParenLetPattern lp
  lp -> lp

elaborateAtomLetPattern :: RowEnv -> TypEnv -> ElabEnv -> Ast.AtomLetPattern -> ElabM Types.AtomLetPattern
elaborateAtomLetPattern renv tenv env = \case
  Ast.ALPNil -> pure Types.ALPNil
  Ast.ALPUnderscore -> pure Types.ALPUnderscore
  Ast.ALPPair l r ->
    Types.ALPPair <$> elaborateLetPattern renv tenv env l <*> elaborateLetPattern renv tenv env r
  Ast.ALPParen lp ->
    case stripParenLetPattern lp of
      Ast.LPATom alp -> elaborateAtomLetPattern renv tenv env alp
      Ast.LPParam _ -> elabError "Parenthesized lambda parameter is not an atomic let pattern"
  Ast.ALPRecord props ->
    Types.ALPRecord <$> mapM (elaborateLetPatternRecordProp renv tenv env) props

elaborateLambdaLiteral :: RowEnv -> TypEnv -> ElabEnv -> Ast.LambdaLiteral -> ElabM Types.Expr
elaborateLambdaLiteral renv tenv env (Ast.LambdaLiteral mtps mfxs mhead body) =
  case mhead of
    Nothing -> do
      mtps' <- maybe (pure []) (mapM freshBound . coerce) mtps
      (meps, mrps, meps', mrps') <- case mfxs of
        Nothing -> pure (Nothing, Nothing, [], [])
        Just (Ast.EffParams meps mrps) -> (Just meps, Just mrps, ,) <$> mapM freshBound meps <*> mapM freshBound mrps
      let env' =
            extendRow (zip (fromMaybe [] mrps) mrps') $
            extendEff (zip (fromMaybe [] meps) meps') $
            extendTyp (zip (maybe [] coerce mtps) mtps') env
      Types.XLambda . Types.Lambda
        mtps'
        meps'
        "."
        Nothing
        Nothing
        (Types.RClosed [])
        <$> elaborateBlock renv tenv env' body
    Just (Ast.LambdaHead params retT) -> do
      mtps' <- maybe (pure []) (mapM freshBound . coerce) mtps
      (meps, mrps, meps', mrps') <- case mfxs of
        Nothing -> pure (Nothing, Nothing, [], [])
        Just (Ast.EffParams meps mrps) -> (Just meps, Just mrps, ,) <$> mapM freshBound meps <*> mapM freshBound mrps
      let env' =
            extendRow (zip (fromMaybe [] mrps) mrps') $
            extendEff (zip (fromMaybe [] meps) meps') $
            extendTyp (zip (maybe [] coerce mtps) mtps') env
      elaborateCurriedLambda
        renv
        tenv
        env'
        mtps'
        meps'
        params
        retT
        body

elaborateCurriedLambda :: RowEnv
  -> TypEnv
  -> ElabEnv
  -> [Taste]
  -> [Taste]
  -> [Ast.LambdaParam]
  -> Maybe Ast.Typ
  -> Ast.Block
  -> ElabM Types.Expr
elaborateCurriedLambda renv tenv env tps eps params retT body =
  Types.XLambda <$> case params of
    [] -> elabError "Lambda head must contain at least one parameter"
    [Ast.LambdaParam n argT] ->
      Types.Lambda
        tps
        eps
        n
        <$> mapM (elaborateType' renv tenv env []) argT
        <*> mapM (elaborateType' renv tenv env []) retT
        <*> pure (Types.RClosed [])
        <*> elaborateBlock renv tenv env body
    Ast.LambdaParam n argT : rest -> do
      innerExpr <- elaborateCurriedLambda renv tenv env [] [] rest retT body
      argT' <- mapM (elaborateType' renv tenv env []) argT
      pure $ Types.Lambda
        tps
        eps
        n
        argT'
        Nothing
        (Types.RClosed [])
        ([], innerExpr)

elaborateFunct :: RowEnv -> TypEnv -> ElabEnv -> Ast.Funct -> ElabM Types.Funct
elaborateFunct renv tenv env (Ast.Funct i o fxs) =
  Types.Funct
    <$> elaborateType' renv tenv env [] i
    <*> elaborateType' renv tenv env [] o
    <*> elaborateEffRow' renv tenv env fxs

-- elaborateType :: RowEnv -> TypEnv -> Ast.Typ -> ElabM Types.Typ
-- elaborateType renv tenv = elaborateType' renv tenv emptyEnv []

-- | The type names the language provides by itself, used to suggest a
--   correction when a declared name is misspelled.
builtinTypeNames :: [Text]
builtinTypeNames = ["Int", "Float", "Boolean", "String", "Nil", "Nothing"]

elaborateType' :: RowEnv -> TypEnv -> ElabEnv -> [Text] -> Ast.Typ -> ElabM Types.Typ
elaborateType' renv tenv env visiting = \case
  Ast.TFlat n
    -- A type parameter declared by the enclosing `funct [T]` or `type Box[T]`
    -- shadows a declared alias of the same name, so it is looked up first.
    -- Without this, the parameter stays an opaque `TFlat` and a scheme that
    -- quantifies over it quantifies over nothing: `funct id[T] (x T) : T = x`
    -- then rejects `id 1` with "cannot unify Int with T".
    | Just bound <- lookupTyp env n -> pure $ Types.TVar bound
    | otherwise -> case n of
    "Int" -> pure Types.TInt
    "Float" -> pure Types.TFloat
    "Boolean" -> pure Types.TBoolean
    "String" -> pure Types.TString
    "Nil" -> pure Types.TNil
    "Nothing" -> pure Types.TNothing
    _ ->
      case lookup (T.unpack n) tenv of
        Just (TypeAliasDef params _)
          | null params -> expandTypeAlias' renv tenv env visiting n (Ast.TypeApps [])
          | otherwise ->
              elabError $ printf
                "Type alias '%s' expects %d argument(s), but was used without any"
                (T.unpack n)
                (length params)
        Just (TypeEnumDef params)
          | null params -> pure $ Types.TEnum n []
          | otherwise ->
              elabError $ printf
                "Enum '%s' expects %d type argument(s), but was used without any"
                (T.unpack n)
                (length params)
        Nothing -> case Suggest.typoNote (builtinTypeNames <> map (T.pack . fst) tenv) n of
          -- A name that is one typo away from a type that exists is almost
          -- certainly that type: silently inventing an opaque `TFlat` would
          -- report the mistake later as a mysterious unification failure.
          -- A name that is not close to anything stays opaque, because a
          -- program may legitimately use a type it does not declare.
          Just hint -> elabError $ printf "unknown type '%s'; %s" (T.unpack n) (T.unpack hint)
          Nothing -> pure $ Types.TFlat n
  Ast.TNil -> pure Types.TNil
  Ast.TArray t -> do
    t' <- elaborateType' renv tenv env visiting t
    pure $ Types.TArray t' (RClosed [])
  Ast.TParen t -> elaborateType' renv tenv env visiting t
  Ast.TPair l r -> do
    l' <- elaborateType' renv tenv env visiting l
    r' <- elaborateType' renv tenv env visiting r
    pure $ Types.TPair l' r' (RClosed [])
  Ast.TFunct (Ast.Funct i o fxs) -> do
      i' <- elaborateType' renv tenv env visiting i
      o' <- elaborateType' renv tenv env visiting o
      fxs' <- elaborateEffRow' renv tenv env fxs
      pure $ Types.TFunct $ Types.Funct i' o' fxs'
  Ast.TRecord (Ast.RecordTyp props) -> do
    props' <- mapM (\(Ast.RecordTypProp c n t) ->
        Types.TRecordProp (elaborateMutability c) n <$> elaborateType' renv tenv env visiting t)
      props
    pure $ Types.TRecord props' (RClosed [])
  Ast.TPending base row -> do
    base' <- elaborateType' renv tenv env visiting base
    row' <- elaborateEffRow' renv tenv env row
    case base' of
      Types.TArray t _ -> pure $ Types.TArray t row'
      Types.TPair l r _ -> pure $ Types.TPair l r row'
      Types.TRecord props _ -> pure $ Types.TRecord props row'
      _ -> elabError
        "the pending row `@R` may only be written on an array, a pair or a record type"
  Ast.TForall (Ast.TypeParams ts) (Ast.EffParams es rs) t -> do
    ts' <- traverse (\n -> (n, ) <$> freshBound n) ts
    es' <- traverse (\n -> (n, ) <$> freshBound n) es
    rs' <- traverse (\n -> (n, ) <$> freshBound n) rs
    let env' = extendEff es' $ extendTyp ts' env
    Types.TForall
      (map snd ts') (map snd es') (map snd rs')
      Map.empty
      Map.empty
      <$> elaborateType' renv tenv env' visiting t
  Ast.TVar t -> Types.TVar <$> getBoundOrMakeMeta typBounds iTypVars env t
    -- case lookupTyp env t of
    --   Just t' -> pure $ Types.TVar t'
    --   _ -> case lookupITyp env t of
    --     Just t' -> pure $ Types.TVar t'
    --     _ -> do
    --       meta <- freshMeta t
    --       let _ = extendITyp [(t, meta)] env
    --       pure $ Types.TVar meta
  Ast.TGenericAlias n ts -> expandTypeAlias' renv tenv env visiting n ts

expandTypeAlias' :: RowEnv -> TypEnv -> ElabEnv -> [Text] -> Text -> Ast.TypeApps -> ElabM Types.Typ
expandTypeAlias' renv tenv env visiting n (Ast.TypeApps ts)
  | n `elem` visiting = elabError $ "Cyclic type alias: " <> T.unpack n
  | otherwise =
    case lookup (T.unpack n) tenv of
      Nothing -> elabError $ "Unknown type alias: " <> T.unpack n
      Just (TypeEnumDef params) ->
        if length params /= length ts then
          elabError $ printf
            "Wrong number of type arguments for enum '%s': expected %d, got %d"
            (T.unpack n)
            (length params)
            (length ts)
        else
          mapM (elaborateTypeArg tenv env) (coerce ts) >>= \args ->
            pure $ Types.TEnum n args
      Just (TypeAliasDef params body) ->
        if length params /= length ts then
          elabError $ printf
            "Wrong number of type arguments for alias '%s': expected %d, got %d"
            (T.unpack n)
            (length params)
            (length ts)
        else
          let body' = substTypeInTyp (zip params ts) body
          in elaborateType' renv tenv env (n : visiting) body'

elaborateTypeArg :: TypEnv -> ElabEnv -> Ast.TypeArg -> ElabM Types.TypeArg
elaborateTypeArg tenv env = elaborateTypeArg' tenv env []

elaborateTypeArg' :: TypEnv -> ElabEnv -> [Text] -> Ast.TypeArg -> ElabM Types.TypeArg
elaborateTypeArg' tenv env visiting = \case
  Ast.TAFlat n
    -- A type parameter declared by the enclosing `funct [T]` or `effect E[T]`
    -- shadows a declared alias of the same name, so it is looked up first.
    -- Without this, `effect Loop[T] ... break : `T -> ()` keeps `T` opaque and
    -- a `loop[T]` program is rejected with "cannot unify `T with a meta".
    | Just bound <- lookupTyp env n -> pure $ Types.TAVar bound
    | otherwise -> case n of
    "Int" -> pure Types.TAInt
    "Float" -> pure Types.TAFloat
    "Boolean" -> pure Types.TABoolean
    "String" -> pure Types.TAString
    "Nil" -> pure Types.TANil
    "Nothing" -> pure Types.TANothing
    _ ->
      case lookup (T.unpack n) tenv of
        Just (TypeAliasDef params _)
          | null params -> expandTypeArgAlias' tenv env visiting n (Ast.TypeApps [])
          | otherwise ->
              elabError $ printf
                "Type alias '%s' expects %d argument(s), but was used without any"
                (T.unpack n)
                (length params)
        Just (TypeEnumDef params)
          | null params -> pure $ Types.TAEnum n []
          | otherwise ->
              elabError $ printf
                "Enum '%s' expects %d type argument(s), but was used without any"
                (T.unpack n)
                (length params)
        Nothing -> pure $ Types.TAFlat n
  Ast.TANil -> pure Types.TANil
  Ast.TAArray t -> Types.TAArray <$> elaborateTypeArg' tenv env visiting t
  Ast.TAParen t -> elaborateTypeArg' tenv env visiting t
  Ast.TAPair l r -> Types.TAPair <$> elaborateTypeArg' tenv env visiting l <*> elaborateTypeArg' tenv env visiting r
  Ast.TAFunct i o -> Types.TAFunct <$> elaborateTypeArg' tenv env visiting i <*> elaborateTypeArg' tenv env visiting o
  Ast.TARecord (Ast.RecordTypeArg props) ->
    Types.TARecord <$>
      mapM (\(Ast.RecordTypeArgProp c n t) ->
        Types.TARecordProp (elaborateMutability c) n <$> elaborateTypeArg' tenv env visiting t)
      props
  Ast.TAMeta t -> Types.TAVar <$> getBoundOrMakeMeta typBounds iTypVars env t
  Ast.TAGenericAlias n ts -> expandTypeArgAlias' tenv env visiting n ts

-- expandTypeArgAlias :: TypEnv -> Text -> Ast.TypeApps -> ElabM Types.TypeArg
-- expandTypeArgAlias tenv = expandTypeArgAlias' tenv emptyEnv []

expandTypeArgAlias' :: TypEnv -> ElabEnv -> [Text] -> Text -> Ast.TypeApps -> ElabM Types.TypeArg
expandTypeArgAlias' tenv env visiting n (Ast.TypeApps ts)
  | n `elem` visiting =
      elabError $ "Cyclic type alias: " <> T.unpack n
  | otherwise =
      case lookup (T.unpack n) tenv of
        Nothing ->
          elabError $ "Unknown type alias: " <> T.unpack n
        Just (TypeEnumDef params) ->
          if length params /= length ts then
            elabError $ printf
              "Wrong number of type arguments for enum '%s': expected %d, got %d"
              (T.unpack n)
              (length params)
              (length ts)
          else
            Types.TAEnum n <$> mapM (elaborateTypeArg' tenv env visiting) (coerce ts)
        Just (TypeAliasDef params body) ->
          if length params /= length ts then
            elabError $ printf
              "Wrong number of type arguments for alias '%s': expected %d, got %d"
              (T.unpack n)
              (length params)
              (length ts)
          else
            case typToTypeArg body of
              Left err ->
                elabError $ printf
                  "Type alias %s is not valid in type-argument position: %s"
                  (T.unpack n)
                  err
              Right bodyArg ->
                elaborateTypeArg' tenv env (n : visiting) $
                  substTypeInTypeArg (zip params ts) bodyArg

substTypeInTyp :: [(Text, Ast.TypeArg)] -> Ast.Typ -> Ast.Typ
substTypeInTyp subst = \case
  Ast.TFlat n -> Ast.TFlat n
  Ast.TNil -> Ast.TNil
  Ast.TArray t -> Ast.TArray $ substTypeInTyp subst t
  Ast.TParen t -> Ast.TParen $ substTypeInTyp subst t
  Ast.TPair l r -> Ast.TPair (substTypeInTyp subst l) (substTypeInTyp subst r)
  Ast.TFunct (Ast.Funct i o fxs) ->
    Ast.TFunct $ Ast.Funct
      (substTypeInTyp subst i)
      (substTypeInTyp subst o)
      (substTypeInEffRow subst fxs)
  Ast.TRecord (Ast.RecordTyp props) ->
    Ast.TRecord $ Ast.RecordTyp $
      map (\(Ast.RecordTypProp q n t) ->
        Ast.RecordTypProp q n (substTypeInTyp subst t)) props
  Ast.TPending t r -> Ast.TPending (substTypeInTyp subst t) r
  Ast.TForall (Ast.TypeParams ts) es t ->
    let subst' = filter (\(name, _) -> name `notElem` ts) subst
    in Ast.TForall (Ast.TypeParams ts) es (substTypeInTyp subst' t)
  Ast.TVar v ->
    case lookup v subst of
      Just arg -> typeArgToTyp arg
      Nothing -> Ast.TVar v
  Ast.TGenericAlias n apps ->
    Ast.TGenericAlias n $ substTypeApps subst apps

substTypeInEffRow :: [(Text, Ast.TypeArg)] -> Ast.EffRow -> Ast.EffRow
substTypeInEffRow subst = \case
  Ast.ERSugar entries t -> Ast.ERSugar (substTypeInEffRowEntry subst <$> entries) t
  r -> r

substTypeInEffRowEntry :: [(Text, Ast.TypeArg)] -> Ast.EffRowEntry -> Ast.EffRowEntry
substTypeInEffRowEntry subst = \case
  Ast.EREEffCons eff -> Ast.EREEffCons $ substTypeInEffCons subst eff
  Ast.EREEffRow row -> Ast.EREEffRow $ substTypeInEffRow subst row

substTypeInEffCons :: [(Text, Ast.TypeArg)] -> Ast.EffCons -> Ast.EffCons
substTypeInEffCons subst = \case
  Ast.EffCons (Ast.ECons n mts) -> Ast.EffCons $ Ast.ECons n $ substTypeApps subst <$> mts
  v@(Ast.EVar _) -> v

substTypeApps :: [(Text, Ast.TypeArg)] -> Ast.TypeApps -> Ast.TypeApps
substTypeApps subst (Ast.TypeApps ts) = Ast.TypeApps $ substTypeInTypeArg subst <$> ts

substTypeInTypeArg :: [(Text, Ast.TypeArg)] -> Ast.TypeArg -> Ast.TypeArg
substTypeInTypeArg subst = \case
  Ast.TAFlat n -> Ast.TAFlat n
  Ast.TANil -> Ast.TANil
  Ast.TAArray t -> Ast.TAArray $ substTypeInTypeArg subst t
  Ast.TAParen t -> Ast.TAParen $ substTypeInTypeArg subst t
  Ast.TAPair l r -> Ast.TAPair (substTypeInTypeArg subst l) (substTypeInTypeArg subst r)
  Ast.TAFunct i o -> Ast.TAFunct (substTypeInTypeArg subst i) (substTypeInTypeArg subst o)
  Ast.TARecord (Ast.RecordTypeArg props) ->
    Ast.TARecord $ Ast.RecordTypeArg $
      map (\(Ast.RecordTypeArgProp q n t) ->
        Ast.RecordTypeArgProp q n (substTypeInTypeArg subst t)) props
  Ast.TAMeta v ->
    case lookup v subst of
      Just arg -> arg
      Nothing -> Ast.TAMeta v
  Ast.TAGenericAlias n apps ->
    Ast.TAGenericAlias n $ substTypeApps subst apps

typeArgToTyp :: Ast.TypeArg -> Ast.Typ
typeArgToTyp = \case
  Ast.TAFlat n -> Ast.TFlat n
  Ast.TANil -> Ast.TNil
  Ast.TAArray t -> Ast.TArray $ typeArgToTyp t
  Ast.TAParen t -> Ast.TParen $ typeArgToTyp t
  Ast.TAPair l r -> Ast.TPair (typeArgToTyp l) $ typeArgToTyp r
  Ast.TAFunct i o -> Ast.TFunct $ Ast.Funct (typeArgToTyp i) (typeArgToTyp o) (Ast.ERSugar [] Nothing)
  Ast.TARecord (Ast.RecordTypeArg props) ->
    Ast.TRecord $ Ast.RecordTyp $
      map (\(Ast.RecordTypeArgProp q n t) -> Ast.RecordTypProp q n (typeArgToTyp t)) props
  Ast.TAMeta t -> Ast.TVar t
  Ast.TAGenericAlias n apps -> Ast.TGenericAlias n apps

typToTypeArg :: Ast.Typ -> Either String Ast.TypeArg
typToTypeArg = \case
  Ast.TFlat n -> Right $ Ast.TAFlat n
  Ast.TNil -> Right Ast.TANil
  Ast.TArray t -> Ast.TAArray <$> typToTypeArg t
  Ast.TParen t -> Ast.TAParen <$> typToTypeArg t
  Ast.TPair l r -> Ast.TAPair <$> typToTypeArg l <*> typToTypeArg r
  Ast.TFunct (Ast.Funct i o (Ast.ERSugar [] Nothing)) ->
    Ast.TAFunct <$> typToTypeArg i <*> typToTypeArg o
  Ast.TFunct Ast.Funct{} ->
    Left "Effectful function types are not allowed in type arguments"
  Ast.TRecord (Ast.RecordTyp props) ->
    Ast.TARecord . Ast.RecordTypeArg <$>
      traverse (\(Ast.RecordTypProp q n t) -> Ast.RecordTypeArgProp q n <$> typToTypeArg t) props
  Ast.TPending {} ->
    Left "The pending row `@R` of an aggregate is not allowed in type-argument position"
  Ast.TForall {} ->
    Left "Forall types are not allowed in type arguments"
  Ast.TVar t -> pure $ Ast.TAMeta t
  Ast.TGenericAlias n ts -> pure $ Ast.TAGenericAlias n ts

elaborateMutability :: Ast.ConstantQualifier -> Types.Mutability
elaborateMutability = \case
  Ast.Val -> Types.Val
  Ast.Var -> Types.Var
  Ast.Imm -> Types.Imm

elaborateEffRow :: RowEnv -> TypEnv -> Ast.EffRow -> ElabM Types.EffRow
elaborateEffRow renv tenv = elaborateEffRow' renv tenv emptyEnv

elaborateEffRow' :: RowEnv -> TypEnv -> ElabEnv -> Ast.EffRow -> ElabM Types.EffRow
elaborateEffRow' renv tenv env row = do
  FlatRow cons t <- flattenEffRow renv tenv env [] row
  pure $ case t of
    Just v -> Types.ROpen (uniqPreserveOrder cons) v
    _ -> Types.RClosed (uniqPreserveOrder cons)

flattenEffRow :: RowEnv -> TypEnv -> ElabEnv -> [String] -> Ast.EffRow -> ElabM FlatRow
flattenEffRow renv tenv env visiting = \case
  Ast.ERAlias n ->
    let name = T.unpack n
        aliases = rowAliases renv
    in if name `elem` visiting then
      elabError $ "Cyclic row alias: " <> name
    else
      case lookup name aliases of
        -- An effect is not a row: `{Doubt}` names a row containing the effect,
        -- but a bare `Doubt` in row position would mean "the row of Doubt",
        -- which does not exist.  The name is declared, so the mistake is not a
        -- typo and must not be reported as an unknown alias.
        Nothing | name `elem` declaredEffects renv ->
          elabError $ printf
            "`%s` is an effect, not a row: write `{%s}` to put it in a row"
            name name
        Nothing -> case Suggest.suggestionNote (map (T.pack . fst) aliases) (T.pack name) of
          Just hint -> elabError $ "Unknown row alias: " <> name <> "; " <> T.unpack hint
          Nothing -> elabError $ "Unknown row alias: " <> name
        Just row -> flattenEffRow renv tenv env (name : visiting) row
  Ast.ERSugar entries Nothing -> do
    foldM (\acc entry ->
        mergeFlatRows acc =<< flattenEffRowEntry renv tenv env visiting entry
      ) emptyFlatRow entries
  Ast.ERSugar entries (Just t) -> do
    fromEntries <- foldM (\acc entry -> do
        mergeFlatRows acc =<< flattenEffRowEntry renv tenv env visiting entry
      ) emptyFlatRow entries
    mergeFlatRows fromEntries . FlatRow [] . Just =<< getBoundOrMakeMeta rowBounds iRowVars env t
      -- case lookupRow env t of
      --   Just t' -> pure $ FlatRow [] $ Just t'
      --   _ -> case lookupIRow env t of
      --     Just t' -> pure $ FlatRow [] $ Just t'
      --     _ -> do
      --       meta <- freshMeta t
      --       let _ = extendIRow [(t, meta)] env
      --       pure $ FlatRow [] $ Just meta
  Ast.ERVar n -> FlatRow [] . Just <$> getBoundOrMakeMeta rowBounds iRowVars env n --do
    -- case lookupRow env n of
    --   Just n' -> pure $ FlatRow [] $ Just n'
    --   _ -> case lookupIRow env n of
    --     Just n' -> pure $ FlatRow [] $ Just n'
    --     _ -> do
    --       meta <- freshMeta n
    --       let _ = extendIRow [(n, meta)] env
    --       pure $ FlatRow [] $ Just meta

flattenEffRowEntry :: RowEnv -> TypEnv -> ElabEnv -> [String] -> Ast.EffRowEntry -> ElabM FlatRow
flattenEffRowEntry renv tenv env visiting = \case
  Ast.EREEffCons c -> do
    c' <- elaborateEffCons tenv env c
    pure $ FlatRow [c'] Nothing
  Ast.EREEffRow r -> flattenEffRow renv tenv env visiting r

emptyFlatRow :: FlatRow
emptyFlatRow = FlatRow [] Nothing

mergeFlatRows :: FlatRow -> FlatRow -> ElabM FlatRow
mergeFlatRows (FlatRow cons1 t1) (FlatRow cons2 t2) =
  case (t1, t2) of
    (Nothing, Nothing) -> pure $ FlatRow (cons1 <> cons2) Nothing
    (Just t, Nothing) -> pure $ FlatRow (cons1 <> cons2) (Just t)
    (Nothing, Just t) -> pure $ FlatRow (cons1 <> cons2) (Just t)
    (Just _, Just _) -> elabError "Multiple effect row tails in one row"

elaborateEffCons :: TypEnv -> ElabEnv -> Ast.EffCons -> ElabM Types.EffCons
elaborateEffCons tenv env = \case
  Ast.EffCons (Ast.ECons n apps) ->
    Types.EffCons . Types.ECons n <$> maybe (pure []) (mapM (elaborateTypeArg tenv env) . coerce) apps
  Ast.EVar n -> Types.EVar <$> getBoundOrMakeMeta rowBounds iRowVars env n
    -- case lookupEff env n of
    --   Just n' -> pure $ Types.EVar n'
    --   _ -> case lookupIEff env n of
    --     Just n' -> pure $ Types.EVar n'
    --     _ -> do
    --       meta <- freshMeta n
    --       let _ = extendIEff [(n, meta)] env
    --       pure $ Types.EVar meta