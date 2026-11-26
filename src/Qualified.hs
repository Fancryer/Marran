{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

-- | Qualified names, @Module::name@.
--
--   The parser keeps a qualified name as the one string it was written as,
--   because only the loader knows what a module is: at parse time @M@ is just a
--   word.  This module is the syntactic half of resolution -- it walks a file
--   and reports every qualified name with the namespace the position implies,
--   and it can rewrite names on the way through.  The loader decides what each
--   one means and calls @mapQualified@ with that decision.
--
--   The walk is the one place that knows every position a name may occupy:
--   expressions, patterns, types, type arguments, effect rows and effect
--   applications.  If a new node is added to the syntax, it belongs here too;
--   the tests in @QualifiedSpec@ keep the list honest.
module Qualified (
    UseKind(..)
  , QualUse(..)
  , qualUses
  , mapQualified
  ) where

import Control.Monad (forM, when)
import Control.Monad.Writer.Strict (Writer, runWriter, tell)
import Data.Text (Text)

import Ast
import Span (Span, noSpan)
import Utils (isQualified)

-- | The namespace a use puts a name in.  It is not quite a 'DeclKind': an
--   effect operation is a value at run time but is declared inside an effect,
--   and a constructor is a function that also belongs to an enumeration.
data UseKind =
    UseValue
  | UseCtor
  | UseType
  | UseEffect
  | UseRow
  | UseOp
  deriving (Eq, Ord, Show)

-- | One qualified spelling a file writes, and where it was written.
data QualUse = QualUse {
    quName :: Text
  , quSpan :: Span
  , quKind :: UseKind
  } deriving (Eq, Show)

-- | Every qualified name in a file, in source order.
qualUses :: Chunk -> [QualUse]
qualUses chunk = snd $ mapQualified (\_ _ _ -> Nothing) chunk

-- | Walk a file, reporting every qualified name and optionally replacing it.
--
--   The callback is asked about a qualified name, its namespace and the span
--   of the node that carries it; @Just@ replaces the spelling, @Nothing@ keeps
--   it.  Unqualified names are never passed to the callback: there is nothing
--   to resolve.
--
--   An annotation has no span of its own in the syntax tree, so a type inside
--   an expression is attributed to the expression that carries it, and a type
--   in a declaration to the declaration.  The span is for a diagnostic, not
--   for semantics.
mapQualified :: (Span -> UseKind -> Text -> Maybe Text) -> Chunk -> (Chunk, [QualUse])
mapQualified f chunk = runWriter (goChunk chunk)
  where
    goName :: Span -> UseKind -> Text -> Writer [QualUse] Text
    goName sp kind n = do
      when (isQualified n) $ tell [QualUse n sp kind]
      pure $ case f sp kind n of
        Just n' -> n'
        Nothing -> n

    goChunk :: Chunk -> Writer [QualUse] Chunk
    goChunk (Module header decls) = Module header <$> mapM goDecl decls

    goDecl :: TopLevelStat -> Writer [QualUse] TopLevelStat
    goDecl = \case
      TypeDef sp n ps t -> TypeDef sp n ps <$> goTyp sp t
      EffectDef sp n ps ops -> EffectDef sp n ps <$> mapM (goEffectOp sp) ops
      RowDef sp n ps r -> RowDef sp n ps <$> goRow sp r
      EnumDef sp n ps cases -> EnumDef sp n ps <$> mapM (goEnumCase sp) cases
      FunctDef sp n tps eps args ret t body ->
        FunctDef sp n tps eps
          <$> mapM (goFunctArg sp) args
          <*> traverse (goRow sp) ret
          <*> goTyp sp t
          <*> goBlock body

    goEffectOp sp (EffectOp n funct) = EffectOp n <$> goFunct sp funct
    goEnumCase sp (EnumCase n fields) =
      EnumCase n <$> forM fields (\(q, f, t) -> do
        t' <- goTyp sp t
        pure (q, f, t'))

    goFunctArg sp = \case
      NamedFunctArg n t -> NamedFunctArg n <$> goTyp sp t
      NilArg -> pure NilArg

    goFunct sp (Funct i o r) =
      Funct <$> goTyp sp i <*> goTyp sp o <*> goRow sp r

    goTyp :: Span -> Typ -> Writer [QualUse] Typ
    goTyp sp = \case
      TFlat n -> TFlat <$> goName sp UseType n
      TNil -> pure TNil
      TArray t -> TArray <$> goTyp sp t
      TParen t -> TParen <$> goTyp sp t
      TPair l r -> TPair <$> goTyp sp l <*> goTyp sp r
      TFunct f -> TFunct <$> goFunct sp f
      TRecord r -> TRecord <$> goRecordTyp sp r
      TPending t r -> TPending <$> goTyp sp t <*> goRow sp r
      TForall tps eps t -> TForall tps eps <$> goTyp sp t
      TVar v -> pure (TVar v)
      TGenericAlias n apps -> TGenericAlias <$> goName sp UseType n <*> goApps sp apps

    goRecordTyp sp (RecordTyp props) = RecordTyp <$> mapM (goRecordTypProp sp) props
    goRecordTypProp sp (RecordTypProp q n t) = RecordTypProp q n <$> goTyp sp t

    goApps :: Span -> TypeApps -> Writer [QualUse] TypeApps
    goApps sp (TypeApps args) = TypeApps <$> mapM (goTypeArg sp) args

    goTypeArg :: Span -> TypeArg -> Writer [QualUse] TypeArg
    goTypeArg sp = \case
      TAFlat n -> TAFlat <$> goName sp UseType n
      TANil -> pure TANil
      TAArray t -> TAArray <$> goTypeArg sp t
      TAParen t -> TAParen <$> goTypeArg sp t
      TAPair l r -> TAPair <$> goTypeArg sp l <*> goTypeArg sp r
      TAFunct i o -> TAFunct <$> goTypeArg sp i <*> goTypeArg sp o
      TARecord r -> TARecord <$> goRecordTypeArg sp r
      TAMeta v -> pure (TAMeta v)
      TAGenericAlias n a -> TAGenericAlias <$> goName sp UseType n <*> goApps sp a

    goRecordTypeArg sp (RecordTypeArg props) =
      RecordTypeArg <$> mapM (goRecordTypeArgProp sp) props
    goRecordTypeArgProp sp (RecordTypeArgProp q n t) =
      RecordTypeArgProp q n <$> goTypeArg sp t

    goRow :: Span -> EffRow -> Writer [QualUse] EffRow
    goRow sp = \case
      ERVar v -> pure (ERVar v)
      ERAlias n apps -> ERAlias <$> goName sp UseRow n <*> traverse (goApps sp) apps
      ERSugar entries tailVar -> ERSugar <$> mapM (goRowEntry sp) entries <*> pure tailVar

    goRowEntry sp = \case
      EREEffCons c -> EREEffCons <$> goEffCons sp c
      EREEffRow r -> EREEffRow <$> goRow sp r

    goEffCons sp = \case
      EVar v -> pure (EVar v)
      EffCons c -> EffCons <$> goECons sp c

    goECons sp (ECons n apps) = ECons <$> goName sp UseEffect n <*> traverse (goApps sp) apps

    goEffApps :: Span -> EffApps -> Writer [QualUse] EffApps
    goEffApps sp (EffApps args rows) =
      EffApps <$> mapM (goEffArg sp) args <*> mapM (goRow sp) rows

    goEffArg sp = \case
      EACons c -> EACons <$> goEffCons sp c
      EARow r -> EARow <$> goRow sp r

    goBlock :: Block -> Writer [QualUse] Block
    goBlock (Block stats e) = Block <$> mapM goStat stats <*> goExp e

    goStat :: BlockStat -> Writer [QualUse] BlockStat
    goStat stat = (\n -> stat {bsNode = n}) <$> goStatNode (bsSpan stat) (bsNode stat)

    goStatNode sp = \case
      BExpNode e -> BExpNode <$> goExp e
      BBindDefNode (BindDef q lp e) -> BBindDefNode <$> (BindDef q <$> goParam sp lp <*> goExp e)
      BAssignNode (Assign n path e) -> BAssignNode <$> (Assign n path <$> goExp e)

    goExp :: Exp -> Writer [QualUse] Exp
    goExp e = (\n -> e {expNode = n}) <$> goExpNode (expSpan e) (expNode e)

    goExpNode :: Span -> ExpNode -> Writer [QualUse] ExpNode
    goExpNode sp = \case
      NName n -> NName <$> goName sp UseValue n
      NApply a b -> NApply <$> goExp a <*> goExp b
      NDollar a b -> NDollar <$> goExp a <*> goExp b
      NLiteral l -> NLiteral <$> goLiteral sp l
      NPair a b -> NPair <$> goExp a <*> goExp b
      NLet p w b -> NLet <$> goLetPattern sp p <*> goExp w <*> goExp b
      NBacktick op a b -> NBacktick op <$> goExp a <*> goExp b
      NPropAccess a n -> NPropAccess <$> goExp a <*> pure n
      NIfThenElse p t f -> NIfThenElse <$> goExp p <*> goExp t <*> goExp f
      NUnder u -> NUnder <$> goUnder u
      NResume a -> NResume <$> goExp a
      NParen b -> NParen <$> goBlock b
      NWith a ts es -> NWith <$> goExp a <*> goApps sp ts <*> goEffApps sp es
      NAnnot a t -> NAnnot <$> goExp a <*> goTyp sp t
      NMatch a cs -> NMatch <$> goExp a <*> mapM goClause cs

    goClause :: MatchClause -> Writer [QualUse] MatchClause
    goClause (MatchClause ps guard body) =
      MatchClause <$> mapM goPattern ps <*> traverse goExp guard <*> goBlock body

    goUnder :: Under -> Writer [QualUse] Under
    goUnder (Under eff b clauses name thenBlock) =
      Under
        <$> goECons (blockSpan b) eff
        <*> goBlock b
        <*> mapM goHandlerClause clauses
        <*> pure name
        <*> goBlock thenBlock

    goHandlerClause :: HandlerClause -> Writer [QualUse] HandlerClause
    goHandlerClause (HandlerClause op args body) =
      HandlerClause <$> goName (blockSpan body) UseOp op <*> pure args <*> goBlock body

    goPattern :: Pattern -> Writer [QualUse] Pattern
    goPattern p = (\n -> p {patNode = n}) <$> goPatternNode (patSpan p) (patNode p)

    goPatternNode :: Span -> PatternNode -> Writer [QualUse] PatternNode
    goPatternNode sp = \case
      PInt i -> pure (PInt i)
      PFloat x -> pure (PFloat x)
      PString s -> pure (PString s)
      PNil -> pure PNil
      PBoolean b -> pure (PBoolean b)
      PName n -> pure (PName n)
      PVal e path -> PVal <$> goExp e <*> pure path
      PArray ps tailP -> PArray <$> mapM goPattern ps <*> traverse goPattern tailP
      PTuple ps -> PTuple <$> mapM goPattern ps
      PCon n ps -> PCon <$> goName sp UseCtor n <*> mapM goPattern ps
      PAs p' n -> PAs <$> goPattern p' <*> pure n
      PCast p' t -> PCast <$> goPattern p' <*> goTyp sp t
      PWildcard -> pure PWildcard
      PParen p' -> PParen <$> goPattern p'
      PStarts l r -> PStarts <$> goPattern l <*> goPattern r
      PEnds l r -> PEnds <$> goPattern l <*> goPattern r

    goParam :: Span -> LambdaParam -> Writer [QualUse] LambdaParam
    goParam sp (LambdaParam n t) = LambdaParam n <$> traverse (goTyp sp) t

    goLetPattern :: Span -> LetPattern -> Writer [QualUse] LetPattern
    goLetPattern sp = \case
      LPParam p -> LPParam <$> goParam sp p
      LPATom a -> LPATom <$> goAtomLetPattern sp a

    goAtomLetPattern :: Span -> AtomLetPattern -> Writer [QualUse] AtomLetPattern
    goAtomLetPattern sp = \case
      ALPNil -> pure ALPNil
      ALPUnderscore -> pure ALPUnderscore
      ALPPair l r -> ALPPair <$> goLetPattern sp l <*> goLetPattern sp r
      ALPParen p -> ALPParen <$> goLetPattern sp p
      ALPRecord props -> ALPRecord <$> mapM (goAtomLetProp sp) props

    goAtomLetProp :: Span -> AtomLetPatternRecordProp -> Writer [QualUse] AtomLetPatternRecordProp
    goAtomLetProp sp (AtomLetPatternRecordProp q p nested) =
      AtomLetPatternRecordProp q <$> goParam sp p <*> traverse (goAtomLetPattern sp) nested

    goLiteral :: Span -> Literal -> Writer [QualUse] Literal
    goLiteral sp = \case
      LAtom a -> pure (LAtom a)
      LArray (ArrayLiteral entries) -> LArray . ArrayLiteral <$> mapM goEntry entries
      LLambda l -> LLambda <$> goLambda l
      LRecord (RecordLiteral base binds) ->
        LRecord <$> (RecordLiteral <$> traverse goExp base <*> mapM (goBind sp) binds)

    goEntry :: ArrayEntry -> Writer [QualUse] ArrayEntry
    goEntry = \case
      AEExp e -> AEExp <$> goExp e
      AEBlock b -> AEBlock <$> goBlock b

    goBind :: Span -> BindDef -> Writer [QualUse] BindDef
    goBind sp (BindDef q p e) = BindDef q <$> goParam sp p <*> goExp e

    goLambda :: LambdaLiteral -> Writer [QualUse] LambdaLiteral
    goLambda (LambdaLiteral tps eps head' body) =
      LambdaLiteral tps eps <$> traverse goHead head' <*> goBlock body

    goHead :: LambdaHead -> Writer [QualUse] LambdaHead
    goHead (LambdaHead params ret) =
      LambdaHead <$> mapM (goParam noSpan) params <*> traverse (goTyp noSpan) ret

-- | The span of a block's first statement or its final expression.  Used where
--   the syntax keeps no position of its own: an effect constructor in @under@,
--   and a handler's operation name.
blockSpan :: Block -> Span
blockSpan (Block [] e) = expSpan e
blockSpan (Block (st : _) _) = bsSpan st
