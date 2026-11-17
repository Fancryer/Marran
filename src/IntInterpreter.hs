{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}

module IntInterpreter (interpret, interpretProgram, prepareSnapshotBenchmark, InterpError(..), errorCodeOf, heapError) where

import qualified TypedIR as IR
import Types (
    Mutability(..),
    ECons(..),
    EffCons(..),
    LetPattern(..),
    AtomLetPattern(..),
    LetPatternRecordProp(..),
    LambdaParam(..), EffRow (..),
    enumCases, enumCaseName, enumCaseFields
  )
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Scientific (Scientific, fromFloatDigits, normalize, scientific)
import Control.Monad.Cont (ContT(..), callCC)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Span (Span, noSpan)
import Module (Module(..), ModuleHeader(..), Imported(..), ImportOrigin(..), Unit(..), Program(..), moduleAt)
import Utils (TextMap, Pretty (..))
import Data.Foldable (find)
import Data.List (intercalate, nub)
import TypedIR (
    TypedExpr(..),
    pattern TEInt, pattern TEFloat, pattern TEBoolean, pattern TEString,
    pattern TENil, pattern TEXVar, pattern TEArray, pattern TEPair,
    pattern TEXLambda, pattern TENLambda, pattern TEApply, pattern TERecord,
    pattern TEHandle, pattern TEParen, pattern TEResume, pattern TELet,
    pattern TEPropAccess, pattern TEIfElse,
    pattern TEAnnot,
    pattern TEMatch,
    TPattern(..), TPatternNode(..), TMatchClause(..),
    Lambda(..), Block, TERecordProp(..))
import Control.Monad.State.Strict
import Control.Monad (foldM, forM, forM_, void, unless, when, zipWithM)
import Infer (freezeMutability, freeze, freezeBlock, freezeLambda, touches)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Eff
import qualified Parser
import System.Random (randomIO, randomRIO)
import Data.Char (chr)
import System.CPUTime (getCPUTime)
import Control.Concurrent (threadDelay)
import Resume (ResumeInfo(..))
import Text.Printf (printf)
import Data.Maybe (isJust, listToMaybe)
import System.Environment (lookupEnv)
import Control.Exception (AsyncException (..), IOException, evaluate, fromException, throwIO, try)
import System.IO.Error (isEOFError)
import System.Environment (lookupEnv, setEnv)
import System.Exit (ExitCode (..), exitWith)
import qualified System.Directory as Dir
import qualified System.Process as Proc
import System.Info (os)
import qualified Data.Text.IO as TIO

import Data.IORef
import qualified Builtins
import qualified Data.IntMap.Strict as IM
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap as IntMap

-- Address to Int
addrToInt :: Address -> Int
addrToInt = addrId

class Stringify a where
  stringify :: a -> Interp Text
  default stringify :: (Pretty a) => a -> Interp Text
  stringify = pure . pretty

-- | Значения во время выполнения
data Value
  = VInt Integer
  | VFloat Scientific
  | VBoolean Bool
  | VString Text
  | VNil
  | VArray [Address]
  | VPair Address Address
  | VRecord EnvId
  -- | A value of a declared enumeration: the constructor it was built with
  --   and its fields.  The mutability of a field is part of the value, because
  --   a constructor with a `var` field creates a cell and reading it costs
  --   `Read`, exactly as a `var` field of a record does.
  | VEnum Text [(Mutability, Address)]
  | VClosure EnvId (Maybe (IntMap Address)) (Maybe Code) (Address -> Interp Address)
  | VThunk TypedExpr EnvId
  | VBThunk Block EnvId
  | VBottom
  -- deriving Show

instance Show Value where
  show = \case
    VInt i -> concat ["(VInt ", show i, ")"]
    VFloat f -> concat ["(VFloat ", show f, ")"]
    VBoolean b -> concat ["(VBoolean ", show b, ")"]
    VString s -> concat ["(VString '", show s, "')"]
    VNil -> "VNil"
    VArray as -> concat ["(VArray [", unwords $ map show as, "])"]
    VPair l r -> concat ["(VPair ", show l, " ", show r, ")"]
    VRecord fields -> "!record" <> show fields <> "!"
    VEnum n fs -> concat ["(VEnum ", T.unpack n, " [", unwords $ map (show . snd) fs, "])"]
    VClosure _ _ code _ -> T.unpack (codeName code)
    VThunk te _ -> "!vthunk" <> show te <> "!"
    VBThunk b _ -> "!bthunk" <> show b <> "!"
    VBottom -> "!bottom!"

instance Pretty Value where
  pretty = \case
    VInt i -> T.pack $ show i
    VFloat f -> T.pack $ show f
    VBoolean True -> "true"
    VBoolean False -> "false"
    VString s -> s
    VNil -> "()"
    VPair l r -> T.concat ["(", pretty l, ", ", pretty r, ")"]
    VArray vals -> "[" <> T.intercalate ", " (map pretty vals) <> "]"
    VRecord eid -> "!record[" <> pretty eid <> "]!"
    VEnum n fs -> T.intercalate " " (n : map (pretty . snd) fs)
    VClosure _ _ code _ -> codeName code
    VThunk e _env -> T.concat ["!vthunk: ", pretty e,"!"]
    VBThunk b _env -> T.concat ["!vthunk: ", pretty b,"!"]
    VBottom -> "⊥"

instance Stringify Value where
  stringify = \case
    VInt i -> pure $ pretty i
    VFloat f -> pure $ pretty f
    VBoolean True -> pure "true"
    VBoolean False -> pure "false"
    VString s -> pure s
    VNil -> pure "()"
    VPair l r -> do
      l' <- stringify l
      r' <- stringify r
      pure $ T.concat ["(", l', ", ", r', ")"]
    VArray vals -> do
      vals' <- mapM stringify vals
      pure $ "[" <> T.intercalate ", " vals' <> "]"
    VRecord eid -> do
      env <- getEnv eid
      bindings' <- go env []
      pure $ "#{" <> T.intercalate "; " bindings' <> "}"
      where
        go :: Env -> [Text] -> Interp [Text]
        go env' acc = do
          bindings' <- forM (Map.toList env'.bindings)
            (\(n, (m, a)) -> do
              a' <- stringify a
              pure $ T.unwords [pretty m, n, "=", a'])
          case env'.parent of
            Nothing -> pure $ acc <> bindings'
            Just p -> do
              e <- getEnv p
              go e bindings'
    -- An enum prints as its constructor applied to its fields, without the
    -- `#` the pattern writes: `Some 5`, `None`.
    VEnum n fs -> do
      fields <- mapM (stringify . snd) fs
      pure $ T.intercalate " " (n : fields)
    VClosure _ _ code _ -> pure $ codeName code
    VThunk e _env -> pure $ T.concat ["!vthunk: ", pretty e,"!"]
    VBThunk b _env -> pure $ T.concat ["!bthunk: ", pretty b,"!"]
    VBottom -> pure "⊥"

-- | A cell of the store.
--
--   The value lives in an 'IORef', so the store is the Haskell heap: GHC traces
--   it precisely, collects cycles and keeps anything a captured continuation
--   still points at.  A hand-written mark-and-sweep could not do that here —
--   the interpreter is CPS over @callCC@, so addresses live in Haskell stack
--   frames and would be freed under the running code.
data Address = Address {
    addrId   :: !Int
  , addrCell :: IORef Value
  }
instance Eq Address where a == b = addrId a == addrId b
instance Ord Address where compare a b = compare (addrId a) (addrId b)
instance Show Address where show a = "Address " <> show (addrId a)
instance Pretty Address where pretty a = T.pack $ printf "#%08x" (addrId a)

instance Stringify Address where
  stringify a = readCell a >>= stringify

-- | An environment: a scope of bindings plus the scope it extends.
--
--   'bindings' is an 'IORef' because a rebind writes into the scope where the
--   name was declared; the scope keeps its identity, so every closure that
--   captured it sees the new binding, exactly as the model's @S-Rebind@ does.
data EnvId = EnvId {
    envId   :: !Int
  , envCell :: IORef Env
  }
instance Eq EnvId where a == b = envId a == envId b
instance Ord EnvId where compare a b = compare (envId a) (envId b)
instance Show EnvId where show e = "EnvId " <> show (envId e)
instance Pretty EnvId where pretty e = T.pack $ printf "&%08x" (envId e)

data Env = Env {
  bindings :: TextMap (Mutability, Address),
  parent   :: Maybe EnvId
}

-- TODO: instance Stringify Env (using #{parent | bindings})

getEnv :: EnvId -> Interp Env
getEnv = liftIO . readIORef . envCell

updateEnv :: EnvId -> Env -> Interp EnvId
updateEnv eid env = do
  liftIO $ writeIORef (envCell eid) env
  pure eid

newEnv :: Env -> Interp EnvId
newEnv env = do
  n <- gets sNextEnv
  modify $ \s -> s {sNextEnv = n + 1}
  ref <- liftIO $ newIORef env
  pure EnvId {envId = n, envCell = ref}

getCurrentEnv :: Interp Env
getCurrentEnv = getEnv =<< gets sEnv

modifyCurrentEnv :: (Env -> Env) -> Interp EnvId
modifyCurrentEnv f = flip modifyEnv f =<< gets sEnv

modifyEnv :: EnvId -> (Env -> Env) -> Interp EnvId
modifyEnv eid f = updateEnv eid . f =<< getEnv eid

findBindingEnv :: EnvId -> Text -> Interp (EnvId, Mutability, Address)
findBindingEnv eid name = do
  found <- findBindingEnvMaybe eid name
  case found of
    Just frame -> pure frame
    Nothing -> do
      op <- findStackOperation name
      case op of
        Nothing -> rtError $ "`" <> name <> "` is not in scope"
        Just (eff, arity) -> do
          env <- gets sEnv
          clos <- makeEffectClosure env arity eff name
          a <- alloc (VClosure env Nothing (Just (CodeNative Whole name)) clos)
          pure (env, Val, a)

findBindingEnvMaybe :: EnvId -> Text -> Interp (Maybe (EnvId, Mutability, Address))
findBindingEnvMaybe eid name = go Set.empty eid
  where
    go visited eid' = do
      when (Set.member eid' visited) $
        rtError $ "internal error: the environment chain of " <> pretty eid' <> " is cyclic"
      env <- getEnv eid'
      case Map.lookup name env.bindings of
        Just (m,a) -> pure $ Just (eid', m, a)
        Nothing -> case env.parent of
          Just p -> go (Set.insert eid' visited) p
          Nothing -> pure Nothing

-- | An operation of an effect whose handler is currently installed.
--
--   Operations are not always lexically visible where they are used: a thunk
--   created outside a handler and forced inside it — @loop {break 1}@ — closes
--   over the caller's environment, which has no binding for @break@.  The type
--   checker admits the call because the effect is named in the expected type,
--   so the interpreter resolves the name through the handler stack, innermost
--   handler first, exactly as 'callEffect' selects the clause to run.
findStackOperation :: Text -> Interp (Maybe (ECons, Int))
findStackOperation name = do
  stack <- gets sKstack
  let matches =
        [ (h.hEffect, arity)
        | h <- stack
        , Just arity <- [Map.lookup name h.hArities]
        ]
  case matches of
    [] -> pure Nothing
    ((eff, arity) : _)
      -- The name alone does not say which effect an unbound operation belongs
      -- to.  If two handlers on the stack provide it, choosing the innermost
      -- one would silently run the wrong operation; report the ambiguity.
      | all ((== effectName eff) . effectName . fst) matches ->
          pure $ Just (eff, arity)
      | otherwise ->
          rtError $ T.concat [
              "the operation `", name, "` is provided by more than one effect on the handler stack (",
              T.intercalate ", " [ "`" <> effectName e <> "`" | e <- nub (map fst matches) ],
              "), so it cannot be resolved by name"
            ]

getCell :: Env -> Text -> Maybe (Mutability, Address)
getCell e x = Map.lookup x e.bindings

getRef :: Env -> Text -> Maybe Address
getRef e x = snd <$> getCell e x

getMut :: Env -> Text -> Maybe Mutability
getMut e x = fst <$> getCell e x

-- | Read a cell.  Reading a cell always succeeds: a cell exists exactly while
--   something can reach it, which is what moving the store to the Haskell heap
--   buys us.
readCell :: Address -> Interp Value
readCell = liftIO . readIORef . addrCell

-- | Overwrite a cell.  Used by the evaluator when a thunk becomes its value
--   (the heap is write-once except for that) and by the copy that a snapshot
--   writes into a fresh cell.
writeCell :: Address -> Value -> Interp ()
writeCell a v = liftIO $ writeIORef (addrCell a) v

-- | A fresh cell holding @v@.
freshCell :: Value -> Interp Address
freshCell v = do
  n <- gets sNextAddr
  modify $ \s -> s {sNextAddr = n + 1}
  ref <- liftIO $ newIORef v
  pure Address {addrId = n, addrCell = ref}

unpackRef :: Env -> Text -> Maybe Address
unpackRef e x = getRef e x

-- | Код замыкания (нужен, чтобы снимок мог переписать функцию, а не только её данные)
--
--   The name is what printing has to say about a function, and it is the only
--   thing a reader can check: an address or a heap id says nothing, and two
--   different functions would print alike.  A lambda has no name, so it says
--   that it is one; @CodeNative@ is the name the library binds a value to, so
--   a builtin prints as what the program calls it.
--
--   'Partial' marks a stage of a curried application.  The name still says
--   which function it came from, which is what a reader wants, and the word
--   says that the value is not that function — it is missing arguments.
data Stage = Whole | Partial

data Code
  = CodeLam IR.Lambda
  | CodeFun Stage Text [Text] IR.Block
  | CodeNative Stage Text

-- | How a function prints.  A value with no recorded code (a continuation, an
--   effect operation built on the fly) says only that it is a function, which
--   is true and says nothing it cannot support.
codeName :: Maybe Code -> Text
codeName = \case
  Just (CodeFun Whole n _ _) -> n
  Just (CodeFun Partial n _ _) -> partialName n
  Just (CodeLam _) -> "<lambda>"
  Just (CodeNative Whole n) -> n
  Just (CodeNative Partial n) -> partialName n
  Nothing -> "<function>"

partialName :: Text -> Text
partialName n = T.concat ["<partial: ", n, ">"]

-- | События мутации (теорема об эффектах): чтение var, перепривязка, создание var, чтение снимком
data Event = EvRead | EvRebind | EvCreate | EvSnapRead
  deriving (Eq, Ord, Show)

data InterpState = InterpState
  { sEnv        :: EnvId
  , sKstack     :: [HandlerFrame]
  , sNextAddr   :: Int
  , sNextEnv    :: Int
  , sNextCont   :: Int                   -- ^ identifies a handler continuation
  , sUsedConts  :: Set Int               -- ^ continuations already resumed
  , sContAddrs  :: Set Int               -- ^ heap addresses holding a continuation
  , sNextHandler :: Int                  -- ^ identifies an installed handler
  , sFreezeMemo :: IntMap Address        -- было Map Address Address
  , sTrace      :: Bool
  , sEvents     :: Map Event Int
  , sNoMemo     :: Bool
  , sForcing    :: Set Int               -- ^ cells whose value is being computed
  , sSpan       :: Span                  -- ^ where the interpreter currently is
  , sCmdArgs    :: [String]              -- ^ the command line, read by `System@args`
  }

type Clause = [Address] -> (Address -> Interp Address) -> Interp Address

data HandlerFrame = HandlerFrame {
  -- | Distinguishes nested handlers of the same effect, so that a captured
  --   continuation can be checked against the handler that created it.
  hId         :: Int,
  hEffect     :: ECons,
  hClauses    :: Map Text Clause,
  -- | Arity of each clause, so that a name reached through the stack can be
  --   turned into the same curried operation closure a lexical binding holds.
  hArities    :: Map Text Int,
  hThen       :: Address -> Interp Address
}

-- | A failure of the interpreter itself: a value of the wrong shape reached a
--   primitive, an address was read after it was freed, a handler went missing.
--
--   These are never consequences of a well-typed program, so reaching one is a
--   bug — but a bug should be a message with a position, not an exception that
--   unwinds through the user's screen.
data InterpError = InterpError {
    ieMessage :: Text
  , ieSpan    :: Span
  , ieCode    :: Maybe Text
  } deriving (Eq)

instance Pretty InterpError where
  pretty = ieMessage

-- | 'show' is used by the few places that print a value of this type; make it
--   print the message rather than a constructor application.
instance Show InterpError where
  show = T.unpack . ieMessage

-- | Raise a runtime error at the node currently being evaluated.
rtError :: Text -> Interp a
rtError msg = do
  sp <- gets sSpan
  raise sp msg

-- | Raise a runtime error at a known node.
rtErrorAt :: Span -> Text -> Interp a
rtErrorAt = raise

raise :: Span -> Text -> Interp a
raise sp msg = lift $ throwError (InterpError msg sp Nothing)

-- | A mistake the program itself reports through the effect @Error@ (a
--   division by zero, an unhandled @error@).  It carries a code of its own: it
--   is not an interpreter bug, so it must not read like one.
programError :: Text -> Interp a
programError msg = do
  sp <- gets sSpan
  lift $ throwError (InterpError msg sp (Just "E0020"))

-- | The diagnostic code a runtime error is reported under.  A program that is
--   well typed only reaches one of these by running out of memory; the rest are
--   interpreter bugs, which are still worth a stable identifier in a report.
errorCodeOf :: InterpError -> Maybe Text
errorCodeOf = ieCode

-- | Mонада интерпретации: CPS с IO, ошибки — отдельный канал.
--
--   'ExceptT' sits under 'ContT' so that an error aborts the whole evaluation,
--   including continuations captured by 'callCC': a runtime error is not
--   something a handler clause may resume from.
type Interp a = ContT Value (ExceptT InterpError (StateT InterpState IO)) a

-- | Run an interpretation, keeping the final state.
runInterp :: Interp Value -> InterpState -> IO (Either InterpError Value, InterpState)
runInterp action = runStateT (runExceptT (runContT action pure))

-- | Запуск интерпретации
--
--   Running out of memory is a property of the program being run, not a bug of
--   the interpreter, so it is reported as a diagnostic: with the source
--   position of @main@ and a code, like every other failure.  Without the catch
--   the RTS prints a message with no position and exits.
interpret :: IR.Chunk -> [String] -> IO (Either InterpError Value)
interpret chunk cmdArgs = do
  rootRef <- newIORef (Env Map.empty Nothing)
  let root = EnvId {envId = 0, envCell = rootRef}
      state = (initialInterpState root) {sCmdArgs = cmdArgs}
  result <- try $ fst <$> runInterp (do
    modify $ \st -> st {sEnv = root}
    _ <- buildInitialEnv cmdArgs
    evalChunk chunk
    ) state

  case result of
    Right ok -> pure ok
    Left e -> case fromException e of
      Just async | async == HeapOverflow || async == StackOverflow ->
        pure (Left (heapError (mainSpan chunk) async))
      _ -> throwIO e

-- | Run a whole program.
--
--   Every module gets an environment of its own, whose parent is the root (the
--   native values).  A module's own declarations are bound there first, so a
--   recursive function closes over an environment that will hold its own name;
--   then the names the module imported are copied in under the spelling this
--   file writes.  Copying the address rather than the value keeps one instance
--   of each function per program, and two private @helper@s of two modules are
--   simply two addresses in two environments.
--
--   Only the entry module's @main@ is called: a library is a program too, and
--   running it would mean running the first module of the import graph, which
--   is not what a reader asked for.
interpretProgram :: Program IR.TopLevelStat -> [String] -> IO (Either InterpError Value)
interpretProgram prog cmdArgs = do
  rootRef <- newIORef (Env Map.empty Nothing)
  let root = EnvId {envId = 0, envCell = rootRef}
      state = (initialInterpState root) {sCmdArgs = cmdArgs}
  result <- try $ fst <$> runInterp (do
    modify $ \st -> st {sEnv = root}
    _ <- buildInitialEnv cmdArgs
    envs <- evalProgram prog root
    case Map.lookup (progEntry prog) envs of
      Nothing -> rtError $ T.concat [
          "internal error: the entry module `", T.pack (progEntry prog),
          "` is not part of the program"
        ]
      Just eid -> do
        modify $ \st -> st {sEnv = eid}
        runEntry (findMainOf prog) eid
    ) state

  case result of
    Right ok -> pure ok
    Left e -> case fromException e of
      Just async | async == HeapOverflow || async == StackOverflow ->
        pure (Left (heapError (programMainSpan prog) async))
      _ -> throwIO e

-- | The body of @main@ in the entry module, as the position of a failure that
--   is not tied to a particular node.
programMainSpan :: Program IR.TopLevelStat -> Span
programMainSpan prog = case findMainOf prog of
  Just fd -> IR.blockSpan (IR.fBlock fd)
  Nothing -> noSpan

findMainOf :: Program IR.TopLevelStat -> Maybe IR.FunctDecl
findMainOf prog = listToMaybe
  [ fd
  | u <- progUnits prog
  , (p, Module _ decls) <- unitModules u
  , p == progEntry prog
  , IR.SFunctDef fd <- decls
  , IR.fName fd == "main"
  ]

-- | Give every module of the program an environment, in dependency order.
evalProgram :: Program IR.TopLevelStat -> EnvId -> Interp (Map FilePath EnvId)
evalProgram prog root = do
  envs <- foldM unitStep Map.empty (progUnits prog)
  pure envs
  where
    unitStep envs (Unit _ mods) = do
      -- Every member of a unit gets its environment before any of them is
      -- filled: a cycle has no first module, and a closure only needs the
      -- environment to exist.
      fresh <- forM mods $ \(p, m) -> do
        eid <- newEnv Env {bindings = Map.empty, parent = Just root}
        pure (p, eid, m)
      -- Own declarations first: a function's body may call any function of its
      -- own module, including itself.
      forM_ fresh $ \(_, eid, m) -> evalModule eid (modDecls m)
      -- Then the imported names, copied from the module that declares them.
      -- The members of this unit are already in the map: a cycle imports from
      -- itself just like any other module, and the other member's environment
      -- exists by now even though the unit as a whole is not finished.
      let here = Map.fromList [ (p, eid) | (p, eid, _) <- fresh ]
          known = Map.union here envs
      forM_ fresh $ \(_, eid, m) -> linkImports known eid m
      pure $ Map.union here envs

    linkImports envs eid m =
      forM_ (Map.toList (mhResolved (modHeader m))) $ \(local, imp) -> case imOrigin imp of
        -- A native name is already bound in the root environment, which is
        -- this module's parent; only a renamed one needs a local binding.
        FromNative _
          | local == imName imp -> pure ()
          | otherwise -> copyFrom eid root local (imName imp)
        FromModule path -> case Map.lookup path envs of
          Nothing -> pure ()
          Just src -> copyFrom eid src local (imName imp)

    copyFrom eid src local declared =
      findBindingEnvMaybe src declared >>= \case
        Just (_, mut, addr) -> do
          _ <- modifyEnv eid $ \env ->
            env {bindings = Map.insert local (mut, addr) env.bindings}
          pure ()
        Nothing -> pure ()

-- | Bind one module's own declarations into an environment.
evalModule :: EnvId -> [IR.TopLevelStat] -> Interp ()
evalModule env0 chunk = do
  let functDefs = [fd | IR.SFunctDef fd <- chunk, IR.fName fd /= "main"]
  forM_ functDefs $ \fd -> do
    let cache = case fst (IR.fRet fd) of
          Just fxs -> if isPureClosure fxs then Just IM.empty else Nothing
          _ -> Just IM.empty
    fn <- makeTopLevelClosure env0 fd
    void $ bindValIn env0 (IR.fName fd) $ VClosure env0 cache
          (Just (CodeFun Whole (IR.fName fd) (map fst $ IR.fArgs fd) (IR.fBlock fd))) fn

  -- The constructors of a declared enumeration are ordinary functions of the
  -- module's scope, so a value is built by applying one: `Some 5`.
  let enumDefs = [ed | IR.SEnumDef ed <- chunk]
  forM_ enumDefs $ \def ->
    forM_ (enumCases def) $ \c -> do
      let muts = [m | (m, _, _) <- enumCaseFields c]
      ctor <- makeConstructor env0 (enumCaseName c) muts
      void $ bindValAddrIn env0 (enumCaseName c) ctor

-- | An out-of-memory condition as a diagnostic.  Kept separate from 'interpret'
--   so that the mapping can be tested without actually exhausting memory.
heapError :: Span -> AsyncException -> InterpError
heapError sp HeapOverflow = InterpError (outOfMemory "heap") sp (Just "E0019")
heapError sp StackOverflow = InterpError (outOfMemory "stack") sp (Just "E0019")
heapError sp _ = InterpError outOfMemoryNoRts sp (Just "E0019")

-- | The message of an out-of-memory diagnostic.  It names the resource, because
--   the two are exhausted for different reasons and a reader needs to know
--   which one to look at.
outOfMemory :: Text -> Text
outOfMemory resource = T.concat [
    "the program ran out of memory: the ", resource, " was exhausted. ",
    "A long recursion keeps a frame per call, because the interpreter delays ",
    "the rest of a block instead of returning from it, and a chain of delayed ",
    "computations is live data as well."
  ]

outOfMemoryNoRts :: Text
outOfMemoryNoRts = "the program ran out of memory"

-- | Call the entry module's @main@.
runEntry :: Maybe IR.FunctDecl -> EnvId -> Interp Value
runEntry mainDecl eid = case mainDecl of
  Nothing -> liftIO (putStrLn "Warning: No 'main' function found") >> pure VNil
  Just fd -> do
    -- `main` is `() -> ...`: the entry point is called with the unit value.
    unit <- alloc VNil
    fn <- makeTopLevelClosure eid fd
    resultAddr <- fn unit
    result <- whnfAddr resultAddr
    reportEvents (fst $ IR.fRet fd)
    readCell result
mainSpan :: IR.Chunk -> Span
mainSpan chunk = case findMain chunk of
  Just (IR.SFunctDef fd) -> IR.blockSpan fd.fBlock
  _ -> noSpan

-- | Операция эффекта: арность и клауза объявляются вместе (единственный источник арности)
data Op = Op {
  opArity  :: Int,
  opClause :: Clause
}

-- | Встроенные эффекты и их операции
globalOps :: [(ECons, [(Text, Op)])]
globalOps = [
    (Eff.elabel "Output", [
      ("say", Op 1 $ \case
        [addrArg] -> \_ -> do
          liftIO . putStr . T.unpack =<< stringify =<< forceValue addrArg
          alloc VNil
        args -> \_ -> arityError "say" 1 args),
      ("sayn", Op 1 $ \case
        [addrArg] -> \_ -> do
          liftIO . putStrLn . T.unpack =<< stringify =<< forceValue addrArg
          alloc VNil
        args -> \_ -> arityError "sayn" 1 args),
      ("trace", Op 2 $ \case
        [labelArg, valArg] -> \_ -> do
          -- `trace` reads `String -> `A -> {Output} `A`: the label
          -- says where the value came from, and the value is shown, not its
          -- thunk.  The cell is forced in place and the argument address is
          -- returned, so the result is the value the label described.
          label <- forceValue labelArg >>= \case
            VString s -> pure s
            other -> stringify other
          v <- forceValue valArg
          shown <- stringify v
          liftIO $ putStrLn $ T.unpack $ T.concat [label, ": ", shown]
          pure valArg
        args -> \_ -> arityError "trace" 2 args)
    ]),
    -- `error` has a clause at the bottom of the stack, so `1 / 0` is a
    -- diagnostic even when the program installs no handler of its own; a
    -- program that writes `under Error to ... handle | error e => ...` replaces
    -- it for the extent of the body.
    (Eff.elabel "Error", [
      ("error", Op 1 $ \case
        [addrArg] -> \_ -> do
          v <- readCell addrArg
          msg <- case v of
            VString s -> pure s
            other -> stringify other
          programError msg
        args -> \_ -> arityError "error" 1 args)
    ]),
    (Eff.elabel "Input", [
      ("read_string", Op 1 $ \_ _ -> do
        -- A line of input is text, not source: the whole line is the string,
        -- quotes and all.  Parsing it as a Mårran literal made `hello` an
        -- error and `'hello'` correct, which is the wrong way round for a
        -- program that asks a person for an answer.
        input <- readInputLine "read_string"
        alloc $ VString input),
      ("read_int", Op 1 $ \_ _ -> do
        input <- readInputLine "read_int"
        case Parser.parseFromText Parser.intLiteral input of
          Left _ -> rtError $ "`read_int` could not parse the line " <> quoted input
          Right i -> alloc $ VInt i),
      ("read_float", Op 1 $ \_ _ -> do
        input <- readInputLine "read_float"
        case Parser.parseFromText Parser.floatLiteral input of
          Left _ -> rtError $ "`read_float` could not parse the line " <> quoted input
          Right f -> alloc $ VFloat f),
      ("read_boolean", Op 1 $ \_ _ -> do
        input <- readInputLine "read_boolean"
        case Parser.parseFromText Parser.bool input of
          Left _ -> rtError $ "`read_boolean` could not parse the line " <> quoted input
          Right b -> alloc $ VBoolean b)
    ]),
    (Eff.elabel "Random", [
      ("random_int", Op 2 $ \case
        [minI, maxI] -> \_ -> do
          lo <- forceValue minI
          hi <- forceValue maxI
          case (lo, hi) of
            (VInt a, VInt b) -> do
              r <- liftIO $ toInteger <$> (randomRIO (fromIntegral a, fromIntegral b) :: IO Int)
              alloc $ VInt r
            _ -> rtError "`random_int` needs an Int as both its lower and upper bound"
        args -> \_ -> arityError "random_int" 2 args),
      ("random_float", Op 1 $ \_ _ -> do
        r <- liftIO $ fromFloatDigits <$> (randomRIO (0.0, 1.0) :: IO Double)
        alloc $ VFloat r),
      ("random_boolean", Op 1 $ \_ _ -> alloc . VBoolean =<< randomIO),
      ("random_string", Op 1 $ \case
        [addr] -> \_ -> do
          v <- readCell addr
          case v of
            VInt n | n <= 0 -> alloc $ VString ""
            VInt n -> do
              chars <- mapM (const $ chr <$> randomRIO (32, 126)) [1 :: Integer .. fromInteger n]
              alloc $ VString (T.pack chars)
            _ -> rtError "`random_string` needs an Int as its length"
        args -> \_ -> arityError "random_string" 1 args)
    ]),
    (Eff.elabel "Time", [
      ("time_ms", Op 1 $ \_ _ -> do
        cpuTime <- liftIO getCPUTime
        alloc $ VInt $ fromInteger $ cpuTime `div` 1_000_000_000),
      ("sleep", Op 1 $ \case
        [addr] -> \_ -> do
          v <- readCell addr
          case v of
            VInt i -> liftIO (threadDelay $ fromInteger i) >> alloc VNil
            _ -> rtError "`sleep` needs an Int as its duration in microseconds"
        args -> \_ -> arityError "sleep" 1 args)
    ]),
    -- `Env`: the process environment.
    (Eff.elabel "Env", [
      ("get_env", Op 1 $ \case
        [addr] -> \_ -> do
          v <- forceValue addr
          case v of
            VString name -> do
              -- A missing variable reads as the empty string: the row has no
              -- `Error`, so the program has to decide what a missing name
              -- means, and `slen (get_env name)` is a natural test.
              found <- liftIO $ lookupEnv (T.unpack name)
              alloc $ VString (maybe "" T.pack found)
            other -> rtError $ "`get_env` expected a String, but got " <> describe other
        args -> \_ -> arityError "get_env" 1 args),
      ("set_env", Op 2 $ \case
        [nameAddr, valueAddr] -> \_ -> do
          nameV <- forceValue nameAddr
          valueV <- forceValue valueAddr
          case (nameV, valueV) of
            (VString name, VString value) -> do
              liftIO $ setEnv (T.unpack name) (T.unpack value)
              alloc VNil
            _ -> rtError "`set_env` needs a String as both the name and the value"
        args -> \_ -> arityError "set_env" 2 args)
    ]),
    -- `File`.  Every operation that can fail reports the
    -- failure through `Error`, the same way `/` reports a zero divisor, so a
    -- program can catch it with `try` or `under Error`.
    (Eff.elabel "File", [
      ("read_file", Op 1 $ \case
        [addr] -> \_ -> do
          v <- forceValue addr
          case v of
            VString path -> do
              r <- liftIO $ try (TIO.readFile (T.unpack path)) :: Interp (Either IOException Text)
              case r of
                Left e -> fileError "read_file" path e
                Right contents -> alloc $ VString contents
            other -> rtError $ "`read_file` expected a String, but got " <> describe other
        args -> \_ -> arityError "read_file" 1 args),
      ("write_file", Op 2 $ \case
        [pathAddr, textAddr] -> \_ -> withFilePathAndText "write_file" pathAddr textAddr $ \path text -> do
          r <- liftIO $ try (TIO.writeFile (T.unpack path) text) :: Interp (Either IOException ())
          either (fileError "write_file" path) (const $ alloc VNil) r
        args -> \_ -> arityError "write_file" 2 args),
      ("append_file", Op 2 $ \case
        [pathAddr, textAddr] -> \_ -> withFilePathAndText "append_file" pathAddr textAddr $ \path text -> do
          r <- liftIO $ try (TIO.appendFile (T.unpack path) text) :: Interp (Either IOException ())
          either (fileError "append_file" path) (const $ alloc VNil) r
        args -> \_ -> arityError "append_file" 2 args),
      ("file_exists", Op 1 $ \case
        [addr] -> \_ -> do
          v <- forceValue addr
          case v of
            VString path -> do
              -- The row has no `Error`, so a path the system rejects is simply
              -- not there, not a failure of the operation.
              there <- liftIO $ Dir.doesPathExist (T.unpack path)
              alloc $ VBoolean there
            other -> rtError $ "`file_exists` expected a String, but got " <> describe other
        args -> \_ -> arityError "file_exists" 1 args),
      ("delete_file", Op 1 $ \case
        [addr] -> \_ -> do
          v <- forceValue addr
          case v of
            VString path -> do
              r <- liftIO $ try (Dir.removeFile (T.unpack path)) :: Interp (Either IOException ())
              either (fileError "delete_file" path) (const $ alloc VNil) r
            other -> rtError $ "`delete_file` expected a String, but got " <> describe other
        args -> \_ -> arityError "delete_file" 1 args),
      ("list_directory", Op 1 $ \case
        [addr] -> \_ -> do
          v <- forceValue addr
          case v of
            VString path -> do
              r <- liftIO $ try (Dir.listDirectory (T.unpack path)) :: Interp (Either IOException [FilePath])
              case r of
                Left e -> fileError "list_directory" path e
                Right entries -> do
                  addrs <- mapM (alloc . VString . T.pack) entries
                  alloc $ VArray addrs
            other -> rtError $ "`list_directory` expected a String, but got " <> describe other
        args -> \_ -> arityError "list_directory" 1 args)
    ]),
    -- `System`.
    (Eff.elabel "System", [
      -- The command line is read when the program asks for it: an `args ()`
      -- in a library is not a reason to give every program a `System` row.
      ("args", Op 1 $ \_ _ -> do
        cmdArgs' <- gets sCmdArgs
        addrs <- mapM (alloc . VString . T.pack) cmdArgs'
        alloc $ VArray addrs),
      ("hostname", Op 1 $ \_ _ -> do
        -- There is no portable hostname in `base`; the environment variable the
        -- platform sets is the closest thing without a second dependency.
        name <- liftIO $ firstJustM [lookupEnv "COMPUTERNAME", lookupEnv "HOSTNAME"]
        alloc $ VString $ maybe (T.pack os) T.pack name),
      ("system", Op 1 $ \case
        [addr] -> \_ -> do
          v <- forceValue addr
          case v of
            VString command -> do
              (code, _, _) <- liftIO $ Proc.readCreateProcessWithExitCode
                (Proc.shell (T.unpack command)) ""
              alloc $ VInt $ case code of
                ExitSuccess -> 0
                ExitFailure n -> fromIntegral n
            other -> rtError $ "`system` expected a String, but got " <> describe other
        args -> \_ -> arityError "system" 1 args),
      -- `exit` never returns.  It is not a diagnostic: the program asked to
      -- stop, so the process ends with the code it gave, exactly as a shell
      -- command would.
      ("exit", Op 1 $ \case
        [addr] -> \_ -> do
          v <- forceValue addr
          case v of
            VInt n -> liftIO $ exitWith $ if n == 0
              then ExitSuccess
              else ExitFailure (fromIntegral n)
            other -> rtError $ "`exit` expected an Int, but got " <> describe other
        args -> \_ -> arityError "exit" 1 args)
    ])
  ]

-- | One line of standard input.
--
--   Reading past the end of the input is a program-level mistake (a script ran
--   out of answers), not a broken interpreter, so it is reported as a runtime
--   diagnostic with a position rather than escaping as a Haskell exception
--   with a backtrace.
readInputLine :: Text -> Interp Text
readInputLine op = do
  result <- liftIO (try getLine)
  case result of
    Right line -> pure $ T.pack line
    Left e
      | isEOFError e -> rtError $ "`" <> op <> "` reached the end of the input"
      | otherwise -> rtError $ "`" <> op <> "` could not read the input: " <> T.pack (show e)

-- | The argument list of an operation whose arity is fixed did not match.
arityError :: Text -> Int -> [Address] -> Interp a
arityError op expected args =
  rtError $ T.concat [
      "`", op, "` takes ", T.pack (show expected), " argument",
      if expected == 1 then "" else "s",
      ", but was applied to ", T.pack (show (length args))
    ]

-- | A line of input, quoted so that trailing spaces are visible in the message.
quoted :: Text -> Text
quoted t = "`" <> t <> "`"

-- | How a value is named in a runtime error.  The full 'Pretty' instance
--   prints records and closures by address, which is noise in a message that
--   only says "this was not an Int".
describe :: Value -> Text
describe = \case
  VInt _ -> "an Int"
  VFloat _ -> "a Float"
  VBoolean _ -> "a Boolean"
  VString _ -> "a String"
  VNil -> "the unit value"
  VArray _ -> "an array"
  VPair _ _ -> "a pair"
  VRecord _ -> "a record"
  VEnum _ _ -> "an enum value"
  VClosure {} -> "a function"
  VThunk _ _ -> "an unevaluated expression"
  VBThunk _ _ -> "an unevaluated expression"
  VBottom -> "an undefined value"

globalHandlers :: [HandlerFrame]
globalHandlers = [
    HandlerFrame {
      hId = -1,
      hEffect = eff,
      hClauses = Map.fromList [(n, opClause o) | (n, o) <- ops],
      hArities = Map.fromList [(n, o.opArity) | (n, o) <- ops],
      hThen = pure
    }
  | (eff, ops) <- globalOps
  ]

-- | The initial environment: the operations of the built-in effects and the
--   native values, exactly the names 'Builtins.builtins' lists.
--
--   The arithmetic and the strings of the native modules live here as native
--   closures.  Each one forces exactly the arguments whose values it needs:
--   a language whose arguments are delayed must not force a `spin` that its
--   result never mentions, so `||` and `&&` stop at the first deciding
--   argument and every other operation forces only what it reads.
--
--   The command line is not bound here: `args` is an operation of `System`, so
--   it reads 'sCmdArgs' when the program asks for it.  A constant would make
--   every program see the name without naming the effect.
buildInitialEnv :: [String] -> Interp EnvId
buildInitialEnv _cmdArgs = do
  -- замыкания операций строятся из той же таблицы, что и клаузы (арность не дублируется)
  let allocEffectCall eff (op, o) = do
        env <- gets sEnv
        clos <- makeEffectClosure env o.opArity eff op
        addr <- alloc $ VClosure env Nothing (Just (CodeNative Whole op)) clos
        pure (op, (Val, addr))
  opBindings <- fmap concat $ forM globalOps $ \(eff, ops) -> mapM (allocEffectCall eff) ops
  let operations = Map.fromList opBindings
  st <- get

  let emptyCache = Just (IM.empty :: IntMap Address)

      -- Build a curried native function of a given arity.  The closures of the
      -- partially applied stages are allocated on every call, as they were
      -- when each operation was written out by hand.  Each stage keeps the name
      -- of the function and says whether it is the whole function or the rest
      -- of one, so `sayn (map f)` says `map` is applied, not that it is `map`.
      nativeN :: Text -> Int -> ([Address] -> Interp Address) -> Interp Address
      nativeN name n body = go [] n Whole
        where
          go acc 0 _ = body (reverse acc)
          go acc k stage = alloc $ VClosure st.sEnv emptyCache (Just (CodeNative stage name)) $ \arg ->
            go (arg : acc) (k - 1) Partial

      native1 name f = nativeN name 1 $ \case [a] -> f a; _ -> arityError name 1 []
      native2 name f = nativeN name 2 $ \case [a, b] -> f a b; _ -> arityError name 2 []

  -- Reading an argument.  A native operation forces its argument to weak head
  -- normal form and then asks for the value it needs; a wrong shape is a bug in
  -- the checker, not in the program, so the message says what it wanted.
  let valueOfArg :: Address -> Interp Value
      valueOfArg = forceValue

      withInt :: Text -> Address -> (Integer -> Interp a) -> Interp a
      withInt what addr k = valueOfArg addr >>= \case
        VInt i -> k i
        other -> rtError $ "`" <> what <> "` expected an Int, but got " <> describe other

      withFloat :: Text -> Address -> (Scientific -> Interp a) -> Interp a
      withFloat what addr k = valueOfArg addr >>= \case
        VFloat f -> k f
        other -> rtError $ "`" <> what <> "` expected a Float, but got " <> describe other

      withBool :: Text -> Address -> (Bool -> Interp a) -> Interp a
      withBool what addr k = valueOfArg addr >>= \case
        VBoolean b -> k b
        other -> rtError $ "`" <> what <> "` expected a Boolean, but got " <> describe other

      withString :: Text -> Address -> (Text -> Interp a) -> Interp a
      withString what addr k = valueOfArg addr >>= \case
        VString s -> k s
        other -> rtError $ "`" <> what <> "` expected a String, but got " <> describe other

      withArray :: Text -> Address -> ([Address] -> Interp a) -> Interp a
      withArray what addr k = valueOfArg addr >>= \case
        VArray xs -> k xs
        other -> rtError $ "`" <> what <> "` expected an array, but got " <> describe other

      intOp :: Text -> (Integer -> Integer -> Integer) -> Interp Address
      intOp name f = native2 name $ \a b ->
        withInt name a $ \x -> withInt name b $ \y -> alloc $ VInt (f x y)

      intCmp :: Text -> (Integer -> Integer -> Bool) -> Interp Address
      intCmp name f = native2 name $ \a b ->
        withInt name a $ \x -> withInt name b $ \y -> alloc $ VBoolean (f x y)

      intFun :: Text -> (Integer -> Integer) -> Interp Address
      intFun name f = native1 name $ \a ->
        withInt name a $ \x -> alloc $ VInt (f x)

      floatOp :: Text -> (Scientific -> Scientific -> Scientific) -> Interp Address
      floatOp name f = native2 name $ \a b ->
        withFloat name a $ \x -> withFloat name b $ \y -> alloc $ VFloat (f x y)

      floatCmp :: Text -> (Scientific -> Scientific -> Bool) -> Interp Address
      floatCmp name f = native2 name $ \a b ->
        withFloat name a $ \x -> withFloat name b $ \y -> alloc $ VBoolean (f x y)

      floatFun :: Text -> (Scientific -> Scientific) -> Interp Address
      floatFun name f = native1 name $ \a ->
        withFloat name a $ \x -> alloc $ VFloat (f x)

      boolOp :: Text -> (Bool -> Bool -> Bool) -> Interp Address
      boolOp name f = native2 name $ \a b ->
        withBool name a $ \x -> withBool name b $ \y -> alloc $ VBoolean (f x y)

      -- Short-circuiting boolean connectives: the second argument is only
      -- forced when the first one does not decide the result.
      shortCircuit :: Text -> Bool -> Interp Address
      shortCircuit name stopOn = native2 name $ \a b ->
        withBool name a $ \x ->
          if x == stopOn
            then alloc $ VBoolean stopOn
            else withBool name b (alloc . VBoolean)

      string2 :: Text -> (Text -> Text -> Text) -> Interp Address
      string2 name f = native2 name $ \a b ->
        withString name a $ \x -> withString name b $ \y -> alloc $ VString (f x y)

      stringFun :: Text -> (Text -> Text) -> Interp Address
      stringFun name f = native1 name $ \a ->
        withString name a $ \x -> alloc $ VString (f x)

  -- Integers.  `/` and `%` report a zero divisor through the effect `Error`,
  -- so a program can catch it (`under Error to ... handle | error e => ...`)
  -- or let it reach the bottom handler, which reports it as a diagnostic.
  plusAddr <- intOp "+" (+)
  minusAddr <- intOp "-" (-)
  timesAddr <- intOp "*" (*)
  divAddr <- native2 "/" $ \a b ->
    withInt "/" a $ \x -> withInt "/" b $ \y ->
      if y == 0
        then callError "division by zero"
        else alloc $ VInt (x `quot` y)
  remAddr <- native2 "%" $ \a b ->
    withInt "%" a $ \x -> withInt "%" b $ \y ->
      if y == 0
        -- `%` is declared pure, so a zero divisor must not become a catchable
        -- `Error`: it is a mistake of the program, reported as a diagnostic.
        then programError "division by zero"
        else alloc $ VInt (x `rem` y)
  negAddr <- intFun "neg" negate
  absAddr <- intFun "abs" abs
  maxAddr <- intOp "max" max
  minAddr <- intOp "min" min
  ieqAddr <- intCmp "ieq" (==)
  ineqAddr <- intCmp "ineq" (/=)
  igtAddr <- intCmp ">" (>)
  iltAddr <- intCmp "<" (<)
  ileAddr <- intCmp "<=" (<=)
  igeAddr <- intCmp ">=" (>=)

  -- Floats.  `Scientific` is exact in decimal, so `/.' rounds to fifteen
  -- decimal places instead of pretending to be binary: the alternative, a
  -- `Double`, would make `0.1 +. 0.2` print `0.30000000000000004`, and the
  -- language has no notation for that.
  fplusAddr <- floatOp "+." (+)
  fminusAddr <- floatOp "-." (-)
  ftimesAddr <- floatOp "*." (*)
  fdivAddr <- floatOp "/." floatDiv
  fremAddr <- native2 "%." $ \a b ->
    withFloat "%." a $ \x -> withFloat "%." b $ \y ->
      if y == 0
        then programError "division by zero"
        -- The quotient must be computed on `Rational`, not on `Scientific`:
        -- `Scientific`'s `Fractional` instance goes through `fromRational`,
        -- which throws on a repeating decimal, so `5.7 %. 6.28` would crash
        -- the interpreter instead of returning a Float.
        else alloc $ VFloat (x - y * fromInteger (truncate (toRational x / toRational y)))
  fnegAddr <- floatFun "fneg" negate
  fabsAddr <- floatFun "fabs" abs
  fmaxAddr <- floatOp "fmax" max
  fminAddr <- floatOp "fmin" min
  feqAddr <- floatCmp "feq" (==)
  fneqAddr <- floatCmp "fneq" (/=)
  fltAddr <- floatCmp "<." (<)
  fgtAddr <- floatCmp ">." (>)
  fleAddr <- floatCmp "<=." (<=)
  fgeAddr <- floatCmp ">=." (>=)

  toIntAddr <- native1 "to_int" $ \a ->
    withFloat "to_int" a $ \x -> alloc $ VInt (truncate x)
  toFloatAddr <- native1 "to_float" $ \a ->
    withInt "to_float" a $ \x -> alloc $ VFloat (fromInteger x)

  -- Strings.
  concatAddr <- string2 "++" (<>)
  slenAddr <- native1 "slen" $ \a ->
    withString "slen" a $ \s -> alloc $ VInt (fromIntegral (T.length s))
  -- start, length, string: characters outside the string are dropped, so a
  -- slice never fails and `sub 0 n s` is a prefix of `s` of length `n`.
  subAddr <- nativeN "sub" 3 $ \case
    [startA, lenA, sA] -> do
      start <- withInt "sub" startA pure
      len <- withInt "sub" lenA pure
      withString "sub" sA $ \s ->
        alloc $ VString $ T.take (fromInteger (max 0 len)) $ T.drop (fromInteger (max 0 start)) s
    args -> arityError "sub" 3 args
  splitAddr <- native2 "split" $ \a b ->
    withString "split" a $ \sep -> withString "split" b $ \s -> do
      xs <- mapM (alloc . VString) $ if T.null sep then [s] else T.splitOn sep s
      alloc $ VArray xs
  joinAddr <- native2 "join" $ \a b ->
    withString "join" a $ \sep -> withArray "join" b $ \xs -> do
      parts <- mapM (\x -> withString "join" x pure) xs
      alloc $ VString (T.intercalate sep parts)
  trimAddr <- stringFun "trim" T.strip
  upperAddr <- stringFun "upper" T.toUpper
  lowerAddr <- stringFun "lower" T.toLower
  containsAddr <- native2 "contains" $ \a b ->
    withString "contains" a $ \needle -> withString "contains" b $ \hay ->
      alloc $ VBoolean (needle `T.isInfixOf` hay)
  replaceAddr <- nativeN "replace" 3 $ \case
    [fromA, toA, sA] -> do
      from <- withString "replace" fromA pure
      to <- withString "replace" toA pure
      withString "replace" sA $ \s ->
        alloc $ VString (if T.null from then s else T.replace from to s)
    args -> arityError "replace" 3 args
  seqAddr <- native2 "seq" $ \a b ->
    withString "seq" a $ \x -> withString "seq" b $ \y -> alloc $ VBoolean (x == y)
  sneqAddr <- native2 "sneq" $ \a b ->
    withString "sneq" a $ \x -> withString "sneq" b $ \y -> alloc $ VBoolean (x /= y)

  -- Booleans.
  notAddr <- native1 "not" $ \a ->
    withBool "not" a $ \x -> alloc $ VBoolean (not x)
  orAddr <- shortCircuit "||" True
  andAddr <- shortCircuit "&&" False
  xorAddr <- boolOp "^" (/=)
  norAddr <- boolOp "nor" (\a b -> not (a || b))
  nandAddr <- boolOp "nand" (\a b -> not (a && b))

  -- `and` is the old short-circuiting conjunction; it stays because the
  -- examples of the paper use it, and it means the same as `&&`.
  legacyAndAddr <- shortCircuit "and" False

  forceAddr <- alloc $ VClosure st.sEnv emptyCache (Just (CodeNative Whole "force")) force
  whnfBuiltinAddr <- alloc $ VClosure st.sEnv emptyCache (Just (CodeNative Whole "whnf")) whnf
  predAddr <- intFun "pred" (subtract 1)
  assertAddr <- native2 "assert" $ \a b ->
    withBool "assert" a $ \ok ->
      if ok
        then alloc VNil
        else withString "assert" b callError

  -- The polymorphic groups of the standard library.  A record's fields are
  -- monomorphic (see `Builtins`), so these live here as plain functions; when
  -- a record field may be quantified they will move into `Functions`,
  -- `Arrays`, `Pairs` and `Conv`, and the flat names will be views of them.
  --
  -- Each one forces exactly what it needs: `id` and `const` return an argument
  -- untouched, so an argument they ignore is never evaluated, and `head` and
  -- `tail` return element addresses without forcing them -- the pending row of
  -- the array says what forcing costs, and the caller pays it.
  --
  -- `map`, `filter`, `foldl`, `foldr`, `any` and `all` apply the function they
  -- are given at once, not when the result is read.  The row is charged
  -- correctly either way; only the moment differs, and delaying the
  -- application would need a thunk over native code, which the store does not
  -- have.
  let applyTo :: Text -> Address -> Address -> Interp Address
      applyTo what fAddr argAddr = do
        fAddr' <- whnf fAddr
        v <- readCell fAddr'
        case v of
          VClosure env _ _ clos -> do
            oldEnv <- gets sEnv
            modify $ \s -> s {sEnv = env}
            result <- clos argAddr
            modify $ \s -> s {sEnv = oldEnv}
            pure result
          other -> rtError $ "`" <> what <> "` expected a function, but got " <> describe other

      -- Two addresses as a pair, for `curry` and `zip`.
      pairOf :: Address -> Address -> Interp Address
      pairOf l r = alloc (VPair l r)

      -- Apply a predicate and read the Boolean it returned.
      applyBool :: Text -> Address -> Address -> Interp Bool
      applyBool what f x = applyTo what f x >>= \v -> withBool what v pure

  idAddr <- native1 "id" pure
  constAddr <- nativeN "const" 2 $ \case
    [a, _] -> pure a
    args -> arityError "const" 2 args
  flipAddr <- nativeN "flip" 3 $ \case
    [f, b, a] -> applyTo "flip" f a >>= \g -> applyTo "flip" g b
    args -> arityError "flip" 3 args
  composeAddr <- nativeN "compose" 3 $ \case
    [g, f, x] -> applyTo "compose" f x >>= applyTo "compose" g
    args -> arityError "compose" 3 args
  applyAddr <- native2 "apply" $ \f x -> applyTo "apply" f x
  curryAddr <- nativeN "curry" 3 $ \case
    [f, a, b] -> pairOf a b >>= applyTo "curry" f
    args -> arityError "curry" 3 args
  uncurryAddr <- native2 "uncurry" $ \f p -> do
    p' <- whnf p
    v <- readCell p'
    case v of
      VPair l r -> applyTo "uncurry" f l >>= \g -> applyTo "uncurry" g r
      other -> rtError $ "`uncurry` expected a pair, but got " <> describe other

  -- Empty arrays are a program-level mistake, not an interpreter bug, and
  -- `head`/`tail` are declared pure, so it is reported as a diagnostic (E0020)
  -- rather than through the catchable `Error` effect.
  headAddr <- native1 "head" $ \a -> withArray "head" a $ \case
    [] -> programError "`head` of an empty array"
    (x:_) -> pure x
  tailAddr <- native1 "tail" $ \a -> withArray "tail" a $ \case
    [] -> programError "`tail` of an empty array"
    (_:xs) -> alloc $ VArray xs
  emptyAddr <- native1 "empty" $ \a -> withArray "empty" a $ \xs -> alloc $ VBoolean (null xs)
  alenAddr <- native1 "alen" $ \a -> withArray "alen" a $ \xs -> alloc $ VInt (fromIntegral (length xs))
  mapAddr <- native2 "map" $ \f a -> withArray "map" a $ \xs -> do
    ys <- mapM (applyTo "map" f) xs
    alloc $ VArray ys
  filterAddr <- native2 "filter" $ \f a -> withArray "filter" a $ \xs -> do
    flags <- mapM (applyBool "filter" f) xs
    alloc $ VArray [x | (x, True) <- zip xs flags]
  anyAddr <- native2 "any" $ \f a -> withArray "any" a $ \xs -> do
    flags <- mapM (applyBool "any" f) xs
    alloc $ VBoolean (or flags)
  allAddr <- native2 "all" $ \f a -> withArray "all" a $ \xs -> do
    flags <- mapM (applyBool "all" f) xs
    alloc $ VBoolean (and flags)
  foldlAddr <- nativeN "foldl" 3 $ \case
    [f, z, a] -> withArray "foldl" a $ \xs ->
      foldM (\acc x -> applyTo "foldl" f acc >>= \g -> applyTo "foldl" g x) z xs
    args -> arityError "foldl" 3 args
  foldrAddr <- nativeN "foldr" 3 $ \case
    [f, z, a] -> withArray "foldr" a $ \xs -> do
      -- Folded from the right: the accumulator is the last element first.
      let step acc x = do
            g <- applyTo "foldr" f x
            applyTo "foldr" g acc
      foldM step z (reverse xs)
    args -> arityError "foldr" 3 args
  concatAddr' <- native1 "concat" $ \a -> withArray "concat" a $ \xs -> do
    parts <- mapM (\x -> withArray "concat" x pure) xs
    alloc $ VArray (concat parts)
  zipAddr <- native2 "zip" $ \a b -> withArray "zip" a $ \as ->
    withArray "zip" b $ \bs -> do
      pairs <- mapM (uncurry pairOf) (zip as bs)
      alloc $ VArray pairs
  atAddr <- native2 "at" $ \a i -> withArray "at" a $ \xs ->
    withInt "at" i $ \n ->
      if n >= 0 && n < fromIntegral (length xs)
        then pure (xs !! fromIntegral n)
        else callError $ T.concat [
            "`at`: index ", T.pack (show n), " is out of range for an array of ",
            T.pack (show (length xs)), if length xs == 1 then " element" else " elements"
          ]
  takeAddr <- native2 "take" $ \n a -> withInt "take" n $ \k ->
    withArray "take" a $ \xs ->
      alloc $ VArray (take (max 0 (fromIntegral k)) xs)
  dropAddr <- native2 "drop" $ \n a -> withInt "drop" n $ \k ->
    withArray "drop" a $ \xs ->
      alloc $ VArray (drop (max 0 (fromIntegral k)) xs)

  fstAddr <- native1 "fst" $ \p -> do
    p' <- whnf p
    v <- readCell p'
    case v of
      VPair l _ -> pure l
      other -> rtError $ "`fst` expected a pair, but got " <> describe other
  sndAddr <- native1 "snd" $ \p -> do
    p' <- whnf p
    v <- readCell p'
    case v of
      VPair _ r -> pure r
      other -> rtError $ "`snd` expected a pair, but got " <> describe other

  -- `show` is `say` without the line: the value is forced, because a printed
  -- value is its text, not a reference to a cell.
  showAddr <- native1 "show" $ \a -> do
    s <- force a >>= stringify
    alloc $ VString s

  -- `==` and `!=` compare two values of one type structurally; `===` and
  -- `!==` compare the values themselves, so `1 === 1` is false: the two 1s are
  -- two values.  The structural comparison forces both sides, because a value
  -- is what is compared, not a reference to a cell.
  eqAddr <- native2 "==" $ \a b -> do
    same <- equalValues Set.empty a b
    alloc $ VBoolean same
  neqAddr <- native2 "!=" $ \a b -> do
    same <- equalValues Set.empty a b
    alloc $ VBoolean (not same)
  refEqAddr <- native2 "===" $ \a b -> do
    a' <- whnf a
    b' <- whnf b
    alloc $ VBoolean (addrId a' == addrId b')
  refNeqAddr <- native2 "!==" $ \a b -> do
    a' <- whnf a
    b' <- whnf b
    alloc $ VBoolean (addrId a' /= addrId b')

  -- `try body on_error` runs `body` with a handler for `Error` installed: a
  -- caught message goes to `on_error`, and a body that finishes normally keeps
  -- its value.  The handler is pushed and popped here rather than built by
  -- `TEHandle`, because the body is a value the program passes, not a block the
  -- checker saw: nothing about it is known until it runs.
  tryAddr <- native2 "try" $ \body onError -> do
    env <- gets sEnv
    kstack0 <- gets sKstack
    handlerId <- gets sNextHandler
    modify $ \s -> s {sNextHandler = handlerId + 1}
    callCC $ \finish -> do
      let finishWithThen result = do
            modify $ \s -> s {sKstack = kstack0, sEnv = env}
            finish result
          catchClause args k = case args of
            [msgAddr] -> do
              modify $ \s -> s {sKstack = kstack0, sEnv = env}
              applyTo "try" onError msgAddr >>= \r -> whnf r >>= finishWithThen
            args -> arityError "error" 1 args
          handler = HandlerFrame
            handlerId
            (Eff.elabel "Error")
            (Map.singleton "error" catchClause)
            (Map.singleton "error" 1)
            finishWithThen
      modify $ \s -> s {sKstack = handler : s.sKstack}
      unit <- alloc VNil
      result <- applyTo "try" body unit >>= whnf
      finishWithThen result

  let natives = [
          ("+", plusAddr),
          ("-", minusAddr),
          ("*", timesAddr),
          ("/", divAddr),
          ("%", remAddr),
          ("neg", negAddr),
          ("abs", absAddr),
          ("max", maxAddr),
          ("min", minAddr),
          ("ieq", ieqAddr),
          ("ineq", ineqAddr),
          (">", igtAddr),
          ("<", iltAddr),
          ("<=", ileAddr),
          (">=", igeAddr),
          ("+.", fplusAddr),
          ("-.", fminusAddr),
          ("*.", ftimesAddr),
          ("/.", fdivAddr),
          ("%.", fremAddr),
          ("fneg", fnegAddr),
          ("fabs", fabsAddr),
          ("fmax", fmaxAddr),
          ("fmin", fminAddr),
          ("feq", feqAddr),
          ("fneq", fneqAddr),
          ("<.", fltAddr),
          (">.", fgtAddr),
          ("<=.", fleAddr),
          (">=.", fgeAddr),
          ("to_int", toIntAddr),
          ("to_float", toFloatAddr),
          ("++", concatAddr),
          ("slen", slenAddr),
          ("sub", subAddr),
          ("split", splitAddr),
          ("join", joinAddr),
          ("trim", trimAddr),
          ("upper", upperAddr),
          ("lower", lowerAddr),
          ("contains", containsAddr),
          ("replace", replaceAddr),
          ("seq", seqAddr),
          ("sneq", sneqAddr),
          ("not", notAddr),
          ("||", orAddr),
          ("&&", andAddr),
          ("^", xorAddr),
          ("nor", norAddr),
          ("nand", nandAddr),
          ("and", legacyAndAddr),
          ("force", forceAddr),
          ("whnf", whnfBuiltinAddr),
          ("pred", predAddr),
          ("assert", assertAddr),
          ("id", idAddr),
          ("const", constAddr),
          ("flip", flipAddr),
          ("compose", composeAddr),
          ("apply", applyAddr),
          ("curry", curryAddr),
          ("uncurry", uncurryAddr),
          ("head", headAddr),
          ("tail", tailAddr),
          ("empty", emptyAddr),
          ("alen", alenAddr),
          ("map", mapAddr),
          ("filter", filterAddr),
          ("any", anyAddr),
          ("all", allAddr),
          ("foldl", foldlAddr),
          ("foldr", foldrAddr),
          ("concat", concatAddr'),
          ("zip", zipAddr),
          ("at", atAddr),
          ("take", takeAddr),
          ("drop", dropAddr),
          ("fst", fstAddr),
          ("snd", sndAddr),
          ("show", showAddr),
          ("==", eqAddr),
          ("!=", neqAddr),
          ("===", refEqAddr),
          ("!==", refNeqAddr),
          ("try", tryAddr)
        ]

  let justNatives = Map.fromList $ map (\(n, a) -> (n, (Val, a))) natives

      allBindings = operations <> justNatives

      -- The checker and the interpreter must offer the same names: a name the
      -- program can call but the interpreter cannot run would crash, and a
      -- name the interpreter can run but the checker rejects is dead code.
      missing = [n | n <- Builtins.names, not (Map.member n allBindings)]
      extra = [n | n <- Map.keys allBindings, n `notElem` Builtins.names]

  unless (null missing && null extra) $
    rtError $ T.concat [
        "internal error: the interpreter and the builtin table disagree",
        if null missing then "" else "; missing: " <> T.intercalate ", " missing,
        if null extra then "" else "; unexpected: " <> T.intercalate ", " extra
      ]

  modifyCurrentEnv $ \e -> e {bindings = allBindings <> e.bindings}

-- | Raise an error through the effect @Error@, so that a handler installed by
--   the program sees it and the bottom handler turns it into a diagnostic when
--   no handler does.
callError :: Text -> Interp Address
callError msg = do
  addr <- alloc (VString msg)
  callEffect (Eff.elabel "Error") "error" [addr]

-- | A failure of a `File` operation, reported through `Error` with the
--   operation and the path in the message: the OS message alone ("does not
--   exist") leaves a reader guessing which file.
fileError :: Text -> Text -> IOException -> Interp Address
fileError op path e = callError $ T.concat [
    "`", op, "` on `", path, "`: ", T.pack (show e)
  ]

-- | Read the path and the text of a two-argument file operation.
withFilePathAndText :: Text -> Address -> Address -> (Text -> Text -> Interp Address) -> Interp Address
withFilePathAndText op pathAddr textAddr k = do
  pathV <- forceValue pathAddr
  textV <- forceValue textAddr
  case (pathV, textV) of
    (VString path, VString text) -> k path text
    _ -> rtError $ "`" <> op <> "` needs a String as both the path and the text"

-- | The first of the actions that answers.
firstJustM :: [IO (Maybe a)] -> IO (Maybe a)
firstJustM [] = pure Nothing
firstJustM (a:rest) = a >>= \case
  Just x -> pure (Just x)
  Nothing -> firstJustM rest

-- | Division of decimals, rounded to fifteen places.
--
--   `Scientific` has no division of its own: the quotient of two decimals is
--   not necessarily a decimal.  The rounding is explicit so that the result is
--   a value of the same type as its operands, and a reader sees the precision
--   the language promises rather than the one a `Double` happens to have.
floatDiv :: Scientific -> Scientific -> Scientific
floatDiv _ 0 = 0 -- unreachable: the caller reports a zero divisor first
floatDiv x y = normalize (scientific n (-15))
  where
    n = round (toRational x / toRational y * 10 ^ (15 :: Int)) :: Integer


-- | Выполнение чанка (игнорируем декларации, просто идём дальше)
evalChunk :: IR.Chunk -> Interp Value
evalChunk mod'@(Module _ chunk) = do
  st <- get
  let env0 = st.sEnv

  let functDefs = [fd | IR.SFunctDef fd <- chunk, fd.fName /= "main"]
  forM_ functDefs $ \fd -> do
    let cache = case fst fd.fRet of
          Just fxs -> if isPureClosure fxs then Just IM.empty else Nothing
          _ -> Just IM.empty
    fn <- makeTopLevelClosure env0 fd
    void $ bindValIn env0 fd.fName $ VClosure env0 cache
          (Just (CodeFun Whole fd.fName (map fst $ IR.fArgs fd) (IR.fBlock fd))) fn

  -- The constructors of a declared enumeration are ordinary functions of the
  -- program's scope, so a value is built by applying one: `Some 5`.
  let enumDefs = [ed | IR.SEnumDef ed <- chunk]
  forM_ enumDefs $ \def ->
    forM_ (enumCases def) $ \c -> do
      let muts = [m | (m, _, _) <- enumCaseFields c]
      ctor <- makeConstructor env0 (enumCaseName c) muts
      void $ bindValAddrIn env0 (enumCaseName c) ctor

  let mainDecl = findMain mod'
  case mainDecl of
    Nothing -> liftIO (putStrLn "Warning: No 'main' function found") >> pure VNil
    Just (IR.SFunctDef mainFunct) -> do
      resultAddr0 <- evalBlock (IR.fBlock mainFunct) pure
      -- результат main доводится до значения: иначе отложенный хвост (ветка if) не выполнится
      resultAddr <- whnfAddr resultAddr0
      reportEvents (fst $ IR.fRet mainFunct)
      traceEval $ T.unpack $ "evalChunk resultAddr: " <> pretty resultAddr
      readCell resultAddr
    Just _ -> rtError "'main' is not a function definition"

findMain :: IR.Chunk -> Maybe IR.TopLevelStat
findMain (Module _ decls) = find isMain decls
  where
    isMain = \case
      (IR.SFunctDef fd) -> fd.fName == "main"
      _ -> False

makeTopLevelClosure :: EnvId -> IR.FunctDecl -> Interp (Address -> Interp Address)
makeTopLevelClosure env fd =
  makeClosureChain env fd.fName (map fst $ IR.fArgs fd) (IR.fBlock fd)

-- | A curried function, as nested lambdas: each argument extends the scope of
--   the previous one, and the first extends the scope where the function is
--   defined (E-App).  The chain must not be built from the caller's scope: a
--   call sees only its lexical parents, and a tail call would otherwise append
--   the caller's environment to the callee's, which made a long loop grow
--   without bound.
makeClosureChain :: EnvId -> Text -> [Text] -> IR.Block -> Interp (Address -> Interp Address)
makeClosureChain _ _ [] _ =
  rtError "internal error: a top-level function was declared with no arguments"
makeClosureChain env _ [argName] block = pure $ \argAddr -> do
  outer <- gets sEnv
  eid <- newEnv Env {
      bindings = Map.singleton argName (Val, argAddr),
      parent = Just env
    }
  modify $ \s -> s {sEnv = eid}
  result <- evalBlock block pure
  modify $ \s -> s {sEnv = outer}
  pure result
makeClosureChain env name (argName:rest) block = pure $ \argAddr -> do
  outer <- gets sEnv
  eid <- newEnv Env {
      bindings = Map.singleton argName (Val, argAddr),
      parent = Just env
    }
  modify $ \s -> s {sEnv = eid}
  -- The rest of the function closes over this argument's scope.
  restClosure <- makeClosureChain eid name rest block
  -- The closure this stage returns is the rest of the function, not the
  -- function: it is missing an argument, and printing says so.
  result <- allocClosure eid (Just IM.empty) (CodeFun Partial name rest block) restClosure
  modify $ \s -> s {sEnv = outer}
  pure result

-- | Замыкание с кодом: код нужен снимку, чтобы переписать функцию (модель: freezeV на замыканиях)
allocClosure :: EnvId -> Maybe (IntMap Address) -> Code -> (Address -> Interp Address) -> Interp Address
allocClosure env cache code fn = alloc (VClosure env cache (Just code) fn)

-- | Run an action as if the interpreter stood at this node, so that a runtime
--   error raised inside it points at the right place.  The previous position is
--   restored afterwards: the caller is still evaluating its own node.
atSpan :: Span -> Interp a -> Interp a
atSpan sp action = do
  old <- gets sSpan
  modify $ \s -> s {sSpan = sp}
  result <- action
  modify $ \s -> s {sSpan = old}
  pure result

-- | Выполнение выражения
evalExpr :: TypedExpr -> (Address -> Interp Address) -> Interp Address
evalExpr expr cont = atSpan (teSpan expr) $ case expr of
    TEInt i -> do
      traceEval $ "evalExpr [TEInt] | " <> show i
      cont =<< alloc (VInt i)
    TEFloat f -> do
      traceEval $ "evalExpr [TEFloat] | " <> show f
      cont =<< alloc (VFloat f)
    TEBoolean b -> do
      traceEval $ "evalExpr [TEBoolean] | " <> show b
      cont =<< alloc (VBoolean b)
    TEString s -> do
      traceEval $ "evalExpr [TEString] | " <> T.unpack s
      cont =<< alloc (VString s)
    TENil -> do
      traceEval "evalExpr [TENil]"
      cont =<< alloc VNil
    TEXVar n _ -> do
      traceEval $ "evalExpr [TEXVar] | " <> T.unpack n
      env <- gets sEnv
      (_, m, a) <- findBindingEnv env n
      when (m == Var) $ logEvent EvRead
      cont a
    TEArray _ _ xs -> do
      traceEval $ "evalExpr [TEArray] | [" <> T.unpack (T.intercalate ", " $ map pretty xs) <> "]"
      st <- get
      xs' <- mapM (\x -> alloc $ VThunk x st.sEnv) xs
      cont =<< alloc (VArray xs')
    TEPair _ l r -> do
      env <- gets sEnv
      traceEval $ "evalExpr [TEPair] | l: " <> T.unpack (pretty l) <> ", r: " <> T.unpack (pretty r)
      l' <- alloc $ VThunk l env
      r' <- alloc $ VThunk r env
      cont =<< alloc (VPair l' r')
    TEXLambda lam -> do
      env <- gets sEnv
      traceEval $ "evalExpr [TEXLambda] | " <> T.unpack (pretty lam)
      body <- evalLambda env lam
      let cache = if isPureClosure lam.lFxs then Just IM.empty else Nothing
      cont =<< allocClosure env cache (CodeLam lam) body
    -- A native name in value position is not a node the interpreter ever
    -- evaluates: `Scope.valueOf` puts a `TENLambda` into the binding for the
    -- checker to name the type, and the interpreter finds the value in the
    -- native scope, above the program's.  A program that stores such a name
    -- (`val f = +; f 1 2`) keeps the variable, which resolves to that same
    -- native address.  So this branch is unreachable, and saying so is more
    -- useful than pretending to implement a second kind of closure.
    TENLambda _ -> rtError "internal error: a native signature reached the interpreter as a value"
    TEApply f x -> do
      traceEval $ "evalExpr [TEApply] | f: " <> T.unpack (pretty f) <> ", x: " <> T.unpack (pretty x)
      fAddr <- force =<< evalExpr f pure
      xAddr <- delayArg x
      v <- readCell fAddr
      case v of
        VClosure env' (Just cache) code clos -> do
          noMemo <- gets sNoMemo
          case (if noMemo then Nothing else IM.lookup (addrToInt xAddr) cache) of
            Just cached -> do
              traceEval $ concat [
                  "evalExpr [TEApply] | fAddr: ",
                  T.unpack $ pretty fAddr,
                  ", xAddr: ",
                  T.unpack $ pretty xAddr,
                  ", don't need to eval: xAddr is cached"
                ]
              pure cached
            _ -> do
              oldEnv <- gets sEnv
              modify $ \s -> s {sEnv = env'}
              result <- clos xAddr
              modify $ \s -> s {sEnv = oldEnv}
              -- Memoisation keeps one entry, not a growing table: an argument
              -- is a fresh cell on every call of a function written as a
              -- recursion, so a table keyed by argument address would only
              -- grow.  One entry still catches the case memoisation is for --
              -- the same cell applied to the same function repeatedly -- and
              -- dropping an entry is transparent for a pure closure: it only
              -- costs a recomputation.
              writeCell fAddr (VClosure env' (Just (IM.singleton (addrToInt xAddr) result)) code clos)
              pure result
        VClosure env' _ _ clos -> do
          oldEnv <- gets sEnv
          modify $ \s -> s {sEnv = env'}
          result <- clos xAddr
          modify $ \s -> s {sEnv = oldEnv}
          pure result
        _ -> rtError $ "the left side of an application is not a function: it is " <> describe v
    TERecord _ ps _ -> do
      st <- get
      when (any (\p -> p.terMut == Var) ps) $ logEvent EvCreate
      triples <- mapM (\p -> (p.terMut, p.terName, ) <$> alloc (VThunk p.terExpr st.sEnv)) ps
      eid <- newEnv Env {
        bindings = Map.fromList [(n, (m, a)) | (m, n, a) <- triples],
        parent = Nothing
      }
      cont =<< alloc (VRecord eid)
    TEPropAccess r x -> do
      rAddr <- whnf =<< evalExpr r pure
      v <- readCell rAddr
      case v of
        VRecord eid -> do
          env <- getEnv eid
          case getCell env x of
            Just (m, a) -> do
              when (m == Var) $ logEvent EvRead
              cont a
            Nothing -> rtError $ "this record has no field `" <> x <> "`"
        _ -> rtError $ "cannot read the field `" <> x <> "` of " <> describe v <> "; only records have fields"
    TEHandle (IR.Handler fx b clauses thenLam) _ -> do
      env <- gets sEnv
      thenFn <- evalLambda env thenLam
      kstack0 <- gets sKstack
      handlerId <- gets sNextHandler
      modify $ \s -> s {sNextHandler = handlerId + 1}
      callCC $ \finish -> do
        let finishWithThen result = do
              traceEval "running then"
              -- обработчик снимается до then: эффекты в then обрабатывает внешний обработчик
              modify $ \s -> s {sKstack = kstack0}
              thenResult <- thenFn result
              modify $ \s -> s {sEnv = env}
              finish thenResult
        let clausesMap = Map.fromList $ map (makeClause handlerId finishWithThen) clauses
            handler = HandlerFrame handlerId fx clausesMap
              (Map.fromList [(name, arity) | (name, _, _, arity) <- clauses])
              finishWithThen
        -- операции эффекта живут в собственном окружении, а не в текущем
        opsEnv <- newEnv Env {bindings = Map.empty, parent = Just env}
        forM_ clauses $ \(name, _, _, arity) -> do
          fn <- makeEffectClosure opsEnv arity fx name
          void $ bindValIn opsEnv name (VClosure opsEnv (Just IM.empty) (Just (CodeNative Whole name)) fn)
        modify $ \s -> s {sEnv = opsEnv, sKstack = handler : s.sKstack}
        -- The body is evaluated to weak head normal form while the handler is
        -- still installed: a thunk returned by the body must not escape and
        -- perform its effects after the handler has been popped.  The model
        -- forces to WHNF, so fields of a returned record or pair stay lazy.
        result <- evalBlock b pure
        result' <- whnf result
        finishWithThen result'
    p@(TEParen _) -> do
      env <- gets sEnv
      cont =<< alloc (VThunk p env)
    TEResume t _ -> do
      -- resume живёт в окружении клаузы, а вызов идёт в его потомке: ищем по цепочке
      env <- gets sEnv
      rAddr <- lookupRef env "resume"
      rVal <- readCell rAddr
      case rVal of
        VClosure _ _ _ clos -> do
          tAddr <- evalExpr t pure
          clos tAddr
        _ -> rtError "`resume` is not a continuation here; it may only be used inside a handler clause"
    TELet pat bound body -> do
      -- A destructuring pattern inspects the *value* of the right-hand side, so
      -- it has to be forced first: `let (a, b) = p` must work when `p` is a
      -- thunk, not only when the right-hand side is a literal pair.  A plain
      -- name pattern binds the address itself, and forcing there would make
      -- `let` strict, which it is not.
      addr0 <- evalExpr bound pure
      addr <- if needsValue pat then whnf addr0 else pure addr0
      bindings' <- matchPattern pat addr
      -- модель: let открывает область; привязки паттерна не выходят за тело
      outer <- gets sEnv
      letEnv <- newEnv Env {
        bindings = Map.fromList [(n, (m, a)) | (n, m, a) <- bindings'],
        parent = Just outer
      }
      modify $ \s -> s {sEnv = letEnv}
      result <- evalExpr body pure
      modify $ \s -> s {sEnv = outer}
      cont result
    TEIfElse cond thenExpr elseExpr -> do
      condVal <- forceValue =<< evalExpr cond pure
      env <- gets sEnv
      case condVal of
        VBoolean True -> cont =<< alloc (VThunk thenExpr env)
        VBoolean False -> cont =<< alloc (VThunk elseExpr env)
        _ -> rtError $ "the condition of an `if` must be a Boolean, but this one is " <> describe condVal
    -- `match e to clauses`: the first clause whose patterns all accept the
    -- subject and whose guard holds runs, and its block is the value.  A
    -- missing clause is a mistake the checker proves away ('NonExhaustiveMatch'),
    -- so reaching the end here means the program did not follow its own types.
    TEMatch subject _ clauses -> do
      traceEval "evalExpr [TEMatch]"
      subjectAddr <- whnf =<< evalExpr subject pure
      subjectEnv <- gets sEnv
      -- The patterns of one clause are alternatives of the same value: the
      -- first one that accepts it supplies the names the block sees.
      let tryPatterns [] = pure Nothing
          tryPatterns (p : ps) =
            matchTPattern p subjectAddr >>= \case
              Nothing -> tryPatterns ps
              Just bindings -> pure $ Just [(n, (Val, a)) | (n, a) <- bindings]
          runClauses [] =
            rtError "no clause of this `match` accepts the value, although the checker proved one must"
          runClauses (TMatchClause ps guard block : rest) = do
            tryPatterns ps >>= \case
              Nothing -> runClauses rest
              Just bindings -> do
                clauseEnv <- newEnv Env {bindings = Map.fromList bindings, parent = Just subjectEnv}
                oldEnv <- gets sEnv
                modify $ \s -> s {sEnv = clauseEnv}
                guardOk <- case guard of
                  Nothing -> pure True
                  Just g -> do
                    gAddr <- whnf =<< evalExpr g pure
                    readCell gAddr >>= \case
                      VBoolean b -> pure b
                      _ -> rtError "the guard of a `match` clause is not a Boolean"
                if guardOk
                  then do
                    result <- evalBlock block pure
                    modify $ \s -> s {sEnv = oldEnv}
                    cont result
                  else do
                    modify $ \s -> s {sEnv = oldEnv}
                    runClauses rest
      runClauses clauses
    TEAnnot e _ -> evalExpr e cont

-- | Mark a cell whose value is being computed, and report a cycle when the
--   same cell is reached again before it has a value.
--
--   The cell is not overwritten until its thunk has been evaluated (that is
--   what call-by-need caches), so a thunk that needs itself -- directly or
--   through a rebinding, as in @val y = + x 1; x := + y 1@ -- would chase its
--   own address forever.  The model has no rule for that term: it diverges.
--   An interpreter can do better than spinning, and a diagnostic with a
--   position is what a reader can act on.
withForcing :: Address -> Interp a -> Interp a
withForcing a action = do
  forcing <- gets sForcing
  when (Set.member (addrId a) forcing) $ blackholeError a
  modify $ \s -> s {sForcing = Set.insert (addrId a) s.sForcing}
  result <- action
  modify $ \s -> s {sForcing = Set.delete (addrId a) s.sForcing}
  pure result

-- | A value that needs itself.  The position is the delayed expression that
--   formed the cycle, because that is the line a reader has to change.
blackholeError :: Address -> Interp a
blackholeError a = do
  v <- readCell a
  current <- gets sSpan
  let sp = case v of
        VThunk e _ -> teSpan e
        _ -> current
      message = T.concat [
          "the value of this binding depends on itself: computing it needs the ",
          "same cell again, so it never gets a value. A delayed computation ",
          "reads a mutable binding as it is when it is forced, so ",
          "`val y = + x 1; x := + y 1` makes `y` and `x` wait for each other."
        ]
  lift $ throwError (InterpError message sp (Just "E0020"))

-- | Приводит VThunk к значению и возвращает его адрес
force :: Address -> Interp Address
force addr = withForcing addr $ do
  v0 <- readCell addr
  case v0 of
    VThunk expr env' -> do
      traceEval $ "force | Forcing " <> T.unpack (pretty addr) <> ": " <> show expr
      oldEnv <- gets sEnv
      modify $ \s -> s {sEnv = env'}
      resultAddr <- case expr of
        TEParen b -> evalBlock b pure
        _ -> evalExpr expr pure
      traceEval $ "force | resultAddr: " <> T.unpack (pretty resultAddr)
      resultAddr' <- force resultAddr
      traceEval $ "force | resultAddr': " <> T.unpack (pretty resultAddr')
      resultVal <- readCell resultAddr'
      traceEval $ "force | resultVal: " <> T.unpack (pretty resultVal)
      modify $ \s -> s {sEnv = oldEnv}
      writeCell addr resultVal
      pure addr  -- возвращаем тот же адрес, но теперь там значение
    VArray es -> do
      mapM_ force es
      pure addr
    VPair l r -> do
      _ <- force l
      _ <- force r
      pure addr
    VRecord eid -> do
      _ <- go eid
      pure addr
      where
        go :: EnvId -> Interp EnvId
        go eid' = do
          env <- getEnv eid'
          forM_ (Map.elems env.bindings) $ force . snd
          case env.parent of
            Just p -> go p
            _ -> pure eid'
    VEnum _ fs -> do
      mapM_ (force . snd) fs
      pure addr
    _ -> do
      traceEval $ "force | No need to force " <> T.unpack (pretty addr)
      pure addr

-- | Слабая головная нормальная форма (модель: S-Expr, E-Prop): thunk вычисляется до
--   значения, компоненты записей, массивов и пар остаются ленивыми (в отличие от force)
--
--   Chasing a chain of thunks is a loop, not a recursion: the else branch of an
--   @if@ is a thunk, so a loop written as a tail call produces one thunk per
--   iteration, and a recursive chase would keep one continuation frame per
--   iteration alive.  Only the cell the caller named is overwritten; the
--   intermediate cells were freshly allocated and are unreachable once the
--   value is known.
whnf :: Address -> Interp Address
whnf addr = go Set.empty addr
  where
    go seen a = do
      v <- readCell a
      case v of
        VThunk expr env' -> do
          -- A chain of thunks that comes back to a cell it already visited
          -- never reaches a value: the cell is only overwritten after the
          -- chase ends, so the same expression would be entered again.
          when (Set.member (addrId a) seen) $ blackholeError a
          oldEnv <- gets sEnv
          modify $ \s -> s {sEnv = env'}
          resultAddr <- case expr of
            TEParen b -> evalBlock b pure
            _ -> evalExpr expr pure
          modify $ \s -> s {sEnv = oldEnv}
          go (Set.insert (addrId a) seen) resultAddr
        _ -> do
          writeCell addr v
          pure addr

-- | Приводит VThunk к значению и возвращает само значение
forceValue :: Address -> Interp Value
forceValue addr = withForcing addr $ do
  v0 <- readCell addr
  case v0 of
    VThunk expr env' -> do
      traceEval $ "forceValue | Forcing " <> T.unpack (pretty addr) <> ": " <> show expr
      oldEnv <- gets sEnv
      modify $ \s -> s {sEnv = env'}
      resultAddr <- force =<< evalExpr expr pure
      resultVal <- readCell resultAddr
      modify $ \s -> s {sEnv = oldEnv}
      writeCell addr resultVal
      pure resultVal
    _ -> do
      traceEval $ "forceValue | No need to force " <> T.unpack (pretty addr)
      pure v0

callEffect :: ECons -> Text -> [Address] -> Interp Address
callEffect eff opName args = do
  callCC $ \k -> do
    traceEval $ concat [
        "callEffect: ", show eff, " ", show opName, " with args [", intercalate ", " $ map show args, "]"
      ]
    st <- get
    case find ((== eff) . hEffect) st.sKstack of
      Just handler -> do
        case Map.lookup opName handler.hClauses of
          Just clauseFn -> clauseFn args k
          Nothing -> rtError $ T.concat [
              "the handler for `", effectName eff, "` does not handle `", opName, "`"
            ]
      Nothing -> rtError $ T.concat [
          "there is no handler for the effect `", effectName eff, "` in scope"
        ]

-- | The name of an effect, without its type arguments.
effectName :: ECons -> Text
effectName (ECons n _) = n

evalLambda :: EnvId -> IR.Lambda -> Interp (Address -> Interp Address)
evalLambda eid lam =
  pure $ \addr -> do
    -- модель (E-App): каждый вызов получает собственное окружение с параметром;
    -- окружение замыкания не меняется
    outer <- gets sEnv
    callEnv <- newEnv Env {
        bindings = Map.singleton lam.lArg (Val, addr),
        parent = Just eid
      }
    modify $ \s -> s {sEnv = callEnv}
    result <- evalBlock lam.lBlock pure
    modify $ \s -> s {sEnv = outer}
    pure result

makeEffectClosure ::
  EnvId
  -> Int
  -> ECons
  -> Text
  -> Interp (Address -> Interp Address)
makeEffectClosure env arity eff op =
    go [] arity
  where
    go acc n =
      pure $ \arg -> case n of
        1 -> callEffect eff op $ reverse (arg : acc)
        _ -> alloc . VClosure env (Just IM.empty) (Just (CodeNative Partial op)) =<< go (arg : acc) (n - 1)

makeClause ::
  Int                             -- the handler that owns the clauses
  -> (Address -> Interp Address)  -- finishWithThen
  -> IR.HandlerClause
  -> (Text, Clause)
makeClause handlerId finishWithThen
  (name, lam, hasResume, _) =
    (name, runClause)
  where
    runClause args k = do
      traceEval $ "makeClause: " <> show name <> " called with args " <> show args
      cur <- gets sEnv
      -- A continuation is one-shot: resuming it twice would replay the rest of
      -- the handled computation with the current heap, duplicating mutations.
      -- It also dies with its handler: a continuation invoked after the
      -- handler returned would re-enter the handled code with the wrong stack.
      contId <- gets sNextCont
      modify $ \s -> s {sNextCont = contId + 1}
      resumeAddr <- alloc $ VClosure cur (Just IM.empty) Nothing $ \tAddr -> do
        alive <- gets (any ((== handlerId) . hId) . sKstack)
        unless alive $
          rtError "`resume` was called after its handler returned; the continuation is no longer installed"
        used <- gets sUsedConts
        when (Set.member contId used) $
          rtError "`resume` was called more than once; a handler continuation is one-shot"
        modify $ \s -> s {sUsedConts = Set.insert contId s.sUsedConts}
        k tAddr
      modify $ \s -> s {sContAddrs = Set.insert (addrToInt resumeAddr) s.sContAddrs}

      -- resume живёт в собственном окружении клаузы
      eid <- newEnv Env {
        bindings = Map.singleton "resume" (Val, resumeAddr),
        parent = Just cur
      }

      clos <- evalLambda eid lam
      result <- applyMany clos eid IM.empty args
      modify $ \s -> s {sEnv = cur}

      case hasResume of
        NoResume -> finishWithThen result
        _ -> do
          -- Returning from a clause that contains `resume` is the one
          -- resumption when the clause did not take the `resume` branch.
          used <- gets sUsedConts
          when (Set.member contId used) $
            rtError "internal error: a handler clause returned after resuming its continuation"
          modify $ \s -> s {sUsedConts = Set.insert contId s.sUsedConts}
          k result

applyMany :: (Address -> Interp Address) -> EnvId -> IntMap Address -> [Address] -> Interp Address
applyMany clos eid cache args = do
  traceEval $ "applyMany: args = " <> show args
  case args of
    [] -> rtError "internal error: a handler clause was applied to no arguments"
    [x] -> applyClos x clos eid cache
    (x:xs) -> do
      addr <- clos x
      v <- readCell addr
      case v of
        VClosure eid' (Just cache') _ next -> applyMany next eid' cache' xs
        VClosure eid' _ _ next -> applyMany next eid' IM.empty xs
        _ -> rtError $ "a handler clause returned " <> describe v <> " instead of a function"
  where
    applyClos :: Address -> (Address -> Interp Address) -> EnvId -> IntMap Address -> Interp Address
    applyClos xAddr cl eid' cache' =
      case IM.lookup (addrToInt xAddr) cache' of
        Just cached -> do
          traceEval $ T.unpack $ "Don't have to apply many closure: " <> pretty xAddr <> " is cached"
          pure cached
        _ -> do
          traceEval $ T.unpack $ "Apply many closure to " <> pretty xAddr
          oldEnv <- gets sEnv
          modify $ \s -> s {sEnv = eid'}
          result <- cl xAddr
          traceEval $ T.unpack $ "Apply many result address: " <> pretty result
          modify $ \s -> s {sEnv = oldEnv}
          pure result

evalBlock :: Block -> (Address -> Interp Address) -> Interp Address
evalBlock (sts, expr) cont = do
  -- модель (E-Block): привязки блока видны только внутри него
  outer <- gets sEnv
  forM_ sts evalStat
  result <- evalExpr expr pure
  modify $ \s -> s {sEnv = outer}
  cont result

-- | Новое окружение для остатка блока: одна привязка поверх текущего
--  (модель: S-Val/Var/Imm). Ранее созданные замыкания и thunk'и остаются
--  в прежнем окружении и поэтому не видят новую привязку.
extendEnv :: Text -> Mutability -> Address -> Interp EnvId
extendEnv n m a = do
  cur <- gets sEnv
  eid' <- newEnv Env {
      bindings = Map.singleton n (m, a),
      parent = Just cur
    }
  modify $ \s -> s {sEnv = eid'}
  pure eid'

-- | Аргумент применения откладывается (E-App): атомарные выражения вычисляются
--  сразу, остальные становятся thunk'ом над текущим окружением.
delayArg :: TypedExpr -> Interp Address
delayArg x = case x of
  TEXVar _ _ -> evalExpr x pure
  TEInt _ -> evalExpr x pure
  TEFloat _ -> evalExpr x pure
  TEBoolean _ -> evalExpr x pure
  TEString _ -> evalExpr x pure
  TENil -> evalExpr x pure
  TEXLambda _ -> evalExpr x pure
  _ -> do
    env <- gets sEnv
    alloc (VThunk x env)

-- | Довести отложенное вычисление по адресу до значения (без глубокого форсирования
--  уже вычисленных структур)
whnfAddr :: Address -> Interp Address
whnfAddr = whnf

evalStat :: IR.Stat -> Interp ()
evalStat stat = atSpan (IR.tStatSpan stat) $ case stat of
  IR.Bind m n t -> do
    eid <- gets sEnv
    case m of
      Imm -> void $ bindImm n t
      _ -> do
        -- thunk замкнут на окружение ДО привязки: привязки не рекурсивны
        a <- alloc $ VThunk t eid
        when (m == Var) $ logEvent EvCreate
        void $ extendEnv n m a
  IR.Rebind n path t -> case path of
    [] -> do
      env <- gets sEnv
      m <- lookupMut env n
      case m of
        Var -> void $ rebind n t
        _ -> rtError $ T.concat [
            "cannot assign to `", n, "`: it is bound with `", pretty m, "`"
          ]
    _ -> void $ rebindPath n path t
  IR.Expr t -> do
    -- модель (S-Expr): оператор-выражение вычисляется до слабой головной нормальной формы;
    -- иначе эффекты в отложенных ветках if и в скобках (...) никогда не выполнятся
    a <- evalExpr t pure
    void $ whnfAddr a

-- | Поиск привязки без ошибки (по цепочке родителей)
findBindingMaybe :: EnvId -> Text -> Interp (Maybe (Mutability, Address))
findBindingMaybe eid0 name = go Set.empty eid0
  where
    go visited eid
      | Set.member eid visited = pure Nothing
      | otherwise = do
          env <- getEnv eid
          case Map.lookup name env.bindings of
            Just ma -> pure (Just ma)
            Nothing -> maybe (pure Nothing) (go (Set.insert eid visited)) env.parent

-- | Корневое (глобальное) окружение: функции верхнего уровня и встроенные операции
rootEnvOf :: EnvId -> Interp EnvId
rootEnvOf eid = do
  env <- getEnv eid
  maybe (pure eid) rootEnvOf env.parent

-- | Окружение снимка (модель: snapshot): свободные переменные ищутся по всей цепочке
--  окружений, каждая привязка заменяется замороженной копией ячейки; живого родителя нет,
--  кроме глобального окружения.
snapshotEnv :: EnvId -> Set Text -> Interp EnvId
snapshotEnv scope names = do
  root <- rootEnvOf scope
  env <- newEnv Env {
    bindings = Map.empty,
    parent = Just root
  }
  forM_ (Set.toList names) $ \name -> do
    found <- findBindingMaybe scope name
    case found of
      -- имя связано внутри самого выражения
      Nothing -> pure ()
      Just (m, addr) -> do
        when (m == Var) $ logEvent EvSnapRead
        addr' <- freezeCell addr
        void $ modifyEnv env $ \env' -> env' {
          bindings = Map.insert name (freezeMutability m, addr') env'.bindings
        }
  pure env

-- | Свободные переменные кода замыкания
codeFreeVars :: Code -> Set Text
codeFreeVars = \case
  CodeLam lam -> Set.delete lam.lArg (freeVarsBlock lam.lBlock)
  CodeFun _ _ args block -> foldr Set.delete (freeVarsBlock block) args
  -- A native function's code is Haskell, not a block: it closes over nothing
  -- the snapshot has to rewrite.
  CodeNative _ _ -> Set.empty

-- | Переписанный код и функция, собранная из него в окружении env'
freezeCode :: EnvId -> Code -> Interp (Code, Address -> Interp Address)
freezeCode env' = \case
  CodeLam lam -> do
    let lam' = freezeLambda lam
    fn <- evalLambda env' lam'
    pure (CodeLam lam', fn)
  CodeFun stage name args block -> do
    let block' = freezeBlock block
    fn <- makeClosureChain env' name args block'
    pure (CodeFun stage name args block', fn)
  CodeNative _ name -> do
    -- Unreachable: 'freezeCell' keeps a native function as the atom it is,
    -- because it captures no bindings for a snapshot to copy.
    rtError $ "internal error: a snapshot tried to copy the native function `" <> name <> "`"

-- | Замороженная копия ячейки (модель: freezeV). Копирование транзитивно: данные,
--  thunk'и и код замыканий, достижимые по свободным переменным. Общая таблица
--  sFreezeMemo сохраняет разделение и обрывает циклы (рекурсия функций).
freezeCell :: Address -> Interp Address
freezeCell a = do
  memo <- gets sFreezeMemo
  case IM.lookup (addrId a) memo of
    Just a' -> pure a'
    Nothing -> do
      v <- readCell a
      case v of
        VClosure env cache code _ -> do
          conts <- gets sContAddrs
          when (Set.member (addrId a) conts) $
            rtError "a snapshot cannot capture `resume`: a handler continuation is one-shot and cannot be frozen"
          case code of
            -- A closure without recorded code is a builtin or an effect
            -- operation.  Such closures are stateless atoms: the operation
            -- names its effect in its captured Haskell function, and the
            -- interpreter never reads the bindings of their env to apply them.
            Nothing -> share a
            -- A native function is an atom for the same reason: its code is
            -- Haskell and it captures no bindings, so a snapshot can keep the
            -- very value instead of rebuilding it.
            Just (CodeNative _ _) -> share a
            Just code0 -> do
              a' <- placeholder
              env' <- snapshotEnv env (codeFreeVars code0)
              (code', fn') <- freezeCode env' code0
              setCell a' (VClosure env' (fmap (const IM.empty) cache) (Just code') fn')
              pure a'
        VThunk expr env -> do
          a' <- placeholder
          env' <- snapshotEnv env (freeVars expr)
          setCell a' (VThunk (freeze expr) env')
          pure a'
        VArray as -> do
          a' <- placeholder
          as' <- mapM freezeCell as
          setCell a' (VArray as')
          pure a'
        VPair l r -> do
          a' <- placeholder
          l' <- freezeCell l
          r' <- freezeCell r
          setCell a' (VPair l' r')
          pure a'
        VRecord eid -> do
          a' <- placeholder
          env <- getEnv eid
          bs <- forM (Map.toList env.bindings) $ \(n, (m, x)) -> do
            when (m == Var) $ logEvent EvSnapRead
            x' <- freezeCell x
            pure (n, (freezeMutability m, x'))
          eid' <- newEnv Env {bindings = Map.fromList bs, parent = Nothing}
          setCell a' (VRecord eid')
          pure a'
        VEnum n fs -> do
          a' <- placeholder
          fs' <- forM fs $ \(m, x) -> do
            when (m == Var) $ logEvent EvSnapRead
            x' <- freezeCell x
            pure (freezeMutability m, x')
          setCell a' (VEnum n fs')
          pure a'
        _ -> share a
  where
    remember x y = modify $ \s -> s {sFreezeMemo = IM.insert (addrId x) y s.sFreezeMemo}
    share x = remember x x >> pure x
    placeholder = do
      a' <- freshCell VBottom
      remember a a'
      pure a'
    setCell x val = writeCell x val

-- | Модель (S-Rebind): привязка перенаправляется в том окружении, где она
--  объявлена, на новую ленивую ячейку; правая часть видит старую привязку.
rebind :: Text -> TypedExpr -> Interp Address
rebind x t = do
  e <- gets sEnv
  (ex, m, addr) <- findBindingEnv e x
  case m of
    Var -> do
      rhsEnv <- newEnv Env {
        bindings = Map.singleton x (Var, addr),
        parent = Just e
      }
      addr' <- alloc $ VThunk t rhsEnv
      _ <- modifyEnv ex $ \env -> env {bindings = Map.insert x (Var, addr') env.bindings}
      logEvent EvRebind
      pure addr'
    _ -> rtError $ T.concat [
        "cannot assign to `", x, "`: it is bound with `", pretty m, "`"
      ]

-- | @r@a := t@ and @r@a@b := t@.
--
--   The right-hand side is delayed, as it is for a plain rebinding, and it sees
--   the value the assigned field had before the write.  A field is not a
--   binding of the current environment, so the old state is presented to the
--   right-hand side as a shallow copy of every record along the path: the copy
--   keeps the fields as they are now, and the assigned field of the innermost
--   copy is the cell that is about to be replaced.  A write to any field of
--   these records from inside the right-hand side lands in the copy and is not
--   visible afterwards; that is the price of reading the old state without a
--   snapshot of the whole store.
rebindPath :: Text -> [Text] -> TypedExpr -> Interp Address
rebindPath name names t = do
  e <- gets sEnv
  (_, m, addr) <- findBindingEnv e name
  -- The name is read to reach the record, so a `var` one costs `Read`; the
  -- assigned field is not read, just as `x := e` does not read `x`.
  when (m == Var) $ logEvent EvRead
  levels <- walk addr names
  -- The copies are built from the inside out: the innermost copy keeps its
  -- bindings, so the right-hand side reads the assigned field's old value, and
  -- every outer copy points its own path field at the copy below it.
  outerAddr <- buildCopies Nothing (reverse levels)
  rhsEnv <- newEnv Env {
    bindings = Map.singleton name (m, outerAddr),
    parent = Just e
  }
  let (targetEnv, targetField, _, _) = head (reverse levels)
  addr' <- alloc $ VThunk t rhsEnv
  _ <- modifyEnv targetEnv $ \env ->
    env {bindings = Map.insert targetField (Var, addr') env.bindings}
  logEvent EvRebind
  pure addr'
  where
    lhs = T.concat [name, T.concat (map (T.append "@") names)]

    -- Every record along the path, from the outermost to the innermost, with
    -- the field the path takes, that field's mutability and the cell it
    -- currently holds.
    walk :: Address -> [Text] -> Interp [(EnvId, Text, Mutability, Address)]
    walk recAddr path = case path of
      [] -> rtError $ "internal error: an empty assignment path at `" <> lhs <> "`"
      (field : rest) -> do
        recAddr' <- whnf recAddr
        v <- readCell recAddr'
        case v of
          VRecord eid -> do
            env <- getEnv eid
            case getCell env field of
              Nothing -> rtError $ T.concat [
                  "the record at `", name, "` has no field `", field,
                  "`, so `", lhs, "` cannot be assigned"
                ]
              Just (fm, fa) -> case rest of
                [] -> pure [(eid, field, fm, fa)]
                _ -> do
                  when (fm == Var) $ logEvent EvRead
                  ((eid, field, fm, fa) :) <$> walk fa rest
          other -> rtError $ T.concat [
              "cannot assign to `", lhs, "`: ",
              describe other, " is not a record, so it has no field `", field, "`"
            ]

    -- Shallow copies, innermost first, each one's path field pointing at the
    -- copy below it.  Returns the address of the outermost copy.
    buildCopies :: Maybe Address -> [(EnvId, Text, Mutability, Address)] -> Interp Address
    buildCopies _ [] = rtError "internal error: an assignment path is empty"
    buildCopies inner ((eid, field, fm, _) : rest) = do
      env <- getEnv eid
      let bindings' = case inner of
            -- The innermost copy is not rewritten: its assigned field is the
            -- old cell the right-hand side must see.
            Nothing -> env.bindings
            Just a -> Map.insert field (fm, a) env.bindings
      eid' <- newEnv Env {bindings = bindings', parent = Nothing}
      addr' <- alloc (VRecord eid')
      case rest of
        [] -> pure addr'
        _ -> buildCopies (Just addr') rest

-- | Трассировка вычислений: включается переменной окружения MARRAN_TRACE
traceEval :: String -> Interp ()
traceEval msg = do
  on <- gets sTrace
  when on $ liftIO $ putStrLn msg

-- | Запись события мутации (счётчики по видам событий)
logEvent :: Event -> Interp ()
logEvent ev = modify $ \s -> s {sEvents = Map.insertWith (+) ev 1 s.sEvents}

-- | Проверка теоремы об эффектах на выполнении: каждое событие мутации должно быть разрешено
--   объявленным рядом main. Включается переменной MARRAN_CHECK_EVENTS. Открытый ряд не проверяется.
reportEvents :: Maybe EffRow -> Interp ()
reportEvents declared = do
  chk <- liftIO $ isJust <$> lookupEnv "MARRAN_CHECK_EVENTS"
  when chk $ do
    evs <- gets sEvents
    let count e = Map.findWithDefault 0 e evs
        reads' = count EvRead + count EvSnapRead
    liftIO $ putStrLn $ concat [
        "EVENTS: read=", show (count EvRead),
        " snapshot-read=", show (count EvSnapRead),
        " rebind=", show (count EvRebind),
        " create=", show (count EvCreate)
      ]
    case declared of
      Just (RClosed cs) -> do
        let has n = EffCons (Eff.elabel n) `elem` cs
            bad = [ "Read" | reads' > 0, not (has "Read") ]
              <> [ "Rebind" | count EvRebind > 0, not (has "Rebind") ]
              <> [ "Var/Cell" | count EvCreate > 0, not (has "Var" || has "Cell") ]
        liftIO $ putStrLn $
          if null bad then "EVENTS: licensed"
          else "EVENT-VIOLATION: not in the declared row: " <> intercalate ", " bad
      _ -> liftIO $ putStrLn "EVENTS: declared row is open or missing, not checked"

alloc :: Value -> Interp Address
alloc = freshCell

bindVal :: Text -> Value -> Interp Address
bindVal x v = do
  eid <- gets sEnv
  bindValIn eid x v

bindValIn :: EnvId -> Text -> Value -> Interp Address
bindValIn e x v = bindValAddrIn e x =<< alloc v

bindValAddrIn :: EnvId -> Text -> Address -> Interp Address
bindValAddrIn e x a = do
  _ <- modifyEnv e $ \env ->
    env {bindings = Map.insert x (Val, a) env.bindings}
  pure a

bindVarIn :: EnvId -> Text -> Value -> Interp Address
bindVarIn e x v = bindVarAddrIn e x =<< alloc v

bindVarAddrIn :: EnvId -> Text -> Address -> Interp Address
bindVarAddrIn e x a = do
  _ <- modifyEnv e $ \env ->
    env {bindings = Map.insert x (Var, a) env.bindings}
  pure a

bindImm :: Text -> TypedExpr -> Interp Address
bindImm name expr = do
  st <- get
  -- общая таблица копий на один снимок: сохраняет разделение и обрывает циклы (рекурсивные функции)
  saved <- gets sFreezeMemo
  modify $ \s -> s {sFreezeMemo = IM.empty}
  frozenEnv <- snapshotEnv st.sEnv (freeVars expr)
  modify $ \s -> s {sFreezeMemo = saved}
  addr <- alloc $ VThunk expr frozenEnv
  _ <- extendEnv name Imm addr
  pure addr

lookupCell :: EnvId -> Text -> Interp (Mutability, Address)
lookupCell eid name = do
  (_, m, a) <- findBindingEnv eid name
  pure (m, a)

lookupRef :: EnvId -> Text -> Interp Address
lookupRef eid name = do
  (_, _, a) <- findBindingEnv eid name
  pure a

lookupMut :: EnvId -> Text -> Interp Mutability
lookupMut e name = do
  (_, m, _) <- findBindingEnv e name
  pure m

freeVars :: TypedExpr -> Set Text
freeVars = \case
  TEXVar n _ -> Set.singleton n
  TEArray _ _ es -> Set.unions (map freeVars es)
  TEPair _ l r -> Set.union (freeVars l) (freeVars r)
  TEXLambda lam ->
    let bodyFV = freeVarsBlock lam.lBlock
    in Set.delete lam.lArg bodyFV  -- аргумент связан
  TEApply f x -> Set.union (freeVars f) (freeVars x)
  TERecord _ props _ -> Set.unions [freeVars (terExpr p) | p <- props]
  TEHandle handler _ -> freeVarsHandler handler
  TEParen b -> freeVarsBlock b
  -- `resume` is syntax, not an ordinary name, but the continuation it denotes
  -- is a value in the clause environment: a snapshot that reaches it must see
  -- the name and refuse to freeze the continuation.
  TEResume e _ -> Set.insert "resume" (freeVars e)
  TELet pat bound body ->
    let boundFV = freeVars bound
        bodyFV = freeVars body
        -- удаляем имена, связанные в паттерне
        patternVars = letPatternVars pat
    in Set.union boundFV (Set.difference bodyFV patternVars)
  TEPropAccess e _ -> freeVars e
  TEIfElse p t f -> Set.unions [freeVars p, freeVars t, freeVars f]
  TEAnnot e _ -> freeVars e
  TEMatch e _ cs ->
    Set.unions $ freeVars e : map clauseVars cs
  _ -> Set.empty
  where
    clauseVars (TMatchClause ps g b) =
      Set.unions $
        map patternVars ps
          <> maybe [] (pure . freeVars) g
          <> [freeVarsBlock b]

    patternVars (MkTPattern _ node) = case node of
      TPValue e -> freeVars e
      TPArray ps t -> Set.unions (map patternVars ps <> maybe [] (pure . patternVars) t)
      TPTuple ps -> Set.unions (map patternVars ps)
      TPCon _ ps -> Set.unions (map patternVars ps)
      TPAs p _ _ -> patternVars p
      TPCast p _ -> patternVars p
      TPStarts l r -> Set.union (patternVars l) (patternVars r)
      TPEnds l r -> Set.union (patternVars l) (patternVars r)
      _ -> Set.empty

-- | Свободные переменные блока: имена, связанные его операторами, исключаются
--  (привязки последовательны и не рекурсивны).
freeVarsBlock :: IR.Block -> Set.Set Text
freeVarsBlock (stats, expr) = go Set.empty stats
  where
    go bound [] = Set.difference (freeVars expr) bound
    go bound (s : ss) =
      let (fvS, bound') = statFree bound s
      in Set.union fvS (go bound' ss)
    statFree bound = \case
      IR.Bind _ n e -> (Set.difference (freeVars e) bound, Set.insert n bound)
      IR.Rebind n _ e -> (Set.difference (Set.insert n (freeVars e)) bound, bound)
      IR.Expr e -> (Set.difference (freeVars e) bound, bound)

freeVarsStat :: IR.Stat -> Set.Set Text
freeVarsStat = \case
  IR.Bind _ _ e -> freeVars e
  IR.Rebind _ _ e -> freeVars e
  IR.Expr e -> freeVars e

freeVarsHandler :: IR.Handler -> Set.Set Text
freeVarsHandler = \case
  IR.Handler _ block clauses thenLam ->
    Set.unions $ [freeVarsBlock block]
    <> map (\(_, l, _, _) -> freeVarsLambda l) clauses
    <> [freeVarsLambda thenLam]

freeVarsLambda :: IR.Lambda -> Set.Set Text
freeVarsLambda lam = freeVarsBlock lam.lBlock

letPatternVars :: LetPattern -> Set.Set Text
letPatternVars = \case
  LPATom alp -> atomLetPatternVars alp
  LPParam (LambdaParam n _) -> Set.singleton n

atomLetPatternVars :: AtomLetPattern -> Set.Set Text
atomLetPatternVars = \case
  ALPPair l r -> Set.union (letPatternVars l) (letPatternVars r)
  ALPRecord props -> Set.unions [maybe Set.empty atomLetPatternVars alp | LetPatternRecordProp _ _ alp <- props]
  _ -> Set.empty

-- | Does matching this pattern need the value of the right-hand side?
--
--   A pair and a record pattern destructure, so the address must be forced to
--   weak head normal form first.  A name, `_` and the nil literal bind the
--   address as it is, which keeps @let x = e@ non-strict.
needsValue :: LetPattern -> Bool
needsValue = \case
  LPParam _ -> False
  LPATom a -> case a of
    ALPPair {} -> True
    ALPRecord {} -> True
    ALPNil -> False
    ALPUnderscore -> False

-- | A constructor of a declared enumeration, as a curried function.
--
--   `Some 5` is an ordinary application: the checker binds every constructor
--   as a function in the program's scope, and the interpreter builds the value
--   the same way.  A `var` field is a cell the constructor creates, so the
--   mutability travels with the field and reading it later costs `Read`,
--   exactly as a `var` field of a record does.
makeConstructor :: EnvId -> Text -> [Mutability] -> Interp Address
makeConstructor env name muts = go muts []
  where
    go [] acc = alloc $ VEnum name (reverse acc)
    go (m : rest) acc =
      alloc $ VClosure env Nothing
        (Just (CodeNative (if null acc then Whole else Partial) name)) $ \arg ->
          go rest ((m, arg) : acc)

-- | Decide whether a value is the one a pattern accepts, and return the names
--   the pattern binds.
--
--   The pattern inspects the subject, so it forces what it has to look at; a
--   name, `_` and an alias of them bind the address as it is, which keeps the
--   components of a matched value as lazy as the value itself.
matchTPattern :: TPattern -> Address -> Interp (Maybe [(Text, Address)])
matchTPattern (MkTPattern _ node) addr = go node
  where
    go = \case
      TPWildcard -> pure $ Just []
      TPName n _ -> pure $ Just [(n, addr)]
      TPInt i -> literal $ \case VInt i' -> i == i'; _ -> False
      TPFloat f -> literal $ \case VFloat f' -> f == f'; _ -> False
      TPString s -> literal $ \case VString s' -> s == s'; _ -> False
      TPBoolean b -> literal $ \case VBoolean b' -> b == b'; _ -> False
      TPNil -> literal $ \case VNil -> True; _ -> False
      -- @val x@: the value must equal the one the path holds, compared with
      -- `==`, so two records with the same fields are the same value here.
      TPValue e -> do
        other <- evalExpr e pure
        equal <- equalValues Set.empty addr other
        pure $ if equal then Just [] else Nothing
      -- @[a b]@ is exactly two elements, @[a; rest]@ is a head and a tail and
      -- @[a b; rest]@ is at least two; the parser records which was written.
      TPArray ps tailP -> do
        v <- readCell =<< whnf addr
        case v of
          VArray xs -> case tailP of
            Nothing
              | length ps /= length xs -> pure Nothing
              | otherwise -> allBinds [matchTPattern p x | (p, x) <- zip ps xs]
            Just tailPat
              | length xs < length ps -> pure Nothing
              | otherwise -> do
                  headsB <- allBinds [matchTPattern p x | (p, x) <- zip ps xs]
                  case headsB of
                    Nothing -> pure Nothing
                    Just bs -> do
                      rest <- alloc $ VArray (drop (length ps) xs)
                      tailB <- matchTPattern tailPat rest
                      pure $ (bs <>) <$> tailB
          _ -> pure Nothing
      TPTuple [l, r] -> do
        v <- readCell =<< whnf addr
        case v of
          VPair addrL addrR -> do
            lb <- matchTPattern l addrL
            rb <- matchTPattern r addrR
            pure $ (<>) <$> lb <*> rb
          _ -> pure Nothing
      TPTuple _ -> pure Nothing
      TPCon n ps -> do
        v <- readCell =<< whnf addr
        case v of
          VEnum n' fs
            | n == n' && length ps == length fs ->
                allBinds
                  [ do
                      -- A `var` field is a cell: looking inside it is a read.
                      when (m == Var && touches p) $ logEvent EvRead
                      matchTPattern p x
                  | (p, (m, x)) <- zip ps fs
                  ]
          _ -> pure Nothing
      TPAs p n _ -> do
        bs <- matchTPattern p addr
        pure $ (\bs' -> bs' <> [(n, addr)]) <$> bs
      TPCast p _ -> matchTPattern p addr
      -- @front |-> rest@: the value starts with @front@ and @rest@ is the
      -- remainder.  The split is the first one that satisfies both patterns,
      -- which for a literal prefix is the only one there is.
      TPStarts l r -> do
        v <- readCell =<< whnf addr
        case v of
          VString s -> firstMatch
            [ do
                prefix <- alloc $ VString (T.take k s)
                suffix <- alloc $ VString (T.drop k s)
                lb <- matchTPattern l prefix
                rb <- matchTPattern r suffix
                pure $ (<>) <$> lb <*> rb
            | k <- [0 .. T.length s]
            ]
          _ -> pure Nothing
      -- @rest <-| back@: the value ends with @back@ and @rest@ is what comes
      -- before it.
      TPEnds l r -> do
        v <- readCell =<< whnf addr
        case v of
          VString s -> firstMatch
            [ do
                rest <- alloc $ VString (T.take (T.length s - k) s)
                back <- alloc $ VString (T.drop (T.length s - k) s)
                lb <- matchTPattern l rest
                rb <- matchTPattern r back
                pure $ (<>) <$> lb <*> rb
            | k <- [0 .. T.length s]
            ]
          _ -> pure Nothing

    literal accepts = do
      v <- forceValue addr
      pure $ if accepts v then Just [] else Nothing

    -- Every sub-pattern has to accept the component it is given; one refusal
    -- refuses the whole pattern.
    allBinds [] = pure $ Just []
    allBinds (attempt : attempts) = attempt >>= \case
      Nothing -> pure Nothing
      Just bs -> fmap (bs <>) <$> allBinds attempts

    firstMatch [] = pure Nothing
    firstMatch (attempt : attempts) = attempt >>= \case
      Just bs -> pure (Just bs)
      Nothing -> firstMatch attempts

-- | Structural equality of two values: what `==` prints as one value.
--
--   The set of pairs already being compared breaks cycles, so a record that
--   contains itself is equal to a copy of itself rather than a loop.
equalValues :: Set (Int, Int) -> Address -> Address -> Interp Bool
equalValues seen a b
  | addrId a == addrId b = pure True
  | Set.member (addrId a, addrId b) seen = pure True
  | otherwise = do
      va <- forceValue a
      vb <- forceValue b
      let seen' = Set.insert (addrId a, addrId b) seen
      case (va, vb) of
        (VInt x, VInt y) -> pure $ x == y
        (VFloat x, VFloat y) -> pure $ x == y
        (VBoolean x, VBoolean y) -> pure $ x == y
        (VString x, VString y) -> pure $ x == y
        (VNil, VNil) -> pure True
        (VArray xs, VArray ys)
          | length xs == length ys -> and <$> zipWithM (equalValues seen') xs ys
          | otherwise -> pure False
        (VPair l1 r1, VPair l2 r2) ->
          (&&) <$> equalValues seen' l1 l2 <*> equalValues seen' r1 r2
        -- An enum is equal when it is the same case with equal fields; the
        -- mutability of a field is how it is reached, not what it holds.
        (VEnum n1 fs1, VEnum n2 fs2)
          | n1 == n2 && length fs1 == length fs2 ->
              and <$> zipWithM (\(_, x) (_, y) -> equalValues seen' x y) fs1 fs2
          | otherwise -> pure False
        (VRecord e1, VRecord e2) -> do
          env1 <- getEnv e1
          env2 <- getEnv e2
          let keys1 = Map.keys env1.bindings
              keys2 = Map.keys env2.bindings
          if keys1 /= keys2
            then pure False
            else and <$> forM keys1 (\k -> case (getRef env1 k, getRef env2 k) of
                    (Just x, Just y) -> equalValues seen' x y
                    _ -> pure False)
        -- Two functions are the same value only when they are the same cell,
        -- which the check above already settled.
        _ -> pure False

matchPattern :: LetPattern -> Address -> Interp [(Text, Mutability, Address)]
matchPattern pat addr = do
  v <- readCell addr
  case pat of
    LPATom (ALPUnderscore; ALPNil) -> pure []
    LPATom (ALPPair l r) -> case v of
      VPair addrL addrR -> do
        -- A component is a cell of its own and may still be a thunk.  It is
        -- forced only when the nested pattern has to inspect it, so
        -- `let (a, b) = p` with two names stays as lazy as `let a = ...`.
        bindL <- matchPattern l =<< valueIfNeeded l addrL
        bindR <- matchPattern r =<< valueIfNeeded r addrR
        pure (bindL <> bindR)
      _ -> rtError $ "this pattern expects a pair, but the value is " <> describe v
    LPATom (ALPRecord props) -> case v of
      VRecord eid -> do
        env <- getEnv eid
        foldM (\acc (LetPatternRecordProp m (LambdaParam n _) mPat) -> do
            case getRef env n of
              Just fieldAddr -> do
                case mPat of
                  Nothing -> pure $ (n, m, fieldAddr) : acc
                  Just subPat -> do
                    let nested = LPATom subPat
                    subBindings <- matchPattern nested =<< valueIfNeeded nested fieldAddr
                    pure $ acc <> subBindings
              Nothing -> rtError $ "this pattern names the field `" <> n <> "`, which the record does not have"
          ) [] props
      _ -> rtError $ "this pattern expects a record, but the value is " <> describe v
    LPParam (LambdaParam n _) -> pure [(n, Val, addr)]

-- | Force a cell only if the pattern about to match it destructures.
valueIfNeeded :: LetPattern -> Address -> Interp Address
valueIfNeeded pat addr = if needsValue pat then whnf addr else pure addr

isImmutableValue :: Value -> Interp Bool
isImmutableValue v = evalStateT (go v) IntMap.empty
  where
    go = \case
      VArray addrs -> foldM (\acc a -> (acc &&) <$> checkAddr a ) True addrs
      VPair l r -> (&&) <$> checkAddr l <*> checkAddr r
      VEnum _ fs -> foldM (\acc (m, a) ->
        if m == Var then pure False else (acc &&) <$> checkAddr a) True fs
      VRecord eid -> do
        env <- lift $ getEnv eid
        foldM
          (\acc (mut, addr) ->
            -- `Var` is checked first: a `Var` field is not frozen
            -- even if its target is an ancestor (a cycle).
            if mut == Var
            then pure False
            else (acc &&) <$> checkAddr addr)
          True
          $ Map.elems env.bindings

      VBottom; VThunk{} -> pure False
      _ -> pure True

    checkAddr a = do
      memo <- get
      case IM.lookup (addrId a) memo of
        Just b -> pure b
        Nothing -> do
          -- Coinductive assumption: a cycle re-entering this cell sees `True`.
          put (IM.insert (addrId a) True memo)
          v' <- lift $ readCell a
          result <- go v'
          modify' (IM.insert (addrId a) result)
          pure result


isPureClosure :: EffRow -> Bool
isPureClosure (RClosed []) = True
isPureClosure (ROpen [] _) = True  -- открытый ряд без эффектов
isPureClosure _ = False

initialInterpState :: EnvId -> InterpState
initialInterpState root = InterpState {
  sEnv        = root,
  sKstack     = globalHandlers,
  sNextAddr   = 0,
  sNextEnv    = 1,
  sNextCont   = 0,
  sUsedConts  = Set.empty,
  sContAddrs  = Set.empty,
  sNextHandler = 0,
  sFreezeMemo = IM.empty,
  sTrace      = False,
  sEvents     = Map.empty,
  sNoMemo     = False,
  sForcing    = Set.empty,
  sSpan       = noSpan,
  sCmdArgs    = []
}

prepareSnapshotBenchmark :: Int -> [(Int, Int)] -> IO (IO (Int, Int, Int))
prepareSnapshotBenchmark rootNode graphEdges = do
  when (rootNode < 0) $
    ioError $ userError "Snapshot graph: negative root node"

  when (any (\(from, to) -> from < 0 || to < 0) graphEdges) $
    ioError $ userError "Snapshot graph: negative node index"

  let allNodes = rootNode : concatMap (\(from, to) -> [from, to]) graphEdges
      nodeCount = maximum allNodes + 1
      adjacency = Map.fromListWith (<>) [(from, [to]) | (from, to) <- graphEdges]

  -- Build the graph exactly once.  Building it cannot legitimately fail, so a
  -- runtime error here is a bug in the interpreter and is raised as an
  -- exception rather than turned into a benchmark result.
  rootRef <- newIORef (Env Map.empty Nothing)
  let root = EnvId {envId = 0, envCell = rootRef}
  (built, initialState) <-
    runInterp
      (do
        modify $ \st -> st {sEnv = root}

        -- Allocate all vertices before connecting them.
        -- This allows arbitrary sharing and forward references.
        addresses <- mapM (const $ alloc VBottom) [0 .. nodeCount - 1]
        let addressMap = Map.fromList (zip [0 ..] addresses)

        -- Fill every vertex with its outgoing references.
        forM_ [0 .. nodeCount - 1] $ \node -> do
          let children = Map.findWithDefault [] node adjacency
              childAddresses = map (addressMap Map.!) children
              nodeAddress = addressMap Map.! node
          writeCell nodeAddress (VArray childAddresses)

        -- Expose the selected root through the root environment.
        let rootAddress = addressMap Map.! rootNode
        _ <- modifyEnv root $ \env -> env {
          bindings = Map.insert "root" (Val, rootAddress) env.bindings
        }
        pure VNil
      )
      (initialInterpState root)

  case built of
    Left err -> ioError $ userError $ T.unpack $ "Snapshot graph: " <> pretty err
    Right _ -> pure ()

  let rootEnv = initialState.sEnv
      initialAddr = initialState.sNextAddr
      initialEnv = initialState.sNextEnv

  -- This action always starts from the same pristine state.
  let runSnapshot = do
        (res, finalState) <-
          runInterp (snapshotEnv rootEnv (Set.singleton "root") >> pure VNil) initialState

        case res of
          Left err -> ioError $ userError $ T.unpack $ "Snapshot traversal: " <> pretty err
          Right _ -> pure ()

        let visited = IM.size finalState.sFreezeMemo
            allocated = finalState.sNextAddr - initialAddr
            allocatedEnvs = finalState.sNextEnv - initialEnv

        -- Force all statistics before returning.
        _ <- evaluate (visited + allocated + allocatedEnvs)

        pure (visited, allocated, allocatedEnvs)

  pure runSnapshot