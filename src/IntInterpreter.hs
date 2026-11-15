{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}

module IntInterpreter (interpret, prepareSnapshotBenchmark, InterpError(..), errorCodeOf, heapError) where

import qualified TypedIR as IR
import Types (
    Mutability(..),
    ECons(..),
    EffCons(..),
    LetPattern(..),
    AtomLetPattern(..),
    LetPatternRecordProp(..),
    LambdaParam(..), EffRow (..)
  )
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Scientific (Scientific, fromFloatDigits, normalize, scientific)
import Control.Monad.Cont (ContT(..), callCC)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Span (Span, noSpan)
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
    Lambda(..), Block, TERecordProp(..))
import Control.Monad.State.Strict
import Control.Monad (foldM, forM, forM_, void, unless, when)
import Infer (freezeMutability, freeze, freezeBlock, freezeLambda)
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
import Data.Maybe (isJust)
import System.Environment (lookupEnv)
import Control.Exception (AsyncException (..), evaluate, fromException, throwIO, try)
import System.IO.Error (isEOFError)
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
    VClosure eid _ _ _ -> "!closure[" <> T.unpack (pretty eid) <> "]!"
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
    VClosure eid _ _ _ -> "!closure[" <> pretty eid <> "]!"
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
    VClosure eid _ _ _ -> pure $ "!closure[" <> pretty eid <> "]!"
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
          a <- alloc (VClosure env Nothing Nothing clos)
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
data Code
  = CodeLam IR.Lambda
  | CodeFun [Text] IR.Block

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
  , sSpan       :: Span                  -- ^ where the interpreter currently is
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
  result <- try $ fst <$> runInterp (do
    modify $ \st -> st {sEnv = root}
    _ <- buildInitialEnv cmdArgs
    evalChunk chunk
    ) (initialInterpState root)
  case result of
    Right ok -> pure ok
    Left e -> case fromException e of
      Just async | async == HeapOverflow || async == StackOverflow ->
        pure (Left (heapError (mainSpan chunk) async))
      _ -> throwIO e

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

-- | The block of @main@, used as the position of a failure that is not tied to
--   a particular node, such as exhaustion of memory.
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
      ("trace", Op 1 $ \case
        [addrArg] -> \_ -> do
          v <- readCell addrArg
          liftIO $ putStrLn $ T.unpack $ pretty v
          pure addrArg
        args -> \_ -> arityError "trace" 1 args)
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
        input <- readInputLine "read_string"
        case Parser.parseFromText Parser.stringLiteral input of
          Left _ -> rtError $ "`read_string` could not parse the line " <> quoted input
          Right s -> alloc $ VString s),
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
--   The arithmetic and the strings of @app/std.marr@ live here as native
--   closures.  Each one forces exactly the arguments whose values it needs:
--   a language whose arguments are delayed must not force a `spin` that its
--   result never mentions, so `||` and `&&` stop at the first deciding
--   argument and every other operation forces only what it reads.
buildInitialEnv :: [String] -> Interp EnvId
buildInitialEnv cmdArgs = do
  -- замыкания операций строятся из той же таблицы, что и клаузы (арность не дублируется)
  let allocEffectCall eff (op, o) = do
        env <- gets sEnv
        clos <- makeEffectClosure env o.opArity eff op
        addr <- alloc $ VClosure env Nothing Nothing clos
        pure (op, (Val, addr))
  opBindings <- fmap concat $ forM globalOps $ \(eff, ops) -> mapM (allocEffectCall eff) ops
  let operations = Map.fromList opBindings
  st <- get

  let emptyCache = Just (IM.empty :: IntMap Address)

      -- Build a curried native function of a given arity.  The closures of the
      -- partially applied stages are allocated on every call, as they were
      -- when each operation was written out by hand.
      nativeN :: Int -> ([Address] -> Interp Address) -> Interp Address
      nativeN n body = go [] n
        where
          go acc 0 = body (reverse acc)
          go acc k = alloc $ VClosure st.sEnv emptyCache Nothing $ \arg ->
            go (arg : acc) (k - 1)

      native1 f = nativeN 1 $ \case [a] -> f a; _ -> arityError "<native>" 1 []
      native2 f = nativeN 2 $ \case [a, b] -> f a b; _ -> arityError "<native>" 2 []

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
      intOp name f = native2 $ \a b ->
        withInt name a $ \x -> withInt name b $ \y -> alloc $ VInt (f x y)

      intCmp :: Text -> (Integer -> Integer -> Bool) -> Interp Address
      intCmp name f = native2 $ \a b ->
        withInt name a $ \x -> withInt name b $ \y -> alloc $ VBoolean (f x y)

      intFun :: Text -> (Integer -> Integer) -> Interp Address
      intFun name f = native1 $ \a ->
        withInt name a $ \x -> alloc $ VInt (f x)

      floatOp :: Text -> (Scientific -> Scientific -> Scientific) -> Interp Address
      floatOp name f = native2 $ \a b ->
        withFloat name a $ \x -> withFloat name b $ \y -> alloc $ VFloat (f x y)

      floatCmp :: Text -> (Scientific -> Scientific -> Bool) -> Interp Address
      floatCmp name f = native2 $ \a b ->
        withFloat name a $ \x -> withFloat name b $ \y -> alloc $ VBoolean (f x y)

      floatFun :: Text -> (Scientific -> Scientific) -> Interp Address
      floatFun name f = native1 $ \a ->
        withFloat name a $ \x -> alloc $ VFloat (f x)

      boolOp :: Text -> (Bool -> Bool -> Bool) -> Interp Address
      boolOp name f = native2 $ \a b ->
        withBool name a $ \x -> withBool name b $ \y -> alloc $ VBoolean (f x y)

      -- Short-circuiting boolean connectives: the second argument is only
      -- forced when the first one does not decide the result.
      shortCircuit :: Text -> Bool -> Interp Address
      shortCircuit name stopOn = native2 $ \a b ->
        withBool name a $ \x ->
          if x == stopOn
            then alloc $ VBoolean stopOn
            else withBool name b (alloc . VBoolean)

      string2 :: Text -> (Text -> Text -> Text) -> Interp Address
      string2 name f = native2 $ \a b ->
        withString name a $ \x -> withString name b $ \y -> alloc $ VString (f x y)

      stringFun :: Text -> (Text -> Text) -> Interp Address
      stringFun name f = native1 $ \a ->
        withString name a $ \x -> alloc $ VString (f x)

  -- Integers.  `/` and `%` report a zero divisor through the effect `Error`,
  -- so a program can catch it (`under Error to ... handle | error e => ...`)
  -- or let it reach the bottom handler, which reports it as a diagnostic.
  plusAddr <- intOp "+" (+)
  minusAddr <- intOp "-" (-)
  timesAddr <- intOp "*" (*)
  divAddr <- native2 $ \a b ->
    withInt "/" a $ \x -> withInt "/" b $ \y ->
      if y == 0
        then callError "division by zero"
        else alloc $ VInt (x `quot` y)
  remAddr <- native2 $ \a b ->
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
  fremAddr <- native2 $ \a b ->
    withFloat "%." a $ \x -> withFloat "%." b $ \y ->
      if y == 0
        then programError "division by zero"
        else alloc $ VFloat (x - y * fromInteger (truncate (x / y)))
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

  toIntAddr <- native1 $ \a ->
    withFloat "to_int" a $ \x -> alloc $ VInt (truncate x)
  toFloatAddr <- native1 $ \a ->
    withInt "to_float" a $ \x -> alloc $ VFloat (fromInteger x)

  -- Strings.
  concatAddr <- string2 "++" (<>)
  slenAddr <- native1 $ \a ->
    withString "slen" a $ \s -> alloc $ VInt (fromIntegral (T.length s))
  -- start, length, string: characters outside the string are dropped, so a
  -- slice never fails and `sub 0 n s` is a prefix of `s` of length `n`.
  subAddr <- nativeN 3 $ \case
    [startA, lenA, sA] -> do
      start <- withInt "sub" startA pure
      len <- withInt "sub" lenA pure
      withString "sub" sA $ \s ->
        alloc $ VString $ T.take (fromInteger (max 0 len)) $ T.drop (fromInteger (max 0 start)) s
    args -> arityError "sub" 3 args
  splitAddr <- native2 $ \a b ->
    withString "split" a $ \sep -> withString "split" b $ \s -> do
      xs <- mapM (alloc . VString) $ if T.null sep then [s] else T.splitOn sep s
      alloc $ VArray xs
  joinAddr <- native2 $ \a b ->
    withString "join" a $ \sep -> withArray "join" b $ \xs -> do
      parts <- mapM (\x -> withString "join" x pure) xs
      alloc $ VString (T.intercalate sep parts)
  trimAddr <- stringFun "trim" T.strip
  upperAddr <- stringFun "upper" T.toUpper
  lowerAddr <- stringFun "lower" T.toLower
  containsAddr <- native2 $ \a b ->
    withString "contains" a $ \needle -> withString "contains" b $ \hay ->
      alloc $ VBoolean (needle `T.isInfixOf` hay)
  replaceAddr <- nativeN 3 $ \case
    [fromA, toA, sA] -> do
      from <- withString "replace" fromA pure
      to <- withString "replace" toA pure
      withString "replace" sA $ \s ->
        alloc $ VString (if T.null from then s else T.replace from to s)
    args -> arityError "replace" 3 args
  seqAddr <- native2 $ \a b ->
    withString "seq" a $ \x -> withString "seq" b $ \y -> alloc $ VBoolean (x == y)
  sneqAddr <- native2 $ \a b ->
    withString "sneq" a $ \x -> withString "sneq" b $ \y -> alloc $ VBoolean (x /= y)

  -- Booleans.
  notAddr <- native1 $ \a ->
    withBool "not" a $ \x -> alloc $ VBoolean (not x)
  orAddr <- shortCircuit "||" True
  andAddr <- shortCircuit "&&" False
  xorAddr <- boolOp "^" (/=)
  norAddr <- boolOp "nor" (\a b -> not (a || b))
  nandAddr <- boolOp "nand" (\a b -> not (a && b))

  -- `and` is the old short-circuiting conjunction; it stays because the
  -- examples of the paper use it, and it means the same as `&&`.
  legacyAndAddr <- shortCircuit "and" False

  forceAddr <- alloc $ VClosure st.sEnv emptyCache Nothing force
  whnfBuiltinAddr <- alloc $ VClosure st.sEnv emptyCache Nothing whnf
  predAddr <- intFun "pred" (subtract 1)
  assertAddr <- native2 $ \a b ->
    withBool "assert" a $ \ok ->
      if ok
        then alloc VNil
        else withString "assert" b callError
  argsAddr <- do
      argAddrs <- mapM (alloc . VString . T.pack) cmdArgs
      alloc $ VArray argAddrs

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
          ("args", argsAddr)
        ]

  -- The library records are views of the very values above, so
  -- `Numbers@+` and `+` are one function and cannot drift apart.
  recordBindings <- forM (Builtins.builtins >>= asRecord) $ \(name, fields) -> do
    propAddrs <- forM fields $ \field ->
      case lookup field natives of
        Just addr -> pure (field, addr)
        Nothing -> rtError $ "internal error: the library record `" <> name
          <> "` names `" <> field <> "`, which is not a native value"
    eid <- newEnv Env {bindings = Map.fromList [(n, (Val, a)) | (n, a) <- propAddrs], parent = Nothing}
    addr <- alloc (VRecord eid)
    pure (name, (Val, addr))

  let justNatives = Map.fromList $ map (\(n, a) -> (n, (Val, a))) natives

      allBindings = operations <> justNatives <> Map.fromList recordBindings

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

  where
    asRecord (Builtins.Builtin name (Builtins.Record fields)) = [(name, fields)]
    asRecord _ = []

-- | Raise an error through the effect @Error@, so that a handler installed by
--   the program sees it and the bottom handler turns it into a diagnostic when
--   no handler does.
callError :: Text -> Interp Address
callError msg = do
  addr <- alloc (VString msg)
  callEffect (Eff.elabel "Error") "error" [addr]

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
evalChunk chunk = do
  st <- get
  let env0 = st.sEnv

  let functDefs = [fd | IR.SFunctDef fd <- chunk, fd.fName /= "main"]
  forM_ functDefs $ \fd -> do
    let cache = case fst fd.fRet of
          Just fxs -> if isPureClosure fxs then Just IM.empty else Nothing
          _ -> Just IM.empty
    fn <- makeTopLevelClosure env0 fd
    void $ bindValIn env0 fd.fName $ VClosure env0 cache
          (Just (CodeFun (map fst $ IR.fArgs fd) (IR.fBlock fd))) fn

  let mainDecl = findMain chunk
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
findMain = find $ \case
  (IR.SFunctDef fd) -> fd.fName == "main"
  _ -> False

makeTopLevelClosure :: EnvId -> IR.FunctDecl -> Interp (Address -> Interp Address)
makeTopLevelClosure env fd = makeClosureChain env (map fst $ IR.fArgs fd) (IR.fBlock fd)

-- | A curried function, as nested lambdas: each argument extends the scope of
--   the previous one, and the first extends the scope where the function is
--   defined (E-App).  The chain must not be built from the caller's scope: a
--   call sees only its lexical parents, and a tail call would otherwise append
--   the caller's environment to the callee's, which made a long loop grow
--   without bound.
makeClosureChain :: EnvId -> [Text] -> IR.Block -> Interp (Address -> Interp Address)
makeClosureChain _ [] _ =
  rtError "internal error: a top-level function was declared with no arguments"
makeClosureChain env [argName] block = pure $ \argAddr -> do
  outer <- gets sEnv
  eid <- newEnv Env {
      bindings = Map.singleton argName (Val, argAddr),
      parent = Just env
    }
  modify $ \s -> s {sEnv = eid}
  result <- evalBlock block pure
  modify $ \s -> s {sEnv = outer}
  pure result
makeClosureChain env (argName:rest) block = pure $ \argAddr -> do
  outer <- gets sEnv
  eid <- newEnv Env {
      bindings = Map.singleton argName (Val, argAddr),
      parent = Just env
    }
  modify $ \s -> s {sEnv = eid}
  -- The rest of the function closes over this argument's scope.
  restClosure <- makeClosureChain eid rest block
  result <- allocClosure eid (Just IM.empty) (CodeFun rest block) restClosure
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
    TENLambda _ -> rtError "native lambdas are not implemented in the interpreter"
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
          void $ bindValIn opsEnv name (VClosure opsEnv (Just IM.empty) Nothing fn)
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

-- | Приводит VThunk к значению и возвращает его адрес
force :: Address -> Interp Address
force addr = do
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
whnf addr = go addr
  where
    go a = do
      v <- readCell a
      case v of
        VThunk expr env' -> do
          oldEnv <- gets sEnv
          modify $ \s -> s {sEnv = env'}
          resultAddr <- case expr of
            TEParen b -> evalBlock b pure
            _ -> evalExpr expr pure
          modify $ \s -> s {sEnv = oldEnv}
          go resultAddr
        _ -> do
          writeCell addr v
          pure addr

-- | Приводит VThunk к значению и возвращает само значение
forceValue :: Address -> Interp Value
forceValue addr = do
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
        _ -> alloc . VClosure env (Just IM.empty) Nothing =<< go (arg : acc) (n - 1)

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
  IR.Rebind n t -> do
    env <- gets sEnv
    m <- lookupMut env n
    case m of
      Var -> void $ rebind n t
      _ -> rtError $ T.concat [
          "cannot assign to `", n, "`: it is bound with `", pretty m, "`"
        ]
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
  CodeFun args block -> foldr Set.delete (freeVarsBlock block) args

-- | Переписанный код и функция, собранная из него в окружении env'
freezeCode :: EnvId -> Code -> Interp (Code, Address -> Interp Address)
freezeCode env' = \case
  CodeLam lam -> do
    let lam' = freezeLambda lam
    fn <- evalLambda env' lam'
    pure (CodeLam lam', fn)
  CodeFun args block -> do
    let block' = freezeBlock block
    fn <- makeClosureChain env' args block'
    pure (CodeFun args block', fn)

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
      IR.Rebind n e -> (Set.difference (Set.insert n (freeVars e)) bound, bound)
      IR.Expr e -> (Set.difference (freeVars e) bound, bound)

freeVarsStat :: IR.Stat -> Set.Set Text
freeVarsStat = \case
  IR.Bind _ _ e -> freeVars e
  IR.Rebind _ e -> freeVars e
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
  sSpan       = noSpan
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