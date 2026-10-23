{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE DefaultSignatures #-}

module Interpreter (interpret) where

import qualified TypedIR as IR
import Types (
    Mutability(..),
    ECons,
    LetPattern(..),
    AtomLetPattern(..),
    LetPatternRecordProp(..),
    LambdaParam(..), EffRow (..)
  )
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Scientific (Scientific, fromFloatDigits)
import Control.Monad.Cont (ContT(..), callCC)
import Utils (TextMap, Pretty (..))
import Data.Foldable (find)
import TypedIR (TypedExpr(..), Lambda(..), Block, TERecordProp(..))
import Control.Monad.State
import Control.Monad (foldM, forM, forM_, void, replicateM, foldM_, when)
import Infer (freezeMutability, freeze)
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
import Data.Traversable (for)
import Data.Maybe (fromMaybe)

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
  | VClosure EnvId (Maybe (Map Address Address)) (Address -> Interp Address)
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
    VClosure eid _ _ -> "!closure[" <> T.unpack (pretty eid) <> "]!"
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
    VClosure eid _ _ -> "!closure[" <> pretty eid <> "]!"
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
    VArray vals -> pure $ "[" <> T.intercalate ", " (map pretty vals) <> "]"
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
    VClosure eid _ _ -> pure $ "!closure[" <> pretty eid <> "]!"
    VThunk e _env -> pure $ T.concat ["!vthunk: ", pretty e,"!"]
    VBThunk b _env -> pure $ T.concat ["!bthunk: ", pretty b,"!"]
    VBottom -> pure "⊥"

-- | Окружение переменных
newtype Address = Address Int deriving (Ord, Eq, Show)
instance Pretty Address where pretty (Address a) = T.pack $ printf "#%08x" a

instance Stringify Address where
  stringify a = do
    heap <- gets sHeap
    stringify $ derefUnsafe heap a

newtype EnvId = EnvId Int deriving (Ord, Eq, Show)
instance Pretty EnvId where pretty (EnvId i) = T.pack $ printf "&%08x" i

data Env = Env {
  bindings :: TextMap (Mutability, Address),
  parent   :: Maybe EnvId
}

-- TODO: instance Stringify Env (using #{parent | bindings})

type Heap = Map Address Value

getEnv :: EnvId -> Interp Env
getEnv eid = do
  st <- get
  case Map.lookup eid st.sEnvs of
    Just e -> pure e
    Nothing -> error "invalid env"

updateEnv :: EnvId -> Env -> Interp EnvId
updateEnv eid env = do
  modify $ \s -> s {sEnvs = Map.insert eid env s.sEnvs}
  pure eid

newEnv :: Env -> Interp EnvId
newEnv env = do
  n <- gets sNextEnv
  let eid = EnvId n
  modify $ \s -> s {sNextEnv = n + 1, sEnvs = Map.insert eid env s.sEnvs}
  pure eid

getCurrentEnv :: Interp Env
getCurrentEnv = getEnv =<< gets sEnv

modifyCurrentEnv :: (Env -> Env) -> Interp EnvId
modifyCurrentEnv f = flip modifyEnv f =<< gets sEnv

modifyEnv :: EnvId -> (Env -> Env) -> Interp EnvId
modifyEnv eid f = updateEnv eid . f =<< getEnv eid

findBindingEnv :: EnvId -> Text -> Interp (EnvId, Mutability, Address)
findBindingEnv eid name = go Set.empty eid
  where
    go visited eid' = do
      when (Set.member eid' visited) $ error $ "Cyclic environment: " <> show eid'
      env <- getEnv eid'
      case Map.lookup name env.bindings of
        Just (m,a) -> pure (eid', m, a)
        Nothing -> case env.parent of
          Just p -> go (Set.insert eid' visited) p
          Nothing -> error $ "Unbound variable: " <> T.unpack name

getCell :: Env -> Text -> Maybe (Mutability, Address)
getCell e x = Map.lookup x e.bindings

getRef :: Env -> Text -> Maybe Address
getRef e x = snd <$> getCell e x

getMut :: Env -> Text -> Maybe Mutability
getMut e x = fst <$> getCell e x

deref :: Heap -> Address -> Maybe Value
deref h a = Map.lookup a h

derefIn :: Address -> Interp (Maybe Value)
derefIn a = do
  st <- get
  pure $ deref st.sHeap a

derefUnsafe :: Heap -> Address -> Value
derefUnsafe h a = case deref h a of
  Just v -> v
  _ -> error $ T.unpack $ "Undead address: " <> pretty a

derefUnsafeIn :: Address -> Interp Value
derefUnsafeIn a = do
  st <- get
  pure $ derefUnsafe st.sHeap a

unpackRef :: Env -> Heap -> Text -> Maybe Value
unpackRef e h x = getRef e x >>= deref h

data InterpState = InterpState {
  sEnv      :: EnvId,
  sEnvs     :: Map EnvId Env,
  sHeap     :: Heap,
  sKstack   :: [HandlerFrame],
  sNextAddr :: Int,
  sNextEnv  :: Int
}

type Clause = [Address] -> (Address -> Interp Address) -> Interp Address

data HandlerFrame = HandlerFrame {
  hEffect     :: ECons,
  hClauses    :: Map Text Clause,
  hThen       :: Address -> Interp Address
}

-- | Монада интерпретации: CPS с IO
type Interp a = ContT Value (StateT InterpState IO) a

-- | Запуск интерпретации
interpret :: IR.Chunk -> [String] -> IO Value
interpret chunk cmdArgs = do
  let initState = InterpState {
        sEnv = EnvId 0,
        sEnvs = Map.empty,
        sHeap = Map.empty,
        sKstack = globalHandlers,
        sNextAddr = 0,
        sNextEnv = 1
      }
  (result, finalState) <- runStateT (runContT (do
      root <- newEnv $ Env Map.empty Nothing
      modify $ \st -> st {sEnv = root}
      _ <- buildInitialEnv
      evalChunk chunk
    ) pure) initState
  pure result

globalHandlers :: [HandlerFrame]
globalHandlers = [
    HandlerFrame {
      hEffect = Eff.elabel "Output",
      hClauses = Map.fromList [
        ("say", \case
          [addrArg] -> \_ -> do
            liftIO . putStr . T.unpack =<< stringify =<< forceValue addrArg
            alloc VNil
          _ -> error "Incorrect args amount"),
        ("sayn", \case
          [addrArg] -> \_ -> do
            liftIO . putStrLn . T.unpack =<< stringify =<< forceValue addrArg
            alloc VNil
          _ -> error "Incorrect args amount"),
        ("trace", \case
          [addrArg] -> \_ -> do
            st <- get
            liftIO $ putStrLn $ T.unpack $ pretty $ derefUnsafe st.sHeap addrArg
            pure addrArg
          _ -> error "Incorrect args amount")
      ],
      hThen = pure
    },
    HandlerFrame {
      hEffect = Eff.elabel "Input",
      hClauses = Map.fromList [
        ("read_string", \_ _ -> do
          input <- T.pack <$> liftIO getLine
          case Parser.parseFromText Parser.stringLiteral input of
            Left err -> error err
            Right s -> alloc $ VString s),
        ("read_int", \_ _ -> do
          input <- T.pack <$> liftIO getLine
          case Parser.parseFromText Parser.intLiteral input of
            Left err -> liftIO (putStrLn err) >> alloc (VInt 0)
            Right i -> alloc $ VInt i),
        ("read_float", \_ _ -> do
          input <- T.pack <$> liftIO getLine
          case Parser.parseFromText Parser.floatLiteral input of
            Left err -> liftIO (putStrLn err) >> alloc (VFloat 0.0)
            Right f -> alloc $ VFloat f),
        ("read_boolean", \_ _ -> do
          input <- T.pack <$> liftIO getLine
          case Parser.parseFromText Parser.bool input of
            Left err -> liftIO (putStrLn err) >> alloc (VBoolean False)
            Right b -> alloc $ VBoolean b)
      ],
      hThen = pure
    },
    HandlerFrame {
      hEffect = Eff.elabel "Random",
      hClauses = Map.fromList [
        ("random_int", \_ _ -> do
          r <- liftIO $ toInteger <$> (randomRIO (minBound, maxBound) :: IO Int)
          alloc $ VInt r),
        ("random_float", \_ _ -> do
          r <- liftIO $ fromFloatDigits <$> (randomRIO (0.0, 1.0) :: IO Double)
          alloc $ VFloat r),
        ("random_boolean", \_ _ -> alloc . VBoolean =<< randomIO),
        ("random_string", \case
          [addr] -> \_ -> do
            st <- get
            r <- T.pack <$> case derefUnsafe st.sHeap addr of
              VInt n | n <= 0 -> pure ""
              VInt n -> map chr <$> replicateM (fromInteger n) (randomRIO (32, 126))
              _ -> error "Not Int"
            alloc $ VString r
          _ -> error "Incorrect args amount")
      ],
      hThen = pure
    },
    HandlerFrame {
      hEffect = Eff.elabel "Time",
      hClauses = Map.fromList [
        ("time_ms", \_ _ -> do
          cpuTime <- liftIO getCPUTime
          alloc $ VInt $ fromInteger $ cpuTime `div` 1_000_000_000),
        ("sleep", \case
          [addr] -> \_ -> do
            st <- get
            case derefUnsafe st.sHeap addr of
              VInt i -> liftIO (threadDelay $ fromInteger i) >> alloc VNil
              _ -> error "Not Int"
          _ -> error "Incorrect args amount")
      ],
      hThen = pure
    }
  ]

buildInitialEnv :: Interp EnvId
buildInitialEnv = do
  let allocEffectCall eff op arity = do
        env <- gets sEnv
        clos <- makeEffectClosure env arity (Eff.elabel eff) op
        addr <- alloc $ VClosure env Nothing clos
        pure (op, addr)
  -- Замыкания для операций
  sayAddr           <- allocEffectCall "Output" "say" 1
  saynAddr          <- allocEffectCall "Output" "sayn" 1
  traceAddr         <- allocEffectCall "Output" "trace" 1
  readStringAddr    <- allocEffectCall "Input"  "read_string" 1
  readIntAddr       <- allocEffectCall "Input"  "read_int" 1
  readFloatAddr     <- allocEffectCall "Input"  "read_float" 1
  readBooleanAddr   <- allocEffectCall "Input"  "read_boolean" 1
  randomIntAddr     <- allocEffectCall "Random" "random_int" 1
  randomFloatAddr   <- allocEffectCall "Random" "random_float" 1
  randomBoolAddr    <- allocEffectCall "Random" "random_boolean" 1
  randomStringAddr  <- allocEffectCall "Random" "random_string" 1
  timeMsAddr        <- allocEffectCall "Time"   "time_ms" 1
  sleepAddr         <- allocEffectCall "Time"   "sleep" 1

  let operations = Map.fromList $ map (\(n, a) -> (n, (Val, a))) [
          sayAddr,
          saynAddr,
          traceAddr,
          readStringAddr,
          readIntAddr,
          readFloatAddr,
          readBooleanAddr,
          randomIntAddr,
          randomFloatAddr,
          randomBoolAddr,
          randomStringAddr,
          timeMsAddr,
          sleepAddr
        ]
  st <- get

  let getInt :: Address -> Interp Integer
      getInt addr = do
        st' <- get
        case deref st'.sHeap addr of
          Just (VThunk _ _) -> do
            _ <- force addr
            st'' <- get
            case deref st''.sHeap addr of
              Just (VInt i) -> pure i
              v -> error $ "Expected Int after forcing, got " <> show v
          Just (VInt i) -> pure i
          Nothing -> error $ T.unpack $ "Undead address in getInt: " <> pretty addr
          Just v -> error $ "Expected Int or thunk, got " <> show v
      getBool :: Address -> Interp Bool
      getBool addr = do
        st' <- get
        case deref st'.sHeap addr of
          Just (VThunk _ _) -> do
            _ <- force addr
            st'' <- get
            case deref st''.sHeap addr of
              Just (VBoolean b) -> pure b
              v -> error $ "Expected Boolean after forcing, got " <> show v
          Just (VBoolean b) -> pure b
          Nothing -> error $ T.unpack $ "Undead address in getBool: " <> pretty addr
          Just v -> error $ "Expected Bool or thunk, got " <> show v

  let emptyCache = Just (Map.empty :: Map Address Address)

  plusAddr <- alloc $ VClosure st.sEnv emptyCache $ \addrA -> do
      a <- getInt addrA
      st' <- get
      alloc $ VClosure st'.sEnv emptyCache $ \addrB -> do
        b <- getInt addrB
        alloc $ VInt $ a + b
  minusAddr <- alloc $ VClosure st.sEnv emptyCache $ \addrA -> do
      a <- getInt addrA
      st' <- get
      alloc $ VClosure st'.sEnv emptyCache $ \addrB -> do
        b <- getInt addrB
        alloc $ VInt $ a - b
  forceAddr <- alloc $ VClosure st.sEnv emptyCache force
  ieqAddr <- alloc $ VClosure st.sEnv emptyCache $ \addrA -> do
      a <- getInt addrA
      st' <- get
      alloc $ VClosure st'.sEnv emptyCache $ \addrB -> do
        b <- getInt addrB
        alloc $ VBoolean $ a == b
  igtAddr <- alloc $ VClosure st.sEnv emptyCache $ \addrA -> do
      a <- getInt addrA
      st' <- get
      alloc $ VClosure st'.sEnv emptyCache $ \addrB -> do
        b <- getInt addrB
        alloc $ VBoolean $ a > b
  andAddr <- alloc $ VClosure st.sEnv emptyCache $ \addrA -> do
      a <- getBool addrA
      st' <- get
      alloc $ VClosure st'.sEnv emptyCache $ \addrB -> do
        b <- getBool addrB
        alloc $ VBoolean $ a && b
  let justNatives = Map.fromList $ map (\(n, a) -> (n, (Val, a))) [
          ("+", plusAddr),
          ("-", minusAddr),
          ("force", forceAddr),
          ("ieq", ieqAddr),
          (">", igtAddr),
          ("and", andAddr)
        ]
  modifyCurrentEnv $ \e -> e {bindings = operations <> justNatives <> e.bindings}

-- | Выполнение чанка (игнорируем декларации, просто идём дальше)
evalChunk :: IR.Chunk -> Interp Value
evalChunk chunk = do
  st <- get
  let env0 = st.sEnv

  let functDefs = [fd | IR.SFunctDef fd <- chunk, fd.fName /= "main"]
  forM_ functDefs $ \fd -> do
    let cache = case fst fd.fRet of
          Just fxs -> if isPureClosure fxs then Just Map.empty else Nothing
          _ -> Just Map.empty
    bindValIn env0 fd.fName . VClosure env0 cache =<< makeTopLevelClosure fd

  let mainDecl = findMain chunk
  case mainDecl of
    Nothing -> liftIO (putStrLn "Warning: No 'main' function found") >> pure VNil
    Just (IR.SFunctDef mainFunct) -> do
      resultAddr <- evalBlock (IR.fBlock mainFunct) pure
      liftIO $ putStrLn $ T.unpack $ "evalChunk resultAddr: " <> pretty resultAddr
      st' <- get
      pure $ derefUnsafe st'.sHeap resultAddr
    Just _ -> error "'main' is not a function definition"

findMain :: IR.Chunk -> Maybe IR.TopLevelStat
findMain = find $ \case
  (IR.SFunctDef fd) -> fd.fName == "main"
  _ -> False

makeTopLevelClosure :: IR.FunctDecl -> Interp (Address -> Interp Address)
makeTopLevelClosure fd = makeClosureChain (map fst $ IR.fArgs fd) (IR.fBlock fd)

makeClosureChain :: [Text] -> IR.Block -> Interp (Address -> Interp Address)
makeClosureChain [] _ = error "Function without arguments not supported"
makeClosureChain [argName] block = pure $ \argAddr -> do
  oldEnv <- gets sEnv
  eid <- newEnv Env {
      bindings = Map.singleton argName (Val, argAddr),
      parent = Just oldEnv
    }
  modify $ \s -> s {sEnv = eid}
  evalBlock block pure
makeClosureChain (argName:rest) block = do
  restClosure <- makeClosureChain rest block
  pure $ \argAddr -> do
    oldEnv <- gets sEnv
    eid <- newEnv Env {
        bindings = Map.singleton argName (Val, argAddr),
        parent = Just oldEnv
      }
    modify $ \s -> s {sEnv = eid}
    alloc $ VClosure eid (Just Map.empty) restClosure

-- | Выполнение выражения
evalExpr :: TypedExpr -> (Address -> Interp Address) -> Interp Address
evalExpr expr cont =
  case expr of
    TEInt i -> do
      -- liftIO $ putStrLn $ "evalExpr [TEInt] | " <> show i
      cont =<< alloc (VInt i)
    TEFloat f -> do
      -- liftIO $ putStrLn $ "evalExpr [TEFloat] | " <> show f
      cont =<< alloc (VFloat f)
    TEBoolean b -> do
      -- liftIO $ putStrLn $ "evalExpr [TEBoolean] | " <> show b
      cont =<< alloc (VBoolean b)
    TEString s -> do
      -- liftIO $ putStrLn $ "evalExpr [TEString] | " <> T.unpack s
      cont =<< alloc (VString s)
    TENil -> do
      -- liftIO $ putStrLn "evalExpr [TENil]"
      cont =<< alloc VNil
    TEXVar n _ -> do
      -- liftIO $ putStrLn $ "evalExpr [TEXVar] | " <> T.unpack n
      env <- gets sEnv
      cont =<< lookupRef env n
    TEArray _ xs -> do
      -- liftIO $ putStrLn $ "evalExpr [TEArray] | [" <> T.unpack (T.intercalate ", " $ map pretty xs) <> "]"
      st <- get
      xs' <- mapM (\x -> alloc $ VThunk x st.sEnv) xs
      cont =<< alloc (VArray xs')
    TEPair l r -> do
      env <- gets sEnv
      -- liftIO $ putStrLn $ "evalExpr [TEPair] | l: " <> T.unpack (pretty l) <> ", r: " <> T.unpack (pretty r)
      l' <- alloc $ VThunk l env
      r' <- alloc $ VThunk r env
      cont =<< alloc (VPair l' r')
    TEXLambda lam -> do
      env <- gets sEnv
      -- liftIO $ putStrLn $ "evalExpr [TEXLambda] | " <> T.unpack (pretty lam)
      body <- evalLambda env lam
      let cache = if isPureClosure lam.lFxs then Just Map.empty else Nothing
      cont =<< alloc (VClosure env cache body)
    TENLambda _ -> error "TODO"
    TEApply f x -> do
      liftIO $ putStrLn $ "evalExpr [TEApply] | f: " <> T.unpack (pretty f) <> ", x: " <> T.unpack (pretty x)
      fAddr <- force =<< evalExpr f pure
      xAddr <- delayArg x
      st <- get
      case derefUnsafe st.sHeap fAddr of
        VClosure env' (Just cache) clos ->
          case Map.lookup xAddr cache of
            Just cached -> do
              liftIO $ putStrLn $ concat [
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
              let newCache = Map.insert xAddr result cache
              modify $ \s -> s {sHeap = Map.insert fAddr (VClosure env' (Just newCache) clos) s.sHeap}
              pure result
        VClosure env' _ clos -> do
          oldEnv <- gets sEnv
          modify $ \s -> s {sEnv = env'}
          result <- clos xAddr
          modify $ \s -> s {sEnv = oldEnv}
          pure result
        _ -> error "Not a function"
    TERecord _ ps -> do
      st <- get
      triples <- mapM (\p -> (p.terMut, p.terName, ) <$> alloc (VThunk p.terExpr st.sEnv)) ps
      eid <- newEnv Env {
        bindings = Map.fromList [(n, (m, a)) | (m, n, a) <- triples],
        parent = Nothing
      }
      cont =<< alloc (VRecord eid)
    TEPropAccess r x -> do
      rAddr0 <- evalExpr r pure
      h0 <- gets sHeap
      rAddr <- case deref h0 rAddr0 of
        Just (VThunk _ _) -> force rAddr0
        _ -> pure rAddr0
      st <- get
      case derefUnsafe st.sHeap rAddr of
        VRecord eid -> do
          env <- getEnv eid
          case getRef env x of
            Just a -> cont a
            Nothing -> error $ concat ["Record doesn't have binding '", T.unpack x, "'"]
        _ -> error "Not a record"
    TEHandle (IR.Handler fx b clauses thenLam) _ -> do
      env <- gets sEnv
      thenFn <- evalLambda env thenLam
      callCC $ \finish -> do
        let finishWithThen result = do
              liftIO $ putStrLn "running then"
              thenResult <- thenFn result
              modify $ \s -> s {sEnv = env}
              finish thenResult
        let clausesMap = Map.fromList $ map (makeClause finishWithThen) clauses
            handler = HandlerFrame fx clausesMap finishWithThen
        -- операции эффекта живут в собственном окружении, а не в текущем
        opsEnv <- newEnv Env {bindings = Map.empty, parent = Just env}
        forM_ clauses $ \(name, _, _, arity) -> do
          fn <- makeEffectClosure opsEnv arity fx name
          void $ bindValIn opsEnv name (VClosure opsEnv (Just Map.empty) fn)
        modify $ \s -> s {sEnv = opsEnv, sKstack = handler : s.sKstack}
        result <- evalBlock b pure
        finishWithThen result
    p@(TEParen _) -> do
      env <- gets sEnv
      cont =<< alloc (VThunk p env)
    TEResume t _ -> do
      st <- get
      env <- getEnv st.sEnv
      case lookupVar env st.sHeap "resume" of
        VClosure _ _ clos -> do
          tAddr <- evalExpr t pure
          clos tAddr
        _ -> error "resume not in scope"
    TELet pat bound body -> do
      addr <- evalExpr bound pure
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
        _ -> error "Condition must be boolean"

-- | Приводит VThunk к значению и возвращает его адрес
force :: Address -> Interp Address
force addr = do
  heap <- gets sHeap
  case deref heap addr of
    Just (VThunk expr env') -> do
      liftIO $ putStrLn $ "force | Forcing " <> T.unpack (pretty addr) <> ": " <> show expr
      oldEnv <- gets sEnv
      modify $ \s -> s {sEnv = env'}
      resultAddr <- case expr of
        TEParen b -> evalBlock b pure
        _ -> evalExpr expr pure
      liftIO $ putStrLn $ "force | resultAddr: " <> T.unpack (pretty resultAddr)
      resultAddr' <- force resultAddr
      liftIO $ putStrLn $ "force | resultAddr': " <> T.unpack (pretty resultAddr')
      st' <- get
      let resultVal = derefUnsafe st'.sHeap resultAddr'
      liftIO $ putStrLn $ "force | resultVal: " <> T.unpack (pretty resultVal)
      modify $ \s -> s {sEnv = oldEnv, sHeap = Map.insert addr resultVal s.sHeap}
      pure addr  -- возвращаем тот же адрес, но теперь там значение
    Just (VArray es) -> do
      mapM_ force es
      pure addr
    Just (VPair l r) -> do
      _ <- force l
      _ <- force r
      pure addr
    Just (VRecord eid) -> do
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
    Just _ -> do
      liftIO $ putStrLn $ "force | No need to force " <> T.unpack (pretty addr)
      pure addr
    Nothing -> error $ T.unpack $ "force | undead address " <> pretty addr

-- | Приводит VThunk к значению и возвращает само значение
forceValue :: Address -> Interp Value
forceValue addr = do
  st <- get
  case deref st.sHeap addr of
    Just (VThunk expr env') -> do
      liftIO $ putStrLn $ "forceValue | Forcing " <> T.unpack (pretty addr) <> ": " <> show expr
      oldEnv <- gets sEnv
      modify $ \s -> s {sEnv = env'}
      resultAddr <- force =<< evalExpr expr pure
      st' <- get
      let resultVal = derefUnsafe st'.sHeap resultAddr
      modify $ \s -> s {sEnv = oldEnv, sHeap = Map.insert addr resultVal s.sHeap}
      pure resultVal
    Just v -> do
      liftIO $ putStrLn $ "forceValue | No need to force " <> T.unpack (pretty addr)
      pure v
    Nothing -> error $ T.unpack $ "forceValue | undead address " <> pretty addr

callEffect :: ECons -> Text -> [Address] -> Interp Address
callEffect eff opName args = do
  callCC $ \k -> do
    -- liftIO $ putStrLn $ concat [
    --     "callEffect: ", show eff, " ", show opName, " with args [", intercalate ", " $ map show args, "]"
    --   ]
    st <- get
    case find ((== eff) . hEffect) st.sKstack of
      Just handler -> do
        case Map.lookup opName handler.hClauses of
          Just clauseFn -> clauseFn args k
          Nothing -> error $ "Operation '" <> T.unpack opName <> "' not found in handler for " <> T.unpack (pretty eff)
      Nothing -> error $ "No handler for effect " <> T.unpack (pretty eff)

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
        _ -> alloc . VClosure env (Just Map.empty) =<< go (arg : acc) (n - 1)

makeClause ::
  (Address -> Interp Address)     -- finishWithThen
  -> IR.HandlerClause
  -> (Text, Clause)
makeClause finishWithThen
  (name, lam, hasResume, _) =
    (name, runClause)
  where
    runClause args k = do
      liftIO $ putStrLn $ "makeClause: " <> show name <> " called with args " <> show args
      cur <- gets sEnv
      resumeAddr <- alloc $ VClosure cur (Just Map.empty) k

      -- resume живёт в собственном окружении клаузы
      eid <- newEnv Env {
        bindings = Map.singleton "resume" (Val, resumeAddr),
        parent = Just cur
      }

      clos <- evalLambda eid lam
      result <- applyMany clos eid Map.empty args
      modify $ \s -> s {sEnv = cur}

      case hasResume of
        NoResume -> finishWithThen result
        _ -> k result

applyMany :: (Address -> Interp Address) -> EnvId -> Map Address Address -> [Address] -> Interp Address
applyMany clos eid cache args = do
  liftIO $ putStrLn $ "applyMany: args = " <> show args
  case args of
    [] -> error "empty argument list"
    [x] -> applyClos x clos eid cache
    (x:xs) -> do
      addr <- clos x
      st <- get
      case derefUnsafe st.sHeap addr of
        VClosure eid' (Just cache') next -> applyMany next eid' cache' xs
        VClosure eid' _ next -> applyMany next eid' Map.empty xs
        _ -> error "expected closure"
  where
    applyClos :: Address -> (Address -> Interp Address) -> EnvId -> Map Address Address -> Interp Address
    applyClos xAddr cl eid' cache' =
      case Map.lookup xAddr cache' of
        Just cached -> do
          liftIO $ putStrLn $ T.unpack $ "Don't have to apply many closure: " <> pretty xAddr <> " is cached"
          pure cached
        _ -> do
          liftIO $ putStrLn $ T.unpack $ "Apply many closure to " <> pretty xAddr
          oldEnv <- gets sEnv
          modify $ \s -> s {sEnv = eid'}
          result <- cl xAddr
          liftIO $ putStrLn $ T.unpack $ "Apply many result address: " <> pretty result
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
--   (модель: S-Val/Var/Imm). Ранее созданные замыкания и thunk'и остаются
--   в прежнем окружении и поэтому не видят новую привязку.
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
--   сразу, остальные становятся thunk'ом над текущим окружением.
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

evalStat :: IR.Stat -> Interp ()
evalStat stat = case stat of
  IR.Bind m n t -> do
    eid <- gets sEnv
    case m of
      Imm -> void $ bindImm n t
      _ -> do
        -- thunk замкнут на окружение ДО привязки: привязки не рекурсивны
        a <- alloc $ VThunk t eid
        void $ extendEnv n m a
  IR.Rebind n t -> do
    env <- gets sEnv
    m <- lookupMut env n
    case m of
      Var -> void $ rebind n t
      _ -> error $ "Cannot assign to non-var binding: " <> T.unpack (pretty m)
  IR.Expr t -> do
    _ <- evalExpr t pure
    pure ()

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

-- | Снимок (модель: snapshot). Свободные переменные ищутся по всей цепочке
--   окружений и копируются с замораживанием; у снимка нет живого родителя,
--   кроме глобального окружения (в нём только val-привязки).
snapshot :: EnvId -> Heap -> Set Text -> Interp EnvId
snapshot oldEnvId oldHeap liveVars = do
  root <- rootEnvOf oldEnvId
  env <- newEnv Env {
    bindings = Map.empty,
    parent = Just root
  }
  forM_ (Set.toList liveVars) $ \name -> do
    found <- findBindingMaybe oldEnvId name
    case found of
      -- имя связано внутри самого выражения
      Nothing -> pure ()
      Just (m, addr) ->
        case deref oldHeap addr of
          Just v -> do
            frozenVal <- freezeValue v
            newAddr <- case v of
              -- функции (в том числе встроенные) разделяются, а не копируются
              VClosure {} -> pure addr
              _ -> alloc frozenVal
            void $ modifyEnv env $ \env' -> env' {
              bindings = Map.insert name (freezeMutability m, newAddr) env'.bindings
            }
          Nothing -> error $ T.unpack $ "Undead address in snapshot: " <> pretty addr
  pure env

-- | Модель (S-Rebind): привязка перенаправляется в том окружении, где она
--   объявлена, на новую ленивую ячейку; правая часть видит старую привязку.
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
      pure addr'
    _ -> error $ concat ["Cannot rebind '", T.unpack x, "': it's ", T.unpack $ pretty m]

allocIn :: InterpState -> Value -> (InterpState, Address)
allocIn st v =
  let addri = st.sNextAddr
      addr = Address addri
      heap' = Map.insert addr v st.sHeap
  in (st {sHeap = heap', sNextAddr = addri + 1}, addr)

alloc :: Value -> Interp Address
alloc v = do
  st <- get
  let (st', a) = allocIn st v
  put st'
  pure a

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
  let liveVars = freeVars expr
  frozenEnv <- snapshot st.sEnv st.sHeap liveVars
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

-- | Поиск переменной в окружении
lookupVar :: Env -> Heap -> Text -> Value
lookupVar e h name =
  case unpackRef e h name of
    Just v -> v
    Nothing -> error $ "Unbound variable: " <> T.unpack name

lookupMut :: EnvId -> Text -> Interp Mutability
lookupMut e name = do
  (_, m, _) <- findBindingEnv e name
  pure m

freezeValue :: Value -> Interp Value
freezeValue v = do
  st <- get
  imm <- isImmutableValue st.sHeap v
  if imm
    then pure v
    else case v of
      VArray addrs -> do
        vals <- forM addrs $ \a ->
          maybe (error $ T.unpack $ "Undead address: " <> pretty a) freezeValue $ deref st.sHeap a
        VArray <$> mapM alloc vals
      VPair l r -> do
        lVal <- maybe (error $ T.unpack $ "Undead address in pair left: " <> pretty l) freezeValue $ deref st.sHeap l
        rVal <- maybe (error $ T.unpack $ "Undead address in pair right: " <> pretty r) freezeValue $ deref st.sHeap r
        VPair <$> alloc lVal <*> alloc rVal
      VRecord eid -> do
        env <- getEnv eid
        env' <- forM (Map.toList env.bindings) $ \(name, (m, addr)) -> do
          val <- maybe (error $ T.unpack $ "Undead address: " <> pretty addr) freezeValue $ deref st.sHeap addr
          newAddr <- alloc val
          pure (name, (freezeMutability m, newAddr))
        VRecord <$> newEnv Env {
          bindings = Map.fromList env',
          parent = Nothing
        }
      VThunk expr eid -> VThunk (freeze expr) <$> snapshot eid st.sHeap (freeVars expr)
      other -> pure other

freeVars :: TypedExpr -> Set Text
freeVars = \case
  TEXVar n _ -> Set.singleton n
  TEArray _ es -> Set.unions (map freeVars es)
  TEPair l r -> Set.union (freeVars l) (freeVars r)
  TEXLambda lam ->
    let bodyFV = freeVarsBlock lam.lBlock
    in Set.delete lam.lArg bodyFV  -- аргумент связан
  TEApply f x -> Set.union (freeVars f) (freeVars x)
  TERecord _ props -> Set.unions [freeVars (terExpr p) | p <- props]
  TEHandle handler _ -> freeVarsHandler handler
  TEParen b -> freeVarsBlock b
  TEResume e _ -> freeVars e
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
--   (привязки последовательны и не рекурсивны).
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

matchPattern :: LetPattern -> Address -> Interp [(Text, Mutability, Address)]
matchPattern pat addr = do
  st <- get
  case deref st.sHeap addr of
    Just v -> case pat of
      LPATom (ALPUnderscore; ALPNil) -> pure []
      LPATom (ALPPair l r) -> case v of
        VPair addrL addrR -> do
          bindL <- matchPattern l addrL
          bindR <- matchPattern r addrR
          pure (bindL <> bindR)
        _ -> error "Let pattern mismatch: expected pair"
      LPATom (ALPRecord props) -> case v of
        VRecord eid -> do
          env <- getEnv eid
          foldM (\acc (LetPatternRecordProp m (LambdaParam n _) mPat) -> do
              case getRef env n of
                Just fieldAddr -> do
                  case mPat of
                    Nothing -> pure $ (n, m, fieldAddr) : acc
                    Just subPat -> do
                      subBindings <- matchPattern (LPATom subPat) fieldAddr
                      pure $ acc <> subBindings
                Nothing -> error $ "Record missing field: " <> show n
            ) [] props
        _ -> error "Let pattern mismatch: expected record"
      LPParam (LambdaParam n _) -> pure [(n, Val, addr)]
    _ -> error "Undead address in let pattern"

isImmutableValue :: Heap -> Value -> Interp Bool
isImmutableValue h = \case
  VArray addrs -> foldM (\t -> \case
      Just v -> (&&) t <$> isImmutableValue h v
      Nothing -> pure False
    ) True $ map (deref h) addrs

  VPair l r -> do
    lImm <- maybe (pure False) (isImmutableValue h) $ deref h l
    rImm <- maybe (pure False) (isImmutableValue h) $ deref h r
    pure $ lImm && rImm

  VRecord eid -> do
    env <- getEnv eid
    foldM (\t (mut, addr) -> do
        if mut == Var
          then pure False
          else case deref h addr of
            Just v -> (&&) t <$> isImmutableValue h v
            Nothing -> pure False
      ) True (Map.elems env.bindings)

  VBottom; VThunk _ _ -> pure False
  _ -> pure True

isPureClosure :: EffRow -> Bool
isPureClosure (RClosed []) = True
isPureClosure (ROpen [] _) = True  -- открытый ряд без эффектов
isPureClosure _ = False