{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

-- | Reading a program that is more than one file.
--
--   A module is one file, and @import@ names another.  The loader reads the
--   files, works out which module each import means, and gives every module two
--   tables: the names it sees and the names it offers.  After that the front end
--   works on resolved modules and never touches the file system.
--
--   Four decisions shape the code:
--
--   * A module's name is not its file name.  @import a@ looks for @a.marr@, and
--     the @module@ header of that file may say anything.  The path identifies a
--     module; the header's name is what a diagnostic quotes.
--
--   * Modules that import each other form one unit.  A cycle cannot be read in
--     dependency order, so the whole cycle is resolved at once, as a fixed
--     point: a module offers its own declarations immediately and everything its
--     imports offer as they settle.
--
--   * A name is resolved to the module that declares it, through any number of
--     re-exports.  In a chain @C -> B -> A@, @C@ gets the name as @A@ offers it,
--     so a name @B@ did not export can never leak through @B@.
--
--   * A module sees its own declarations and its imports, and nothing else.
--     Two modules may each have a private @helper@; they are different names,
--     because each has a table of its own.
module Loader (
    LoadError(..)
  , loadProgram
  , loadText
  , searchCandidates
  ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Text (Text)
import Data.List (nub)
import Data.Maybe (fromMaybe)
import qualified Data.Graph as Graph
import Data.Graph (SCC(..))
import System.Directory (doesFileExist)
import System.FilePath (takeDirectory, (</>), normalise, isAbsolute)

import qualified Ast
import Ast (Chunk)
import Builtins (Builtin(..), BuiltinKind(..), builtins, moduleNames)
import Module
import Parser (chunk, parseFromTextNamed)
import Span (Span, noSpan)

-- | A failure of the loader.  The message is the text a reader sees and the
--   span says where in which file, so the renderer can quote the line.
data LoadError = LoadError {
    leSpan    :: Span
  , leMessage :: Text
  , leNotes   :: [Text]
  } deriving (Show)

-- | Where an import takes its names from.
data Source =
    -- | A file, by the path the loader gave it.
    SrcModule FilePath
    -- | A native module.  The empty name is @import @native@ with no module:
    --   the whole native scope.
  | SrcNative Text
  deriving (Eq, Show)

-- | One import after the file it names was found.
data Import = Import {
    iSpan   :: Span
  , iSource :: Source
  , iNames  :: Maybe [ExportDecl]
  } deriving (Show)

-- | One module of the graph while the loader works on it.
data Node = Node {
    nPath      :: FilePath
  , nSource    :: Text
  , nChunk     :: Chunk
  , nImports   :: [Import]
    -- | The names this module offers to an importer.
  , nPublished :: Table
    -- | The names this module sees.
  , nVisible   :: Table
  } deriving (Show)

-- ---------------------------------------------------------------------------
-- Reading
-- ---------------------------------------------------------------------------

-- | Read a program from a file.
loadProgram :: FilePath -> IO (Either LoadError (Program Ast.TopLevelStat))
loadProgram path = do
  exists <- doesFileExist path
  if not exists
    then pure $ Left $ LoadError noSpan (T.concat ["cannot read `", T.pack path, "`"]) []
    else TIO.readFile path >>= loadText path

-- | Read a program whose first module is already in memory.
--
--   Tests write their program in a string; the imports it names are still read
--   from disk, because a program that imports a module must see the same file a
--   reader would.
loadText :: FilePath -> Text -> IO (Either LoadError (Program Ast.TopLevelStat))
loadText path src =
  case parseFromTextNamed path chunk src of
    Left e -> pure $ Left $ LoadError noSpan (T.pack e) []
    Right c -> do
      graph <- readGraph (normalise path) src c
      pure $ graph >>= resolveGraph (normalise path)

-- | The files an import may mean, in the order they are tried.
--
--   A module next to its importer wins, so a program can carry its own library;
--   the bundled directories are the fallback, which keeps @--run@ working from
--   a build directory as well as from the repository root.  A name with a
--   separator is a path the writer chose, so it is looked up next to the
--   importer and as written only: adding @app/marr@ to a deliberate path would
--   be guessing.
searchCandidates :: FilePath -> Text -> [FilePath]
searchCandidates importer name =
  nub [ dir </> file | dir <- dirs, dir /= "" ]
  where
    file = T.unpack name <> ".marr"
    named = T.unpack name
    deliberate = isAbsolute named || any (`elem` ("/\\" :: String)) named
    here = takeDirectory importer
    dirs
      | deliberate = [here, "."]
      | otherwise = here : "." : bundled
    bundled = ["app/marr", "app", "../app/marr", "../app", "../../app/marr", "../../app"]

-- | The imports of a chunk, with the directory nesting already pushed into the
--   module names.
writtenImports :: Chunk -> [(Span, Bool, [(Text, Maybe [ExportDecl])])]
writtenImports c =
  [ (idSpan i, idNative i, unitsOf i)
  | i <- mhImports (Ast.modHeader c)
  ]
  where
    unitsOf i = case idUnit i of
      -- `import @native` alone: one nameless unit, which the source lookup
      -- reads as the whole native scope.
      Nothing -> [("", Nothing)]
      Just u -> importUnitsRaw u

importUnitsRaw :: ImportUnit -> [(Text, Maybe [ExportDecl])]
importUnitsRaw = \case
  ImportModule n names -> [(n, names)]
  ImportDir d us -> concatMap (map (\(n, names) -> (d <> n, names)) . importUnitsRaw) us

readGraph :: FilePath -> Text -> Chunk -> IO (Either LoadError (Map FilePath Node))
readGraph mainPath mainSource mainChunk =
  go (Map.singleton mainPath (Node mainPath mainSource mainChunk [] Map.empty Map.empty)) [mainPath]
  where
    go nodes [] = pure $ Right nodes
    go nodes (p : rest) = case Map.lookup p nodes of
      Nothing -> go nodes rest
      Just n -> do
        step <- readImports nodes (nPath n) (writtenImports (nChunk n))
        case step of
          Left e -> pure $ Left e
          Right (nodes', planned, added) ->
            go (Map.insert p (n {nImports = planned}) nodes') (rest <> added)

    readImports nodes _ [] = pure $ Right (nodes, [], [])
    readImports nodes importer ((sp, native, units) : rest) = do
      sources <- traverse (sourceOf importer sp native) units
      case sequence sources of
        Left e -> pure $ Left e
        Right srcs -> do
          loaded <- loadAll nodes [ p | SrcModule p <- srcs ]
          case loaded of
            Left e -> pure $ Left e
            Right (nodes', added) -> do
              step <- readImports nodes' importer rest
              case step of
                Left e -> pure $ Left e
                Right (nodes'', planned, more) ->
                  pure $ Right
                    ( nodes''
                    , [ Import sp src names | (src, (_, names)) <- zip srcs units ] <> planned
                    , nub (added <> more)
                    )

    -- A native import names no file.
    sourceOf importer sp native (name, _)
      | native = pure $ Right $ SrcNative name
      -- An import that names no module and is not native cannot happen: the
      -- parser only allows a bare import after `@native`.
      | T.null name = pure $ Right $ SrcNative ""
      | otherwise = do
          let candidates = searchCandidates importer name
          found <- firstExisting candidates
          case found of
            Nothing -> pure $ Left $ LoadError sp (T.concat [
                "cannot find the module `", name, "`"
              ]) [ "looked for: " <> T.intercalate ", " (map T.pack candidates) ]
            Just path -> pure $ Right $ SrcModule (normalise path)

    loadAll nodes [] = pure $ Right (nodes, [])
    loadAll nodes (p : ps)
      | Map.member p nodes = loadAll nodes ps
      | otherwise = do
          src <- TIO.readFile p
          case parseFromTextNamed p chunk src of
            Left e -> pure $ Left $ LoadError noSpan (T.pack e) []
            Right c -> do
              let chunkSource = src
              step <- loadAll (Map.insert p (Node p chunkSource c [] Map.empty Map.empty) nodes) ps
              pure $ fmap (\(ns, added) -> (ns, p : added)) step

firstExisting :: [FilePath] -> IO (Maybe FilePath)
firstExisting [] = pure Nothing
firstExisting (p : ps) = do
  ok <- doesFileExist p
  if ok then pure (Just p) else firstExisting ps

-- ---------------------------------------------------------------------------
-- Resolving
-- ---------------------------------------------------------------------------

-- | The strong components of the import graph, dependencies first.
--
--   `stronglyConnComp` answers in dependency order, so a component comes after
--   everything it imports; that is the order the tables are settled in and the
--   order the front end checks them in.
resolveGraph :: FilePath -> Map FilePath Node -> Either LoadError (Program Ast.TopLevelStat)
resolveGraph entry nodes = do
  -- Only `module Main` is a program.  A file that names itself otherwise is a
  -- library, and running it would mean running something the writer wrote to be
  -- imported; saying so is better than finding no `main` and starting anyway.
  case Map.lookup entry nodes of
    Just n | Ast.mhName (Ast.modHeader (nChunk n)) /= "Main" ->
      Left $ LoadError (Ast.mhSpan (Ast.modHeader (nChunk n))) (T.concat [
          "`", Ast.mhName (Ast.modHeader (nChunk n)),
          "` is a library, not a program: a file that is run must say `module Main`"
        ]) []
    _ -> pure ()
  settled <- foldlM settleComponent nodes comps
  pure $ Program
    (map (unitOf settled) comps)
    (Map.toList (Map.map nSource settled))
    entry
  where
    comps = Graph.stronglyConnComp
      [ (p, p, deps n) | (p, n) <- Map.toList nodes ]
    deps n = [ p | Import _ (SrcModule p) _ <- nImports n ]

members :: SCC a -> [a]
members = \case
  AcyclicSCC p -> [p]
  CyclicSCC ps -> ps

-- | One unit of checking.
--
--   A module alone is a unit of its own.  The modules of a cycle share a unit,
--   because their type-level declarations have to be read together, but each
--   keeps its own tables and its own declarations.
unitOf :: Map FilePath Node -> SCC FilePath -> Unit Ast.TopLevelStat
unitOf nodes comp = Unit paths [ (p, settledModule (nodes Map.! p)) | p <- paths ]
  where
    paths = members comp

settledModule :: Node -> Module Ast.TopLevelStat
settledModule n = (nChunk n) {
    modHeader = (Ast.modHeader (nChunk n)) {
        mhResolved = nVisible n
      , mhPublished = nPublished n
      }
  }

-- | Settle the tables of one component.  A single module reads its imports from
--   the tables earlier components already settled; a cycle grows its own tables
--   until they stop changing, then the strict pass reports what never appeared.
settleComponent ::
     Map FilePath Node
  -> SCC FilePath
  -> Either LoadError (Map FilePath Node)
settleComponent nodes comp = do
  let paths = members comp
      -- Tables of the modules settled so far.  `Map.union` below is left-biased,
      -- so a member's own grown table wins over the stale one in `nodes`.
      known = Map.map nPublished nodes
      start = Map.fromList [ (p, declaredTable nodes p) | p <- paths ]
      grown = grow nodes paths (Map.union start known)
      tables = Map.union grown known
  published <- foldlM (\t p -> do
                  pub <- strictPublish nodes tables p
                  pure $ Map.insert p pub t) Map.empty paths
  let allTables = Map.union published tables
  visible <- foldlM (\t p -> do
                vis <- strictVisible nodes allTables p
                pure $ Map.insert p vis t) Map.empty paths
  pure $ foldl' (\ns p -> case (Map.lookup p published, Map.lookup p visible) of
      (Just pub, Just vis) ->
        Map.adjust (\n -> n {nPublished = pub, nVisible = vis}) p ns
      _ -> ns) nodes paths

-- | The names a module declares: every top-level name and its kind.  The
--   constructors of an enum are values of the module's scope, so they travel
--   with it.
declaredTable :: Map FilePath Node -> FilePath -> Table
declaredTable nodes p = Map.fromList
  [ (name, Imported (FromModule p) name k)
  | (name, k) <- declared (nChunk (nodes Map.! p)) ]

declared :: Chunk -> [(Text, DeclKind)]
declared c = concatMap one (Ast.modDecls c)
  where
    one stat = (Ast.topLevelName stat, Ast.declKindOf stat)
             : case stat of
                 Ast.EnumDef _ _ _ cases -> [ (caseName ec, KindFunct) | ec <- cases ]
                 _ -> []
    caseName (Ast.EnumCase n _) = n

-- | The constructors of each enumeration a file declares.
--
--   A table keyed by name cannot answer \"which values belong to this enum\":
--   the constructors are ordinary entries of it, and nothing in an entry says
--   which declaration it came from.  This map is that relation, and it is what
--   lets a list naming `enum Colour` bring `Red` and `Green` along with the
--   type -- a type whose values cannot be written is not much of an export.
type Enums = Map FilePath (Map Text [Text])

enumsOf :: Map FilePath Node -> Enums
enumsOf nodes = Map.map enumsOfChunk nodes

enumsOfChunk :: Node -> Map Text [Text]
enumsOfChunk n = Map.fromList
  [ (Ast.topLevelName stat, map caseName cases)
  | stat@(Ast.EnumDef _ _ _ cases) <- Ast.modDecls (nChunk n)
  ]
  where
    caseName (Ast.EnumCase c _) = c

-- | The constructors one name brings when it denotes an enumeration.
--
--   `Nothing` for a name that is not an enum, so a caller can treat the answer
--   as \"nothing extra\" without a second lookup.
constructorsOf :: Enums -> ImportOrigin -> Text -> [Text]
constructorsOf enums origin name = case origin of
  FromNative _ -> []
  FromModule p -> Map.findWithDefault [] name (Map.findWithDefault Map.empty p enums)

-- | The names a native module offers.  `@native` with no module is the whole
--   native scope, which is what the test preamble and a program that wants the
--   library without naming every module import.
nativeTable :: Text -> Either LoadError Table
nativeTable m
  | T.null m = Right $ Map.fromList
      [ (bName b, Imported (FromNative "") (bName b) (nativeKind b)) | b <- builtins ]
  | null names =
      Left $ LoadError noSpan (T.concat ["there is no native module `", m, "`"])
        [ "native modules: " <> T.intercalate ", " moduleNames ]
  | otherwise = Right $ Map.fromList
      [ (n, Imported (FromNative m) n k) | (n, k) <- names ]
  where
    names = [ (bName b, nativeKind b) | b <- builtins, bModule b == m ]

nativeKind :: Builtin -> DeclKind
nativeKind b = case bKind b of
  Op _ -> KindEffect
  Native -> KindFunct

-- | An import with its names looked up in the table of its source.  A name the
--   source does not offer is 'Nothing': during the growth of a cycle the source
--   may not have settled yet, and the strict pass reports the ones that never
--   appear.
resolveImport :: Enums -> Map FilePath Table -> Import -> [(Text, Maybe Imported)]
resolveImport enums tables i = case iSource i of
  SrcNative m -> case nativeTable m of
    Left _ -> [ (name, Nothing) | name <- listed ]
    Right t -> keep t
  SrcModule p -> keep (Map.findWithDefault Map.empty p tables)
  where
    listed = maybe [] (map edName) (iNames i)

    -- A bare import brings the source's whole table, which already holds the
    -- constructors of its enumerations; there is nothing to expand.  A list of
    -- names is where an enumeration turns into its values.
    keep t = case iNames i of
      Nothing -> [ (n, Just imp) | (n, imp) <- Map.toList t ]
      Just decls -> withConstructors enums (map edName decls)
        [ (localOf ed, Map.lookup (edName ed) t) | ed <- decls ]

-- | A name list with the constructors of every enumeration in it.
--
--   Naming an enum names its values: a file that writes `Colour` in a signature
--   and `#Red` in a pattern must be able to write `Red` in an expression, or
--   the type it imported is one it cannot use.  A constructor keeps its
--   declared name even when the type was renamed with `as`, because the two
--   live in different namespaces and `<new name>.Red` is not a spelling the
--   language has.
--
--   The second argument is the names the list writes by itself.  A constructor
--   the list already mentions is left to that entry: `[enum Colour funct Red as
--   Crimson]` asks for `Red` under another name, and adding the declared `Red`
--   as well would undo the rename.  This is also the way out of a clash between
--   two enums that both have a `Red`.
withConstructors :: Enums -> [Text] -> [(Text, Maybe Imported)] -> [(Text, Maybe Imported)]
withConstructors enums spelled = concatMap one
  where
    one (local, Nothing) = [(local, Nothing)]
    one (local, Just imp) = [ (n, Just i) | (n, i) <- entriesOf enums spelled (local, imp) ]

-- | The table entries one name of a list brings.  The same rule as
--   'withConstructors', for a name that is known to exist.
entriesOf :: Enums -> [Text] -> (Text, Imported) -> [(Text, Imported)]
entriesOf enums spelled (local, imp) =
  [ (n, i) | (n, i) <- enumValues enums local imp, n == local || n `notElem` spelled ]

-- | One entry of a name list, together with the values an enum brings.
--
--   A constructor is a value of the enumeration's module: its declared name is
--   the constructor's, and its kind is 'KindFunct', so an importer adds it as a
--   function and two constructors of one name still clash as two values.
enumValues :: Enums -> Text -> Imported -> [(Text, Imported)]
enumValues enums local imp =
  (local, imp) : [ (c, ctor c) | c <- constructorsOf enums (imOrigin imp) (imName imp) ]
  where
    ctor c = imp {imName = c, imKind = KindFunct}

localOf :: ExportDecl -> Text
localOf ed = fromMaybe (edName ed) (edAlias ed)

-- | The table a module offers, as far as the tables known so far allow.  A name
--   its export list asks for and nothing provides is dropped, not reported: the
--   strict pass does the reporting once the whole component has settled.
publishOf :: Map FilePath Node -> Map FilePath Table -> FilePath -> Table
publishOf nodes tables p = case mhExports (Ast.modHeader (nChunk n)) of
    Nothing -> Map.union imported own
    Just decls -> Map.fromList
      [ entry
      | ed <- decls
      , Just imp <- [Map.lookup (edName ed) (Map.union own imported)]
      , entry <- entriesOf (enumsOf nodes) (map edName decls) (localOf ed, imp)
      ]
  where
    n = nodes Map.! p
    own = declaredTable nodes p
    imported = foldl' add Map.empty (nImports n)
    add acc i = foldl' (\t (local, imp) -> maybe t (\i' -> Map.insert local i' t) imp)
                  acc (resolveImport (enumsOf nodes) tables i)

-- | The table a module offers, once its component has settled: an export list
--   that names nothing the module has is an error here.
strictPublish :: Map FilePath Node -> Map FilePath Table -> FilePath -> Either LoadError Table
strictPublish nodes tables p = case mhExports (Ast.modHeader (nChunk n)) of
    Nothing -> pure $ Map.union own imported
    Just decls -> Map.fromList . concat <$> traverse select decls
  where
    n = nodes Map.! p
    own = declaredTable nodes p
    spelled = map edName (fromMaybe [] (mhExports (Ast.modHeader (nChunk n))))
    imported = foldl' add Map.empty (nImports n)

    add acc i = foldl' (\t (local, imp) -> maybe t (\i' -> Map.insert local i' t) imp)
                  acc (resolveImport (enumsOf nodes) tables i)

    select ed = case Map.lookup (edName ed) (Map.union own imported) of
      Nothing -> Left $ LoadError (edSpan ed) (T.concat [
          "`", edName ed, "` is not declared or imported here, so it cannot be exported"
        ]) [ available ]
      Just imp -> Right (entriesOf (enumsOf nodes) spelled (localOf ed, imp))
      where
        available = case Map.keys (Map.union own imported) of
          [] -> "this module declares and imports nothing"
          names -> "the module declares or imports: " <> T.intercalate ", " names

-- | The table a module sees: everything it imports, with two imports of one
--   name reported.
--
--   A declaration of the module itself wins over an import of the same name, so
--   a shadowed import is dropped rather than reported: a module that redefines
--   `+` still sees its own `+`, and the reader does not have to rename the
--   import to say so.  The tables of the module's own declarations are kept
--   apart ('declaredTable'), because the checker registers them itself; this
--   table is only what came from outside.
strictVisible :: Map FilePath Node -> Map FilePath Table -> FilePath -> Either LoadError Table
strictVisible nodes tables p = do
  imported <- foldlM add Map.empty (nImports n)
  pure $ Map.withoutKeys imported (Map.keysSet own)
  where
    n = nodes Map.! p
    own = declaredTable nodes p

    add acc i = foldlM (insertImport (iSpan i)) acc
                      (resolveImport (enumsOf nodes) tables i)

insertImport :: Span -> Table -> (Text, Maybe Imported) -> Either LoadError Table
insertImport _ acc (_, Nothing) = Right acc
insertImport sp acc (local, Just imp) = case Map.lookup local acc of
    -- The same declaration named twice -- a constructor reached both through
    -- its enum and by its own name -- is one name, not a clash.
    Just other | other == imp -> Right acc
    Nothing -> Right $ Map.insert local imp acc
    Just other
      | namespaceOf (imKind other) == namespaceOf (imKind imp) ->
          Left $ LoadError sp (T.concat [
              "two imports bring `", local, "`: ", describe other, " and ", describe imp
            ]) [ "write `as` in one of the import lists to keep both names" ]
      | otherwise -> Right acc
  where
    describe i = T.concat [quote (imOrigin i), " (", kindName (imKind i), ")"]
    quote = \case
      FromModule path -> T.pack (baseName path)
      FromNative m | T.null m -> "@native"
      FromNative m -> T.concat ["@native ", m]

baseName :: FilePath -> String
baseName = reverse . takeWhile (`notElem` ("/\\" :: String)) . reverse

kindName :: DeclKind -> Text
kindName = \case
  KindFunct  -> "a function"
  KindType   -> "a type"
  KindEffect -> "an effect"
  KindRow    -> "a row"
  KindEnum   -> "an enumeration"

-- | Grow the tables of a cycle until they stop changing.  Every step only adds
--   names, so the loop settles after at most as many rounds as there are names.
--
--   The grown tables are unioned with the ones already known: a cycle's table is
--   what its own modules offer, and the modules that were settled before it must
--   stay in the map, because a member imports from them as well as from its
--   neighbours.
grow :: Map FilePath Node -> [FilePath] -> Map FilePath Table -> Map FilePath Table
grow nodes paths start = go (0 :: Int) start
  where
    budget = 2 + sum [ Map.size t | t <- Map.elems start ]
               + sum [ length (declared (nChunk (nodes Map.! p))) | p <- paths ]
    go n current
      | n > budget = current
      | otherwise =
          let next = Map.union
                (Map.fromList [ (p, publishOf nodes current p) | p <- paths ])
                current
          in if next == current then current else go (n + 1) next

foldlM :: (b -> a -> Either e b) -> b -> [a] -> Either e b
foldlM _ acc [] = Right acc
foldlM f acc (x : xs) = case f acc x of
  Left e -> Left e
  Right acc' -> foldlM f acc' xs
