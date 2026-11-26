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
import System.FilePath (takeDirectory, (</>), normalise, isAbsolute, dropExtension)

import qualified Ast
import Ast (Chunk)
import Builtins (Builtin(..), BuiltinKind(..), builtins, moduleNames)
import Module
import Parser (chunk, parseFromTextNamed)
import Qualified (UseKind(..), QualUse(..), qualUses, mapQualified)
import Span (Span, noSpan)
import Utils (splitQualified, qualifyName)
import qualified Suggest

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
  -- Qualification is the last step of settling: it reads the published table
  -- of every imported module, which is only now final, and the visible table of
  -- the module itself, which says what an import actually reached.
  let info = ModuleInfo nodes allTables (enumsOf nodes) (effectsOf nodes)
  qualified <- foldlM (\t p -> do
                  chunk' <- qualifyNode info (visible Map.! p) (nodes Map.! p)
                  pure $ Map.insert p chunk' t) Map.empty paths
  pure $ foldl' (\ns p -> case (Map.lookup p published, Map.lookup p visible, Map.lookup p qualified) of
      (Just pub, Just vis, Just chunk') ->
        Map.adjust (\n -> n {nPublished = pub, nVisible = vis, nChunk = chunk'}) p ns
      _ -> ns) nodes paths

-- ---------------------------------------------------------------------------
-- Qualified names
-- ---------------------------------------------------------------------------

-- | Everything a qualified name may need to see.
data ModuleInfo = ModuleInfo {
    miNodes   :: Map FilePath Node
  , miTables  :: Map FilePath Table
  , miEnums   :: Enums
    -- | The operations each effect declares, per module.  An operation is not
    --   a top-level name: it travels with its effect, so the published table
    --   cannot answer `M::op` on its own.
  , miEffects :: Map FilePath (Map Text [Text])
  }

-- | The effects each module declares, and the operations of each.
effectsOf :: Map FilePath Node -> Map FilePath (Map Text [Text])
effectsOf nodes = Map.map ofNode nodes
  where
    ofNode n = Map.fromList
      [ (name, [ op | Ast.EffectOp op _ <- ops ])
      | Ast.EffectDef _ name _ ops <- Ast.modDecls (nChunk n)
      ]

-- | What a resolved qualified name asks the file to do with the spelling.
--
--   A value keeps its spelling and becomes a binding of its own; every other
--   namespace is resolved here and the syntax tree carries the local name.
data Decision = Decision {
    dRewrite :: Maybe Text
  , dAlias   :: Maybe QualifiedAlias
  }

-- | A declaration a qualified name can name.
data Target =
    TableTarget Imported
    -- | An operation, and the effect that declares it as the source offers it.
    --   The operation's own name is the one the use writes.
  | OpTarget Text Imported

-- | The spellings a file may use for the modules it imports.
--
--   A module answers to its header's name and to the name of its file: the
--   header is what it calls itself, the file name is what `import` writes, and
--   a reader may have either in mind.
importedSpellings :: Map FilePath Node -> Node -> [(Text, Source)]
importedSpellings nodes n = nub
  [ (spelling, src)
  | i <- nImports n
  , (spelling, src) <- spellings (iSource i)
  ]
  where
    spellings = \case
      -- `import @native` is the whole native scope, so every native module is
      -- a name it can be asked about.  The source of a spelling is still the
      -- one module that actually offers the name: `@native` brings `sayn`, but
      -- `Numbers::sayn` must be told that `Numbers` does not offer it.
      SrcNative m | T.null m -> [ (x, SrcNative x) | x <- moduleNames ]
      SrcNative m -> [(m, SrcNative m)]
      SrcModule p -> case Map.lookup p nodes of
        Nothing -> []
        Just src -> [ (s, SrcModule p)
                    | s <- nub
                        [ Ast.mhName (Ast.modHeader (nChunk src))
                        , T.pack (dropExtension (baseName p))
                        ] ]

-- | Resolve every qualified name in one module and record what it found.
qualifyNode :: ModuleInfo -> Table -> Node -> Either LoadError Chunk
qualifyNode info visible n = do
  let header = Ast.modHeader thisChunk
  decisions <- foldlM decide Map.empty (qualUses thisChunk)
  let (chunk', _) = mapQualified
        (\_ kind name -> Map.lookup (kind, name) decisions >>= dRewrite)
        thisChunk
      -- One spelling can be used in more than one namespace: `M::Some` is a
      -- value in an expression and a constructor in a pattern, and the two
      -- decisions describe the same binding.  Keeping one alias per qualified
      -- spelling and local name is what lets the checker add it once.
      aliases = Map.map nondescript $ Map.fromListWith (<>)
        [ (name, [alias])
        | ((_, name), d) <- Map.toList decisions
        , Just alias <- [dAlias d]
        ]
  pure chunk' { Ast.modHeader = header {mhQualified = aliases} }
  where
    nondescript = foldr keep []
    keep a acc
      | any (same a) acc = acc
      | otherwise = a : acc
    same a b = qaLocal a == qaLocal b
            && qaKind a == qaKind b
            && qaOrigin a == qaOrigin b
            && qaName a == qaName b
    thisChunk = nChunk n
    sources = importedSpellings (miNodes info) n

    decide acc (QualUse name sp kind)
      | Map.member (kind, name) acc = pure acc
      | otherwise = do
          d <- resolveUse info visible (nImports n) sources sp kind name
          pure $ Map.insert (kind, name) d acc

-- | Resolve one qualified spelling in the namespace its position implies.
resolveUse ::
     ModuleInfo
  -> Table
  -> [Import]
  -> [(Text, Source)]
  -> Span
  -> UseKind
  -> Text
  -> Either LoadError Decision
resolveUse info visible imports sources sp kind q = do
  (m, x) <- case splitQualified q of
    Just pair -> pure pair
    Nothing -> qualError sp (T.concat ["`", q, "` is not a qualified name"]) []
  src <- findSource m
  offer <- offeredTable src
  target <- findTarget m x src offer
  case target of
    TableTarget imp
      | kind == UseValue -> do
          local <- localSpelling info visible imports src sp m x x imp
          pure $ Decision Nothing (Just $ alias local Nothing imp)
      | kind == UseCtor -> do
          local <- localSpelling info visible imports src sp m x x imp
          en <- constructorEnum info visible sp m x imp
          -- A pattern is matched against the constructor's declared name, so
          -- the spelling is rewritten rather than aliased: the tag a value
          -- carries is the declared one, not the one this file imported it
          -- under.
          pure $ Decision (Just (imName imp)) (Just $ alias local en imp)
      | otherwise -> do
          local <- localSpelling info visible imports src sp m x x imp
          pure $ Decision (Just local) Nothing
    OpTarget offered imp -> do
      -- An operation keeps its name; the effect is what an import brings and
      -- what makes the operation reachable.
      _ <- localSpelling info visible imports src sp m offered offered imp
      pure $ Decision (Just x) Nothing
  where
    findSource m =
      case nub [s | (spelling, s) <- sources, spelling == m] of
        [] -> Left $ notImportedModule sp m (writtenNames)
        [s] -> Right s
        _ -> qualError sp
          (T.concat ["`", m, "` names more than one imported module"])
          ["import the two modules by different paths, or name one with `as`"]

    -- What the file itself wrote after `import`, for a reader who is told a
    -- module is missing.  The expanded spellings of `@native` would name every
    -- native module; the import is one line, and the note should quote it.
    writtenNames = nub $ concatMap written imports
    written i = case iSource i of
      SrcNative m | T.null m -> ["@native"]
      SrcNative m -> [m]
      SrcModule p -> case Map.lookup p (miNodes info) of
        Nothing -> [T.pack (dropExtension (baseName p))]
        Just src -> nub
          [ Ast.mhName (Ast.modHeader (nChunk src))
          , T.pack (dropExtension (baseName p))
          ]

    offeredTable = \case
      SrcNative m' -> nativeTable m'
      SrcModule p -> Right $ Map.findWithDefault Map.empty p (miTables info)

    alias local en imp = QualifiedAlias
      { qaLocal = local
      , qaKind = imKind imp
      , qaOrigin = imOrigin imp
      , qaName = imName imp
      , qaEnum = en
      , qaOp = Nothing
      }

    -- The entries of the source's published table, and the operations its
    -- effects declare.
    findTarget m x src offer = case kind of
      UseValue -> case values of
        (imp : _) -> pure (TableTarget imp)
        [] -> operations
      UseCtor -> case [imp | imp <- entries, imKind imp == KindFunct] of
        (imp : _) -> pure (TableTarget imp)
        [] -> missing
      UseType -> tableTarget [imp | imp <- entries, imKind imp `elem` [KindType, KindEnum]]
      UseEffect -> case effectsOfSource of
        (imp : _) -> pure (TableTarget imp)
        [] -> missing
      UseRow -> tableTarget [imp | imp <- entries, imKind imp == KindRow]
      UseOp -> case nativeOps of
        (imp : _) -> pure (TableTarget imp)
        [] -> operations
      where
        entries = Map.findWithDefault [] x offer
        values = [ imp | imp <- entries, imKind imp == KindFunct ]
              <> nativeOps
        nativeOps =
          [ imp | imp <- entries
                , imKind imp == KindEffect
                , nativeOrigin (imOrigin imp) ]
        effectsOfSource =
          [ imp | imp <- entries
                , imKind imp == KindEffect
                , not (nativeOrigin (imOrigin imp)) ]

        tableTarget imps = case imps of
          (imp : _) -> pure (TableTarget imp)
          [] -> missing

        missing
          | null entries = Left $ notOffered info src sp m x offer
          | otherwise = Left $ kindMismatch sp m x entries kind

        -- A use of an operation is the one case where the name is not in the
        -- table: an operation belongs to its effect, and only the effect is
        -- exported.  The effect must still be one this file imported, which
        -- `localSpelling` checks.
        operations = case src of
          SrcNative _ -> missing
          SrcModule _ -> case
            [ (offered, imp)
            | (offered, imps) <- Map.toList offer
            , imp <- imps
            , imKind imp == KindEffect
            , FromModule p <- [imOrigin imp]
            , x `elem` Map.findWithDefault [] (imName imp)
                          (Map.findWithDefault Map.empty p (miEffects info))
            ] of
              [] -> missing
              [(offered, imp)] -> pure (OpTarget offered imp)
              _ -> qualError sp (T.concat [
                  "`", x, "` is an operation of more than one effect of `", m, "`"
                ]) ["name the effect in a row, or handle it"]

-- | The local spelling of a declaration an import brought, or why it did not.
localSpelling ::
     ModuleInfo
  -> Table
  -> [Import]
  -> Source
  -> Span
  -> Text
  -> Text
  -> Text
  -> Imported
  -> Either LoadError Text
localSpelling info visible imports src sp m written offered imp =
  case nub present of
    [] -> case nub reconstructed of
      [] -> qualError sp (T.concat [
          "`", written, "` is offered by `", m, "` but not imported here"
        ]) [T.concat ["name it in the import list of `", m, "`"]]
      locals -> qualError sp (T.concat [
          "`", written, "` from `", m, "` is shadowed by a declaration of ",
          T.intercalate " or " [T.concat ["`", l, "`"] | l <- locals], " here"
        ]) [ "a qualified name does not reach an import that a declaration shadows"
             , "rename the import with `as`, or use the declaration's own spelling" ]
    [local] -> pure local
    locals
      | offered `elem` locals -> pure offered
      | otherwise -> qualError sp (T.concat [
          "`", written, "` from `", m, "` is imported under more than one name: ",
          T.intercalate ", " locals
        ]) ["keep one spelling in the import list"]
  where
    present = [local | (local, i) <- tableEntries visible, i == imp]
    -- What the imports would have brought, had nothing shadowed it.  Running
    -- the same resolution the visible table was built from says which local
    -- name the declaration had in mind.
    reconstructed =
      [ local
      | i <- imports
      , iSource i == src
      , (local, Just imp') <- resolveImport (miEnums info) (miTables info) i
      , imp' == imp
      ]

-- | The enumeration a constructor belongs to, as this file spells it.
--
--   A pattern needs the declaration to know the fields and the cases, so a
--   constructor whose enumeration was not imported cannot be matched -- even
--   when the constructor itself was imported by name.
constructorEnum ::
     ModuleInfo -> Table -> Span -> Text -> Text -> Imported
  -> Either LoadError (Maybe Text)
constructorEnum info visible sp m x imp = case imOrigin imp of
  FromNative _ -> qualError sp
    (T.concat ["`", x, "` is a native value, not a constructor"]) []
  FromModule p ->
    case [ e
         | (e, cs) <- Map.toList (Map.findWithDefault Map.empty p (miEnums info))
         , imName imp `elem` cs ] of
      [] -> qualError sp (T.concat [
          "`", x, "` is not a constructor of `", m, "`"
        ]) ["a `#` pattern names a constructor"]
      (e : _) -> case
        nub [ local
            | (local, i) <- tableEntries visible
            , i == Imported (FromModule p) e KindEnum
            ] of
          [] -> qualError sp (T.concat [
              "the constructor `", x, "` belongs to the enumeration `", e,
              "`, which is not imported here"
            ]) [T.concat ["a constructor pattern needs its enumeration: import `", e, "`"]]
          (local : _) -> pure (Just local)

-- | The diagnostic for a module spelling that names nothing imported.
notImportedModule :: Span -> Text -> [Text] -> LoadError
notImportedModule sp m known = LoadError sp
  (T.concat ["the module `", m, "` is not imported"]) notes
  where
    names = nub known
    notes = case names of
      [] -> ["this file imports no module by a qualified name"]
      _ -> ["the modules this file imports are: " <> T.intercalate ", " names]
        <> maybe [] (\s -> ["did you mean `" <> s <> "`?"])
             (Suggest.best names m)

-- | The diagnostic for a name the source does not offer at all.
notOffered :: ModuleInfo -> Source -> Span -> Text -> Text -> Table -> LoadError
notOffered info src sp m x offer = case src of
  SrcModule p
    | Map.member x (declaredTable (miNodes info) p) ->
        LoadError sp (T.concat [
            "`", x, "` is declared in `", m, "` but not exported"
          ]) ["a module offers the names its export list names"]
  _ -> LoadError sp (T.concat [where_, " does not offer `", x, "`"]) (notes)
  where
    where_ = case src of
      SrcModule _ -> T.concat ["the module `", m, "`"]
      SrcNative nm -> T.concat ["`@native ", nm, "`"]
    names = nub (Map.keys offer)
    notes =
      [case names of
         [] -> "it offers nothing"
         _ -> "it offers: " <> T.intercalate ", " names]
      <> maybe [] (\s -> ["did you mean `" <> qualifyName m s <> "`?"])
           (Suggest.best names x)

-- | The diagnostic for a name that is there, but in another namespace.
kindMismatch :: Span -> Text -> Text -> [Imported] -> UseKind -> LoadError
kindMismatch sp m x entries kind = LoadError sp (T.concat [
    "`", x, "` in `", m, "` is ", kinds, ", not ", wanted
  ]) notes
  where
    kinds = T.intercalate " and " (map kindName (mapKindNub (map imKind entries)))
    wanted = describeUse kind
    notes = case kind of
      UseType | any ((== KindEffect) . imKind) entries ->
        [T.concat ["an effect goes in a row: write `{", x, "}`"]]
      UseEffect ->
        ["an operation is not an effect: use it as a value or in a handler clause"]
      UseCtor -> ["a `#` pattern names a constructor"]
      _ -> []

describeUse :: UseKind -> Text
describeUse = \case
  UseValue -> "a value"
  UseCtor -> "a constructor"
  UseType -> "a type"
  UseEffect -> "an effect"
  UseRow -> "a row"
  UseOp -> "an operation"

nativeOrigin :: ImportOrigin -> Bool
nativeOrigin = \case
  FromNative _ -> True
  FromModule _ -> False

qualError :: Span -> Text -> [Text] -> Either LoadError a
qualError sp msg notes = Left $ LoadError sp msg notes

-- | The names a module declares: every top-level name and its kind.  The
--   constructors of an enum are values of the module's scope, so they travel
--   with it.
--
--   A file may declare two things under one name -- `funct f` and `type f` are
--   told apart by the position a use puts them in -- so the table keeps both
--   rather than the last one read.
declaredTable :: Map FilePath Node -> FilePath -> Table
declaredTable nodes p = tableFromList
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
  | T.null m = Right $ tableFromList
      -- The whole scope is every native module at once, but each name keeps
      -- the module that declares it: that is what lets a qualified spelling
      -- check that the module it writes really offers the name, and it makes
      -- `@native` and `@native M` one declaration of `x`, not two.
      [ (bName b, Imported (FromNative (bModule b)) (bName b) (nativeKind b))
      | b <- builtins ]
  | null names =
      Left $ LoadError noSpan (T.concat ["there is no native module `", m, "`"])
        [ "native modules: " <> T.intercalate ", " moduleNames ]
  | otherwise = Right $ tableFromList
      [ (n, Imported (FromNative m) n k) | (n, k) <- names ]
  where
    names = [ (bName b, nativeKind b) | b <- builtins, bModule b == m ]

nativeKind :: Builtin -> DeclKind
nativeKind b = case bKind b of
  Op _ -> KindEffect
  Native -> KindFunct
  -- A type-directed native is still a function to the checker: it is a value
  -- applied to an argument, and only `with` changes how it is called.
  TypeDirected -> KindFunct

-- | The entries one name of a list asks for.
--
--   A name alone is every declaration of that spelling, because a module may
--   declare a function and a type under one name and exporting the name exports
--   the name.  A kind narrows it to one namespace: `[type cell]` asks for the
--   type, `[funct cell]` for the function, and a module that has only the other
--   one is told so rather than silently given nothing.
namedEntries :: Table -> ExportDecl -> [Imported]
namedEntries t ed =
  [ imp
  | imp <- Map.findWithDefault [] (edName ed) t
  , maybe True (\k -> namespaceOf (imKind imp) == namespaceOf k) (edKind ed)
  ]

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
      Nothing -> [ (n, Just imp) | (n, imp) <- tableEntries t ]
      Just decls -> withConstructors enums (map edName decls)
        [ (localOf ed, Just imp)
        | ed <- decls, imp <- namedEntries t ed ]

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
--
--   Only an enumeration brings values.  A name may be a function and an
--   enumeration at once, and the function does not own the enumeration's
--   constructors.
enumValues :: Enums -> Text -> Imported -> [(Text, Imported)]
enumValues enums local imp =
  (local, imp) : case imKind imp of
    KindEnum -> [ (c, ctor c) | c <- constructorsOf enums (imOrigin imp) (imName imp) ]
    _ -> []
  where
    ctor c = imp {imName = c, imKind = KindFunct}

localOf :: ExportDecl -> Text
localOf ed = fromMaybe (edName ed) (edAlias ed)

-- | The table a module without an export list offers: everything it declares
--   and everything it imported from another module.
--
--   A native name is the exception.  `import @native` is how a file gets
--   `sayn` and `map` for itself; it is not a promise to pass them on, and a
--   module that re-exported the whole native scope would make its importers
--   depend on which builtins it happened to use.  A module that wants an
--   importer to see a native name writes an export list and names it there --
--   which is also the moment the rest of its interface becomes explicit.
offerByDefault :: Table -> Table -> Table
offerByDefault own imported = mergeTables own (Map.mapMaybe keep imported)
  where
    keep imps = case filter (not . native) imps of
      [] -> Nothing
      kept -> Just kept

    native (Imported (FromNative _) _ _) = True
    native _ = False

-- | The table a module offers, as far as the tables known so far allow.  A name
--   its export list asks for and nothing provides is dropped, not reported: the
--   strict pass does the reporting once the whole component has settled.
publishOf :: Map FilePath Node -> Map FilePath Table -> FilePath -> Table
publishOf nodes tables p = case mhExports (Ast.modHeader (nChunk n)) of
    Nothing -> offerByDefault own imported
    Just decls -> tableFromList
      [ entry
      | ed <- decls
      , imp <- namedEntries visible ed
      , entry <- entriesOf (enumsOf nodes) spelled (localOf ed, imp)
      ]
  where
    n = nodes Map.! p
    own = declaredTable nodes p
    spelled = map edName (fromMaybe [] (mhExports (Ast.modHeader (nChunk n))))
    visible = mergeTables own imported
    imported = importedOf (enumsOf nodes) tables (nImports n)

-- | The table a module offers, once its component has settled: an export list
--   that names nothing the module has is an error here.
strictPublish :: Map FilePath Node -> Map FilePath Table -> FilePath -> Either LoadError Table
strictPublish nodes tables p = case mhExports (Ast.modHeader (nChunk n)) of
    Nothing -> pure $ offerByDefault own imported
    Just decls -> tableFromList . concat <$> traverse select decls
  where
    n = nodes Map.! p
    own = declaredTable nodes p
    spelled = map edName (fromMaybe [] (mhExports (Ast.modHeader (nChunk n))))
    visible = mergeTables own imported
    imported = importedOf (enumsOf nodes) tables (nImports n)

    select ed = case namedEntries visible ed of
      -- A name that is here, but in another namespace, is a different mistake
      -- from a name that is not here at all: `[type cell]` in a module whose
      -- `cell` is a function is a wrong kind, not a typo.
      [] | others@(_ : _) <- Map.findWithDefault [] (edName ed) visible ->
        Left $ LoadError (edSpan ed) (T.concat [
            "`", edName ed, "` is ", kinds others, " here, not ", asked
          ]) [ "write the kind it is, or drop the kind and rename it with `as`" ]
      [] -> Left $ LoadError (edSpan ed) (T.concat [
          "`", edName ed, "` is not declared or imported here, so it cannot be exported"
        ]) [ available ]
      imps -> Right
        [ entry
        | imp <- imps
        , entry <- entriesOf (enumsOf nodes) spelled (localOf ed, imp)
        ]
      where
        asked = case edKind ed of
          Nothing -> "a name this module has"
          Just k -> kindName k
        available = case Map.keys visible of
          [] -> "this module declares and imports nothing"
          names -> "the module declares or imports: " <> T.intercalate ", " names
        kinds = T.intercalate " and " . map kindName . mapKindNub . map imKind

-- | One kind per namespace, so a name declared as a function and a type says
--   both.
mapKindNub :: [DeclKind] -> [DeclKind]
mapKindNub = foldr step []
  where
    step k acc
      | any ((== namespaceOf k) . namespaceOf) acc = acc
      | otherwise = k : acc

-- | The names a module's imports bring, as one table.
importedOf :: Enums -> Map FilePath Table -> [Import] -> Table
importedOf enums tables = foldl' add Map.empty
  where
    add acc i = foldl' one acc (resolveImport enums tables i)
    one acc (_, Nothing) = acc
    one acc (local, Just imp) = addEntry local imp acc

addEntry :: Text -> Imported -> Table -> Table
addEntry local imp acc = case Map.lookup local acc of
  Nothing -> Map.insert local [imp] acc
  Just others
    | imp `elem` others -> acc
    | otherwise -> Map.insert local (others <> [imp]) acc

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
  pure $ Map.filter (not . null) $ Map.mapWithKey shadowed imported
  where
    n = nodes Map.! p
    own = declaredTable nodes p

    -- A declaration of the module wins over an import of the same name -- but
    -- only in its own namespace: a file that declares `funct f` may still
    -- import `type f`, because a use tells the two apart by position.
    shadowed name imps =
      [ imp
      | imp <- imps
      , not (any ((== namespaceOf (imKind imp)) . namespaceOf . imKind)
                 (Map.findWithDefault [] name own))
      ]

    add acc i = do
      names <- strictImport nodes tables i
      foldlM (insertImport (iSpan i)) acc names

-- | The strict form of 'resolveImport': every name an import names must be one
--   the source offers.
--
--   During the growth of a cycle a name may legitimately be missing, so
--   'resolveImport' drops it and the rounds continue.  Once the rounds are
--   over, a name that never appeared is a mistake in the import, and reporting
--   it at the import line is worth more than an `E0007` at a use three
--   functions later: the reader is told what the source does offer, and, when
--   the name exists but is private, that too.
strictImport :: Map FilePath Node -> Map FilePath Table -> Import -> Either LoadError [(Text, Imported)]
strictImport nodes tables i = case iSource i of
  SrcNative m
    | T.null m -> Right (tableEntries wholeNative)
    | otherwise -> case nativeTable m of
        Left e -> Left e {leSpan = iSpan i}
        Right t -> keep t Nothing
  SrcModule p -> keep (Map.findWithDefault Map.empty p tables) (Just p)
  where
    wholeNative = either (const Map.empty) id (nativeTable "")

    keep t src = case iNames i of
      Nothing -> Right (tableEntries t)
      Just decls -> concat <$> traverse (one t src) decls

    one t src ed = case namedEntries t ed of
      [] -> Left $ missing t src ed
      imps -> Right [ entry
                    | imp <- imps
                    , entry <- entriesOf (enumsOf nodes) spelled (localOf ed, imp) ]
      where
        -- A constructor the list names by itself is left to its own entry, so
        -- the set has to be the whole list, not this entry.
        spelled = maybe [] (map edName) (iNames i)

    missing t src ed = LoadError (edSpan ed) (T.concat [
        "`", edName ed, "` is not offered by ", where_
      ]) (notes t src)
      where
        where_ = case src of
          Just p -> "the module `" <> T.pack (baseName p) <> "`"
          Nothing -> "`@native " <> nativeName <> "`"
        nativeName = case iSource i of
          SrcNative m -> m
          SrcModule _ -> ""

        -- A name that is there in another namespace is a wrong kind, not a
        -- typo: `import lib [type cell]` in a module whose `cell` is a
        -- function is answered with the kind it actually is.
        notes offeredBy origin =
          case (edKind ed, Map.findWithDefault [] (edName ed) offeredBy) of
          (Just k, others@(_ : _)) ->
            [ T.concat [
                "`", edName ed, "` is ", kinds others, " in ", named origin,
                ", not ", kindName k
              ] ]
          -- A name the module declares but does not export is a different
          -- mistake from a name it never had: the first asks for the export
          -- list to change, the second for the spelling.
          _ -> case origin of
            Just p | Map.member (edName ed) (declaredTable nodes p) ->
              [ T.concat [
                  "`", edName ed, "` is declared in ", T.pack (baseName p),
                  " but not exported: a module offers the names its export list names"
                ] ]
            _ -> [ offered offeredBy ]

        named = \case
          Just p -> T.pack (baseName p)
          Nothing -> T.concat ["`@native ", nativeName, "`"]

        kinds = T.intercalate " and " . map kindName . mapKindNub . map imKind

        offered tbl = case Map.keys tbl of
          [] -> "the source offers nothing"
          names -> "it offers: " <> T.intercalate ", " names

-- | Add one import's names to a table, reporting a clash.
--
--   A table entry is a list, so a name that is a function in one import and a
--   type in another is one name with both.  Two entries of one namespace under
--   one name are a clash, and `as` is the way out.
insertImport :: Span -> Table -> (Text, Imported) -> Either LoadError Table
insertImport sp acc (local, imp) = case Map.lookup local acc of
    Nothing -> Right $ Map.insert local [imp] acc
    -- The same declaration named twice -- a constructor reached both through
    -- its enum and by its own name -- is one name, not a clash.
    Just others | imp `elem` others -> Right acc
      | Just other <- sameNamespace others -> Left $ LoadError sp (T.concat [
            "two imports bring `", local, "`: ", describe other, " and ", describe imp
          ]) [ "write `as` in one of the import lists to keep both names" ]
      | otherwise -> Right $ Map.insert local (others <> [imp]) acc
  where
    sameNamespace others = lookup True
      [ (True, other) | other <- others
      , namespaceOf (imKind other) == namespaceOf (imKind imp) ]
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
