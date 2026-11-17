{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}

-- | The parts of a program that are about files rather than expressions: the
--   @module@ header, the names it exports, the imports it makes, and the units
--   the loader groups modules into.
--
--   These live in a module of their own because all three levels need them: the
--   parser puts a header on every chunk, the elaborator keeps it in the IR, and
--   the checker keeps it in the typed IR, so a diagnostic can name the module it
--   came from without a side channel.
module Module (
    Module(..)
  , ModuleHeader(..)
  , ExportDecl(..)
  , ImportDecl(..)
  , ImportUnit(..)
  , Imported(..)
  , ImportOrigin(..)
  , Table
  , Unit(..)
  , Program(..)
  , DeclKind(..)
  , prettyDeclKind
  , headerExportsAll
  , importUnits
  , namespaceOf
  , parsedHeader
  , moduleAt
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (listToMaybe)
import GHC.Generics (Generic)
import Sexp (Sexp (..))
import Span (Span)
import Utils (Pretty (..))

-- | A file: its header and its declarations.
--
--   The three levels instantiate @d@ with their own declaration type, so the
--   header survives elaboration and type checking unchanged.
data Module d = Module {
    modHeader :: ModuleHeader
  , modDecls  :: [d]
  } deriving (Eq, Show, Functor, Foldable, Traversable, Generic)

instance Show d => Sexp (Module d) where sexp = show

instance Pretty d => Pretty (Module d) where
  pretty (Module header ds) =
    T.intercalate "\n" (pretty header : map pretty ds)

-- | @module name [d1 ... dn]@, followed by the file's imports.
--
--   A module is one file, and the file is addressed by its own name when
--   another module imports it.  The name written here is what the module calls
--   itself in diagnostics, and the name a program must use to be runnable:
--   @module Main@.
--
--   The export list is optional.  When it is present it is the whole interface:
--   a declaration it does not name is private to the module.  When it is absent
--   the module exports everything it declares and everything it imports.
--
--   The imports are kept twice: as they were written ('mhImports', which the
--   printer shows and the loader reads) and as they resolve ('mhResolved', for
--   everything after loading).  A resolved name maps the local name a file
--   writes to the module that declares it and the name it is declared under, so
--   a chain of re-exports always points at the declaration itself.
--
--   'mhPublished' is the other direction -- the names this module offers to an
--   importer -- in the same form.  Both tables are keyed by the name a use
--   writes, which is what a per-module scope is built from.
data ModuleHeader = ModuleHeader {
    mhName      :: Text
  , mhImports   :: [ImportDecl]
  , mhResolved  :: Table
  , mhPublished :: Table
  , mhExports   :: Maybe [ExportDecl]
  , mhSpan      :: Span
  } deriving (Eq, Show, Generic)

-- | What a name stands for: where it is declared, what it is called there, and
--   what kind of declaration it is.
data Imported = Imported {
    imOrigin :: ImportOrigin
  , imName   :: Text
  , imKind   :: DeclKind
  } deriving (Eq, Ord, Show, Generic)

instance Sexp Imported where sexp = show

instance Pretty Imported where
  pretty (Imported o n _) = T.concat [pretty o, ".", n]

-- | A table of names, keyed by the name a use writes.
--
--   Both directions are one of these: what a file sees of the outside
--   ('mhResolved', which the loader keeps apart from the file's own
--   declarations) and what it offers an importer ('mhPublished').
type Table = Map Text Imported

-- | The namespace a kind belongs to.
--
--   A function and a type may share a name: a use tells them apart by the
--   position it puts the name in, exactly as two declarations of one file do.
--   Two functions (or two types) of one name clash, and that is what the loader
--   reports when two imports bring them.
namespaceOf :: DeclKind -> Text
namespaceOf = \case
  KindFunct  -> "value"
  KindEnum   -> "type"
  KindType   -> "type"
  KindEffect -> "type"
  KindRow    -> "row"

instance Sexp ModuleHeader where sexp = show

instance Pretty ModuleHeader where
  pretty (ModuleHeader n imports _ _ exports _) = T.intercalate "\n" $
    (T.concat [
        "module ", n,
        maybe "" (\ds -> T.concat [" [", T.unwords (map pretty ds), "]"]) exports
      ] : map pretty imports)

-- | A header as the parser produces it: nothing is resolved yet, so both tables
--   are empty and the loader fills them in.
parsedHeader :: Text -> [ImportDecl] -> Maybe [ExportDecl] -> Span -> ModuleHeader
parsedHeader n imports exports sp =
  ModuleHeader n imports Map.empty Map.empty exports sp

-- | Does this header export everything it declares, rather than a list?
headerExportsAll :: ModuleHeader -> Bool
headerExportsAll = \case
  ModuleHeader _ _ _ _ Nothing _ -> True
  ModuleHeader _ _ _ _ (Just _) _ -> False

-- | One name in an export or import list.
--
--   The kind is usually omitted, because a name is enough to find the
--   declaration; it is written when a module declares two things under one
--   name, or when the reader wants to be explicit.  @as@ renames the name: in
--   an export list it is the name everyone who imports the module uses, and in
--   an import list it is the name this file uses.
data ExportDecl = ExportDecl {
    edSpan  :: Span
  , edKind  :: Maybe DeclKind
  , edName  :: Text
  , edAlias :: Maybe Text
  } deriving (Eq, Show, Generic)

instance Sexp ExportDecl where sexp = show

instance Pretty ExportDecl where
  pretty (ExportDecl _ k n alias) = T.concat [
      maybe "" ((<> " ") . pretty) k,
      n,
      maybe "" (" as " <>) alias
    ]

-- | One @import@ line as it was written.
data ImportDecl = ImportDecl {
    idSpan   :: Span
    -- | @import @native ...@: the names come from the native modules, not from
    --   a file.
  , idNative :: Bool
    -- | The target.  'Nothing' is only meaningful for a native import with no
    --   module: @import @native@ takes the whole native scope.
  , idUnit   :: Maybe ImportUnit
  } deriving (Eq, Show, Generic)

instance Sexp ImportDecl where sexp = show

instance Pretty ImportDecl where
  pretty (ImportDecl _ native unit) = T.concat [
      "import ", if native then "@native " else "",
      maybe "" pretty unit
    ]

-- | What an @import@ names.
data ImportUnit =
    -- | @import a@, @import a#f@, @import a [f g as h]@.  'Nothing' is the
    --   whole export list of @a@; the list is the same grammar an export list
    --   uses, so a kind and an alias mean the same thing.
    ImportModule Text (Maybe [ExportDecl])
    -- | @import 'lib/' [a b]@: the units inside are looked up under the
    --   directory.
  | ImportDir Text [ImportUnit]
  deriving (Eq, Show, Generic)

instance Sexp ImportUnit where sexp = show

instance Pretty ImportUnit where
  pretty = \case
    ImportModule n Nothing -> n
    ImportModule n (Just ds) ->
      T.concat [n, " [", T.unwords (map pretty ds), "]"]
    ImportDir d us ->
      T.concat ["'", d, "' [", T.unwords (map pretty us), "]"]

-- | Every module an import line names, in the order they are written, with the
--   directory prefix the nesting gave them.
importUnits :: ImportDecl -> [(Text, Maybe [ExportDecl])]
importUnits (ImportDecl _ _ Nothing) = []
importUnits (ImportDecl _ _ (Just u)) = go "" u
  where
    go prefix = \case
      ImportModule n names -> [(prefix <> n, names)]
      ImportDir d us -> concatMap (go (prefix <> d)) us

-- | Where an import's names come from.
data ImportOrigin =
    -- | A file, by the path the loader gave it.  The path is what identifies a
    --   module; the @module@ header only names it for a reader.
    FromModule FilePath
    -- | The native table.  An empty name means @import @native@ without a
    --   module, which brings the whole native scope.
  | FromNative Text
  deriving (Eq, Ord, Show, Generic)

instance Sexp ImportOrigin where sexp = show

instance Pretty ImportOrigin where
  pretty = \case
    FromModule p -> T.pack p
    FromNative n -> T.concat ["@native ", n]

-- | A unit of checking: one module, or a cycle of modules checked together.
--
--   A cycle cannot be read in dependency order, so the loader groups its
--   modules into one unit: their type-level declarations are read together,
--   because an alias of one may name an alias of another.  Every module keeps
--   its own declarations and its own tables, though: a cycle does not make two
--   private @helper@s one name, and a module inside it still sees only what it
--   imported.  'unitPaths' lists the files of the unit, which is what an
--   importer of any of them gets.
data Unit d = Unit {
    unitPaths   :: [FilePath]
  , unitModules :: [(FilePath, Module d)]
  } deriving (Eq, Show, Functor, Foldable, Traversable, Generic)

instance Show d => Sexp (Unit d) where sexp = show

instance Pretty d => Pretty (Unit d) where
  pretty unit = T.intercalate "\n\n" [ pretty m | (_, m) <- unitModules unit ]

-- | A whole program in units, with the sources the loader read.
--
--   The units are in dependency order: a unit comes after every unit it
--   imports.  The sources are kept so that a diagnostic from any file can quote
--   the line it is about -- the renderer needs the text, and by the time a type
--   error is reported the file itself is long gone.  'progEntry' is the file the
--   program was started from, which is the only one allowed to say
--   @module Main@.
data Program d = Program {
    progUnits   :: [Unit d]
  , progSources :: [(FilePath, Text)]
  , progEntry   :: FilePath
  } deriving (Eq, Show, Functor, Foldable, Traversable, Generic)

instance Show d => Sexp (Program d) where sexp = show

instance Pretty d => Pretty (Program d) where
  pretty (Program units _ _) = T.intercalate "\n" (map pretty units)

-- | The module a path names, if the program contains it.  The entry file is
--   matched by its own path; an import names a module by the path it resolved
--   to, so the same lookup answers both questions.
moduleAt :: Program d -> FilePath -> Maybe (Module d)
moduleAt prog path = listToMaybe
  [ m | u <- progUnits prog
      , (p, m) <- unitModules u
      , p == path ]

-- | The kind of a declaration, for the kind a list may write before a name.
data DeclKind =
    KindFunct
  | KindType
  | KindEffect
  | KindRow
  | KindEnum
  deriving (Eq, Ord, Show, Generic)

instance Sexp DeclKind where sexp = show

instance Pretty DeclKind where
  pretty = prettyDeclKind

prettyDeclKind :: DeclKind -> Text
prettyDeclKind = \case
  KindFunct  -> "funct"
  KindType   -> "type"
  KindEffect -> "effect"
  KindRow    -> "row"
  KindEnum   -> "enum"
