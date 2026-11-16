{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}

-- | The parts of a file that are about the file itself: the @module@ header
--   and the list of names it exports.
--
--   These live in a module of their own because all three levels need them:
--   the parser puts a header on every chunk, the elaborator keeps it in the
--   IR, and the checker keeps it in the typed IR, so a diagnostic can name the
--   module it came from without a side channel.
module Module (
    Module(..)
  , ModuleHeader(..)
  , ExportDecl(..)
  , DeclKind(..)
  , prettyDeclKind
  , headerExportsAll
  ) where

import Data.Text (Text)
import qualified Data.Text as T
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

-- | @module name [d1 ... dn]@: the header every file starts with.
--
--   A module is one file, and the file is addressed by its own name when
--   another module imports it.  The name written here is what the module calls
--   itself in diagnostics, and the name a program must use to be runnable:
--   @module Main@.
--
--   The export list is optional.  When it is present it is the whole
--   interface: a declaration it does not name is private to the module.  When
--   it is absent the module exports everything it declares.
data ModuleHeader = ModuleHeader {
    mhName    :: Text
  , mhExports :: Maybe [ExportDecl]
  , mhSpan    :: Span
  } deriving (Eq, Show, Generic)

instance Sexp ModuleHeader where sexp = show

instance Pretty ModuleHeader where
  pretty (ModuleHeader n exports _) = T.concat [
      "module ", n,
      maybe "" (\ds -> T.concat [" [", T.unwords (map pretty ds), "]"]) exports
    ]

-- | Does this header export everything it declares, rather than a list?
headerExportsAll :: ModuleHeader -> Bool
headerExportsAll = \case
  ModuleHeader _ Nothing _ -> True
  ModuleHeader _ (Just _) _ -> False

-- | One name in an export list.
--
--   The kind is usually omitted, because a name is enough to find the
--   declaration; it is written when a module declares two things under one
--   name, or when the reader wants to be explicit.  @as@ renames the name for
--   everyone who imports the module, so @funct f as g@ exports @g@ and nobody
--   outside can see @f@.
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

-- | The kind of a declaration, for the kind a list may write before a name.
data DeclKind =
    KindFunct
  | KindType
  | KindEffect
  | KindRow
  | KindEnum
  deriving (Eq, Show, Generic)

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
