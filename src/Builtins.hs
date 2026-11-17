{-# LANGUAGE OverloadedStrings #-}

-- | The names the native modules offer, and which module offers each.
--
--   A builtin is visible to two independent components: the type checker
--   ('Scope.globalScope' gives it a scheme) and the interpreter
--   ('IntInterpreter.buildInitialEnv' gives it a value or an effect
--   operation).  Those tables used to be written by hand on both sides, and
--   they drifted: @pred@ type-checked but crashed at run time, while
--   @read_string@, @read_float@, @random_float@, @time_ms@ and friends were
--   implemented but rejected by the checker.  This module is the one list both
--   sides are checked against, so a name added in one place and forgotten in
--   the other is reported instead of discovered by a user.
--
--   The list is the standard library of line 0.2, cut into the native modules
--   @import @native@ names.  A group of names used to be a record in a source
--   file; a record could not hold a polymorphic field, so half of the library
--   was flat names and half was fields, and a reader had to know which was
--   which.  A module has no such limit: every name of @Arrays@ is polymorphic
--   and none of it needs a field.  The interface is documented in
--   @docs/stdlib.md@.
--
--   Nothing here is visible without an import.  The interpreter still binds
--   every native name in its own environment below a program's, but the
--   checker only adds the names of the modules a file imported, so an
--   unimported @map@ is reported as an unknown name.
module Builtins (
  Builtin(..),
  BuiltinKind(..),
  builtins,
  names,
  namesOfKind,
  modules,
  moduleNames,
  namesOfModule,
  effectsOfModule,
  moduleOf
) where

import Data.Text (Text)
import qualified Data.List as List

-- | How a builtin reaches the program.
data BuiltinKind =
    -- | A value the interpreter builds directly (a closure over native code).
    Native
    -- | An operation of a built-in effect.  The name of the effect is also the
    --   name of the module the operation comes from.
  | Op Text
  deriving (Eq, Ord, Show)

data Builtin = Builtin {
    bModule :: Text
  , bName   :: Text
  , bKind   :: BuiltinKind
} deriving (Eq, Ord, Show)

-- | Every name a native module offers.  Keep this list and the two
--   implementations in step; 'Marran.Test.BuiltinSpec' fails when they are not.
builtins :: [Builtin]
builtins = [
    -- Numbers: the arithmetic of `Int` and `Float`, and the conversions
    -- between them.
    Builtin "Numbers" "pred" Native,
    Builtin "Numbers" "+" Native,
    Builtin "Numbers" "-" Native,
    Builtin "Numbers" "*" Native,
    Builtin "Numbers" "/" Native,
    Builtin "Numbers" "%" Native,
    Builtin "Numbers" "neg" Native,
    Builtin "Numbers" "abs" Native,
    Builtin "Numbers" "max" Native,
    Builtin "Numbers" "min" Native,
    Builtin "Numbers" "ieq" Native,
    Builtin "Numbers" "ineq" Native,
    Builtin "Numbers" ">" Native,
    Builtin "Numbers" "<" Native,
    Builtin "Numbers" "<=" Native,
    Builtin "Numbers" ">=" Native,

    Builtin "Numbers" "+." Native,
    Builtin "Numbers" "-." Native,
    Builtin "Numbers" "*." Native,
    Builtin "Numbers" "/." Native,
    Builtin "Numbers" "%." Native,
    Builtin "Numbers" "fneg" Native,
    Builtin "Numbers" "fabs" Native,
    Builtin "Numbers" "fmax" Native,
    Builtin "Numbers" "fmin" Native,
    Builtin "Numbers" "feq" Native,
    Builtin "Numbers" "fneq" Native,
    Builtin "Numbers" "<." Native,
    Builtin "Numbers" ">." Native,
    Builtin "Numbers" "<=." Native,
    Builtin "Numbers" ">=." Native,

    Builtin "Numbers" "to_int" Native,
    Builtin "Numbers" "to_float" Native,

    -- Strings
    Builtin "Strings" "++" Native,
    Builtin "Strings" "slen" Native,
    Builtin "Strings" "sub" Native,
    Builtin "Strings" "split" Native,
    Builtin "Strings" "join" Native,
    Builtin "Strings" "trim" Native,
    Builtin "Strings" "upper" Native,
    Builtin "Strings" "lower" Native,
    Builtin "Strings" "contains" Native,
    Builtin "Strings" "replace" Native,
    Builtin "Strings" "seq" Native,
    Builtin "Strings" "sneq" Native,

    -- Booleans.  `and` is the conjunction the paper's examples are written
    -- with; `&&` is the C spelling of the same operation, and both stay.
    Builtin "Booleans" "not" Native,
    Builtin "Booleans" "||" Native,
    Builtin "Booleans" "&&" Native,
    Builtin "Booleans" "^" Native,
    Builtin "Booleans" "nor" Native,
    Builtin "Booleans" "nand" Native,
    Builtin "Booleans" "and" Native,

    -- Functions
    Builtin "Functions" "id" Native,
    Builtin "Functions" "const" Native,
    Builtin "Functions" "flip" Native,
    Builtin "Functions" "compose" Native,
    Builtin "Functions" "apply" Native,
    Builtin "Functions" "curry" Native,
    Builtin "Functions" "uncurry" Native,

    -- Arrays
    Builtin "Arrays" "head" Native,
    Builtin "Arrays" "tail" Native,
    Builtin "Arrays" "empty" Native,
    Builtin "Arrays" "alen" Native,
    Builtin "Arrays" "map" Native,
    Builtin "Arrays" "filter" Native,
    Builtin "Arrays" "any" Native,
    Builtin "Arrays" "all" Native,
    Builtin "Arrays" "foldl" Native,
    Builtin "Arrays" "foldr" Native,
    Builtin "Arrays" "concat" Native,
    Builtin "Arrays" "zip" Native,
    Builtin "Arrays" "at" Native,
    Builtin "Arrays" "take" Native,
    Builtin "Arrays" "drop" Native,

    -- Pairs
    Builtin "Pairs" "fst" Native,
    Builtin "Pairs" "snd" Native,

    -- Conv: the comparisons and the conversion to text.  `==` compares content
    -- and `===` compares the values themselves, which is why a reader sees
    -- `1 === 1` as false: the two 1s are different values, even though they
    -- are equal.
    Builtin "Conv" "show" Native,
    Builtin "Conv" "==" Native,
    Builtin "Conv" "===" Native,
    Builtin "Conv" "!=" Native,
    Builtin "Conv" "!==" Native,

    -- Memory: the two ways to force a delayed computation.
    Builtin "Memory" "force" Native,
    Builtin "Memory" "whnf" Native,

    -- Output.  `trace` shows its value; it is a function, not an operation,
    -- because it takes two arguments and returns the second.
    Builtin "Output" "say" (Op "Output"),
    Builtin "Output" "sayn" (Op "Output"),
    Builtin "Output" "trace" (Op "Output"),

    -- Input
    Builtin "Input" "read_string" (Op "Input"),
    Builtin "Input" "read_int" (Op "Input"),
    Builtin "Input" "read_float" (Op "Input"),
    Builtin "Input" "read_boolean" (Op "Input"),

    -- Random
    Builtin "Random" "random_int" (Op "Random"),
    Builtin "Random" "random_float" (Op "Random"),
    Builtin "Random" "random_boolean" (Op "Random"),
    Builtin "Random" "random_string" (Op "Random"),

    -- Time
    Builtin "Time" "time_ms" (Op "Time"),
    Builtin "Time" "sleep" (Op "Time"),

    -- Env
    Builtin "Env" "get_env" (Op "Env"),
    Builtin "Env" "set_env" (Op "Env"),

    -- File
    Builtin "File" "read_file" (Op "File"),
    Builtin "File" "write_file" (Op "File"),
    Builtin "File" "append_file" (Op "File"),
    Builtin "File" "file_exists" (Op "File"),
    Builtin "File" "delete_file" (Op "File"),
    Builtin "File" "list_directory" (Op "File"),

    -- System
    Builtin "System" "args" (Op "System"),
    Builtin "System" "hostname" (Op "System"),
    Builtin "System" "system" (Op "System"),
    Builtin "System" "exit" (Op "System"),

    -- Error: `error` is the operation a handler catches; `try` handles the
    -- effect inside the language and `assert` reports a failed condition
    -- through it, so neither needs a clause in a handler the program writes.
    Builtin "Error" "error" (Op "Error"),
    Builtin "Error" "assert" Native,
    Builtin "Error" "try" Native
  ]

names :: [Text]
names = map bName builtins

namesOfKind :: (BuiltinKind -> Bool) -> [Text]
namesOfKind p = [bName b | b <- builtins, p (bKind b)]

-- | The modules in the order they are documented, each with its names.
modules :: [(Text, [Text])]
modules = [(m, [n | (m', n) <- pairs, m' == m]) | m <- order]
  where
    pairs = List.sortOn fst [(bModule b, bName b) | b <- builtins]
    order = List.nub (map fst pairs)

moduleNames :: [Text]
moduleNames = map fst modules

namesOfModule :: Text -> [Text]
namesOfModule m = concatMap snd (filter ((m ==) . fst) modules)

-- | The effects a module declares operations of.  A module of operations is
--   named after its effect, so this is the module's own name for every module
--   that is one; `Functions` and `Conv`, which are values, have none.
effectsOfModule :: Text -> [Text]
effectsOfModule m = List.nub
  [ eff
  | Builtin m' _ (Op eff) <- builtins
  , m' == m
  ]

-- | The module a name comes from, if any.
moduleOf :: Text -> Maybe Text
moduleOf n = case [m | Builtin m n' _ <- builtins, n' == n] of
  (m:_) -> Just m
  [] -> Nothing
