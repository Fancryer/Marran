{-# LANGUAGE OverloadedStrings #-}

-- | The names every program starts with.
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
--   The list grew into the standard library of line 0.2: the arithmetic, the
--   strings and the booleans of @app/std.marr@ live here.  A record of the
--   library (@Numbers@, @Strings@, @Booleans@) is not a second definition of
--   its fields; it names them, and both sides build the record out of the very
--   values they bind globally.  That is what makes @Numbers@+@ and @+@ the same
--   function rather than two that must be kept in step.
--
--   Not every group of @app/std.marr@ can be a record yet.  A record's fields
--   are inferred at one type ('Infer.inferRecord'), so a field cannot be
--   quantified: @Arrays@ would have to hold @map@ at a single element type.
--   The fields of @Functions@, @Arrays@, @Pairs@, @Conv@, @Output@ and
--   @Input@ are therefore unpacked into the native scope as plain functions,
--   and only the monomorphic groups are records.  When a record field may be
--   polymorphic these names will move into their records as well, and the flat
--   names will be built from the records, exactly as @+@ and @Numbers@+@
--   already are.
module Builtins (
  Builtin(..),
  BuiltinKind(..),
  builtins,
  names,
  namesOfKind
) where

import Data.Text (Text)

-- | How a builtin reaches the program.
data BuiltinKind =
    -- | A value the interpreter builds directly (a closure over native code,
    --   or a constant such as @args@).
    Native
    -- | A record whose fields are the named builtins.  The fields are listed
    --   globally as well, so @Booleans@@not@ and @not@ are the same value; the
    --   order here is the order @app/std.marr@ declares them in, which is the
    --   order a record prints its fields in only if the names happen to sort
    --   that way, and that is fine.
  | Record [Text]
    -- | An operation of a built-in effect.
  | Op Text
  deriving (Eq, Ord, Show)

data Builtin = Builtin {
  bName :: Text,
  bKind :: BuiltinKind
} deriving (Eq, Ord, Show)

-- | Every name visible in the initial scope.  Keep this list and the two
--   implementations in step; 'Marran.Test.BuiltinSpec' fails when they are not.
builtins :: [Builtin]
builtins = [
    -- integers
    Builtin "pred" Native,
    Builtin "+" Native,
    Builtin "-" Native,
    Builtin "*" Native,
    Builtin "/" Native,
    Builtin "%" Native,
    Builtin "neg" Native,
    Builtin "abs" Native,
    Builtin "max" Native,
    Builtin "min" Native,
    Builtin "ieq" Native,
    Builtin "ineq" Native,
    Builtin ">" Native,
    Builtin "<" Native,
    Builtin "<=" Native,
    Builtin ">=" Native,

    -- floats
    Builtin "+." Native,
    Builtin "-." Native,
    Builtin "*." Native,
    Builtin "/." Native,
    Builtin "%." Native,
    Builtin "fneg" Native,
    Builtin "fabs" Native,
    Builtin "fmax" Native,
    Builtin "fmin" Native,
    Builtin "feq" Native,
    Builtin "fneq" Native,
    Builtin "<." Native,
    Builtin ">." Native,
    Builtin "<=." Native,
    Builtin ">=." Native,

    -- conversions
    Builtin "to_int" Native,
    Builtin "to_float" Native,

    -- strings
    Builtin "++" Native,
    Builtin "slen" Native,
    Builtin "sub" Native,
    Builtin "split" Native,
    Builtin "join" Native,
    Builtin "trim" Native,
    Builtin "upper" Native,
    Builtin "lower" Native,
    Builtin "contains" Native,
    Builtin "replace" Native,
    Builtin "seq" Native,
    Builtin "sneq" Native,

    -- booleans
    Builtin "not" Native,
    Builtin "||" Native,
    Builtin "&&" Native,
    Builtin "^" Native,
    Builtin "nor" Native,
    Builtin "nand" Native,
    -- the conjunction the paper's examples are written with; `&&` is the name
    -- `app/std.marr` gives it
    Builtin "and" Native,

    -- introspection and memory
    Builtin "force" Native,
    Builtin "whnf" Native,

    -- the polymorphic groups of `app/std.marr`, unpacked (see the note above):
    -- `Functions`
    Builtin "id" Native,
    Builtin "const" Native,
    Builtin "flip" Native,
    Builtin "compose" Native,
    Builtin "apply" Native,
    Builtin "curry" Native,
    Builtin "uncurry" Native,

    -- `Arrays`
    Builtin "head" Native,
    Builtin "tail" Native,
    Builtin "empty" Native,
    Builtin "alen" Native,
    Builtin "map" Native,
    Builtin "filter" Native,
    Builtin "any" Native,
    Builtin "all" Native,
    Builtin "foldl" Native,
    Builtin "foldr" Native,
    Builtin "concat" Native,
    Builtin "zip" Native,
    Builtin "at" Native,
    Builtin "take" Native,
    Builtin "drop" Native,

    -- `Pairs`
    Builtin "fst" Native,
    Builtin "snd" Native,

    -- `Conv` (`parse` is still missing: see TODO)
    Builtin "show" Native,

    -- `try` handles `Error` inside the language: it installs a handler for the
    -- body, so it is a function, not an operation whose clause a handler needs.
    Builtin "try" Native,

    Builtin "say" (Op "Output"),
    Builtin "sayn" (Op "Output"),
    Builtin "trace" (Op "Output"),

    Builtin "read_string" (Op "Input"),
    Builtin "read_int" (Op "Input"),
    Builtin "read_float" (Op "Input"),
    Builtin "read_boolean" (Op "Input"),

    Builtin "random_int" (Op "Random"),
    Builtin "random_float" (Op "Random"),
    Builtin "random_boolean" (Op "Random"),
    Builtin "random_string" (Op "Random"),

    Builtin "time_ms" (Op "Time"),
    Builtin "sleep" (Op "Time"),

    -- `Env`, `File` and `System` are declared by `app/std.marr` and implemented
    -- here; none of them needs a record, because their operations are ordinary
    -- effect operations.
    Builtin "get_env" (Op "Env"),
    Builtin "set_env" (Op "Env"),

    Builtin "read_file" (Op "File"),
    Builtin "write_file" (Op "File"),
    Builtin "append_file" (Op "File"),
    Builtin "file_exists" (Op "File"),
    Builtin "delete_file" (Op "File"),
    Builtin "list_directory" (Op "File"),

    Builtin "args" (Op "System"),
    Builtin "hostname" (Op "System"),
    Builtin "system" (Op "System"),
    Builtin "exit" (Op "System"),

    -- `error` is the operation of `Error` a handler catches; `assert` is a
    -- plain function that performs it, so a handler needs one clause, not two.
    Builtin "error" (Op "Error"),
    Builtin "assert" Native,

    -- the records of the library, field by field as `app/std.marr` lists them
    Builtin "Numbers" (Record [
        "+", "-", "*", "/", "%", "neg", "abs", "max", "min",
        "ieq", "ineq", "<", ">", "<=", ">=",
        "+.", "-.", "*.", "/.", "%.", "fneg", "fabs", "fmax", "fmin",
        "feq", "fneq", "<.", ">.", "<=.", ">=.",
        "to_int", "to_float"]),
    Builtin "Strings" (Record [
        "++", "slen", "sub", "split", "join", "trim", "upper", "lower",
        "contains", "replace", "seq", "sneq"]),
    Builtin "Booleans" (Record [
        "not", "||", "&&", "^", "nor", "nand"])
  ]

names :: [Text]
names = map bName builtins

namesOfKind :: (BuiltinKind -> Bool) -> [Text]
namesOfKind p = [bName b | b <- builtins, p (bKind b)]
