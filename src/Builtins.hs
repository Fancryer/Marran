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
    Builtin "pred" Native,
    Builtin "not" Native,
    Builtin "+" Native,
    Builtin "-" Native,
    Builtin "force" Native,
    Builtin "whnf" Native,
    Builtin "ieq" Native,
    Builtin "and" Native,
    Builtin ">" Native,
    Builtin "<" Native,
    Builtin "args" Native,

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
    Builtin "sleep" (Op "Time")
  ]

names :: [Text]
names = map bName builtins

namesOfKind :: (BuiltinKind -> Bool) -> [Text]
namesOfKind p = [bName b | b <- builtins, p (bKind b)]
