{-# LANGUAGE OverloadedStrings #-}
module ExamplesSpec (eSpec) where

import Control.Monad (forM_)
import Data.List (isInfixOf, isPrefixOf)
import Data.Maybe (listToMaybe)
import qualified Data.Text as T
import System.Environment (setEnv)
import Test.Hspec

import Suite (cases, rejectedProgram, runProgram, runProgramWithInput, runSourceWithInput)

-- | The example programs of the paper, as tests.  The event check of the
--   interpreter is enabled, so a mutation event that the declared row does not
--   license fails the corresponding test.
eSpec :: Spec
eSpec = beforeAll_ (setEnv "MARRAN_CHECK_EVENTS" "1") $ describe "example programs" $ do
  forM_ cases $ \(name, expected) ->
    it (name ++ " prints " ++ show expected) $ do
      r <- runProgram name
      case r of
        Left err -> expectationFailure $ "program failed: " ++ err
        Right out -> do
          let ls = lines out
              violations = filter ("EVENT-VIOLATION" `isInfixOf`) ls
              printed = filter (not . isReport) ls
          violations `shouldBe` []
          printed `shouldBe` expected

  it "handle_while returns the value passed to break" $ do
    r <- runProgramWithInput "handle_while" "1\n2\n5\n"
    case r of
      Left err -> expectationFailure $ "program failed: " ++ err
      Right out -> do
        let ls = lines out
            violations = filter ("EVENT-VIOLATION" `isInfixOf`) ls
            printed = filter (not . isReport) ls
        violations `shouldBe` []
        printed `shouldBe` ["7"]

  it "a snapshot cannot capture `resume`" $ do
    r <- runSourceWithInput "snapshot_resume.marr" "" $ T.unlines
      [ "effect E"
      , "  ask : () -> Int"
      , "end"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (under E to"
      , "    (ask (); 0)"
      , "  handle"
      , "  | ask c =>"
      , "      imm f = {(x) = resume x};"
      , "      7"
      , "  | then s => s)"
      ]
    case r of
      Left err -> err `shouldSatisfy` ("snapshot cannot capture `resume`" `isInfixOf`)
      Right _ -> expectationFailure "a snapshot of `resume` should fail"

  it "a continuation cannot be resumed after its handler returned" $ do
    r <- runSourceWithInput "resume_gone.marr" "" $ T.unlines
      [ "row M = {Var; Cell; Read; Rebind}"
      , "effect E"
      , "  ask : () -> Int"
      , "end"
      , ""
      , "funct main () : {... M; Output} () ="
      , "  var saved = {(x) = x};"
      , "  (under E to"
      , "    (ask (); 0)"
      , "  handle"
      , "  | ask c =>"
      , "      saved := {(x) = resume x};"
      , "      7"
      , "  | then s => s);"
      , "  sayn (saved 1)"
      ]
    case r of
      Left err -> err `shouldSatisfy` ("after its handler returned" `isInfixOf`)
      Right _ -> expectationFailure "resuming after the handler should fail"

  it "an operation provided by two stacked handlers is ambiguous" $ do
    r <- runSourceWithInput "ambiguous_op.marr" "" $ T.unlines
      [ "effect A"
      , "  ping : () -> Int"
      , "end"
      , ""
      , "effect B"
      , "  ping : () -> Int"
      , "end"
      , ""
      , "funct keep (x () -> {A} Int) : {A} #{ val f : () -> {A} Int } ="
      , "  #{ val f = x }"
      , ""
      , "funct main () : {Output; A; B} () ="
      , "  val r = keep {ping ()};"
      , "  sayn (under A to"
      , "    (under B to"
      , "      (r@f) ()"
      , "    handle"
      , "    | ping c => 2"
      , "    | then s => s)"
      , "  handle"
      , "  | ping c => 1"
      , "  | then s => s)"
      ]
    case r of
      Left err -> err `shouldSatisfy` ("provided by more than one effect" `isInfixOf`)
      Right _ -> expectationFailure "the ambiguous operation should fail"

  it "charges the effects of the then clause to the handler" $ do
    r <- runSourceWithInput "then_effects.marr" "" $ T.unlines
      [ "effect E"
      , "  ask : () -> Int"
      , "end"
      , ""
      , "funct run () : {Output} () ="
      , "  sayn (under E to"
      , "    (ask (); 0)"
      , "  handle"
      , "  | ask c => 1"
      , "  | then s => (var x = s; x; 0))"
      , ""
      , "funct main () : {Output} () ="
      , "  run ()"
      ]
    case r of
      Left err -> do
        err `shouldSatisfy` ("Read" `isInfixOf`)
        err `shouldSatisfy` ("Var" `isInfixOf`)
      Right out -> expectationFailure $
        "the then clause creates and reads state, so the handler must report it; got output: "
          ++ take 300 out

  it "unifies the result of the then clause with the body" $ do
    r <- runSourceWithInput "then_result.marr" "" $ T.unlines
      [ "effect E"
      , "  ask : () -> Int"
      , "end"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (under E to"
      , "    (ask (); 0)"
      , "  handle"
      , "  | ask c => 1"
      , "  | then s => ('hello'))"
      ]
    case r of
      Left err -> do
        err `shouldSatisfy` ("String" `isInfixOf`)
        err `shouldSatisfy` ("Int" `isInfixOf`)
      Right out -> expectationFailure $
        "a then clause that returns a String where the body is an Int must be rejected; got output: "
          ++ take 300 out

  it "unifies the parameter of the then clause with the body" $ do
    r <- runSourceWithInput "then_param.marr" "" $ T.unlines
      [ "effect E"
      , "  ask : () -> Int"
      , "end"
      , ""
      , "funct main () : {Output} () ="
      , "  sayn (under E to"
      , "    (ask (); 'x')"
      , "  handle"
      , "  | ask c => 'y'"
      , "  | then s => (+ 1 s))"
      ]
    case r of
      Left err -> do
        err `shouldSatisfy` ("String" `isInfixOf`)
        err `shouldSatisfy` ("Int" `isInfixOf`)
      Right out -> expectationFailure $
        "the then clause may not use a String body as an Int; got output: "
          ++ take 300 out

  it "accepts a then clause whose mutation effects are declared" $ do
    r <- runSourceWithInput "then_licensed.marr" "" $ T.unlines
      [ "effect E"
      , "  ask : () -> Int"
      , "end"
      , ""
      , "funct main () : {Output; Var; Rebind; Read} () ="
      , "  var x = 0;"
      , "  (under E to"
      , "    (ask (); 0)"
      , "  handle"
      , "  | ask c => 1"
      , "  | then s => (x := + x s; x));"
      , "  sayn x"
      ]
    case r of
      Left err -> expectationFailure $ "the declared row is sufficient: " ++ err
      Right out -> do
        out `shouldSatisfy` ("EVENTS: licensed" `isInfixOf`)
        out `shouldSatisfy` (not . ("EVENT-VIOLATION" `isInfixOf`))

  describe "aggregate types and escaping state" $ do
    it "gives a non-empty array its array type" $ do
      r <- runSourceWithInput "array_type.marr" "" $ T.unlines
        [ "funct make () : [Int] ="
        , "  [5]"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn 0"
        ]
      case r of
        Left err -> expectationFailure $
          "an array literal must have type [Int], not the element type: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["0"]

    it "lets the empty array take the annotated element type" $ do
      r <- runSourceWithInput "array_empty.marr" "" $ T.unlines
        [ "funct make () : [Int] ="
        , "  []"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn 0"
        ]
      case r of
        Left err -> expectationFailure $ "the empty array must be usable at [Int]: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["0"]

    it "parses a parenthesised pair type" $ do
      r <- runSourceWithInput "pair_type.marr" "" $ T.unlines
        [ "funct make () : (Int, Int) ="
        , "  (5, 6)"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn 0"
        ]
      case r of
        Left err -> expectationFailure $ "a pair annotation must parse: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["0"]

    it "reports Cell when a local var escapes inside an array" $ do
      r <- runSourceWithInput "array_escape.marr" "" $ T.unlines
        [ "funct make () : {Var; Read} [Int]@{Read} ="
        , "  var x = 5;"
        , "  [x]"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn 0"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("Cell" `isInfixOf`)
        Right _ -> expectationFailure
          "the array stores a thunk that reaches the local var, so the block must report Cell"

    it "reports Cell when a local var escapes inside a pair" $ do
      r <- runSourceWithInput "pair_escape.marr" "" $ T.unlines
        [ "funct make () : {Var; Read} (Int, Int)@{Read} ="
        , "  var x = 5;"
        , "  (x, 1)"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn 0"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("Cell" `isInfixOf`)
        Right _ -> expectationFailure
          "a pair stores its components as thunks, so the block must report Cell"

    it "accepts an escaping array when Cell is declared" $ do
      r <- runSourceWithInput "array_escape_ok.marr" "" $ T.unlines
        [ "funct make () : {Var; Read; Cell} [Int]@{Read} ="
        , "  var x = 5;"
        , "  [x]"
        , ""
        , "funct main () : {Output; Var; Read; Cell} () ="
        , "  sayn 0"
        ]
      case r of
        Left err -> expectationFailure $ "the declared row is sufficient: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["0"]

    it "keeps Var when the result cannot hold state" $ do
      r <- runSourceWithInput "var_not_cell.marr" "" $ T.unlines
        [ "funct make () : {Var; Read} Int ="
        , "  var x = 5;"
        , "  x"
        , ""
        , "funct main () : {Output; Var; Read} () ="
        , "  sayn (make ())"
        ]
      case r of
        Left err -> expectationFailure $
          "an Int result cannot carry the local var out of the block: " ++ err
        Right out -> do
          filter (not . isReport) (lines out) `shouldBe` ["5"]
          out `shouldSatisfy` ("EVENTS: licensed" `isInfixOf`)

  describe "pending rows of local bindings" $ do
    it "gives a closure over a local alias of a var the Read effect" $ do
      r <- runSourceWithInput "alias_closure.marr" "" $ T.unlines
        [ "funct make () : {Var; Read; Cell} () -> {Read} Int ="
        , "  var x = 5;"
        , "  val y = x;"
        , "  {y}"
        , ""
        , "funct main () : {Output; Var; Read; Cell} () ="
        , "  sayn (make () ())"
        ]
      case r of
        Left err -> expectationFailure $
          "the closure reads x through y, so its row must contain Read: " ++ err
        Right out -> do
          filter (not . isReport) (lines out) `shouldBe` ["5"]
          out `shouldSatisfy` ("EVENTS: licensed" `isInfixOf`)

    it "rejects a closure annotation that hides the Read of an alias" $ do
      r <- runSourceWithInput "alias_hidden.marr" "" $ T.unlines
        [ "funct make () : {Var; Read; Cell} () -> {} Int ="
        , "  var x = 5;"
        , "  val y = x;"
        , "  {y}"
        , ""
        , "funct main () : {Output; Var; Read; Cell} () ="
        , "  sayn 0"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("Read" `isInfixOf`)
        Right _ -> expectationFailure
          "the closure reads x through y, so a pure arrow row must be rejected"

  describe "pending rows of parameters" $ do
    it "does not make a parameter of a pure lambda state-bearing" $ do
      r <- runSourceWithInput "param_pure.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val add = {(n) = + n 1};"
        , "  sayn (add 2)"
        ]
      case r of
        Left err -> expectationFailure $
          "`+ n 1` reads nothing, so the lambda needs no Read: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["3"]

    it "accepts a state-bearing variable as an argument to a pure function" $ do
      -- The paper's own `line unit q`: the argument row is charged at the call
      -- site, so a pure identity of parameters may receive a `var` value.
      r <- runSourceWithInput "param_var_arg.marr" "" $ T.unlines
        [ "funct twice (unit Int) (qty Int) : Int = + unit qty"
        , ""
        , "funct main () : {Output; Var; Rebind; Read} () ="
        , "  var unit = 10;"
        , "  sayn (twice unit 3);"
        , "  unit := + unit 5;"
        , "  sayn (twice unit 3)"
        ]
      case r of
        Left err -> expectationFailure $
          "passing a var value to a pure function must be allowed: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["13", "18"]

    it "charges the row of a reading thunk to a pure parameter (T-App)" $ do
      r <- runSourceWithInput "param_pure_reject.marr" "" $ T.unlines
        [ "funct force_it (f () -> Int) : Int = f ()"
        , ""
        , "funct main () : {Output; Var; Read} () ="
        , "  var u = 1;"
        , "  sayn (force_it {+ u 1})"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("Read" `isInfixOf`)
        Right _ -> expectationFailure
          "the thunk reads u, so a pure parameter row must be rejected"

    it "accepts the same thunk when the parameter is row-polymorphic" $ do
      r <- runSourceWithInput "param_row_poly.marr" "" $ T.unlines
        [ "funct force_it (f () -> `R Int) : `R Int = f ()"
        , ""
        , "funct main () : {Output; Var; Read} () ="
        , "  var u = 1;"
        , "  sayn (force_it {+ u 1})"
        ]
      case r of
        Left err -> expectationFailure $
          "a row-polymorphic parameter must accept a reading thunk: " ++ err
        Right out -> do
          filter (not . isReport) (lines out) `shouldBe` ["2"]
          out `shouldSatisfy` ("EVENTS: licensed" `isInfixOf`)

    it "keeps the declared row on every arrow of a curried function" $ do
      -- A partial application is still a delayed computation that costs the
      -- whole row, so `val f = two 1` may not hide the Output.
      r <- runSourceWithInput "param_partial_row.marr" "" $ T.unlines
        [ "funct two (u Int) (q Int) : {Output} Int = sayn u; q"
        , ""
        , "funct main () : {Output} () ="
        , "  val f = two 1;"
        , "  sayn (f 2)"
        ]
      case r of
        Left err -> expectationFailure $ "the row must reach main: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["1", "2"]

    it "rejects the same program when main drops the Output" $ do
      r <- runSourceWithInput "param_partial_reject.marr" "" $ T.unlines
        [ "funct two (u Int) (q Int) : {Output} Int = sayn u; q"
        , ""
        , "funct main () : {} () ="
        , "  val f = two 1;"
        , "  f 2;"
        , "  ()"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("Output" `isInfixOf`)
        Right _ -> expectationFailure
          "f 2 outputs, so a closed empty row must be rejected"

  describe "pending rows of let names" $ do
    it "charges the row of the right-hand side at a use of a let name" $ do
      -- A `let` name is an alias of the address the right-hand side computes,
      -- so forcing it costs that row, just as forcing a `val` does.  Without
      -- this a closure over `y` was typed as pure and still read the `var`.
      r <- runSourceWithInput "let_alias_reject.marr" "" $ T.unlines
        [ "funct make () : {Var} () -> {} Int ="
        , "  var x = 5;"
        , "  let y = x in"
        , "    {y}"
        , ""
        , "funct main () : {Output} () ="
        , "  val f = make ();"
        , "  sayn (f ())"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("Read" `isInfixOf`)
        Right _ -> expectationFailure
          "the closure reads x through the alias, so a pure row is wrong"

    it "accepts the same program once the arrow names Read" $ do
      -- `Cell` as well: the closure that escapes reads `x` through the alias,
      -- so the state of `x` does leave the block inside it.
      r <- runSourceWithInput "let_alias_accept.marr" "" $ T.unlines
        [ "funct make () : {Var; Read; Cell} () -> {Read} Int ="
        , "  var x = 5;"
        , "  let y = x in"
        , "    {y}"
        , ""
        , "funct main () : {Output; Var; Read; Cell} () ="
        , "  val f = make ();"
        , "  sayn (f ())"
        ]
      case r of
        Left err -> expectationFailure $
          "a row that names Read must license the alias: " ++ err
        Right out -> do
          filter (not . isReport) (lines out) `shouldBe` ["5"]
          out `shouldSatisfy` ("EVENTS: licensed" `isInfixOf`)

    it "keeps the row of a pair pattern from being empty" $ do
      -- The pattern's type is unified with the right-hand side, so an empty
      -- annotation on a pair would drag the row down to `{}`.
      r <- runSourceWithInput "let_pair_row.marr" "" $ T.unlines
        [ "funct main () : {Output; Var; Read} () ="
        , "  var x = 3;"
        , "  let (a, b) = (x, 1) in"
        , "    sayn (+ a b)"
        ]
      case r of
        Left err -> expectationFailure $
          "a pair pattern over a reading component needs Read, not rejection: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["4"]

    it "destructures a pair that the right-hand side does not spell out" $ do
      -- The interpreter has to force the right-hand side before matching:
      -- `let (a, b) = p` used to fail with "expects a pair, but the value is
      -- an unevaluated expression" whenever `p` was a thunk.
      r <- runSourceWithInput "let_pair_thunk.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val p = (1, 2);"
        , "  let (a, b) = p in"
        , "    sayn (+ a b)"
        ]
      case r of
        Left err -> expectationFailure $
          "a pair pattern must force its right-hand side: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["3"]

    it "destructures nested components of a pair" $ do
      -- A component of a pair is a cell of its own; a nested pattern has to
      -- force it before matching, or the interpreter reports that it expects
      -- a pair but sees an unevaluated expression.
      r <- runSourceWithInput "let_pair_nested.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val p = (1, (2, 3));"
        , "  let (a, (b, c)) = p in"
        , "    sayn (+ a (+ b c))"
        ]
      case r of
        Left err -> expectationFailure $
          "a nested component has to be forced: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["6"]

    it "does not force a component that the pattern does not inspect" $ do
      -- Only a destructuring pattern needs the value.  A name pattern keeps
      -- the cell, so a component that would diverge stays unevaluated.
      r <- runSourceWithInput "let_pair_lazy_component.marr" "" $ T.unlines
        [ "funct spin (n Int) : Int = spin n"
        , "funct main () : {Output} () ="
        , "  let (a, b) = (spin 1, 2) in"
        , "    sayn b"
        ]
      case r of
        Left err -> expectationFailure $
          "a name pattern must not force its component: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["2"]

    it "destructures a record that the right-hand side does not spell out" $ do
      r <- runSourceWithInput "let_record_thunk.marr" "" $ T.unlines
        [ "funct main () : {Output; Var; Read; Cell} () ="
        , "  var x = 7;"
        , "  val r = #{ var f = x };"
        , "  let #{ var f } = r in"
        , "    sayn f"
        ]
      case r of
        Left err -> expectationFailure $
          "a record pattern must force its right-hand side: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["7"]

    it "destructures a nested record field" $ do
      r <- runSourceWithInput "let_record_nested.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val r = #{ val b = #{ val c = 2 } };"
        , "  let #{ val b } = r in"
        , "    sayn b@c"
        ]
      case r of
        Left err -> expectationFailure $
          "a nested record field has to be forced: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["2"]

    it "does not leak the alias row out of the let body" $ do
      -- `let y = x in y` reads the var inside the block and returns an Int, so
      -- the block is `{Var; Read}` — no Cell, because nothing holding state
      -- leaves it.
      r <- runSourceWithInput "let_row_scope.marr" "" $ T.unlines
        [ "funct main () : {Output; Var; Read} () ="
        , "  var x = 5;"
        , "  let y = x in"
        , "    sayn y"
        ]
      case r of
        Left err -> expectationFailure $
          "the row of the alias belongs to the let body: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["5"]

    it "freezes a closure that reads through a let alias" $ do
      -- `imm` has to freeze the row of the let body, or the snapshot would keep
      -- reading the live cell.  `a` sees the new value, `b` keeps the old one.
      r <- runSourceWithInput "let_alias_imm.marr" "" $ T.unlines
        [ "funct main () : {Output; Var; Read; Cell; Rebind} () ="
        , "  var x = 5;"
        , "  val a = {let y = x in y};"
        , "  imm b = {let y = x in y};"
        , "  x := 42;"
        , "  sayn (a ());"
        , "  sayn (b ())"
        ]
      case r of
        Left err -> expectationFailure $
          "a snapshot of a reading closure must type-check: " ++ err
        Right out -> do
          filter (not . isReport) (lines out) `shouldBe` ["42", "5"]
          out `shouldSatisfy` ("EVENTS: licensed" `isInfixOf`)

  describe "pending rows of aggregates" $ do
    it "rejects an array whose components read state when the row is empty" $ do
      r <- runSourceWithInput "array_row_empty.marr" "" $ T.unlines
        [ "funct make () : [Int] ="
        , "  var x = 5;"
        , "  [x]"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn 0"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("Read" `isInfixOf`)
        Right _ -> expectationFailure
          "`[Int]` means `[Int]@{}`, so an element that reads a var must be rejected"

    it "accepts the same array once the row is written" $ do
      r <- runSourceWithInput "array_row_read.marr" "" $ T.unlines
        [ "funct make () : {Var; Read; Cell} [Int]@{Read} ="
        , "  var x = 5;"
        , "  [x]"
        , ""
        , "funct main () : {Output; Var; Read; Cell} () ="
        , "  sayn 0"
        ]
      case r of
        Left err -> expectationFailure $
          "the pending row `@{Read}` must license the element that reads x: " ++ err
        Right _ -> pure ()

    it "accepts a wider row than the components need" $ do
      -- T-Pair and T-Rec let the annotation be any upper bound, not the
      -- smallest one: an array of literals may still be annotated `@{Read}`.
      r <- runSourceWithInput "array_row_wide.marr" "" $ T.unlines
        [ "funct make () : {Read} [Int]@{Read} ="
        , "  [1]"
        , ""
        , "funct main () : {Output; Read} () ="
        , "  val xs = make ();"
        , "  sayn 0"
        ]
      case r of
        Left err -> expectationFailure $
          "an annotation is an upper bound, so a smaller component row fits: " ++ err
        Right _ -> pure ()

    it "reads a pair annotation the same way" $ do
      r <- runSourceWithInput "pair_row_read.marr" "" $ T.unlines
        [ "funct make () : {Var; Read; Cell} (Int, Int)@{Read} ="
        , "  var x = 5;"
        , "  (x, 1)"
        , ""
        , "funct main () : {Output; Var; Read; Cell} () ="
        , "  sayn 0"
        ]
      case r of
        Left err -> expectationFailure $
          "a pair annotation must parse and license the component: " ++ err
        Right _ -> pure ()

    it "charges the pending row of a record at a field access" $ do
      -- T-Prop: reading a field costs the record's pending row.  The field is
      -- `val`, so the record is `#{val f : Int}@{Read}` and `r@f` costs Read.
      r <- runSourceWithInput "record_row_prop.marr" "" $ T.unlines
        [ "funct main () : {Output; Var; Read; Cell} () ="
        , "  var x = 5;"
        , "  val r = #{ val f = x };"
        , "  sayn (r@f)"
        ]
      case r of
        Left err -> expectationFailure $
          "the field holds a thunk that reads x, so the access costs Read: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["5"]

    it "rejects the same field access when the row omits Read" $ do
      r <- runSourceWithInput "record_row_reject.marr" "" $ T.unlines
        [ "funct main () : {Output; Var; Cell} () ="
        , "  var x = 5;"
        , "  val r = #{ val f = x };"
        , "  sayn (r@f)"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("Read" `isInfixOf`)
        Right _ -> expectationFailure
          "the pending row of the record contains Read, which main does not declare"

    it "lets a row variable be written on an aggregate" $ do
      r <- runSourceWithInput "array_row_var.marr" "" $ T.unlines
        [ "funct copy (xs [Int]@`R) : [Int]@`R = xs"
        , ""
        , "funct main () : {Output} () ="
        , "  val xs = copy [1];"
        , "  sayn 0"
        ]
      case r of
        Left err -> expectationFailure $
          "a row variable on an aggregate must parse and unify: " ++ err
        Right _ -> pure ()

    it "prints the pending row only when it is not empty" $ do
      emptyRow <- runSourceWithInput "array_row_print_empty.marr" "" $ T.unlines
        [ "funct f () : [Int] = 5"
        ]
      readRow <- runSourceWithInput "array_row_print_read.marr" "" $ T.unlines
        [ "funct f () : [Int]@{Read} = 5"
        ]
      case emptyRow of
        Left err -> do
          err `shouldSatisfy` ("[Int]" `isInfixOf`)
          err `shouldSatisfy` (not . ("@{}" `isInfixOf`))
        Right _ -> expectationFailure "the annotation mismatch must be reported"
      case readRow of
        Left err -> err `shouldSatisfy` ("@{Read}" `isInfixOf`)
        Right _ -> expectationFailure "the annotation mismatch must be reported"

  describe "printing values" $ do
    it "prints array elements, not their addresses" $ do
      -- `stringify` used `pretty` on the element addresses, so `sayn [1, 2]`
      -- printed `[#00000019, #0000001a]`.
      r <- runSourceWithInput "print_array.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  sayn [1, 2];"
        , "  sayn [['a'], ['b', 'c']];"
        , "  sayn [(1, 2), (3, 4)];"
        , "  sayn #{ val xs = [1] }"
        ]
      case r of
        Left err -> expectationFailure $ "printing an array must work: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe`
          ["[1, 2]", "[[a], [b, c]]", "[(1, 2), (3, 4)]", "#{val xs = [1]}"]

  describe "effects visible where they are declared" $ do
    it "runs an operation from a function that names the effect in its row" $ do
      r <- runSourceWithInput "effect_in_function.marr" "" $ T.unlines
        [ "effect Doubt"
        , "  ask : Int -> Int"
        , "end"
        , ""
        , "funct twice () : {Doubt} Int = + (ask 1) (ask 2)"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (under Doubt to twice ()"
        , "  handle"
        , "  | ask x => resume x"
        , "  | then s => s)"
        ]
      case r of
        Left err -> expectationFailure $ "the effect must be callable from a function: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["3"]

    it "charges the effect of an operation to the caller" $ do
      -- `ask` may only be called where `Doubt` is allowed: the operation's own
      -- declared type says nothing about the effect, so the row does.
      r <- runSourceWithInput "effect_unlicensed.marr" "" $ T.unlines
        [ "effect Doubt"
        , "  ask : Int -> Int"
        , "end"
        , ""
        , "funct twice () : Int = + (ask 1) (ask 2)"
        , ""
        , "funct main () : {Output} () = sayn (twice ())"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("Doubt" `isInfixOf`)
        Right out -> expectationFailure $
          "calling an operation without its effect in the row must be rejected; got output: "
            ++ take 300 out

    it "rejects a bare effect name in row position, suggesting `{Doubt}`" $ do
      r <- runSourceWithInput "effect_as_row.marr" "" $ T.unlines
        [ "effect Doubt"
        , "  ask : Int -> Int"
        , "end"
        , ""
        , "funct twice () : Doubt Int = + (ask 1) (ask 2)"
        , ""
        , "funct main () : {Output} () = sayn (twice ())"
        ]
      case r of
        Left err -> do
          err `shouldSatisfy` ("not a row" `isInfixOf`)
          err `shouldSatisfy` ("{Doubt}" `isInfixOf`)
          err `shouldSatisfy` (not . ("Unknown row alias" `isInfixOf`))
        Right out -> expectationFailure $
          "an effect is not a row; got output: " ++ take 300 out

    it "still lets a row alias name a row of effects" $ do
      r <- runSourceWithInput "effect_row_alias.marr" "" $ T.unlines
        [ "effect Doubt"
        , "  ask : Int -> Int"
        , "end"
        , ""
        , "row D = {Doubt}"
        , ""
        , "funct twice () : {...D} Int = + (ask 1) (ask 2)"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (under Doubt to twice ()"
        , "  handle"
        , "  | ask x => resume x"
        , "  | then s => s)"
        ]
      case r of
        Left err -> expectationFailure $ "a row alias over an effect must work: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["3"]

  it (rejectedProgram ++ " is rejected with the missing Read effect") $ do
    r <- runProgram rejectedProgram
    case r of
      Left err -> do
        err `shouldSatisfy` ("Read" `isInfixOf`)
        -- The diagnostic must look like a diagnostic: a coded header, then a
        -- location, then the source line and a caret run.
        let ls = lines err
        ls `shouldSatisfy` (not . null)
        listToMaybe ls `shouldSatisfy` maybe False isCodedHeader
        ls `shouldSatisfy` any (" --> " `isPrefixOf`)
        ls `shouldSatisfy` any ("^" `isInfixOf`)
      Right out -> expectationFailure $
        "expected a type error, got output: " ++ take 300 out
  where
    isReport l = "EVENTS:" `isInfixOf` l || "EVENT-VIOLATION" `isInfixOf` l
    isCodedHeader l =
      case words l of
        (w:_) -> "error[" `isPrefixOf` w
        [] -> False
