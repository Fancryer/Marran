{-# LANGUAGE OverloadedStrings #-}
module ExamplesSpec (eSpec) where

import Control.Exception (AsyncException (HeapOverflow))
import Control.Monad (forM_)
import Data.List (isInfixOf, isPrefixOf)
import Data.Maybe (listToMaybe)
import qualified Data.Text as T
import System.Environment (setEnv)
import Test.Hspec

import IntInterpreter (InterpError (..), errorCodeOf, heapError)
import Span (isNoSpan, spanAt)
import Utils (Pretty (..))
import Suite (cases, rejectedProgram, programPath, runProgram, runProgramWithInput, runSource, runSourceWithInput)

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

  describe "annotations on expressions" $ do
    it "lets an annotation refine an aggregate the checker could not pin down" $ do
      -- `[]` on its own has element type `Nothing`; the annotation says which
      -- array the reader means, and `head` then has something to return.
      r <- runSourceWithInput "annot_empty_array.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val xs = [] : [Int];"
        , "  sayn xs;"
        , "  sayn (1 : Int, 2)"
        ]
      case r of
        Left err -> expectationFailure $ "the annotation must refine the type: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["[]", "(1, 2)"]

    it "rejects an annotation that the expression cannot have" $ do
      r <- runSourceWithInput "annot_mismatch.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  sayn (1 : Boolean)"
        ]
      case r of
        Left err -> do
          err `shouldSatisfy` ("E0003" `isInfixOf`)
          err `shouldSatisfy` ("1 : Boolean" `isInfixOf`)
        Right _ -> expectationFailure "the checker must reject `1 : Boolean`"

    it "rejects an annotation that hides the latent effects of a function" $ do
      r <- runSourceWithInput "annot_pure_arrow.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  sayn ({(x) = sayn x} : Int -> {} ())"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("Output" `isInfixOf`)
        Right _ -> expectationFailure
          "the body prints, so a pure arrow row must be rejected"

    it "annotates the whole application, not its argument" $ do
      -- `inc 1 : Int` is `(inc 1) : Int`.  A weaker precedence would make the
      -- annotation apply to `1` in some positions and to the call in others.
      r <- runSourceWithInput "annot_application.marr" "" $ T.unlines
        [ "funct inc (x Int) : Int = + x 1"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (inc 1 : Int);"
        , "  sayn (let y = 5 in y : Int);"
        , "  sayn ((1, 2) : (Int, Int))"
        ]
      case r of
        Left err -> expectationFailure $ "the annotation must parse and run: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["2", "5", "(1, 2)"]

    it "does not disturb the colon of a lambda head" $ do
      r <- runSourceWithInput "annot_lambda_head.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val f = {(x) : Int = + x 1};"
        , "  sayn (f 2);"
        -- An annotation covers the whole expression, so a function that is
        -- annotated has to be bound before it can be applied: there is no
        -- `((f : T) 4)` shape, and `f : T 4` would annotate `f 4`.
        , "  val g = {(x : Int) = x} : Int -> Int;"
        , "  sayn (g 4)"
        ]
      case r of
        Left err -> expectationFailure $ "a lambda head still parses as a head: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["3", "4"]

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

    it "prints a function by its name, not by its address" $ do
      -- A function used to print as `!closure[&00000000]!`: every function was
      -- the same unreadable word, and a reader could not tell `add1` from `+`.
      r <- runSourceWithInput "print_function.marr" "" $ T.unlines
        [ "funct add1 (x Int) : Int = + x 1"
        , "funct twice (x Int) : Int = add1 (add1 x)"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn add1;"
        , "  sayn twice;"
        , "  sayn +;"
        , "  sayn pred;"
        , "  sayn [add1, twice];"
        , "  sayn (add1, twice)"
        ]
      case r of
        Left err -> expectationFailure $ "printing a function must work: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe`
          ["add1", "twice", "+", "pred", "[add1, twice]", "(add1, twice)"]

    it "says that a partial application is not the whole function" $ do
      -- `add 1` is a function, but it is not `add`: printing the bare name would
      -- claim that it takes the arguments it has already been given.
      r <- runSourceWithInput "print_partial.marr" "" $ T.unlines
        [ "funct add (x Int) (y Int) : Int = + x y"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (add 1);"
        , "  sayn (map {x = + x 1});"
        , "  sayn (add 1 2);"
        , "  sayn (seq (show (add 1)) '<partial: add>')"
        ]
      case r of
        Left err -> expectationFailure $ "printing a partial application must work: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe`
          ["<partial: add>", "<partial: map>", "3", "true"]

    it "prints a lambda as a lambda, since it has no name" $ do
      r <- runSourceWithInput "print_lambda.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val f = {x = + x 1};"
        , "  sayn f;"
        , "  sayn (f 1)"
        ]
      case r of
        Left err -> expectationFailure $ "printing a lambda must work: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["<lambda>", "2"]

    it "prints a delayed element as its value, not as a thunk" $ do
      -- Array and record fields hold delayed expressions.  A printed value is
      -- the value, so the element is forced on the way out instead of showing
      -- `!vthunk: + 1 2!`.
      r <- runSourceWithInput "print_thunk.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  sayn [+ 1 2, 3];"
        , "  sayn #{val a = + 1 2};"
        , "  sayn (add1, 1)"
        , ""
        , "funct add1 (x Int) : Int = + x 1"
        ]
      case r of
        Left err -> expectationFailure $ "printing a delayed element must work: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe`
          ["[3, 3]", "#{val a = 3}", "(add1, 1)"]

    it "`trace` shows the value it is given, after its label" $ do
      -- `app/std.marr` declares `trace : String -> `A -> {Output} `A`, so the
      -- label is part of the call, and the printed value is what the call
      -- returns: `sayn (trace 'x' 5)` prints `x: 5` and then `5`.
      r <- runSourceWithInput "trace_value.marr" "" $ T.unlines
        [ "funct add1 (x Int) : Int = + x 1"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (trace 'calc' (add1 41));"
        , "  sayn (trace 'sum' (+ 1 2));"
        , "  sayn (trace 'fn' add1);"
        , "  sayn (trace 'arr' [+ 1 2, 3]);"
        , "  sayn (trace 'rec' #{val a = + 1 2})"
        ]
      case r of
        Left err -> expectationFailure $ "`trace` must take a label and a value: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe`
          ["calc: 42", "42", "sum: 3", "3", "fn: add1", "add1",
           "arr: [3, 3]", "[3, 3]", "rec: #{val a = 3}", "#{val a = 3}"]

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

  describe "Nothing is the bottom type" $ do
    it "types `[[1], []]` and `[[], [1]]` the same way" $ do
      -- The empty array is `[Nothing]`, and `Nothing <: T`; an ordinary
      -- unification only knows that when the bottom type is on the left, so
      -- the order of the components used to matter.
      r <- runSourceWithInput "empty_arrays.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  sayn [[1], []];"
        , "  sayn [[], [1]]"
        ]
      case r of
        Left err -> expectationFailure $
          "the order of the components must not matter: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe`
          ["[[1], []]", "[[], [1]]"]

    it "rejects an `Int` where `Nothing` is declared" $ do
      -- `Nothing` is a subtype of everything, but nothing is a subtype of it
      -- except itself: a parameter declared `Nothing` stays empty.
      r <- runSourceWithInput "bottom_param.marr" "" $ T.unlines
        [ "funct f (x Nothing) : Int = 0"
        , ""
        , "funct main () : {Output} () = sayn (f 1)"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("Nothing" `isInfixOf`)
        Right out -> expectationFailure $
          "an Int is not a Nothing; got output: " ++ take 300 out

  describe "assignment to a path" $ do
    it "writes a field and the right-hand side sees the old value" $ do
      -- P1-3: `r@a := + r@a 1` is a rebinding of the field, not an update of
      -- the record: the right-hand side is delayed, so `r@a` still names the
      -- old cell while it is being built.
      r <- runSourceWithInput "path_assign_old.marr" "" $ T.unlines
        [ "funct main () : {Output; Var; Cell; Read; Rebind} () ="
        , "  var r = #{ var a = 1; val b = 10 };"
        , "  r@a := + r@a 1;"
        , "  sayn r@a;"
        , "  sayn r@b"
        ]
      case r of
        Left err -> expectationFailure $ "a path assignment must type-check: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["2", "10"]

    it "walks a nested path" $ do
      r <- runSourceWithInput "path_assign_nested.marr" "" $ T.unlines
        [ "funct main () : {Output; Var; Cell; Read; Rebind} () ="
        , "  var r = #{ var a = #{ var b = 1 }; val c = 5 };"
        , "  r@a@b := + r@a@b 10;"
        , "  sayn r@a@b;"
        , "  sayn r@c"
        ]
      case r of
        Left err -> expectationFailure $ "a nested path must type-check: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["11", "5"]

    it "is seen by a closure that reads the field afterwards" $ do
      -- The write replaces the binding of the field in the record's
      -- environment, like S-Rebind does for a name, so an existing closure
      -- reads the new value.
      r <- runSourceWithInput "path_assign_closure.marr" "" $ T.unlines
        [ "funct main () : {Output; Var; Cell; Read; Rebind} () ="
        , "  var r = #{ var a = 1 };"
        , "  val g = {r@a};"
        , "  r@a := 2;"
        , "  sayn (g ());"
        , "  sayn r@a"
        ]
      case r of
        Left err -> expectationFailure $ "the closure must type-check: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["2", "2"]

    it "writes a var field of a val record" $ do
      -- The binding of the record and the mutability of the field are separate
      -- questions: `val r` freezes the name `r`, not the `var` fields inside
      -- the record it names, so `r@a := 2` is allowed and `r := ...` is not.
      r <- runSourceWithInput "path_assign_val_record.marr" "" $ T.unlines
        [ "funct main () : {Output; Cell; Read; Rebind} () ="
        , "  val r = #{ var a = 1 };"
        , "  r@a := 2;"
        , "  sayn r@a"
        ]
      case r of
        Left err -> expectationFailure $
          "a field of a `val` record is writable when the field is `var`: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["2"]

    it "refuses to write a val field" $ do
      r <- runSourceWithInput "path_assign_val_field.marr" "" $ T.unlines
        [ "funct main () : {Output; Cell; Read; Rebind} () ="
        , "  var r = #{ val a = 1 };"
        , "  r@a := 2;"
        , "  sayn r@a"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("r@a" `isInfixOf`)
        Right out -> expectationFailure $
          "a `val` field must not be assignable; got output: " ++ take 300 out

    it "refuses to walk into a value that is not a record" $ do
      r <- runSourceWithInput "path_assign_not_record.marr" "" $ T.unlines
        [ "funct main () : {Output; Cell; Read; Rebind} () ="
        , "  var x = 1;"
        , "  x@a := 2;"
        , "  sayn x"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("Int" `isInfixOf`)
        Right out -> expectationFailure $
          "an Int has no fields; got output: " ++ take 300 out

    it "refuses an unknown field" $ do
      r <- runSourceWithInput "path_assign_no_field.marr" "" $ T.unlines
        [ "funct main () : {Output; Cell; Read; Rebind} () ="
        , "  var r = #{ var a = 1 };"
        , "  r@nope := 2;"
        , "  sayn r@a"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("nope" `isInfixOf`)
        Right out -> expectationFailure $
          "the record has no field `nope`; got output: " ++ take 300 out

    it "pays Rebind, Cell and the walk in the row" $ do
      -- The row of `r@a := ...` is the row of the right-hand side, the rows of
      -- the records the path walked (a `var` field on the way costs `Read`) and
      -- `Rebind`; the construction of the record itself is `Cell` and `Var`.
      r <- runSourceWithInput "path_assign_row.marr" "" $ T.unlines
        [ "funct main () : {Output; Cell; Read} () ="
        , "  var r = #{ var a = 1 };"
        , "  r@a := 2;"
        , "  sayn r@a"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("Rebind" `isInfixOf`)
        Right out -> expectationFailure $
          "the assignment must charge Rebind; got output: " ++ take 300 out

  describe "records are updated, not extended" $ do
    it "keeps the fields of the base" $ do
      r <- runSourceWithInput "record_update.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val base = #{ val a = 1; val b = 2 };"
        , "  val s = #{ base | val c = 3 };"
        , "  sayn s;"
        , "  sayn s@a"
        ]
      case r of
        Left err -> expectationFailure $ "an update must keep the base fields: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe`
          ["#{val a = 1; val b = 2; val c = 3}", "1"]

    it "replaces a field and leaves the base alone" $ do
      r <- runSourceWithInput "record_update_replace.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val base = #{ val a = 1 };"
        , "  val s = #{ base | val a = 2 };"
        , "  sayn s;"
        , "  sayn base"
        ]
      case r of
        Left err -> expectationFailure $ "a replaced field must update the result: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe`
          ["#{val a = 2}", "#{val a = 1}"]

    it "adds the type of the base fields to the result" $ do
      -- The type of `s` must name `a`, or `s@a` would not type-check even at
      -- run time.
      r <- runSourceWithInput "record_update_type.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val base = #{ val a = 1 };"
        , "  val s = #{ base | val b = 'x' };"
        , "  sayn s@a"
        ]
      case r of
        Left err -> expectationFailure $ "s@a must type-check: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["1"]

    it "refuses to change the mutability of a field" $ do
      r <- runSourceWithInput "record_update_mut.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  val base = #{ val a = 1 };"
        , "  val s = #{ base | var a = 2 };"
        , "  sayn s"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("var" `isInfixOf`)
        Right out -> expectationFailure $
          "a field must not change mutability; got output: " ++ take 300 out

  describe "builtins are as lazy as the language" $ do
    it "`and false x` never touches `x`" $ do
      -- `and` used to force its second argument unconditionally, so a program
      -- that short-circuited diverged instead.
      r <- runSourceWithInput "lazy_and.marr" "" $ T.unlines
        [ "funct spin (n Int) : Boolean = spin n"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (and false (spin 1))"
        ]
      case r of
        Left err -> expectationFailure $ "`and` must short-circuit: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["false"]

    it "`and true x` is the value of `x`" $ do
      r <- runSourceWithInput "lazy_and_true.marr" "" $ T.unlines
        [ "funct spin (n Int) : Int = spin n"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (and true (ieq 1 1));"
        , "  sayn (and true (ieq 1 2))"
        ]
      case r of
        Left err -> expectationFailure $ "`and true x` must be `x`: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["true", "false"]

    it "`if` does not touch the branch it does not take" $ do
      r <- runSourceWithInput "lazy_if.marr" "" $ T.unlines
        [ "funct spin (n Int) : Int = spin n"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (if true then 1 else spin 2)"
        ]
      case r of
        Left err -> expectationFailure $ "`if` must be lazy: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["1"]

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

  describe "enums and match" $ do
    it "builds a value by applying its constructor, and prints it without `#`" $ do
      r <- runSourceWithInput "enum_print.marr" "" $ T.unlines
        [ "enum Maybe[a] | Some (val v : a) | None"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (Some 5);"
        , "  sayn None"
        ]
      case r of
        Left err -> expectationFailure $ "an enum value must print: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["Some 5", "None"]

    it "selects the clause whose constructor matches" $ do
      r <- runSourceWithInput "enum_match.marr" "" $ T.unlines
        [ "enum Maybe[a] | Some (val v : a) | None"
        , ""
        , "funct value (m Maybe[Int]) : Int ="
        , "  match (m) to"
        , "    | #Some x => x"
        , "    | #None => 0"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (value (Some 3));"
        , "  sayn (value None)"
        ]
      case r of
        Left err -> expectationFailure $ "`match` must select a clause: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["3", "0"]

    it "lets the first clause that fits win, and a guard decide" $ do
      r <- runSourceWithInput "match_guard.marr" "" $ T.unlines
        [ "funct classify (n Int) : String ="
        , "  match (n) to"
        , "    | x if (ieq x 0) => 'zero'"
        , "    | 1 => 'one'"
        , "    | 2 3 => 'two or three'"
        , "    | _ => 'other'"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (classify 0);"
        , "  sayn (classify 1);"
        , "  sayn (classify 3);"
        , "  sayn (classify 9)"
        ]
      case r of
        Left err -> expectationFailure $ "a guarded clause must decide: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe`
          ["zero", "one", "two or three", "other"]

    it "binds the whole subject with `as`" $ do
      r <- runSourceWithInput "match_as.marr" "" $ T.unlines
        [ "funct name (n Int) : String ="
        , "  match (n) to"
        , "    | 1 as one => 'one'"
        , "    | other => 'other'"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (name 1);"
        , "  sayn (name 2)"
        ]
      case r of
        Left err -> expectationFailure $ "`as` must bind the subject: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["one", "other"]

    it "compares against a value the program already has with `val`" $ do
      r <- runSourceWithInput "match_val.marr" "" $ T.unlines
        [ "funct same (n Int) (m Int) : Boolean ="
        , "  match (n) to"
        , "    | val m => true"
        , "    | _ => false"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (same 1 1);"
        , "  sayn (same 1 2)"
        ]
      case r of
        Left err -> expectationFailure $ "`val` must compare with `==`: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["true", "false"]

    it "splits a string with `|->` and `<-|`" $ do
      r <- runSourceWithInput "match_split.marr" "" $ T.unlines
        [ "funct tail_of (s String) : String ="
        , "  match (s) to"
        , "    | 'ab' |-> rest => rest"
        , "    | rest <-| 'yz' => rest"
        , "    | _ => 'none'"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (tail_of 'abcdef');"
        , "  sayn (tail_of 'wxyz');"
        , "  sayn (tail_of 'nope')"
        ]
      case r of
        Left err -> expectationFailure $ "a split pattern must type-check: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["cdef", "wx", "none"]

    it "tells an exact array, a head and a tail, and at least two apart" $ do
      r <- runSourceWithInput "match_array.marr" "" $ T.unlines
        [ "funct shape (xs [Int]) : String ="
        , "  match (xs) to"
        , "    | [a b] => 'two'"
        , "    | [a; rest] => 'head'"
        , "    | [] => 'empty'"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (shape [1, 2]);"
        , "  sayn (shape [1, 2, 3]);"
        , "  sayn (shape [])"
        ]
      case r of
        Left err -> expectationFailure $ "an array pattern must type-check: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["two", "head", "empty"]

    it "reads a var field of an enum and charges Read" $ do
      r <- runSourceWithInput "enum_var_read.marr" "" $ T.unlines
        [ "enum Mut | Box (var x : Int) | Empty"
        , ""
        , "funct unbox (b Mut) : {Read} Int ="
        , "  match (b) to"
        , "    | #Box x => x"
        , "    | #Empty => 0"
        , ""
        , "funct main () : {Output; Var; Read} () ="
        , "  sayn (unbox (Box 7));"
        , "  sayn (unbox Empty)"
        ]
      case r of
        Left err -> expectationFailure $ "a var field must be readable: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["7", "0"]

    it "rejects a match that leaves a constructor unhandled" $ do
      r <- runSourceWithInput "match_gap.marr" "" $ T.unlines
        [ "enum Maybe[a] | Some (val v : a) | None"
        , ""
        , "funct value (m Maybe[Int]) : Int ="
        , "  match (m) to"
        , "    | #Some x => x"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (value (Some 1))"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("E0021" `isInfixOf`)
        Right out -> expectationFailure $
          "a missing constructor is a static error; got output: " ++ take 300 out

    it "compares two values structurally with `==` and by identity with `===`" $ do
      -- `===` is the value itself, not its content: the two `1`s are two
      -- values, so `1 === 1` is false while `== 1 1` is true.
      r <- runSourceWithInput "builtin_compare.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  sayn (== 1 1);"
        , "  sayn (=== 1 1);"
        , "  sayn (!= 1 2);"
        , "  sayn (!== 1 1)"
        ]
      case r of
        Left err -> expectationFailure $ "the comparisons must type-check: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe`
          ["true", "false", "true", "true"]

  describe "memory" $ do
    it "a long tail-recursive loop finishes and prints its result" $ do
      r <- runSourceWithInput "long_loop.marr" "" $ T.unlines
        [ "funct step (i Int) (acc Int) : Int ="
        , "  if ieq i 0 then acc else step (pred i) (+ acc 1)"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (step 1000000 0)"
        ]
      case r of
        Left err -> expectationFailure $ "the loop must not run out of memory: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["1000000"]

    it "a structure that becomes unreachable is collected" $ do
      -- Each iteration builds a record over `i` and drops it.  With a growing
      -- table of cells this loop is the one that used to exhaust the heap.
      r <- runSourceWithInput "gc_records.marr" "" $ T.unlines
        [ "funct burn (i Int) : Int ="
        , "  if ieq i 0 then 0 else"
        , "    let garbage = #{ val left = i; val right = - i 1 } in"
        , "    if ieq garbage@left 0 then 0 else burn (pred i)"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (burn 200000)"
        ]
      case r of
        Left err -> expectationFailure $ "the garbage must be collected: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["0"]

    it "an exhausted heap is a diagnostic with a code and a position" $ do
      let err = heapError (spanAt "mem.marr" 5 3) HeapOverflow
      errorCodeOf err `shouldBe` Just "E0019"
      T.unpack (pretty err) `shouldSatisfy` ("out of memory" `isInfixOf`)
      ieSpan err `shouldSatisfy` (not . isNoSpan)

    it "a value that needs itself is a diagnostic, not a hang" $ do
      -- `val y = + x 0` closes over the environment before `x` is rebound, so
      -- `y` reads whatever `x` is when it is forced; after `x := + y 1` the two
      -- cells wait for each other.  The model has no rule for the term, so the
      -- interpreter must not spin: it reports the cycle at the delayed
      -- expression and keeps the position a reader can act on.
      r <- runSourceWithInput "blackhole.marr" "" $ T.unlines
        [ "funct main () : {Output; Var; Read; Rebind; Cell} () ="
        , "  var x = 1;"
        , "  val y = + x 0;"
        , "  x := + y 1;"
        , "  sayn y"
        ]
      case r of
        Left err -> do
          err `shouldSatisfy` ("E0020" `isInfixOf`)
          err `shouldSatisfy` ("depends on itself" `isInfixOf`)
          lines err `shouldSatisfy` any (" --> " `isPrefixOf`)
        Right out -> expectationFailure $
          "a cyclic thunk must be a diagnostic, got output: " ++ take 300 out

  describe "the standard library" $ do
    it "gives a native name to a module that imported it, and hides it otherwise" $ do
      -- A native name is not a global: a module sees the names of the native
      -- modules it imported.  Importing `Numbers` brings `+` and `pred`, and
      -- nothing else; importing nothing leaves even `+` unbound.
      r <- runSource "native_imports.marr" "" $ T.unlines
        [ "module Main [funct main]"
        , "import @native Numbers"
        , "import @native Output"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (+ 1 2);"
        , "  sayn (pred 5)"
        ]
      case r of
        Left err -> expectationFailure $ "the imported names must be visible: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["3", "4"]

    it "refuses a native name of a module that was not imported" $ do
      -- `slen` belongs to `Strings`, which this module did not import, so the
      -- checker reports it although the interpreter has the value below.
      r <- runSource "native_hidden.marr" "" $ T.unlines
        [ "module Main"
        , "import @native Numbers"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (slen 'abc')"
        ]
      case r of
        Left err -> err `shouldSatisfy` isInfixOf "E0007"
        Right out -> expectationFailure $
          "a native name that was not imported must be rejected, got: " ++ take 300 out

    it "reports a zero divisor through `Error`, so a handler can catch it" $ do
      r <- runSourceWithInput "division_by_zero.marr" "" $ T.unlines
        [ "funct safe_div (a Int) (b Int) : {Output} Int ="
        , "  (under Error to"
        , "    (/ a b)"
        , "  handle"
        , "  | error e => sayn (++ 'caught: ' e); 0"
        , "  | then x => x)"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (safe_div 10 2);"
        , "  sayn (safe_div 1 0)"
        ]
      case r of
        Left err -> expectationFailure $ "`/` must be catchable: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe`
          ["5", "caught: division by zero", "0"]

    it "takes a remainder of decimals whose quotient repeats" $ do
      -- `%.` computed the quotient with `Scientific`'s `Fractional` instance,
      -- which goes through `fromRational` and throws on a repeating decimal:
      -- `5.7 %. 6.28` killed the interpreter instead of returning 5.7.
      r <- runSourceWithInput "decimal_remainder.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  sayn (5.7 `%.` 6.28);"
        , "  sayn (fneg 7.5 `%.` 2.0);"
        , "  sayn (6.28 `%.` 2.0)"
        ]
      case r of
        Left err -> expectationFailure $ "`%.` must not crash on 5.7 %. 6.28: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe`
          ["5.7", "-1.5", "0.28"]

    it "an uncaught `error` is a diagnostic with a code of its own" $ do
      r <- runSourceWithInput "uncaught_error.marr" "" $ T.unlines
        [ "funct main () : {Output; Error} () ="
        , "  sayn (error 'boom')"
        ]
      case r of
        Left err -> do
          err `shouldSatisfy` ("E0020" `isInfixOf`)
          err `shouldSatisfy` ("boom" `isInfixOf`)
        Right out -> expectationFailure $
          "an uncaught error must be a diagnostic; got output: " ++ take 300 out

    it "`||` does not touch its second argument when the first one decides" $ do
      r <- runSourceWithInput "lazy_or.marr" "" $ T.unlines
        [ "funct spin (n Int) : Boolean = spin n"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (|| true (spin 1));"
        , "  sayn (&& false (spin 2))"
        ]
      case r of
        Left err -> expectationFailure $ "`||` and `&&` must short-circuit: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["true", "false"]

    it "slices a string past its ends without failing" $ do
      -- `sub` takes a start and a length, so a slice that runs past the end is
      -- simply shorter: a reader of `sub 0 n s` should not have to guard n.
      r <- runSourceWithInput "sub_slice.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  sayn (sub 1 3 'abcdef');"
        , "  sayn (sub 0 100 'abc');"
        , "  sayn (sub 10 2 'abc');"
        , "  sayn (slen (sub 2 0 'abc'))"
        ]
      case r of
        Left err -> expectationFailure $ "`sub` must not fail on a long length: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["bcd", "abc", "", "0"]

    it "keeps `id` and `const` lazy, so an argument they ignore is not forced" $ do
      -- `id` returns its argument's address, not its value: a delayed spin that
      -- neither is asked for must not run, and `head` must not force the first
      -- element either -- the pending row of the array says what that costs.
      r <- runSourceWithInput "lazy_id.marr" "" $ T.unlines
        [ "funct spin (n Int) : Int = spin n"
        , ""
        , "funct main () : {Output} () ="
        , "  sayn (const 1 (spin 2));"
        , "  sayn (alen (map {x = spin x} []))"
        ]
      case r of
        Left err -> expectationFailure $ "`const` and `map` must not force: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["1", "0"]

    it "reports an index past the end through `Error`, so `try` can catch it" $ do
      r <- runSourceWithInput "at_out_of_range.marr" "" $ T.unlines
        [ "funct main () : {Output; Error} () ="
        , "  sayn (try {u = at [1, 2] 5} {e = 0});"
        , "  sayn (at [10, 20] 1)"
        ]
      case r of
        Left err -> expectationFailure $ "`at` must report through `Error`: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["0", "20"]

    it "runs `Env` and `File` as effects with operations, not as constants" $ do
      -- The operations are named by a row: a program that does not declare
      -- `File` cannot call `write_file`, and `get_env` of a name that was just
      -- set reads the value back.
      r <- runSourceWithInput "env_and_file.marr" "" $ T.unlines
        [ "funct main () : {Output; Env; File; Error} () ="
        , "  set_env 'MARRAN_TEST_VAR' 'v';"
        , "  sayn (get_env 'MARRAN_TEST_VAR');"
        , "  val path = 'marran_spec_probe.tmp';"
        , "  write_file path 'x';"
        , "  sayn (read_file path);"
        , "  delete_file path;"
        , "  sayn (file_exists path)"
        ]
      case r of
        Left err -> expectationFailure $ "`Env` and `File` must run: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["v", "x", "false"]

    it "rejects `write_file` in a function whose row does not name `File`" $ do
      r <- runSourceWithInput "file_without_row.marr" "" $ T.unlines
        [ "funct main () : {Output} () ="
        , "  write_file 'x' 'y'"
        ]
      case r of
        Left err -> err `shouldSatisfy` ("File" `isInfixOf`)
        Right out -> expectationFailure $
          "a call to `write_file` must charge `File`; got output: " ++ take 300 out

    it "reads a line of input as a string, without requiring quotes" $ do
      -- The line is the answer, not source: a program that asks a person for a
      -- name must accept `world` typed as it is.  A line that happens to be a
      -- string literal keeps it, because the input is never parsed.
      r <- runSourceWithInput "read_string_plain.marr" "world\n'quoted'\n" $ T.unlines
        [ "funct main () : {Output; Input} () ="
        , "  sayn (++ 'hello, ' (read_string ()));"
        , "  sayn (read_string ())"
        ]
      case r of
        Left err -> expectationFailure $ "`read_string` must take the line as it is: " ++ err
        Right out -> filter (not . isReport) (lines out) `shouldBe` ["hello, world", "'quoted'"]

  describe "running a program by path" $ do
    it "finds a file whose path has a directory, not just a bundled name" $ do
      -- `--run` used to accept only a bare name under `app/marr`, so a file
      -- anywhere else could not be run at all.  A path with a separator is
      -- taken as written; a bare name still looks in the bundled directories.
      let dir = "app/marr"
      found <- programPath (dir ++ "/scoping")
      found `shouldBe` Just (dir ++ "/scoping.marr")
      -- An absolute path is a path too, and `.marr` is not doubled.
      abs1 <- programPath (dir ++ "/scoping.marr")
      abs1 `shouldBe` Just (dir ++ "/scoping.marr")

    it "does not invent a path for a name it cannot find" $ do
      found <- programPath "no_such_program_anywhere"
      found `shouldBe` Nothing

  where
    isReport l = "EVENTS:" `isInfixOf` l || "EVENT-VIOLATION" `isInfixOf` l
    isCodedHeader l =
      case words l of
        (w:_) -> "error[" `isPrefixOf` w
        [] -> False
