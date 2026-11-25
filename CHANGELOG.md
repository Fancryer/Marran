# Changelog for `Mårran`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## 0.2.3.0 - 2026-11-24

The two P0 items of the 0.2 line are closed: the `Cell` analysis no longer
lets a block carry mutable storage out of itself unannounced, and `freeze` now
reaches every value a snapshot can hold.  Both were holes in the model of
`imm`, not in its implementation.

- `Cell` is charged for state that escapes through a declared enumeration.
  `canHoldState` became the monadic `canHoldStateIn`, which looks the fields of
  an enum up in its declaration (`Scope.findEnum`) instead of reading them off
  the type, and substitutes the type arguments for the parameters.  An enum
  declared with a `var` field therefore carries state by construction.
- The last arrow of a constructor with a `var` field now carries `Var; Cell`
  (`Types.constructorTyp`): applying the constructor creates a mutable binding
  and the value owns that cell.  The charge sits on the type, so an aliased
  constructor (`val c = MkBox; c 1`) and one passed to a function
  (`apply2 MkBox`) pay it exactly as `MkBox 1` does; a program that builds a
  `var`-field enum must declare `Cell`, as it already had to for a record
  literal with a `var` field.
- Recursive enums terminate both questions (`canHoldStateIn`, `typeHoldsCell`)
  through a visited set; a cycle without a `var` field holds no cell.
- `freezeTyp` descends into the type arguments of an enum through the new
  `freezeTypeArgExcept` (`TAArray`, `TAPair`, `TAFunct`, `TARecord` with its
  mutabilities, `TAEnum`), so a record inside an enum becomes frozen too.
- A partially applied native or constructor is now a run-time value of its
  own (`VPartial`): the arguments it already received are addresses, not
  hidden inside a Haskell closure.  `share`ing such a value used to leave a
  snapshot aliasing live cells -- `val f = MkBox r; imm g = f; r@n := 10`
  read `10` through `g` and now reads the frozen `0`.  `applyValue`,
  `applyPartial`, `nativeN`, `makeEffectClosure` and `makeConstructor` build
  and apply it; `freezeCell` copies its arguments.
- `freezeCell` also copies the target of a `with` (`VTypeApp`).
- The checker refuses a snapshot of a function that applies a constructor with
  a `var` field (`imm f = {(n) = MkBox n}`), and `freezeCell` refuses a
  snapshot of the constructor itself: a constructor is a native, so freezing
  cannot rewrite its code, and applying the frozen value would allocate a
  fresh cell behind a type that no longer says `Cell`.  The value such a
  constructor builds is ordinary data and freezes normally: the `imm` builds
  it where its right-hand side already charges `Cell`, then snapshots the
  value (`imm s = MkBox 2`, also through a `val` binding).
- Assigning a field whose mutability is not `Var` is now a run-time error
  instead of a silent write into a frozen copy.  This is the backstop for the
  one case the frozen type cannot spell: a state-bearing record used as an
  enum's type argument stays a `TAVar`, because `TypeArg` has no effect row to
  carry the record's, so the static check still admits `w@v@n := 5` and the
  interpreter refuses it.

Tests: 496 examples, 0 failures.

## 0.2.2.0 - 2026-11-23

Explicit type application and the first type-directed native arrive together:
`with` now works without a `forall` in the type, and `parse` uses it to know
the type it has to build.  Imports gain a re-export rule, so a module can say
which of its names an importer sees.

- `with` no longer requires a `TForall`: `TypedIR.TEWith` carries a `TypeRep`,
  and the checker resolves the scheme of the name, substitutes the explicit
  arguments and instantiates the rest.  Names and effect operations take type
  arguments; the old path stays for non-names.  `with [T]` and `with #[T]` are
  the same, and the argument is attached to the name, so `parse with [Int] s`
  is `(parse with [Int]) s`.
- `parse` is the first type-directed native (`Conv@parse`).  It reads Int,
  Float, Boolean, String, `()`, arrays, pairs, records and enums from text.
  The checker sees a polymorphic scheme and requires `with`; a type it cannot
  build is a static error, and a type variable is a run-time `E0020`, because
  the interpreter no longer has the type.
- The parser backtracks a `nil` in a type argument, so `with [(Int, String)]`
  parses as a pair type.  `as` is a keyword.
- A file without an export list offers what it declares and what it imported
  from another file.  The native names it imported for itself are not passed
  on: `import @native` is how a file gets `sayn` and `map` for itself, not a
  promise to pass them to an importer, which names what it wants to share.
- The checker reads a lambda argument against the arrow it is passed to, so
  `map {i = i@price}` sees the fields of the element before the array is
  known.
- `Pretty TRecordProp` prints a property as `val name : type` instead of its
  `Show` form.
- `app/modules.marr` is removed.  It was marked deprecated, and the module
  system replaces it.

Known limitations of the 0.2 line remain open in `docs/todo.md`: the soundness
of the `Cell` analysis and the completeness of `freeze`.

Tests: 483 examples, 0 failures.

## 0.2.0.0 - 2026-11-14

The 0.2 line drops the paper and the talk from the project and concentrates on
the language and its interpreter. This release collects everything that the
0.1 branch had in progress.

- The front end and the diagnostics no longer rely on partial functions:
  `Parser.tok` replaces `fromJust` with a case split whose impossible branch
  reports an internal error through Megaparsec, `ErrorContext.lineAt` uses
  `drop` instead of `!!`, and the lexer folds over literal digits instead of
  calling `read`.  `Benchmark.generateTree` walks the levels with `zip` rather
  than indexing them.
- `Suggest.distance` builds its table with `scanl`/`zip5` instead of indexing
  lists of lists.  The result is unchanged (a property test compares it with
  the previous implementation), and the cost drops from O(n²·m²) to O(n·m).

- `freezeTyp` keeps the lacks constraints it adds while freezing the body of a
  `TForall`.  Constraints on the quantified variables still move into the
  `forall`'s own maps, but constraints on variables that the `forall` does not
  bind now stay in the surrounding scope.  Previously they were dropped, so a
  frozen value could later have an open row tail instantiated with `Read`.
- Property-based tests for the unifier (`test/UnifyPropertySpec.hs`): equality
  after a successful unification, symmetry, replay, occurs checks for types and
  rows (including indirect cycles), subset semantics of `subsumesEffRow`, and
  shared effect-row tails.  For `freeze` (`test/FreezePropertySpec.hs`):
  mutation effects and `var` fields are gone, every surviving row or effect
  variable is constrained, freezing is idempotent, aliasing preserves the
  constraints, and expression freezing removes `var` bindings and rebinds.

- Aggregate types have their pending row: `[T]@R`, `(T1, T2)@R` and
  `#{...}@R`.  The syntax reuses the existing effect-row parser, so a row
  variable, a row alias and a sugared row all work; an aggregate written
  without `@R` means `@{}`, as in the paper.  `Typ` grew the row for `TArray`,
  `TPair` and `TRecord`, `Ast.TPending` and `Elaborator.elaborateType'` place
  the row, and a `TPending` in type-argument position is rejected instead of
  being silently dropped.
- T-Array, T-Pair, T-Rec and T-Prop are implemented with those rows: an
  aggregate charges a fresh row variable that is only required to bound the
  rows of its components and their mentions, and `t@l` charges the record's
  pending row plus `Read` when the field is `var`.  The row is printed only
  when it is not empty, so `[Int]` keeps reading as `[Int]`, while
  `[Int]@{Read}` survives into diagnostics and the typed IR.
- A declared `@R` is an upper bound, not an equation: T-Pair and T-Rec say
  "any such bound", so a value whose components need less than the annotation
  fits.  The new `subsumesType` (recursive, through nested aggregates and
  record fields) checks the return type of a function and the annotation of a
  `val`, `var`, `imm` and of a record field by inclusion of the aggregate's
  row; everything else is still an ordinary unification, because the paper has
  no subtyping.
- `freeze` follows `freeze(T)`: `freeze([T]@R) = [freeze(T)]@freeze_Row(R)`,
  and likewise for pairs and records, so a snapshot does not keep a mutable
  row on an aggregate it froze.
- The interpreter forces the right-hand side of a `let` before it matches a
  *destructuring* pattern, and only then: `let (a, b) = p` and `let #{...} = r`
  used to report that the value is an unevaluated expression whenever the
  right-hand side was a thunk rather than a literal pair or record.  A name
  pattern still binds the address itself, so `let` stays non-strict.
- `ExamplesSpec` gained seven more regressions for `let`: the hole above, the
  same program once the arrow names `Read`, a pair pattern whose row must not
  be empty, a `let` that reads inside its body without leaking the row, an
  `imm` snapshot of a closure that reads through a `let` alias (it keeps the
  old value while a `val` sees the new one), and the two destructuring forms
  whose right-hand side is a `val`.
- Property tests, `UnifySpec` and `FreezeSpec` generate aggregate rows and
  canonicalise them through `canonRow`; `ExamplesSpec` gained eight
  regressions for the pending rows of aggregates, from an empty row that
  rejects an element reading a `var` to a row-variable copy and the printed
  form, and `UnifySpec` nine unit tests for `subsumesType` itself (a smaller
  row fits, a larger one does not, the relaxation is recursive through a
  nested aggregate and a record field, and a record with a different field
  set or mutability is rejected).  `stack test`: 315 examples, 0 failures.
- Local `val`, `var` and `imm` bindings carry a pending row: `XVar` charges
  the effect of forcing the delayed computation, a `var` gets a fresh row
  variable that every assignment extends, and `imm` freezes its row.  A
  closure `{y}` where `val y = x` and `x` is a `var` now has row `{Read}`, so
  `funct make () : ... () -> {Read} Int = ... {y}` is accepted and the same
  closure annotated with a pure arrow is rejected.  Parameters of functions and
  lambdas carry the latent row of their arrow, and aggregates carry `@R`.
- A `let` name is an alias of the value its right-hand side computes — the
  interpreter binds the very same address — so it carries that row as its
  pending row, just as a `val` does.  Before this the hole was still open in
  one place: `funct make () : {Var} () -> {} Int = var x = 5; let y = x in {y}`
  type-checked, and forcing the returned closure read `x` while the event
  checker declared the run licensed.  The pattern type of a pair or a record
  also had the empty row hard-coded, which the unification with a reading
  right-hand side then reported as a missing `Read`; both now take a fresh row
  variable.  The row given to a destructured name is the row of the whole
  right-hand side, not of its component: that is the same over-approximation
  as T-Prop charging the record's row for any field, and it is the direction
  the paper's "upper bound of the components" allows.
- `subsumesEffRow` grows a shared open tail when only the left row has extra
  effects.  A rebinding such as `x := + x 1` requires
  `Read ∪ ρ ⊆ ρ`; the old code treated the shared tail as a unification and
  rejected every counter with `E0005`.  Equality (`unifyEffRows`) still rejects
  a shared tail with different explicit effects, because there the two rows
  must denote the same set.
- Freezing an `imm` expression no longer adds lacks constraints to row
  variables that the environment controls, namely those occurring in pending
  rows or in the types of visible bindings.  The snapshot copies their current
  values, and a later rebinding may legally extend the same row with `Read`;
  constraining it made the `quote` example fail after the pending rows of
  bindings became visible.  Rows owned by the frozen value itself (quantified
  tails and rows created inside the expression) are still constrained.
- `test/ExamplesSpec`: regressions for a closure over a local alias of a
  `var`, and for a pure arrow annotation that tries to hide that `Read`.
- `stack test`: 285 examples, 0 failures.

- A handler forces the body of its `under` block to weak head normal form
  while the handler is still installed, so the body no longer needs an
  explicit `force` for its effects to be handled.
- New builtin `whnf` with the same type as `force`: it forces one step
  (weak head normal form) instead of forcing deeply.
- `resume` is one-shot: resuming the same continuation twice is a runtime
  error instead of replaying the rest of the handled computation.  A
  continuation also dies with its handler: resuming it after the handler has
  returned is an error, and a snapshot that reaches a continuation refuses to
  freeze it.
- Two effects in one row that declare the same operation name are rejected
  with `E0018`; an operation resolved through the handler stack is an error
  when more than one effect on the stack provides its name.
- The `then` clause of a handler now contributes its latent row to the
  handler's row, and its argument and result types are unified with the body's
  type.  Previously the row was taken from `inferLambda`'s empty evaluation
  row, so a `then` that read, rebound or created state reported none of it,
  and the clause could accept or return a value whose type the handler's own
  type did not describe.
- `typeOfTypedExpr` gives an array literal the type `[T]` instead of the
  element type `T`.  A non-empty array could not be annotated with its array
  type (`funct f () : [Int] = [5]` failed with a unification error); only the
  empty array slipped through because its element type `Nothing` unifies with
  anything.
- The escaping-state analysis treats the elements of an array and the
  components of a pair as delayed computations.  The interpreter stores them
  as thunks, so `[x]` and `(x, 1)` keep a local `var x` reachable even though
  the component type is `Int`; such blocks now report `Cell` instead of
  `Var`.  The implementation has no pending-row annotation on aggregates, so
  this is the sound approximation; the change only refines `Cell` versus
  `Var`, not whether an effect is reported.
- A parenthesised type such as `(Int, Int)` parses as a pair type.  The `()`
  alternative used to consume the opening parenthesis and the parser reported
  the first token inside as unexpected instead of trying the parenthesised
  type.
- The unused `handlerCreatesCell`/`introducesLocalState` helpers were removed:
  the rows of handler clauses and of `then` already enter the handler's row.

## 0.1.0.1 - 2026-11-12

- Spans at the AST, IR and TypedIR levels (`src/Span.hs`); every node parsed
  from source carries a position, and `SpanSpec` checks that every example
  program is fully spanned.
- Diagnostics in the Rust style: `error[CODE]: message`, a `--> file:line:col`
  header, a gutter with the offending source line and carets, and `= note`
  lines for the frame stack. `ErrorContext` renders them; `docs/errors.md`
  documents the format and every code.
- Syntax errors are reported by the same renderer: `Parser` converts
  Megaparsec bundles into `ParseErrorInfo` at the boundary, so an unexpected
  token, keyword or end of input comes out as `E0013` with a caret of the
  right width.
- `E0001` was split by kind: `E0014` duplicate definitions, `E0015` records,
  `E0016` handlers, `E0017` application and arity, `E0018` inference
  limitations. `E0001` now means an internal invariant only.
- The interpreter reports runtime errors through `ExceptT InterpError` instead
  of `error`, so a failed `read_*` or an unreachable binding is a diagnostic
  with a span rather than a crash.
- `Pretty ExprNode` covered neither arrays, records, `with`, `let` nor native
  lambdas, so a diagnostic that mentioned one of them killed the process; all
  five are rendered now.
- A new example, `app/marr/quote.marr`: `imm` freezes a unit price together
  with the code that reads it, so a quote taken before a price change keeps
  the old price while a later `val` sees the new one.
- "Did you mean?" suggestions (`Suggest`): optimal string alignment distance,
  a threshold of `max 1 (length / 3)`, and silence on a tie. They are attached
  to `E0007` for an unknown value, to `E0015` for an unknown record field, and
  to an unknown type or row alias in the elaborator. `SuggestSpec` covers both
  the hits and the cases where nothing must be suggested.
- Top-level declarations carry a span (`Ast.TopLevelStat`,
  `Types.TopLevelStat`), so `E0014` for a function or an effect defined twice
  points at the second declaration instead of printing without a location.
- A suggestion is carried as a message frame on the error stack. The renderer
  prints it after the trace, uncapped and never merged with a neighbouring
  frame, and the location of a diagnostic comes from the innermost frame that
  actually has one.

## 0.1.0.0 - 2026-11-11

- A single interpreter (`IntInterpreter`); `Interpreter` is a compatibility
  re-export. The heap, the table of copies and the table of code are
  `IntMap`s, and a snapshot is 1.5–3.9 times faster than with `Map`s.
- Freezing of types and effect rows (`freezeTyp`, `freezeRowMutIn`) with
  row-lacks constraints for open rows; generalisation and instantiation carry
  the constraints.
- The executable runs the example programs of the paper and checks their
  output; the same checks are part of `stack test`.
- The unused `--always-strict` and `--forbid-memo` options were removed:
  memoisation of pure closures is always on and there is no strict mode.
- Debug tracing removed from the parser and the type checker.
