# Mårran

Mårran is an experimental statically typed programming language exploring the interaction between non-strict evaluation, controlled mutation, and algebraic effects.

Instead of restricting aliasing through ownership or linear types, Mårran introduces environment snapshot semantics via the imm binding qualifier. Mutation affects bindings rather than values, while lazy evaluation remains explicit and effect-aware.

The language combines:

- demand-driven evaluation with explicit forcing
- environment-based mutation semantics
- row-polymorphic algebraic effects
- higher-rank polymorphism
- elaboration into a typed intermediate representation

Mårran investigates whether environment freezing can serve as a semantic alternative to ownership systems in non-strict functional languages.

Version 0.2 is the interpreter-focused line: the language, the type-and-effect
inference engine and the interpreter are developed further, while the paper and
the talk that accompanied 0.1 are no longer maintained.

## Building and testing

The project is a Stack project and needs GHC 9.12.4 (see `stack.yaml`).

```
stack build          # library and the marran-exe driver
stack test           # the Hspec suites and the example programs
```

`stack test` runs the Hspec suites for unification, generalisation, freezing,
source spans, diagnostics, syntax errors, suggestions, builtins, the benchmark
graphs, the QuickCheck properties of the unifier and of `freeze`, and every
example program under `app/marr`. The programs are elaborated, type-checked and
interpreted with the mutation event check enabled; each one is compared
against its expected output, and `app/marr/imm_needs_read.marr` must be
rejected by the type checker. A failure fails the test suite.

The executable runs the same examples by hand:

```
stack exec marran-exe                    # run the examples
stack exec marran-exe -- --run NAME      # run one program
stack exec marran-exe -- --bench --csv bench.csv
                                         # the benchmark graphs
stack exec marran-exe -- --bench-edges --csv bench_edges.csv
                                         # the wider edge sweep
```

## Layout

- `src/` — the implementation: lexer, parser, elaborator, type-and-effect
  inference (`Infer`, `Unify`, `Scope`, `Types`, `TypedIR`), the interpreter
  (`IntInterpreter`), the benchmark harness and the test driver (`Suite`).
- `app/` — the executable (`Main.hs`) and the example programs (`app/marr`).
  `app/marr/handle_while.marr` (effect handlers with an explicit polymorphic
  type argument) is a complete `while` loop: `break` returns the loop's result
  and `continue` starts the next iteration. It is covered by `stack test` with
  a fixed standard input.
- `test/` — the Hspec suites. `SpanSpec` checks that every syntax node
  carries a source position, `DiagnosticSpec` pins the shape of rendered
  diagnostics, and `SuggestSpec` pins when a "did you mean" hint is offered
  and, more importantly, when it is not.
- `docs/errors.md` — how errors are rendered and what the `E____` codes mean.
- `prover/marr/` — a Lean 4 development that checks the syntactic facts about
  `freeze` (that `freeze` yields frozen terms, is the identity on them,
  preserves bound names and does not add free variables). It corresponds to
  the design that 0.1 documented and is not developed further in 0.2.

## Acknowledgment

Work on the language and its implementation was done with the help of an AI
assistant.
