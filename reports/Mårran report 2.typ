#import "@preview/cheq:0.3.0"

#let start = datetime(year: 2026, month: 2, day: 28)
#let period = (start, start + duration(weeks: 6, days: 3))
#let today = datetime(year: 2026, month: 2, day: 28)

= Project progress report --- Mårran
\
*Date:* #today.display()

*Reporting period:* #period.map(d => d.display()).join(" to ")

\

#set heading(numbering: "1.1.")

= Naming

The language was previously named NuML. It was renamed to Mårran to provide a more distinctive and unique identity and avoid ambiguity with existing projects.

= Overview

Mårran is an experimental statically typed programming language that explores the interaction between non-strict evaluation, mutable bindings, and algebraic effects.

The language is built around three core principles:

- Explicitly controlled laziness: expressions are evaluated only when forced
- Mutation confined to bindings: values remain immutable, while state exists in environments
- Effect-driven semantics: all observable behavior, including mutation and evaluation, is governed by effect rows

A central feature of the language is the `imm` qualifier, which introduces a mutation firewall at the level of bindings by capturing and freezing the environment at the point of definition.

Mårran aims to demonstrate that non-strict evaluation and mutation can coexist safely without ownership systems or linear types, relying instead on a small set of semantic invariants and effect tracking.

*Current focus:* parser validation, AST elaboration, and semantic refinement.

The current development phase concentrated on stabilizing the frontend pipeline and validating the core semantics of the language.

*This includes:*
- systematic identification and elimination of parser inconsistencies
- implementation of an elaboration phase from AST to a typed intermediate representation (IR)
- development of mechanisms for handling type variables (meta, bound, skolem)
- refinement of effect row semantics and their interaction with type inference

The elaboration phase plays a central role in resolving surface syntax into a semantically precise representation, preparing the program for subsequent type checking and inference.

= Core semantics

Mårran defines a non-strict evaluation model where expressions are evaluated only when explicitly forced.

== Laziness and forcing

Evaluation is demand-driven. Expressions are not reduced unless required by a forcing context.

The `force` operation explicitly triggers evaluation. This makes evaluation order observable and controllable, rather than implicit.

== Mutation model

Mutation is confined to bindings rather than values.

Values themselves are immutable. State exists in environments, and mutation affects bindings, not the underlying values.

This separation ensures that values remain stable and composable, even in the presence of stateful computations.

== Referential transparency

Despite supporting mutation, Mårran preserves referential transparency at the value level.

Expressions that do not interact with mutable bindings or effects behave as pure values and can be safely substituted.

== The `imm` construct

The `imm` qualifier enforces a mutation boundary at binding time by capturing and freezing the environment in which the binding is defined.

For an `imm` binding:
- all referenced bindings are snapshotted at the moment the binding is created
- further mutations to those bindings do not affect the value bound by the `imm` binding

This acts as a “mutation firewall”, allowing controlled interaction between mutable and immutable contexts.

== Effects and evaluation

All observable behavior, including:

- mutation
- forcing of lazy expressions
- control flow

is modeled via algebraic effects.

Effect rows explicitly track which effects a computation may perform.

This unifies:

- evaluation
- mutation
- control

under a single semantic framework.

= Frontend pipeline

The frontend of Mårran is structured as a sequence of transformations:

Source Text → Tokens → AST → Elaborated IR

Each stage progressively refines the program from a surface-level representation into a semantically precise form.

The lexer performs deterministic tokenization without context-sensitive rules.

The parser constructs an untyped abstract syntax tree (AST) that closely mirrors the surface syntax of the language. At this stage, the representation is intentionally permissive and does not enforce semantic constraints.

The elaboration phase transforms the AST into a typed intermediate representation (IR). This stage is responsible for:

- resolving type and effect variables
- expanding type and row aliases
- normalizing effect row structure
- introducing explicit representations for bindings, functions, and handlers

The resulting IR enforces key structural invariants required by the type system and is designed to be directly consumed by the type inference engine.

A key design principle is the separation between syntax and semantics:
the AST preserves the flexibility of the surface language, while the elaborated IR encodes a canonical and unambiguous representation.

The elaboration phase also establishes a disciplined handling of variable scopes by introducing distinct classes of variables (e.g. bound variables) and ensuring consistent identity across the program.

\
= Implementation status

The frontend of Mårran is structurally complete and operational.

All major stages — lexing, parsing, and elaboration — are implemented and integrated into a single evaluation pipeline.

The elaboration phase is partially complete and already performs key transformations required for semantic processing, including:

- name resolution for type and effect variables
- expansion of type and row aliases
- normalization of effect rows
- construction of a typed intermediate representation

This intermediate representation serves as the internal form used by the interpreter and the type inference engine.

Several aspects of the semantic layer are still under active development.

In particular:

- the handling of bound variables is not yet fully stabilized
- interaction between meta, bound, and skolem variables is still being refined
- certain invariants required by the type inference system are not yet fully enforced

A type inference system is implemented at a foundational level, including unification over types, type arguments, and effect rows.

However, it is not yet fully integrated into the evaluation pipeline, and its correctness depends on ongoing refinement of the semantic model.

From a validation perspective:

- the lexer is fully tested and considered stable
- the parser has been validated on representative programs
- the elaboration phase is currently validated through incremental testing and debugging

No fundamental architectural blockers have been identified. The remaining work is primarily concerned with semantic completeness and correctness rather than structural changes.

= Type system and semantic invariants

Mårran employs a statically typed system with explicit tracking of effects and a separation between value-level and effect-level reasoning.

The type system is designed not only to ensure type safety, but also to enforce a set of semantic invariants governing laziness, mutation, and effectful computation.

== Type variables and scopes

The system distinguishes between multiple classes of type variables, each serving a different role in the inference process:

- *Meta* variables represent unknown types introduced during inference
- *Skolem* variables represent rigid, non-instantiable types used to prevent unsound generalization
- *Bound* variables represent explicitly scoped type parameters introduced during elaboration

This separation allows the system to precisely control where instantiation is permitted and where types must remain fixed.

In particular, bound variables are treated as rigid identifiers tied to their scope, while meta variables are the only class of variables that may be solved during unification.

== Unification

Type inference is based on a unification engine that operates over:

- types
- type arguments
- effect rows

Unification includes an occurs check to prevent cyclic types and ensures that substitutions respect scope boundaries.

Meta variables may be instantiated with types, while skolem and bound variables cannot be solved.

Additional constraints ensure that:

- skolem variables do not escape their scope
- substitutions do not violate level restrictions
- effect rows remain structurally consistent

== Effect rows

Effects are represented using row polymorphism.

An effect row is either:

- closed (a fixed set of effects), or
- open (a set of effects with a tail variable)

Unification of effect rows involves:

- matching common effects
- propagating differences into row variables
- constructing unified rows that preserve all participating effects

This allows functions to remain polymorphic over effects while still tracking observable behavior.

== Interaction with laziness

The type system is designed to coexist with non-strict evaluation.

In particular, types do not encode evaluation order directly. Instead, evaluation is controlled operationally (via `force`) and semantically (via effects).

This separation allows:

- lazy evaluation to remain implicit in the core language model
- effects to capture observable consequences of evaluation

== Semantic invariants

The type system enforces several key invariants:

- *No cyclic types* (via occurs check)
- *No skolem escape* (rigid variables cannot leak into outer scopes)
- *Controlled instantiation* (only meta variables may be solved)
- *Effect consistency* (effect rows remain well-formed under unification)

These invariants collectively ensure that:

- laziness does not introduce unsoundness
- mutation remains confined to well-defined contexts
- effectful computations remain explicitly tracked

The type system is not designed as a standalone component, but as a mechanism for enforcing the semantic model of the language.

= Design insight: imm without ownership

A central design question in Mårran is how to safely combine mutation with non-strict evaluation without relying on ownership systems or linear types.

Traditional approaches enforce safety by restricting aliasing:

- linear types ensure single ownership
- uniqueness types prevent sharing of mutable data
- region systems control lifetime explicitly

Mårran takes a different approach.

Instead of restricting who can access a value, it controls when mutations can affect it.

== Snapshot semantics

The `imm` construct provides a semantic boundary by capturing the environment at the point of binding.

When a binding is declared using imm, the environment at that point is captured and associated with the binding. Subsequent mutations to those bindings do not affect the captured value.

This can be understood as a form of environment snapshotting rather than value copying.

As a result:

- mutation remains available outside the boundary
- bindings declared with `imm` behave as if they were evaluated in an immutable environment

== Interaction with laziness

Non-strict evaluation introduces a subtle challenge:
a value may reference a binding that is mutated before it is forced.

Without additional structure, this breaks referential transparency.

The `imm` construct resolves this by ensuring that:

- either the expression bound by `imm` is forced after its environment has been fixed, or
- it carries the frozen environment captured at binding time that prevents future mutations from affecting its evaluation

This allows laziness and mutation to coexist without requiring strict evaluation or ownership tracking.

== Effects as a unifying mechanism

Mårran models both mutation and evaluation as effects.

This makes it possible to:

- track when evaluation is performed
- control when mutation is observable
- reason about boundaries introduced by `imm`

In this setting, `imm` does not eliminate effects — it constrains their visibility.

== Why ownership is not required

The key observation is that unsoundness does not arise from mutation alone, but from _uncontrolled interaction between mutation and deferred evaluation._

By introducing a boundary that stabilizes the environment, Mårran avoids the need for:

- linear usage tracking
- alias control
- explicit lifetime management

Instead, safety is achieved through:

- controlled evaluation (`force`)
- explicit effect tracking
- environment freezing (`imm`)

== Consequences

This design leads to several properties:

- mutable state can be used freely without infecting the entire program
- lazy evaluation remains the default, rather than an opt-in feature
- pure and impure computations can coexist without a strict separation

The resulting model preserves much of the flexibility of dynamic environments while retaining static guarantees about behavior.

This shifts the focus from ownership of values to stability of environments.

\

= Current limitations

While the core semantic model of Mårran has been established, several aspects remain under active refinement.

The interaction between laziness, effects, and mutation is conceptually defined, but not yet fully formalized.

In particular:

- the precise operational semantics of `force` in the presence of effect handlers is not fully specified
- the boundary behavior of `imm` with respect to partially evaluated expressions requires further clarification
- the relationship between effect tracking and evaluation order is not yet formally proven

At the implementation level:

- handling of bound variables in the type system is incomplete
- interaction between meta, skolem, and bound variables is not fully stabilized
- some invariants are enforced operationally rather than guaranteed by construction

These limitations do not affect the overall architecture, but indicate that the system is still in a semantic exploration phase.

= Future work

The next stage of development focuses on turning the current semantic model into a fully coherent, formalized, and validated system.

A primary direction is the formalization of the language semantics.

This includes:

- a small-step operational semantics describing evaluation, including the interaction between laziness, force, and mutation
- a big-step semantics for reasoning about program outcomes
- a static semantics in the form of typing rules, capturing effect tracking and scope discipline

A central challenge is to formally capture the interaction between:

- deferred evaluation (laziness)
- environment-based mutation
- snapshot semantics introduced by `imm` bindings

The goal of this formalization is to establish that:

- referential transparency is preserved at the value level
- mutation does not introduce inconsistencies across evaluation boundaries
- effect tracking accurately reflects all observable behavior

Alongside formalization, the implementation will be extended to align with the semantic model:

- integration of the type inference engine into the interpreter
- completion of bound variable handling and scope discipline
- refinement of effect row unification and its interaction with evaluation

Further research directions include:

- studying the expressive power of `imm` as an alternative to ownership-based systems
- exploring extensions of the effect system (e.g. effect handlers, effect masking)

The central question is whether environment freezing (imm) can serve as a semantic alternative to ownership in a non-strict setting.

= Conclusion

Mårran explores an alternative approach to combining laziness and mutation without relying on ownership or linear type systems.

Instead of restricting aliasing, it introduces semantic boundaries that control when mutation becomes observable.

The combination of:

- explicit forcing
- effect tracking
- environment freezing via `imm`

provides a foundation where:

- lazy evaluation remains the default
- mutation is available but controlled
- referential transparency is preserved at the value level

While the system is not yet fully formalized, the current results suggest that this approach is viable and worth further investigation.

\
= Short weekly log
To be updated.

\
= Appendix A. Code examples

\
```hs
data Taste =
  Meta Text Int Int
  | Skolem Text Int Int
  | Bound Text Int
```

This representation reflects the separation between inference variables (meta), rigid variables (skolem), and explicitly scoped variables (bound), which is central to the elaboration and type inference phases.

\
```hs
(TVar x@Meta{}, t) -> do
  t' <- applyTypeSubst scope t
  if typeOccursInType x t' then
    throwError $ TypeUnificationError t1' t'
  else
    bindMetaType scope x t'
```

This fragment illustrates unification with occurs check and controlled instantiation of meta variables.


\
```hs
resolveTypTaste :: ElabEnv -> Text -> ElabM Types.Taste
resolveTypTaste env n =
  case lookupTyp env n of
    Nothing -> throwError $ UnboundVarError $ "Unbound type variable: " <> n
    Just t -> pure t
```

Type variables are resolved explicitly during elaboration. Unbound variables are treated as errors rather than implicitly introduced, enforcing scope correctness early.

\
```hs
ts' <- traverse (\nm -> (nm,) <$> freshBound nm) (coerce ts)
let env' = extendTyp ts' env
```

Bound variables are introduced during elaboration using fresh identifiers. Each type parameter is assigned a unique identity, ensuring that variables are compared by identity rather than by name. 
This avoids accidental capture and ensures correct handling of scope.

\
```hs
bindMetaType _ Skolem{} _ =
  throwError $ TypeError "Cannot solve a skolem"
```

Skolem variables are rigid and cannot be instantiated during unification.