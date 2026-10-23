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