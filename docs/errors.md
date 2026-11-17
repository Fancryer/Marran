# Diagnostics

Every error the front end reports is rendered in the style of Rust's
diagnostics: a header line with a stable code, the location, the offending
line with a caret run under the region the error is about, and the chain of
expressions the checker passed through as notes.

```
error[E0003]: cannot unify the type `Boolean` with the type `Int`
 --> app/marr/x.marr:2:9
  |
2 |   sayn (+ true 1)
  |         ^^^^^^^
  |
  = + true
  = + true 1
  = (+ true 1) at app/marr/x.marr:2:8
  = sayn (+ true 1) at app/marr/x.marr:2:3
```

Notes are the innermost frames first, adjacent duplicates are collapsed, and
a stack longer than six frames ends with `... N more`. The location of the
frame that is already shown as the primary label is omitted from its note.
A note that is a message rather than a frame (a `did you mean` hint, see below)
is never capped, never merged with its neighbours, and comes after the trace.

Positions are attached by the parser and carried through every stage: the
declarations (`Ast.TopLevelStat`, `Types.TopLevelStat`), the AST
(`Ast.Exp`, `Ast.BlockStat`), the IR (`Types.Expr`, `Types.Stat`) and the
typed IR (`TypedIR.TypedExpr`, `TypedIR.Stat`) all record the region of source
they came from. `test/SpanSpec.hs` walks every example program and fails if any
declaration, node or statement lost its span, so a forgotten position in the
parser is a test failure rather than a diagnostic without a location.

## Syntax errors

The lexer and the grammar report failures through Megaparsec. `Parser.hs`
converts the first error of a bundle into the same `Diagnostic` value the
checker uses: `reachOffset` turns the reported offset into a line and column,
and the rendering of the offending token gives the caret run its width, so a
three-letter token gets three carets rather than one.

```
error[E0013]: unexpected `sayn`
 --> app/marr/bad.marr:2:3
  |
2 |   sayn 1
  |   ^^^^
  |
```

At the end of a line the message names what the grammar would have accepted
there, capped at four alternatives so that a parser with many branches does
not produce a wall of text. End of input is reported as such instead of as an
empty token. `test/ParserSpec.hs` pins the header, the position and the
carets.

A file has to open with its `module` header, so a file that was written before
the header became mandatory fails on its first token. The message names the
fix rather than the token it tripped over:

```
error[E0013]: a file must start with a module header: `module Main` for a program, `module Name` for a module
 --> scratch/program.marr:1:1
  |
1 | funct main () : {Output} () =
  | ^
  |
```

## Modules and imports

Imports are resolved before the type checker runs, so a mistake about a file is
reported by the loader: there is no code, and the position is the `import` line
(or the export name) that is wrong. The renderer quotes the file the import is
in, and the notes say what to do next.

```
error: cannot find the module `numbers`
 --> scratch/main.marr:3:1
  |
3 | import numbers
  | ^^^^^^^^^^^^^^
  |
  = looked for: scratch/numbers.marr, ./numbers.marr, app/marr/numbers.marr, app/numbers.marr
```

The cases the loader reports:

| Situation | Message |
|-----------|---------|
| a module is not on disk | ``cannot find the module `a` ``, with the list of paths tried |
| a name the export list names is unknown | ``` `f` is not declared or imported here, so it cannot be exported ```, with the names the module does have |
| a name the import list names is unknown | `` `f` is not offered by the module `a.marr` ``, with the names the source does offer |
| an import or export list names the wrong kind | ``` `f` is a function in a.marr, not a type ```, with the advice to write the kind it is |
| an import names a native module that is not there | ``there is no native module `Nosuch` ``, with the list of native modules |
| two imports bring one name | ``two imports bring `f`: a.marr (a function) and b.marr (a function)``, with the advice to rename one |
| the entry file is not `module Main` | ``` `Lib` is a library, not a program: a file that is run must say `module Main` ``` |

A name an import list writes is a claim about another file, so the loader checks
it at the line that makes it. Waiting for the checker to say the name is not in
scope would report the symptom three functions later; the loader knows which
file the list is about, and it reports the mistake where a reader can fix it:

```
error: `nosuch` is not offered by the module `numbers.marr`
 --> main.marr:3:13
  |
3 | import numbers [funct nosuch]
  |             ^^^^^^^^^^^^
  |
  = it offers: one
```

Two imports of *different* namespaces do not clash: a function and a type may
share a name, exactly as two declarations of one file may. Only two values, or
two types, of one name are an error, and `as` is the way out. A table entry is
therefore a list: one spelling, one declaration per namespace.

The kind a list writes chooses the namespace. A bare name brings every
declaration of that spelling, and `[type f]` or `[funct f]` asks for one of
them. A kind that the source does not have there is a mistake about the kind,
not about the spelling, and the note says which one the source has:

```
error: `cell` is not offered by the module `func.marr`
 --> main.marr:3:11
  |
3 | import func [type cell]
  |           ^^^^^^^^^
  |
  = `cell` is a function in func.marr, not a type
```

Shadowing follows the same rule: a file's own `funct f` wins over an imported
`funct f`, but an imported `type f` still arrives, because a use tells the two
apart by position.

An enumeration carries its constructors. Naming `enum Colour` in an export or
import list names `Red` and `Green` too, because a type whose values cannot be
written is not much of an export; repeating a constructor in the list is the
same declaration twice, not a clash. `as` renames the type only — `enum Colour
as Shade` makes `Shade` the spelling in signatures while `Red` keeps its declared
name — and two enums that both have a `Red` clash unless one of them spells the
constructor out and renames it: `[enum Shade funct Red as Crimson]`.

A rename reaches the body of the declaration, not only its table entry: the
types a declaration mentions are written in the vocabulary of the module that
declares it, so an importer that writes `Shade` must not receive a constructor
or an operation that still says `Colour`. Function and constructor schemes,
enum fields, the signatures and rows of an effect's operations, and a type or
row alias' body all take the local spelling.

A private name is not a special case: a module's table holds only what it
exports, so an unexported name is not "hidden" from the importer, it was never
imported. An import that names it is told so at the import line — `` `f` is not
offered by the module `a.marr` ``, with the note that `f` is declared there but
not exported — because the export list is what has to change. A use of a name
that never came through any import is the ordinary ``E0007`` about a name in
scope, and no note suggests the private spelling.

The entry point is the only `main` that runs. A library may declare one; the
interpreter calls the `main` of the module named on the command line.

## Suggestions

An unknown name is often a typo, so the checker looks for a name that is close
to the one it could not resolve and appends a note when it finds one:

```
error[E0007]: `coutner` is not in scope
 --> app/marr/x.marr:3:8
  |
3 |   sayn coutner
  |        ^^^^^^^
  |
  = coutner
  = sayn coutner at app/marr/x.marr:3:3
  = did you mean `counter`?
```

The distance is the optimal string alignment distance: insertions, deletions,
substitutions and transpositions of adjacent characters, where a transposition
counts as one edit (`lenght` → `length` is one, not two). A candidate is
offered when its distance is at most `max 1 (length / 3)`, so a typo in a long
identifier may be further away than one in a short one.

The note is deliberately quiet:

- nothing is suggested when the nearest candidate is beyond the threshold;
- nothing is suggested when two candidates are equally close, because picking
  one of them by the order of a `Map` would teach the wrong name;
- the name itself is never suggested.

Suggestions are produced for four kinds of mistake:

| Where | Candidates |
|-------|-----------|
| a value (`E0007`) | every binding visible from the current scope, walking `parent` |
| a record field (`E0015`) | the fields of the record being projected |
| a type alias name | the declared aliases plus the built-in type names |
| a row alias name | the declared rows |

The first two keep the name and add a note. The last two cannot: an unknown
type or row name has no sensible meaning, so it is rejected at elaboration,
with the hint in the message itself:

```
error: unknown type 'Prise'; did you mean `Price`?
error: Unknown row alias: Mutatoin; did you mean `Mutation`?
```

The threshold there is stricter, because a program may legitimately name a type
that it does not declare (an opaque `TFlat`). A name is reported only when it is
at least four characters long, exactly one edit from a known name, and that name
is the unique candidate at that distance; `Prise` next to `Price` is a typo,
while `Foo` next to `Food` is left alone and stays opaque. A name that is not
close to anything also stays opaque and fails later at unification.

## Runtime errors

A program that type-checks can still fail while it runs, and those failures go
through the same renderer: a code, a position and a caret run. The interpreter
does not raise an exception that unwinds through the user's screen, because a
message without a position is not something a reader can act on.

Two kinds are expected of a well-typed program:

- `E0020` — the program itself failed. A division by zero in `%`, an uncaught
  `error` or a failed `assert` of the effect `Error`, or a value that needs
  itself: `val y = + x 1; x := + y 1` makes the two cells wait for each other,
  because a delayed computation reads a mutable binding as it is when it is
  forced. The model has no rule for such a term — it diverges — so the
  interpreter reports the cycle at the delayed expression instead of spinning
  forever. `%` and `head`/`tail` of an empty array are reported this way
  rather than through `Error`, because they are declared pure.
- `E0019` — the program exhausted memory: the Haskell heap or the stack. The
  position is the body of `main`, since the exhaustion is not tied to a node.

Anything else the interpreter reports carries no code and is a gap in the
interpreter: a value of the wrong shape reached a primitive, a handler went
missing, a native signature arrived as a value.

## Codes

| Code  | Meaning |
|-------|---------|
| E0001 | an internal type error; reaching the user means a gap in the checker |
| E0002 | a type-argument error |
| E0003 | two types cannot be unified |
| E0004 | two type arguments cannot be unified |
| E0005 | two effect rows cannot be unified, or the body performs effects the signature does not declare |
| E0006 | two effects cannot be unified |
| E0007 | a name is not in scope |
| E0008 | assignment to a `val` or `imm` binding |
| E0009 | a binding shadows another binding in the same scope |
| E0010 | a handler-related effect error, such as `resume` outside a handler clause |
| E0011 | a handler clause resumes more than once |
| E0012 | an unimplemented construct reached the checker |
| E0013 | a syntax error reported by the lexer or the grammar |
| E0014 | a duplicate definition (a function, an effect, or a handler clause) |
| E0015 | a record error (an unknown field, a non-record base, a field whose mutability changes) |
| E0016 | a handler error (an operation the effect does not declare, a missing or repeated clause, a marker effect such as `Var` that has no operations, or an effect declared with no operations) |
| E0017 | an application or arity error (`with` arguments, an effect parameter list, a non-function head) |
| E0018 | an inference limitation (an occurs check, an escaping rigid variable, a failed instantiation, a forbidden effect in a constrained row, or an operation name provided by two effects in the same row) |
| E0019 | the program exhausted memory (the heap or the stack), reported at the body of `main` |
| E0020 | the program itself failed: an uncaught `error`/failed `assert` of the effect `Error`, a zero divisor in `%`, or a value that needs itself |
| E0021 | a `match` does not cover every value of its subject's type |

Errors raised by the elaborator (the phase between the parser and the type
checker) carry a message but no code: they are about the shape of the program
rather than about types. They still go through the same renderer, and their
`Show` instance prints the user-facing message instead of a constructor.
