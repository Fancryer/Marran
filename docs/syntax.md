# Mårran syntax reference

Status: frozen at `0.2.3.2`.  Only the internal AST, semantics, errors and
warnings may change before `0.3.0`; the surface below does not.

This document describes the surface syntax that the reference implementation
accepts.  It is about spelling and shape, not about typing, effects, runtime
behaviour or diagnostics.  Section 8 records the behaviours that the freeze
accepts explicitly rather than leaving them to accident.

EBNF notation: `[x]` is optional, `{x}` is zero or more repetitions, `x | y` is
a choice, and quoted text is a literal token.

## 1. Lexical structure

### 1.1 Comments and whitespace

```ebnf
line-comment  ::= '//|' { any character except newline }
block-comment ::= '/|' { any character } '|\'
```

Comments are whitespace and may appear between any two tokens.  A plain `//`
is not a comment.  Newlines are whitespace; semicolons, not line breaks,
separate statements.

### 1.2 Names

A name begins with a letter, a digit, `_`, or one of the operator characters

```
+ / % | & ^ ~ < = > . * ! ? -
```

If it begins with a letter, digit or `_`, it may contain those characters and
operator characters.  If it begins with an operator character, it consists of
operator characters only.  A lone `|` is the pipe token, not a name.

```marr
x
snake_case
M::name
+
<=
|>
```

Backticks have two jobs:

```ebnf
type-variable  ::= '`' name
infix-name     ::= '`' name '`'
```

A type variable spells a type, effect or row variable depending on its
position.  An infix name is an operator written infix:

```marr
a `plus` b
```

A reference may be qualified with one module part:

```ebnf
qualified-name ::= name [ '::' name ]
```

Only references are qualified.  A declaration, parameter, field and type
variable are plain names; `M::x` is for a use of an imported name, not for a
declaration.

### 1.3 Keywords

The following words are reserved and cannot be used as names:

```
as        effect    else      end       enum
false     forall    funct     handle    if
imm       import    in        let       match
module    pattern   resume    row       then
to        true      type      under     unwinds
val       var       with
demands   ensures
```

The Unicode spellings are aliases:

```
⊥  = false
⊤  = true
∀  = forall
∈  = in
```

### 1.4 Reserved tokens

These tokens are reserved by the freeze.  Some already have a grammar
production; the rest have none yet.

| Token | Status |
|---|---|
| `|->` | pattern split, starts a prefix |
| `<-|` | pattern split, ends a suffix |
| `<-` | reserved; no production yet |
| `${` | reserved; no production yet |
| `pattern` | reserved keyword; no production yet |
| `demands` | reserved keyword; no production yet |
| `ensures` | reserved keyword; no production yet |
| `unwinds` | reserved keyword; no production yet |

`${` is one token.  A program that means `$` followed by a lambda literal must
write a space: `$ { ... }`.

### 1.5 Literals

```ebnf
integer   ::= decimal | hexadecimal
decimal   ::= digit { digit | '_' }
hexadecimal ::= '0' ('x' | 'X') hex-digit { hex-digit | '_' }

float     ::= decimal '.' decimal [ exponent ]
            | decimal exponent
            | '0' ('x' | 'X') hex-float 'p' [ sign ] decimal
exponent  ::= ('e' | 'E') [ sign ] decimal

string    ::= "'" { string-char } "'"
string-char ::= '\n' | '\t' | '\r' | '\\' | "\'"
              | any character except "'"
```

Integers and floats are unsigned.  `-` is an ordinary operator name, not part
of a literal.  A decimal exponent needs no decimal point: `1e3`, `1.0e3` and
`1E-3` are floats.

Strings use single quotes.  The escapes are `\n`, `\t`, `\r`, `\\` and `\'`.
A backslash before any other character stays two characters.

Booleans are `true` and `false`, with `⊤` and `⊥` as aliases.  The empty tuple
`()` is the unit value and the unit type.

### 1.6 Punctuation and operators

```
( ) [ ] { } #{ #[ # ${ @
: :: := = -> <- |-> <-| => ==> ...
, ; _
$ . + - * / % | & ^ ~ < > = ! ?
```

Many of these are also name characters; the token table decides which spelling
wins.  In particular, `==` and `===` are names, `==>` is the `forall` arrow,
and `|->`/`<-|` are single tokens.

## 2. Modules

### 2.1 Header

```ebnf
chunk ::= 'module' name [ export-list ] { import } { declaration }
```

Every file starts with a header.  `module Main` marks a program; `module Name`
marks a module.  The header has no `end`.

### 2.2 Export list

```ebnf
export-list ::= '[' export { export } ']'
export      ::= [ kind ] name [ 'as' name ]
kind        ::= 'funct' | 'type' | 'effect' | 'row' | 'enum'
```

The list is whitespace-separated, not comma-separated.  A missing kind means
the name in whichever namespace it has.  `enum` and `type` name the same
type-level namespace.  At least one export is required if the brackets are
present.

```marr
module Collections [funct map funct filter type List]
```

### 2.3 Imports

```ebnf
import        ::= 'import' [ '@native' ] [ import-unit ]
import-unit   ::= string '[' { import-unit } ']'
                | name [ '#' export | '[' { export } ']' ]
```

The import list is a header list: imports come after the module header and
before the first declaration.  The forms are:

```marr
import Base
import Base#map
import Base [map filter as keep]
import 'lib/' [Base Util]
import @native
import @native Numbers
```

`@native` is the marker for the native scope, not a keyword.  `@native` alone
imports the whole native scope.

## 3. Declarations

Declarations are top-level only.  There are five forms.

### 3.1 Type alias

```ebnf
type-def ::= 'type' name [ type-params ] '=' type
```

```marr
type PairOf[T] = (T, T)
```

### 3.2 Enumeration

```ebnf
enum-def  ::= 'enum' name [ type-params ] enum-case { enum-case }
enum-case ::= '|' name { '(' qualifier name [ ':' ] type ')' }
qualifier ::= 'val' | 'var' | 'imm'
```

At least one case is required.  Every field is parenthesised, has a qualifier
and a type.  The `:` before the type is optional.  There is no `end`.

```marr
enum Maybe[T]
  | None
  | Some (val x : T)
```

### 3.3 Effect

```ebnf
effect-def ::= 'effect' name [ type-params ]
                 { effect-op [ ';' ] }
               'end'
effect-op  ::= name ':' op-type
op-type    ::= pair-type '->' [ effect-row ] type
```

An effect ends with `end`; the operations are separated by `;`, and a trailing
`;` is allowed.  An effect with no operations is syntactically accepted.

```marr
effect Math
  add : Int -> Int -> Int;
  sub : Int -> Int -> Int
end
```

### 3.4 Row alias

```ebnf
row-def ::= 'row' name [ type-params ] '=' effect-row
```

```marr
row Console = {Output; Input}
```

### 3.5 Function

```ebnf
funct-def ::= 'funct' name [ type-params ] [ effect-params ]
              funct-arg { funct-arg }
              ':' [ effect-row ] type '=' block
funct-arg ::= '(' ')'
            | '(' name [ ':' ] type ')'
```

Every argument is one parenthesised group; `()` is the unit argument.  There
are no commas between arguments.  The `:` before an argument's type is
optional, so `(x Int)` and `(x : Int)` are the same.

The return part is the one place where a row and a type can start with the
same spelling.  The implementation resolves it as follows:

```marr
funct f () : Int = ...          // type only
funct f () : {Output} Int = ... // braced row and type
funct f () : Console Int = ...  // row alias and type
funct f () : `R Int = ...       // row variable and type
```

A bare name followed by a type is a row alias; a bare name followed by `=` is
the result type.  The empty row can also be left out.  There is no `end`.

## 4. Types and effects

### 4.1 Type grammar

```ebnf
type       ::= pair-type [ '->' [ effect-row ] type ]
pair-type  ::= type-atom [ ',' pair-type ]
type-atom  ::= type-atom-base [ '@' effect-row ]
type-atom-base ::= qualified-name [ type-apps ]
                 | '()'
                 | '[' type ']'
                 | '(' type ')'
                 | type-variable
                 | record-type
                 | forall-type
type-apps  ::= '#[' [ type-arg { ';' type-arg } [ ';' ] ] ']'
```

The arrow is right-associative.  A comma builds a pair type, and a pair type
must be parenthesised when it appears as an expression annotation.  A type
application uses `#[...]`; a bare `Name[...]` is an error that says the `#` is
missing.  An array is `[T]` with nothing in front of it.

`@` after a type atom attaches a pending effect row:

```marr
[Int]@`R
```

### 4.2 Type parameters and effect parameters

```ebnf
type-params   ::= '[' name { name } ']'
effect-params ::= '{' [ name { name } ] [ '|' name { name } ] '}'
```

Names are separated by whitespace, not commas.  In effect parameters the
names before `|` are effect variables; the names after `|` are row variables.

```marr
funct map[T]{E | R} ...
```

### 4.3 Effect rows

```ebnf
effect-row ::= type-variable
             | qualified-name [ type-apps ]
             | '{' [ row-entry { ';' row-entry } [ ';' ] [ '|' type-variable ] ] '}'
row-entry  ::= effect-constructor
             | '...' effect-row
effect-constructor ::= type-variable | qualified-name [ type-apps ]
```

A row is a variable, a row alias, or a braced list.  A braced list may end with
`| `R` to name its tail.  `...` spreads another row into the list.

```marr
{Output; Input | `R}
{...Console}
```

Effect application uses `#[...]` in types:

```marr
Loop#[Int]
```

### 4.4 `forall`

```ebnf
forall-type ::= ('forall' | '∀') (type-params [ effect-params ]
                                | effect-params)
                '==>' type
```

At least one of the type or effect parameter groups is required.

```marr
forall [T] ==> T -> T
forall [T]{E | R} ==> T -> {E | R} T
```

### 4.5 Type arguments

```ebnf
type-arg ::= type-arg-atom [ ',' type-arg ]
           | type-arg-atom '->' type-arg
type-arg-atom ::= qualified-name [ type-apps ]
                | '()'
                | '(' type-arg ')'
                | '[' type-arg ']'
                | type-variable
                | record-type-arg
```

Type arguments inside `#[...]` are separated by semicolons.  A comma inside one
argument builds a pair; an arrow builds a function type.

```marr
Map#[Int; String]
Map#[(Int, String)]
```

A `forall` is not currently accepted in a type-argument atom.

### 4.6 Record types

```ebnf
record-type ::= '#{' record-field { ';' record-field } [ ';' ] '}'
record-field ::= qualifier name [ ':' ] type
```

A record type needs at least one field.  A semicolon is required between
fields; a trailing semicolon is optional.  The colon before the type is
optional, as it is in the other binding forms.

```marr
#{val x : Int; var y : String}
```

## 5. Expressions

### 5.1 Precedence

From loosest to tightest:

| Level | Form |
|---|---|
| annotation | `e : T` |
| `resume` | `resume e` |
| `$` | `f $ e` (right-associative) |
| backtick infix | `a `op` b` (left-associative) |
| `with` | `e with [T] {E}` |
| application | `f x y` (left-associative) |
| access | `e@field` |
| prefix forms | `if`, `let`, `under`, `match`, literals, parentheses, names |

`$` is the low-precedence application operator.  Its right operand takes an
annotation first:

```marr
sayn $ [] : [Int]     // sayn ([] : [Int])
```

### 5.2 Application and `with`

```ebnf
expr        ::= annot-expr
annot-expr  ::= resume-expr [ ':' annot-type ]
resume-expr ::= 'resume' resume-expr | dollar-expr
dollar-expr ::= backtick-expr [ '$' annot-expr ]
backtick-expr ::= with-expr { infix-name with-expr }
with-expr   ::= apply-expr { with-args }
apply-expr  ::= access-expr { access-expr }
access-expr ::= prefix-expr { '@' name } { with-args }
with-args   ::= 'with' ( '[' type-arg { ';' type-arg } ']' [ effect-apps ]
                       | effect-apps )
effect-apps ::= '{' [ eff-arg { ';' eff-arg } ] [ '|' effect-row { effect-row } ] '}'
eff-arg     ::= effect-constructor | '...' effect-row
```

A function is applied by juxtaposition: `f x y` is `(f x) y`.  `with` supplies
type arguments and effect arguments:

```marr
parse with [Int] s
loop with [Int] {Loop} 5
```

`with` spells its type arguments as a plain `[...]`.  An ordinary application
uses `#[...]`.

### 5.3 `if`, `let`, `match`, `under`

```ebnf
if-expr    ::= 'if' expr 'then' expr 'else' expr
let-expr   ::= 'let' let-pattern '=' expr 'in' expr
match-expr ::= 'match' block 'to' match-clause { match-clause }
under-expr ::= 'under' effect-constructor 'to' block 'handle'
               ( handler-clause { handler-clause } [ '|' 'then' name '=>' block ]
               | '|' 'then' name '=>' block )
```

`if` always has `else`.  `let` binds a pattern.  `match` takes a block as its
subject and one or more clauses.

`under` handles one concrete effect.  A handler clause is

```ebnf
handler-clause ::= '|' qualified-name { name } '=>' block
```

and its final clause may be `| then name => block`.  If a handler has operation
clauses but no `then`, the identity continuation is supplied.  `resume` is only
meaningful inside a handler clause.

```marr
under Math to add 5 3
handle
| add a b => resume + a b
| then x => x
```

### 5.4 Match clauses

```ebnf
match-clause ::= '|' pattern-no-as { pattern-no-as } [ 'as' name ] [ 'if' expr ] '=>' block
```

The patterns before `as` are alternatives of one clause: `| 1 2 3 as n => ...`
matches any of the three values and binds the matched value to `n`.  A guard
follows the alias.  There is no `else`; an unguarded wildcard clause is the
explicit catch-all.

### 5.5 Array, record and lambda literals

```ebnf
array  ::= '[' [ expr { ',' expr } [ ',' ] ] ']'
record ::= '#{' [ expr '|' ] bind-def { ';' bind-def } [ ';' ] '}'
lambda ::= '{' [ type-params ] [ effect-params ] [ lambda-head ] block '}'
lambda-head ::= lambda-params [ ':' type ] '='
lambda-params ::= { lambda-param }+
                | '(' typed-param { ';' typed-param } ')'
lambda-param ::= name | '()' | '(' typed-param ')'
typed-param ::= name [ [ ':' ] type ]
```

An array is comma-separated and may be empty.  An entry is an expression; a
block entry is written in parentheses:

```marr
[(val x = 1; x + 1), 2]
```

A record literal starts with `#{`.  The optional part before `|` is the base
record; every field is a `val`, `var` or `imm` binding:

```marr
#{base | val a = 1; var b : Int = 2}
```

A lambda starts with `{`.  A head may be absent, in which case the braces hold
a block and the lambda takes no arguments.  A head is parameters, an optional
result type, and `=`:

```marr
{ x = x + 1 }
{ (x Int) : Int = x + 1 }
{ () = 42 }
```

### 5.6 Parentheses

```ebnf
parenthesised ::= '(' exp ')'
                | '(' exp ',' exp { ',' exp } [ ',' ] ')'
                | '(' block ')'
```

Parentheses group an expression, build a tuple, or hold a block.  The tuple
form is recognised when a comma follows the first expression.  A block inside
parentheses is the same node as a `block` elsewhere.

## 6. Patterns

### 6.1 Pattern grammar

```ebnf
pattern       ::= pattern-no-as [ 'as' name ]
pattern-no-as ::= pattern-tuple
pattern-tuple ::= pattern-starts [ ',' pattern-no-as ]
pattern-starts ::= pattern-suffix
                    [ '|->' pattern-starts
                    | { '<-|' pattern-suffix } ]
pattern-suffix ::= pattern-atom [ ':' annot-type ]
pattern-atom  ::= integer | float | string | '()' | boolean
                | 'val' path
                | array-pattern
                | '#' qualified-name { pattern-no-as }
                | '_'
                | '(' pattern ')'
                | name
path          ::= qualified-name { '@' name }
array-pattern ::= '[' { pattern } [ ';' pattern ] ']'
```

`|->` is right-associative and `<-|` is left-associative.  A comma is looser
than either arrow, so `a, b <-| c` is a pair whose second component ends with
`c`.  A `<-|` chain cannot be followed by `|->` at the same level, while the
right operand of `|->` may itself be a `<-|` chain.

A tuple pattern is written `a, b` or `(a, b)` and matches a pair.  A single
tuple pattern is irrefutable when both components are, so it can be the whole
clause for a pair subject.

`#` introduces a constructor pattern.  Its arguments are patterns, but the
argument list stops before `as`, because `as` belongs to the clause or to the
whole pattern.

`val` compares against a value that already exists:

```marr
match (x) to
  | val expected => ...
```

`_` matches anything and binds nothing.

### 6.2 Array patterns

```marr
[]
[a b]       // exactly two elements
[a; rest]   // head and tail
[a b; rest] // at least two elements, then the tail
```

The semicolon separates the fixed head from the tail pattern.

### 6.3 Pattern aliases

An alias binds the whole matched value:

```marr
| #Some x as whole => whole
```

In a match clause the alias after all alternatives belongs to the clause:

```marr
| 1 2 3 as n => n
```

`as` is also used to rename exports and imports.  The keyword is shared; the
position decides which meaning applies.

## 7. Blocks and bindings

### 7.1 Block

```ebnf
block      ::= { block-stat ';' } expr
block-stat ::= bind-def | assignment | expr
```

A block is zero or more statements, each followed by `;`, then one final
expression without a trailing `;`.  The final expression is the value of the
block.

```marr
val x = 1;
var y : Int = 2;
x + y
```

### 7.2 Bindings

```ebnf
bind-def ::= qualifier lambda-param '=' expr
qualifier ::= 'val' | 'var' | 'imm'
lambda-param ::= name [ [ ':' ] type ]
```

`val` is an immutable binding, `var` is mutable, and `imm` takes a snapshot.
The qualifier is required in a block.  The type annotation is optional, and
the colon before it is optional.

### 7.3 Assignment

```ebnf
assignment ::= name { '@' name } ':=' expr
```

Assignment targets a name and an optional field path.  The left side is not an
arbitrary expression, and it is not qualified; `x@field := value` is the form.

### 7.4 `let` patterns

```ebnf
let-pattern ::= let-atom { ',' let-atom }
let-atom    ::= let-atom-base | lambda-param
let-atom-base ::= '()'
                | '_'
                | '(' let-pattern ')'
                | record-let-pattern
record-let-pattern ::= '#{' let-record-field { ';' let-record-field } [ ';' ] '}'
let-record-field ::= qualifier lambda-param [ '=' let-atom ]
```

A `let` pattern is a subset of a match pattern: names, `_`, `()`, parentheses,
comma pairs and record patterns.  It does not accept literals, constructor
patterns or `val` patterns.  The freeze documents the asymmetry; unifying the
two grammars is deferred.

## 8. Current quirks accepted by the freeze

These are behaviours that the reference implementation has today.  The freeze
accepts them explicitly rather than leaving them to accident.

1. A `let` pattern is a strict subset of a match pattern.  It accepts names,
   `_`, `()`, parentheses, comma pairs and record patterns, but not literals,
   constructor patterns or `val` patterns.
2. The colon before a parameter or field type is optional in several
   productions, but not everywhere; it is optional in function arguments,
   enum fields, bindings and record fields.
3. `as` serves export/import renaming and pattern aliasing; the future
   contract doc string will add a third use.
4. `@` serves property access, assignment paths, pending rows, and the
   `@native` import marker.
5. `under` with operation clauses but no `then` inserts the identity handler.
6. `effect` allows zero operations syntactically, but handling such an effect
   is rejected later.
7. `pattern`, `demands`, `ensures`, `unwinds`, `${` and `<-` are hard reserved
   tokens, not warnings.  Existing programs that use them as names do not
   parse.
8. `//` is not a comment; only `//|` is.
9. Type parameters are whitespace-separated; type arguments are
   semicolon-separated.
10. A `forall` type is not accepted inside a type-argument atom.

The record-field separator, the exponent-only float, the string escapes, the
single `with` spelling, tuple patterns and the split-arrow chains are fixed by
the grammar above; they are not open quirks.
