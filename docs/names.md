# Names in Mårran

Status: frozen at `0.2.3.2`.

This note is about names, not about the grammar of declarations.  `syntax.md`
is the reference for the forms that introduce and use a name.

## 1. What the parser enforces

A name begins with a letter, a digit, `_`, or an operator character

```
+ / % | & ^ ~ < = > . * ! ? -
```

A name that begins with a letter, digit or `_` may contain those characters and
operator characters.  A name that begins with an operator character contains
operator characters only.  A lone `|` is the pipe token, not a name.

The following are not names:

- keywords (`funct`, `val`, `match`, `pattern`, ...);
- reserved tokens (`<-`, `${`, `|->`, `<-|`);
- `_`, which is the wildcard;
- a backticked type variable, which is a reference to a type, effect or row
  variable in scope.

A declaration, parameter, field and type parameter are plain names.  A use may
be qualified:

```marr
M::map
```

There is exactly one `::`; `A::B::c` is not a name.  The module part is the
module's header name or the base name of its file.

## 2. Namespaces

Mårran keeps a value namespace and a type-level namespace.  A function and a
type may share a spelling; an export list disambiguates them with a kind:

```marr
module M [funct f type f]
```

`enum` and `type` name the same type-level namespace.  An effect and a row are
declarations of their own kind; they are imported and exported with `effect`
and `row`.

Enum constructors are values: `Some 5` builds a value, while `#Some x` is the
pattern that matches it.  The constructor is imported with its enumeration.

## 3. Conventions used by the standard library

These are conventions, not parser rules:

| Kind | Convention | Example |
|---|---|---|
| module | PascalCase | `Collections` |
| type | PascalCase | `Maybe`, `List` |
| effect | PascalCase | `Output`, `Error` |
| row | PascalCase | `Console` |
| enum constructor | PascalCase | `Some`, `None` |
| function | lower case, `snake_case` for phrases | `map`, `sum_nats` |
| value | lower case | `x`, `result` |
| type parameter | short, usually uppercase | `[T]`, `[a]` |
| type variable at a use | backticked, usually uppercase | `` `T `` |
| operator | symbolic | `+`, `<=`, `|>` |

A type parameter is written plain in its declaration and backticked at a use:

```marr
funct id[T] (x `T) : `T = x
```

## 4. Qualification and imports

A use is qualified with the module it came from:

```marr
Base::map
```

The module part is resolved against the header name of the imported file or
the base name of its file.  `Lib` and `lib` both name `lib.marr` when that is
the file's base name.  Qualification is disambiguation, not a way around the
module system: the name must be exported and brought in by the import list.

An import may rename a name:

```marr
import Base [map as transform]
import Base#map as transform
```

The renamed name is the one the importing module uses.  The original spelling
is not available unless the import list also brings it.

## 5. Native names

The native scope is imported with `@native`:

```marr
import @native
import @native Numbers
```

A native name keeps the module that declares it.  `Output::sayn` resolves to
the `sayn` of the native `Output` module, and `Numbers::sayn` is refused
because `Numbers` does not declare it.  A plain `sayn` is available only when
the native module that declares it is imported.

## 6. Reserved spellings

The freeze reserves these hard:

```
pattern  demands  ensures  unwinds  <-  ${
```

They cannot be identifiers.  The first four are keywords; `<-` and `${` are
tokens with no production yet.  `|->` and `<-|` are tokens with pattern
productions.

`old`, `decreases`, `invariant`, `variant` and `modifies` are deliberately not
reserved.  If they are added later, they should be contextual or annotation
forms, so that they remain usable as ordinary names outside their positions.
