# Diff Details

Date : 2026-06-14 23:52:45

Directory /mnt/c/Users/Alice Liddell/Documents/projects/haskellets/marran/src

Total : 43 files,  1517 codes, -371 comments, 146 blanks, all 1292 lines

[Summary](results.md) / [Details](details.md) / [Diff Summary](diff.md) / Diff Details

## Files
| filename | language | code | comment | blank | total |
| :--- | :--- | ---: | ---: | ---: | ---: |
| [/home/alice/haskellets/numl/CHANGELOG.md](//home/alice/haskellets/numl/CHANGELOG.md) | Markdown | -7 | 0 | -5 | -12 |
| [/home/alice/haskellets/numl/README.md](//home/alice/haskellets/numl/README.md) | Markdown | -1 | 0 | -1 | -2 |
| [/home/alice/haskellets/numl/Setup.hs](//home/alice/haskellets/numl/Setup.hs) | Haskell | -2 | 0 | -1 | -3 |
| [/home/alice/haskellets/numl/app/Main.hs](//home/alice/haskellets/numl/app/Main.hs) | Haskell | -4 | 0 | -3 | -7 |
| [/home/alice/haskellets/numl/dist-newstyle/cache/plan.json](//home/alice/haskellets/numl/dist-newstyle/cache/plan.json) | JSON | -1 | 0 | 0 | -1 |
| [/home/alice/haskellets/numl/hie.yaml](//home/alice/haskellets/numl/hie.yaml) | YAML | -2 | 0 | 0 | -2 |
| [/home/alice/haskellets/numl/numl.cabal](//home/alice/haskellets/numl/numl.cabal) | Cabal | -104 | -3 | -7 | -114 |
| [/home/alice/haskellets/numl/package.yaml](//home/alice/haskellets/numl/package.yaml) | YAML | -67 | -6 | -8 | -81 |
| [/home/alice/haskellets/numl/src/Ast.hs](//home/alice/haskellets/numl/src/Ast.hs) | Haskell | -368 | -9 | -85 | -462 |
| [/home/alice/haskellets/numl/src/Eff.hs](//home/alice/haskellets/numl/src/Eff.hs) | Haskell | -173 | -6 | -23 | -202 |
| [/home/alice/haskellets/numl/src/Infer.hs](//home/alice/haskellets/numl/src/Infer.hs) | Haskell | -151 | -424 | -18 | -593 |
| [/home/alice/haskellets/numl/src/Lexer.hs](//home/alice/haskellets/numl/src/Lexer.hs) | Haskell | -286 | -3 | -52 | -341 |
| [/home/alice/haskellets/numl/src/Lib.hs](//home/alice/haskellets/numl/src/Lib.hs) | Haskell | -5 | 0 | -2 | -7 |
| [/home/alice/haskellets/numl/src/Occurs.hs](//home/alice/haskellets/numl/src/Occurs.hs) | Haskell | -48 | -6 | -9 | -63 |
| [/home/alice/haskellets/numl/src/Parser.hs](//home/alice/haskellets/numl/src/Parser.hs) | Haskell | -440 | -13 | -80 | -533 |
| [/home/alice/haskellets/numl/src/Record.hs](//home/alice/haskellets/numl/src/Record.hs) | Haskell | -25 | 0 | -7 | -32 |
| [/home/alice/haskellets/numl/src/Resume.hs](//home/alice/haskellets/numl/src/Resume.hs) | Haskell | -14 | -3 | -6 | -23 |
| [/home/alice/haskellets/numl/src/Scope.hs](//home/alice/haskellets/numl/src/Scope.hs) | Haskell | -106 | -78 | -20 | -204 |
| [/home/alice/haskellets/numl/src/Types.hs](//home/alice/haskellets/numl/src/Types.hs) | Haskell | -204 | -14 | -41 | -259 |
| [/home/alice/haskellets/numl/src/Unify.hs](//home/alice/haskellets/numl/src/Unify.hs) | Haskell | -265 | -15 | -28 | -308 |
| [/home/alice/haskellets/numl/src/Utils.hs](//home/alice/haskellets/numl/src/Utils.hs) | Haskell | -48 | 0 | -12 | -60 |
| [/home/alice/haskellets/numl/stack.yaml](//home/alice/haskellets/numl/stack.yaml) | YAML | -6 | -60 | -6 | -72 |
| [/home/alice/haskellets/numl/stack.yaml.lock](//home/alice/haskellets/numl/stack.yaml.lock) | YAML | -7 | -4 | -2 | -13 |
| [/home/alice/haskellets/numl/test/Main.hs](//home/alice/haskellets/numl/test/Main.hs) | Haskell | -11 | 0 | -1 | -12 |
| [/home/alice/haskellets/numl/test/Spec.hs](//home/alice/haskellets/numl/test/Spec.hs) | Haskell | -531 | -47 | -108 | -686 |
| [src/Ast.hs](/src/Ast.hs) | Haskell | 437 | 23 | 96 | 556 |
| [src/Debug.hs](/src/Debug.hs) | Haskell | 9 | 55 | 3 | 67 |
| [src/Eff.hs](/src/Eff.hs) | Haskell | 112 | 2 | 21 | 135 |
| [src/Elaborator.hs](/src/Elaborator.hs) | Haskell | 586 | 6 | 64 | 656 |
| [src/Infer.hs](/src/Infer.hs) | Haskell | 715 | 56 | 88 | 859 |
| [src/Interpreter.hs](/src/Interpreter.hs) | Haskell | 146 | 14 | 17 | 177 |
| [src/Lexer.hs](/src/Lexer.hs) | Haskell | 290 | 0 | 54 | 344 |
| [src/Lib.hs](/src/Lib.hs) | Haskell | 5 | 0 | 2 | 7 |
| [src/Occurs.hs](/src/Occurs.hs) | Haskell | 47 | 0 | 6 | 53 |
| [src/Parser.hs](/src/Parser.hs) | Haskell | 639 | 72 | 106 | 817 |
| [src/Record.hs](/src/Record.hs) | Haskell | 26 | 0 | 7 | 33 |
| [src/Resume.hs](/src/Resume.hs) | Haskell | 15 | 2 | 6 | 23 |
| [src/Scope.hs](/src/Scope.hs) | Haskell | 173 | 18 | 23 | 214 |
| [src/Sexp.hs](/src/Sexp.hs) | Haskell | 44 | 0 | 9 | 53 |
| [src/TypedIR.hs](/src/TypedIR.hs) | Haskell | 253 | 49 | 36 | 338 |
| [src/Types.hs](/src/Types.hs) | Haskell | 386 | 9 | 68 | 463 |
| [src/Unify.hs](/src/Unify.hs) | Haskell | 443 | 14 | 48 | 505 |
| [src/Utils.hs](/src/Utils.hs) | Haskell | 67 | 0 | 17 | 84 |

[Summary](results.md) / [Details](details.md) / [Diff Summary](diff.md) / Diff Details