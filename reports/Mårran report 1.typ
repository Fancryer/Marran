#import "@preview/cheq:0.3.0"

#let start = datetime(year: 2026, month: 2, day: 19)
#let period = (start, start + duration(days: 7))
#let today = datetime(year: 2026, month: 2, day: 28)

= Project progress report --- NuML
\
*Date:* #today.display()

*Reporting period:* #period.map(d => d.display()).join(" to ")

\

#set heading(numbering: "1.1.")

= Overview

NuML is a statically typed functional programming language under development. The language follows a non-strict evaluation model and introduces an explicit, orthogonal effect layer separate from value types.

This reporting period focused on stabilizing the entire syntax layer:

- Formal grammar finalized
- Lexer fully implemented and tested
- Parser fully implemented with complete AST coverage

*Current focus:* roundtrip correctness and precedence-aware pretty-printing.

The frontend pipeline is now structurally complete:

Source Text #sym.arrow Tokens #sym.arrow AST

The current phase is devoted to validation and semantic consistency of this pipeline.

\
== Language model (current scope)

*Evaluation model:* non-strict.

Effects are represented syntactically and semantically as a layer orthogonal to value types. They are not encoded as types and are not treated as type constructors. Effect rows are parsed and represented explicitly in the AST.

Let-bindings are used for local bindings and value decomposition inside expressions. They are not currently used to implement general-purpose polymorphic generalization mechanisms.

The focus of this phase is syntactic correctness and structural integrity, not type inference.

\
= Completed work
== Formal grammar

The grammar is fully implemented and covers:
- Expressions (application, infix operators, control constructs, effect handling constructs)
- Literals
- Let-patterns
- Effect row syntax (closed and open forms, aliases)
- Top-level declarations
- Type syntax (parsing only; typing rules are outside current scope)

Expression precedence is resolved explicitly via a precedence table in the parser implementation.

Remaining work in this area is limited to documentation and refinement of presentation, not structural changes.

Full grammar is provided in Appendix A.

No blocking issues.

\
== Lexer

The lexer implementation is complete and stable.

*Token categories include:*
- Structural delimiters and punctuation
- Brackets and grouping constructs
- Operators and binding constructs
- Identifiers (term-level, infix, type variables)
- Keywords
- Literals:
  - Decimal integers
  - Hexadecimal integers
  - Decimal floating-point
  - Hexadecimal floating-point (binary exponent notation)
  - String literals
  - Boolean literals
  - Nil literal

*Design characteristics:*
- Deterministic tokenization with no context-sensitive branching.
- Support for numeric underscore separators.
- Unicode aliases for selected symbolic constructs.

*Testing strategy:*
- Unit tests for deterministic token recognition.
- Property-based tests for numeric literal normalization and parsing stability.

All lexer tests pass. Screenshots of test runs are provided in Appendix C.

\
== Parser and AST
The parser is fully implemented and covers all grammar rules.

*Key architectural aspects:*
- Parsing operates strictly on token streams (no direct character-level parsing).
- Expression parsing uses a precedence table to resolve associativity and operator hierarchy.
- AST nodes correspond directly to grammar constructs.
- Effect rows and handling constructs are represented explicitly in the AST.

\
*Current technical focus:*

*Roundtrip stability:*
AST #sym.arrow pretty-print #sym.arrow parse #sym.arrow AST

The pretty-printer currently lacks full precedence-aware parenthesization, which may lead to roundtrip mismatches in nested expressions. Addressing this is the main short-term task.

*Parser tests include:*
- Deterministic parsing examples.
- Structural AST comparison.
- Preliminary roundtrip tests.

Representative parsing examples are included in Appendix B.

\
= Validation status

#show: cheq.checklist
*Frontend completeness:*
- [x] Grammar
- [x] Lexer
- [x] Parser
- [x] AST coverage

*Validation stage:*
- [x] Lexer fully validated via automated tests.
- [x] Parser structurally validated via example programs.
- [/] Roundtrip validation in progress.

No architectural blockers identified.

\
= Next steps

1. Implement precedence-aware pretty-printer.
2. Stabilize roundtrip tests.
3. Expand parser test coverage for nested constructs.
4. Begin formal documentation of static semantics in the next development phase.

\
= Open issues

1. Pretty-printer requires precedence-aware parenthesis insertion.
2. Error recovery strategy is not yet implemented.
3. Test coverage for deeply nested effect constructs can be expanded.

\
= Short weekly log
To be updated.

\
= Appendix A - Formal grammar

NuML formar grammar is written in ANTLR4 (G4) format:
- `*` (asterisk) means 0+ repetitions;
- `+` (plus) means 1+ repetitions;
- `()` (parentheses) means grouping;
- `|` (vertical bar) means alternative (for example, `a | b` means `a or b`);
- `'str'` (text in single quotes) means string literal;
- `[]` (chars and escapes in brackets) means group of chars (for example, `[a-zA-Z0-9_*&$?]`);
- `?` (question mark) means 0-1 occurrences;
- `.` (dot) means any char (for example, `.+` means 1+ any chars).

== Lexer grammar

Lexer rules always start with uppercase letter (for example, `LexerRule1`).

```
lexer grammar NuMLLexer;

Dollar: '$';
AtSign: '@';
BackTick: '`';

Comment_Start: '/|';
Comment_End: '|\\';

BlockComment: Comment_Start .*? Comment_End -> channel(1);
Brace_Square_Left_Sharp: '#[';
Brace_Square_Left: '[';
Brace_Square_Right: ']';
Brace_Curly_Left_Sharp: '#{';
Brace_Curly_Left: '{';
Brace_Curly_Right: '}';
Brace_Paren_Left: '(';
Brace_Paren_Right: ')';

Char_String: '\'' ('\\\\' | '\\\'' | Char)*? '\'';
SemiColon: ';';
Colon: ':';
Comma: ',';
Ellipsis: '...';

OP_Assign: '=';
OP_Pipe: '|';
OP_Rebind: ':=';

Float: IntDigitPart '.' IntDigitPart ExponentPart?;
HexFloat: '0' [xX] (HexIntDigitPart? '.' HexIntDigitPart | HexIntDigitPart) HexExponentPart;
HexInt: '0' [xX] HexIntDigitPart;
Int: IntDigitPart;

KW_Effect: 'effect';
KW_Else: 'else';
KW_End: 'end';
KW_False: 'false' | '⊥';
KW_Forall: 'forall' | '∀';
KW_Funct: 'funct';
KW_Handle: 'handle';
KW_If: 'if';
KW_In: 'in' | '∈';
KW_Imm: 'imm';
KW_Let: 'let';
KW_Match: 'match';
KW_Resume: 'resume';
KW_Row: 'row';
KW_Then: 'then';
KW_To: 'to';
KW_True: 'true' | '⊤';
KW_Type: 'type';
KW_Under: 'under';
KW_Val: 'val';
KW_Var: 'var';
KW_With: 'with';

LineComment: '//|' ~[\r\n]* -> channel(1);

OP_Underscore: '_';

OP_Function: '->';
OP_MatchArrow: '=>';
OP_HRP_Arrow: '==>';

MetaName: BackTick Name;
InfixName: BackTick Name BackTick;
Name: [a-zA-Z_0-9+/%|&^~<=>.*!?-]+;

fragment Char: ~['];
fragment Digit: [0-9];
fragment ExponentPart: [eE] [+-]? Digit+;
fragment HexDigit: [0-9a-fA-F];
fragment HexExponentPart: [pP] [+-]? Digit+;
fragment HexIntDigitPart: HexDigit+ ('_' HexDigit+)*;
fragment IntDigitPart: Digit+ ('_' Digit+)*;
fragment SingleLineInputCharacter: ~[\r\n\u0085\u2028\u2029];

WS: [ \t\u000C\r\n]+ -> channel(1);
```

== Parser grammar
\

Parser rules always start with lowercase letter (for example, `parserRule1`).
```
parser grammar NuMLParser;

options
{
  tokenVocab=NuMLLexer;
}

chunk: stats=top_level_stat* EOF;

top_level_stat: type_def | eff_def | row_def | funct_def;

type_def: 'type' Name type_params? eff_params? '=' type;

funct_def: 'funct' Name type_params? eff_params? funct_args ':' (fx=eff_row)? out=type '=' block;

eff_def: 'effect' Name type_params? eff_params? effect_op* 'end';
row_def: 'row' Name type_params? '=' eff_row;

effect_op: Name ':' type;

funct_args: ocaml_style_arg+;

ocaml_arg: Name ':'? type;
ocaml_style_arg: '(' ocaml_arg ')' | nil;

bind_def: constant_qualifier lambda_param '=' exp;

constant_qualifier: 'var' | 'val' | 'imm';

block: (block_stat ';')* exp;

path_exp: exp '@' Name;

assign: (Name | path_exp) ':=' exp;

let_pattern: atom_let_pattern | lambda_param;

atom_let_pattern:
  '(' ')'
  | '_'
  | <assoc=right> '(' let_pattern (',' let_pattern)+ ','? ')'
  | '(' let_pattern ')'
  | '#{' Name ':' atom_let_pattern (';' Name ':' atom_let_pattern)+ '}'
  ;

block_stat: exp | bind_def | assign;

type_apps: '[' type_arg (';' type_arg)* ']';
eff_apps: '{' eff_arg (';' eff_arg)* '}';
eff_arg: eff_cons | '...' eff_row;
type_params: '[' Name+ ']';
eff_params: '{' Name+ '}';

eff_row:
  MetaName                                                    #eff_row_evar
  | Name                                                      #eff_row_alias
  | '{' (eff_row_entry (';' eff_row_entry)*)? ('|' Name)? '}' #eff_row_sugar
  ;

eff_row_entry: eff_cons | '...' eff_row;

eff_cons: Name type_params?;

type: funct_type;
funct_type: pair_type ('->' eff_row? funct_type)?;
pair_type: type_atom (',' pair_type)?;

type_atom:
  Name type_apps                #generic_type_alias
  | Name                        #flat_type
  | nil                         #nil_type
  | '[' type ']'                #array_type
  | '(' type ')'                #paren_type
  | MetaName                    #tvar_type
  | record_t                    #record_type
  | KW_Forall (
      type_params
      | eff_params
      | type_params eff_params
    ) '==>' type                #forall_type
  ;

record_t: '#{' record_t_prop (';'? record_t_prop)* ';'? '}';
record_t_prop: constant_qualifier Name ':'? type;

type_arg: funct_type_arg;
funct_type_arg: pair_type_arg ('->' funct_type_arg)?;
pair_type_arg: type_arg_atom (',' pair_type_arg)?;
type_arg_atom:
  Name                #flat_type_arg
  | nil               #nil_type_arg
  | '[' type_arg ']'  #list_type_arg
  | '(' type_arg ')'  #paren_type_arg
  | MetaName          #tvar_type_arg
  | Name type_apps    #generic_type_arg_alias
  | record_t_arg      #record_type_arg
  ;

record_t_arg: '#{' record_t_arg_prop (';'? record_t_arg_prop)* ';'? '}';
record_t_arg_prop: constant_qualifier Name ':'? type_arg;

exp: if_exp | let_exp | under | resume_exp;
resume_exp: 'resume' resume_exp | dollar_exp;
dollar_exp: backtick_exp ('$' dollar_exp)?;
backtick_exp: postfix_exp (InfixName postfix_exp)*;

postfix_exp: apply_exp postfix_op*;
postfix_op: '@' Name | 'with' (type_apps | eff_apps | type_apps eff_apps);
apply_exp: simple_term+;
if_exp: 'if' cond=exp 'then' then=exp 'else' else=exp;
let_exp: 'let' let_pattern '=' what=exp KW_In where=exp;

simple_term:
  literal                       #literal_exp
  | '(' exp (',' exp)+ ','? ')' #tuple_exp
  | '(' block ')'               #parens_exp
  | Name                        #name_exp
  ;

under:
  'under' eff_cons 'to' block
  'handle' (
    handler_clause+ ('|' 'then' '=>' block)?
    | handler_clause* '|' 'then' '=>' block
  );

handler_clause: '|' Name+ '=>' block;

literal: atom | array_literal | lambda_literal | record_literal;

atom: string | number | nil | boolean;
number: int | float;
nil: '(' ')';
boolean: KW_True | KW_False;
int: Int | HexInt;
float: Float | HexFloat;
string: Char_String;

array_literal: '[' (array_entry (',' array_entry)*)? ','? ']';
array_entry: exp | block ';';

lambda_literal: '{' type_params? eff_params? lambda_head? block '}';

lambda_params: ('(' lambda_param ')' | nil | Name)+ | '(' lambda_param (';' lambda_param)+ ')';
lambda_head: lambda_params ('|' out=type)? '=';
lambda_param: Name (':'? type)?;

record_literal: '#{' (exp '|')? bind_def (';' bind_def)* ';'? '}';
```

\
= Appendix B — Code Examples
Below are examples of property-based tests, some of which are temporarily written directly within the main spec test function, while others are moved to separate functions.

```hs
-- inside spec funtion: fragment start
it "parses complex string" $
  property $ do
    let allowedChars = ['\0'..'\127'] \\ ['\'']
    let escapeSeq = elements ["\\\\", "\\'"]
    let regularChar = elements $ allowedChars \\ ['\\']
    n <- T.concat <$> listOf (oneof [T.singleton <$> regularChar, escapeSeq])
    let input = "'" <> n <> "'"
    pure $ parseTokens input `shouldBe`
      Right [TString $ T.replace "\\\\" "\\" $ T.replace "\\'" "'" n]

it "parses escaped backslash" $
  property $ do
      l <- genName
      r <- genName
      pure $ parseTokens (T.concat ["'", l, "\\\\", r, "'"]) `shouldBe`
        Right [TString $ l <> "\\" <> r]
-- inside spec function: fragment end

prop_decInt :: Positive Integer -> Bool
prop_decInt (Positive n) = parseTokens (T.pack $ show n) == Right [TInt n]

prop_decIntUnderscore :: Positive Integer -> Property
prop_decIntUnderscore (Positive n) =
  forAll (insertUnderscores $ show n) $ \txt ->
    case parseTokens $ T.pack txt of
      Right [TInt m]  -> m == n
      _               -> False

prop_hexInt :: Positive Integer -> Bool
prop_hexInt (Positive n) =
  let hex = showHex n ""
      txt = "0x" ++ hex
  in case parseTokens $ T.pack txt of
       Right [THexInt m]  -> m == n
       _                  -> False

prop_noCrash :: String -> Bool
prop_noCrash s =
  case parseTokens $ T.pack s of
    Left _  -> True
    Right _ -> True

insertUnderscores :: String -> Gen String
insertUnderscores = \case
  [] -> pure []
  [x] -> pure [x]
  (x:xs) -> do
    rest <- insertUnderscores xs
    insert <- arbitrary
    pure $ x : (if insert then '_' : rest else rest)
```

\
And there are some examples of expressions in NuML and their corresponding AST. Examples was partially generated, some of them are hand-written:

```hs
printExps :: IO ()
printExps = do
  arr <- generate $ do
    depth <- choose (0, 5)
    vectorOf 2 $ genTopExp depth
  mapM_
    (\a ->
      do
        putStrLn $ T.unpack $ T.append "Exp: " $ pretty a
        putStrLn $ "Exp AST: " ++ show a)
    arr
  _ <- putStrLn ""
  let
    parseAndPrintExp = either
      (putStrLn . (++) "Error: ")
      (\e -> do
        printf "Exp: %s\n" $ pretty e
        printf "Exp AST: %s\n" $ show e)
      . parseExpFromText
  _ <- parseAndPrintExp "#{val x    : Int = 5  }@   x"
  _ <- parseAndPrintExp "[1, 2, 3]"
  _ <- parseAndPrintExp "if pred x y then 42 else if f z 4 then 5 else 0"
  pure ()
```

//#image("Exp AST examples.png")

Some examples of complex parser or lexer rules:

```hs
-- Lexer.hs:
hexFloatLiteral :: Lexer Scientific
hexFloatLiteral = lexeme $ do
  _ <- char '0'
  _ <- oneOf ['x', 'X']
  (a, b) <- choice [
    do
      a <- optional hexIntDigitPart
      _ <- char '.'
      (,) (fromMaybe "" a) <$> hexIntDigitPart,
    do (, "") <$> hexIntDigitPart
    ]
  e <- hexExponentPart

  let
    mantissa = parseHexInt $ a <> b
    fracLen  = length $ stripUnderscore b
    base     = scientific mantissa $ (-4) * fracLen
    exp2     = parseExponent e

  pure $ base * (2 ^^ exp2)

token :: Lexer Token
token = choice [
    infixName,
    tvar,
    sym "$" TDollar,
    sym "@" TAt,
    sym "`" TBackTick,
    sym "#[" TSharpSquareL, sym "[" TSquareL, sym "]" TSquareR,
    sym "#{" TSharpBraceL,  sym "{" TBraceL,  sym "}" TBraceR,
    sym "(" TParenL,        sym ")" TParenR,
    sym ":=" TRebind,
    sym ":" TColon,
    sym "," TComma,
    sym "..." TEllipsis,
    sym "=>" TMatchArrow,
    sym "==>" THRPArrow,
    sym "=" TAssign,
    sym "|" TPipe,
    sym "_" TUnderscore,
    sym "->" TArrow,
    kw "effect" KWEffect,
    kw "else" KWElse,
    kw "end" KWEnd,
    choice $ map (`kw` KWFalse) ["false", "⊥"],
    choice $ map (`kw` KWForall) ["forall", "∀"],
    kw "funct" KWFunct,
    kw "handle" KWHandle,
    kw "if" KWIf,
    choice $ map (`kw` KWIn) ["in", "∈"],
    kw "imm" KWImm,
    kw "let" KWLet,
    kw "match" KWMatch,
    kw "resume" KWResume,
    kw "row" KWRow,
    kw "then" KWThen,
    kw "to" KWTo,
    choice $ map (`kw` KWTrue) ["true", "⊤"],
    kw "type" KWType,
    kw "under" KWUnder,
    kw "val" KWVal,
    kw "var" KWVar,
    kw "with" KWWith,
    THexFloat <$> try hexFloatLiteral,
    TFloat <$> try floatLiteral,
    THexInt <$> try hexIntLiteral,
    TInt <$> intLiteral,
    charString,
    name
  ]

stringChar :: Lexer Char
stringChar = choice [
    string "\\\\" $> '\\',
    string "\\'" $> '\'',
    satisfy (/= '\'')
  ]


charString :: Lexer Token
charString = lexeme $ TString . T.pack <$> between (char '\'') (char '\'') (many stringChar)
```

```hs
-- Parser.hs:
typ :: Parser Typ
typ = makeExprParser typAtom table
  where
    table = [[InfixR $ TPair <$ commasym], [InfixR functionOp]]
    functionOp = do
      symbol TArrow
      eff <- optional effRow
      pure $ \from to -> TFunct from to eff

typAtom :: Parser Typ
typAtom =
  choice [
    try $ TGenericAlias <$> name <*> typeApps,
    TFlat <$> name,
    TNil <$ nil,
    TArray <$> brackets typ,
    try $ TParen <$> parens typ,
    TVar <$> meta,
    TRecord <$> recordType,
    forallType
  ]

recordType :: Parser RecordTyp
recordType = sharpBraces $
  RecordTyp <$> sepBy1 recordTProp (optional semisym) <* optional semisym

forallType :: Parser Typ
forallType = do
  keyword KWForall
  (ts, es) <- choice [
      -- ts es
      try $ (,) <$> typeParams <*> effParams,
      -- ts
      (, mempty) <$> typeParams,
      -- es
      (mempty, ) <$> effParams
    ]
  symbol THRPArrow
  TForall ts es <$> typ

recordTProp :: Parser RecordTypProp
recordTProp = do
  q <- constantQualifier
  n <- name
  _ <- optional colonsym
  RecordTypProp q n <$> typ
```

\
= Appendix C — Test Evidence
As part of the lexer development, comprehensive testing was implemented using `Hspec` and `QuickCheck`, including both unit tests and property-based tests.

== Integer Literal Testing
- Decimal numbers: testing parsing of arbitrary positive integers (`prop_decInt`);
- Hexadecimal numbers: verifying correct parsing of 0xFF-style literals (`prop_hexInt`);
- Underscores in numbers: testing support for underscore separators (`prop_decIntUnderscore`), including generating random positions for underscores.
== Floating-Point Number Testing
Verifying parsing of floating-point numbers with preserved precision (e.g., `12.34` #sym.arrow `12.34`).

== Identifier and Keyword Testing
Ensuring keywords are not split from subsequent characters (e.g., `keywordX` is recognized as a single identifier rather than keyword `keyword` + identifier `X`).

== String Literal Testing
- Simple strings: parsing quoted strings with arbitrary content;
- Escaped quotes: verifying correct handling of `\'` within strings;
- Escaped backslashes: testing `\\\\` handling;
- Complex strings: generating strings with mixed content including regular characters (excluding `'` and `\`) and escape sequences, verifying that escaped sequences are correctly transformed into corresponding characters.

== Robustness Testing
"No crash" property (`prop_noCrash`): ensuring the lexer handles any input without crashing (returning either a successful result or an error).

== Data Generators
Specialized generators were developed for property-based tests:
- Random insertion of underscores into string representations of numbers;
- Identifier name generation;
- String generation considering escaping rules;

Results
All tests pass successfully, confirming the lexer works correctly on both typical and edge cases, including proper handling of escape sequences and support for underscore separators in numbers.

//#image("Lexer tests.png")