# kore-lean: ILDS koreparser on Lean v4.34.0, with a printer and a round-trip test

State: milestone 1, step M1.1 ([../milestone-1/README.md](../milestone-1/README.md)), done 2026-11-05.
This package is the Lean syntax of KORE and the reader of the KORE krust emits.
Its AST is the input of the translation to applicative matching logic of step M1.2.
It is a standalone Lake package on Lean `v4.34.0` with no dependency: no Mathlib, no Batteries.

`Q-kore-reader` ([../goals.toml](../goals.toml)) was resolved for the port:
the port reads every KORE file listed under "Results" and the round-trip holds on each.

## Upstream

Upstream: <https://gitlab.com/ilds/aml-lean/koreparser>, commit `11b91adeb291a53266f27e90ab57641649398bd2` (2025-01-08, "Delete definition.kore"), written for Lean `nightly-2023-08-17`.
Upstream has three source files: `KoreParser/AST.lean`, `KoreParser/Parser.lean` (a `Parsec` reader) and `KoreParser/ParserDSL.lean` (a reader through Lean's syntax categories).
The upstream MIT `LICENSE` and the per-file copyright headers are kept;
files new in this port carry a header that names the same license.

## Layout

| File | Content |
|---|---|
| `KoreParser/AST.lean` | the KORE syntax (ported, reshaped; see "AST") |
| `KoreParser/Parser.lean` | the reader (ported from upstream `Parser.lean`) |
| `KoreParser/Printer.lean` | the printer from AST to KORE text (new) |
| `KoreParser/Tokens.lean` | the token stream that the round-trip test compares (new) |
| `KoreParser/Stats.lean` | small total functions over the AST, and kernel-checked examples (new) |
| `RoundTrip.lean` | the `roundtrip` executable, which is also the `lake test` driver (new) |
| `test/features.kore` | a hand-written definition that uses every construct of the grammar (new) |
| `test/Eval.lean` | `#eval` of the total functions on `../kcore-spec/examples/peano/Peano/definition.kore` (the milestone-1 subject, Source paths relative) (new) |
| `scripts/generate-kore.sh` | regenerates the KORE of the k-rust examples and of IMP with krust (new) |

## AST

The grammar is the one of `haskell-backend/docs/kore-syntax.md`.
The choices that matter to M1.2:

- `Pattern` is one inductive type whose children are `List Pattern` or `Pattern`.
  A function over it recurses structurally, mutually with a function over `List Pattern`
  (`termination_by structural`), as `Pattern.size` in `KoreParser/Stats.lean` and the printer do.
  Lean v4.34.0 accepts this, and the kernel reduces such functions: `Pattern.size` of a sample axiom is checked by `decide`.
- `KSort` has the same shape (`var`, or `ctor` with `List KSort` arguments).
  `R` is `KSort.var`, `R{}` is `KSort.ctor R []`, as the text distinguishes them.
- Identifiers are plain strings wrapped by role:
  `SymbolIdent`, `EVarIdent`, `SVarIdent`, `SortIdent`, `ModuleName`, `SortVar`, each over `Identifier := { name : String }`.
  A set variable's name is stored without its `@`; a `\`-prefixed symbol keeps its `\`.
- String literals and domain values hold the decoded code points (a Lean `String`), not the escaped text.
- `\and` and `\or` are n-ary (`List Pattern`), as the grammar's `<patterns>` says.
  `\left-assoc` and `\right-assoc` are kept as constructors with the symbol, its sorts and the operands;
  expanding them into nested applications is left to the translation.
- Attributes are `List AppPattern` (an application pattern: head, sorts, arguments), in their textual order.
- Sentences keep upstream's constructors (`import`, `sort`, `hookedSort`, `symbol`, `hookedSymbol`, `alias`, `axiom`, `claim`);
  all sequences are `List`.
- Every type derives `Repr`, `BEq` and `Inhabited`, and has `DecidableEq`.
  Lean v4.34.0 does not derive `DecidableEq` for nested inductive types,
  so `KSort.decEq` and `Pattern.decEq` are written by mutual structural recursion (constructor index first, then fields);
  the other types derive it.

The parser is `partial`; the printer, the `DecidableEq` instances and the functions of `Stats.lean` are total.

## What changed from upstream, and why

Build and packaging:

- `lean-toolchain` is `leanprover/lean4:v4.34.0`; `lakefile.lean` became `lakefile.toml`.
- `Lean.Data.Parsec` no longer exists; its successor in core is `Std.Internal.Parsec.String.Parser`, which the port uses.
  It is part of the Lean toolchain, so no Batteries dependency is needed.
- Upstream `Main.lean` (`Hello, {hello}!`, referring to an undefined `hello`) and the empty root `KoreParser.lean` are replaced by a root that imports the modules and by `RoundTrip.lean`.
- `ParserDSL.lean` is not ported.
  It reads KORE through Lean syntax categories, so it needs a Lean `Environment` at run time (`runParserCategory`), traces every identifier with `dbg_trace`, reads `\nu` as `\mu`, and duplicates `Parser.lean`.
  `Parser.lean` is the reader.
- The `#eval`s, `#check`s and inline sample inputs in the upstream sources are removed; the tests read real files.

AST (`AST.lean`):

- `Array` children became `List`, for structural recursion (see "AST").
- Upstream's mutual `Pattern`, `AppPattern`, `MultiOr`, `MLPattern` became one inductive `Pattern`:
  the split forced mutual recursion over four types for every function.
  The constructors keep upstream's names (`var`, `string`, `top`, …, `exist`, `forall`, `mu`, `nu`, `ceil`, …, `dv`);
  `appPattern` became `app`.
- `\and` and `\or` became n-ary.
  Upstream accepted exactly two operands, which the grammar does not require and krust does not respect (see "Findings").
- `MultiOr`, `leftAssocMultiOr` and `rightAssocMultiOr` are removed:
  the grammar puts only an application pattern under `\left-assoc` and `\right-assoc`, and an n-ary `\or` is now a pattern of its own.
- `Symbol`, `Alias` and `SymbolOrAlias` were mutual inductive types with no recursion; they are structures (`Symbol` and `Alias` extend `SymbolOrAlias`).
- `KAttribute` (a wrapper of `AppPattern`) is replaced by `AppPattern`.
- `BEq`, `Hashable`, `Inhabited` and `DecidableEq` were added (upstream derived only `Repr`).
- The `partial` `ToString` instances of `KSort` and of patterns, which printed a non-KORE notation (`⊤<s>`, `φ ∧<s> ψ`, and a placeholder for multi-or), are removed; `Printer.lean` prints KORE.

Reader (`Parser.lean`), bugs fixed against the grammar:

- Identifier characters: upstream accepted `\` and rejected `'` after the first letter.
  The grammar's identifier is a letter followed by letters, digits, `'` and `-`;
  every krust definition uses `'` (`Lbl'Unds'…`), so upstream could not read any.
- `\forall` was parsed by a copy of the `\exists` parser (matching the text `\exists` and building `.exist`).
- `\dv` was commented out of the pattern alternatives, so no domain value could be read.
- String literals were read up to the first `"` with no escapes.
  They are now decoded as the grammar says: printable ASCII other than `"` and `\` stands for itself, and `\t \n \f \r \" \\ \xhh \uhhhh \Uhhhhhhhh` each name one code point.
  A raw character outside printable ASCII, an unknown escape, a surrogate or a code point above U+10FFFF is an error.
- Comments (`// …`, `/* … */`), which the grammar treats as whitespace, are skipped.
- A keyword is now a whole identifier token: upstream matched the keyword as a prefix followed by one whitespace character.
- A symbol identifier may start with `\` (`<symbol-identifier> ::= ['\']? <identifier>`); upstream left it out because it could not tell such a symbol from a connective.
  The port reads the name after `\` and treats it as a connective when it is one of the grammar's connectives, as a symbol otherwise.
- A definition must be followed by end of input; upstream ignored trailing text.

Reader, structure:

- Upstream chose a production by trying alternatives under `attempt`.
  The port chooses by the next character, which the grammar permits:
  `"` begins a string literal, `@` a set variable, `\` a connective or a `\`-symbol,
  and an identifier is an element variable when `:` follows it and an application otherwise.
  A sentence is chosen by its keyword, and a module's sentences end at `endmodule`.
  The accepted language is the same, and an error reports the position where the input stops fitting.
- Empty lists (`{}`, `()`, `[]`) are recognized by their closing delimiter rather than by a failing first item.

## The round-trip test

For each input file `f`, `roundtrip` requires:

1. `parse f` succeeds, giving `d`;
2. `parse (print d)` succeeds and equals `d` (by `DecidableEq`);
3. the token streams of `f` and of `print d` are equal.

Token stream (`KoreParser/Tokens.lean`):
whitespace (space, tab, line feed, carriage return) and comments separate tokens and are dropped;
a token is a punctuation mark (`{`, `}`, `(`, `)`, `[`, `]`, `,`, `:`, `:=`),
an identifier (the longest run of identifier characters after a letter, with its leading `\` or `@` if any; keywords included),
or a string literal, compared by its decoded code points, so `"\x41"` and `"A"` are the same token.
The token reader uses the parser's identifier and string-literal readers;
the escape decoding and the printer's escaping are checked separately by unit checks.

Before the files, `roundtrip` runs unit checks on constructs the krust inputs lack:
escape decoding and printing, rejection of bad literals, `\nu` versus `\mu`, `\forall` versus `\exists`,
`R` versus `R{}`, n-ary and nullary `\and`/`\or`, `'` and `-` in identifiers, `\`-symbols, comments, keywords, trailing input.

Run from this directory:

```sh
lake build
lake test                        # unit checks, ../kcore-spec/examples/peano/Peano/definition.kore, test/peano-syntaxDefinition.kore (milestone-1's texts, Source paths relative), test/features.kore
scripts/generate-kore.sh gen > gen.list   # the examples' and IMP's KORE, into gen/ (ignored by .gitignore)
lake exe roundtrip $(cat gen.list)
lake env lean test/Eval.lean     # axioms by top connective, and \and/\or arities, of definition.kore
```

`generate-kore.sh` runs `<repo>/target/release/krust kcompile` on each `<repo>/examples/*.k` (main module: the upper-cased file stem),
on IMP (`imp-semantics/src/kimp/kdist/imp-semantics/imp.k`, `IMP`, `IMP-SYNTAX`, as `benchmarks/registry/imp.toml` compiles it),
and on IMP for proving together with `imp-semantics/examples/specs/imp-simple-spec.k`, whose output carries claims.

## Results (2026-11-05)

krust: `target/release/krust` (`krust 0.8.0`, built 2026-11-03) in the k-rust checkout at `b51b1f0e8`;
it regenerates `../milestone-1/kore/definition.kore` byte for byte.
Every file passes all three conditions; `macros.kore` is not an input (see "Findings").

```toml
# file = [bytes, tokens, sentences, axioms, claims]
"milestone-1/kore/definition.kore"        = [107740, 24677,  323, 202,  0]
"milestone-1/kore/syntaxDefinition.kore"  = [ 42585,  9140,  142,  21,  0]
"test/features.kore"                      = [  1747,   630,   22,   9,  1]
"arithmetic/definition.kore"              = [ 93303, 21471,  286, 175,  0]
"list-unification/definition.kore"        = [164531, 37222,  469, 313,  0]
"map-framing/definition.kore"             = [215084, 46566,  532, 354,  0]
"rewrite/definition.kore"                 = [ 94481, 21531,  288, 176,  0]
"z3-inference/definition.kore"            = [ 94573, 21694,  288, 176,  0]
"imp/definition.kore"                     = [585416, 98287, 1188, 971,  0]
"imp-proof/definition.kore"               = [592701, 98919, 1188, 971,  0]
"imp-spec/definition.kore"                = [636900, 105316, 1205, 975, 13]
# and each example's syntaxDefinition.kore (39-111 kB), all passing
```

`examples/reachability.k` and `examples/transitive-reachability.k` do not compile as definitions (`ClaimInDefinition`: they are specifications) and are skipped; IMP's specification covers claims instead.

Timings on the shared host (load average about 50):
`lake build` from clean takes 5.7 s and 0.68 GB.
The whole round-trip of the largest file, `imp-spec/definition.kore` (637 kB: parse, print, parse again, compare, tokenize both), takes 0.15 to 0.21 s and 31.6 MB peak RSS (`time -f %M`); the parse alone measures about 13 ms in the driver.

On `definition.kore`, `test/Eval.lean` gives 202 axioms of 2,374 pattern nodes, by top connective:
`\implies` 101, `\exists` 73, `\or` 13, `\equals` 11, `\not` 2, `\rewrites` 2.

## Findings about the KORE krust emits

- krust emits n-ary `\or`: in `definition.kore`, four with 3 operands and one with 17 (the no-junk axioms of the subject's sorts).
  This is valid per the grammar (`<patterns>`), and is one reason upstream could not read krust's output.
- All attributes krust emits are application patterns, as the grammar requires.
- The inputs contain no escape sequence, no comment, no `\left-assoc`/`\right-assoc`, no `\forall`, `\mu`, `\nu`, `\next`, `\floor` or `\iff`;
  `test/features.kore` and the unit checks cover those.
- `kcompile` writes a `macros.kore` of one line feed when there are no macros.
  That is not a `<definition>`: the grammar requires a `[ … ]` attribute list and at least one module.
- No text krust emitted in these inputs was outside the grammar.
