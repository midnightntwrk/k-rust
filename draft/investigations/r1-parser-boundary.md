# R1: Rust parser compatibility boundary

> **Historical scope:** this report established that the proposed surface can
> be parsed as Rust. R12 subsequently proved and selected the stronger
> requirement that supported KRS source is a genuine rustc-valid Cargo crate
> hosted by procedural macros. Statements below that rustc validity is not
> required describe the pre-R12 decision and are superseded.

## Decision

KRS can keep the proposed **outer language** valid Rust concrete syntax. The
current forms do not justify a Rust parser fork or an independently maintained
Rust-like grammar.

Use `syn::File` as the initial outer parser, then give KRS its own parsers for
the token payloads of `k::...` attributes and a small, closed set of macros
such as `k![...]`, `term![...]`, and `map_cell![...]`. In other words, the
boundary should be:

```text
Rust grammar: modules, imports, items, types, functions, ordinary expressions
              and ordinary patterns
KRS grammar:  k:: attribute payloads and explicitly named macro payloads
```

This is a Rust-parsable language, not necessarily a crate that `rustc` can
name-resolve or type-check. That distinction should be part of the eventual
compatibility promise.

## Tested artifact

[`r1-imp-sample.rs`](r1-imp-sample.rs) is a 100-line IMP-like slice containing:

- builtin imports and open sort traits;
- token and closed-constructor declarations;
- expression and statement productions with concrete-syntax, precedence,
  associativity, and strictness attributes;
- a two-cell configuration and initializer;
- a multi-cell assignment rule with a guard; and
- a short-circuit expression rule.

The sample intentionally exercises the boundary rather than claiming to be a
complete port of every IMP production and rule.

The local tool versions were:

```text
rustc 1.97.1 (8bab26f4f 2026-07-14)
cargo 1.97.1 (c980f4866 2026-06-30)
rustfmt 1.9.0-stable (8bab26f4f6 2026-07-14)
syn 2.0.119, features = ["full"]
edition = 2024
```

A temporary Cargo harness performed exactly this check:

```rust
let source = std::fs::read_to_string(path)?;
let file = syn::parse_file(&source)?;
println!("parsed {} top-level items", file.items.len());
```

Observed results:

```text
$ wc -l draft/investigations/r1-imp-sample.rs
100 draft/investigations/r1-imp-sample.rs

$ cargo run --offline --quiet --manifest-path <syn-check>/Cargo.toml -- \
    draft/investigations/r1-imp-sample.rs
parsed 23 top-level items

$ rustfmt --edition 2024 --emit stdout \
    draft/investigations/r1-imp-sample.rs >/dev/null
# exit status 0

$ rustc --edition 2024 --crate-type lib --emit metadata \
    draft/investigations/r1-imp-sample.rs
error[E0433]: cannot find module or crate `k` in this scope
...
```

`rustc` reached name and macro resolution and reported the expected missing
`k` crate/attributes/macros; it reported no parser error. This is evidence for
Rust grammar compatibility, not for ordinary Rust compilation.

Three smaller probes located the edge precisely:

```rust
// Accepted by syn as one Rust item. The macro body is a balanced token tree.
#[k::requires(x != 0)]
fn rule(x: Term) -> Term {
    match x {
        k![<k> $PGM => result ... </k>] => term![result],
        _ => x,
    }
}

// Rejected: "unexpected token, expected `;`".
fn direct_rewrite(x: Term) -> Term {
    x => result
}

// Rejected: "expected `=>`" after `value`.
fn sort_ascription(x: Term) -> Term {
    match x {
        value: Value => value,
        _ => x,
    }
}
```

Thus even K-looking tokens such as cells, `$PGM`, `=>`, and `...` can occur in
a Rust-parsable file when they are deliberately inside a macro token tree.
They cannot be added directly to Rust expression or pattern grammar.

## What remains ordinary Rust syntax

The following proposed forms parsed without accommodation:

| KRS concept | Rust parse form | Parser result |
|---|---|---|
| Module/import/builtin | `mod`, `use` | Native Rust AST |
| Open sort | attributed `trait` | Native item and supertrait AST |
| Subsort membership | `impl Trait for Type` | Native impl AST |
| Constructor/token | attributed struct/enum | Native data AST |
| Configuration | attributed struct and `impl` | Native item AST |
| Rule identity | attributed standalone `fn` | Native function AST |
| Whole-state rule | `match` returning `Option` | Native expression AST |
| As/or/wildcard/record patterns | `@`, `|`, `_`, `{ .. }` | Native pattern AST |
| Syntax template/regex | string or raw string in attribute | Rust literal token |
| K sequence/map/term pattern | macro in pattern position | Native `Pat::Macro` shell |
| K sequence/map/term result | macro in expression position | Native `Expr::Macro` shell |

`syn` represents an attribute list and a macro body as a `TokenStream`, so it
does not require those inner tokens to be a Rust expression. It also has an
explicit `Pat::Macro` form, which is why the sample's `k![...]` and
`term![...]` patterns parse in match arms.

## Attribute boundary

Attributes are sufficient for declarative metadata, with two implementation
rules.

First, do not run every attribute through the conventional nested-meta parser.
Different attributes need typed payload parsers:

- `#[k::syntax("...", precedence = 60, assoc = "left")]` can use a
  comma-separated KRS metadata parser;
- `#[k::strict(sequence = [lhs, rhs])]` should parse its field-name list as a
  Rust array-like payload and then resolve the names against the production;
- `#[k::requires(x != 0)]` should parse its arguments as a restricted
  `syn::Expr`, then lower that expression to logical IR; and
- `#[k::raw_attr("preserves-definedness")]` should accept only the documented
  literal/raw representation and retain it exactly.

`syn::Attribute::parse_args` explicitly supports expression-shaped arguments;
`parse_nested_meta` is only for the conventional Rust meta-item convention.
Using the latter indiscriminately would create an artificial limitation.

Second, the compiler must validate where each `k::` attribute is legal and
reject every unknown typed attribute or field. `syn` deliberately performs no
such semantic check. A namespaced attribute path is syntactically Rust, but
without a companion macro crate `rustc` will report it as unresolved.

Practical attribute limits are:

- the payload must still lex as balanced Rust token trees;
- an attribute can only be attached where Rust permits an outer or inner
  attribute;
- attribute expressions do not provide new binders or new pattern grammar;
  and
- large object-language grammars may become unreadable as attributes, even
  though they remain parseable. That readability question belongs to R4, not
  to the Rust parser decision.

## Macro and pattern boundary

Macros are the necessary escape hatch for K patterns which Rust cannot express
natively. They cover K sequences, associative collections, dynamic term
destructuring, cell fragments, and—if desired—local rewrite notation.

There are meaningful costs:

1. The outer parser sees only `Pat::Macro` or `Expr::Macro`. It does not know
   that `name`, `value`, `rest`, or `env` are bindings. The KRS macro-payload
   parser must produce a pattern AST and merge its bindings into the enclosing
   rule scope.
2. A Rust trait object cannot be structurally destructured. A wrapper such as
   `Term<dyn Expr>` therefore needs `term![...]` for constructor matching, or a
   different typed term representation chosen by R2.
3. Rust slice-rest syntax is not a general sequence construction syntax, and
   Rust has no map/set associative pattern. `k![head, rest @ ..]`,
   `k![..rest]`, and map remainder forms need KRS parsing inside the macro.
4. Rust's `value @ pattern`, or-pattern, `_`, and record patterns should remain
   native wherever possible. KRS should not duplicate ordinary patterns in a
   macro unless dynamic/open-sort matching forces it.
5. Macro bodies must be token-based and whitespace-insensitive. `rustfmt` may
   change spacing or layout inside macro invocations. Object-language syntax
   and pretty-print formats whose spaces matter should stay in string
   literals.
6. Standard Rust refactoring and semantic IDE features stop at the macro
   boundary. Highlighting and delimiter matching remain available, but field
   rename and binding analysis require a KRS language-server plugin.

Direct `x => y` local rewrites and K's `X:Sort` pattern annotation are the two
tested examples that cannot inhabit the normal Rust expression/pattern AST.
The current design already has honest alternatives: whole pre/post state
construction for rewrites and typed constructors, wrapper APIs, guards, or a
term-pattern macro for sort refinement.

## Required grammar extensions

For the forms currently proposed: **none**.

The following would require extensions only if KRS insists on putting them
outside explicit macro islands:

| Desired spelling | Conflict with Rust grammar | Compatible spelling |
|---|---|---|
| `old => new` as an expression | `=>` is not a Rust binary operator | explicit pre/post match, or `rewrite!(old => new)` |
| `value: Value` inside a match pattern | `:` is not general pattern ascription | typed constructor/guard, or `term![value: Value]` |
| literal `<k> ... </k>` cells | angle tokens do not form a Rust item/pattern | configuration records and `k![...]` |
| AC map/set destructuring | Rust has no collection-pattern protocol | `map![key => value, rest @ ..]` |
| matching-logic binders/operators | Rust expressions have different binding and truth semantics | a marked `ml![...]` form or typed `k::ml` API |
| K precedence block operators such as `>` | not Rust declaration syntax | repeated typed syntax attributes or a grammar macro/item |

A new top-level grammar should be considered only if a later investigation
shows that these explicit islands dominate normal Rust code or make real KWasm
or KMIR definitions materially less readable. Parser novelty by itself is not
a reason to abandon the Rust shell.

## Recommended parser architecture

1. Parse the complete source with a pinned `syn` version and explicit Rust
   edition. Keep the original source alongside the AST; `syn` is not a
   lossless concrete syntax tree and does not retain comments/trivia for
   rewriting.
2. Accept a documented Rust item subset. Reject unmarked ordinary Rust behavior
   that the KRS IR cannot lower, even though `syn` can parse it.
3. Dispatch recognized `k::` attributes to small typed parsers. Parse logical
   expressions into a restricted Rust-expression AST before lowering; never
   preserve an unchecked token blob except through `k::raw_attr`.
4. Dispatch only reserved KRS macro names to context-specific parsers
   (`Pattern`, `Term`, `KSequence`, collection pattern, or matching logic).
   Unknown macros should be a diagnostic, not silently treated as executable
   Rust.
5. Normalize native Rust patterns and KRS macro patterns into one explicit
   pattern IR before type checking. This is where binding, framing, symbolic
   matching, and pre/post rewrite semantics become visible.
6. Preserve `proc_macro2` spans and stable source-item identifiers for lowering
   diagnostics. Add differential parser fixtures that must parse with both
   `syn` and the repository's pinned `rustfmt`/Rust toolchain.
7. Treat a companion `k` crate providing IDE-visible names or procedural macros
   as optional tooling. The compiler should not depend on `rustc` macro
   expansion; pattern macros and K's relational semantics are easier and more
   honest to analyze directly.

`syn`'s main architectural shortcomings are first-error parsing and lack of a
lossless/error-recovering CST. If compiler-quality multi-error recovery or an
IDE becomes an immediate requirement, evaluate a versioned rust-analyzer
syntax parser as the outer CST while retaining the same Rust-shell/KRS-island
language boundary. `rustc_private` is a worse default because it requires a
nightly compiler and tightly couples KRS to compiler internals.

## Consequence for the broader design

R1 resolves only lexical/grammatical compatibility. It does not validate the
semantic honesty or readability of the proposed trait, rule, grammar, and
configuration mappings. R2–R5 still need to determine those shapes. They can,
however, proceed under a useful constraint: prefer native Rust AST forms, and
put every unavoidable K-specific grammar behind a visibly named attribute or
macro rather than silently changing Rust grammar.
