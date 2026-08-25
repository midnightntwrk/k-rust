# R4: Object-language grammar

## Decision

Use a **hybrid grammar design**:

1. nominal term productions live on Rust structs and enum variants, with a
   checked `#[k::syntax("...")]` template referring to named fields; and
2. grammar relationships and non-nominal productions live in a small set of
   item-position macro islands such as `k::precedence!`, `k::associativity!`,
   and `k::grammar!`.

Attributes alone are concise for the common case but cannot honestly model
every K grammar sentence. A separate grammar DSL for everything would duplicate
the data model and weaken the Rust correspondence. The hybrid keeps constructor
definitions Rust-native while making genuinely grammatical concepts explicit.

All proposed forms fit the R1 boundary: Rust items outside, KRS token parsers
inside namespaced attributes and macros. No Rust grammar fork is needed.

## Nominal productions

Named Rust fields become named K non-terminals. The syntax template interleaves
literal terminals and field placeholders:

```rust
#[k::syntax("{lhs} + {rhs}", group = "additive")]
#[k::strict(sequence = [lhs, rhs])]
pub struct Add {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

impl Expr for Add {}
```

The compiler must check that:

- each field occurs exactly once unless a future feature explicitly permits an
  omitted or repeated grammar argument;
- every placeholder names a field;
- literal braces are escaped;
- the field sort is known and legal in that production;
- template terminals do not contain unescaped layout that should instead be a
  pretty-print directive; and
- the declared symbol and overload group, if present, are unique/well formed.

The template is a grammar declaration, not Rust's `format!` language and not a
runtime string. Its deliberately small placeholder grammar should be parsed by
KRS and diagnosed at the field span.

Tuple structs and tuple enum variants may use positional placeholders (`{0}`,
`{1}`), but named fields should be the project style. They improve record
patterns, generated projection functions, diagnostics, and refactorability.

If `#[k::syntax]` is omitted, KRS may generate a prefix production from the
Rust item path for internal constructors:

```text
Add(lhs: Expr, rhs: Expr)
```

The generated spelling and symbol must be stable and inspectable. Public
object-language syntax should be explicit rather than relying on that default.

## Closed enums and open sorts

An attributed enum defines a closed constructor family and one K sort:

```rust
#[k::constructors]
pub enum Boolean {
    #[k::syntax("true")]
    True,
    #[k::syntax("false")]
    False,
}

impl Value for Boolean {}
```

Each variant lowers to a production returning `Boolean`; the `impl` lowers to
the subsort production placing `Boolean` in open sort `Value`. This avoids
pretending the enum itself can be reopened.

An empty `#[k::sort] trait` lowers to a sort declaration. A supported sort
implementation lowers to a subsort production with no constructor label.

## Precedence and associativity

K precedence is a partial order over production groups, and group
associativity can cover several productions. Numeric precedence on individual
attributes would lose that structure and encourage a known K mistake: marking
`+` and `-` individually left-associative does not make mixed `x + y - z`
unambiguous.

Use named groups on productions and module-level declarations:

```rust
#[k::syntax("{lhs} * {rhs}", group = "multiplicative")]
pub struct Mul { /* ... */ }

#[k::syntax("{lhs} + {rhs}", group = "additive")]
pub struct Add { /* ... */ }

#[k::syntax("{lhs} - {rhs}", group = "additive")]
pub struct Sub { /* ... */ }

k::precedence! {
    multiplicative > additive > comparison > equality > boolean_and > boolean_or
}

k::associativity! {
    left: multiplicative, additive, comparison, equality, boolean_and, boolean_or;
}
```

These are item macros containing a KRS grammar, so `syn` accepts the file while
KRS can type-check group references. A deliberately named
`#[k::self_associative(left)]` can expose K's per-production form when needed;
plain `assoc = "left"` should not ambiguously mean both forms.

The macro syntax should also allow multiple unrelated precedence chains rather
than forcing a total numeric order.

## Tokens and lexical syntax

A token is a nominal domain sort, not a one-variant constructor:

```rust
#[k::token(regex = r"[a-zA-Z][a-zA-Z0-9_]*", prec = 2)]
pub struct Id(String);
```

KRS treats the field as an author/tooling representation and lowers the item to
a token sort/production, not to a K constructor wrapping `String`. Token sorts
cannot also declare constructors. Hooks and token-to-string conversions are
separate attributes/imported APIs.

Reusable lexical identifiers and unusual regex-terminal composition are
grammar-level rather than nominal:

```rust
k::grammar! {
    lexical Alphanum = r"[0-9a-zA-Z]";
}
```

Regexes remain Rust raw-string literals so whitespace and escaping survive
`rustfmt`.

## Brackets

K bracket productions normally do not create an AST node. Modeling parentheses
as `struct Parenthesized(Expr)` would falsely promise that the node survives
parsing. Provide a syntax-only form:

```rust
#[k::bracket("({value})")]
pub trait Expr: KItem {}
```

This creates a same-sort bracket production for `Expr`. Parametric brackets
that apply to every sort, and brackets with unusual constraints, use the
advanced grammar macro:

```rust
k::grammar! {
    bracket<S: k::Sort> S = "(" S ")";
}
```

The precise advanced grammar spelling remains an implementation detail, but it
must produce typed Definition IR rather than splice raw K text.

## Syntactic lists

Syntactic lists are grammar productions with element sort, delimiter, empty or
non-empty behavior, overload metadata, and generated symbols. A standalone
list that does not participate in subsorting can use a type alias:

```rust
#[k::list(
    element = dyn Expr,
    separator = ",",
    symbol = "expr_list",
    terminator_symbol = ".expr_list"
)]
pub type Exprs = k::List<Term<dyn Expr>>;
```

When the list name is itself an open K sort or participates in a subsort
diamond, it must be a sort trait rather than an alias. This is required by
KWasm's `EmptyStmts < Instrs/Defns < Stmts` hierarchy:

```rust
#[k::list(element = dyn Stmt, separator = "", overload = "listStmt")]
pub trait Stmts: KItem {}

#[k::list(element = dyn Instr, separator = "", overload = "listStmt")]
pub trait Instrs: Stmts {}
```

`#[k::non_empty_list]` or `non_empty = true` selects K's `NeList` form. An
`overload` field names the K overload group when several lists participate in
subsort-specific overload selection, as in KWasm. This is not inferred from
Rust's `Vec<T>` because an ordinary semantic list value and a syntactic list
have different parser behavior.

## Sort synonyms and parametric productions

Rust type aliases provide a clear sort-synonym spelling:

```rust
#[k::sort_synonym]
pub type Name = Id;
```

Normal generic structs/traits can represent many parametric K sorts and
productions. K's special same-sort polymorphic productions—rewrite, brackets,
matching-logic connectives—belong in the standard library or `k::grammar!`
rather than being rediscovered from unconstrained Rust generics.

## Parsing controls and pretty printing

The typed production attributes should cover commonly used K controls:

- `group`, `symbol`, `overload`, and `terminator_symbol`;
- `prefer`, `avoid`, `apply_priority`, `prec`, and `bracket`;
- visibility and deprecation; and
- macro/alias/function/strictness behavior when those apply to the symbol.

Pretty printing is related but separate from recognition. A syntax template can
generate a simple default format. Nontrivial line breaking, indentation, color,
or a print form different from the parse form uses `#[k::format("...")]` with
K's format mini-language validated by KRS.

Do not overload `#[k::syntax]` with undocumented whitespace conventions.

## Advanced grammar macro versus raw K

`k::grammar!` is a typed KRS island for source-level grammar concepts that do
not correspond to a Rust nominal item:

- lexical identifiers;
- standalone/group associativity and precedence;
- parametric and bracket productions;
- syntax-only overloads or injections; and
- future K grammar features before a polished Rust-native shorthand exists.

Its parser should lower to the same Definition IR nodes as attributes. It is
not a raw string passed through to `.k`.

A separate, conspicuous escape hatch may be provided:

```rust
k::raw_k! {
    /* literal source-level K sentence */
}
```

Raw K prevents full KRS type checking, formatting, symbol analysis, and source
mapping for that sentence. It should be warned on and forbidden in strict or
portable profiles.

## IMP and KWasm coverage

The hybrid directly covers the features found in the initial corpus:

| Corpus feature | KRS form |
|---|---|
| IMP literals/operators/statements | struct/variant syntax templates |
| IMP mixed precedence and associativity | named groups plus module macros |
| IMP parentheses | trait bracket attribute |
| IMP `Id` regex | token item |
| IMP dangling `else` preference | typed `avoid`/`prefer` production control |
| IMP formatting | default template or explicit format attribute |
| KWasm abstract syntax sorts | open sort traits |
| KWasm later extensions | separate structs/enums implementing those traits |
| KWasm overloaded empty/instruction/statement lists | attributed list aliases with overload groups |
| KWasm syntax-only helper productions | `k::grammar!` |

## Remaining implementation questions

These do not block the language shape:

1. Finalize the template escaping rules and whether terminal fragments may be
   adjacent to placeholders without separators.
2. Choose exact macro punctuation and build a formatter for macro interiors;
   `rustfmt` preserves token trees but does not understand their semantics.
3. Decide whether simple numeric precedence is offered as optional sugar. If
   so, it must lower to named groups and must not replace partial-order support.
4. Define the default prefix syntax/name mangling and stability policy.
5. Determine which K parsing attributes are portable across declared K pins;
   unknown typed attributes must fail rather than silently becoming raw.

None requires a Rust parser fork or changes the hybrid decision.
