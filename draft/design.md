# KRS design

This is the authoritative pre-implementation design for KRS. The investigation
reports record the evidence behind it; where an older sketch differs from this
document, this document wins.

The semantic shape described here is decided. Exact punctuation inside the
compiler-owned macro islands may be refined by the first implementation, but
that refinement must not change the distinctions or compatibility promises
below.

## Purpose and compatibility contract

KRS is a Rust-shaped language for authoring K definitions. It compiles to the
same source-level K constructs that an author could write in `.k` and then uses
the stock K frontend, execution backends, prover, and pyk ecosystem. It is not
a Rust-to-K translator, a replacement K backend, or a way to give arbitrary
Rust programs symbolic semantics.

“Works like Rust” has a precise boundary:

| Dimension | KRS promise |
|---|---|
| Lexing and outer parsing | KRS uses Rust 2024 tokens and item grammar. The authored definition is a genuine Cargo crate. |
| Names and modules | rustc resolves Rust paths, visibility, aliases, `mod`, `use`, and re-exports. KRS resolves the additional names bound inside K-only macro islands. |
| Nominal data | Structs and closed enums retain their familiar constructor and pattern shape. |
| Plain Rust items | An unmarked `fn`, `match`, enum, trait, or import keeps ordinary Rust semantics. |
| Relational items | K behavior is introduced only by conspicuous `k::` attributes, types, or macro islands. |
| rustc compatibility | Supported KRS source must pass `cargo check`. KRS procedural attributes consume relational forms such as refutable parameters before ordinary Rust checks and expand them to declarations and descriptors. |
| K compatibility | Accepted typed constructs must either lower faithfully for the selected K pin/backend or fail before K is invoked. |

KRS favors semantic honesty over surface purity. It does not make enums
reopenable, make rules ordered, represent undefinedness as `None`, make object
Boolean constraints host booleans, or pretend associative matching is Rust
collection destructuring.

The host architecture is:

```text
Cargo crate -> KRS proc macros -> rustc-valid declarations/descriptors
           -> host collector -> KRS semantic/relational IR
           -> KRS Definition IR -> k-rust and/or .k
```

“Genuine Rust” describes the source, package graph, path resolution, macro
expansion, and tooling host. It does not make Rust's trait solver the authority
for K subsorting or turn the generated descriptors into a concrete
implementation of the defined language. `cargo check` and `krs check` are
complementary: the former checks the Rust host; the latter checks the complete
K theory.

## Surface layers and ergonomic macros

The explicit notation in this document is a **reference surface**, not a claim
that every construct should always be written in its most expanded form. KRS
should keep three layers independent:

1. The semantic and Definition IRs state the actual K meaning and invariants.
2. The explicit KRS reference surface gives each concept a stable,
   Rust-shaped, mechanically understandable representation.
3. An ergonomic surface may provide Rust macro invocations which expand to
   explicit descriptors equivalent to the reference surface.

This separation lets KRS improve human readability without redefining rules,
binders, framing, logic, or sentence kinds. The reference form remains useful
for specifications, diagnostics, AI tools, macro documentation, and cases
where an author wants full control. It need not be the dominant spelling in a
large semantics.

An ergonomic macro is acceptable only if it has a transparent expansion
contract:

- its invocation remains valid Rust outer syntax;
- its expansion has exactly the same resolved semantic IR as the corresponding
  explicit form;
- it does not infer away distinctions such as transition versus equation,
  object `Bool` versus matching logic, or existential versus fresh binders;
- bindings, hygiene, generated item identities, and source spans are stable;
- diagnostics point to the invocation and can show the relevant expansion;
  and
- `krs expand` can display a deterministic reference-surface form.

Built-in KRS attributes and item macros are real procedural macros. The
`proc-macro` crate is only a facade: payload parsing and descriptor types live
in ordinary shared libraries used by the macros, analyzer, formatter,
`krs expand`, and KRS editor support. Macros never perform whole-definition K
analysis, so KRS does not acquire a second semantic frontend.

Source-span behavior is part of the macro contract. Each authored identifier
must map to one meaningful generated Rust use; repeated generated uses receive
call-site spans. Golden rust-analyzer navigation tests accompany expansion and
diagnostic tests.

The macro vocabulary is deliberately not fixed before the first complete
example language. A compact spelling which merely saves characters can hide
the feature an author most needs to notice. Conversely, a macro that groups a
repeated semantic pattern may make both the K intent and the Rust analogy much
clearer. Candidate macros therefore require corpus evidence rather than being
added from isolated snippets.

## Source and package model

KRS uses ordinary Rust source organization:

```rust
pub mod expr;
mod machine;

use k::builtin::int::{self, Int};
pub use expr::{Expr, Value};
```

- `mod` includes a source module in the crate ownership tree.
- `use` performs lexical name resolution only. Adding an unused `use` can
  never activate syntax, equations, or rules.
- `pub` and restricted visibility control the KRS API.
- Every included semantic item is part of the selected definition facet;
  privacy does not make a rule dormant.
- Dependencies make another package available, while definition/target
  composition explicitly selects its exported theory facet.

A KRS package is an ordinary Cargo package. Cargo owns the package graph,
features, source roots, and Rust dependencies. KRS definition facets and
targets live under namespaced Cargo metadata:

```toml
[package]
name = "imp-semantics"
version = "0.1.0"
edition = "2024"

[dependencies]
krs = "=0.1.0"

[package.metadata.krs]
k-namespace = "ORG-EXAMPLE-IMP"

[package.metadata.krs.toolchain]
k = "=7.1.337"

[lib]
path = "src/lib.rs"

[package.metadata.krs.definitions.imp]
root = "crate"
syntax-root = "crate::imp"

[package.metadata.krs.targets.llvm]
definition = "imp"
backend = "llvm"

[package.metadata.krs.targets.haskell]
definition = "imp"
backend = "haskell"
features = ["verification"]
```

`Cargo.lock` resolves the Rust package graph, including the KRS libraries and
`k-rust`. A supplemental `Krs.lock` records the exact K/pyk/backend toolchain,
builtin registry, raw K dependency hashes, and the compatibility unit tying
them to the resolved `k-rust` commit. It does not duplicate Cargo's dependency
solver. The reference K frontend, Rust frontend, and builtin pins must
describe the same K release. A final definition cannot contain two packages
with the same immutable K namespace. Raw `.k` dependencies are explicit FFI
packages with locked files and declared modules, not ambient include paths.

Backend selection uses Rust's cfg shell:

```rust
#[cfg(k_backend = "llvm")]
#[k::rule]
fn concrete_only(/* ... */) -> State { /* ... */ }
```

The initial backend values are `llvm` and `haskell`. Capability checks happen
before emission; a construct is never silently removed to make a target
compile.

## Sorts, terms, and constructors

`Term<S>` is a symbolic object-language term of K sort `S`, not a Rust value
which KRS evaluates. Open K sorts are marker traits:

```rust
#[k::sort]
pub trait KItem {}

#[k::sort]
pub trait KResult: KItem {}

#[k::sort]
pub trait Expr: KItem {}

#[k::sort]
pub trait Value: Expr + KResult {}
```

Trait supertraits and attributed constructor declarations add edges and
members to a compiler-owned subsort relation. The compiler computes one
path-independent transitive closure for the selected definition, including
diamonds. It does not generate Rust blanket impl chains whose result depends
on a path through the graph.

Attributed traits are Rust-resolved sort declarations, not runtime marker
bounds which every constructor literally implements. Constructor membership
is explicit descriptor data. This is necessary for real rustc compatibility:
blanket impls which try to derive every transitive membership conflict at
legal diamonds. Within one host build, descriptors use rustc-resolved type
keys to join paths; KRS immediately replaces those temporary keys with stable
package/module/item identities.

An extension can add a constructor without editing the sort declaration:

```rust
#[k::constructor(sort = Value, syntax = "{value}")]
pub struct IntValue {
    pub value: Int,
}
```

The rare after-the-fact edge between two already declared sorts is explicit:

```rust
k::subsort!(ExistingValue => KResult);
```

Closed constructor families use enums and retain closed-world exhaustiveness:

```rust
#[k::constructors(sort = Value)]
pub enum Boolean {
    #[k::syntax("true")]
    True,
    #[k::syntax("false")]
    False,
}
```

An open sort trait is never exhaustively matchable. KRS must diagnose attempts
to infer enum-style exhaustiveness for it. `From` remains a conversion and is
not used to encode sort membership.

Open or dynamic constructor patterns use `term![...]`. Ordinary Rust patterns
remain available when their nominal type is known.

## Object-language grammar

The grammar layer is hybrid. Nominal productions live on structs and enum
variants, while relationships between productions and non-nominal grammar
sentences use typed item macros.

```rust
#[k::constructor(
    sort = Expr,
    syntax = "{lhs} + {rhs}",
    group = "additive",
)]
#[k::seqstrict(sequence = [lhs, rhs])]
pub struct Add {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

k::precedence! {
    multiplicative > additive > comparison > equality
}

k::associativity! {
    left: multiplicative, additive;
}
```

Named fields become named nonterminals. A syntax template is a checked grammar
template, not a runtime format string. It normally mentions each field once.
Public program syntax should be explicit; an omitted template may receive a
stable prefix form only for internal constructors.

Precedence is a partial order over named production groups. Group
associativity is distinct from K's per-production associativity, exposed
separately as `#[k::self_associative(...)]`. KRS must not infer mixed-operator
associativity from repeated per-production attributes.

Other core forms are:

```rust
#[k::token(regex = r"[a-zA-Z][a-zA-Z0-9_]*", prec = 2)]
pub struct Id(String);

#[k::bracket("({value})")]
pub trait Expr: KItem {}

#[k::list(element = dyn Expr, separator = ",", symbol = "expr_list")]
pub type Exprs = k::List<Term<dyn Expr>>;
```

Tokens are domain sorts, not wrapper constructors. Brackets are syntax-only
and do not invent AST nodes. A standalone syntactic list may be a type alias;
a list name that participates in open subsorting or overload diamonds must be
an attributed sort trait.

`k::grammar!` represents typed lexical, parametric, bracket, injection,
overload, and other non-nominal grammar sentences. `#[k::format]` is distinct
from recognition grammar. `k::raw_k!` is a warned, non-portable escape hatch
which loses some KRS checking and is forbidden by strict profiles.

`pub` and public program grammar are independent. A target's `syntax-root`
chooses externally parseable productions; `#[k::internal]` keeps an
administrative production out of that grammar without removing it from the
term signature.

## Configurations and framing

Fixed configuration trees use nested structs and nominal cell wrappers:

```text
Cell<T>          exactly one leaf cell
KCell<KSequence> standard computation-cell specialization
OptionalCell<T>  zero or one cell
SetCells<T>      zero or more AC-idempotent cells
ListCells<T>     zero or more ordered cells
MapCells<K, T>   zero or more AC cells indexed by a key child
```

```rust
#[k::cell]
pub struct Frame {
    pub locals: Cell<Map>,
}

#[k::configuration(root = "machine")]
pub struct Machine {
    pub k: KCell<KSequence>,
    pub env: Cell<Map>,
    pub frame: Frame,
}
```

Field identifiers are cell names exactly as written unless overridden with
`#[k::cell(name = "...")]`; KRS performs no implicit case conversion.

Initialization is a restricted declarative associated function:

```rust
impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] program: Term<dyn KItem>,
    ) -> Self {
        Self {
            k: KCell::new(k![program]),
            env: Cell::new(Map::empty()),
            frame: Frame { locals: Cell::new(Map::empty()) },
        }
    }
}
```

For rule matching, `cells!` is the canonical path-independent form:

```rust
#[k::rule]
fn assign(
    name: Term<Id>,
    value: Term<dyn Value>,
    env: Term<Map>,
    cells! {
        k: KCell(Assign(name, value), tail @ ..),
        env: Cell(env),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: KCell(..tail),
        env: Cell(map![env[name <- value]]),
        ..state
    }
}
```

Every object-term binding has an ordinary `Term<Sort>` Rust parameter before
the final configuration subject. K-sequence, map, and configuration frames are
introduced structurally inside `cells!` because their sorts follow from their
positions. The parameter order must match the first occurrence of term
bindings in the subject; this keeps sorts explicit after generic authoring
types such as `Map<K, V>` are erased to K's unparameterized `Map` sort.

KRS resolves cell identities, inserts omitted ancestors, frames omitted
siblings and generated cells, and normalizes all changes as one simultaneous
pre/post rewrite. `..state` is a symbolic configuration frame, not Rust struct
update execution. Direct nested record patterns remain useful when coupling to
the current tree shape is intentional.

Collection cells and fragments use explicit `cell_set!`, `cell_list!`,
`cell_map!`, and `fragment!` islands. Their matching can be associative,
commutative, nondeterministic, or indexed; none inherits Rust collection or
ownership semantics. Generated top and counter cells remain compiler-internal.

## Patterns and rules

One K transition rule is one independently named refutable function clause:

```rust
#[k::rule]
#[k::requires(int::ne(denominator, 0))]
fn divide(
    term![Div(numerator, denominator)]: Term<dyn Expr>,
) -> Term<dyn Expr> {
    term![IntValue(int::div(numerator, denominator))]
}
```

The function is a declaration, not callable Rust. Its argument pattern is the
pre-pattern and its single restricted result expression is the post-term.
Rules at one priority are independent alternatives; source order is not part
of their semantics. Multi-arm `match` is therefore rejected in rule bodies.

Normalized meaning is:

```text
forall U.
  (Pre(U) and Requires(U))
    rewrites-to
  exists E. (Post(U, E) and Ensures(U, E))
```

Patterns use Rust constructors, records, `_`, `binding @ pattern`, and
or-patterns when those meanings transfer. Compiler-owned islands cover the
relational structures Rust lacks:

```rust
fn pattern_examples() {
    let k![head, tail @ ..] = k_subject;
    let list![head, rest @ ..] = list_subject;
    let set![element, rest @ ..] = set_subject;
    let map![key => value, rest @ ..] = map_subject;
}
```

`requires` and `ensures` contain object-language `Term<Bool>` values. They are
not Rust guards or matching-logic patterns. Priority and fallback are explicit
`#[k::priority(...)]` and `#[k::owise]`; no ordering is inferred from files or
function names.

All RHS-only names require an explicit binder:

- `#[k::exists(x: S)]` introduces a symbolic witness;
- `#[k::fresh(x: S)]` invokes K's runtime freshness mechanism;
- `#[k::forall(x: S)]` exposes K's unbound universal behavior; and
- `#[k::set_vars(x: S)]` declares a possibly partial or multi-valued ML set
  variable.

These are distinct in the IR and have target-specific capability checks.

## Object Booleans and matching logic

KRS keeps three categories separate:

1. `Term<S>` is an object term.
2. `Term<Bool>` is an object Boolean term used by `requires` and `ensures`.
3. `MlPattern` is a matching-logic pattern.

Canonical Boolean operations are explicit builtin term constructors:

```rust
#[k::requires(k::and_bool![
    int::le(0, index),
    int::lt(index, list::size(values)),
])]
#[k::rule]
fn checked(term![At(values, index)]: Term<dyn Expr>) -> Term<dyn Expr> {
    term![values]
}
```

V1 does not reinterpret Rust `<`, `+`, `&&`, or arbitrary operator traits as K
operations. Matching logic uses a closed typed island:

```rust
fn logic_examples() {
    let _ = ml![bottom::<Int>()];
    let _ = ml![and(ceil(value), holds(int::gt(value, 0)))];
    let _ = ml![exists(x: Int, equals(result, x))];
}
```

Its core includes top, bottom, conjunction, disjunction, negation,
implication, equivalence, ML equality, ceil/floor, object-Boolean embedding,
and quantifiers. Bottom is an explicit IR node. It is never inferred from
`Option::None`, failed host control flow, or a Boolean `false` term.

## Functions, equations, simplification, and claims

K function symbols are productions with declared functionality:

```rust
#[k::function(partial, sort = Value)]
pub struct Lookup(pub Map, pub Key);

#[k::equation]
fn lookup_hit(
    term![Lookup(map![key => value, _rest @ ..], key)]: Term<dyn Value>,
) -> Term<dyn Value> {
    term![value]
}
```

`partial` means at most one result; an undefined application denotes bottom.
`total` additionally asserts existence. One equation is one independent
clause rooted at the declared function. Equations may have explicit priority
or `owise`; they are not ordered Rust match arms.

A function may read the current configuration only through an explicit
read-only effect:

```rust
#[k::function(total, reads = Machine, sort = Bool)]
pub struct AccountExists(pub Account);

#[k::equation]
fn account_exists(
    term![AccountExists(account)]: Term<Bool>,
    k::Global(cells! { accounts: cell_set![AccountCell(account), _rest @ ..] }):
        k::Global<Machine>,
) -> Term<Bool> {
    term![true]
}
```

The global pattern is not an object argument and cannot be updated or
constructed on the RHS. The compiler records and propagates the hidden global
configuration dependency which K generates.

Simplification clauses are a separate sentence kind:

```rust
#[k::simplification(priority = 40)]
fn add_zero(term![int::add(value, 0)]: Term<Int>) -> Term<Int> {
    term![value]
}
```

Their integer is a simplifier hint, not transition priority. KRS does not claim
to prove simplifier soundness, termination, function coverage, or confluence;
it diagnoses invalid combinations and obvious cycles where practical.

Claims use the same pre/post shape but never enter execution:

```rust
#[k::claim(all_paths)]
fn safety(pre: Machine) -> Machine { post }
```

Every claim explicitly selects `all_paths` or `one_path`. Trusted claims remain
visibly marked and warn in proof-oriented builds.

## Evaluation and static forms

Common evaluation strategy is metadata on a nominal production:

```rust
#[k::seqstrict(sequence = [lhs, rhs])]
#[k::result(Value)]
#[k::hybrid]
pub struct Add { /* fields */ }
```

Fields replace K's fragile one-based positions. `strict` permits selected
positions independently; `seqstrict` requires earlier positions in the listed
sequence to satisfy the chosen result predicate. The default result sort is
the open `KResult`. Named `using = alias` groups select reusable context-alias
templates. Heating sort `K`, unknown fields/results, and `hybrid` without a
strictness declaration are rejected.

An explicit context is a zero-return refutable declaration with one named
hole:

```rust
#[k::context(hole = operand)]
#[k::requires(is_assignable(operand))]
fn assignment_target(
    cells! { k: KCell(k![Assign(operand, _), _tail @ ..]) }: Machine,
) {}
```

It has no post-state. `#[k::heat_as(...)]` explicitly represents the unusual
case where the hole is transformed for heating. A context alias has the same
shape with `#[k::context_alias(name = execute, here = site)]`; several
declarations may intentionally share the alias name.

K syntactic macros and aliases are static clauses, spelled to avoid confusion
with Rust macros or runtime transitions:

```rust
#[k::desugar]
fn add_empty_else(term![IfWithoutElse(c, t)]: Term<Statement>)
    -> Term<Statement>
{
    term![IfElse(c, t, EmptyBlock)]
}

#[k::alias]
fn pretty_empty(term![PrettyEmpty]: Term<Statement>) -> Term<Statement> {
    term![VerboseEmptyBlock]
}
```

The root production and clause carry the same static mode. Recursive variants
are explicit. Desugaring acts before execution; an alias additionally reverses
for final unparsing. Neither is a runtime equation.

`#[k::anywhere]` uses the clause shape but is a separate IR kind which may act
at any term occurrence. With K 7.1.337 it is an LLVM-only capability: Haskell
rejects it, and K's hidden override unsoundly strips the rule. KRS therefore
rejects `anywhere` in Haskell and portable targets.

Anonymous K `#fun` uses a recognized term combinator:

```rust
fn anonymous<S, T>(argument: Term<S>) -> Term<T> {
    k::fun(argument, |pattern: Term<S>| term![result])
}
```

This lowers to a generated one-clause K function with lexical captures. It is
not an executed or first-class Rust closure and cannot contain host effects,
multiple clauses, or side conditions.

## Builtins, hooks, and raw access

`k` is a reserved, compiler-provided sysroot crate generated and tested for
the exact K pin:

```rust
use k::builtin::int::{self, Int};
use k::builtin::map::{self, Map};
```

Its entries carry their defining K module, exact symbol/hook, signature,
attributes, backend capabilities, and K-version range. Imports only bind
names; lowering adds the minimal K builtin modules actually referenced by the
selected grammar and semantics. Builtin operations build terms and do not run
during KRS compilation.

Known hooks use checked `#[k::hook("DOMAIN.name")]`. Unknown hooks and future
attributes require conspicuous raw attributes, warn normally, and fail strict
or portable profiles. KRS never claims an implementation exists merely
because an author wrote a hook string.

## Compiler and lowering architecture

KRS owns a source-level, frontend-neutral K Definition IR. It has one native
frontend adapter and one standard source emitter:

```text
KRS Rust-compatible CST
  -> resolved KRS semantic/relational IR
  -> target-neutral K Definition IR
       |-> structured k-rust Definition -> Rust frontend passes -> KORE
       `-> deterministic .k source artifact
             `-> any compatible K frontend -> KORE
  -> existing LLVM/Haskell backends and pyk
```

The `k-rust` adapter targets its structured source `Definition`, `Sentence`,
and `Term` model, not its outer source AST, KAST JSON, or KORE AST. This lets
KRS skip reparsing generated syntax and rule bubbles while reusing its
configuration expansion, checking, strictness/freezer, macro, freshness,
projection, sort-injection, and KORE-lowering passes. It may become the default
frontend after the full IMP equivalence gate.

The `.k` emitter remains supported as a readable expansion, ecosystem
boundary, and differential oracle. It does not target Java: the current Java
frontend, `k-rust`'s outer frontend, or another compatible implementation can
consume the same artifact. KRS does not generate KORE itself on the native
path. Its Definition IR must not be replaced by `k-rust` types: it also carries
stable Rust paths, typed KRS semantics, macro provenance, target-neutral
capability information, and mappings needed to compare native lowering with
the emitted source meaning.

`k-rust` is currently a v0.x dependency. `Krs.lock` pins its exact commit and K
builtin revision. If the native frontend does not support a construct, native
`krs build` fails with a capability diagnostic while `krs emit-k` may still
produce the standard source artifact. It does not silently invoke a different
frontend or change the theory.

Build targets select semantic backends such as LLVM or Haskell, not frontend
implementations. Differential frontend execution belongs to compiler CI and
commands such as `krs check --differential`; the currently pinned Java
implementation is a reference oracle there, not part of the KRS source or
target model.

Generated output is organized by logical roles, normally:

```text
<NS>-<DEF>-SYNTAX
<NS>-<DEF>-SIGNATURE
<NS>-<DEF>-SHARED
<NS>-<DEF>-CONCRETE
<NS>-<DEF>-SYMBOLIC
<NS>-<DEF>              facade/main module
```

This partition is compiler-owned. Rust files and `use` edges do not map
one-to-one to K files or imports. The compiler aggregates a selected facet,
computes its closure, and emits an acyclic `requires`/import graph. The facade
publicly exposes selected program syntax and privately composes the theory.

Stable K symbols and rule labels derive from the immutable package K namespace
plus canonical Rust item path, never source lines, aliases, package version, or
generated module partition. A sidecar maps emitted names and ranges back to
KRS spans and macro-expansion origins on both routes. `k-rust` sentence
locations and term metadata improve native diagnostics but do not replace this
map. Outer-KAST JSON is not a preferred adapter: its v4 schema cannot represent
all source sentences such as context aliases.

The manifest also generates kdist/pyk integration. `krs build` and the kdist
bridge must use the same target descriptor and produce equivalent artifacts.

## Validation and equivalence

Correctness is established with a layered differential oracle against a
hand-written K baseline at the same K pin:

1. exact KRS CST, resolved IR, relational normalization, symbols, emitted `.k`,
   and source-map goldens;
2. exact normalized `k-rust` Definition adapter snapshots and comparison with
   that frontend parsing generated `.k`;
3. normalized Java `parsed.json` comparison;
4. structural KORE comparison between hand-written K, generated `.k` processed
   by the pinned reference toolchain, and the native adapter;
5. accepted/rejected object-language parse corpora and unparse round trips;
6. concrete execution traces and bounded-search result sets; and
7. symbolic proof status and normalized terminal/frontier constraints.

Raw textual Kore, exact KCFG shapes, enumeration order, solver timing, and
backend-generated identifiers are not stable public goldens.

Milestone one is a complete modern IMP port with equivalent grammar,
execution, search, and proof behavior. Later gates add KWasm-shaped open-sort
and overload stress tests and KMIR/KEVM-shaped configurations, collections,
global functions, and lemmas.

## Explicit Rust deviations

These deviations are part of the language contract and must be prominent in
documentation and diagnostics:

- attributed refutable functions are declarative clauses, not callable Rust;
- clause source order has no semantic effect except explicit K priority;
- rule/equation bodies are restricted terms, not arbitrary Rust execution;
- `Term<S>` values are symbolic object terms, including `Term<Bool>`;
- attributed sort traits declare a K subsort relation; constructor membership
  is descriptor data rather than literal Rust trait implementation, and open
  sorts are never exhaustive;
- `cells!` frames configuration structure rather than performing ownership or
  record update;
- sequence and associative collection macros use relational matching;
- partial K functions denote bottom, never `Option::None`;
- `ml!` logic is distinct from object Booleans;
- strictness describes the object language's evaluator, not Rust evaluation;
- `k::fun` is a generated K function, not a first-class host closure; and
- global function context is an explicit read effect despite not appearing as
  an object-language argument.

## What remains before freezing a v1 specification

No unresolved conceptual investigation blocks implementation. The remaining
work is a bounded validation program, ordered with explicit exit gates in the
[implementation plan](implementation-plan.md):

1. harden the shared syntax/IR libraries, proc-macro facade, deterministic host
   collector, and Definition IR, then port IMP end-to-end;
2. freeze macro punctuation using real parser/type-checker prototypes,
   especially `cells!`, `fragment!`, and collection patterns;
3. verify initializer closure and cell-fragment edge cases against the pinned
   frontend;
4. compile generated module visibility and facet composition fixtures on LLVM
   and Haskell;
5. generate and exhaustively probe the first pinned builtin registry;
6. verify stable symbols, diagnostic source mapping, raw K dependencies, and
   identical `krs build`/kdist artifacts; and
7. run the complete layered IMP equivalence gate before expanding the surface;
8. qualify macro span behavior with expansion, diagnostic, and rust-analyzer
   navigation goldens; and
9. qualify the native `k-rust` Definition adapter against generated `.k` and
   the pinned reference implementation, and contribute or wrap an
   invariant-preserving structured-Definition entry API.

After the explicit IMP port is stable, run the macro ergonomics study in the
validation queue. It may select a small built-in convenience layer for v1, but
the explicit reference surface and IR remain valid regardless of that result.

These tests may refine spelling, diagnostics, or emitter organization. A
failure which would require collapsing one of the semantic distinctions in
this document is a design issue and must be brought back as an explicit
decision rather than patched around.
