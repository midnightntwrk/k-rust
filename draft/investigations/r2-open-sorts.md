# R2: Open-sort representation

## Decision

Adopt **marker traits for open K sorts**, ordinary structs for individual
productions, and enums only for constructor families that the author intends
to keep closed.

```rust
#[k::sort]
pub trait Stmt: KItem {}

#[k::sort]
pub trait Instr: Stmt {}

#[k::sort]
pub trait PlainInstr: Instr {}

#[k::syntax("{ty}.const {value}", symbol = "aIConst")]
pub struct IConst {
    pub ty: IValType,
    pub value: WasmInt,
}

impl PlainInstr for IConst {}
```

The important contract is:

- a `#[k::sort] trait` denotes an open set of terms;
- its supertraits denote immediate subsort edges, with the child on the left
  (`PlainInstr < Instr < Stmt` above);
- `impl Sort for Constructor` puts a nominal production in that result sort;
- the KRS compiler computes subsort membership as a relation, not as a chain of
  runtime Rust trait-object conversions; and
- a term of an open sort has the standard spelling `Term<dyn Sort>` when a
  sized Rust type is required.

This is the best match for both K's modularity and a Rust reader's expectations.
Traits advertise an open world and enums advertise a closed one. Reopenable
enums would make the shortest toy example but would break exactly the Rust
intuition KRS is intended to preserve.

Two refinements to the current design sketch are required:

1. **Subsort closure is path-independent.** Multiple paths in a subsort diamond
   establish one membership fact; they do not generate overlapping impls or
   nested source-level conversions.
2. **Overloaded syntactic-list names are sorts, not mere type aliases.** The
   KWasm hierarchy needs `Instrs`, `Defns`, `Stmts`, and `EmptyStmts` to
   participate independently in subsorting. An attributed sort trait can also
   carry the list production.

The implementation may use one erased term node internally, but that is an IR
choice beneath the typed trait surface. It should not become the author-facing
type system.

For lowering purposes, distinguish a production struct from an attributed
closed-family enum. A `#[k::syntax] struct Br` is one production whose result
sort is supplied by its one sort impl; it should not create an artificial
singleton K sort named `Br`. A `#[k::constructors] enum WasmValue`, by contrast,
deliberately declares a closed KRS/K sort: its variants return `WasmValue`, and
`impl KResult for WasmValue` is a subsort edge. This retains R4's useful enum
model without adding an injection layer for every ordinary production.

## The KWasm stress case

The representative hierarchy is spread across `wasm.md` and `wasm-text.md`.
The common module declares:

```text
PlainInstr < Instr < Stmt
EmptyStmt  < Instr < Stmt
EmptyStmt  < Defn  < Stmt

EmptyStmts < Instrs < Stmts
EmptyStmts < Defns  < Stmts
```

It then adds many `PlainInstr` productions. The text-format module imports that
module and adds more plain instructions, block and folded instruction families,
all of the previously abstract definition families, and `ModuleDecl < Stmt`.
The semantics module later adds administrative `Instr` and `HelperInstr`
productions. Test and auxiliary modules extend `PlainInstr` and `Stmt` again.

This is not just a large enum split over several files. There are two genuine
diamonds:

```text
                 Stmt                         Stmts
                /    \                       /     \
             Instr   Defn                 Instrs  Defns
                \    /                       \     /
              EmptyStmt                   EmptyStmts
```

The empty-list diamond matters to parsing: all four list productions share an
`overload(listStmt)` group, and the least empty-list sort lets the parser choose
the most specific overloaded production. Consequently, list representation and
open-sort representation cannot be designed independently.

## Recommended KWasm-shaped encoding

The following is a structural port rather than a complete production-by-
production transcription. It includes the recursive and modular cases that
distinguish the candidates.

```rust
// wasm-common.rs

#[k::sort]
pub trait KItem {}

#[k::sort]
pub trait Stmt: KItem {}

#[k::sort]
pub trait Instr: Stmt {}

#[k::sort]
pub trait Defn: Stmt {}

#[k::sort]
pub trait PlainInstr: Instr {}

// This declaration is intentionally a diamond.
#[k::sort]
pub trait EmptyStmt: Instr + Defn {}

#[k::list(
    element = dyn Stmt,
    separator = "",
    overload = "listStmt"
)]
pub trait Stmts: KItem {}

#[k::list(
    element = dyn Instr,
    separator = "",
    overload = "listStmt"
)]
pub trait Instrs: Stmts {}

#[k::list(
    element = dyn Defn,
    separator = "",
    overload = "listStmt"
)]
pub trait Defns: Stmts {}

#[k::list(
    element = dyn EmptyStmt,
    separator = "",
    overload = "listStmt",
    terminator_symbol = ".List{\"listStmt\"}"
)]
pub trait EmptyStmts: Instrs + Defns {}

#[k::syntax("{ty}.const {value}", symbol = "aIConst")]
pub struct IConst {
    pub ty: IValType,
    pub value: WasmInt,
}

impl PlainInstr for IConst {}

#[k::syntax("drop", symbol = "aDrop")]
pub struct Drop;

impl PlainInstr for Drop {}

// wasm-text.rs imports wasm-common.rs and extends its open sorts.

#[k::syntax("br {target}")]
pub struct Br {
    pub target: Index,
}

impl PlainInstr for Br {}

#[k::syntax("block {id} {ty} {body} end {end_id}")]
pub struct BlockInstr {
    pub id: OptionalId,
    pub ty: TypeDecls,
    pub body: Term<dyn Instrs>,
    pub end_id: OptionalId,
}

impl Instr for BlockInstr {}

#[k::syntax("({instruction} {operands})")]
pub struct FoldedInstr {
    pub instruction: Term<dyn PlainInstr>,
    pub operands: Term<dyn Instrs>,
}

impl Instr for FoldedInstr {}

#[k::syntax("(module {id} {definitions})")]
pub struct ModuleDecl {
    pub id: OptionalId,
    pub definitions: Term<dyn Defns>,
}

impl Stmt for ModuleDecl {}

// A later test module can extend the imported category without editing it.

#[k::syntax("ref {value}")]
pub struct TestRef {
    pub value: Int,
}

impl PlainInstr for TestRef {}
```

`BlockInstr` and `FoldedInstr` demonstrate the recursive case. `Term` supplies
the indirection required for a finite Rust representation; the sort parameter
retains the static K sort:

```rust
pub struct Term<S: ?Sized> {
    node: Arc<TermNode>,
    marker: PhantomData<fn(&S)>,
}

struct TermNode {
    symbol: SymbolId,
    children: Vec<Term<dyn KItem>>,
}
```

This is schematic library implementation, not a promise that KRS executes
terms as heap-allocated Rust trait objects. In particular, there is no vtable
dispatch in the lowered definition. `dyn` truthfully says that a field accepts
any term implementing the open sort, while `Term` says that the value is a
symbolic K term rather than an owned instance of one concrete Rust struct.

Construction can use ordinary constructor syntax under an expected sort or a
small `term![...]` macro. Destructuring an open term necessarily crosses a
dynamic boundary and should be explicit:

```rust
#[k::rule]
fn enter_block(
    term![BlockInstr { body, .. }]: Term<dyn Instr>,
) -> Term<dyn Instr> {
    term![SequenceInstrs(body)]
}
```

Rust cannot structurally match a `dyn Trait`, so promising a native enum-style
pattern here would be false. The pattern macro should still reuse Rust record,
tuple, `@`, `|`, `_`, and `..` syntax internally. Rules are refutable clauses,
so open-sort non-exhaustiveness is not a burden in the common rule surface.

## Subsort and membership semantics

### Relation, not generated Rust impl paths

Let `direct_subsort` contain every supertrait edge. KRS computes its reflexive,
transitive closure after resolving the effective module import graph:

```text
member(constructor, super_sort) :=
    exists principal_sort.
        produces(constructor, principal_sort)
        and principal_sort <= super_sort
```

For `EmptyStmt`, the two paths to `Stmt` produce one pair
`(EmptyStmt, Stmt)`. The compiler must not generate two competing conversions
or regard the paths as distinct evidence.

Ordinary Rust already gives the right logical reading to `trait Child: Parent`:
every `Child` is a `Parent`. The small deviation is implementation mechanics:
Rust normally requires an implementor of `Child` to satisfy all supertrait
obligations explicitly. KRS accepts the leaf declaration and closes membership
itself. A future companion crate or IDE facade may synthesize those repetitive
Rust impls, but they are not part of KRS source semantics.

In particular, do not implement closure with one Rust blanket impl per edge:

```rust
impl<T: Instr + ?Sized> Stmt for T {}
impl<T: Defn + ?Sized> Stmt for T {} // overlaps for EmptyStmt implementors
```

Rust coherence conservatively rejects these potentially overlapping impls.
Treating the graph as a set-valued compiler relation makes the intended diamond
both legal and unambiguous.

The type checker should enforce these initial coherence rules:

- sort traits are marker-only in the MVP: no methods, associated types,
  associated constants, negative impls, or specialization;
- the direct subsort graph is acyclic;
- duplicate direct edges and duplicate constructor memberships are diagnosed;
- diamonds are legal and idempotent;
- an individual production has one principal result sort, unless an explicit
  K overload declaration gives it several checked signatures; and
- enum exhaustiveness applies only to the enum's own closed constructor family,
  never to an open trait that the enum implements.

The one-principal-sort rule avoids silently interpreting this as two unrelated
K productions with the same symbol:

```rust
impl Instr for SomeConstructor {}
impl Defn for SomeConstructor {} // error unless explicitly modeled as overload
```

If a family genuinely belongs below two sorts, declare the diamond as a sort
and put the constructors at its least point:

```rust
#[k::sort]
trait EmptyStmt: Instr + Defn {}

impl EmptyStmt for EmptyConstructor {}
```

### Extension after declaration

The important KResult-style operation remains ordinary-looking:

```rust
// Declared in a builtin module.
#[k::sort]
pub trait KResult: KItem {}

// Declared in a language module later.
pub enum WasmValue {
    I32(Int),
    I64(Int),
}

impl KResult for WasmValue {}
```

A later module can likewise add a new constructor to an imported sort because
the constructor is local and the marker trait is open. This aligns with Rust's
usual orphan intuition: a local type may implement a visible foreign trait.

K can also add a subsort edge between two already-declared, already-imported
sorts. A supertrait header cannot express that after the child trait has been
declared. Do not distort ordinary `impl` to hide this uncommon operation.
Provide a visibly relational item:

```rust
k::subsort!(ExistingValue => KResult);
```

It lowers exactly to `syntax KResult ::= ExistingValue` and is checked against
the same sort graph. This macro is also the honest escape from Rust's orphan
and coherence rules when both endpoints come from dependencies. Most modular
extensions—including the KWasm text module—do not need it, because they add a
local production or local child sort to an existing open parent.

## Candidate comparison

### 1. Marker traits (recommended)

```rust
trait Instr: Stmt {}
trait PlainInstr: Instr {}

struct Br(Index);
impl PlainInstr for Br {}

struct Block(Term<dyn Instrs>);
impl Instr for Block {}
```

Strengths:

- openness, supertype bounds, and downstream implementations are familiar;
- adding a production does not edit a central declaration;
- multiple inheritance states KWasm's diamonds directly;
- recursive fields retain their expected sort with `Term<dyn Sort>`;
- enums remain available where exhaustiveness is actually valid; and
- each sort/production/edge has a direct lowering to K Definition IR.

Costs:

- dynamic open-term patterns need `term![...]`;
- `dyn` and `Term` are noisier than a bare enum field;
- KRS closes leaf membership rather than requiring Rust's repetitive
  supertrait impls; and
- a rare after-the-fact edge between existing traits needs `k::subsort!`.

These costs are visible and local. None teaches the wrong open/closed-world
model.

### 2. Hypothetical reopenable enums

```rust
#[k::open]
enum Instr {
    Plain(PlainInstr),
    Empty(EmptyStmt),
}

extend enum Instr {
    Block(BlockInstr),
    Folded(FoldedInstr),
}
```

This gives pleasant constructor syntax and native-looking patterns, but only by
changing a central Rust guarantee. It also fails under the KWasm diamonds. An
`EmptyStmt` would need wrapper variants along both `Instr` and `Defn` paths;
then `Stmt` either contains two representations of the same least-sort term or
the compiler must invent implicit injections and canonicalization.

Exhaustiveness has no coherent modular meaning. If a match is exhaustive before
an imported module adds `Block`, it becomes non-exhaustive afterward. Requiring
`_` on every open enum match makes it behave like `#[non_exhaustive]` forever
and removes its main advantage. Dependency compilation and public API hashing
would also depend on downstream variants, reversing Rust's crate model.

Recursive variants need `Box` or another wrapper anyway:

```rust
enum Instr {
    Block { body: Box<Instrs> },
    // downstream variants still unknown
}
```

This candidate is concise only when the world is already closed. In that case
an ordinary KRS enum should be used without reopening.

### 3. `From`/conversion-based wrappers

```rust
struct Instr(TermNode);
struct PlainInstr(TermNode);
struct Stmt(TermNode);

impl From<PlainInstr> for Instr { /* ... */ }
impl From<Instr> for Stmt { /* ... */ }
impl From<Defn> for Stmt { /* ... */ }
```

`From` describes how to construct a value, not the proposition that all terms
of one sort inhabit another sort. That mismatch becomes observable in a
diamond:

```text
EmptyStmt -> Instr -> Stmt
EmptyStmt -> Defn  -> Stmt
```

There are now two conversion chains to choose, potentially two nested wrapper
representations, and ambiguous `.into()` inference. Authors would also need
`.into()` at construction sites even though K subsorting normally inserts
injections according to expected sorts.

Generated `From<Term<dyn Child>> for Term<dyn Parent>` implementations can be a
useful Rust API for external tooling. They should be derived from the subsort
graph and canonicalized; they should not define that graph or appear throughout
KRS semantics source.

### 4. One untyped universal term wrapper

```rust
struct Term {
    sort: SortId,
    symbol: SymbolId,
    children: Vec<Term>,
}

let block = Term::apply("BlockInstr", vec![body]);
```

This handles recursion, extension, and diamonds effortlessly. It also discards
nearly all of the benefit of choosing Rust as the metalanguage. Wrong field
sorts, wrong rule subject sorts, and invalid helper signatures become dynamic
compiler checks; editor completion sees only `Term`; every pattern needs a
macro or symbol comparison; and an AI reader cannot infer signatures from
Rust types.

This is a good representation for the compiler's canonical term IR. A typed
facade such as `Term<dyn Instr>` is essentially the recommended trait design
laid over that IR.

### 5. Sort marker types plus a generic `Subsort` trait

This is the strongest alternative not in the original three-way comparison:

```rust
#[k::sort]
pub struct Instr;

#[k::sort]
pub struct PlainInstr;

impl k::Subsort<Instr> for PlainInstr {}

#[k::production(result = PlainInstr)]
pub struct Br(Index);

type InstrTerm = Term<Instr>;
```

It removes `dyn`, makes every relation an explicit impl, and works well with a
phantom-typed universal term. It does not, however, preserve the most useful
Rust intuition: `Instr` looks like an instantiable zero-sized data type rather
than an open interface, and constructor membership needs a second generic
protocol or an attribute. The direction of `Subsort<Instr> for PlainInstr` is
less immediately legible than `trait PlainInstr: Instr`.

Nor does it buy ordinary rustc checking. Generic transitive closure is not
expressible with a straightforward coherent blanket impl, diamonds still make
overlap relevant, and K's later old-sort-to-old-sort edges can violate orphan
rules. KRS still needs its own relation solver. The only material win is shorter
`Term<Instr>` spelling, which is not enough to outweigh the weaker authoring
model. Revisit this only if real ports show `dyn` dominating source or if a
rustc-type-checkable companion API becomes a primary requirement.

## Exhaustiveness policy

Open traits and closed enums must retain different diagnostics.

```rust
#[k::constructors]
enum Mutability {
    Const,
    Var,
}

fn spelling(value: Mutability) -> String {
    match value {
        Mutability::Const => "const",
        Mutability::Var => "var",
    }
}
```

This match may be exhaustively checked because downstream modules cannot add an
enum variant. In contrast, a match over `Term<dyn Instr>` is never declaration-
exhaustive. The compiler may know every currently imported constructor, but a
new importing module can extend the sort. It should therefore:

- allow refutable `#[k::rule]` clauses without a catch-all;
- require an explicit fallback/`owise` clause when a total function consumes an
  open sort, unless totality is established by a stronger checker;
- never infer permanent exhaustiveness from the currently loaded constructor
  registry; and
- report known-world coverage as an optional lint, not a semantic guarantee.

This is the same mental split Rust teaches between matching an enum and working
through a trait interface.

## Parser, type-checker, and lowering consequences

No Rust grammar extension is needed. `trait`, supertraits, `impl`, structs,
enums, `dyn`, and generic `Term<...>` types all parse through the R1 Rust shell.
The list metadata and dynamic term patterns remain typed attribute/macro
islands.

Name resolution and type checking should run in deliberate passes:

1. resolve the effective KRS module/import graph;
2. collect sort traits and nominal constructors without depending on item
   order;
3. collect direct subsort edges, list productions, and constructor result
   memberships;
4. reject cycles and incoherent production signatures, then compute closure;
5. type-check production fields, rules, functions, overload groups, and list
   relations against the closed graph; and
6. lower to K Definition IR while retaining direct-edge versus inferred-edge
   provenance for diagnostics.

The principal lowering is direct:

| KRS item | K definition concept |
|---|---|
| `#[k::sort] trait Instr` | sort declaration `syntax Instr` |
| `trait PlainInstr: Instr` | subsort production `syntax Instr ::= PlainInstr` |
| `impl PlainInstr for Br` plus syntax metadata | production returning `PlainInstr` |
| list-attributed sort trait `Instrs` | `List{Instr, ""}` production returning `Instrs` |
| `trait EmptyStmts: Instrs + Defns` | two subsort productions |
| `Term<dyn Instr>` | a term expected/inferred at sort `Instr` |
| `k::subsort!(A => B)` | later subsort production `syntax B ::= A` |

The emitted K should contain the declared direct subsort edges, not every pair
in the transitive closure. The closure is for KRS checking and coercion; K's
frontend retains responsibility for its normal injections, parser ordering,
and overload processing.

## Declaration-size comparison

For the nine-sort KWasm statement/list slice and its nine direct subsort edges:

| Candidate | Sort/edge shape | Per new production | Pattern behavior | Modular result |
|---|---|---|---|---|
| Marker traits | 9 traits; edges mostly in supertrait lists | struct + one `impl` | `term!` at open boundary; native inner Rust patterns | Preserves extension and both diamonds |
| Reopenable enums | central nested enums plus implicit/explicit injection variants | new downstream variant | attractive until mandatory wildcard | Breaks Rust closure and diamond identity |
| Conversion wrappers | wrapper per sort + conversion per edge/path | constructor + conversion plumbing | wrapper destructuring or macro | Open, but path-dependent and noisy |
| Untyped `Term` | sort IDs/signatures in metadata | symbol declaration | macro/dynamic everywhere | Open but loses static author guidance |
| Marker types + `Subsort` | 9 marker types + 9 generic impls | production attribute/protocol | typed wrapper plus macro | Technically viable, weaker Rust intuition |

The marker-trait version is not always the fewest tokens. It is the only one
whose extra tokens continue to explain true facts: openness, membership,
recursive sort expectations, and the absence of exhaustiveness.

## Acceptance tests implied by this decision

R2 should be considered implemented only when the compiler can demonstrate:

1. the two KWasm diamonds close to one membership fact per endpoint pair;
2. a text-format module adds `Br: PlainInstr`, `BlockInstr: Instr`, and
   `ModuleDecl: Stmt` without editing the common module;
3. a recursively nested block has field type `Term<dyn Instrs>` and rejects a
   `Defns` term;
4. the four overloaded list productions lower with their distinct result sorts
   and least empty-list sort intact;
5. a rule can match a downstream constructor through `Term<dyn Instr>`;
6. exhaustive checking succeeds for a closed enum and is not promised for an
   open sort;
7. adding a new imported constructor does not invalidate a previously compiled
   rule declaration; and
8. generated `.k` has the same direct sort/list graph as the hand-written
   KWasm slice, subject to explicit symbol-name mapping.

## Sources inspected

- `wasm-semantics/.../wasm.md`, especially `WASM-COMMON-SYNTAX` and
  `WASM-INTERNAL-SYNTAX` (K 7.1.329)
- `wasm-semantics/.../wasm-text.md`, especially
  `WASM-TEXT-COMMON-SYNTAX`
- `wasm-semantics/.../test.md` and `auxil.md` for later extensions
- K user manual sections on syntax declarations, subsort overloading, named
  non-terminals, and parametric productions
