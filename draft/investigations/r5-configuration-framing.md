# R5: Configuration and framing

## Decision

Use nested Rust structs to declare the fixed cell tree, and use five nominal
wrapper families for cells whose multiplicity or collection semantics matter:

```text
Cell<T>                 // exactly one leaf cell
OptionalCell<T>         // zero or one cell
SetCells<T>             // zero or more cells, AC and idempotent
ListCells<T>            // zero or more cells, ordered
MapCells<K, T>          // zero or more cells, AC and indexed by a key subcell
```

`KCell<KSequence>` is the standard main-cell specialization of `Cell<T>`.
An attributed nested struct describes the contents of a cell that has child
cells rather than term contents. The field containing it supplies the cell's
name:

```rust
use k::builtin::{Int, List, Map};
use k::configuration::{Cell, KCell};

#[k::cell]
pub struct CurrentFrame {
    pub current_body: Cell<List>,
    pub caller: Cell<Ty>,
    pub locals: Cell<List>,
}

#[k::configuration(root = "kmir")]
pub struct Kmir {
    pub k: KCell<KSequence>,
    #[k::cell(name = "currentFrame")]
    pub current_frame: CurrentFrame,
    pub stack: Cell<List>,
    pub functions: Cell<MaybeMap>,
}
```

The default K cell name is the field identifier exactly as written, after
removing Rust's `r#` raw-identifier prefix. KRS does **not** silently convert
snake case to camel case or hyphens. `#[k::cell(name = "...")]` is required
when the K name differs. This makes renames and emitted K symbols predictable.

Configuration initialization remains a restricted `#[k::init]` associated
function. Its annotated parameters declare K configuration variables; its
result is a declarative initializer tree, not host-language code executed to
manufacture a mutable Rust value:

```rust
impl Kmir {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] program: Term<dyn KItem>,
    ) -> Self {
        Self {
            k: KCell::new(k![program]),
            current_frame: CurrentFrame {
                current_body: Cell::new(List::empty()),
                caller: Cell::new(Ty(-1)),
                locals: Cell::new(List::empty()),
            },
            stack: Cell::new(List::empty()),
            functions: Cell::new(MaybeMap::None),
        }
    }
}
```

For rules, keep ordinary Rust record patterns when tying a rule to the current
nesting is useful. Add a compiler-parsed `cells!` pattern/expression for K's
path-independent configuration abstraction:

```rust
#[k::rule]
fn assign(
    state @ cells! {
        k: KCell(k![Assign(name, value), tail @ ..]),
        env: Cell(env),
    }: Machine,
) -> Machine {
    cells! {
        k: KCell(k![..tail]),
        env: Cell(env.update(name, value)),
        ..state
    }
}
```

The compiler resolves `k` and `env` as declared cell identities, inserts their
omitted ancestors, supplies typed frames for all omitted siblings and generated
cells, and creates one simultaneous pre/post rewrite. `..state` is therefore a
configuration frame, not Rust struct-update execution. This form retains K's
useful property that inserting or removing an intermediate parent does not
force unrelated rules to change.

Collection-cell matching and cell fragments require their own visibly special
macros. Their schematic payloads are shown below; they cannot honestly inherit
Rust collection or ownership semantics:

```text
cell_set![item, rest @ ..]
cell_list![first, rest @ ..]
cell_map![key => item, rest @ ..]
fragment![Fs { f: cell_set![item, rest @ ..] }]
```

All complete item examples above are within the R1 boundary: the outer file is
Rust syntax, while K-specific patterns remain inside named macro token trees.

## Configuration declaration model

### Fixed and nested cells

An attributed configuration struct is a schema for one complete runtime
configuration. It is not itself necessarily a K cell.

```rust
#[k::configuration]
pub struct Calc {
    #[k::cell(color = "green")]
    pub k: KCell<KSequence>,
    #[k::cell(color = "yellow")]
    pub env: Cell<Map<Id, Term<dyn Value>>>,
}
```

With no `root` argument, KRS emits the fields as top-level cells. If there is
more than one top-level cell, the K frontend generates its internal
`<generatedTop>` cell just as it does for an ordinary K declaration. A named
root is explicit:

```rust
#[k::configuration(root = "kmir")]
pub struct Kmir { /* children of <kmir> */ }
```

`#[k::cell] struct` is permitted only as the content type of fixed, optional,
or repeated cells. Its fields must themselves be cells. An ordinary term
struct cannot accidentally become a cell group merely because it has fields.
Conversely, a leaf cell contains an ordinary K term and uses `Cell<T>` (or
`KCell<T>`). This lets the compiler reject a mixture of child cells and term
contents, matching K's well-formedness restriction.

The struct field declaration order is retained for deterministic `.k` output
and generated production arity. Rules resolve children by cell identity, not
by position, so reordering fixed fields is semantically inert after lowering.

### IMP encoding

The full IMP configuration is direct:

```rust
#[k::configuration]
pub struct Machine {
    #[k::cell(color = "green")]
    pub k: KCell<KSequence>,
    #[k::cell(color = "yellow")]
    pub env: Cell<Map<Id, Term<dyn Value>>>,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] program: Term<dyn Stmt>,
        #[k::config_var(name = "ENV")] env: Map<Id, Term<dyn Value>>,
    ) -> Self {
        Self {
            k: KCell::new(k![program]),
            env: Cell::new(env),
        }
    }
}
```

This lowers to `$PGM:Stmt` and `$ENV:Map` rather than inventing a special `$`
identifier syntax. `main` gives `PGM` its positional-input and main-syntax
behavior. At most one parameter may be `main`.

### KMIR encoding

KMIR demonstrates that deep fixed state does not need another abstraction:

```rust
#[k::cell]
pub struct CurrentFrame {
    #[k::cell(name = "currentBody")]
    pub current_body: Cell<List>,
    pub caller: Cell<Ty>,
    pub dest: Cell<Place>,
    pub target: Cell<MaybeBasicBlockIdx>,
    pub unwind: Cell<UnwindAction>,
    pub locals: Cell<List>,
    #[k::cell(name = "currentSpan")]
    pub current_span: Cell<Span>,
}

#[k::configuration(root = "kmir")]
pub struct Kmir {
    pub k: KCell<KSequence>,
    #[k::cell(name = "retVal")]
    pub ret_val: Cell<RetVal>,
    #[k::cell(name = "currentFunc")]
    pub current_func: Cell<Ty>,
    #[k::cell(name = "currentFrame")]
    pub current_frame: CurrentFrame,
    pub stack: Cell<List>,
    pub functions: Cell<MaybeMap>,
    pub types: Cell<MaybeMap>,
    pub memory: Cell<MaybeMap>,
}

impl Kmir {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] program: Term<dyn KItem>,
    ) -> Self {
        Self {
            k: KCell::new(k![program]),
            ret_val: Cell::new(RetVal::NoReturn),
            current_func: Cell::new(Ty(-1)),
            current_frame: CurrentFrame {
                current_body: Cell::new(List::empty()),
                caller: Cell::new(Ty(-1)),
                dest: Cell::new(Place::sentinel()),
                target: Cell::new(MaybeBasicBlockIdx::None),
                unwind: Cell::new(UnwindAction::Unreachable),
                locals: Cell::new(List::empty()),
                current_span: Cell::new(Span(-1)),
            },
            stack: Cell::new(List::empty()),
            functions: Cell::new(MaybeMap::None),
            types: Cell::new(MaybeMap::None),
            memory: Cell::new(MaybeMap::None),
        }
    }
}
```

The initializer body may contain literals, variables declared by its
parameters, constructors, imported builtin constants, and calls to declared
total K functions. It may not contain loops, mutation, I/O, an arbitrary Rust
call, early return, or host control flow. Every configuration field must be
initialized exactly once. KRS lowers the expression tree into K initializer
productions/rules and retains an optional `#[k::ensures(...)]` on the init item
for the top initializer.

Configuration parameters can also carry parser selection metadata:

```rust
fn init(
    #[k::config_var(name = "FOO", parser_module = "TEST")] foo: Foo,
) -> Self {
    /* restricted initializer expression */
}
```

This is the Rust-shaped equivalent of K's configuration-declaration `parser`
attribute. It belongs on the parameter, where the variable name and sort are
already explicit.

K also recognizes fresh integer variables in configuration initializers. Keep
that feature explicit with compiler intrinsics usable only in `#[k::init]`:

```rust
#[k::configuration(root = "allocator")]
pub struct Allocator {
    pub first: Cell<Int>,
    pub second: Cell<Int>,
}

impl Allocator {
    #[k::init]
    fn init() -> Self {
        Self {
            first: Cell::new(k::config::fresh_named::<Int>("INITIAL_ID")),
            second: Cell::new(k::config::fresh::<Int>()),
        }
    }
}
```

Each unnamed call denotes a distinct initial constant; equal names denote the
same initial constant throughout the definition. The pinned K frontend accepts
only `Int` here, so the generic-looking spelling is checked and rejected for
other sorts. These initial constants reserve counter values before execution;
they are different from rule-level `#[k::fresh(...)]` binders and from external
configuration variables.

## Optional and repeated cells

Multiplicity is inferred from the resolved wrapper type, not duplicated in an
attribute string. KRS rejects `#[k::raw_attr("multiplicity(...)")]` or a typed
cell attribute that conflicts with the field's wrapper.

The initializer constructors deliberately carry both the cell's default
template and whether an instance is initially present:

```rust
#[k::configuration(root = "collections")]
pub struct Collections {
    pub optional: OptionalCell<Int>,
    pub set: SetCells<Int>,
    pub list: ListCells<Int>,
}

impl Collections {
    #[k::init]
    fn init() -> Self {
        Self {
            optional: OptionalCell::absent(0),
            set: SetCells::empty_with(0),
            list: ListCells::empty_with(0),
        }
    }
}
```

The payload to `absent`/`empty_with` is not a hidden runtime element. It is the
default initializer for a cell that may later be introduced with omitted
contents. To request K's `initial=""` behavior, use
`OptionalCell::initial(value)` or `SetCells::singleton(value)` (and the
corresponding list/map constructor).

K currently also initializes an optional/repeated cell implicitly when its
template contains a configuration variable, while issuing a warning asking
for `initial=""`. KRS should require the explicit `initial`/`singleton` form.
It emits the same K attribute and avoids preserving a surprising warning-based
source convention. A compatibility lint can explain the difference when
translating existing K.

At runtime and in rule patterns, an optional cell has two structural forms:

```text
OptionalCell::Absent
OptionalCell::Present(value)
```

This is not object-language `Option<T>`: absence means that the cell production
is missing from the configuration. The compiler remembers the declaration's
default separately, so a rule need not carry it in `Absent`.

### Map cells and their keys

A concurrent configuration illustrates the map-cell design:

```rust
#[k::cell]
pub struct Thread {
    #[k::key]
    pub id: Cell<Int>,
    pub k: KCell<KSequence>,
}

#[k::cell]
pub struct Threads {
    pub thread: MapCells<Int, Thread>,
}

#[k::configuration]
pub struct ConcurrentMachine {
    pub threads: Threads,
    #[k::cell(name = "next-id")]
    pub next_id: Cell<Int>,
}

impl ConcurrentMachine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] program: Term<dyn Stmt>,
    ) -> Self {
        Self {
            threads: Threads {
                thread: MapCells::singleton(Thread {
                    id: Cell::new(0),
                    k: KCell::new(k![program]),
                }),
            },
            next_id: Cell::new(1),
        }
    }
}
```

For `MapCells<K, T>`, `T` must be a `#[k::cell]` struct and exactly one field
must be `#[k::key]`. KRS requires that field to occur first and checks that its
content sort is the wrapper's key parameter `K`. This encodes the frontend's
actual rule: the first child cell is the map key; its name has no special
meaning.

The key remains part of the complete `Thread` cell. `MapCells<Int, Thread>` is
therefore not a Rust `HashMap<Int, Thread-without-id>` even though indexed
matching looks map-like. K's generated map element contains both the key term
and the complete surrounding cell term, including its key subcell.

Map pattern syntax makes indexed lookup explicit:

```rust
#[k::rule]
fn join(
    state @ cells! {
        k: KCell(k![Join(id), tail @ ..]),
        thread: cell_map![
            id => Thread {
                k: KCell(k![Return(value), ..]),
                ..
            },
            threads @ ..
        ],
    }: ConcurrentMachine,
) -> ConcurrentMachine {
    cells! {
        k: KCell(k![value, ..tail]),
        thread: cell_map![..threads],
        ..state
    }
}
```

In a pattern, `key => item_pattern` asks for the cell indexed by the evaluated
key, and `rest @ ..` binds the remaining cell map. On the RHS, `..rest`
reconstructs that remainder. Omitting the selected entry removes it. A
construction entry may spell `key => item_expression`; KRS verifies that the
item's key subcell agrees with `key` or fills an omitted key field from it.

If the map key is not mentioned, a `cell_map!` item pattern denotes K's
nondeterministic constrained selection rather than an indexed lookup. KRS
should warn on that form by default because it has materially different
performance and branching behavior.

### Set and list cells

Set cells use associative-commutative-idempotent matching:

```text
cell_set![thread @ Thread { .. }, rest @ ..] // pattern
cell_set![new_thread, ..rest]                // expression
```

Duplicate complete cell terms collapse; selecting an element can branch. No
`Eq`, `Hash`, iterator order, or host set API is implied.

List cells preserve order and permit matching/insertion only at supported
ends:

```text
cell_list![first, rest @ ..] // front pattern
cell_list![rest @ .., last]  // back pattern
cell_list![new, ..rest]      // front insertion
cell_list![..rest, new]      // back insertion
```

K's current frontend supports `type="List"` for multiplicity `*`, although an
older tutorial page still says only Set and Map are permitted. The current
user manual and `GenerateSentencesFromConfigDecl` implementation both include
List, so KRS should support it and pin compatibility tests to the selected K
version.

The frontend also accepts `type="Bag"`. It is omitted from the primary API
because the requested useful modes are Set/List/Map and unordered non-idempotent
bags are rarely the clearest choice. `BagCells<T>` can be provided as a
versioned compatibility wrapper without changing the design.

## Framing and rule normalization

KRS must keep four different frames distinct in its IR:

| Source notation | Frame kind | Algebra |
|---|---|---|
| omitted cell in `cells!`, `..state` | configuration/cell-tree frame | declared cell structure |
| `k![head, tail @ ..]` | K-sequence tail | associative sequence, tail only |
| `cell_set!`, `cell_list!`, `cell_map!` remainder | collection frame | ACU/ACUI/list as appropriate |
| `fragment![...]` binding | first-class cell fragment | product of optional child-cell slots and collection remainders |

They must not become one untyped `Rest` node. Collection matching may produce
multiple decompositions, while fixed-cell completion has one declaration-led
shape.

An ordinary nested record rule remains available:

```rust
#[k::rule]
fn set_local(
    state @ Kmir {
        current_frame: CurrentFrame {
            locals: Cell(locals),
            ..
        },
        ..
    }: Kmir,
) -> Kmir {
    Kmir {
        current_frame: CurrentFrame {
            locals: Cell::new(update(locals)),
            ..state.current_frame
        },
        ..state
    }
}
```

This is concise and provides normal field navigation, but it intentionally
names the parent path. The equivalent path-independent rule uses `cells!`:

```rust
#[k::rule]
fn set_local(
    state @ cells! { locals: Cell(locals) }: Kmir,
) -> Kmir {
    cells! { locals: Cell(update(locals)), ..state }
}
```

The latter is the recommended spelling for semantic rules. The former is
useful when a particular parent is semantically relevant or when ordinary Rust
tooling is more valuable than resilience to configuration refactoring.

Cell identities must be unique in one declared configuration, excluding the
multiple runtime instances of one repeated cell. This matches the K frontend's
configuration-information model and lets `cells! { locals: ... }` resolve
without an invented path language. If composition creates a name collision,
KRS rejects it and asks the author to rename a cell at its declaration.

After resolution, the rule above normalizes to a complete `Kmir` pre-pattern
and post-pattern. Omitted parents and siblings receive generated typed frame
variables. All changed cells share the same frames, so distant updates happen
simultaneously. A RHS cell omitted without `..state`, an explicit optional
absence, or an explicit collection remainder is an error rather than an
accidental deletion.

## First-class cell fragments

Cell fragments are not just partial state matches. K permits a fragment of a
parent cell to become an ordinary term, be passed to a function, and later be
matched or reconstructed. The K frontend generates a `ParentCellFragment`
sort whose fixed child positions are optional and whose repeated positions
contain collection fragments.

Expose that generated family as the nominal compiler type
`CellFragment<Parent>` and construct/match it only with `fragment!`:

```rust
#[k::cell]
pub struct Fs {
    pub f: SetCells<Int>,
}

pub struct CollectOdd(pub CellFragment<Fs>);

#[k::rule]
fn start_collect(
    state @ cells! {
        k: KCell(k![StartCollect, tail @ ..]),
        fs: fragment![all_fs @ Fs { .. }],
    }: Machine,
) -> Machine {
    cells! {
        k: KCell(k![CollectOdd(all_fs), ..tail]),
        ..state
    }
}

#[k::function]
#[k::requires(i % 2 == 1)]
fn collect_odd(
    fragment![Fs {
        f: cell_set![i, rest @ ..],
    }]: CellFragment<Fs>,
) -> Set<Int> {
    Set::item(i) | collect_odd(fragment![Fs { f: cell_set![..rest] }])
}
```

Inside a configuration pattern, `fragment![all_fs @ Fs { .. }]` captures the
complete contents of the declared `fs` cell as a first-class fragment term;
it does not move the cell out of the state. In a function pattern,
`fragment![Fs { ... }]` destructures the generated fragment positions.
Omitting a fixed child from a fragment means "this fragment did not capture
that child", which is distinct from capturing an optional cell and observing
that the optional cell is absent. The compiler must retain this distinction,
as the K frontend does with generated `CellOpt` sorts.

`CellFragment<P>` cannot have a general public Rust constructor. Its valid
field set and algebras are generated from configuration `P`, and malformed or
fully ambiguous fragments are subject to K frontend restrictions. Keeping the
macro compiler-owned prevents the stdlib from promising combinations K cannot
lower.

## Attributes and composed cells

Recognized typed field attributes include:

```text
#[k::cell(name = "status-code", exit)]
#[k::cell(color = "green", format = "...")]
#[k::cell(stream = "stdin")]
#[k::key]
```

`exit` requires a single fixed cell containing `Int`. `stream` is not a visual
annotation: K imports and specializes stream modules and changes initializer
behavior, so it is a compiler-recognized attribute with target-version checks.
`color` and `format` are typed presentation attributes. Less common production
attributes use the existing explicit `#[k::raw_attr("...")]` escape hatch and
are preserved for K lowering.

K's `<cell/>` syntax composes a cell declared in another module. In KRS, the
schema type is imported normally and the field is marked at the composition
site:

```rust
use io_semantics::Io;

#[k::configuration]
pub struct Machine {
    pub k: KCell<KSequence>,
    #[k::external_cell]
    pub io: Io,
}
```

The compiler verifies that `Io` exports one compatible cell declaration and
emits the external-cell form when producing `.k`. There must still be exactly
one fully composed configuration in the final definition.

## Generated cells and APIs

Do not expose `<generatedTop>` or `<generatedCounter>` as user fields.

- `<generatedTop>` is an implementation wrapper inserted when a declaration
  has multiple top-level cells. `#[k::configuration(root = "...")]` is the
  user-facing way to request a real named root.
- `<generatedCounter>` is inserted when fresh constants require it and is also
  added to relevant claims by frontend passes. Its initial value accounts for
  all `k::config::fresh` constants in the initializer tree.
- generated initializer symbols, cell collection sorts/items, optional-cell
  units, cell-fragment sorts, sort predicates, and projections are likewise
  compiler artifacts.

Normalized configuration IR records these cells and symbols so emitted K and
Kore can be inspected and differentially tested. Source rules automatically
frame them. An advanced raw-K escape hatch may mention internal cells, but the
ordinary KRS type for a configuration must not change merely because one rule
uses a fresh variable.

## Compiler syntax versus standard library

The boundary should be explicit:

| Facility | Owner | Reason |
|---|---|---|
| `#[k::configuration]`, `#[k::cell]`, `#[k::init]`, `#[k::config_var]`, `#[k::key]` | compiler | declares schema, names, defaults, and generated K productions |
| `Cell`, `KCell`, `OptionalCell`, `SetCells`, `ListCells`, `MapCells`, `CellFragment` | versioned stdlib types interpreted by compiler after name resolution | gives IDE-visible nominal types; behavior is not implementable as Rust containers |
| `cells!`, `cell_set!`, `cell_list!`, `cell_map!`, `fragment!` | compiler-parsed macros | introduce bindings and associative/structural pattern semantics unavailable in Rust AST |
| `k::config::fresh`, `fresh_named` | compiler intrinsics with stdlib declarations | allocates definition-wide initial integer constants and sizes the generated counter |
| term-level `Map`, `Set`, `List`, `KSequence` operations | stdlib K symbols/functions | ordinary imported object-theory terms, separately hookable by the target |
| framing, cell completion, default insertion, generated cells/sorts | compiler normalization | depends on the complete configuration graph and pre/post rule pair |

The compiler resolves wrapper types semantically, including aliases and
qualified imports; it must not recognize them by raw token spelling. A small
companion `k` crate can supply declarations for rust-analyzer and rustc parser
experiments, but Rust trait implementations do not define collection-cell
matching.

Term collections and cell collections must remain visibly distinct. A
`Cell<Map<K, V>>` is one fixed cell whose **contents** are a K Map.
`MapCells<K, T>` is a repeated family of structurally named cells compiled to a
generated map sort. Their patterns, defaults, and generated projections differ.

## Rust semantic deviations that must be documented

The surface intentionally borrows Rust's visual vocabulary without claiming
these host semantics:

1. Rule patterns bind logical terms; they do not borrow or move memory. The
   same binding can occur repeatedly on a RHS.
2. `..state` shares configuration frames between pre and post. It is not a
   sequence of reads followed by Rust struct-update evaluation.
3. Configuration values are immutable symbolic terms. There is no `&mut`,
   interior mutability, iterator, entry API, allocation, or drop behavior.
4. `OptionalCell<T>` is cell absence/presence, not the object-theory enum
   `Option<T>`.
5. Set and map patterns can branch under AC matching. Map lookup keys may be K
   function terms evaluated before lookup, not host-hashable values.
6. A map-cell value includes its key subcell and surrounding cell. The generic
   key parameter documents/indexes that structure rather than removing it from
   `T`.
7. Cell struct patterns are not exhaustive over future configuration changes
   when `..` or `cells!` frames them. KRS should lint fixed patterns that omit a
   frame.
8. Initializer functions and wrapper constructors are declarations interpreted
   by KRS. They are not callable runtime constructors with ordinary Rust
   evaluation order.

These deviations are acceptable because each occurs behind a `k::` marker,
nominal K type, or visibly special macro. Plain Rust structs, functions,
matches, `Option`, and standard collections retain their ordinary meaning.

## Required validation

Before lowering, KRS can diagnose configuration errors more directly than K's
generated productions do:

- exactly one complete configuration after external-cell composition;
- no duplicate cell identity in the configuration graph;
- fixed cell groups contain only cells and leaf cells contain one term;
- `MapCells` has one `#[k::key]` child of the declared key sort;
- repeated cells are the only child of their immediate collection parent, as
  required by K's configuration model;
- initializer fields and configuration variables agree with the schema;
- every optional/repeated cell explicitly chooses empty versus initially
  present behavior;
- collection and K-sequence patterns use legal remainder positions;
- each RHS preserves, replaces, creates, or removes cells explicitly; and
- cell-fragment uses are supported by the pinned K frontend version.

KRS should preserve declaration spans through generated cell, initializer,
fragment, and collection productions so any later K frontend error points back
to the field or macro that caused it.

## Remaining blockers

No unresolved issue blocks the overall configuration surface. Three details
need prototype/equivalence tests before freezing exact spellings:

1. **Initializer closure with input-dependent defaults.** K's `CloseCells`
   rejects some RHS cell completion when the initializer requires a
   configuration variable. KRS must reproduce the exact accepted subset and
   issue the error at `OptionalCell`/collection construction. This affects
   validation, not the schema model.
2. **Cell-fragment edge cases.** The current frontend source documents limits
   around fragments used only in normal terms and fully filled fragment terms.
   The `fragment!` macro should begin with the proven forms from the manual and
   expand only after golden tests against `SortCells`.
3. **Collection-pattern grammar details.** The chosen macros and separation of
compiler/stdlib responsibilities are clear, but exact syntax for multiple
   entries, a keyless nondeterministic map selection, and symbolic construction
   should be fixed together with R7's logic/pattern IR.

The following are compatibility/version questions rather than design
blockers: whether to expose `BagCells<T>` in tier 1, which stream attributes to
support initially, and whether external cell composition is needed before the
first IMP/KMIR milestone.

## Sources inspected

- K user manual sections “Configuration Declaration”, “Collection Cells:
  `multiplicity` and `type` attributes”, “Matching on cell fragments”, parser
  generation for configuration variables, and function access to global
  configuration.
- K tutorial lessons 1.15 (configuration variables, nesting, and configuration
  abstraction) and 1.17 (optional cells and map-cell concurrency).
- K frontend `GenerateSentencesFromConfigDecl.java`, especially generation of
  initializers, optional units, Set/List/Map/Bag cell collection sorts and map
  keys, cell fragment/`CellOpt` sorts, and generated-top wrapping.
- K frontend `SortCells.java`, `CloseCells.java`, `AddParentCells.java`, and
  generated counter/top support.
- current IMP `calc.k`/`expr.k`, KMIR `rt/configuration.md` and representative
  multi-cell rules, and KWasm's nested map-cell configuration.
- R1's Rust parser boundary and sample, plus R3's relational rule surface and
  requirement for distinct typed frames.
