# R10: Modules, builtins, dependencies, and toolchain

> R11 adds a native structured frontend route through `k-rust`. The package,
> facet, builtin, stable-name, and kdist decisions here still apply; statements
> that `.k` is the only production boundary are superseded by
> [R11](r11-k-rust-frontend-integration.md).
>
> R12 also supersedes this report's standalone `Krs.toml` and non-rustc package
> assumptions. Cargo now owns the package graph and KRS metadata is namespaced
> inside `Cargo.toml`; the module/facet and external-toolchain reasoning remains
> applicable. See [R12](r12-rust-host-architecture.md).

## Decision

KRS should present one Rust module and package system and treat K's file and
module organization as a lowering concern. In particular:

- Rust `mod` defines the source ownership tree and includes that module in the
  enclosing KRS definition;
- Rust `use` performs name lookup and aliasing only;
- Rust `pub`, `pub(crate)`, `pub(super)`, and `pub use` control the KRS API;
- a manifest definition/target selects which crate or facet is composed into a
  rewrite theory; and
- lowering aggregates a selected KRS crate before generating a small, fixed
  family of K modules and the necessary `requires` closure.

Do **not** lower each `use` to K `imports`, or each `.rs` file to one K module.
A K import composes every recursively imported rule and equation and also
changes syntax visibility. A Rust use merely puts names in lexical scope. Real
Rust modules can refer to one another in patterns that would create K module
cycles, while KRS already needs crate-wide collection to compute the open-sort
and subsort closure selected in R2.

For each selected definition, generate these logical K modules:

```text
<NS>-<DEF>-SYNTAX       externally selected object-program grammar
<NS>-<DEF>-SIGNATURE    all remaining sorts and productions
<NS>-<DEF>-SHARED       configuration and backend-independent semantics
<NS>-<DEF>-CONCRETE     LLVM-only sentences [concrete]
<NS>-<DEF>-SYMBOLIC     Haskell-only sentences [symbolic]
<NS>-<DEF>              generated main-module facade
```

The exact number may be reduced when a module is empty, but these roles belong
in Definition IR even if the text emitter coalesces them. The facade publicly
imports `SYNTAX` and privately imports implementation modules. Implementation
modules directly and privately import every signature/builtin/dependency module
needed to parse their sentences. KRS, not K's comparatively coarse syntax
privacy, enforces source visibility.

This design is consistent with R6: the compiler owns a structured K Definition
IR, emits deterministic `.k` as the supported boundary, and lets the stock K
frontend perform normal import resolution, builtin loading, desugaring, and
backend filtering.

## Why the two K graphs must stay below the source language

K currently has two organization mechanisms:

1. `requires "path"` makes files available to the outer parser; and
2. `imports MODULE` composes a module's sentences into another module.

The K manual describes both hierarchies as DAGs. Current KMIR demonstrates an
additional practical reason not to expose the file graph: `ty.md` requires
`alloc.md`, while `alloc.md` requires `ty.md`; `ParserUtils` terminates this by
tracking canonical files already loaded. KMIR then avoids actual K module
cycles with `TYPES-SORTS`, `ALLOC-SORTS`, `BODY-SORTS`, and similar forward
signature modules. KRS can provide the same result more cleanly by collecting
the crate before emission and writing a canonical, acyclic generated
`requires` closure.

The source correspondence is therefore deliberately not one-to-one:

| KRS/Rust concept | KRS meaning | Generated K concern |
|---|---|---|
| crate | versioned definition namespace and compilation unit | one or more generated definition facades |
| `.rs` file | storage for a Rust module | source-map partition only; no required K file identity |
| `mod child;` | include child in the module ownership tree | child's items are collected into the selected definition |
| inline `mod child {}` | same module semantics as an external file | same lowering as `mod child;` |
| `use p::X as Y` | bind the origin item under a local name | no K edge by itself; references retain origin IDs |
| `pub` | downstream KRS name visibility | API metadata; not inferred from K module visibility |
| `pub use` | downstream KRS re-export of the original item | metadata re-export; the K symbol keeps its origin name |
| manifest dependency | make another crate's metadata/source available | required source artifact plus selected signature/theory imports |
| target composition | activate a definition's rules and equations | private import of its generated semantic facade |

This preserves a strong Rust expectation: adding or removing an unused `use`
cannot change the transition relation. It also prevents a glob import from
silently activating rules.

## KRS modules and definition composition

### Source modules

Use Rust 2024 module path rules for the MVP:

```rust
// src/lib.rs
pub mod expr;
pub mod calc;
mod implementation_detail;

pub use expr::{Expr, Value};
```

`crate`, `self`, `super`, aliases, glob imports, and the ordinary Rust
visibility lattice should behave as Rust readers expect. The compiler should
resolve module and item paths before it constructs the K Definition IR. A use
site records the canonical definition ID, so aliases do not affect emitted K
symbols.

All modules reachable through `mod` from a selected crate root are compiled.
Their rule items are active in that definition regardless of whether their
names are imported into the root module, just as module inclusion is separate
from lexical `use`. KRS should warn about a private module containing public
global semantic effects only if that proves confusing in real ports; privacy
does not mean that a rule is dormant.

### Multiple definition facets

IMP, KWasm, and KMIR compile more than one useful theory from the same source:
an executable LLVM definition, a Haskell proof definition, an LLVM C library,
and sometimes a smaller parser/AST definition. The manifest should allow named
definition facets without making K module names author-facing:

```toml
[definitions.imp]
root = "crate"
syntax-root = "crate::imp"

[targets.llvm]
definition = "imp"
backend = "llvm"
parser = "glr"
opt-level = 3

[targets.llvm-lib]
definition = "imp"
backend = "llvm"
llvm-kompile-type = "c"

[targets.haskell]
definition = "imp"
backend = "haskell"
features = ["verification"]
```

`root` selects the module subtree/facet whose sentences are composed.
`syntax-root` selects the program grammar exported through the generated
syntax module. The default is the whole crate for both, which is enough for the
first IMP port. A later `k::definition!` source item is unnecessary unless
manifest-only composition proves hard to read.

An external semantic library is made available in `[dependencies]`; a target
or definition explicitly composes its exported facet. `use dependency::X`
still only binds names. The exact manifest spelling can be prototyped, but the
semantic distinction must not change.

### Public program syntax versus public KRS API

These are independent axes:

- `pub` says that a dependent KRS crate may name an item;
- inclusion under `syntax-root` says that its production participates in the
  target's object-program parser; and
- `#[k::internal]` can keep an administrative production out of that parser
  while retaining it in the definition signature.

This distinction is needed for KWasm's text grammar versus administrative
instructions and for KMIR's external AST parser. Rust visibility must not
accidentally decide which strings the generated parser accepts.

The generated layout is conceptually:

```k
module ORG-EXAMPLE-IMP-IMP-SYNTAX
  // externally parseable syntax only
endmodule

module ORG-EXAMPLE-IMP-IMP-SIGNATURE
  imports public ORG-EXAMPLE-IMP-IMP-SYNTAX
  // public and private internal term declarations
endmodule

module ORG-EXAMPLE-IMP-IMP-SHARED
  imports private ORG-EXAMPLE-IMP-IMP-SIGNATURE
  imports private INT
  imports private BOOL
  // configuration, equations, rules, contexts, claims
endmodule

module ORG-EXAMPLE-IMP-IMP-CONCRETE [concrete]
  imports private ORG-EXAMPLE-IMP-IMP-SHARED
  // LLVM-specific sentences
endmodule

module ORG-EXAMPLE-IMP-IMP-SYMBOLIC [symbolic]
  imports private ORG-EXAMPLE-IMP-IMP-SHARED
  // Haskell-specific sentences
endmodule

module ORG-EXAMPLE-IMP-IMP [private]
  imports public  ORG-EXAMPLE-IMP-IMP-SYNTAX
  imports private ORG-EXAMPLE-IMP-IMP-SHARED
  imports private ORG-EXAMPLE-IMP-IMP-CONCRETE
  imports private ORG-EXAMPLE-IMP-IMP-SYMBOLIC
endmodule
```

K import privacy mainly controls transitive syntax visibility; recursively
imported semantic sentences still compose. The KRS resolver remains the source
of truth for whether an author could name a private item. Generated modules may
have broader direct visibility than source code because they are compiler
output, not a supported handwritten API.

### Avoiding K module cycles

Within one KRS crate, collect all selected items before partitioning them into
the generated roles. Recursive type references and mutually referring Rust
modules therefore require no K import edge. Direct sort/subsort edges are
emitted once in `SIGNATURE`, and rules are emitted after that signature exists.

Across crates, package dependencies and explicit facet composition must be
acyclic. KRS reports a package/facet cycle using Rust paths before emitting K.
This is stricter and easier to diagnose than allowing a generated K import
cycle.

The `.k` emitter should normally write one deterministic entry file per target
and one source file per dependency artifact, with all `requires` at the top.
Splitting a large local definition into several generated files is a cache and
diagnostic optimization, not a language feature.

## Builtins and hooks

### A compiler sysroot crate

`k` should be a reserved, compiler-provided crate whose API is generated and
tested for each supported K release:

```rust
use k::builtin::bool::{self, Bool};
use k::builtin::int::{self, Int};
use k::builtin::map::{self, Map};

#[k::requires(int::ne(denominator, 0))]
#[k::rule]
fn divide(Div(numerator, denominator): Expr) -> Expr {
    IntValue(int::div(numerator, denominator))
}
```

These declarations are compiler metadata, not Rust implementations. Each
builtin entry records at least:

```text
BuiltinItem {
  krs_path,
  defining_k_module,
  source_signature,
  exact_k_symbol_or_hook,
  textual_k_spelling,
  functionality,
  attributes,
  backend_capabilities,
  introduced/deprecated K versions,
}
```

Name resolution is Rust-like and only exposes explicitly imported names.
Lowering computes a minimal set of private K module imports from the builtin
items actually referenced. For example, a rule using `int::div` needs `INT` in
its implementation module, whereas an object grammar that only embeds integer
literals may need `INT-SYNTAX` in the program syntax module. A `use` alone does
not force an otherwise unused K import.

Do not copy K's builtin equations or implement them in the KRS standard
library. Import the modules shipped by the pinned K distribution, so the stock
frontend and backend remain the authority.

### Operators are typed term constructors, not Rust execution

R7 deliberately uses `int::lt`, `int::add`, and `k::and_bool!` rather than
host-looking `<`, `+`, and `&&`. Keep that policy in v1. Builtin calls construct
K terms; they do not run Rust code during compilation.

Operator sugar can be added later through a closed, sort-directed table in the
pinned builtin registry. It must never depend on arbitrary Rust `Add`/`Ord`
trait resolution, because K functions can be partial and symbolic and K's
Boolean connectives do not have Rust short-circuit semantics. Explicit module
paths remain the canonical, unambiguous spelling.

The `.k` emitter uses the registry's canonical source spelling, such as
`X +Int Y`, while Definition IR retains the exact imported symbol identity.
This makes the emitter resilient to local aliases and gives R8 a structural
comparison point.

### Hook policy

Hooks are backend contracts, not merely fast imported functions. K's builtin
sorts and functions combine `hook(...)` with constraints such as `token`,
`function`, `total`, `impure`, collection algebra attributes, or an SMT hook.
Support them in three tiers:

1. **Standard hooks** are available only through the versioned `k::builtin`
   bindings. Their signatures and companion attributes are compiler-known.
2. **Known custom hook attachment** uses typed `#[k::hook("DOMAIN.name")]` on
   an eligible sort or production. KRS checks the pinned hook registry,
   signature, attributes, and selected backends.
3. **Unknown/future hooks** require the existing conspicuous raw escape hatch,
   for example `#[k::raw_attr("hook(VENDOR.name)")]`. Portable/strict builds
   reject it; normal builds warn and preserve it exactly.

KRS should never claim that an arbitrary user hook has an implementation.
Backend availability is checked before invoking `kompile`. A hook supported by
LLVM but not Haskell either lives behind a backend cfg or makes the target fail
with a capability diagnostic.

The builtin registry should be derived from the pinned K distribution and then
reviewed/committed as KRS data. Pure text scraping is sufficient to discover
names but insufficient to infer all signatures and backend guarantees. Golden
compilation tests must cover each exposed binding group.

## Backend configuration

Use Rust's ordinary cfg shell with KRS-defined predicates:

```rust
#[cfg(k_backend = "llvm")]
#[k::rule]
fn concrete_bytes(/* ... */) -> State { /* ... */ }

#[cfg(k_backend = "haskell")]
#[k::simplification]
fn symbolic_bytes(/* ... */) -> MlPattern { /* ... */ }

#[cfg(feature = "verification")]
mod verification;
```

The supported closed values initially are `llvm` and `haskell`. Backend
capabilities such as `set_variables`, `llvm_library`, and `booster` should be
resolved by the target and exposed to checking as derived cfg/capability facts,
not accepted as arbitrary strings.

When a predicate maps exactly to K's module filters, place the sentence in the
generated `[concrete]` or `[symbolic]` module. This keeps one inspectable `.k`
source artifact compilable by both normal backends, matching patterns used by
KWasm and K's builtin modules. Markdown selectors such as KMIR's
`k & ! symbolic` are unnecessary for generated `.k`.

Conditions that K cannot express as a module attribute are evaluated by KRS
when generating a target-specific source artifact. Definition IR records the
cfg expression and retained/dropped status so differential tests can explain
the difference.

Do not reuse the word `symbolic` for backend cfg at item level: K already has a
`symbolic(...)` simplifier applicability attribute. `k_backend = "haskell"`
is longer but unambiguous. Backend-divergent semantics should remain sparse,
warnable, and covered by cross-backend tests; the K manual gives the same
trust warning for `[symbolic]`/`[concrete]` modules.

## Manifest, lockfile, and package metadata

Use a dedicated `Krs.toml`, with Cargo-shaped conventions where they retain
their meaning. Do not overload `Cargo.toml`: KRS is Rust-parsable but not a
rustc crate, and its K toolchain/definition targets have no Cargo equivalent.

```toml
[package]
name = "imp-semantics"
version = "0.1.0"
edition = "2024"
k-namespace = "ORG-EXAMPLE-IMP"

[toolchain]
k = "=7.1.337"

[lib]
path = "src/lib.rs"

[dependencies]
semantics-common = { path = "../semantics-common", version = "0.4" }

[definitions.imp]
root = "crate"
syntax-root = "crate::imp"

[targets.llvm]
definition = "imp"
backend = "llvm"
parser = "glr"
opt-level = 3

[targets.haskell]
definition = "imp"
backend = "haskell"
features = ["verification"]
```

The exact K release is mandatory in `Krs.lock`. A package may declare a
supported range, but a workspace resolves one exact version satisfying every
crate. K, pyk's `kframework` package, the builtin registry, and generated outer
KAST adapters are one toolchain unit. The driver rejects a mismatched
`kompile --version` or pyk version rather than hoping their schemas agree.

KRS need not provision K in v1. It should support an explicit toolchain path,
the active environment, and reproducible wrappers such as Nix, while `krs
doctor` reports the selected K, pyk, LLVM/Haskell backend, and booster
versions. Existing RV projects' `deps/k_release` can be imported when creating
a manifest, but `Krs.lock` is KRS's authority thereafter.

The lockfile records:

- exact KRS package versions and source/content hashes;
- one exact K release and builtin-registry schema hash;
- raw K dependency locations, exported module names, and content hashes;
- selected feature resolution; and
- metadata schema versions, not machine-local output paths.

The final-definition linker rejects two packages with the same
`k-namespace`. Initially it should also reject multiple versions of one
namespace in a definition. Unlike Rust symbols, K module and explicit symbol
names inhabit a global definition namespace; silently linking two versions
would be unsound. Authors needing parallel major versions must give them
distinct declared namespaces.

### Raw K dependencies

Existing K projects remain important dependencies. Model them as explicit FFI
packages rather than pretending their modules are Rust modules:

```toml
[k-dependencies.vendor]
path = "vendor/definition"
entry = "vendor.md"
modules = ["VENDOR", "VENDOR-SYNTAX"]
version = "1.2.0"
```

KRS copies or requires the locked source artifact, imports the declared
modules, and generates a checked Rust-shaped extern metadata facade for names
the author wants to use. It detects module/symbol collisions after the K
frontend parses the combined definition. Unchecked access uses `k::raw_k!` and
loses KRS type checking/source mapping as already established by R4/R6.

Path dependencies may be convenient during development, but release/CI builds
should require a content hash. Absolute include directories and ambient
`K_INCLUDE_PATH` are not part of a reproducible package identity.

## Stable names and compatibility policy

Every production used from pyk should have an explicit emitted `symbol(...)`.
K's default mangling includes module, sort, and production spelling and is not
a stable API. KRS defaults should derive a deterministic symbol from:

```text
package k-namespace + canonical Rust item path + constructor/variant
```

The package version, local `use` alias, target backend, and generated module
partition are deliberately excluded. A public item rename is therefore an API
and serialized-term breaking change. `#[k::symbol("...")]` can preserve the
old identity across a Rust rename or provide an interop name.

Apply the same policy to rule labels, initializer symbols, list terminators,
and generated projections/predicates where K permits control. Compiler-created
names include a stable item ID and role, not a source line number. R6's sidecar
maps these names and generated ranges back to KRS spans.

Package metadata (`.krsmeta`) exports:

- public Rust paths, sorts, productions, subsort edges, function signatures,
  and grammar groups;
- origin K module and exact K symbol/label for each exported item;
- exported definition facets and syntax roots;
- required builtin capabilities and K compatibility range; and
- compiler/language-edition/metadata schema versions.

Dependents type-check against this metadata and retain origin identities
through re-exports. Changing a private generated module partition must not
change downstream symbols.

Compatibility is layered:

| Version | Governs | Policy |
|---|---|---|
| KRS language edition | accepted source semantics | opt-in, Cargo-like edition |
| KRS compiler | diagnostics/lowering implementation | normal semantic versioning |
| `.krsmeta`/Definition IR schema | compiler/package interchange | explicit schema version and adapter |
| package version | public KRS/symbol API | semver, with symbol changes treated as breaking |
| K release | frontend, builtins, hooks, KAST/Kore | one exact lock pin per final definition |
| backend/booster | execution/proof behavior | recorded per target artifact and test matrix |

Raw K attributes, raw hooks, and raw K sentences are revalidated for every new
K pin. A KRS compiler supporting two K releases carries two builtin registries
and two equivalence matrices; it must not present their union as one fictional
portable API.

## kdist and pyk integration

Follow the modern IMP/KWasm/KMIR artifact shape without requiring each KRS
author to hand-maintain Python build logic.

For package `imp-semantics`, expose conventional targets:

```text
imp-semantics.source
imp-semantics.llvm
imp-semantics.llvm-lib
imp-semantics.haskell
```

The source target contains generated `.k`, the source map, symbol map,
`.krsmeta`, a target descriptor, and any locked raw K sources. Backend targets
depend on it and call version-matched `pyk.ktool.kompile.kompile` with manifest
arguments (`main_file`, generated main/syntax module, backend, parser choice,
LLVM type, optimization, and warnings-as-errors).

KRS should ship a small Python bridge and generate a declarative kdist plugin
or package stub from `Krs.toml`. The generated code contains no semantic build
decisions; it delegates to the target descriptor. This retains the ecosystem's
entry-point discovery and `kdist.which/get` behavior while keeping the manifest
authoritative.

`krs build` may invoke the same bridge directly, but it must produce the same
artifact as `kdist build`. Its cache context includes at least:

- KRS compiler and Definition IR schema versions;
- complete `Krs.lock` and selected definition/target/features;
- source and dependency content hashes;
- exact K/pyk/backend versions; and
- all kompile arguments and raw include artifacts.

Downstream pyk code should locate a target through kdist, load
`compiled.json`/the definition directory, and consume the KRS symbol map rather
than duplicating K label strings. The generated artifact descriptor gives pyk
the main module, syntax module, source directory, compiled definition path, and
source-map path. This directly supports R8's parser, execution, search, and
proof oracle.

Do not make pyk's outer `KDefinition` classes the KRS authoring IR. R6 found
that their source-definition coverage is incomplete and that KAST JSON and
hidden outer-parsed APIs are version-coupled. Pyk is the orchestration and
inspection interface after `.k` emission, not the source language's semantic
foundation.

## End-to-end example

Source:

```rust
// src/lib.rs
pub mod expr;
pub mod machine;

// src/expr.rs
use k::builtin::int::{self, Int};

#[k::sort]
pub trait Expr: KItem {}

#[k::syntax("{lhs} + {rhs}", group = "additive")]
pub struct Add {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}
impl Expr for Add {}

#[k::rule]
fn add(Add(IntValue(x), IntValue(y)): Expr) -> Expr {
    IntValue(int::add(x, y))
}
```

Resolution and lowering behave as follows:

1. `mod expr` includes declarations and the rule in the selected crate; `use`
   makes `Int` and `int` available only in `expr`.
2. `Add`'s explicit grammar goes into the selected program `SYNTAX` role; its
   stable symbol derives from the package namespace and `crate::expr::Add`.
3. The rule goes into `SHARED` and references the builtin registry identity for
   integer addition.
4. `SHARED` privately imports `INT`; `SYNTAX` imports only the builtin syntax
   needed by its reachable grammar.
5. The facade supplies K's main module, while the target descriptor supplies
   the separately generated syntax module to pyk/kompile.
6. Generated K labels and locations map back to `crate::expr::add` and its KRS
   spans.

Moving the `use`, aliasing `Int`, or reordering source files cannot alter the
theory. Removing the builtin application removes its semantic K import after
dead import linting, but importing an unused name never changes behavior.

## What this resolves

The architecture now has clear answers for the previously underspecified
areas:

- K's file/module graphs are generated, not surfaced as a second module
  language.
- Rust `use` retains Rust meaning; semantic composition is explicit at the
  crate/facet target level.
- Syntax and semantics are separated by generated roles without forcing KRS
  authors to maintain `FOO-SYNTAX` mirrors.
- Builtins are versioned compiler-sysroot bindings to K modules and hooks, not
  copied implementations.
- Backend differences use Rust cfg and lower to K's concrete/symbolic modules
  where exact.
- One lock pin unifies K, pyk, builtins, KAST adapters, and backend artifacts.
- Stable package namespaces and explicit generated symbols make pyk APIs and
  differential tests robust against K's default mangling.
- Modern kdist/pyk integration is generated from the KRS manifest rather than
  recreated by every semantics project.

## Remaining prototype questions

No conceptual choice here blocks a compiler architecture. Five bounded probes
should precede freezing exact spellings:

1. **Generated module visibility.** Compile a two-crate fixture with public
   program syntax, public administrative constructors, private constructors,
   and dependency rules. Confirm on both LLVM and Haskell that the proposed
   direct/private imports parse every generated rule, expose only the selected
   program grammar, and still compose dependency semantics.
2. **Builtin registry.** Generate bindings for `BOOL`, `INT`, `MAP`, `LIST`,
   `SET`, `BYTES`, `STRING`, `K-EQUAL`, and `ML-SYNTAX` at one K pin. Compare
   their exposed signatures/attributes with parsed KAST and compile one use of
   every exposed operation on each supported backend.
3. **Facet selection.** Port IMP's `expr`, executable, LLVM-library, and
   verification targets to one manifest. Decide whether `root` plus features
   is sufficient or whether a small explicit `compose = [...]` list is needed.
4. **Generated kdist bridge.** Build the same target through `krs build` and
   `kdist build`; require identical source and kompiled artifact hashes after
   path normalization, and verify that source-map/symbol metadata is usable
   from pyk.
5. **Raw K dependency packaging.** Link one small external `.k` package by
   locked content hash, deliberately introduce a module and symbol collision,
   and ensure the diagnostic identifies both KRS/dependency origins before a
   backend is run.

These probes decide emitter details, registry coverage, and manifest syntax.
They do not reopen the central separation between Rust name resolution, K
theory composition, and generated K organization.

## Sources inspected

- all current KRS draft and R1-R8 investigation reports, especially R2's
  crate-wide sort closure, R4's hybrid grammar, R6's `.k` boundary, R7's
  builtin term spelling, and R8's pinned differential oracle;
- `good-k.md` and the modern IMP, KWasm, and KMIR repository layouts;
- IMP's `expr.k`, `calc.k`, `imp.k`, `imp-verification.k`, kdist plugin,
  pyk wrapper, `pyproject.toml`, and `deps/k_release`;
- KWasm's syntax/semantics module families, backend targets, literate selectors,
  kdist plugin, and K 7.1.329 pin;
- KMIR's `*-SORTS` cycle-breaking modules, configuration/runtime structure,
  backend targets, kdist/pyk use, and K 7.1.337 pin;
- the K user manual sections on files/modules, public/private imports and
  syntax, module `[symbolic]`/`[concrete]`, symbols, functions, tokens, and
  hooks;
- K's `domains.md` builtin modules, including concrete/symbolic alternates and
  private imports; and
- K frontend `ParserUtils`, module signatures/import visibility, and R6's
  outer-KAST/Kore boundary findings.
