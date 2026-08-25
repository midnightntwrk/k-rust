# Sol-agent implementation orchestration

This document turns the
[implementation plan](implementation-plan.md) into a repeatable multi-agent
workflow. It assumes one root integration agent and at most three concurrent
Sol implementation agents sharing the same filesystem.

The purpose of orchestration is not maximum fan-out. It is to shorten the
critical path while keeping interfaces, evidence, and semantic ownership
coherent.

## Roles

### Root integrator

The root agent owns:

- milestone decomposition and task dependency order;
- shared manifests, cross-crate interfaces, and authoritative design changes;
- non-overlapping file ownership assignments;
- resolving cross-lane API requests;
- workspace-wide formatting, tests, Clippy, and artifact review;
- deciding whether a milestone exit gate passed; and
- scheduling the next wave only after integration succeeds.

The root should continue useful integration or documentation work while lanes
run. It does not duplicate an active lane's implementation.

### Sol implementation lanes

Each Sol agent receives one bounded objective with:

- exact owned paths;
- required design and investigation inputs;
- explicit non-goals;
- expected artifacts;
- verification commands; and
- a completion-packet format.

Agents may inspect the entire workspace but edit only their owned paths. They
request shared-manifest or foreign-module changes from the root rather than
creating overlapping patches.

### Oracle lane

When a wave has a mature implementation API, one lane should be assigned to
adversarial fixtures and oracles rather than another feature. This agent owns
UI/LSP/differential tests and tries to disprove the implementation lane's
claims.

## Shared-filesystem rules

This workspace currently has no enclosing Git repository, so branch or
worktree isolation is unavailable. Coordination uses path ownership:

1. Only the root edits an existing shared file unless ownership is explicitly
   delegated.
2. Two live agents never own the same file glob.
3. New crates can be built concurrently when the root manifest uses a safe
   workspace glob; otherwise only the root adds workspace members.
4. An agent which needs a foreign change sends the root the requested API and
   reason, then continues on work that does not require it.
5. Agents never clean, delete, or mechanically rewrite another lane's files.
6. Root integration begins only after every lane has stopped editing.

If this project gains a Git repository, retain logical ownership and add one
worktree/branch per lane. Do not replace ownership with merge-conflict-driven
coordination.

## Task packet template

Every delegated task should contain:

```text
Objective
  One observable outcome, not a general topic.

Read first
  Exact design/report files and relevant existing APIs.

Owned paths
  File globs the lane may create or edit.

Do not edit
  Shared manifests, docs, or neighboring crates owned elsewhere.

Required behavior
  Invariants and edge cases which must hold.

Non-goals
  Adjacent work deliberately excluded from this lane.

Verification
  Commands and expected positive/negative results.

Handoff
  Changed files, decisions, commands/results, unresolved risks, and requested
  integration changes.
```

Prompts should link to authoritative files rather than paraphrase the whole
language design. A lane must still receive enough local context to avoid
re-deriving settled decisions.

## Completion packet

A lane is complete only when it reports:

1. files created or changed;
2. API and representation decisions made;
3. exact verification commands and results;
4. negative fixtures and why they fail;
5. remaining limitations or risks;
6. any requested changes outside owned paths; and
7. confirmation that no ownership collision occurred.

“Implemented successfully” without evidence is a status update, not a handoff.

## Integration loop

For each wave, the root performs:

1. **Preflight:** confirm the previous gate, freeze shared APIs needed by the
   wave, and assign non-overlapping ownership.
2. **Launch:** start no more than three Sol lanes. Use high reasoning for new
   semantic interfaces or risk spikes and medium reasoning for bounded fixture
   or mechanical adapter work.
3. **Monitor:** answer API questions, redirect scope drift, and record design
   findings. Do not continuously poll; agents send milestone/blocker messages.
4. **Handoff review:** inspect the actual files and evidence, not only the
   completion summary.
5. **Integration:** make shared-manifest/API adjustments, remove duplication,
   and ensure one authoritative representation per concept.
6. **Adversarial gate:** run all positive tests plus expected-failure fixtures,
   clean-build determinism, and relevant LSP/differential probes.
7. **Decision:** mark the gate passed, send targeted follow-up work to an
   existing lane, or schedule a repair wave. Never start broader language work
   with a failed foundational gate.

## Agent reuse

Keep completed agents available for follow-up tasks in their area:

- the IR lane reviews schema and stable-identity extensions;
- the provenance lane reviews every new macro/span shape;
- the native-adapter lane reviews `k-rust` API and capability changes; and
- later oracle lanes retain ownership of their fixture families.

This preserves local knowledge without letting any lane become the sole owner
of a cross-cutting semantic decision. The root remains the integration owner.

## Wave plan

### Wave 0: M0 foundations — active

Three independent risk lanes run concurrently:

| Lane | Owned result | Gate contribution |
|---|---|---|
| A: IR/contracts | Root workspace and `krs-ir` protocol, identity, provenance, host/serialized descriptor separation, deterministic JSON goldens | Stable serializable contract |
| B: provenance spike | Standalone stable proc-macro experiment and evidence report | Exact nested source-range strategy |
| C: native wrapper | `krs-k-rust` version/pin/capability wrapper and provisional bootstrap boundary | Native dependency isolation |

The root owns this orchestration document, cross-lane integration, and the M0
exit decision.

Wave 0 passes only when the production workspace verifies as a whole, the span
strategy recovers every required authored token, and the native dependency is
optional outside its adapter crate.

### Wave 1: M1 real-Rust host

Run in two subwaves so macros do not guess an unstable syntax API.

Wave 1A:

- Lane A owns `krs-syntax` ASTs/parsers and parser tests.
- Lane B owns the author-facing `krs` facade, host registration, and collector
  protocol implementation.
- Lane C owns Cargo-metadata selection and generated host-collector fixtures.

After the root freezes the parser and registration APIs, Wave 1B:

- Lane A owns `krs-macros` code generation for sort/constructor/rule.
- Lane B owns semantic collection validation and open-sort closure.
- Oracle lane owns UI, duplicate-name, determinism, dependency-retention, and
  LSP fixtures.

Wave 1 passes only when an external Cargo fixture uses the facade alone and
produces identical descriptor bytes on repeated clean builds.

### Wave 2: M2 dual-lowering smoke

- Lane A owns minimal semantic/Definition IR lowering and canonical `.k`
  emission.
- Lane B extends `krs-k-rust` for the same Definition IR and KORE artifacts.
- Lane C owns CLI commands, source/symbol sidecars, and the generated collector
  execution path.
- The next oracle task compares `.k`, source Definition structure, KORE, one
  execution, and induced diagnostic locations.

This wave is integrated one vertical node kind at a time. Neither adapter may
introduce route-specific semantic meaning.

### Wave 3: M3 explicit IMP slices

Use one vertical implementation lane, one neighboring-support lane, and one
oracle lane per slice rather than assigning horizontal compiler layers to
different agents.

For example, in expression/grammar Slice A:

- implementation lane owns token/production/precedence nodes through both
  adapters;
- support lane owns builtin catalog and parser/unparser plumbing; and
- oracle lane owns accepted/rejected programs, tree comparison, and LSP/UI
  fixtures.

Repeat this model for configuration/state, control/evaluation, and
static/verification slices. Shared IR changes are assigned to one lane at a
time and reviewed by the original IR agent.

#### Subwave 3A.0: expression contract gate

Slice A begins with one serial shared-contract lane owning only
`crates/krs-ir/**`. No parser, macro, compiler, adapter, or fixture lane edits
against an unfrozen schema. The gate must represent the actual `expr.k`
families rather than a second one-off smoke theory:

- declared and compiler-provided `Int`/`Bool` sorts through one typed sort
  reference used consistently by productions, variables, and terms;
- authored and compiler-provided applications through one typed symbol
  reference, with an enumerated pin-specific builtin identity rather than raw
  hook or label strings;
- token/regex productions and lexical precedence;
- nominal production groups plus typed bracket, avoid, format, strict, and
  seqstrict metadata;
- partial-order precedence and group associativity sentences; and
- mandatory nested provenance, deterministic serialization, and rejection of
  adapter-only IDs or unclassified raw attributes.

This advances the semantic/Definition schema deliberately. The descriptor
protocol advances only when the exact parser-owned payload and reference keys
are known; a schema version must not be bumped merely to reserve variants.
The contract gate uses a hand-built expression definition covering unary
negation, binary addition, Boolean conjunction, and parentheses, with
canonical-byte and invalid-shape tests.

After root freezes that representation, three disjoint lanes proceed:

| Lane | Ownership | Required result |
|---|---|---|
| A: host grammar surface | `crates/krs-syntax/**`, then `crates/krs-macros/**` after parser freeze | Rust-valid token, constructor metadata, bracket, precedence, and associativity forms produce an exact current protocol with parser-keyed provenance. |
| B: lowering and builtins | `crates/krs-compiler/**`, `crates/krs/**` only through root-approved facade wiring | The descriptor bundle resolves against a pin-specific `Int`/`Bool` catalog and emits canonical expression K with no raw-label escape hatch. |
| C: native and oracle | `crates/krs-k-rust/**` for the adapter, with a separate test-only oracle owner | The same Definition IR maps structurally to native source nodes; emitted and native parsing agree on accepted/rejected expression programs and trees. |

Root retains protocol/schema review, shared manifests and lockfiles, facade
re-exports, the explicit IMP expression package, and final integration. Slice
A is not complete when syntax merely emits: precedence, strictness-generated
contexts, builtin evaluation, parse rejection, unparse, diagnostics, and both
frontend routes must all pass.

### Waves 4-6

- M4 uses Sol agents primarily as adversarial oracle owners: source structure,
  KORE, execution/search, and proof can be compared independently.
- M5 fans out by genuinely separate boundaries: packaging/facets,
  builtins/capabilities, and kdist/pyk/cross-platform reproduction.
- M6 assigns one candidate ergonomic macro per lane, all compared against the
  frozen explicit IMP corpus and unchanged semantic-IR hash.

## Failure and escalation policy

An agent stops and messages the root before:

- changing a settled semantic invariant;
- introducing a new shared dependency or protocol version;
- editing another lane's owned file;
- adding an adapter-only interpretation;
- weakening an expected-failure test;
- using an unstable/compiler-private API in a production crate; or
- expanding scope beyond its task packet.

A failed experiment is a valid deliverable when the evidence is complete. The
root decides whether to choose a fallback, revise the plan, or run a focused
repair wave.

## Frozen M0 conversion invariants

These invariants are the integration contract for subsequent waves:

1. **Macro to `HostDescriptor`:** expansion emits rustc-valid declarations and
   process-local type-key functions plus validated, host-only line and
   Unicode-scalar-column anchors. It does not emit final byte ranges, read a
   local absolute path into an artifact, or assign global K meaning.
2. **`HostDescriptor` to `DescriptorBundle`:** only the host collector crosses
   this boundary. It checks the protocol, resolves Cargo package source,
   materializes content-addressed byte ranges using the shared parser, joins
   build-local type keys to stable item IDs, rejects stale or ambiguous
   anchors/references, and discards every `TypeId`, function pointer, and
   collection-order input before serialization.
3. **`DescriptorBundle` to semantic IR:** the compiler consumes only stable
   references. It rejects duplicate identities and unresolved references,
   computes open-sort and whole-theory relations once, and appends logical
   provenance frames without inventing source ranges.
4. **Semantic IR to Definition IR:** lowering is deterministic and
   target-neutral. It assigns generated modules and K labels in one shared
   pass, preserves explicit sentence kinds and origin stacks, and does not
   introduce frontend-specific semantics.
5. **Definition IR to `.k` or `k-rust`:** both adapters are structural
   consumers of the same checked meaning. Unsupported native capabilities fail
   explicitly. The `k-rust` route accepts only a definition prepared through
   an invariant-preserving boundary; the current parsed bootstrap remains
   test-only until upstream exposes that API.

Changing any of these invariants requires a design decision, appropriate
protocol/schema bump, and differential evidence. An adapter may not compensate
for a missing compiler check.

## Current orchestration record

### Wave 0 result

Wave 0 used three `gpt-5.6-sol` agents at high reasoning:

- `/root/m0_ir_workspace` delivered the workspace and `krs-ir` contracts;
- `/root/m0_span_provenance` delivered the stable proc-macro and LSP spike; and
- `/root/m0_krust_adapter` delivered the exact-pinned native adapter.

Integration review found that the initial protocol v1 incorrectly required
final content-addressed byte ranges in `HostDescriptor` and required fabricated
ranges on logical IR transformations. The IR lane repaired this as protocol
v2: host descriptors now carry validated pre-materialization anchors, while
serialized origin stacks distinguish concrete ranged frames from metadata-only
transformations. Protocol v1 was an unpublished M0 draft and is explicitly
rejected rather than silently reinterpreted.

M0 **passes**. Root verification covered 21 workspace tests, rustfmt, check,
Clippy with warnings denied, exact Git lock resolution for `k-rust`, reparsable
KORE smoke artifacts, typed native diagnostics, and the standalone provenance
suite including expected compiler failures and three rust-analyzer probes.

Known work intentionally carried into M1 is source lookup and hashing,
shared-parser anchor materialization, Cargo source canonicalization, and
centralizing provenance role names in `krs-syntax`.

### Wave 1A result

Wave 1A delivered `krs-syntax`, the `krs` host-registration facade, and
deterministic collector planning/generation. Integration added logical Cargo
source identities (`registry/Git`, `workspace`, or external `path`) to the
path-free canonical selection data. All workspace gates, the generated mock
collector, the renamed-facade/cross-crate registration fixture, and the M0
provenance suite pass.

The Wave 1B launch review found one remaining dependency in the interface
graph: a procedural macro cannot construct a final `StableItemId` because K
namespace and canonical Cargo source belong to Cargo-metadata selection.
Before macro implementation starts, `HostDescriptor` must therefore carry a
non-serializable package/item lookup identity which the collector joins to the
selected Cargo package. Only `DescriptorBundle` may contain the final
`StableItemId`. This is a focused M1 interface repair, not a new frontend.

That repair is now frozen as protocol v3. `HostItemId` and every host type
reference remain non-serializable; constructor fields and rule target
references carry build-local Rust type keys, while rule targets are keyed by
the shared parser's `(role, ordinal)`. Only the collector replaces those with
stable identities. Protocol v1 and v2 inputs are rejected. Root preflight
passed 48 workspace tests including doctests, rustfmt, workspace check, Clippy
with warnings denied, the standalone cross-package registration fixture, and
the full provenance verifier including all three rust-analyzer probes.

One final parser seam precedes macro launch: `krs-syntax` must expose
constructor field sorts and rule reference candidates with their protocol-v3
keys. In particular, skipped bare bindings retain their original AST ordinals;
they are not renumbered into short-name constructor guesses.

### Wave 1A task packets

Wave 1A freezes three interfaces before any procedural macro code is written:

| Lane | Owned paths | Observable result | Explicit non-goals |
|---|---|---|---|
| A: shared syntax | `crates/krs-syntax/**` | Span-preserving ASTs and parsers for the M1 sort, constructor, rule, and named-constructor term payloads; one canonical provenance-role catalog; positive and negative parser tests | Proc-macro expansion, global name resolution, open-sort closure |
| B: host registration | `crates/krs/**` | Author-facing core types and an explicit, replaceable registration boundary whose entries yield `HostDescriptor`; cross-module/dependency fixture proves intentional retention and unordered enumeration | Parsing payloads, converting to `DescriptorBundle`, semantic analysis |
| C: collector planning | `crates/krs-cli/**`, `tests/collector-planning/**` | Cargo-metadata package/facet selection plus deterministic generation of a host-only collector package which explicitly depends on and references every selected semantics crate | Running semantic collection, materializing provenance, user-facing command breadth |

All three lanes may request root manifest/dependency changes but may not edit
the root manifest. Lane C tests generation against a mock collector entry point
in its owned fixtures; it must not invent a second registration or descriptor
model while Lane B owns that interface.

After integrating Wave 1A, the root freezes parser and registration APIs and
launches Wave 1B for real proc macros, descriptor resolution/open-sort closure,
and adversarial UI/determinism/LSP oracles.

### Wave 1B execution packets

Wave 1B uses two implementation subwaves. This avoids asking the oracle lane
to encode unstable expansion details, while still testing the integrated
author experience before M1 is declared complete.

#### Subwave 1B.1: implementation

Both lanes use `gpt-5.6-sol` with high reasoning. They may inspect the whole
workspace, but their edit sets are disjoint:

| Lane | Owned paths | Observable result |
|---|---|---|
| A: procedural macros | `crates/krs-macros/**` | Real `#[sort]`, `#[constructor]`, `#[rule]`, and minimal `term!` expansions produce rustc-valid declarations plus protocol-v3 host registrations using only `krs-syntax` and `krs-ir` contracts. |
| B: collection/compiler | `crates/krs-compiler/**` | Caller-supplied Cargo package context converts unordered protocol-v3 host descriptors into a deterministic stable bundle, materializes provenance, resolves type references, and computes the minimal M1 open-sort relation. |

Lane A must:

- discover the renamed `krs` facade dependency rather than spelling a fixed
  crate path;
- preserve the original Rust item and use target-crate `env!` and
  `module_path!()` expressions at expansion time;
- obtain all accepted syntax, semantic reference keys, and authored anchors
  from `krs-syntax` rather than implementing a parallel parser;
- emit process-local `TypeId` key functions only for explicit Rust paths;
- diagnose unsupported placements and M1 rule shapes at the responsible
  authored token; and
- keep `term!` deliberately narrow. In particular, it must not pretend that a
  bare path's constructor-versus-binding meaning can be inferred by short
  name.

Lane B must:

- accept package contexts supplied by the Cargo-metadata/CLI layer; it must not
  run Cargo or infer a semantic namespace from an absolute path;
- canonicalize and match manifest-directory hints consistently, validate the
  `module_path!()` crate-root segment, then discard host-only paths;
- construct the only final `PackageId` and `StableItemId` values;
- join build-local `TypeId` values to declaration IDs before serialization;
- reparse source using `krs-syntax` to materialize exact byte ranges from
  line/scalar anchors, rejecting stale or ambiguous matches;
- reject protocol mismatches, duplicate item IDs, duplicate provenance or
  reference keys, unresolved references, and item-kind mismatches;
- deterministically order every set-valued result; and
- compute direct and transitive open-sort membership, including diamonds,
  without encoding it as Rust blanket-implementation coherence.

Neither lane may edit the root manifest, `Cargo.lock`, `crates/krs/**`,
`crates/krs-ir/**`, `crates/krs-syntax/**`, `crates/krs-cli/**`, or the draft
documents. Requests for those changes go to the root. Neither lane owns `.k`
or native lowering in this wave.

Each lane first runs its package-local format, check, test, doctest, and Clippy
gates with warnings denied. Its handoff includes positive and negative tests,
the exact commands/results, limitations, and requested cross-owned API edits.

#### Root integration checkpoint

After both lanes stop editing, the root:

1. inspects generated code and collection logic rather than accepting only the
   completion summaries;
2. adds the two crates to dependency wiring, re-exports macros from the
   author-facing facade, and updates `Cargo.lock` once;
3. resolves API requests without moving semantic analysis into macros or Cargo
   concerns into the compiler;
4. builds one tiny external package through registration and collection; and
5. runs workspace, standalone-registration, and provenance gates.

Only a compiling integrated author path freezes the API for the oracle lane.

#### Subwave 1B.2: adversarial oracle

One fresh high-reasoning Sol agent owns `tests/ui/**`, `tests/lsp/**`, and
`tests/definitions/m1/**` plus any self-contained test harness under `tests/`.
It may request but not directly make production changes. Its job is to try to
falsify the integrated M1 claims with:

- an external package that depends only on the renamed `krs` facade;
- accepted sort, unit/record constructor, simple rule, and `term!` cases;
- rejected attribute placement, payload, rule signature, path, stale-anchor,
  duplicate-ID, duplicate-reference, and unresolved-reference cases;
- identical short names across modules and dependency packages;
- explicit dependency retention and repeated clean collection with identical
  canonical bytes;
- multi-parent diamond closure and the blanket-implementation E0119
  counterexample documented as something KRS must not rely on; and
- rust-analyzer diagnostics, navigation, rename, and hover probes at the
  authored Rust surface.

The root triages oracle failures. Test defects stay with the oracle lane;
production defects return as focused follow-up tasks to the relevant existing
implementation agent. No expected failure is weakened merely to pass the
gate.

### Wave 1 exit procedure

M1 passes only after all of the following succeed from a clean integrated
workspace:

```text
cargo fmt --all -- --check
cargo check --workspace --all-targets --locked
cargo test --workspace --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
standalone registration fixture gates
stable provenance verifier, including rust-analyzer probes
M1 oracle suite and byte-for-byte repeated collection
```

The root then records the exact test counts, protocol version, supported M1
surface, deliberate restrictions, and remaining packaging risks here before
launching any M2 lowering work.
