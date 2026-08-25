# M4 complete-IMP implementation preflight

## Status and scope

This is a read-only implementation preflight made on 2026-08-20, except for
this report. It does not claim that M4 is implemented. The concurrent M3D
claim lane owns the claim implementation and `tests/m3d/**`; this report does
not modify or validate that live work.

The M4 target is the one in
[`draft/implementation-plan.md`](../../implementation-plan.md): one complete,
ordinary Rust IMP package, one resolved Definition IR, both source and native
lowerings, and the full layered R8 differential gate. M4 is not a fourth
incremental language slice and must not pass by concatenating the M3 PASS
messages. It needs a fresh complete-package gate whose two frontend routes
start from the same collected bundle.

## Executive result

M4 can reuse almost all behavioral oracle inputs without copying them:

- M3A owns expression parse/unparse and concrete evaluation;
- M3B owns state initialization, maps, exact execution traces, stuck states,
  and the division diagnostic;
- M3C owns complete IMP control parsing, all 187 trace states, 16 search
  frontiers, and eight bounded infinite-loop states;
- M3D owns four simplifications, static adjunct behavior, selected proof
  claims, a depth-zero residual frontier, and source/definition diagnostics;
  and
- the M3C native KORE investigation owns the only reviewed native/reference
  structural compatibility policy currently demonstrated end to end.

What does not exist is release-blocking: there is no complete Rust-authored
M4 package, M4 pin manifest, combined source-definition comparator, complete
native/reference KORE comparator, full proof runner for KRS output, stable-name
move fixture, or four-boundary diagnostic fixture. The M3D declarations are
currently split among a green M3C copy, an intentionally staged `surface`
package, and focused executable slices. They are valuable source material,
not a complete release package.

M4 must begin only after the active M3D claim slice is green through
collection, both IRs, `.k`, native adaptation, native Haskell-compatible KORE,
and the frozen selected proof outcomes. In particular, a passing `cargo check`
of the claim fixture is not that gate.

## Evidence that exists and can be reused

### Frozen external sources and tool pins

The following are already hash-checked by the existing strict verifiers:

| Evidence | Existing authority | Observed pin |
| --- | --- | --- |
| Reference K | `tests/m3a/pins.json` through `tests/m3d/pins.json` | 7.1.337, commit `4a46d1231473b599c699160132fd6e76a5c46406` |
| Native frontend | `tests/m3a/pins.json`, Cargo locks, local checkout | `k-rust` 0.3.0, commit `58f33885b736148dae189623d1aac989ce9be475` |
| Modern IMP | `tests/m3b/pins.json` through `tests/m3d/pins.json` | commit `683a773418add3bcae8ded47c2b24e94494e1988` |
| KAST envelope | all Python normalizers | exact KAST v4 |
| Rust package contract | root and authored manifests | edition 2024, MSRV 1.88, locked Cargo graph |
| Current serialized KRS boundary | `ProtocolVersion::CURRENT`, `IrSchemaVersion::CURRENT` | protocol 11, semantic/Definition schema 6 |
| Sidecars | `crates/krs-compiler/src/sidecar.rs` | schema 2 |

The exact upstream source files should be read in place, not copied into M4:

- `../inspirations/runtimeverification/imp-semantics/src/kimp/kdist/imp-semantics/expr.k`;
- the adjacent `calc.k`, `imp.k`, and `imp-verification.k`;
- `../inspirations/runtimeverification/imp-semantics/examples/specs/imp-simple-spec.k`;
- and the adjacent `imp-sum-spec.k`.

Their hashes already appear in `tests/m3d/pins.json`. The M4 pin manifest
should repeat those hashes as inputs so one M4 result is auditable without
inferring a transitive pin, while the canonical input remains the upstream
checkout.

The current strict verifier hashes are also reusable pins:

| Verifier | SHA-256 |
| --- | --- |
| `tests/m3a/verify.py` | `8cf21899e30a9a6f41e13b4310989ee535314907954e50df9c9f325bee6348f9` |
| `tests/m3b/verify.py` | `08401de91efba5c39456e094295643b36504a123801c6db5d421667b5762ea05` |
| `tests/m3c/verify.py` | `9ef82c970a37128ac7b445fae30ee99590d56ae8a8f66190cf62afbcd4e1358b` |
| `tests/m3d/verify.py` | `2ed14f41b39cf95fdfd132d1fa675c3d550375c75499d78711a2c901d023bc9f` |

The M4 runner may import fail-closed helper functions from these scripts, as
the M3B/M3C Rust-authored runners already do, but it must verify these hashes
first. It must not mutate their module constants or pins to make KRS output
pass.

### Object-language and behavioral oracles

The exact reusable inputs are:

| Layer | Reusable paths and behavior |
| --- | --- |
| Expressions | `tests/m3a/corpus/**`, nine accepted trees, two syntax rejects, two parsed-but-stuck type cases, and the documented unary `- 1` unparse mismatch only |
| State | `tests/m3b/corpus/**`, five accepted programs, 51 depth-indexed configurations, two syntax rejects, two stuck states, and division-by-zero hook failure |
| Control | `tests/m3c/corpus/**`, eight accepted programs, 187 configurations, 16 search frontiers, eight live infinite-loop bounds, four syntax diagnostics, and three stuck states |
| Static | `tests/m3d/corpus/static-evaluation.imp`, expected environment `x = 6, y = 0` |
| Proof | upstream `imp-simple-spec.k`, upstream `imp-sum-spec.k`, and `tests/m3d/claims/static-spec.k` |

The M4 runner should consume these paths directly through a checked corpus
manifest. Duplicating the files would create two sources of truth and defeat
the collision check already present in `tests/m3d/verify.py::verify_pins`.

### Rust-authored source fixtures

The closed complete operational IMP source is
`tests/m3c/rust-definition/src/lib.rs`. Its SHA-256 is
`8703da529c7e2049f16cadb262f36d1c5f190064c4fd7346f45009ae327c5b3f`;
`tests/m3d/rust-definition/src/m3c.rs` is currently byte-identical. The M3C
production runner freezes 83 descriptors with kind counts
`5 sort / 21 constructor / 29 grammar / 1 configuration / 27 rule`, 27
emitted productions, 27 emitted rules, 57 symbol rows, and 471 source rows.

The M3D source material is disjoint and must be assembled deliberately:

- `tests/m3d/rust-definition/first-slice/src/main.rs` demonstrates total and
  partial functions, equations, and equation priority;
- `alias-slice/src/main.rs` demonstrates the static alias production/clause;
- `context-slice/src/main.rs` demonstrates `m3d_eval` selected by
  `M3dTwice`'s named `seqstrict`;
- `simplification-slice/src/main.rs` spells the four exact IMP
  simplifications and checks a guarded/priority probe;
- `claim-slice/src/main.rs` is the live focused source for `branching`,
  `sum-loop`, and circular `sum-spec`; and
- `surface/src/lib.rs` spells five static adjunct claims plus `addition-1`
  and `addition-var`, but those declarations lack the explicit labels now
  required by the claim contract and are not an acceptance fixture.

The focused slice executables depend directly on compiler/IR/native crates to
inspect intermediate values. The release package must not. Like M3A-M3C, its
normal dependencies should contain only the renamed author-facing facade:

```toml
[dependencies]
k = { package = "krs", path = "../../../crates/krs" }
```

Compiler inspection belongs in the external M4 runner.

### Existing native structural proof

`draft/investigations/native-kore-m3c/src/main.rs` parses KORE with the pinned
public `k-rust` AST and compares sentence multisets. The reviewed M3C closure
is:

```text
alpha + labels + named-projector policy
reference=1069 actual=1069 missing=0 extra=0
```

The native M3C KORE pin is
`bebdda37e31c862b60faf380f44bcdc38b5bf049288bdbb01a385bc6ad599877`.
This tool is reusable code, not yet the M4 gate: it is hard-wired to one module
and its `has_named_projection` filter is broader than the final policy stated
in its report. M4 must classify complete symbol/equation projector pairs,
prove they are closed and unused by every retained sentence, and fail on a
lone projector declaration, equation, or retained reference.

## Proposed `tests/m4` tree

Create this tree only after M3D claim closure:

```text
tests/m4/
  README.md
  pins.json
  corpus.json                    # paths + hashes of reused M3A-D/upstream inputs
  verify.py                      # ordered top-level gate, no semantic normalization here
  oracle/
    source_definition.py        # fail-closed parsed/compiled KAST projection
    behavior.py                 # imports frozen M3A-C helpers after hash checks
    proofs.py                    # source proof status/frontier/constraint comparison
  native/
    Cargo.toml
    Cargo.lock
    src/main.rs                  # productionized KORE multiset comparator
  rust-definition/
    Cargo.toml
    Cargo.lock
    .gitignore
    README.md
    src/lib.rs                   # one ordinary complete package
    src/imp.rs                   # owned copy of the closed explicit M3C source
    src/verification.rs          # four IMP simplifications
    src/static_adjunct.rs        # function/equation/alias/context stress surface
    src/claims.rs                # labeled proof corpus; feature-independent
  compatibility/
    stable-names/
      baseline/
      private-move/
      public-move/
      public-move-pinned/
    diagnostics/
      rust-expansion/
      krs-analysis/
      k-frontend/
      backend-capability/
```

`README.md`, `pins.json`, `corpus.json`, and `verify.py` are root-integration
files. Lanes should not edit them concurrently. Generated `target/` or
`*-kompiled/` directories must not be checked in.

### Complete package assembly

Use one Cargo package named `krs-m4-complete-imp` with namespace
`KRS-M4-COMPLETE-IMP`, one `main` definition facet rooted at `crate`, edition
2024, `rust-version = "1.88"`, `publish = false`, warnings denied, and its own
`[workspace] resolver = "3"`. `src/lib.rs` should declare the four modules
above and publicly re-export only the intended object-language API.

`src/imp.rs` should begin as an owned copy of the closed M3C source rather
than `#[path]`-including another milestone fixture. This makes the M4 package
self-contained and lets the stable-name tests move declarations without
mutating earlier evidence. The M4 source-contract test must reject
`include_str!`, `include_bytes!`, `raw_k!`, filesystem/process access, copied
generated artifacts, and any dependency on `krs-compiler`, `krs-ir`,
`krs-k-rust`, or a handwritten K definition.

`verification.rs` owns exactly the four unprioritized simplifications in
upstream `IMP-VERIFICATION`. `static_adjunct.rs` owns the separately identified
stress surface from `tests/m3d/fixtures/static-adjunct.k`; it must never be
normalized into the upstream IMP definition. `claims.rs` owns exact labels and
claim meaning, but does not invent a second claim for the depth-zero run.

The minimum already frozen claim set is ten authored claims:

- `addition-1`, `addition-var`, `branching`, `sum-loop`, and `sum-spec`;
- `total-equation`, `partial-equation`, `explicit-priority`, `static-alias`,
  and `context-alias`.

`addition-depth-zero` is an invocation of `addition-1` with proof depth zero.
The five adjunct claims should be selectable individually even though the M3D
oracle currently proves their module as one run.

The wording in `tests/m3d/README.md` also assigns the *complete proof corpus*
to M4. Treat that literally: after the selected ten are green, add all 13
claims in upstream `imp-simple-spec.k` and both claims in
`imp-sum-spec.k`, for 15 upstream claims plus the five adjunct claims. This
adds real surface beyond the current focused claim slice:

- `addition-2` (two concrete `Id` keys and an entry-bearing environment);
- whole-map anonymous/existential forms in `branching-program`;
- nested/dead-code branching and typed `Stmt` binders;
- delayed while cut rules and map rewrites;
- `.Map => entries` in `sum-N`;
- negative integer spelling in the BMC and sum specifications; and
- the four-map-entry, conjunctive, circular `two-sum-spec` claim.

Freeze reference outcomes for those ten previously unpinned upstream claims
in `tests/m4/pins.json` before requiring KRS equality. Do not silently reduce
“complete proof corpus” back to the five selected M3D hashes.

## Differential gates and required ordering

The top-level runner should stop at the first failed layer and print the layer
name. Run gates in this order:

1. **Input/tool preflight.** Check every source/verifier hash, exact Git
   revisions, K/KAST/native versions, Cargo locks, MSRV declaration, and the
   M4 corpus manifest. Reject ambient mismatches.
2. **Ordinary Rust package.** `fmt`, `check`, Clippy, docs, tests, and the
   rust-analyzer probe. Assert facade-only dependencies and no fallback.
3. **KRS frontend determinism.** Run `krs check` twice, `expand` twice,
   `emit-k` twice, and native `build` twice for each supported backend.
   Snapshot and hash the descriptor bundle, semantic IR, Definition IR,
   emitted K, symbol map, source map, native adapted Definition projection,
   and KORE artifacts. Registration order must be reversed in an in-process
   contract fixture as the focused M3D slices already do.
4. **Source-definition structure.** Compile the upstream baseline and emitted
   K with the same reference pin and compare fail-closed normalized
   `parsed.json` project modules. Then compare the compiled project projection.
   This gate precedes behavior; M3C's separate generated sentence counts are
   not a substitute for structural equality.
5. **Native/source structure.** Compare the adapted native source Definition
   against Definition IR, then compare native/reference KORE sentence
   multisets under only the reviewed policy below. Check LLVM and Haskell
   dialects separately and retain `Sentence::Claim` as KORE claims.
6. **Parser/unparser.** Run every accepted/rejected M3A-M3C input against both
   source definitions. Compare full terms, rejection class/range, and exact
   unparse output. The single signed-integer M3A mismatch is allowed only for
   the exact existing input and reference behavior.
7. **Concrete behavior.** Compare exact rewrite counts, normalized final
   states, all 51 M3B and 187 M3C depth states, stuck cases, division failure,
   and static adjunct execution.
8. **Search.** Compare normalized result sets, not enumeration order, for all
   16 existing frontiers and the eight live infinite-loop bounds. Include
   constraints in result identity when symbolic search is added.
9. **Proof.** Compare claim KAST first, then proved/failed/incomplete status,
   normalized terminal/frontier constraints, and representative applied user
   labels. Re-run `addition-1` at depth zero and require the existing residual
   frontier rather than accepting any exit 1.
10. **Compatibility and diagnostics.** Run stable-name move cases, the four
    diagnostic boundaries, clean-checkout reproduction, and byte-for-byte
    reruns last. These are part of the M4 release gate, not cleanup.

Behavior may be parallelized within one layer, as M3C does with
`KRS_M3C_ORACLE_WORKERS`, but layers must remain serial so a structural failure
cannot be obscured by a later behavioral PASS.

## Compatibility policy to freeze

### Parsed and compiled KAST

Start from R8 and the current M3 normalizers:

- select explicitly enumerated project modules;
- remove only `Source`, `Location`, parser-production provenance, digest,
  content-start, and generated unique-ID metadata enumerated for K 7.1.337;
- sort only imports, modules, attributes, sentence collections, and grammar
  group members whose model is set-valued;
- map every authored KRS production/rule label to one explicit baseline label;
- alpha-normalize generated/anonymous variables by occurrence, kind, and sort;
- retain productions, sorts, semantic attributes, cells, initializers, rule
  and claim bodies, `requires`, `ensures`, priorities, simplification,
  circularity, and all binder sorts; and
- fail on an unknown node, field, attribute, label, sort, arity, or envelope.

Do not require raw `parsed.json` equality. The emitted KRS definition is one
flattened project module while modern IMP uses layered syntax/rule modules;
compare a semantic projection with an explicit origin-module mapping.

### Native/reference KORE

The accepted M3C policy is the maximum starting allowance:

1. remove only enumerated metadata attributes and canonicalize attribute
   order;
2. alpha-normalize variables consistently within each sentence while
   preserving element/set kind and sort;
3. normalize labels through an explicit table (current rule-label
   qualification should already agree); and
4. exclude only complete, closed, unused named-field projector
   symbol/equation pairs introduced by the structured native adapter.

No `cool-like` exception is allowed. No generic `project:*` prefix filter is
allowed. M4 must extend projector ownership to new M3D fields and assert that
no retained axiom or claim references an excluded symbol. Sentence
multiplicity is semantic and remains part of equality.

Claims need additional structural checks: native source uses
`Sentence::Claim`, KORE uses `kore::ast::Sentence::Claim`, the body is an
implication, `branching` scopes its existential over RHS/ensures, all-path
claims do not acquire a fake all-path attribute, one-path coverage retains
`one-path`, `sum-spec`/`two-sum-spec` retain circularity, and no claim carries
rule/equation priority.

### Behavior, search, and proof

- Explicit production and freezer maps may normalize KRS-generated names to
  baseline names. Unknown project/freezer names fail.
- Search results are sets of normalized `(state, constraint, depth)` values;
  enumeration and thread completion order are ignored.
- Proof variables are alpha-normalized by name occurrence and sort. Unknown
  proof KAST nodes fail.
- Semantic proof evidence is status, terminal/stuck frontier count,
  constraints, and selected user labels. KCFG node numbers, solver timing,
  simplifier step counts, and generated freezer names are informational only.

### Stable names

The documented policy is in R10: emitted public identities derive from K
namespace plus canonical Rust item path; package version, local `use` alias,
backend, checkout path, and generated module partition do not participate.
A public path/name change is breaking unless an explicit emitted symbol keeps
the old identity. Moving a private item may change its internal
`StableItemId`, but must not change any public symbol or downstream artifact.

Current production blockers are visible in the source: `StableItemId` carries
module path and name, but descriptors do not serialize item visibility, and
there is no implemented author-facing `#[k::symbol("...")]` override found in
the parser/macro/compiler path. M4 therefore needs both representation and
fixture work before it can satisfy the implementation-plan move gate.

The four cases under `compatibility/stable-names` should assert:

- private move: internal IDs/source map may change; public symbol projection,
  parser terms, and public KORE symbols do not;
- public move: the public symbol diff is detected and classified breaking;
- pinned public move: the explicit symbol preserves the baseline public
  symbol while source provenance moves; and
- all cases: absolute path, Cargo package version, backend, and collection
  order never change the emitted identity.

## Native/source proof harness integration

The source proof route exists: `tests/m3d/verify.py::prove` compiles a fresh
Haskell definition, invokes pinned `kprove`, emits spec JSON, and fail-closed
normalizes claim and result KAST. Reuse this logic after substituting only the
KRS-emitted definition/spec modules and explicit label mapping.

The native route currently proves structure, not proof execution.
`krs build --backend haskell` writes `definition.kore`,
`syntaxDefinition.kore`, and `macros.kore`; `k-rust` stops at KORE artifacts,
and no production KRS command feeds those files into a Haskell backend or
`kprove`. Therefore M4 must not report “native proof outcomes match” merely
because native claims compile.

The honest M4 integration is two-stage:

1. require native/source claim AST and KORE structural equality before any
   proof runs; and
2. either add a pinned external Haskell-backend consumer for native KORE and
   compare its proof outcomes, or explicitly scope v0.1 proof execution to the
   emitted-source route while treating native proof execution as a typed
   capability gap.

The implementation plan says selected proof claims have the same status, so
the first option is the stronger release interpretation. The root should
freeze this decision before declaring M4 complete; the harness must not
silently fall back from native to source compilation.

## Diagnostics and source-map release tests

M4 requires one intentional failure at each boundary, with an exact authored
Rust token/range and a stable layer/code classification:

| Boundary | Reuse | M4 addition |
| --- | --- | --- |
| Rust expansion | macro negative fixtures and `crates/krs-macros/tests/lsp_probe.py` | one complete-package malformed attribute/term and rust-analyzer diagnostic range |
| KRS analysis | M2 negative collection cases and focused M3D invalid descriptor mutations | one cross-item complete-IMP error reported by `krs check` at the authored token, with no generated collector path |
| K frontend | M2 generated-range remap plus M3 induced `.k` diagnostics | mutate one generated M4 term, map the K `Location` through `sources.json` to the exact Rust token |
| Backend/capability | typed `DefinitionCompileError` and `FrontendDiagnostic` in `krs-k-rust` | one unsupported backend/profile or proof construct with stable stage/code and authored origin |

The native wrapper already preserves renderer-independent code, message,
source, and location, but `krs-cli` currently formats native errors as text and
does not map every frontend/backend diagnostic through the emitted/source or
native-origin sidecar. That translation and a raw-generated-path prohibition
remain M4 blockers.

## Remaining surface and compiler blockers

These are observed gaps, not speculative redesigns:

1. **Active claim closure.** `tests/m3d/rust-definition/claim-slice` is owned by
   the current M3D lane. Its checked-in `CHECKPOINT.md` still records a missing
   `claim_ensures_path#0` provenance anchor, while the live source contains
   later full-layer assertions. Re-audit the checkpoint after that lane lands;
   do not infer completion from either file alone.
2. **Addition and adjunct claims.** The focused executable contains only
   `branching`, `sum-loop`, and `sum-spec`. `addition-1`, `addition-var`, and
   all five static adjunct claims remain only in the staged surface, without
   the exact explicit labels required by the current claim contract. M4 needs
   them in a green executable package and proof matrix.
3. **Complete upstream proof corpus.** Ten upstream claims beyond the selected
   M3D five have no KRS-authored fixture or pins. Whole-map anonymous/
   existential forms, `addition-2`, typed statement binders, negative literal
   spelling, multi-entry map rewrites, conjunction, and `two-sum-spec` must be
   proven representable or diagnosed as typed capability gaps.
4. **Exact IMP format control.** The M3C README documents that K's `% ` escaped
   format-space control is rejected by the structured-format parser and an
   ordinary space is emitted instead. M4 exact unparse equivalence must either
   implement `% ` or pin a narrowly demonstrated semantically identical
   compatibility rule; the current source-level mismatch cannot be forgotten.
5. **No assembled package.** The green M3D root is deliberately just the M3C
   copy. Focused slices each carry their own partial theory and direct compiler
   dependencies. A facade-only complete package and deterministic aggregate
   counts/pins must be built.
6. **Source-definition equality.** M3C compares behavior modulo explicit
   production/freezer maps and checks generated definition counts, but it does
   not establish normalized full source-structure equality between layered
   modern IMP and the flattened KRS module. M4 must.
7. **Native KORE comparator.** The investigation tool is not a permanent test,
   covers only M3C, and must tighten its named-projector implementation before
   adding functions, aliases, contexts, simplifications, and claims.
8. **Native proof execution.** Native Haskell-dialect KORE generation exists;
   backend proof orchestration does not. This needs either integration or an
   explicit typed release limitation.
9. **Stable-name visibility/override.** Visibility is not in the serialized
   descriptor contract and no public explicit-symbol override is implemented,
   so private/public move behavior cannot yet meet the documented policy.
10. **Supplemental toolchain lock.** No `Krs.lock` exists. `Cargo.lock` plus
    JSON test pins provide evidence but do not yet fulfill the v0.1 lock
    contract tying KRS schema, builtin registry, `k-rust`, K/pyk, and backend
    versions together.
11. **Diagnostic translation.** Native diagnostics are structured inside the
    adapter, but the CLI/user-facing mapping back to authored Rust across all
    four boundaries is not a complete, tested contract.
12. **LSP complete-package evidence.** Existing probes cover earlier macro
    shapes. Claims, binders, Id tokens, maps, context aliases, simplifications,
    and explicit stable symbols need diagnostic/navigation coverage in the
    complete package.

Unsupported M3D adjuncts deliberately excluded by the frozen oracle
(`anywhere`, anonymous `#fun`, global-configuration functions, set/fresh
variables, `symbolic`, `concrete`, and `owise`) are not automatically M4 IMP
blockers. They become blockers only if one of the 15 upstream proof claims
actually needs their meaning. `anywhere` remains Haskell-incompatible in K
7.1.337 and must be a typed capability diagnostic, never dropped.

## Commands for the eventual gate

Run the frozen independent inputs first:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tests/m3a/verify.py
PYTHONDONTWRITEBYTECODE=1 python3 tests/m3b/verify.py
KRS_M3C_ORACLE_WORKERS=1 PYTHONDONTWRITEBYTECODE=1 python3 tests/m3c/verify.py
PYTHONDONTWRITEBYTECODE=1 python3 tests/m3d/verify.py
```

Then check the complete ordinary package:

```bash
cargo fmt --check --manifest-path tests/m4/rust-definition/Cargo.toml
cargo check --locked --manifest-path tests/m4/rust-definition/Cargo.toml
cargo clippy --locked --manifest-path tests/m4/rust-definition/Cargo.toml --all-targets --no-deps -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --locked --manifest-path tests/m4/rust-definition/Cargo.toml --no-deps
cargo test --locked --manifest-path tests/m4/rust-definition/Cargo.toml
```

Exercise every production command from the repository root, using fresh or
KRS-owned output directories:

```bash
cargo run --locked -p krs-cli --bin krs -- check --manifest-path tests/m4/rust-definition/Cargo.toml --package krs-m4-complete-imp --definition main --backend llvm
cargo run --locked -p krs-cli --bin krs -- expand --manifest-path tests/m4/rust-definition/Cargo.toml --package krs-m4-complete-imp --definition main
cargo run --locked -p krs-cli --bin krs -- emit-k --manifest-path tests/m4/rust-definition/Cargo.toml --package krs-m4-complete-imp --definition main --output /dev/shm/krs-m4/emitted-a
cargo run --locked -p krs-cli --bin krs -- build --manifest-path tests/m4/rust-definition/Cargo.toml --package krs-m4-complete-imp --definition main --backend llvm --output /dev/shm/krs-m4/native-llvm-a
cargo run --locked -p krs-cli --bin krs -- build --manifest-path tests/m4/rust-definition/Cargo.toml --package krs-m4-complete-imp --definition main --backend haskell --output /dev/shm/krs-m4/native-haskell-a
```

Repeat `expand`, `emit-k`, and both `build` commands into `*-b` directories
and compare canonical bytes/hashes. The permanent single entry point should
then be:

```bash
TMPDIR=/dev/shm KRS_M4_ORACLE_WORKERS=1 PYTHONDONTWRITEBYTECODE=1 python3 tests/m4/verify.py
```

The M4 runner, not a human command sequence, should compile the upstream and
generated source definitions, invoke the native comparator, run all corpora,
and prove all selected/full-corpus labels. It should print the exact pin and
compatibility policy version in its completion summary.

## Disjoint Sol-agent implementation ownership

Keep the active M3D claim owner in place until its handoff is reviewed. After
root freezes the resulting protocol/schema and claim surface, use this wave:

| Lane | Exclusive owned paths | Deliverable | Must not edit |
| --- | --- | --- | --- |
| A: complete authored package | `tests/m4/rust-definition/**` | Facade-only complete IMP/static/claim package; exact source ledger; ordinary Rust and registration-order gate | production crates, M3 trees, M4 root/oracle/native/compat files |
| B: source/behavior/proof oracle | `tests/m4/oracle/**` | Fail-closed KAST normalizer; reused corpus runner; all proof statuses/frontiers; proposed pin values in handoff | M3 pins/verifiers, authored package, native tool, M4 root files |
| C: native/compat adversary | `tests/m4/native/**`, `tests/m4/compatibility/**` | Tight KORE comparator, projector closure proof, stable-name moves, four-boundary diagnostics | authored package, M3 trees, source oracle, production crates |

The root integrator alone owns `tests/m4/{README.md,pins.json,corpus.json,verify.py}`,
shared manifests/locks, any protocol/schema decision, and production-crate
repairs. If a production blocker needs a Sol follow-up, serialize it before the
wave and give one agent an exact non-overlapping crate set:

- format/provenance or remaining claim surface:
  `crates/krs-syntax/**` + `crates/krs-macros/**` only after the M3D owner is
  idle;
- stable identity/visibility: `crates/krs-ir/**` then a root integration pass,
  before package fixtures pin IDs; or
- native diagnostics/backend integration: `crates/krs-k-rust/**`, before Lane
  C pins KORE/diagnostics.

Do not run those three production repair sets concurrently: claim metadata,
stable identity, provenance, native origins, and canonical JSON all meet at
the shared descriptor/Definition boundary. The oracle lanes should remain
adversarial and request APIs rather than patching production code.

## M4 exit decision

M4 passes only when the complete facade-only package is reproducible from a
clean checkout, every artifact layer is deterministic, source and native
structure close under the written policy, all reused parse/execution/search
oracles match, the frozen selected claims and the explicitly scoped complete
proof corpus have pinned outcomes, stable-name moves behave as documented,
and each diagnostic boundary reports an authored range. Any unavailable tool,
native proof fallback, unknown normalized node, or unclassified structural
difference is a failed or explicitly blocked gate, never a PASS.
