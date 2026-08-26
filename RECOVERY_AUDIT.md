# KRS recovery audit and continuation plan

Updated: 2026-08-26 JST

## Decision

Use this directory as the development repository. Its signed recovery import
has now been reconciled forward into a green post-F7 baseline. Do not spend
more time trying to manufacture an exact checkout of `9d507b0`: the surviving
forensic routes have been exhausted, the missing top-level M3D oracle has been
functionally reconstructed and independently qualified, and the complete M4
gate passed twice back-to-back without source, pin, lockfile, environment, or
tool revision changes.

The implementation seams are reconstructed through the macro fixtures, compiler, CLI, native adapter, independent M3D oracle, and recovered M4 definition/proof packages.
Recovery archaeology is closed.

The active development objective is the known project end state, not reconstruction of intermediate worktree state and not qualification of representative slices.
Readable IMP and the initial KWasm, KEVM, and KMIR slices are signed authoring baselines.
They do not constitute complete ports.
Continue in this order:

1. preserve the complete IMP gate and the three fail-closed semantic gates as regression authorities;
2. complete the KRS KEVM port against the pinned `evm-semantics` source inventory and selected upstream behavior and proof suites;
3. complete the KRS KMIR port against the pinned `mir-semantics` source inventory and selected upstream behavior and proof suites;
4. close any remaining KWasm coverage after the KEVM and KMIR work, so all three ports satisfy the same explicit completion contract.

The canonical product definitions live in the standalone `semantics/` Cargo workspace.
`tests/kwasm`, `tests/kevm`, and `tests/kmir` own only external evidence, probes, revision pins, and fail-closed qualification gates.

## Authorities and path translation

These sources have different jobs:

1. `../recovery/` is the immutable forensic authority. Its evidence and
   archives must not be edited.
2. `krs.RECOVERY_PROVENANCE.md` describes how the 580-file extraction was
   assembled and the confidence of individual recovered files. Keep it
   unchanged.
3. This file records development decisions, current-machine observations, and
   the path to a usable repository.
4. `LAST_KNOWN_PROMPT.md` establishes the last completed packages and the next
   intended feature. It is not an additional source snapshot.
5. `../inspirations/runtimeverification/good-k.md` ranks the local K ecosystem
   checkouts as design and corpus references. It is not KRS recovery evidence
   and does not override the revisions pinned by KRS.

The provenance file was originally adjacent to an `evidence/` directory.
Because KRS has since been copied out as a sibling development repository, a
provenance reference such as `../evidence/krs-transcript-replay/` now resolves
to `../recovery/evidence/krs-transcript-replay/`.

## What the added evidence changes

The earlier audit was written before `../recovery/evidence/` was available.
Several of its recommendations are now obsolete.

| Earlier conclusion | Current conclusion |
|---|---|
| Search for the missing evidence tree | It is present under `../recovery/evidence/` and has been reviewed. |
| The stable macro expander was unavailable | An exact 6,300-line `fbccdc7` expander is present. The extracted 486-line variant was only an old clean-prefix replay and has now been replaced. |
| Sixty-seven clean-commit source paths might be absent | Most implementation paths were materialized from other evidence, but Phase 4 found that eight top-level M3D oracle files required by M4 were not transferred. Their historical Git identities survive; their blobs do not. The debug archive and built executable remain irrelevant generated artifacts. |
| Continue raw-object recovery before development | Targeted loose-object, pack-index, allocated-block, and retain-all unallocated scans are complete. No known recovery route remains worth blocking on. |
| Maintain two speculative active reconstruction lines | Preserve one exact import commit, then reconcile forward. The import commit and immutable evidence retain every alternative needed for comparison. |

The goal is now functional reconstruction with explicit provenance, not more
forensics and not a fabricated byte-exact Git history.

## Established facts

### Extraction integrity and completeness

- The authoritative archive is
  `../recovery/artifacts/krs-recovered-v2-20260824.tar.gz`, SHA-256
  `b7054652b7f1216101c2d00e50e6fd7eed92c645f6c47b1d53cc46b4c0cf6250`.
- Its authoritative ledger is
  `../recovery/evidence/krs-extract-ready-identities.tsv`, SHA-256
  `dd90603f687ec891b1cb4dc4eb18ac0ff00f46229625093d213c625ef902f1f8`.
- The root commit `c99f25a` matches all 580 ledger entries by SHA-256. No
  ledger path is absent or differs in that tagged import.
- `krs.RECOVERY_PROVENANCE.md` is deliberately outside that 580-file project
  ledger.
- `../recovery/evidence/krs-transfer-completeness-20260825.md` was useful for
  the initial transfer audit, but its claim that every authored test path is
  materialized is superseded by the executable M4 preflight described below.
  In particular, `tests/m3d/verify.py`, `pins.json`, and the reference corpus
  are absent.
- Outside the missing authored M3D oracle package, the two intentionally
  untransferred signed-tree paths are `kore-exec.tar.gz` and `test`, both
  generated/debug build artifacts. They are not reconstruction inputs.

The extraction problem is checkpoint coherence, not missing authored files or
random corruption.

### Local extras and transfer cleanup

All nested `PaxHeader` paths, `.playwright-mcp/`, `agent-sandbox-test/`, and
`agent-sandbox-test2/` have been removed from the development repository.
Their forensic counterparts remain in `../recovery/`. Commit `a48c597` adds
ignore rules for those artifacts, AppleDouble metadata, Python caches, and
build output.

The audit, last-known prompt, and provenance note are intentionally retained
outside the authoritative 580-file project ledger.

### Git state

This repository now has a new signed development history. It still has no
remote and deliberately contains no reconstructed original objects:

- `c99f25a` — signed 580-file recovery import plus the three recovery notes;
- signed tag `recovery-import-2026-08-25` — immutable comparison point;
- `a48c597` — recovery/session ignore rules;
- `adcf985` — exact stable `k-rust` adapter manifest;
- `60592d3` — exact `fbccdc7` macro-expander baseline;
- `cb033b8` — schema-9 IR tests and canonical goldens;
- `28b2f9d` — executable recovery audit and continuation plan;
- `82ec76f` — schema-9 compiler lowering, emission, and focused adjunct
  coverage;
- `302c765` — audit advancement to the native adapter seam;
- `43db2b4` — schema-9 `k-rust` adapter, KRS-owned preparation compatibility
  layer, focused adapter tests, and retained M3D fixture reconciliation;
- `3d2632e` — audit advancement beyond the adapter seam;
- `a53053b` — direct-evidence collision provenance recovery and restored CLI
  collector-planning qualification;
- `1ffb361` — recovered macro fixture inventory, initializer import hygiene,
  nonlinear-binding qualification, and missing negative-fixture
  reconstruction;
- `d741692` — recovery audit advanced to the qualification sequence;
- `24b6a64` — full workspace, MSRV, syntax/F7, and C7/Q8 qualification, with
  the missing M3D package isolated as the remaining source gap.
- `1546c2b` — independently reconstructed and qualified M3D oracle package.
- `95fc96d` — signed green post-F7 M4 recovery baseline.
- `5ff228f` — signed collector integration of the F7 source/trivia contract.
- `35b4ef6` — signed complete readable-IMP authoring milestone.
- `39022c8` — signed readable KWasm integer milestone.
- `04599da` — signed readable KWasm division/trap milestone.
- `70f0f13` — signed readable KEVM operational milestone.
- `44b1d74` — signed readable KMIR operational milestone.

Every new commit and the import tag verify against the configured ED25519 Git
signing key. Valid signed original commit objects survive in the evidence
repository, but their trees are incomplete and cannot serve as a checkout. Do
not recreate commits under the old IDs, graft partial object stores into this
repository, or describe the new root commit as an original historical commit.

### Proven project checkpoints

The recovered session establishes this sequence:

1. `a84bb688a80750829cca44c37b147802e3f204c9` —
   `Resolve readable precedence associativity`.
   This is the last checkpoint with a directly observed full green M4 run.
2. `3c4f0b9bbd354d332542f34473958d6640b84b3f` —
   `Settle formatter trivia architecture`.
   Documentation/evidence package; the worktree was reported clean.
3. `9d507b03c26105c82ad38f92a0d7fb776e2e0f6b` —
   `Add gap-classified source trivia facade`.
   The full `krs-syntax` suite and Clippy passed and the worktree was reported
   clean. A post-commit full M4 run is not visible.

After `9d507b0`, the session only explored the compiler collector and hit an
agent-routing glitch. No collector edit or later commit is evidenced. There
is therefore no unfinished collector patch to recover.

The post-C7 M4 result recorded immediately before the formatter packages was:

- 23 parses;
- 31 executions;
- 246 bounded-depth states;
- 16 searches;
- 8 rejections and one expected failure;
- 21 bounded proofs;
- 7 compatibility probes;
- evidence hash
  `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`.

## Important source decisions

### Syntax and F7

The F7 syntax work is strong recovery material:

- `crates/krs-syntax/src/trivia.rs` and
  `crates/krs-syntax/tests/trivia.rs` are complete;
- final exact `error.rs` and `lib.rs` are present;
- exact or strongly reconstructed rule/state-macro seams are present;
- 132 `krs-syntax` tests passed in the prior disposable audit.

Keep this work and repair forward. Do not roll the syntax crate back to an
older signed-tree subset merely to maximize matching hashes.

### Macro expander

Commit `60592d3` promotes the exact `fbccdc7` expander:

- current and exact evidence:
  `../recovery/evidence/fbccdc7-exact-commit-files/crates/krs-macros/src/expand.rs`,
  6,300 lines, SHA-256
  `280318732b52cec0e240c4e3c96b39a879eb0930ca625bb071bc1f1a71877cbd`;
- expected post-C7 stable pin:
  `63ef847cd73d8d6fb236f0baeb441c86d1b199142daa7eb17b93359976d24e2a`.

The exact file defines all 28 functions called by the recovered final
`crates/krs-macros/src/lib.rs`. Its two unit tests, Rust 1.88 check, and library
Clippy gate pass. Seven expander update events are recorded after the
`fbccdc7` commit time in
`../recovery/evidence/krs-transcript-replay/filechanges.tsv`. Their original
rollout payloads are not transferred as standalone patch files, but their
metadata and the final expected hash remain useful constraints.

Commit `1ffb361` completes functional macro recovery. It restores the exact
`fbccdc7` fixture runner (SHA-256
`6148a08697e1c0125ecfb7e7ace82837a9edd29deb2c8a4e80a42db8d400d6`), its
full negative-fixture manifest, and its full positive fixture, reconciled
forward only for the later `map![key -> value]` spelling. It also extends the
existing consumed-island import mechanism to bare `k!` and `map!` invocations
inside `#[init]`, so generated qualification retains author lint credit
without placing an allowance on authored imports.

`duplicate_binder` is intentionally a positive nonlinear-pattern fixture:
`term![Foo(value, value)]` introduces one binding with two occurrences. The
older runner's rejection expectation was stale and must not be restored.

Six negative fixture blobs named by the exact runner were absent from every
recoverable object store. Their original Git and SHA-256 identities remain in
the forensic ledgers, but their bytes do not. They are therefore explicitly
functional reconstructions: each exercises its original real macro path and
produces the pinned local diagnostic for malformed state reuse, wrapper/state
family mismatch, invalid labels, host-literal conditions, unbound condition
references, or result-only references.

The demonstrated macro gates are now:

- two unit tests, six fixture tests, and doc tests;
- positive fixture check, Clippy, execution, and deterministic repeat;
- the full negative diagnostic inventory, including real collection and
  type-identity cases;
- Rust 1.88 all-target checking;
- current-toolchain all-target Clippy with warnings denied.

The resulting expander does not match the expected post-C7 stable hash and is
not claimed byte-exact. Its behavior is qualified and its reconstruction
boundary is recorded; do not chase the final hash by regressing the fixtures.

### Cargo dependency seam

`Krs.lock` pins the current root `Cargo.lock` SHA-256 exactly, but the recovered
adapter manifest did not describe that graph. Commit `adcf985` restores the
exact stable path-style dependency with Z3 inference enabled.

The exact stable manifest is recoverable from command output in
`../recovery/evidence/krs-bash-events.jsonl`, event
`toolu_01E6c2pvU6U3vYsmM1TPW4Q3`. Extracting its complete section produces the
expected stable SHA-256
`dd61532f2c7426ad1fdab72414cfddcb14eb92e105d99ec8da035521a9405779`.
It uses:

```toml
k-rust = { version = "=0.3.0", path = "../../../inspirations/midnightntwrk/k-rust/crates/k-rust", default-features = false, features = ["z3-inference"] }
```

The sibling repository is now at the pinned commit. Its repository-level
workspace manifest enables the later `z3-sys/gh-release` feature, which would
add 155 downloader/archive dependencies and bypass the ambient Z3 provenance
frozen by KRS. The KRS lock is coherent only with that one external workspace
feature removed. The sibling root therefore has one explicit integration
override, `z3 = "0.20.2"`; the pinned `crates/k-rust` subtree remains byte
unchanged. With that override, full `cargo metadata --locked` succeeds and
`Cargo.lock` remains unchanged. Preserve this condition explicitly until KRS
vendors or otherwise owns its dependency topology.

### IR, compiler, and adapter

`crates/krs-ir/src/definition.rs` and `semantic.rs` are large compile-clean
transcript reconstructions with extensive direct-read corroboration. They are
not exact `9d507b0` blobs, but they preserve valuable later readable-language
work. Keep them as the forward model unless a stronger exact variant proves
both newer and coherent.

Commit `cb033b8` reconciles the old `m2_ir` and `m3_expression_ir` tests and
regenerates three empty/stale canonical goldens from validated schema-9
models. All 129 `krs-ir` tests pass on Rust 1.98 and Rust 1.88; the library
Clippy gate passes.

Commit `82ec76f` eliminates the compiler's 68-error schema seam by
reconstructing `lowering.rs` and `emit.rs` forward against the retained IR.
The compiler now handles classified grammar, typed subsorts, production
groups, precedence and associativity, builtin and declared terms, fixed and
nested configurations, simultaneous configuration rules, explicit and
default labels, conditions and priorities, context aliases, and typed claim
metadata. The claim/context acceptance slice covers HERE, `_B:Bool`,
`?N:Int`, `ensures`, circularity, one-path versus implicit all-path, and
generated ranges for distinct adjunct roles.

The demonstrated compiler gates are:

- all 62 active library/integration tests pass on Rust 1.98 and Rust 1.88;
- compiler Clippy passes with warnings denied on the installed Rust 1.98
  toolchain;
- both normally ignored M3B and M3C canonical-source tests pass under exact K
  7.1.337;
- `Cargo.lock` remains SHA-256
  `83c15d6a7b176cb465a7f79156449d41b3d33c7859bc7e89dd0f6fe9a14bbb8a`,
  still matching `Krs.lock`.

Rust 1.88 Clippy was not run because that rustup toolchain lacks the Clippy
component; its locked check and full compiler test suite pass. Do not install
or silently substitute a toolchain component merely to erase this recorded
environmental distinction.

Commit `43db2b4` reconstructs `krs-k-rust` against schema 9. The adapter now
preserves builtin and declared sorts/applications, map operations, full grammar
items and classified attributes, group precedence and associativity, legacy
and fixed/nested configurations, configuration variables and cell properties,
context aliases and strictness metadata, structured configuration rules, and
native claim sentences with binders, conditions, modalities, circularity, and
origin roles. Claims remain `k-rust` `Sentence::Claim` values rather than being
downgraded to rules.

The exact pinned `k-rust` revision predates the later upstream
`outer::prepare_definition` convenience API assumed by the displaced fixture.
KRS therefore owns one explicit compatibility layer: it asks the pinned public
loader to establish an embedded-prelude/bootstrap `LoadedDefinition`, applies
the selected backend filter, removes the empty bootstrap module, injects the
already-structured KRS modules, expands configurations, and resolves the graph.
It never parses emitted candidate `.k`. This is a pin reconciliation, not a
change to the sibling checkout and not evidence that the later API existed at
the frozen revision.

Adapter qualification is now demonstrated by:

- `cargo check -p krs-k-rust --lib --locked`;
- 12 adapter tests plus doc tests on the active Rust toolchain;
- the same 12 tests plus doc tests on Rust 1.88;
- current-toolchain `cargo clippy -p krs-k-rust --all-targets --locked -- -D warnings`;
- the retained M3D claim slice through native Haskell compilation, including
  maps/builtins, three claims, existential and anonymous variables, authored
  `ensures`, circularity, and implicit all-path behavior;
- the retained M3D context slice through preparation, `resolve_strict`, one
  generated context, `resolve_contexts`, one heat rule, one cool rule, and
  permanent compilation.

The retained fixtures used the obsolete recovered `map![key => value]`
spelling while the exact macro baseline accepts `map![key -> value]`; only
those map arrows and expectations tied to the recovered current emitter/native
pin were reconciled. These are explicit functional-reconstruction edits, not
portrayed as recovered original bytes.

Commit `a53053b` closes the CLI seam. Direct transcript evidence proves that
schema 9 retained `LoweringError::NameCollision::second_origin: OriginStack`;
the compiler now passes the authored second declaration's origin through every
collision preflight, and a focused test pins the exact reported origin. The
same commit restores the six collector-planning tests by reconciling fallible
canonical JSON, request-factory shadowing, and real Cargo library-target
metadata.

The CLI now passes its active and MSRV all-target checks, focused tests, and
Clippy gates. Production `check`, `expand`, `emit-k`, and native `build`
integration have also passed. A locked all-target workspace check passes after
the macro milestone. A stable-ledger mismatch remains a classification signal,
not authority to replace a later file wholesale.

### M4 ledgers

The current `tests/m4/pins.json` is the promoted post-C7 behavioral/proof
authority, reconciled to schema 9 and the recovered source path policy. It
contains 269 source identities, 23 parses, 31 executions, 246 bounded-depth
states, 16 searches, 21 proof outcomes, and seven compatibility probes. The
M3C helper pin is the independently recorded recovered digest
`4c0db024a7e302706b4ec97d7c4f87292277d31d66114f073dced994ab727bc7`;
the current `tests/m3c/verify.py` matches its recovered working-tree copy
byte-for-byte.

Source-ledger reconciliation is mechanical and fail-closed. The final recovery
refresh changed only the top-level `source_sha256` mapping. Behavior, proof,
corpus, toolchain, revision, and emitted-source artifact pins were not changed
to accommodate results. The native `definition.kore` pin changed only after
the KRS-owned `_GenN` sort-collision repair reproduced byte-identically, and
the compatibility report pin changed only after all seven corrected live
probes passed as one set. Any source edit makes this ledger stale again.
Produce a proposal with `tests/m4/refresh_source_ledger.py`, inspect the diff,
and run the checker before the next full M4 invocation. Never use source-ledger
refresh to bless a behavioral or proof difference.

## Current-machine prerequisites

Observed on 2026-08-25:

| Prerequisite | State |
|---|---|
| K checkout | Correct commit `4a46d1231473b599c699160132fd6e76a5c46406`; Pyk venv reports 7.1.337. |
| IMP semantics checkout | Correct commit `683a773418add3bcae8ded47c2b24e94494e1988`. |
| `k-rust` checkout | Correct detached commit `58f33885b736148dae189623d1aac989ce9be475`; root workspace has the documented system-Z3 integration override above. |
| Z3 | Correct, 4.12.5. |
| Ambient Rust | 1.98.0. |
| MSRV Rust | Correct, 1.88.0 installed through rustup. |
| MSRV Clippy | Not installed for the rustup 1.88.0 toolchain; the ambient 1.98 Clippy gate passes with warnings denied. |
| MSRV rustfmt | Not installed for the rustup 1.88.0 toolchain. Do not install it merely to erase this environmental distinction. |
| rust-analyzer | The host rustup proxy has no installed component. Use the ephemeral exact recovered analyzer at `/var/tmp/krs-rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/bin/rust-analyzer`, exposed by `/var/tmp/krs-ra-1.97.1-bin`; it reports `rust-analyzer 1.97.1 (8bab26f 2026-07-14)`. |
| K executables | Cached exact K 7.1.337, kore-exec 0.1.155, and LLVM backend 0.1.140 binaries verified directly; `kup shell` remains the preferred entry when network/cache configuration permits. |

The required Cargo registry dependencies are now present. Locked commands use
the frozen root lock without regeneration. The adapter enables
`z3-inference`, so local link and execution gates need the Nix Z3 library path
in `LIBRARY_PATH` and `LD_LIBRARY_PATH`; this is an environment requirement,
not an unavailable frontend capability or a reason to change dependency
topology.

On this machine the required directory is:

```text
/nix/store/bncr69nhmgvphbynb1a3g4a2jb9b8vj0-z3-4.12.5-lib/lib
```

Use `/var/tmp`, not `/tmp`, for M4 workspaces and set
`KRS_M4_ORACLE_WORKERS=1`; `/tmp` is a crowded tmpfs on this host.

## K ecosystem reference map

`../inspirations/runtimeverification/good-k.md` does not change Phases 0-4.
It clarifies which local repositories should inform reconstruction and which
should wait until the baseline is green.

### Immediate reconstruction references

- `runtimeverification/k/` is the implementation source of truth. Pyk lives
  inside this repository; consult its pinned source when K behavior or APIs
  are ambiguous.
- `runtimeverification/imp-semantics/` is the small source-language oracle and
  modern project-shape reference already used by M4. Its own
  `deps/k_release` is 7.1.318, while KRS deliberately runs its frozen source
  evidence under K 7.1.337. Do not silently substitute one pin for the other.
- `midnightntwrk/k-rust/` is the pinned native frontend/backend dependency and
  the most direct implementation comparison for the adapter seam.

These repositories may answer reconstruction questions, but they do not
justify changing a recovered KRS behavior or pin without KRS-local evidence.

### Post-baseline design and corpus ladder

The recovered post-F7 baseline is green.
Use the Tier 1 projects in this order:

1. `wasm-semantics/` (KWasm, K 7.1.329) supplies the first qualified real-language authoring baseline;
2. `evm-semantics/` (KEVM, K 7.1.337) is the next full-port authority for scale and production-semantic complexity;
3. `mir-semantics/` (KMIR, K 7.1.337) follows as the full-port authority for fresh K conventions and larger multi-cell and rule-shape stress;
4. `kontrol/` (K 7.1.337) remains reserved for prover-as-a-product, Pyk orchestration, and CLI workflow design rather than KRS core semantic coverage.

Check each repository's `deps/k_release` before borrowing a construct. Copy
modern semantics and testing patterns from Tier 1/2 projects; do not copy
project tooling from older `pl-tutorial`, `proof-generation`, or other
pre-current-K repositories. Read a repository's own agent instructions before
working inside it.

## Path forward

### Phase 0 — establish a trustworthy development history — complete

The exact 580-file import, three recovery documents, signed root commit,
signed import tag, artifact cleanup, and separate ignore-rule commit are all
complete. The root import remains directly comparable to the authoritative
ledger, and every subsequent repair is an ordinary Git diff.

### Phase 1 — restore dependency and toolchain coherence — complete

The sibling revision, exact adapter manifest, Rust 1.88 toolchain, cached K
components, ambient Z3, and full locked metadata resolution are verified.
`Cargo.lock` and its `Krs.lock` hash pin are unchanged. The sibling
system-Z3 override is an explicit machine prerequisite, not an undocumented
lock refresh.

### Phase 2 — restore the macro implementation — complete

1. The exact `fbccdc7` expander baseline is committed.
2. The required later behavior is reconstructed without claiming the missing
   post-C7 byte identity: initializer import hygiene, the full fixture runner
   and manifest, the later positive fixture, nonlinear binding semantics, and
   six focused missing negative sources.
3. Unit, fixture, positive Clippy/run/repeat, negative diagnostic, MSRV check,
   and current Clippy gates pass.

Exit criterion met by signed commit `1ffb361`. The exact runner is retained;
the expander and six missing fixture sources are documented functional
reconstructions.

### Phase 3 — reconcile the recovered late implementation line — complete

1. `krs-ir` unit and integration targets now compile and pass on both
   toolchains; obsolete tests and goldens are reconciled.
2. `krs-compiler/src/emit.rs` and `lowering.rs` are aligned with the retained
   Definition/Semantic IR; the active, MSRV, Clippy, and pinned-K compiler
   gates pass.
3. `krs-k-rust` is aligned with that Definition IR and the pinned native
   frontend through the documented KRS compatibility preparation layer.
4. `krs-cli` is aligned with direct-evidence collision provenance and the
   restored collector-planning suite. Production check/expand/emit/build
   integration passes.
5. The locked all-target workspace check passes after the macro milestone.

Implementation-reconstruction criterion met: the locked workspace check and
every focused crate gate pass, and every recovery-only compatibility layer is
explained. This does not include the independent M3D oracle package; Phase 4's
fail-closed M4 preflight is the authority for that separate test-evidence
boundary.

### Phase 4 — establish the new green recovery baseline — complete

Qualification completed before M4 remains green: the full locked workspace
suite, strict rustdoc/doc tests, Rust 1.88 all-target checking, the complete
syntax/F7 suite on both Rust toolchains, and the C7/Q8 K 7.1.337 gate. Ambient
Rust 1.98 Clippy still requires only the four classified historical-test style
exemptions (`too_many_lines`, `disallowed_names`, `struct_excessive_bools`, and
`items_after_test_module`); every other warning remains denied.

Commit `1546c2b` adds the independently qualified M3D reconstruction. Its
standalone gate passes under K 7.1.337; all six inherited IMP invocations and
five independent adjunct claims reproduce their surviving M4 normalized
records.

The final M4 recovery line additionally establishes:

1. The authored `tests/m4/rust-definition/src/imp.rs` expands byte-for-byte to
   `tests/m4/goldens/imp.expanded.rs`. Semantic IR, Definition IR, emitted K,
   explicit non-associativity, and expanded-reference compilation pass.
2. Schema-9 production rustdoc emission is restored as K comments with source
   ranges.
3. Proof specs import upstream `IMP-VERIFICATION-SYNTAX`, so `$n`, `$s`, and
   the other verification-only identifiers are parsed in the spec module
   without contaminating the executable semantic module.
4. The native proof support package fail-closes over exactly one spec module,
   one semantic import, and one exact claim. Incomplete residual comparison
   canonicalizes only KORE conjunction and exact Map concatenation as
   associative/commutative; ordinary application argument order remains
   exact.
5. KRS repairs one pinned-`k-rust` minimizer defect after parsed KORE is
   returned: if `_GenN` is reused for different sorts in one sentence, only
   the later conflicting `(kind, name, sort)` identity is alpha-renamed.
   Collision-free output remains byte-for-byte untouched and the pinned
   checkout remains unchanged.
6. `#[k::symbol]` now replaces the moved Rust item path in the stable backend
   identity rather than appending to it. The four-fixture adversary proves
   that the pinned public move preserves baseline `Expr` and `publicValue`
   identities while retaining moved descriptor provenance and source-map
   keys.
7. The K-frontend diagnostic probe uses the same executable/spec split as the
   proof route and imports `IMP-VERIFICATION-SYNTAX`; it still requires the K
   diagnostic to select the exact moved generated bytes before mapping them
   to authored `bool::and`.
8. Native check/test/Clippy, 17 adapter tests, seven residual-comparator tests,
   and all M4 oracle/probe unit tests pass.
9. Nine missing subordinate `Cargo.lock` files have been generated and
   reviewed as fixture-local resolutions. The root `Cargo.lock` and
   `Krs.lock` remain preserved.

### Qualified Phase 4 source package — M3D oracle reconstruction

The imported tree retained the M3D Rust-authored implementation slices but
lost eight top-level oracle files that existed at the last green M4 checkpoint:

- `tests/m3d/README.md`;
- `tests/m3d/verify.py`;
- `tests/m3d/pins.json`;
- `tests/m3d/fixtures/static-adjunct.k`;
- `tests/m3d/fixtures/induced-definition-error.k`;
- `tests/m3d/fixtures/induced-source-error.k`;
- `tests/m3d/claims/static-spec.k`;
- `tests/m3d/corpus/static-evaluation.imp`.

The forensic tree audit records the original Git blob IDs for all eight, but
marks every blob missing. Full content-hash scanning of `../recovery/` found no
surviving copy of the critical files. Independent contracts still preserve:

- verifier SHA-256
  `2ed14f41b39cf95fdfd132d1fa675c3d550375c75499d78711a2c901d023bc9f`;
- M3D pins SHA-256
  `2a27f0efead1c233f59f81d4e7c4fe37b56d8b1dcba203ff52e63d7769ecc085`;
- static-adjunct SHA-256
  `ffbe89ef33ad062c0d1e58f6fc77f52ec0063365155b3042cae8a247a328a462`;
- static-spec SHA-256
  `2b32479b9e982cac3c8ebb0b6e423662219c9d1ed1d387be80050732a522d444`;
- the complete source/behavior/proof policies in the 267-entry M4 ledger,
  `corpus.json`, `tests/m4/oracle/`, and the three M4 proof ledgers;
- the static execution result `x = 6, y = 0` and the last green M4 aggregate
  recorded below.

The reconstruction followed this order:

1. Reconstruct the eight-file M3D package from the retained M3D authored
   slices, M4 reference-policy code, upstream pinned IMP sources, diagnostic
   contracts, and proof ledgers. Claim byte identity only for a file that
   matches its surviving SHA-256 or Git blob identity; otherwise label it a
   functional reconstruction.
2. Run the reconstructed standalone M3D source, execution, diagnostic, and
   proof gate under K 7.1.337. Preserve the old semantic pins where their
   complete values survive; do not infer proof success from exit status.

Both steps pass. The likely original cell-ellipsis claim framing was recovered
by comparing normalized claim identities rather than by relaxing pins. All six
inherited IMP invocations and five independent adjunct claims reproduce their
surviving M4 records exactly. Every new top-level M3D file remains labeled a
functional reconstruction because none matches a surviving original blob.

The M3D package is complete in signed commit `1546c2b`. The post-C7 M4 ledger
has also been promoted and mechanically reconciled as described above; do not
repeat either recovery step.

### Resolved M4 blocker — consumed attribute-argument rename

Rust-analyzer does not expose stable proc-macro source positions to the
production provenance collector. The current recovery keeps analysis expansion
available with a synthetic `InvocationFallback` only when both exact captures
fail. This does not weaken collection: the compiler still rejects every
imprecise authored anchor, while normal rustc exact capture is unchanged.

The authored LSP investigation restored all ordinary input-token hooks:
readable sort declarations, parents and memberships; readable rule RHS binder
uses; narrowing paths; and qualified application paths. Stale probe fragments
were reconciled to the recovered `k::k!` spelling.

Before the plural-expander fix, renaming the authored `Expr;` declaration
produced 80 edits and covered every required semantic use except the `Expr`
token in:

```rust
#[k::constructors(sort = Expr, result = KResult)]
```

The earlier experiment preserved the sort witness in the singular
`#[k::constructor]` expander, but M4 uses the plural enum-family
`#[k::constructors]` path. Preserving `membership_sort()` in that actual
expander supplies rust-analyzer with the semantic bridge from the hidden
`TypeId` witness back to the consumed attribute token. No authoring syntax,
descriptor meaning, provenance key, or identity changes.

The checked-in gate now reports zero diagnostics, all 24 definition/hover
classes, `map::update` completion, and all five rename families. `Expr` rename
returns 82 edits, including the constructor-family attribute; the assertion
was never weakened.

### Final M4 qualification

On 2026-08-26, two consecutive complete invocations of
`python3 tests/m4/verify.py` passed without any intervening source, pin,
lockfile, environment, or tool revision change. Both runs proved:

- M4.1 exact source/tool/revision preflight at descriptor protocol 15 and
  Definition IR schema 9;
- M4.2 workspace/package format, check, Clippy, tests, docs, macro diagnostics,
  rust-analyzer, and readable-IMP LSP qualification;
- M4.3 deterministic artifacts for 124 descriptors, exact reviewed expansion,
  and the 83-descriptor replacement package;
- M4.4 fail-closed parsed/compiled source projections with 98 parsed and 244
  compiled sentences;
- M4.5 exact native KORE parity:
  `reference=1206 native=1206 reference_projector_pairs=0 native_projector_pairs=40`;
- M4.6 23 parses, 31 executions, 246 bounded-depth states, 16 searches, 8
  rejections, one expected failure, and evidence SHA-256
  `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`;
- M4.7 21 reference-source proofs, 21 actual-source proofs, 21 dry-run specs,
  21 native-Haskell results, and 20 unique native claims; and
- M4.8 seven live compatibility probes with report SHA-256
  `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.

The final deterministic native artifact pins are:

| artifact | SHA-256 |
|---|---|
| `.krs-artifacts` | `4992e03ec15408f887a401455c9f719384c6d5bb69e661487f91abe576ceb1b5` |
| `definition.kore` | `1483dc5eacf7fed1f5fd56d0c33530a6552d06b19216159758e5b0d57211d518` |
| `macros.kore` | `e1d5a374973b2fa9eb2502c3acdee5244ee7a89a965dd7acd69cda4b7d7814e0` |
| `syntaxDefinition.kore` | `9963fcfacc153cf8e12e900ace1b4416be6672d5c4ac620a3e73af2d69c7c051` |

Phase 4 is complete. The new baseline receives a new signed identity and does
not claim to be `9d507b0`.

### Phase 5 — readable IMP milestone

Implementation and final qualification are complete.

The readable-IMP milestone establishes:

- the normative `draft/readability/spec` now describes the compiling surface rather than the preimplementation build list;
- readable sorts, grammar, wrapper-free configuration, rules, map update, F7 collection, and all four F3 method gates are present in the production M4 package;
- `krs fmt` is integrated as a Rustfmt-first workspace formatter with editor, stdin, check, discovery, diff, trivia, fixpoint, corpus, and edit-stability coverage;
- readable-rule overlap checking runs after semantic sort inference and rejects deterministic cross-table overlaps;
- `draft/readability/spec/imp.expanded.rs` is byte-identical to the live deterministic M4 expansion golden;
- workspace formatting, the intended warnings-denied Clippy gate, all workspace tests, the focused overlap regression, formatter corpus tests, live expansion comparison, and Rust 1.88 workspace checks pass;
- the complete M4 gate passes at protocol 15 and Definition IR schema 9: 124 descriptors, 98 parsed and 244 compiled sentences, native KORE parity at 1,206/1,206 sentences, 23 parses, 31 executions, 246 bounded-depth states, 16 searches, 8 rejections, one expected failure, all 21 proof specifications and 20 unique native claims, and all seven compatibility probes;
- the M4 behavior evidence remains
  `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`,
  and the compatibility report remains
  `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.

The final source-ledger, Rust formatting, diff-hygiene, and three-specimen formatter-corpus checks also pass. `aligned` remains the explicitly provisional trailing-comment default; the fixed two-space gutter remains available until the user freezes that presentation choice.

Phase 5 is complete: the normative authoring specimen, its byte-exact expansion, and the complete IMP oracle are green from the signed milestone containing this record.

### Phase 6 — qualify the initial authoring layer against KWasm — milestone complete; port incomplete

Two representative KWasm integer slices are checked in under `tests/kwasm/` and documented in `draft/readability/kwasm/README.md`.
They port the real abstract integer-arithmetic path from the pinned KWasm checkout at commit `212271bd434bd402e27c42f6416854342733386d`:

- `i32` and `i64` value types;
- typed integer values, recursive instruction lists, and a recursive value stack;
- integer constants and `add`, `sub`, `mul`, and `div_u` instructions;
- real simultaneous `<instrs>` and `<valstack>` transitions with WebAssembly operand order;
- modulo-`2^32` and modulo-`2^64` wraparound, including signed literal normalization and `-1`;
- explicit nonzero/zero `requires` partitions, `undefined`, and divide-by-zero trap generation;
- one concrete all-path simple-addition claim.

The first slice exposed one authoring gap, W1: a readable machine rule could not rewrite an ordinary fixed leaf cell alongside its computation-cell head.
Protocol 16 adds that exact structured shape across parsing, provenance, host IR, macro expansion, descriptor collection, semantic lowering, and reference expansion.
No modulo builtin was added: the selected nonnegative invariant implements exact reduction through the existing integer division, multiplication, and subtraction operations.
Readable patterns still do not claim repeated symbolic equality, so same-width operand matching remains split into explicit i32 and i64 rules.

The second slice required no KRS authoring extension or protocol bump.
Existing `int::div`, `int::eq`, `int::ne`, guarded equations, constructors, and readable machine rules express the selected KWasm rules directly.
The slice does not invent `owise` or modulo support: KWasm's selected operators are exhaustive through unconditional or explicit zero/nonzero equations, while remainder and the global fallback remain deferred until a corpus requires them.

The fail-closed KWasm gate passes under KRS K 7.1.337 with:

- 60 descriptors;
- deterministic readable and independently expanded compilation;
- Rustfmt, `krs fmt --check`, warnings-denied Clippy, and six focused rust-analyzer definition/hover probes with zero diagnostics;
- emitted K compilation through the Haskell backend;
- 32 pinned native executions spanning both widths, zero, maxima, negative constants, operand order, nesting, all add/sub/mul wraparound forms, exact and truncated unsigned division, high-bit unsigned values, and divide-by-zero traps;
- one native `kprove` result equal to `#Top`;
- structured value-versus-trap behavior SHA-256 `4a3b6107cb23fa451a392d0a0ef1d42203d5eb64cda8cbcda025e75d2458afd5`;
- normalized native `definition.kore` SHA-256 `53e07c223f166b3ba60f2226dc57a17d1fb0256532f6fea4c0ad6770151c600d`.

The KORE pin normalizes only the temporary absolute `semantics.k` source path and alpha-renaming of K-generated binders in `isSort` membership axioms.
Three independent compilations converge to the same normalized hash.
The gate fails if either expected normalization shape is absent or changes.

The optional direct structured `k-rust` compilation route is not an acceptance requirement for this slice.
It currently reaches an unrelated no-map embedded-prelude `Map:lookup` failure, while emitted K compilation, native execution, and native proof all pass.
Treat that route as a future adapter/prelude investigation only when a selected corpus requires it; do not misclassify it as a failure of the readable KWasm semantics.

After the W1 extension and the fixture-only division/trap extension, the complete IMP M4 gate passes at descriptor protocol 16 and Definition IR schema 9.
All semantic IR, Definition IR, emitted K, source-map, symbol-map, behavior, proof, native KORE, and compatibility evidence remains unchanged.
Only the descriptor bundle changed, and replacing its sole `"protocol_version": 16` field with `15` reproduces the prior pinned descriptor-bundle hash byte-for-byte.
The protocol-16 descriptor-bundle SHA-256 is `0db28e2913cbb04d310243c62ebdccee29e035ae0d7f4680645a06845bfe498b`.

The final M4 run proves:

- M4.1 exact source/tool/revision preflight at protocol 16 and IR schema 9;
- M4.2 workspace/package format, check, Clippy, tests, docs, diagnostics, MSRV coverage, and readable IMP LSP;
- M4.3 124 deterministic descriptors, exact reviewed expansion, 83-descriptor replacement parity, and six repeated CLI/API artifact reproductions;
- M4.4 98 parsed and 244 compiled source sentences;
- M4.5 native KORE parity at `reference=1206 native=1206`;
- M4.6 23 parses, 31 executions, 246 bounded-depth states, 16 searches, 8 rejections, one expected failure, and unchanged evidence SHA-256 `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`;
- M4.7 21 reference-source proofs, 21 readable-source proofs, 21 dry-run specifications, 21 native Haskell results, and 20 unique native claims;
- M4.8 seven live compatibility probes with unchanged report SHA-256 `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.

The Phase 6 qualification milestone is complete from the signed milestone containing this record.
It is an acceptance baseline for subsequent porting, not completion of the KWasm port.

### Phase 7 — readable KEVM operational milestone — milestone complete; port incomplete

The user explicitly selected KEVM before KMIR. The first KEVM milestone is
checked in under `tests/kevm/` and documented in
`draft/readability/kevm/README.md`. It pins the clean KEVM checkout at
`d818397e9b7ffa213d687e64418dc8f5293e1ce2`, whose K 7.1.337 release exactly
matches KRS.

The selected slice is based on KEVM's real opcode pipeline and checked-in
opcode summaries. A structured program adapter replaces only Bytes decoding;
the fixture retains PUSH widths, a recursive word stack, modulo-`2^256` ADD,
PC observation and movement, gas deduction, successful halt, stack underflow,
out-of-gas, and invalid-instruction status across five ordinary state cells.
It therefore adds a resource-sensitive, status-bearing operational dimension
beyond KWasm rather than cloning its arithmetic surface.

No production KRS change was required. Existing protocol-16 fixed-leaf
rewrites express the five simultaneous cell transitions, and existing guarded
equations express KEVM's sufficient/insufficient gas partition. Bytes, maps,
sets, bags, multiplicity cells, accounts, storage, calls, fork schedules,
cryptographic hooks, priorities, `owise`, and full symbolic claims remain
explicitly deferred.

The fail-closed gate passes with 69 descriptors, deterministic readable and
expanded compilation, emitted-K parity, K 7.1.337 native compilation, 14
normal/exceptional executions, six zero-diagnostic rust-analyzer probes, and
one native all-path claim closing with `#Top`. The behavior hash is
`3cd26827055518f97e39af8eb30979712bb55ea132aff21009b683e531da35aa`; the
normalized KORE hash is
`672953aa73dbcce4aa15aae8e663e1a42e86d12816e6a16a21d4966edb7e5a04`.

This result qualifies the initial operational baseline only.
The full KEVM port remains incomplete.

### Phase 8 — readable KMIR operational milestone — milestone complete; port incomplete

The first KMIR milestone is checked in under `tests/kmir/` and documented in `draft/readability/kmir/README.md`.
It pins the clean KMIR checkout at `4d793252bcd77091ee759ca6cd1629db41ed5496`, whose K 7.1.337 release exactly matches KRS.

The selected slice follows KMIR's actual `#execBlockIdx` / `#execBlock` / `#execStmts` / `#execStmt` / `#execTerminator` pipeline.
A recursive adapter replaces serialized builtin Lists at the body boundary and installs a graph into `Map<Int, BasicBlock>`.
A second map represents the selected untyped-local boundary while preserving indexed copies, persistent updates, read-before-write staging, integer addition, `Goto`, Boolean `SwitchInt`, local `_0`, and top-level return.
Calls, types, projections, memory, references, unwind, arbitrary switch branch lists, and generated proof workflows remain explicit future evidence.

The slice exposed one narrow independent-expansion gap, K1.
Readable map rules caused reference expansion to insert `use k::map` even when the authored module already imported that macro for a concrete map claim.
The duplicate macro import made the expanded crate fail to compile.
The compiler now compares use trees before insertion, with a focused unit regression for attributed equivalent imports and unrelated imports.
No descriptor protocol, IR schema, syntax, lowering, or runtime change was required.

The fail-closed gate passes with 103 descriptors, deterministic readable and expanded compilation, 11 native executions, six zero-diagnostic rust-analyzer probes, and one native all-path claim closing with `#Top`.
The behavior hash is `e150e7a86c513ec5966185fe079d8f58c34c57a66e73991ff8ac9b1f9aaee5c5`; the normalized KORE hash is `5b05ecb38c803c8ae95d517e46f10e2725ac74f45f3cb7867cf85e600c818f7c`.
The all-path claim spans installation, graph lookup, ordered statements, copied locals, addition, `Goto`, true `SwitchInt`, and return.
The unchanged KEVM and KWasm gates pass, and the complete IMP M4 gate retains its 1,206/1,206 native KORE parity, behavior evidence `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`, all proofs, and compatibility evidence `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.

Each corpus remains an acceptance oracle, not a source of silent KRS syntax changes.
Kontrol is not part of the active KEVM/KMIR semantic-coverage goal and must not silently expand it.

This result qualifies the initial operational baseline only.
The full KMIR port remains incomplete.

### Phase 9 — promote reusable semantic product packages — complete

The three KRS definitions now live in the canonical standalone `semantics/` Cargo workspace:

- `krs-kwasm-semantics` in `semantics/kwasm` with K namespace `KRS-KWASM`;
- `krs-kevm-semantics` in `semantics/kevm` with K namespace `KRS-KEVM`;
- `krs-kmir-semantics` in `semantics/kmir` with K namespace `KRS-KMIR`.

The old `tests/*/rust-definition` copies are removed.
The three test directories retain the independent external corpora, source and revision pins, editor probes, artifact ledgers, behavior ledgers, and native proof gates.
All product crates share `semantics/Cargo.lock`.

`semantics/coverage.toml` defines the machine-readable completion contract and records the pinned upstream inventories, current coverage, adapter boundaries, and deferred surfaces.
At this milestone the source inventories and KRS rule counts are:

| Port | Source files | Syntax declarations | Source rules | KRS equations | KRS machine rules | Complete |
|---|---:|---:|---:|---:|---:|---|
| KWasm | 13 | 386 | 884 | 8 | 8 | no |
| KEVM | 98 | 478 | 3,440 | 8 | 13 | no |
| KMIR | 19 | 525 | 787 | 0 | 22 | no |

The standalone workspace passes formatting, locked offline all-target checking, all workspace tests, and warnings-denied Clippy.
The direct rust-analyzer probes report zero diagnostics and resolve every pinned definition and hover.
The fail-closed semantic gates pass from the canonical packages with unchanged structured behavior evidence:

- KWasm: 60 descriptors, 32 executions, one native proof, behavior SHA-256 `4a3b6107cb23fa451a392d0a0ef1d42203d5eb64cda8cbcda025e75d2458afd5`, normalized KORE SHA-256 `d85e22389012617a27323d2cdece0340c8e5bc45364a1d499118a50f2972f4bb`;
- KEVM: 69 descriptors, 14 executions, one native proof, behavior SHA-256 `3cd26827055518f97e39af8eb30979712bb55ea132aff21009b683e531da35aa`, normalized KORE SHA-256 `378f29dcfa3536c2dccf978f67579f58109300c007e8ad3cdbbd36e916626d3f`;
- KMIR: 103 descriptors, 11 executions, one native proof, behavior SHA-256 `e150e7a86c513ec5966185fe079d8f58c34c57a66e73991ff8ac9b1f9aaee5c5`, normalized KORE SHA-256 `f4790c58f86f1acb1c484ed2fc84cbcda2b28c988e084cfa2cb7948ebe06db6e`.

The changed expansion, artifact, and KORE identities are explained by canonical package paths, package names, and K namespaces rather than semantic behavior changes.
All new identities are fail-closed in the three source and artifact ledgers.

### Phase 10 — replace the KEVM program adapter with builtin Bytes — complete

The KEVM package now stores the program in K's pinned builtin `Bytes` domain instead of a KRS-owned recursive opcode list.
Descriptor protocol 17 and Definition IR schema 10 add the selected shared authoring surface:

- builtin sort `Bytes` backed by `BYTES`;
- `bytes::length` emitted as `lengthBytes(B)`;
- `bytes::get` emitted as `B [ I ]`;
- claim-only `k::bytes!(b"...")` tokens transported canonically as lower-hex `b"\xhh..."` payloads.

The protocol rejects malformed and noncanonical byte-token payloads.
Focused tests cover alias-safe registry completeness, parser retention, canonical macro transport, reference expansion, and exact K emission.

The KEVM opcode pipeline now bounds lookup with `lengthBytes`, reads the opcode at the program counter, recognizes `STOP`, `ADD`, `PC`, and `PUSH1` through `PUSH32`, and decodes PUSH immediates recursively in big-endian order.
Execution preserves the original program bytes while retaining the prior stack, PC, gas, and exceptional-status behavior.

The fail-closed KEVM gate passes with 85 descriptors, 14 native executions, and one native proof under K 7.1.337.
The structured behavior SHA-256 is `8c0359e611d760916bdbca2966998b02a9ef38ee1e4a8467861b38bb793e86d7`.
The normalized KORE SHA-256 is `957aa5e19a3a49a832ad92753f785e797d1aa2f731c280030fc903791ed5f7a0`.
This phase removes the KEVM structured-program adapter but does not claim the remaining opcode, state, call, transaction, schedule, or cryptographic surfaces.

The unchanged KWasm and KMIR baselines pass at protocol 17 and Definition IR schema 10 with their prior emitted K, behavior hashes, KORE hashes, and native proofs.
The complete IMP M4 gate also passes every phase at protocol 17 and schema 10.
Its emitted K, native KORE parity, behavior/search digest, proof outcomes, and compatibility digest remain unchanged; only the descriptor, Semantic IR, Definition IR, and source-sidecar identities moved with the shared protocol/schema unit.

### Phase 11 — replace the KMIR block-program adapter with builtin List — complete

The shared KRS authoring surface now includes K's associative builtin `List` in descriptor protocol 18 and Definition IR schema 11.
The closed operation catalog covers `.List`, `ListItem`, associative concatenation, indexed lookup, persistent indexed update, and `size`.
Semantic and Definition IR retain the dynamic result sort of indexed lookup, and canonical K emission uses an explicit projection such as `{PROGRAM:List [ INDEX:Int ]}:>BasicBlock`.
The native `k-rust` adapter maps the same operations to `.List`, `ListItem`, `_List_`, `List:get`, `List:set`, and `sizeList`, with the required semantic cast on lookup.

Focused tests qualify exact registry identities, alias safety, descriptor arity, Semantic and Definition IR validation, exact source emission, reference expansion, and native frontend adaptation.
The three semantic source ledgers now include the shared lowering, overlap, sidecar, descriptor-protocol, and state files that participate in this surface.

The KMIR package now stores `<program>` as `List<BasicBlock>` and begins execution directly at block index zero.
The KRS-owned `BlockProgram` constructors, installer command, installed-block `Map`, and `<blocks>` cell are removed.
The program list is preserved across execution, and `#execBlockIdx` performs direct typed list lookup.
The all-path claim constructs and preserves the four-block program through `list::empty`, `list::item`, and `list::concat`.

The fail-closed KMIR gate passes with 94 descriptors, 11 native executions, and one native all-path proof under K 7.1.337.
Its structured behavior SHA-256 is `dd173192fa881b744030cef7b57aca8f646e2788b21397d00c826db0d41b4abf`.
Its normalized KORE SHA-256 is `d71738e52d51bba416ee52391bf71a7ba9bf9a017b839c3493547f0b1f3c8d34`.

The KEVM and KWasm gates pass unchanged at protocol 18 and Definition IR schema 11 with 85 and 60 descriptors, 14 and 32 executions, and one native proof each.
The complete IMP M4.1–M4.8 gate passes at the same versions with byte-identical emitted K, 1,206/1,206 native KORE parity, unchanged behavior evidence `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`, all 21 proof specifications, and unchanged compatibility evidence `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.

This phase removes KMIR's block-program adapter.
It does not complete the KMIR port: locals remain an untyped `Map`, and the source inventory still contains deferred type, projection, memory, call, unwind, intrinsic, arithmetic, priority, and symbolic-workflow surfaces.

The normative formatter target remains:

- `draft/readability/spec/imp.rs` first;
- `draft/readability/spec/decisions.md` second;
- `draft/readability/spec/open-questions.md` for genuinely unresolved items.

`draft/readability/result/` is historical design evolution, not the
implementation authority.

### Current goal completion audit

| Requirement | Authoritative evidence | Status |
|---|---|---|
| Finish `draft/readability/spec` | Normative `imp.rs`, deterministic `imp.expanded.rs`, implemented `decisions.md`, deliberately unresolved `open-questions.md`, and M4.2–M4.4 | complete; the trailing-comment policy, `{ .. }`, and no-k-head spelling remain explicitly open rather than silently resolved |
| Make KRS work on IMP | Complete M4.1–M4.8 gate at protocol 18 and IR schema 11, including exact source projection, 1,206/1,206 native KORE parity, behavior hash `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`, all proofs, and compatibility hash `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6` | complete |
| Complete the KRS KWasm port | `semantics/coverage.toml`, canonical `semantics/kwasm`, and the fail-closed KWasm gate | incomplete: 8 equations and 8 machine rules qualify the arithmetic baseline against an 884-rule source inventory; recursive instruction and value-stack boundaries and deferred semantic surfaces remain |
| Complete the KRS KEVM port | `semantics/coverage.toml`, canonical `semantics/kevm`, and the fail-closed KEVM gate | incomplete: 20 equations and 14 machine rules qualify the Bytes-backed opcode baseline against a 3,440-rule source inventory; the program adapter is removed, while the remaining opcode and stateful semantic surfaces remain |
| Complete the KRS KMIR port | `semantics/coverage.toml`, canonical `semantics/kmir`, and the fail-closed KMIR gate | incomplete: 22 machine rules qualify the block-execution baseline against a 787-rule source inventory; the block-program adapter is removed, while untyped locals and deferred semantic surfaces remain |
| Preserve recovery boundaries | `krs.RECOVERY_PROVENANCE.md` and `../recovery/` remain unchanged; all reconstructed work is committed only in the live KRS repository | complete |

Representative acceptance slices are evidence-backed baselines, not substitutes for the explicit full-port completion contract.
A port may be marked complete only when its pinned syntax, configuration, executable-rule, behavior, proof, and adapter-boundary requirements are all discharged in `semantics/coverage.toml`.

## Guardrails

- Do not modify `../recovery/` or delete its displaced variants.
- Do not replace `draft/` with a clean-commit subset; later user-authored work
  exists only in the recovered tree.
- Do not fabricate old commit IDs or claim byte identity where only functional
  reconstruction is possible.
- Do not treat every stable-ledger mismatch as damage; classify expected F7
  and later work first.
- Do not regenerate `Cargo.lock` before restoring the exact stable dependency
  manifest and testing the original lock.
- Do not refresh M4 behavioral pins to conceal a changed result.
- Do not begin collector integration or formatter rendering while the
  recovery baseline is red.
- Do not resume raw-disk searching unless genuinely new media or session
  payloads appear.

## Immediate next action

Resume full KEVM coverage next against the pinned `evm-semantics` inventory and its upstream behavior and proof suites.
Select each next implementation tranche from an uncovered upstream syntax, configuration, executable-rule, behavior, or proof requirement; do not optimize further for already removed adapters or recovered intermediate state.
After KEVM satisfies the completion contract, complete KMIR against the pinned `mir-semantics` inventory, beginning with its remaining typed-local and projection boundary only insofar as the selected upstream corpus requires it.
Prefer shared KRS authoring features when the same source construct is required by multiple ports, but qualify every feature through the active port before broadening it.
Preserve all three semantic gates and the complete IMP M4 gate at each coherent signed milestone.
Return to any remaining KWasm inventory after KEVM and KMIR so the active three-port goal closes without deferred adapters or unrecorded source coverage.
Do not reopen recovery forensics unless genuinely new evidence or media appears.

## Audit hygiene

The recovery evidence and `krs.RECOVERY_PROVENANCE.md` remain unchanged. This
audit is the mutable, committed record of decisions and qualification results;
update it whenever a recovery phase, environmental prerequisite, or gate
changes materially.
