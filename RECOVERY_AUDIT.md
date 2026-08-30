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

K-Rust is the routine development-time correctness authority for all three semantic ports.
Default semantic gates must compile Definition IR directly through the pinned K-Rust frontend and execute concrete corpora through persistent in-process backend workers.
They must not invoke `kompile`, `krun`, `kprove`, the JVM, or the Haskell backend.
The explicit `--java-reference` option reserves the K toolchain comparison and proof workload for deliberate final validation.
Any missing K-Rust feature or defect must be recorded in `K_RUST_UPSTREAM.toml`; KRS-specific fixes must remain in the dedicated `k-rust-krs` checkout or the KRS adapter so the shared upstream checkout stays clean.

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

### Phase 12 — KEVM core unsigned arithmetic tranche — complete; port incomplete

The next KEVM tranche selects the pinned core unsigned arithmetic family from `evm.md` and `evm-types.md`.
The canonical package now decodes and executes `MUL`, `SUB`, `DIV`, and `MOD` in addition to the prior `ADD` path.
It preserves KEVM's top-first operand order, modulo-`2^256` multiplication and subtraction, zero-totalized unsigned division and modulus, `Gverylow = 3` subtraction, and `Glow = 5` multiplication, division, and modulus.
Structural underflow and insufficient-gas branches cover every selected binary operation.

This tranche exposed a real shared authoring requirement rather than an adapter opportunity.
The prior `#kevmChop` approximation used truncating division and was correct only for nonnegative intermediates.
KEVM subtraction requires Euclidean normalization because `0 - 1` must become `2^256 - 1`.
Descriptor protocol 19 and Definition IR schema 12 therefore add K's pinned `INT.mod` operation.
The `int::modulo` marker remains typed through registry resolution, descriptor transport, Semantic IR, Definition IR, reference expansion, canonical K emission as `modInt`, and native frontend adaptation.
Focused registry and end-to-end KEVM tests qualify the new identity.

The fail-closed KEVM gate passes with 131 descriptors, 25 native executions, and two native all-path proofs under K 7.1.337.
The behavior matrix includes normal and wraparound multiplication, top-first subtraction and negative wraparound, division and modulus with nonzero and zero divisors, both gas classes, family underflow, and a combined arithmetic execution.
Its structured behavior SHA-256 is `94652cf0651fc95b2e4746f5945463ea7591d6eae50463f3dabe4d7cf83ca16a`.
Its normalized KORE SHA-256 is `64846d863fb029bfd4a33626ef52c410ef6a89fe7b54853c1d7927e69a3935bd`.

The unchanged KWasm and KMIR gates pass at protocol 19 and Definition IR schema 12 with byte-identical emitted K, unchanged behavior and KORE hashes, 32 and 11 executions, and one native proof each.
The complete IMP M4.1–M4.8 gate passes at the same versions with byte-identical emitted K, 1,206/1,206 native KORE parity, unchanged behavior evidence `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`, all 21 proof specifications, and unchanged compatibility evidence `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.

This tranche advances the explicit KEVM inventory but does not complete the port.
Signed arithmetic, ternary modular arithmetic, exponentiation, bitwise and comparison families, and all stateful EVM surfaces remain uncovered.

### Phase 13 — KEVM signed and ternary modular arithmetic tranche — complete; port incomplete

The next KEVM tranche selects the adjacent `SDIV`, `SMOD`, `ADDMOD`, and `MULMOD` family from the pinned `evm.md`, `evm-types.md`, `schedule.md`, and checked-in opcode summaries.
The canonical package now carries KEVM's two's-complement `sgn` and `abs` boundary, signed division and dividend-signed modulus, zero-divisor totalization, minimum-word divided by negative-one overflow, and exact unbounded ternary intermediates before modulus.
It preserves top-first operands, charges `Glow = 5` for the signed binary pair and `Gmid = 8` for the ternary pair, and covers zero/one-element binary and zero/one/two-element ternary underflow branches.

No shared KRS protocol or IR extension was required.
The tranche composes the already-selected native `INT.mod`, truncating positive `INT.tdiv`, integer arithmetic, comparisons, and Boolean connectives.
This follows the pinned KEVM implementation rather than adding host-side signed-word or modular arithmetic.

The fail-closed KEVM gate passes with 186 descriptors, 41 native executions, and two native all-path proofs under K 7.1.337.
The behavior matrix distinguishes signed quotient sign combinations, zero division, minimum-word overflow, signed remainder behavior, full-precision `ADDMOD` and `MULMOD` intermediates, `Gmid` out-of-gas, ternary underflow, and the combined arithmetic path.
Its structured behavior SHA-256 is `e17f37450188a0211d0171b3a13f3a1981cac74e62aaa5f68a4a5a812c715a13`.
Its normalized KORE SHA-256 is `5eb5a0f6c2596a9cfacdc1815995fe9f67214989ddcaac48fc8a111920c3fc12`.

The unchanged KWasm and KMIR gates pass at protocol 19 and Definition IR schema 12 with byte-identical emitted K, unchanged behavior and KORE hashes, 32 and 11 executions, and one native proof each.
The complete IMP M4.1–M4.8 gate passes at the same versions with byte-identical emitted K, 1,206/1,206 native KORE parity, unchanged behavior evidence `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`, all 21 proof specifications, and unchanged compatibility evidence `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.

This tranche advances the explicit KEVM inventory but does not complete the port.
Exponentiation, comparison, bitwise, environmental, memory, storage, control-flow, call, creation, log, and termination families remain uncovered.

### Phase 14 — KEVM comparison tranche — complete; port incomplete

The next KEVM tranche selects the pinned `LT`, `GT`, `SLT`, `SGT`, `EQ`, and `ISZERO` family from `evm.md`, `evm-types.md`, `schedule.md`, and the checked-in opcode summaries.
The canonical package now carries KEVM's Boolean-to-word boundary and four-part signed-less definition over two's-complement sign and magnitude.
It preserves top-first comparison operands, unary zero testing, `Gverylow = 3` charging, binary and unary underflow, and insufficient-gas behavior.

No shared KRS protocol or IR extension was required.
The tranche composes the pinned integer comparison and Boolean operations with the already-qualified KEVM word-sign helpers.

The fail-closed KEVM gate passes with 250 descriptors, 57 native executions, and two native all-path proofs under K 7.1.337.
The behavior matrix distinguishes unsigned ordering from every signed sign partition, both-negative magnitude reversal, equality, zero testing, `Gverylow` out-of-gas, unary and binary underflow, and a combined arithmetic/comparison path.
Its structured behavior SHA-256 is `7e8d7c9dd848a5b2994fd3dbbfd2d7bed71e1d3b6f6ff59a1d5ac73d0a553cb4`.
Its normalized KORE SHA-256 is `557e778d1bf392b8b144628eea443553f0929008a82e671f268716e8f2a876c1`.

The unchanged KWasm and KMIR gates pass at protocol 19 and Definition IR schema 12 with byte-identical emitted K, unchanged behavior and KORE hashes, 32 and 11 executions, and one native proof each.
The complete IMP M4.1–M4.8 gate passes at the same versions with byte-identical emitted K, 1,206/1,206 native KORE parity, unchanged behavior evidence `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`, all 21 proof specifications, and unchanged compatibility evidence `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.

This tranche advances the explicit KEVM inventory but does not complete the port.
Exponentiation, bitwise, environmental, memory, storage, control-flow, call, creation, log, and termination families remain uncovered.

### Phase 15 — KEVM Shanghai pure-word expression tranche — complete; port incomplete

The next KEVM tranche selects the remaining Shanghai-active pure-word expression opcodes from the pinned `evm.md`, `evm-types.md`, `gas.md`, `schedule.md`, and checked-in opcode summaries.
The canonical package now decodes and executes `EXP`, `SIGNEXTEND`, `AND`, `OR`, `XOR`, `NOT`, `BYTE`, `SHL`, `SHR`, and `SAR`.
It preserves top-first operands, modulo-`2^256` exponentiation, two's-complement sign extension, big-endian byte indexing, KEVM's exact `NOT` definition, logical shifts, and sign-filling arithmetic right shift.
Explicit guards totalize shifts of 256 bits or more without invoking an oversized host shift.
`CLZ` remains excluded because the pinned Shanghai schedule disables it; its first active schedule is Osaka.

This tranche requires a shared KRS extension rather than a port-local approximation.
Descriptor protocol 20 and Definition IR schema 13 add the pinned modular exponentiation, base-two logarithm, integer shift, and bitwise operation identities.
The seven operations remain typed through registry resolution, descriptor transport, Semantic IR, Definition IR, reference expansion, canonical K emission, and native frontend adaptation.
Focused registry, golden, reference-expansion, emission, and native-adaptation tests qualify the new identities.

The fail-closed KEVM gate passes with 354 descriptors, 81 native executions, and three native all-path proofs under K 7.1.337.
The 24 added behavior cases distinguish zero-, one-, and two-byte exponent charging, exponent out-of-gas, positive, negative, and invalid sign extension, every selected bitwise operation, valid and invalid byte indices, wrapping and oversized shifts, positive and negative arithmetic shifts, unary and binary underflow, fixed-cost out-of-gas, and the combined pure-word path.
The combined program terminates successfully at program counter 50 with zero gas.
Its structured behavior SHA-256 is `5ce64ab234171a0f9f6e17235a5a96f6c2cfeba060b9f68997fd623996e049d5`.
Its normalized KORE SHA-256 is `ba7b2eeadb4bd7a901423a1955d5ee83eb579287e8215b46cbb815d33a498f29`.
All three claims close with `#Top` through native `kprove`.

The unchanged KWasm and KMIR gates pass at protocol 20 and Definition IR schema 13 with byte-identical emitted K, unchanged behavior and KORE hashes, 32 and 11 executions, and one native proof each.
Only their expected descriptor, IR, source-sidecar, and artifact identities move with the shared extension.
The complete IMP M4.1–M4.8 gate passes at protocol 20 and Definition IR schema 13 with byte-identical emitted K, 1,206/1,206 native KORE parity, unchanged behavior evidence `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`, all 21 proof specifications, and unchanged compatibility evidence `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.

### Phase 16 — isolate and qualify the k-rust 0.4 frontend/backend authority — complete

KRS now selects k-rust `0.4.0` at upstream commit `3cce7a47941c4dc0664e6e870d4e0529d74753c6` from the dedicated `../inspirations/midnightntwrk/k-rust-krs` worktree.
The shared k-rust main checkout is no longer an input and may remain upstream-clean.
The dedicated worktree carries the one KRS-specific root-manifest policy that disables the unpinned `gh-release` Z3 acquisition path and links the Nix-pinned Z3 4.12.5 library instead.

The adapter maps its historical public `Backend::Haskell` compatibility spelling to k-rust 0.4's symbolic `CompilationBackend::Rust` target.
Because KRS claims carry explicit modalities, native compilation sets `default_claims_to_all_path = false`.
All 17 adapter tests pass.

`Krs.lock` and the complete M4 ledger pin the frontend, backend, and shared KORE subtrees separately.
The final isolated M4.1–M4.8 gate passes with exact 1,206/1,206 native KORE parity, behavior evidence `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`, all proofs, and compatibility evidence `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.
`K_RUST_HANDOFF.md` records the coordination boundary and upstream follow-up policy.
Later direct native KEVM compilation exposed the semantic-cast projection defect now recorded in `K_RUST_UPSTREAM.toml`.

This tranche advances the explicit KEVM inventory but does not complete the port.
Environmental, memory, storage, control-flow, call, creation, log, termination, transaction, schedule, account, cryptographic, and symbolic surfaces remain uncovered.

### Phase 17 — KEVM Shanghai stack-manipulation tranche — complete; port incomplete

The next KEVM tranche selects `POP`, `DUP1` through `DUP16`, and `SWAP1` through `SWAP16` from the pinned `evm.md`, Shanghai schedule, and direct opcode summaries.
The canonical package decodes the complete byte ranges and implements recursive stack size, depth-indexed lookup, and depth-indexed replacement functions.
Execution preserves KEVM's top-relative indexing, `Gbase` cost for `POP`, `Gverylow` cost for `DUP` and `SWAP`, dynamic-depth underflow partition, and the 1,024-word `DUP` overflow boundary.

The fail-closed KEVM gate passes with 400 descriptors, 91 native executions, and four native all-path proofs under K 7.1.337.
The ten added behavior cases cover `POP`, first- and sixteenth-depth duplication and exchange, each family underflow boundary, fixed-cost out-of-gas, and a concrete 1,024-word overflow state.
Its structured behavior SHA-256 is `45f9d16df4836a1d5895d6c035112922e6f4338c89dc385e2e55fd46da45b596`.
Its normalized KORE SHA-256 is `0c650f24525918a49de4747e55a9c261f3aa4af4427eaaf9f7b54053ca550c19`.
The added combined claim spans `DUP3`, `SWAP2`, `POP`, gas exhaustion, and successful halt; all four claims close with `#Top` through native `kprove`.

This tranche advances the explicit KEVM inventory but does not complete the port.
Environmental, memory, storage, control-flow, call, creation, log, termination, transaction, schedule, account, cryptographic, and symbolic surfaces remain uncovered.

### Phase 18 — KEVM Shanghai control-flow tranche — complete; port incomplete

The next KEVM tranche selects `JUMP`, `JUMPI`, and `JUMPDEST` from the pinned `evm.md`, Shanghai schedule, and direct `JUMPDEST` summary.
The canonical package decodes all three opcodes and scans the immutable `Bytes` program to validate destinations.
The scan advances over whole `PUSH1` through `PUSH32` instructions, so a `0x5b` immediate byte cannot be mistaken for executable `JUMPDEST` syntax.
It preserves KEVM's false-`JUMPI` destination bypass, true-branch and unconditional destination checks, `Gjumpdest = 1`, `Gmid = 8`, `Ghigh = 10`, unary/binary underflow partitions, insufficient-gas behavior, and `EVMC_BAD_JUMP_DESTINATION` outcome.

The fail-closed KEVM gate passes with 449 descriptors, 103 native executions, and five native all-path proofs under K 7.1.337.
The twelve added behavior cases cover valid forward `JUMP`, true and false `JUMPI`, invalid opcode, out-of-range and PUSH-immediate destinations, both family underflow boundaries, insufficient gas, and a combined execution containing both conditional outcomes plus an unconditional jump.
Its structured behavior SHA-256 is `a3e2c4910a24ac98d11424e15016c06f0f6b83ae18c0669c9eddf35aabfb2991`.
Its normalized KORE SHA-256 is `f40756568a8f7d594eb14831e5dbf0ec1d70d312bfce4dad418617d1e5f3f04d`.
The combined control-flow claim and all four prior claims close with `#Top` through native `kprove`.

The unchanged KWasm and KMIR gates pass with 32 and 11 executions and one native proof each.
The complete IMP M4.1–M4.8 gate also passes with exact 1,206/1,206 native KORE parity, unchanged behavior evidence `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`, all 21 proof specifications, and unchanged compatibility evidence `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.

This tranche advances the explicit KEVM inventory but does not complete the port.
Environmental, memory, storage, call, creation, log, termination, transaction, schedule, account, cryptographic, and symbolic surfaces remain uncovered.

### Phase 19 — KEVM Shanghai execution-context tranche — complete; port incomplete

The next KEVM tranche selects the nullary `ADDRESS`, `ORIGIN`, `CALLER`, `CALLVALUE`, `CALLDATASIZE`, `CODESIZE`, `GASPRICE`, `RETURNDATASIZE`, `COINBASE`, `TIMESTAMP`, `NUMBER`, `PREVRANDAO`, `GASLIMIT`, `CHAINID`, `BASEFEE`, and `GAS` family from the pinned `evm.md` and Shanghai schedule.
The canonical package now carries the exact selected transaction, call, block, chain, output, and gas configuration cells.
Each operation enforces the 1,024-word push boundary before charging `Gbase = 2`, and `GAS` pushes the post-charge remainder.
The upstream `STOP` transition now clears `<output>` rather than preserving it.

The `STOP` rule exposed a shared authoring requirement rather than a port-local approximation opportunity.
Descriptor protocol 21 and Definition IR schema 14 add the pinned zero-argument `BYTES.empty` identity.
The facade spelling `bytes::empty()` emits `.Bytes` and remains typed through registry resolution, descriptor transport, Semantic IR, Definition IR, reference expansion, canonical K emission, and native frontend adaptation.

Ordinary KEVM development qualification now uses K-Rust behavior as the default authority.
The release-mode persistent runner executes all 105 cases in approximately three seconds and directly observes the `<output>` cell.
The structured K-Rust behavior SHA-256 is `3f0a2ee31bfc1e242c103f6dafac73d7330bcf7d162bd4f95e875fb5e4bada0c`.
The normalized KORE SHA-256 is `1298606514130917d09a3ce1451fa3716426540679f22b7b76d191337e801e72`.
The six Java/K proofs remain explicit milestone or final authority checks through `tests/kevm/verify.py --java-reference`; they are not run during ordinary development.

This tranche advances the explicit KEVM inventory but does not complete the port.
`BLOCKHASH`, memory, storage, copying, call, creation, log, explicit return/revert, transaction, schedule, account, cryptographic, and symbolic surfaces remain uncovered.

### Phase 20 — KEVM Shanghai block-history tranche — complete; port incomplete

The next KEVM tranche selects `BLOCKHASH` from the pinned `evm.md`, `schedule.md`, and `summaries/blockhash-summary.k` evidence.
The canonical package now carries the exact upstream `<blockhashes>` builtin-List cell and decodes opcode `0x40` without overlapping the invalid-opcode partition.
The lookup preserves the upstream newest-first traversal, current and future block rejection, 256-block cutoff, and zero sentinel.
Execution replaces the unary stack argument, advances the program counter by one, charges Shanghai `Gblockhash = 20`, and retains the existing underflow and out-of-gas ordering.

The K-Rust-first development corpus now contains 112 executions.
It covers the latest and older available hashes, the current-block exclusion, the 256-block boundary, the zero sentinel, stack underflow, insufficient gas, and a combined execution-context path.
The structured behavior SHA-256 is `f8e5d5f96c411272446a7de335b4fd7fbe8d1cbb466117c7629e864551aeb31b`.
The normalized KORE SHA-256 is `27c2e3e57cf8d5fc60c78daf9ed10a810ce73f2b4baac8c0da7d7df083627de3`.
The six Java/K proofs remain deferred to an explicit milestone or final `tests/kevm/verify.py --java-reference` run.

This tranche advances the explicit KEVM inventory but does not complete the port.
Memory, storage, copying, call, creation, log, explicit return/revert, transaction, schedule, account, cryptographic, and symbolic surfaces remain uncovered.

### Phase 21 — KEVM Shanghai memory tranche — complete; port incomplete

The next KEVM tranche selects `MLOAD`, `MSTORE`, `MSTORE8`, and `MSIZE` from the pinned `evm.md`, Shanghai schedule, and checked-in opcode summaries.
The canonical package now carries exact `<localMem>:Bytes` and `<memoryUsed>:Int` cells, zero-padded big-endian 32-byte reads, padded full-word writes, low-byte writes, and active-memory size observation.
Memory grows in 32-byte words and charges `Cmem(N) = 3*N + N*N/512`, including the quadratic expansion boundary.
The selected operations retain the upstream `Gverylow` or `Gbase` base cost, structural underflow, and insufficient-gas ordering.

Descriptor protocol 22 and Definition IR schema 15 add the pinned `BYTES.update` and `BYTES.padRight` operations.
Both operations remain typed through registry resolution, descriptor transport, Semantic IR, Definition IR, reference expansion, canonical K emission, and native frontend adaptation.

Ordinary qualification now compiles Definition IR directly through the KRS adapter, K-Rust frontend, and K-Rust backend.
The native frontend exposed a K-Rust semantic-cast defect for typed builtin `List:get`; KRS lowers that boundary directly to the generated `project:<Sort>` function and records the upstream issue in `K_RUST_UPSTREAM.toml`.
The shared K-Rust checkout remains clean, and the dedicated checkout retains only its solver-policy and deep-result changes.

The K-Rust-first development corpus contains 124 executions and seven deferred Java/K proofs.
The behavior matrix covers zero-padded reads, full-word and unaligned writes, no-expansion and quadratic-expansion boundaries, low-byte truncation, family underflow, out-of-gas, `MSIZE`, and a combined write/read/size execution through `STOP`.
K-Rust caught an invalid 17-gas premise in the combined memory claim; the exact selected schedule requires 20 gas, and the claim and corpus now agree.
The structured behavior SHA-256 is `fb36c7bdc155b79289a3864978ffab557186c0ebf2c1bc422a1c7b7dd601e973`.
The native K-Rust KORE SHA-256 is `b501017bd064c3a4a915c707575c23004f7c051a025e26f0230b5fdf1b505235`.
Java behavior and proof execution remain deferred to explicit final or requested validation.

This tranche advances the explicit KEVM inventory but does not complete the port.
Storage, copying, call, creation, log, explicit return/revert, transaction, schedule, account, cryptographic, and symbolic surfaces remain uncovered.

### Phase 22 — KEVM Shanghai non-account load/copy tranche — complete; port incomplete

The canonical KEVM package now implements `CALLDATALOAD`, `CALLDATACOPY`, `CODECOPY`, and `RETURNDATACOPY` against the pinned `evm.md` and four checked-in opcode summaries.
`CALLDATALOAD` performs a zero-padded big-endian 32-byte read without expanding local memory.
The three copy operations preserve the upstream top-first destination/source/width operand order, expand local memory in 32-byte words, and charge `Gverylow + Gcopy * ceil(width / 32)` plus exact memory expansion.
Calldata and program sources zero-pad out-of-range bytes.
Return-data copies require `source + width <= lengthBytes(output)` and otherwise consume the operands, charge gas and active memory, preserve local bytes, and halt with `EVMC_INVALID_MEMORY_ACCESS`.
Insufficient gas is resolved before the return-data bounds failure.

The K-Rust-first corpus contains 148 executions and eight deferred Java/K proofs.
It covers full and short calldata loads, normal and source-padded copies, zero-width non-expansion, the 33-byte copy-gas ceiling, every zero/one/two-operand copy underflow boundary, out-of-gas ordering, valid and invalid return-data bounds, and a combined load/copy path.
The fail-closed K-Rust behavior SHA-256 is `28f7b7c3912b13a978f47dc030d4e1cffcc37d9b1b7c7c26954e7e6ce885c6be`.
The native K-Rust KORE SHA-256 is `96fb32d6b25b80ca243f54ed43b6f691da9da6e432d89433374a73a050c1fd0f`.
Java behavior and proof execution remain deferred to explicit final or requested validation.

This tranche advances the explicit KEVM inventory but does not complete the port.
Storage, account access, calls, creation, logs, explicit return/revert, transactions, schedules, cryptographic hooks, and symbolic surfaces remain uncovered.

### Phase 23 — KEVM Shanghai current-account storage — complete; port incomplete

Descriptor protocol 23 and Definition IR schema 16 add typed `Map` lookup and key-membership operations plus K's builtin `Set` sort and its empty, item, concatenation, and membership operations.
The operations retain their result and operand sorts through facade marker identity, descriptor transport, Semantic IR, Definition IR, canonical K source emission, reference expansion, and direct K-Rust adaptation.
Typed Map lookup uses the same explicit native `project:<Sort>` boundary as typed List lookup, avoiding K-Rust's recorded semantic-cast erasure defect.

Focused native qualification verifies the closed registries, exact canonical source spellings, structural native terms, and the exact `Map:lookup`, `MAP.in_keys`, `SET.unit`, `SET.element`, `SET.concat`, and `SET.in` labels exposed by the pinned K-Rust prelude.
No Java frontend or backend participates in this development gate.

Descriptor protocol 24 and Definition IR schema 17 add classified repeated-cell multiplicity and collection type, nested ancestry-aware rule emission, and readable head-rule `requires` transport.
The canonical configuration now preserves `<accounts><account multiplicity="*" type="Map">` with nested `<acctID>`, `<storage>`, and `<origStorage>` cells; no permanent top-level current-storage adapter was introduced.

The KEVM package implements `SLOAD` and `SSTORE` with absent-slot zero fallback, accessed-storage Map-of-Sets, 100/2100 warm/cold loads, cold store surcharge, Shanghai set/reset/dirty costs, stipend and static-mode ordering, and the 4,800/19,900/2,800 refund cases.
Storage/access/refund mutation occurs only after successful charging, and the repeated account rule is guarded by equality between `<id>` and `<acctID>`.

K-Rust's own CLI initially rejected its generated parameterized repeated-cell initializer `initAccountCell(Init:Map)` during cell concretization.
The dedicated KRS checkout carries a focused local fix and regression, while the exact standalone reproducer and requested upstream action are recorded in `K_RUST_UPSTREAM.toml`.
The shared K-Rust checkout remains clean.

The independently expanded readable Rust originally lost the declaration owner
for nested account leaves and tried to resolve `account_id`, `storage`, and
`original_storage` as direct `Machine` fields.  The reference surface now emits
owner-qualified `cells!` fields, the macro transport retains those exact nested
owners, and protocol-v7 accepts declared nested-cell owners while the collector
still rejects identities absent from the fixed-cell table.  A focused
`NestedMachine`/`Store::env` regression and the full readable re-emission gate
both pass.

The K-Rust-first corpus contains 163 executions and eight deferred Java/K proofs.
It covers cold absent/present and repeated warm loads; clean set/reset/clear; dirty restoration refunds; stipend and ordinary out-of-gas; static violation; storage underflow; and deliberate non-selection of a mismatched account.
The fail-closed behavior SHA-256 is `773bd0c59d3d3144dba682b4f78ec6e7f88b8b77fa9bd2bb118646cc15a797d1`.
The native K-Rust KORE SHA-256 is `cdcb4ef444b2716e9b4fd1b62179b70b7a258df3da8a6bb8133c1b873624487d`.
No Java frontend or backend participated; the explicit final authority run remains deferred to `tests/kevm/verify.py --java-reference`.

### Phase 24 — KEVM Shanghai explicit return/revert — complete; port incomplete

The next control-flow tranche selects `RETURN` and `REVERT` from pinned
`evm.md` and the Shanghai schedule.  Both operations consume a memory start
and width, charge `Gzero = 0` plus exact memory expansion, copy a byte-exact
zero-padded range into `<output>`, and terminate without advancing `<pc>`.
`RETURN` selects `EVMC_SUCCESS`; `REVERT` selects `EVMC_REVERT`.

The implementation reuses the qualified Bytes and memory surfaces rather than
introducing an output adapter.  It preserves stack, output, memory, memory-use,
and gas state when expansion charging fails, and includes both binary-stack
underflow partitions.

The K-Rust-first corpus now contains 170 executions and eight deferred Java/K
proofs.  The behavior SHA-256 is
`8cf77c612be95a04e049334076071649649e155ef3b808fc04101f5166b561d9` and
the native K-Rust KORE SHA-256 is
`18356845d6d2c52a249b15c7c3aa9dca3f247dc3e2b8b4b66421bbb6f179005a`.
No Java frontend or backend participated.

### Phase 25 — KEVM Shanghai account queries — complete; port incomplete

Descriptor protocol 25 adds typed `#[k::rule(owise)]` metadata for ordered fallback rules.
The authored marker and `rule_owise` provenance survive ordinary, head, and configuration descriptors, Semantic IR, Definition IR, canonical K emission as effective priority 200, and deterministic readable expansion.
Overlap analysis compares the effective default priority 50 with the fallback priority 200, so a present-account rule and its absent-account fallback remain intentionally ordered rather than spuriously conflicting.

The KEVM account shape now includes nested `<balance>:Int` and `<code>:Bytes` leaves and the machine configuration includes `<accessedAccounts>:Set`.
The selected tranche implements `BALANCE`, `EXTCODESIZE`, `EXTCODECOPY`, and `SELFBALANCE`.
Present-account rules require exact equality between the requested address and `<acctID>`, while absent-account `BALANCE` and `EXTCODESIZE` rules return zero and absent-account `EXTCODECOPY` copies from empty bytes through an ordered fallback.

Berlin account access costs are exactly 100 for warm accounts and 2,600 for cold accounts.
An account enters `<accessedAccounts>` only after successful charging.
`EXTCODECOPY` additionally charges memory expansion and `3 * ceil(width / 32)`, copies bytes exactly, and right-pads missing source bytes with zero.
Out-of-gas behavior leaves the stack, local memory, active-memory words, gas, and account-access set unchanged.

The first fresh K-Rust execution exposed a decoder partition overlap because the invalid-opcode equation still included decimal opcodes 49, 59, 60, and 71.
Excluding the four newly implemented opcodes fixed the KRS semantics; this was not a K-Rust defect and is not recorded upstream.

The focused Rust gate and all 183 K-Rust corpus executions pass without Java.
The behavior SHA-256 is `e9a34043f4ef04e46cde7e4af46a475bdad43b821a2d08f7ec400079effa16d8`.
The native K-Rust KORE SHA-256 is `4f9702babfd0603d1e4bda0d57f1ce8cbfe24a47857ef97c60469b63aa580b42`.
The eight Java/K proofs remain deferred to the explicit final `tests/kevm/verify.py --java-reference` authority run.

### Phase 26 — KEVM Shanghai LOG0-LOG4 — complete; port incomplete

The exact builtin-List `<log>` configuration cell now holds typed `LogEntry` values containing the current address, an ordered builtin List of zero through four topics, and the byte-exact event data.
Successful execution appends one entry, consumes only the start, width, and selected topics, updates active memory words, advances the program counter, and deducts gas.

The Shanghai charge is memory expansion plus `Glog = 375`, `Glogdata = 8` per byte, and `Glogtopic = 375` per topic.
Stack underflow takes precedence over static-mode rejection, static rejection takes precedence over charging, and all log, stack, memory-use, program-counter, and gas state remains unchanged when charging fails.
Memory extraction uses the already qualified zero-padded Bytes boundary.

All five opcodes from `0xa0` through `0xa4` have direct K-Rust behavior evidence.
The 190-case corpus passes without Java with behavior SHA-256 `aff843ba6fca75a459621d009e3aae1a516241a306c25f07bfb421128fc6da5b` and native KORE SHA-256 `74f7aa3682f9763a9108c850307b0b063431927bc8c950da23b11104fed59f7a`.
The eight Java/K proofs remain deferred to final validation.

### Phase 27 — KEVM Shanghai SHA3 — complete; port incomplete

Descriptor protocol 26 and Definition IR schema 18 add the closed typed `krypto::keccak256_raw` function-hook identity.
The hook remains exactly `Bytes -> Bytes` through syntax parsing, provenance, descriptors, Semantic IR, Definition IR, canonical K emission as `KRYPTO.keccak256raw`, readable expansion, and direct K-Rust adaptation.

The KEVM package now decodes opcode `0x20`, extracts zero-padded memory bytes, hashes them with the selected hook, converts the digest to an unsigned big-endian word, and charges Shanghai `Gsha3 = 30`, `Gsha3word = 6`, and exact memory expansion.
The four-case tranche covers the standard empty and `abc` digests, stack underflow, and atomic out-of-gas behavior.

K-Rust's backend already implemented the hook, but its frontend omitted the `KRYPTO` namespace and silently compiled the application as an ordinary symbol.
The dedicated KRS checkout carries the minimal namespace fix and regression; `K_RUST_UPSTREAM.toml` records the upstream defect, while the shared checkout remains clean.

All 194 K-Rust corpus executions pass without Java.
The behavior SHA-256 is `2ac33e0f5c9adcc353ebb50acc4d04f5a8bd5168796f46ef8f47c728668fcda6` and the native K-Rust KORE SHA-256 is `696e4665c1b9c076b7315acbc908b29ca8093de2588037367f25af96c6028e54`.
The eight Java/K proofs remain deferred to final validation.

### Phase 28 — KEVM Shanghai EXTCODEHASH — complete; port incomplete

The canonical account shape now includes the upstream `<nonce>:Int` leaf and the native and deferred-reference harnesses expose its `NONCE` initializer.
The selected `#kevmAccountEmpty` boundary follows the pinned upstream definition: an account is empty exactly when its code is empty and both nonce and balance are zero.

`EXTCODEHASH` decodes opcode `0x3f`, charges 100 gas for a warm account or 2,600 gas for a cold account, marks access only after successful charging, returns `Keccak(code)` for a present nonempty account, and returns zero for an empty or absent account through the ordered fallback.
The corpus independently qualifies code-, nonce-, and balance-based nonemptiness plus empty-present, absent, underflow, and atomic out-of-gas behavior.

All 201 K-Rust corpus executions pass without Java.
The behavior SHA-256 is `e0dc0292635871695fdee0b0e1d423f228d66cf2a08a95e61f321d39143a68f9` and the native K-Rust KORE SHA-256 is `6d8eb6a9c9598b1e7886f40a41e838f1623ac6b32d67845e735945ee6fede191`.
The eight Java/K proofs remain deferred to final validation.

### Phase 29 — KEVM Shanghai PUSH0 — complete; port incomplete

The pinned Shanghai inventory exposed `PUSH0` as an uncovered active opcode before the call-frame tranche.
The canonical package now decodes `0x5f` as `PUSHZERO`, pushes the exact zero word, advances the program counter by one, charges `Gbase = 2`, and reuses the qualified 1,024-word push boundary and atomic gas failure.

All 203 K-Rust corpus executions pass without Java.
The behavior SHA-256 is `fbac2e70e2c882e977a4f035d7890af07756e9830658f6080a8764ec4e8a409f` and the native K-Rust KORE SHA-256 is `8b11c02cdee0585a93c4457598d369a4373b0f23243637cc48b5f251079a7af2`.
The eight Java/K proofs remain deferred to final validation.

### Phase 30 — KEVM Shanghai STATICCALL empty/absent branch — complete; port incomplete

The call-family audit identifies upstream whole nested `<callState>` and `{<accounts>|<substate>}` fragments stored in builtin Lists as the required boundary for nonempty child execution and rollback.
KRS does not yet expose those first-class cell terms, and this phase does not introduce a port-local frame adapter.

The source-complete branch that does not require a child frame now qualifies `STATICCALL` to non-precompile absent accounts and present empty accounts.
It decodes `0xfa`, enforces the six-operand stack contract, charges exact Berlin warm/cold account access plus both argument and return memory regions, marks access and expands memory only after successful charging, clears return data, returns success, and retains atomic underflow and out-of-gas behavior.
Nonempty-code and precompile targets have no success rule and are not claimed complete.

All 208 K-Rust corpus executions pass without Java.
The behavior SHA-256 is `548897681091f221fe0435e33895ba13234b964c1ca2a9d7004ee8076bd7d22d` and the native K-Rust KORE SHA-256 is `a5ec34d806f128baba9a6a6e55c39a11992f4b3b014c9c0176badb5ccf5ca58e`.
The eight Java/K proofs remain deferred to final validation.

### Phase 31 — K-Rust-first KMIR and KWasm qualification — complete

The KMIR and KWasm default gates now use the same direct Definition IR to K-Rust frontend/backend route as KEVM.
Routine runs build `krs-native-compile` and `krs-native-runner`, compile the pinned Definition IR without parsing emitted K, and execute each concrete corpus through one persistent worker.
The previous `kompile`, `krun`, and `kprove` route remains available only through `--java-reference`.

Structured bootstrap preparation now removes the loader-added `DEFAULT-CONFIGURATION` module and its dangling imports before inserting the authored definition.
This prevents the fallback `<k>` initializer from colliding with KWasm's real `<instrs>` computation cell.
A focused adapter regression compiles a fixed `<instrs>` configuration, and `K_RUST_UPSTREAM.toml` records the upstream structured-loading gap.

The KWasm gate passes at descriptor protocol 26 and Definition IR schema 18 with 60 descriptors, 32 K-Rust executions, behavior SHA-256 `4a3b6107cb23fa451a392d0a0ef1d42203d5eb64cda8cbcda025e75d2458afd5`, and direct KORE SHA-256 `35835f531a224c68f5ab63892448d2a2f60a6f0c268be521189a8f4df04245d1`.
The KMIR gate passes at the same schemas with 94 descriptors, 11 K-Rust executions, behavior SHA-256 `f10f7a2df6103ffca4814598f42667b123a682489228eaa1c18419c5582f0d4a`, and direct KORE SHA-256 `33e12b776065b81010aa8e9eca0b3b68bb8cd9bc5775332eeffcc68064321b67`.
No Java or Haskell backend was run during this phase.

### Phase 32 — KEVM nested STATICCALL return and rollback — complete; port incomplete

KRS and the dedicated K-Rust checkout now preserve complete nested `<callState>` fragments through the builtin-List call stack.
The KEVM slice installs a nonempty-code child context, restores all 15 caller fields, and models success, revert, and represented exceptional return branches.
Typed `<interimStates>` snapshots preserve the selected repeated-account record plus complete substate, drop on success, and restore on revert or exception.
The selected-account boundary is exact for the current static/non-mutating account surface but must become a full repeated-account collection snapshot before mutable nested calls or creation.

The native-only gate passes 212 K-Rust executions with behavior SHA-256 `05522da133bebf7a7619d1d52aeb55896bdadd2189a89f2bfbd8160093d35dc1` and direct KORE SHA-256 `8b29f3a39aa9dabf9140462ca543f175420b837a40fe4c5487399f7c38443326`.
No Java or Haskell backend was run during this phase.

### Phase 33 — KEVM Shanghai identity precompile — complete; port incomplete

Address 4 now selects the Shanghai `ID` precompile through a structurally distinct base-gas result, so ordinary account calls and precompile calls cannot overlap in K-Rust rule dispatch.
The port charges exact `15 + 3 * ceil(input-width / 32)` execution gas, applies EIP-150 forwarded-gas capping, returns the input bytes exactly, copies bounded returndata into caller memory, warms the account, and consumes the forwarded allowance on precompile failure.
The two new corpus cases qualify both sufficient and insufficient forwarded gas while observing empty call/world stacks.

The complete native-only checkpoint passes with 260 equations, 259 machine rules, 8 claims, 888 descriptors, and 214 K-Rust executions.
The behavior SHA-256 is `7f2f4377a87584e7e1879b756d0d30a09390dddccaf02ccac5304fa1cc89eaa9` and the direct KORE SHA-256 is `fa81cb7cb6b4e0d514bea5abb69028d7f71ae63dd25f681692ab56b4cf3024c0`.
All eight Java reference proofs remain deferred to the explicit `--java-reference` final-validation mode; no Java or Haskell backend was run during this phase.

### Phase 34 — KEVM Shanghai SHA-256 precompile — complete; port incomplete

Descriptor protocol 27 and Definition IR schema 19 add `krypto::sha256_raw` to the closed typed hook catalog.
The KRS route preserves the `Bytes -> Bytes` identity through descriptor collection, both IRs, canonical K emission as `KRYPTO.sha256raw`, readable expansion, and direct K-Rust adaptation.
K-Rust already implemented raw digest evaluation but omitted `KRYPTO.sha256raw` from its dispatcher; the dedicated checkout carries the one-line dispatch fix and a standard-vector backend regression, while `K_RUST_UPSTREAM.toml` records the upstream issue.

Address 2 now implements the Shanghai `SHA256` precompile with exact `60 + 12 * ceil(input-width / 32)` gas, EIP-150 forwarded-gas success/failure, byte-exact output, bounded caller-memory copying, access warming, and empty call/world stack postconditions.
The complete native-only milestone gate passes 907 descriptors and 216 K-Rust executions with behavior SHA-256 `9688304cb7bf003c1c06eddd154f8e411e48c8f785f5c9c85739eab344e29237` and direct KORE SHA-256 `a0180c02bec835c6d822ca1050db9fe4ae3648500d96846b74e4fbdf1b220dfe`.
The definition contains 264 equations, 262 machine rules, and 8 claims across 907 descriptors.
The refreshed provenance, schema, source, artifact, expansion, native KORE, and behavior pins all pass their fail-closed checks.
No Java or Haskell backend was run during this phase; eight Java reference proofs remain explicitly deferred to the optional `--java-reference` final gate.

### Phase 35 — KEVM Shanghai RIPEMD-160 precompile — complete; port incomplete

Descriptor protocol 28 and Definition IR schema 20 add `krypto::ripemd160_raw` to the closed typed hook catalog.
The KRS route preserves its `Bytes -> Bytes` identity through descriptor collection, both IRs, canonical K emission as `KRYPTO.ripemd160raw`, readable expansion, and direct K-Rust adaptation.
K-Rust already implemented RIPEMD-160 and generic raw digest evaluation but omitted the raw dispatcher entry; the dedicated checkout carries the one-line dispatch fix and standard empty-input byte-vector regression, while `K_RUST_UPSTREAM.toml` records the upstream issue.

Address 3 implements the Shanghai `RIP160` precompile with exact `600 + 120 * ceil(input-width / 32)` gas, a byte-exact 20-byte digest left-padded to 32 bytes, EIP-150 forwarded-gas success/failure, bounded caller-memory copying, access warming, and empty call/world stack postconditions.
The complete native-only milestone gate passes 926 descriptors and 218 K-Rust executions with behavior SHA-256 `42a3d597a59afde0478dae10cf7d614ab3bef0b002df8a4e863804eaf47d5fc6` and direct KORE SHA-256 `1d77a68b723560b94de2bafc6498ee516ca9571135e28910e58c12f25445bd8b`.
The definition contains 268 equations, 265 machine rules, and 8 claims across 926 descriptors.
No Java or Haskell backend was run during this phase; eight Java reference proofs remain explicitly deferred to the optional `--java-reference` final gate.

### Phase 36 — KEVM Shanghai ECREC precompile — complete; port incomplete

Descriptor protocol 29 and Definition IR schema 21 add `krypto::ecdsa_recover` to the closed typed hook catalog.
The KRS route preserves its `Bytes * Int * Bytes * Bytes -> Bytes` identity through descriptor collection, both IRs, canonical K emission as `KRYPTO.ecdsaRecover`, readable expansion, and direct K-Rust adaptation.
The dedicated K-Rust checkout now returns empty Bytes for invalid concrete recovery inputs instead of Bottom, and `K_RUST_UPSTREAM.toml` records the correctness defect and focused regressions.

Address 1 implements the Shanghai `ECREC` precompile with fixed 3,000 gas, zero-padded 128-byte input splitting, valid recovered-address output, successful empty returndata for invalid signatures, EIP-150 forwarded-gas failure, bounded caller-memory copying, access warming, and empty call/world stack postconditions.
The complete native-only corpus passes 949 descriptors and 221 K-Rust executions with behavior SHA-256 `de383024cbcc4efc3ba9ee4db7f689267af845b550005699f3db49afee851c44` and direct KORE SHA-256 `9d5829c79cc082bb4fd9a3c3b6f591953623242bb764f6af9f66ae7bdea520f5`.
The definition contains 274 equations, 268 machine rules, and 8 claims across 949 descriptors.
No Java or Haskell backend was run during this phase; eight Java reference proofs remain explicitly deferred to the optional `--java-reference` final gate.

### Phase 37 — KEVM Berlin MODEXP precompile — complete; port incomplete

Address 5 implements the Berlin EIP-2565 `MODEXP` precompile through the already-qualified `int::pow_mod` and `int::log2` boundaries.
The implementation parses zero-padded 32-byte base, exponent, and modulus lengths; consumes zero-padded big-endian operands; emits exactly the declared modulus width; returns empty Bytes for a zero output width; and returns zero at the declared width when the modulus is zero.
The semantic wrapper totalizes modulus zero before the raw `INT.powmod` hook, matching pinned KEVM rather than treating K-Rust's partial raw hook as a defect.

Gas charging implements `max(200, floor(ceil(max(base length, modulus length) / 8)^2 * max(adjusted exponent length, 1) / 3))` with the Berlin divisor of three.
Focused native cases pin `2^5 mod 13 = 6`, modulus zero, zero output width, 199/200 forwarded-gas failure/success, and a 216-gas vector whose exponent length exceeds 32 bytes.
The persistent native runner now accepts repeatable `--case` selectors for focused inner-loop qualification while an unfiltered invocation retains the complete corpus as the milestone gate.

The complete native-only corpus passes 992 descriptors and 226 K-Rust executions with behavior SHA-256 `2f28aab675ac152c03c6da3f68d0476bb91d08881c7525c5bca552873b8a13b4` and direct KORE SHA-256 `46db9fbf7e127ea6885c7f2fab6d6b8761a34f08c4df77faecf5078747a14c3a`.
The definition contains 290 equations, 271 machine rules, and 8 claims across 992 descriptors.
No K-Rust bug or missing feature was encountered, and no Java or Haskell backend was run; eight Java reference proofs remain explicitly deferred to the optional `--java-reference` final gate.

### Phase 38 — KEVM Istanbul ECADD precompile — complete; port incomplete

Descriptor protocol 30 and Definition IR schema 22 add declared-sort `krypto::bn128_valid` and `krypto::bn128_add` identities to the closed typed hook catalog.
The KRS route enforces `G1Point -> Bool` and `G1Point * G1Point -> G1Point`, emits the exact `KRYPTO.bn128valid` and `KRYPTO.bn128add` names, and preserves them through descriptor collection, both IRs, canonical K emission, and direct K-Rust adaptation.

K-Rust did not implement any pinned BN128 hook.
The dedicated `k-rust-krs` checkout now implements G1 validity and addition through `substrate-bn` 0.6.0 with Ethereum-compatible infinity, field-bound, curve-membership, and two-`Int` constructor behavior.
Focused backend regressions cover the standard EIP/revm addition vector, infinity, an invalid field coordinate, and an off-curve point.
`K_RUST_UPSTREAM.toml` records the partial local fix and leaves multiplication, G2 validity, and pairing open for addresses 7 and 8.

Address 6 implements Istanbul `ECADD` with zero-padded 128-byte coordinate input, exact 64-byte output, fixed 150 gas charging, invalid-point precompile failure, EIP-150 forwarded-gas failure, bounded caller-memory copying, access warming, touched-account tracking, and empty call/world stack postconditions.
The complete native-only corpus passes 1,027 descriptors and 230 K-Rust executions with behavior SHA-256 `a7335b2307a2df0dca1ceb9f15786d13d1bbb13824c422da21d791ce94bf59a1` and direct KORE SHA-256 `bc6cddc9ccdf34abb2a9ea6938255d466e5c819226e6a5d3958008268dec84c0`.
The definition contains 299 equations, 274 machine rules, and 8 claims across 1,027 descriptors.
No Java or Haskell backend was run; eight Java reference proofs remain explicitly deferred to the optional `--java-reference` final gate.

### Phase 39 — KEVM Istanbul ECMUL precompile — complete; port incomplete

Descriptor protocol 31 and Definition IR schema 23 add declared-sort `krypto::bn128_mul` to the closed typed hook catalog.
The KRS route enforces `G1Point * Int -> G1Point`, emits the exact `KRYPTO.bn128mul` name, and preserves it through descriptor collection, both IRs, canonical K emission, and direct K-Rust adaptation.

The dedicated `k-rust-krs` checkout implements multiplication through `substrate-bn` 0.6.0 and reduces the complete unsigned 256-bit scalar rather than narrowing it to a machine integer.
Focused backend regressions cover generator multiplication by two, zero-scalar infinity, invalid input points, and negative hook inputs.
`K_RUST_UPSTREAM.toml` records multiplication as locally fixed while G2 validity and pairing remain open for address 8.

Address 7 implements Istanbul `ECMUL` with zero-padded 96-byte input, exact 64-byte output, fixed 6,000 gas charging, invalid-point precompile failure, EIP-150 forwarded-gas failure, bounded caller-memory copying, access warming, touched-account tracking, and empty call/world stack postconditions.
The complete native-only corpus passes 1,053 descriptors and 234 K-Rust executions with behavior SHA-256 `0b930a079c7f2e56711fc4e71eebb8c47efb01bdf844c816a4b767bbfbf8c2d9` and direct KORE SHA-256 `6c8f71fb2af7626ef2ffec1dc8e07909a30ed50b5bed6ebdf07ff2eb03778a1f`.
The definition contains 306 equations, 277 machine rules, and 8 claims across 1,053 descriptors.
No Java or Haskell backend was run; eight Java reference proofs remain explicitly deferred to the optional `--java-reference` final gate.

### Phase 40 — KEVM Istanbul ECPAIRING precompile — complete; port incomplete

Descriptor protocol 32 and Definition IR schema 24 add declared-sort `krypto::bn128_g2_valid` and builtin-List `krypto::bn128_ate` identities to the closed typed hook catalog.
The KRS route enforces `G2Point -> Bool` and `List * List -> Bool`, emits the exact `KRYPTO.bn128g2valid` and `KRYPTO.bn128ate` names, and preserves them through descriptor collection, both IRs, canonical K emission, and direct K-Rust adaptation.

The dedicated `k-rust-krs` checkout implements G2 field, curve, and subgroup validation and pairing-product evaluation through `substrate-bn` 0.6.0.
Focused backend regressions cover G2 generator and infinity validity, off-curve and out-of-field rejection, empty-product identity, a non-identity generator product, a cancelling product, injected concrete List elements, mismatched lists, invalid points, and opaque lists.
`K_RUST_UPSTREAM.toml` records the complete BN128 hook-family local fix for upstream review.

Address 8 implements Istanbul `ECPAIRING` with exact 192-byte tuple validation, upstream-compatible imaginary/real G2 byte decoding, G1/G2 infinity encoding, exact 32-byte Boolean output, `45,000 + 34,000 * pair-count` gas charging, invalid-length and invalid-point precompile failure, EIP-150 forwarded-gas failure, bounded caller-memory copying, access warming, touched-account tracking, and empty call/world stack postconditions.
The complete native-only corpus passes 1,100 descriptors and 240 K-Rust executions with behavior SHA-256 `7d7fd9dac9d3088682fa3ea27686c2a431219ded26f8a13400d2f4025f024673` and direct KORE SHA-256 `b9244153684ae6cb40f17954d5e67c5590a1e52fdcff54e14fadea87d819ffb0`.
The definition contains 321 equations, 280 machine rules, and 8 claims across 1,100 descriptors.
No Java or Haskell backend was run; eight Java reference proofs remain explicitly deferred to the optional `--java-reference` final gate.

### Phase 41 — KMIR typed locals and move invalidation — complete; port incomplete

The KMIR locals cell now uses the source-shaped builtin `List` of typed entries rather than the port-local `Map<Int, MirValue>` adapter.
`newLocal` and initialized entries retain opaque type and mutability metadata, assignment preserves both fields, and `place(local(...), .ProjectionElems)` is the exact selected place boundary.
Copy reads preserve the source entry; move reads return its value while replacing the source with a metadata-preserving moved entry; moved entries may be reassigned and cannot be read.

This tranche exposed a shared KRS lowering gap because readable three-argument cell updates were previously validated only as `map::update`.
Head-rule lowering now resolves the cell sort and admits the registered persistent update for either builtin `Map` or builtin `List`, while retaining exact collection/base identity checks.
No descriptor-protocol or Definition IR schema change was required.

The focused semantics test passes with 130 descriptors and the native K-Rust corpus passes 13 executions with behavior SHA-256 `4863d82660266c837d0e85c496403a3157598b8983380fd3d47bf391383db983`.
The direct K-Rust KORE SHA-256 is `558e53aed25196b7b8f0e35a648c5d022f7ccd3d913b3b4439d6a62de7c79ec0`.
Nonempty projection traversal is the next KMIR data boundary.
No Java or Haskell backend was run; the reference proof remains deferred to the optional `--java-reference` final gate.

### Phase 42 — KMIR aggregate field projection — complete; port incomplete

KMIR `Place` terms now admit one source-shaped `projectionElemField(fieldIdx(...), Ty)` in addition to `.ProjectionElems`.
Typed aggregate values retain their variant index and builtin-List fields.
Projected copies select the field through typed List lookup; projected assignment rebuilds the field list, aggregate, and enclosing typed local through nested persistent List updates while preserving local type and mutability metadata.

Two new K-Rust cases qualify a nonzero field read and a field write observed through a later projected copy.
The native corpus passes 15 executions with behavior SHA-256 `2958d25ed98f5bc25ef8dc0449f75b06d801ca8702808e6ac0e98b539f177258`.
The definition contains 31 machine rules and one claim across 145 descriptors, and its direct K-Rust KORE SHA-256 is `e0769f3821a79e1a523c394b9b5f0f5c6dd526737dffb4972d2ce8e609278b3a`.
No K-Rust bug or missing feature was encountered.
No Java or Haskell backend was run; the reference proof remains deferred to the optional `--java-reference` final gate.

### Phase 43 — KMIR binary operations and ordered `SwitchInt` — complete; port incomplete

KMIR values now use the selected upstream `Integer(value, width, signed)` and `BoolVal(value)` constructor shapes.
Rvalues use `rvalueUse` and staged `rvalueBinaryOp` evaluation with source-shaped `binOpAdd`, `binOpSub`, `binOpMul`, and all six integer comparison operators.
The selected arithmetic rules preserve equal operand width and signedness metadata and are qualified only on non-overflowing concrete inputs; integer truncation, overflow behavior, and checked arithmetic remain explicit later work.

The temporary Boolean two-target `SwitchInt` adapter has been removed.
Terminators now carry `switchTargets(Branches, otherwise)`, scan ordered `branch(value, target)` entries, match Boolean discriminants through the upstream zero/one convention, match selected integer discriminants, and fall back to the otherwise block.
Width-aware unsigned truncation for integer discriminants remains deferred.

The K-Rust-only corpus adds subtraction, multiplication, the `42 > 0` comparison from pinned `const-arithm-simple.rs`, another ordered comparison, comparison-driven control flow, ordered Boolean branch scanning, and ordered integer branch scanning.
The native corpus passes 22 executions with behavior SHA-256 `3e04c4f0c8d1531b69b6d55bdff97a4f1efa93b0164409c5d588202c31506041`.
The definition contains 44 machine rules and one claim across 188 descriptors, and its direct K-Rust KORE SHA-256 is `bf4a10f594cd61830656edfc9885ab93a6e713596f91cabd58d2c4ede2d86d80`.
No K-Rust bug or missing feature was encountered.
No Java or Haskell backend was run; the reference proof remains deferred to the optional `--java-reference` final gate.

### Phase 44 — KMIR Boolean comparison and bitwise operations — complete; port incomplete

The staged `rvalueBinaryOp` path now covers Boolean operands for all six comparison constructors, following pinned KMIR's `false < true` ordering.
It also covers `binOpBitAnd`, `binOpBitOr`, and `binOpBitXor` for equal-metadata integer operands and Boolean operands.
The selected bitwise results preserve integer width and signedness, while Boolean exclusive disjunction uses inequality as the exact truth function.

Pinned `bitwise-not-shift.rs` is now acceptance evidence for integer and Boolean bitwise behavior.
Five new K-Rust executions qualify all three integer operations, Boolean exclusive disjunction, and Boolean ordering.
The native corpus passes 27 executions with behavior SHA-256 `8e780b730d402e8e27697893d228d4744b9c6cbf10c51d96ed6ac6d1c67cdbbf`.
The definition contains 56 machine rules and one claim across 206 descriptors, and its direct K-Rust KORE SHA-256 is `b2b5f0894308d5f7742adaa6a652e804056a18623042d4179694785ccc3388e1`.
No K-Rust bug or missing feature was encountered.
No Java or Haskell backend was run; the reference proof remains deferred to the optional `--java-reference` final gate.

### Phase 45 — KMIR width-aware numeric core — complete; port incomplete

KMIR now defines total signed and unsigned width-normalization functions and selects between them through the value's signedness bit.
Ordinary add, subtract, multiply, and divide rules require the infinite-precision result to equal its normalized representation, preserving pinned undefinedness on overflow; division and truncating remainder also require a nonzero divisor.
`rvalueCheckedBinaryOp` stages both operands and returns the source-shaped variant-zero aggregate containing the wrapped result and exact overflow flag for addition, subtraction, and multiplication.

The binary family now includes signed and unsigned left/right shifts and the unchecked shift variants with their width guard.
Unary evaluation covers signed negation, Boolean not, and signed/unsigned integer bitwise not.
Integer `SwitchInt` matching now compares branch values with the discriminant's unsigned width-normalized representation, including the pinned `-127_i8` to `129` example.

The K-Rust corpus adds 18 executions covering no-overflow and overflowing checked arithmetic, signed/unsigned wraparound, division and remainder truncating toward zero, normal and unchecked shifts, unary wraparound and not, and width-aware signed discriminants.
The native corpus passes 45 executions with behavior SHA-256 `071c1cab4e736d6e6e4735b529b6fb12e1cc54010e4a9c1af3d497c486c020f2`.
The definition contains seven equations, 70 machine rules, and one claim across 256 descriptors, and its direct K-Rust KORE SHA-256 is `44c8b65efb494136c5350699692d58c267b73f96165d6198d32b9dbf7c6460be`.
No K-Rust bug or missing feature was encountered.
No Java or Haskell backend was run; the reference proof remains deferred to the optional `--java-reference` final gate.

### Phase 46 — KMIR recursive aggregate field projection — complete; port incomplete

The one-field projection special case has been replaced by partial recursive `#readProjection` and `#writeProjection` functions over source-shaped `ProjectionElems`.
Reads traverse arbitrary `projectionElemField` chains through typed builtin-List lookup.
Writes rebuild the selected field and every enclosing aggregate through persistent List updates, preserving nested variant indices plus the enclosing local's type and mutability.
Invalid projection/value combinations remain undefined because the recursive functions are partial.

Pinned `struct.rs` is now acceptance evidence for aggregate-field behavior.
Two new K-Rust executions qualify a two-level nested field read and a two-level nested write observed through a later read.
The native corpus passes 47 executions with behavior SHA-256 `994b5a7303689a3a0f4368963ac83ee6710354e5e2c6b999d601f3fc9734fef4`.
The definition contains 11 equations, 70 machine rules, and one claim across 264 descriptors, and its direct K-Rust KORE SHA-256 is `2bdb48cf9de9c358c07ce2b621f258cd814992a2cdd0bbb52e920a2a67b1a64d`.
No K-Rust bug or missing feature was encountered.
No Java or Haskell backend was run; the reference proof remains deferred to the optional `--java-reference` final gate.

### Phase 47 — KMIR local-indexed range projection — complete; port incomplete

KMIR now retains source-shaped `Range(List)` values and `projectionElemIndex(local(...))` projection syntax.
The partial `#expectUsize` function accepts exactly a typed `Integer(_, 64, false)` index local, matching the pinned source boundary.
Recursive reads select the indexed element before continuing through the remaining projections.
Recursive writes persistently rebuild the selected element, enclosing ranges or aggregates, and the typed local while preserving type and mutability metadata.
Invalid indices, index-local shapes, and value/projection combinations remain undefined.

Pinned `array_write.rs` is now acceptance evidence for the dynamic array-index boundary; its reference and dereference behavior remains explicitly deferred.
Two new K-Rust executions qualify a local-indexed range read and a local-indexed persistent write observed through a later read.
The native corpus passes 49 executions with behavior SHA-256 `8cfeea1eaf7a26d493610ec971cf9bbb274378d189dd5e21d9e706977f4235d8`.
The definition contains 14 equations, 70 machine rules, and one claim across 273 descriptors, and its direct K-Rust KORE SHA-256 is `168ca1421b8808fb114360ed0016c4890049679aad053f22d62983a6f14cfeaf`.
No K-Rust bug or missing feature was encountered.
No Java or Haskell backend was run; the reference proof remains deferred to the optional `--java-reference` final gate.

### Phase 48 — KMIR constant-index range projection — complete; port incomplete

KMIR `Place` terms now admit source-shaped `projectionElemConstantIndex(offset, minLength, fromEnd)` values.
Front-relative reads and writes select the supplied in-range offset.
End-relative reads and writes require the supplied minimum length to equal the concrete range length and consistently select `minLength - offset`.
Both routes continue through arbitrary remaining selected projections and persistently rebuild every enclosing range or aggregate while preserving typed-local metadata.

The pinned upstream source contains an inconsistency for the end-relative case: its prose and `CtxIndex` write path use `MINLEN -Int OFFSET`, while its read expression uses `getValue(ELEMENTS, OFFSET)`.
KRS follows the documented Stable MIR meaning and records the actionable upstream report in `MIR_SEMANTICS_UPSTREAM.toml`.
Pinned `exec-smir/arrays/array_write.state` supplies concrete source-shaped front-relative evidence.

Four new K-Rust executions qualify front- and end-relative reads plus persistent writes.
The native corpus passes 53 executions with behavior SHA-256 `edf22b0202f2c5a7c2db5baed1541f879f46696396ef8c3c3e9c9f02cbe260c7`.
The definition contains 18 equations, 70 machine rules, and one claim across 279 descriptors, and its direct K-Rust KORE SHA-256 is `06654ac2508c21faeb46b92ec3ec51aca8522233691b0510f11708203fb96a09`.
No K-Rust bug or missing feature was encountered.
No Java or Haskell backend was run; the reference proof remains deferred to the optional `--java-reference` final gate.

### Phase 49 — KMIR same-frame references and dereferencing — complete; port incomplete

KMIR now retains source-shaped erased regions, shared and default mutable borrow kinds, metadata sizes, metadata triples, `Reference(height, place, mutability, metadata)` values, `rvalueRef`, and `projectionElemDeref`.
Selected reference creation targets the current stack frame and derives reference mutability from the source borrow kind.
Dynamic index projections are frozen into front-relative constant indices at borrow time, so later mutation of an index local cannot retarget an existing reference.

Dereference reads fetch the same-frame pointee and append the retained place projections before continuing the selected recursive traversal.
Dereference writes redirect `#setLocalValue` to the pointee local, append the retained and remaining projection paths, and persistently rebuild the pointee without replacing the reference.
The selected metadata is the exact thin-pointer triple `metadata(noMetadataSize, 0, noMetadataSize)` emitted by the pinned array program.
Stack-relative references, pointer offsets, metadata-driven slice truncation, raw pointers, and allocation references remain deferred.

Pinned `array_write.smir.json` now supplies serialized Stable MIR evidence for mutable reference creation through a dynamic array index, dereference assignment, and later indexed copies.
Three new K-Rust executions qualify shared reference creation, dynamic-index freezing followed by dereference read, and a mutable write through a retained constant-index reference.
The native corpus passes 56 executions with behavior SHA-256 `a0422115f128b36c8c128c084b85fb355d8fa7c64bad96843426cce2d7bf9ec7`.
The definition contains 29 equations, 74 machine rules, and one claim across 328 descriptors, and its direct K-Rust KORE SHA-256 is `96ddf2b9bed65cb4f2cc1c6f93748a52ba847619ea916eae1bc8855b97940267`.
No K-Rust bug or missing feature was encountered.
No Java or Haskell backend was run; the reference proof remains deferred to the optional `--java-reference` final gate.

### Phase 50 — KMIR subslice projection — complete; port incomplete

KMIR `Place` terms now admit source-shaped `projectionElemSubslice(from, to, fromEnd)` values.
Front-relative reads remove `from` elements from the front and `to` elements from the back.
End-relative reads follow the pinned source's reversed operand interpretation.
Nested writes rebuild the selected value and persistently replace the same contiguous region while preserving enclosing ranges, aggregates, and typed-local metadata.
Retained references preserve subslice projections unchanged when their place is frozen.

This tranche extends the shared KRS List surface with exact `LIST.range` and `LIST.updateAll` operations in descriptor protocol 33 and Definition IR schema 25.
The K-Rust backend already implements both hooks.
Its frontend assigns the `LIST.updateAll` production without an explicit `symbol(...)` the synthesized label `updateList(_,_,_)_LIST_List_List_Int_List`; the KRS adapter now uses that pinned identity and a focused regression verifies it against the production hook.
No K-Rust checkout change or upstream report was required.

Pinned `array_match.rs` is now acceptance evidence for the Stable MIR subslice boundary.
Four new K-Rust executions qualify front- and end-relative reads plus nested persistent writes in both orientations.
The native corpus passes 60 executions with behavior SHA-256 `6918f8a904d1ff6c58186dfa1104167a907ce9e829dbc44f5d31dd9c2b3753f7`.
The definition contains 36 equations, 75 machine rules, and one claim across 342 descriptors, and its direct K-Rust KORE SHA-256 is `1df01324c61877a08e07600b0e5dba1c6c40f6fd120a2c503255140731e26660`.
The complete default KMIR gate passes at protocol 33, and the protocol/schema compatibility refresh also passes the KEVM 240-execution and KWasm 32-execution K-Rust gates.
The shared Rust workspace library suite passes 104 tests.
No Java or Haskell backend was run; the reference proof remains deferred to the optional `--java-reference` final gate.

### Phase 51 — KMIR projected moves and checked-arithmetic assertions — complete; port incomplete

KMIR now retains the source `Moved` value inside aggregates and ranges, in addition to the existing metadata-preserving whole-local moved state.
A projected `Move` returns the selected value and persistently reconstructs its enclosing value with only the selected projection replaced by `Moved`.
The selected route preserves the enclosing local's type and mutability and remains partial for unsupported projection/value combinations.

The control-flow surface now includes source-shaped `assert(condition, expected, message, target, unwindActionContinue)` terminators and the checked-arithmetic `assertMessageOverflow` constructor.
Assert operands use the existing explicit evaluation pipeline.
A matching `BoolVal` continues at the target block; a mismatch leaves `#ProgramError(AssertError(message))` terminal at the head of the computation, with the target continuation retained behind it exactly as in the pinned source rule sequence.
Other assertion messages and unwind actions remain deferred.

Pinned `arith.smir.json` supplies serialized Stable MIR evidence for checked addition and multiplication followed by an `Assert` whose condition is a projected `Move` of the overflow flag.
Two new K-Rust executions qualify the no-overflow continuation and overflowing terminal-error paths.
The native corpus passes 62 executions with behavior SHA-256 `6df248ebbe08683e264b9fd4b239ad71dc74b9794eb7b6b56159fe4898c52a7f`.
The definition contains 36 equations, 81 machine rules, and one claim across 369 descriptors, and its direct K-Rust KORE SHA-256 is `2d3bf7e81955c84aa6c7bb9faf91e7bb0c134d3a8938c200d8909aad2cff4de7`.
No shared KRS protocol or Definition IR change was required.
The complete default KMIR gate passes at descriptor protocol 33 with 62 K-Rust executions.
The KEVM and KWasm source-ledger preflights also pass after pinning the updated shared coverage ledger; their semantic artifacts were not regenerated because this tranche changed no shared KRS source or schema.
No Java or Haskell backend was run; the reference proof remains deferred to the optional `--java-reference` final gate.

### Phase 52 — KMIR remaining primitive arithmetic, downcast, and runtime terminators — complete; port incomplete

KMIR now retains the source `binOpAddUnchecked`, `binOpSubUnchecked`, and `binOpMulUnchecked` constructors.
Each uses the same width-aware arithmetic and undefined-on-overflow guard as the pinned source rules, while checked arithmetic remains confined to the existing wrapped-result route.

The recursive place engine now admits `projectionElemDowncast(variantIdx(...))`.
Reading reinterprets an aggregate with the selected variant before continuing through the projection tail; writing persistently rebuilds the selected aggregate and enclosing typed local, including writes through fields of the downcast variant.

The control-flow surface now includes source-shaped `terminatorKindDrop(place, target, unwind)` and `terminatorKindUnreachable` values.
`Drop` follows the pinned semantics' current no-op elaboration and enters its target block without inspecting or mutating the place.
`Unreachable` leaves terminal `#ProgramError(ReachedUnreachable)` state.

Seven new K-Rust executions qualify all three unchecked arithmetic constructors on defined inputs, downcast reinterpretation and field update, drop continuation, and unreachable failure.
The native corpus passes 69 executions with behavior SHA-256 `da32f14b143747925a8049d9d1a869439cc93246ca890ebc9b436bd5bfc3e3cb`.
The definition contains 39 equations, 87 machine rules, and one claim across 392 descriptors, and its direct K-Rust KORE SHA-256 is `3668773329a373472675f005ec7f350ce377345b496477a194208bd5f01d4a8e`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 69 K-Rust executions.
The KEVM and KWasm source-ledger preflights pass after pinning the updated shared coverage ledger; their semantic artifacts were not regenerated because this tranche changed no shared KRS source or schema.
No Java or Haskell backend was run; the reference proof remains deferred to the optional `--java-reference` final gate.

### Phase 53 — KMIR regular function calls and stack frames — complete; port incomplete

KMIR now uses the source-shaped nested current frame with current-function identity, caller metadata, destination, continuation target, unwind action, typed locals, a function map, and a call stack.
Regular constant-target calls resolve the callee through the function map, save the caller frame, reserve locals from the callee declarations, and begin the callee's first block.

Argument setup covers constants plus copied and moved whole-local operands.
Copies preserve the saved caller local; moves replace it with a metadata-preserving moved entry before the caller is restored.
Nested returns restore the caller function, body, metadata, and locals, place an initialized callee return value at the destination, and resume at the selected target block.
Unit returns restore the caller without writing an uninitialized return local.

Pinned Stable MIR artifacts cover a nested zero-argument call chain and constant/copied argument transfer.
Five new K-Rust executions qualify returned-value placement, nested unit calls, constant arguments, copied arguments, and caller-side moved-argument invalidation.
The native corpus passes 74 executions with behavior SHA-256 `fae9d39724016563bf6b33dad24544901edc04840e0ffe5930ee40cbfde12e11`.
The definition contains 44 equations, 95 machine rules, and one claim across 450 descriptors, and its direct K-Rust KORE SHA-256 is `95293b5366b4e686cf9404f4ef7ac92f0b6dc7df71edc012f543bf391e448a9a`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 74 K-Rust executions.
The KEVM and KWasm source-ledger pins retain their existing semantic artifacts while acknowledging the updated shared coverage ledger.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 54 — KMIR cross-frame reference arguments and returns — complete; port incomplete

Reference-valued call arguments now follow the pinned frame-height protocol.
Copying or moving an argument increments every selected reference height recursively through aggregate and range values after the caller frame is pushed.
Returning a value decrements those heights before writing into the restored caller.

Read-only dereference now resolves a positive-height reference through the saved stack frame at `height - 1`, adjusts any fetched reference by the traversed height, and applies the retained place and operand projections against that frame's locals.
The existing same-frame route remains the fallback for height zero.
Cross-frame mutation and nested cross-frame dereference chains remain deferred rather than being approximated by current-frame writes.

Pinned `refAsArg` and `refReturned` Stable MIR plus concrete state artifacts supply direct authority for callee dereference and returned-reference restoration.
Two new K-Rust executions qualify a copied reference dereferenced by its callee and a reference returned to and dereferenced by its caller.
The native corpus passes 76 executions with behavior SHA-256 `90573c79c87b5757b7b18fe702a3679c95ea00785aa7d516da49479baffb65ce`.
The definition contains 54 equations, 98 machine rules, and one claim across 471 descriptors, and its direct K-Rust KORE SHA-256 is `1620f30a47334f09dbc0c8db0584a30f46a0590f50120fb2dcc9dc85899ce4e6`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 76 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 55 — KMIR cross-frame mutable-reference writes — complete; port incomplete

Positive-height mutable-reference writes now select the saved frame at `height - 1` and update the referenced caller local rather than falling through to current-frame mutation.
Retained reference projections are appended to the post-dereference write path.
The saved typed local preserves its original type and mutability.

Replacement values are recursively adjusted by `-height` before storage, following the pinned upstream `#adjustRef(#buildUpdate(...), 0 -Int FRAME)` policy.
This keeps references written by a callee in caller coordinates rather than validating only the scalar `mutableRef` example.

Pinned `mutableRef.rs`, Stable MIR, and concrete state artifacts supply direct authority for callee mutation of caller state.
One K-Rust execution qualifies the source-shaped scalar write, and a second qualifies caller-coordinate restoration for a reference-valued write.
The native corpus passes 78 executions with behavior SHA-256 `85d9e8f7dc399dca982170edefa6a4f5bbe6dc1df110ee9270b8d2be8ff2b7e9`.
The definition contains 56 equations, 99 machine rules, and one claim across 478 descriptors, and its direct K-Rust KORE SHA-256 is `9494d7de734f9408beb4fc45dbbc287a787938697d3c59937c897c23b7830f16`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 78 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 56 — KMIR stack-aware nested reference reads — complete; port incomplete

Projected copy reads now use an execution-level traversal over every selected aggregate, downcast, range-index, subslice, and dereference step.
The traversal retains access to the call stack between steps, so a dereference that fetches another positive-height reference can select its saved frame and continue.
References transferred across two saved call frames use the same height-indexed route.

Pinned `doubleRef` and `refAsArg2` source, Stable MIR, and concrete state artifacts supply direct authority for repeated dereference and multi-frame reference transfer.
Three new K-Rust executions qualify repeated same-frame dereference, a positive-height dereference followed by another positive-height dereference, and a read through two saved call frames.
Representative aggregate, range, and frozen-index reads also pass through the new traversal.
The native corpus passes 81 executions with behavior SHA-256 `6af61b32a29817f0e36ec7fa2b33c9d531e40ef844da265b8144570f7305a9ee`.
The definition contains 56 equations, 107 machine rules, and one claim across 487 descriptors, and its direct K-Rust KORE SHA-256 is `ad7c1dacdae49f36f01ecf972333b925b67d37839f475a1aafc5154239d76996`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 81 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 57 — KMIR shared read/write/move projection traversal — complete; port incomplete

Projected reads, writes, and moves now use one upstream-shaped execution traversal carrying a local or saved-stack target, persistent reconstruction contexts, current locals, and an explicit action.
Field, range-index, and subslice traversal records the enclosing value needed for persistent reconstruction.
Dereference discards obsolete contexts and redirects the target to the referenced current or saved local.

Nested positive-height dereference writes now continue through references fetched from caller frames before updating the final saved target.
Projected moves through a cross-frame reference return the selected value in current coordinates and rebuild the caller aggregate with only that projection replaced by `Moved`.
Reference-valued replacements retain the upstream recursive `-height` restoration policy.

Pinned `weirdRefs` source, Stable MIR, and concrete state artifacts supply direct authority for nested mutable dereference and reference/field chains.
Two new K-Rust executions qualify nested cross-frame mutation and cross-frame projected move invalidation.
Representative nested aggregate, indexed range, same-frame dereference write, and checked projected-move behaviors remain green through the shared route.
The native corpus passes 83 executions with behavior SHA-256 `6f60db8ed84bb49b34f51491603b3c80b4e601b44e8dbe4e16ba6fb4466ab500`.
The definition contains 60 equations, 104 machine rules, and one claim across 515 descriptors, and its direct K-Rust KORE SHA-256 is `c9d80249c6e43c431d1658680ed6f5e6f6cc73bcf0b5fb481ed4db7a9a24b7db`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 83 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 58 — KMIR pointer offsets and metadata-truncated references — complete; port incomplete

KMIR now retains the source `PointerOffset(offset, originSize)` projection over `Range` values and applies reference metadata in the pinned upstream order.
Dereference first applies the frozen projections retained in the reference place, then a metadata-provided pointer offset, then static or dynamic metadata truncation, and finally the remaining operand projections.
No-metadata range references retain the source array-head behavior, while no-metadata non-range references pass through unchanged.

Pointer-offset traversal records the original range as a persistent reconstruction context.
Metadata truncation narrows the selected view without adding a reconstruction context, following the pinned `rt/data.md` equations.
Writes therefore rebuild through the pointer offset and any earlier field/index/subslice contexts while leaving the truncation itself view-only.
The same traversal restores caller coordinates for a pointer-offset write through a saved stack frame.

Pinned `offset_read`, `offset_write`, `offset_struct_field_read`, and `offset_struct_field_write` source, Stable MIR, and concrete state artifacts supply direct authority for the selected behavior.
Five new K-Rust executions qualify retained and metadata-provided offsets, dynamic and static truncation, aggregate-contained pointer offsets, persistent writes, and cross-frame mutation.
The native corpus passes 88 executions with behavior SHA-256 `2de12e49f41544faa570d4bc57195d7db7885b323fba6a484269368d18fd14a5`.
The definition contains 66 equations, 109 machine rules, and one claim across 534 descriptors, and its direct K-Rust KORE SHA-256 is `4126cb73768af4289e1bac5a2b04bab7cc246623c9ec6c9fb9af4b807f143254`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 88 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 59 — KMIR raw local pointers and AddressOf — complete; port incomplete

KMIR now retains the source-shaped `rvalueAddressOf(Mutability, Place)` operation and `PtrLocal(height, place, mutability, metadata)` value.
Direct local addresses freeze dynamic index projections before storing the pointer, so later index-local mutation cannot retarget the address.
Addressing a reference through the sole `Deref` projection uses the pinned upstream shortening rule and converts the reference directly to a raw pointer over the same place and metadata.

Raw-pointer dereference reuses the shared projection traversal for local and saved-stack targets.
It therefore inherits field/index/subslice reconstruction, pointer offsets, metadata truncation, cross-frame writes, and caller-coordinate restoration without a parallel pointer adapter.
Recursive reference-height adjustment now covers `PtrLocal` values as well as pointers nested inside aggregates and ranges, so copied pointer arguments select their caller frame and restore correctly on return.

Pinned `ref_ptr_cases` source, Stable MIR, and concrete state artifacts supply direct authority for local addresses, frozen array-element identity, reference-to-pointer conversion, and raw-pointer mutation.
Five new K-Rust executions qualify direct address reads, frozen dynamic indices, reference-to-pointer writes, pointer argument transfer and cross-frame mutation, and pointer-offset raw-pointer writes.
The native corpus passes 93 executions with behavior SHA-256 `94f655d52675adb0a1d3ee8b28ae89aa0a671197960cdd66e701b152513d58d3`.
The definition contains 68 equations, 114 machine rules, and one claim across 547 descriptors, and its direct K-Rust KORE SHA-256 is `3fa2c3625c6d474a4f93cc1821aceecf4aec6241203596076a10e3c2d161ea3e`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 93 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 60 — KMIR raw-pointer identity comparison — complete; port incomplete

KMIR now implements the pinned raw-pointer `binOpEq` and `binOpNe` contract.
Two pointers compare equal exactly when their frame height, frozen projected place, and complete metadata match; pointer mutability is deliberately ignored.
The implementation uses repeated structural pattern variables for the equal case and ordered fallback rules for inequality, so it preserves pointer provenance without inventing numeric host addresses.

The existing pinned `ref_ptr_cases` evidence directly exercises aliasing references, distinct locals, and distinct array-element addresses.
Five new K-Rust executions qualify equality across different mutability, inequality for distinct locals and array projections, metadata-sensitive inequality, and frame-height-sensitive inequality.
The native corpus passes 98 executions with behavior SHA-256 `196be580799f090f5248807b619c2fbcba26f86d6ecfaadf454bc9081d219088`.
The definition contains 68 equations, 118 machine rules, and one claim across 551 descriptors, and its direct K-Rust KORE SHA-256 is `cb53a1042047cdbfc13837b2ea6d281481bd11294b4768c007ddb16f18d67e37`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 98 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 61 — KMIR pointer metadata and bounded offset arithmetic — complete; port incomplete

KMIR now retains `unOpPtrMetadata` and `binOpOffset` from the pinned pointer-operation surface.
Dynamic metadata extraction returns `Integer(size, 64, false)` for both `PtrLocal` and `Reference` values and remains undefined for metadata shapes for which upstream supplies no rule.

A zero offset preserves every component of any raw pointer, including a thin pointer without origin metadata.
Nonzero offsets preserve the current view size and advance only the metadata offset when the operand is nonnegative and the resulting offset does not exceed the static or dynamic origin size.
The exact one-past-end result remains defined as a pointer value, matching upstream; subsequent dereference remains guarded by the projection traversal.

Pinned `offset_get_unchecked` source, Stable MIR, and concrete state artifacts supply direct authority for pointer metadata extraction, offset arithmetic, and offset-element reads.
Five new K-Rust executions qualify pointer and reference dynamic metadata, zero-offset thin-pointer identity, a dynamic interior offset followed by dereference, and the static one-past-end boundary.
The native corpus passes 103 executions with behavior SHA-256 `fdf1d3936524950570fb756f9fc0c36c96e536371b414f95b620d14fe3e0abb3`.
The definition contains 68 equations, 123 machine rules, and one claim across 560 descriptors, and its direct K-Rust KORE SHA-256 is `a0b7c0e2893da391d244d2f9809be2ab98fd123f22c6abf1581a05b7ae59caf7`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 103 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 62 — KMIR pointer unsizing coercion — complete; port incomplete

KMIR now retains the source-shaped `rvalueCast(castKindPointerCoercion(pointerCoercionUnsize), operand, target)` boundary.
The cast evaluates copied and moved operands through the existing operand machinery, so move invalidation remains uniform rather than requiring a cast-specific local adapter.

Raw local pointers and references with static size metadata are converted to the corresponding dynamic size.
Frame height, frozen place, mutability, pointer offset, and origin metadata are preserved exactly.
Unsupported coercions and operands remain undefined; general `PtrToPtr` casts remain deferred until their type-directed projection and metadata conversion dependencies are present.

The pinned `offset_get_unchecked` source, Stable MIR, and concrete state artifacts supply direct authority for the selected `PointerCoercion::Unsize` behavior.
Three new K-Rust executions qualify raw-pointer provenance preservation, reference unsizing through a moved operand, and metadata extraction from an unsized pointer.
The native corpus passes 106 executions with behavior SHA-256 `1f417dfb8dae6e174eef1f1132aec97db617dba34139be29a2dfe20dd898302f`.
The definition contains 68 equations, 126 machine rules, and one claim across 573 descriptors, and its direct K-Rust KORE SHA-256 is `746dd1e67528813efc7d5114ca29ff295b334490a09f36b6de48677c73fc812a`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 106 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 63 — KMIR concrete pointer types and same-pointee casts — complete; port incomplete

KMIR now retains the concrete `<types>` lookup boundary as a builtin map from `Ty` to the selected `typeInfoPtrType(pointee)` surface.
The exact all-path claim carries the new fixed cell explicitly, preserving closed-configuration coverage.

Whole-local copy and move `rvalueCast(castKindPtrToPtr, operand, target)` operations resolve source and target type entries before evaluating the operand.
When both pointer types name the same pointee, every raw-pointer component is preserved unchanged, matching the pinned higher-priority upstream rule.
The move form continues through the shared operand machinery and invalidates its source local.
Missing type entries, different pointees, projected operands, and projection-changing casts remain undefined.

Pinned `rt/data.md` and `rt/types.md` rules supply direct authority for the source cast staging, type lookup, and identical-pointee compatibility contract.
Two new K-Rust executions qualify copy and move casts between distinct pointer types with a common pointee.
The native corpus passes 108 executions with behavior SHA-256 `c0efc639626051392fb6fa5630e9c3f4e191319a47b98866b2d0a17502ecae26`.
The definition contains 71 equations, 129 machine rules, and one claim across 588 descriptors, and its direct K-Rust KORE SHA-256 is `cd8e8c0d7d6992d56ceedc8937acad767ac8bc24fa36b4c7dc4d56fdad710f4a`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 108 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 64 — KMIR recursive array pointer casts — complete; port incomplete

KMIR now retains primitive-u8, dynamic-slice, and unsized-array `TypeInfo` entries for the selected projection-changing `PtrToPtr` boundary.
The cast resolver follows the pinned upstream source-first recursion through explicit compare, source, and target phases, avoiding ambiguous overlapping fallback rules while preserving the source rule order.

Source arrays append the source-shaped zero `projectionElemConstantIndex`, target arrays append `projectionElemSingletonArray`, and inverse adjacent projections cancel.
Thin and dynamic metadata convert according to the resolved target pointee, while pointer frame height, base place, mutability, offset, and origin metadata remain unchanged.
The recursive traversal supports nested arrays and rejects incompatible terminal pointees by remaining undefined.
Projected operands, static-array lengths, transparent-wrapper and zero-sized projections, allocation references, opaque casts, and subtype projections remain deferred.

Pinned `rt/types.md`, `prove-rs/pointer-cast.rs`, and the `pointer-cast-length-test-fail` source, Stable MIR, and state artifacts supply direct authority for source-first array traversal, pointer projection, metadata conversion, and the deliberate invalid-length boundary.
Four new K-Rust executions qualify slice-to-element dereference, element-to-slice construction, inverse projection cancellation through a roundtrip, and nested slice-to-element conversion.
The native corpus passes 112 executions with behavior SHA-256 `43f55f9fbe7b9f9c9265c9b98677f766ec76f3cfb4443a78aa1f277aa548fc7f`.
The definition contains 82 equations, 135 machine rules, and one claim across 632 descriptors, and its direct K-Rust KORE SHA-256 is `15bb33b93d203d33e52bfcd9c43455c8b7198461238557cf4f24673ea66e3b3f`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 112 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 65 — KMIR fixed-array pointer metadata — complete; port incomplete

KMIR now retains source-shaped fixed-array lengths as `someTyConst(tyConst(tyConstKindValue(...)))` values with allocation bytes, empty provenance, alignment, and mutability.
The selected unsigned `usize` allocation bytes are decoded little-endian, matching pinned KMIR's concrete `readTyConstInt` boundary without replacing it by an integer-length adapter.

The pointer-cast resolver already cancels inverse array-element and singleton-array projections, so equal-element slice/fixed-array and differing fixed-array casts preserve the same pointer place.
Target metadata conversion now covers thin-to-static, dynamic-to-static, static-to-dynamic, and static-to-static sizes while retaining the upstream source-size origin.
Construction of a pointer to a longer fixed array remains allowed as upstream specifies; insufficient origin length remains a later dereference failure rather than a cast failure.
Signed constants, non-value TyConst kinds, nonempty provenance, transparent-wrapper and zero-sized projections, and allocation references beyond fixed-length metadata remain deferred.

Pinned `rt/types.md`, `rt/data.md`, `prove-rs/pointer-cast.rs`, and the `pointer-cast-length-test-fail` source, Stable MIR, and state artifacts supply direct authority for the allocation-backed length, metadata conversion, and deliberate invalid-length boundary.
Three new K-Rust executions qualify slice-to-fixed-array conversion, fixed-array-to-slice conversion, and a moved fixed-array pointer length change with ordinary invalidation.
The native corpus passes 115 executions with behavior SHA-256 `c8f6b5d851c8cb4f68f92c13c80cd1c30ec6efad72d3c5a152df2f590eb09624`.
The definition contains 88 equations, 135 machine rules, and one claim across 660 descriptors, and its direct K-Rust KORE SHA-256 is `462df2bc83098bf7fbc225a8d4507e926f1d5964a19a8a6edc7fb19f866f8b5e`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 115 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 66 — KMIR zero-sized pointer casts — complete; port incomplete

KMIR now retains the source `typeInfoVoidType` zero-sized pointee and the `projectionElemToZST` / `projectionElemFromZST` cast projections.
Material-to-ZST and ZST-to-material `PtrToPtr` casts preserve pointer frame height, base place, mutability, and metadata while appending the corresponding source marker.
Adjacent inverse markers cancel during cast-projection append, recovering the original place across a roundtrip.

The explicit TypeInfo cases keep `#zeroSizedType` total over the retained metadata subset and make the cast rules structurally disjoint for KRS's overlap proof.
Pinned KMIR defines construction and inverse cancellation for these projections but no dereference traversal rule, so dereferencing an outstanding ZST marker remains deliberately undefined.
Function-item, empty-tuple, and empty-struct ZST classification, transparent wrappers, and ZST materialization remain deferred.

Pinned `rt/types.md` supplies direct authority for void-type classification, material/ZST cast direction, the no-recursion boundary, and inverse cancellation.
Three new K-Rust executions qualify both standalone directions and a moved roundtrip with ordinary source invalidation.
The native corpus passes 118 executions with behavior SHA-256 `417b6c6b502fda09cd3f7ebe274d5a68845925df9e091ed4c9b9f0e2c8a714e4`.
The definition contains 95 equations, 141 machine rules, and one claim across 681 descriptors, and its direct K-Rust KORE SHA-256 is `c50e97cb9c8ad176c85e4d951c1c170984f6de990e345030b66c4cbee136bdcc`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 118 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 67 — KMIR transparent-wrapper pointer casts — complete; port incomplete

KMIR now retains source-shaped singleton `typeInfoStructType` metadata, including `AdtDef`, singleton `Tys`, and `someLayoutShape(layoutShape(fieldsShapeArbitrary(mk(machineSize(0) .MachineSizes)), ...))`.
The local `String` token surface carries the ignored struct name.
KRS independent expansion now preserves declared token-sort constructor fields as symbolic terms over concrete token newtypes instead of rendering a nonexistent algebraic `StringSort` trait.

The pointer-cast resolver follows pinned KMIR's source-first transparent-wrapper rules.
Source structs append `projectionElemField(fieldIdx(0), FIELD)`, target structs append `projectionElemWrapStruct`, and the exact array-to-wrapper case takes priority over ordinary source-array unwrapping.
Only `projectionElemWrapStruct` followed by its field projection cancels at runtime, preserving the valid cancellation direction documented by pinned `rt/data.md`.

Wrapper projection traversal materializes `Aggregate(variantIdx(0), ListItem(VALUE) .List)` and records `CtxWrapStruct`.
Persistent writes first rebuild the selected singleton aggregate and then remove the synthetic wrapper context before updating the underlying field value.

Four new K-Rust executions qualify wrapper-to-field dereference reads, field-to-wrapper dereference reads, moved roundtrip cancellation, and persistent writes through a wrapper pointer.
The native corpus passes 122 executions with behavior SHA-256 `73f684bb61ca48defa2b3824151a20a5988a707cd18c60c8f039b28d94c893c4`.
The definition contains 102 equations, 145 machine rules, and one claim across 746 descriptors, and its direct K-Rust KORE SHA-256 is `7d9b5a519f5241edd98157b9a360afd5afdd06e55abc688d0e8177239dbfeb5d`.
The shared KRS reference projection changed without a descriptor protocol or Definition IR schema change, and its full compiler test suite passes.
No K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 122 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 68 — KMIR raw-pointer/reference type metadata — complete; port incomplete

KMIR now retains the source `typeInfoRefType(pointee)` constructor alongside `typeInfoPtrType(pointee)`.
Reference outer types are non-zero-sized and require no metadata of their own, matching the pinned type helpers.

Raw `PtrLocal` values now support all four raw-pointer/reference source and target type combinations for `PtrToPtr`.
Equal pointees preserve the complete pointer and metadata, while unequal pointees enter the existing source-first projection and target-metadata conversion route.
This retains the source distinction between value representation and type metadata: the runtime value remains a raw pointer even when its source or target type entry is a reference type.

Three new K-Rust executions qualify reference-to-pointer same-pointee preservation, raw-pointer-slice to reference-element conversion followed by dereference, and reference-element to reference-slice conversion.
The native corpus passes 125 executions with behavior SHA-256 `3e1d3af09a6e90ecdbaf99fe5003de8f58c5259d6647ddbe0f6d1fd7dba730e9`.
The definition contains 104 equations, 151 machine rules, and one claim across 756 descriptors, and its direct K-Rust KORE SHA-256 is `77513d66e89786445701127ae7b7659403e883dfea92440e07c6348134b635eb`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 125 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 69 — KMIR allocation-reference reads — complete; port incomplete

KMIR now retains source-shaped `allocId(Int)` allocation identities and `AllocRef(AllocId, ProjectionElems, Metadata)` values.
The concrete configuration adds an allocation-memory `Map` keyed by `AllocId`, matching the selected concrete lookup role of pinned KMIR's `<memory>` cell without introducing a local-address adapter.

Read-only dereference of an allocation reference restarts shared projection traversal from the selected allocation value, discards obsolete local reconstruction contexts, replays the allocation reference's retained projections, applies its static, dynamic, or absent metadata truncation, and then continues with the operand projections.
The stored pointer offset is intentionally ignored, matching pinned `rt/data.md` and its existing FIXME.
The rule is restricted to read actions, so this tranche does not silently enable mutation or move invalidation of typically read-only allocated constants.

Three new K-Rust executions qualify direct scalar allocation lookup, retained allocation-field projection, and dynamic allocation-slice truncation.
Pinned `alloc.md`, `rt/value.md`, `rt/configuration.md`, and `rt/data.md` provide direct authority for the identity, value, configuration, and traversal shapes.
The native corpus passes 128 executions with behavior SHA-256 `5654ab148767886e23b905f9921a993345863716744763f3c931d29a1598abe9`.
The definition contains 104 equations, 152 machine rules, and one claim across 764 descriptors, and its direct K-Rust KORE SHA-256 is `483a2f1646502b7531b7547c641422ebf99afabc814b1c9cfb38f6ee408c3ce3`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 128 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 70 — KMIR allocation-reference pointer metadata — complete; port incomplete

Allocation references now participate in pinned KMIR's selected fat-pointer operations.
`PointerCoercion::Unsize` converts the current `staticSize` to `dynamicSize` while preserving the `AllocId`, retained projections, pointer offset, and origin metadata exactly.
`unOpPtrMetadata` extracts a dynamic allocation-reference size as an unsigned 64-bit `Integer`, matching the existing local pointer/reference result shape.

Two new K-Rust executions qualify source-preserving allocation-reference unsizing and subsequent dynamic metadata extraction.
The native corpus passes 130 executions with behavior SHA-256 `929c4e6b42cb2e9fd4ef60ca0ef076ad707941240c0e0185a150ef76d94a8947`.
The definition contains 104 equations, 154 machine rules, and one claim across 766 descriptors, and its direct K-Rust KORE SHA-256 is `247a27618b38b9dbde194576a9adebac0e94147981a362d5f7853d180b09c30a`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 130 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 71 — KMIR same-representation pointer transmutation — complete; port incomplete

KMIR now retains the source `castKindTransmute` boundary for local references, raw pointers, and allocation references.
Whole-local copy or move operands resolve the source local type and target type through the concrete `<types>` map.
The complete value is preserved only when both type keys resolve to equal `TypeInfo`, matching pinned KMIR's supported identity case without guessing byte-layout compatibility.
Move operands continue to use ordinary source invalidation.

Three new K-Rust executions qualify allocation-reference copy transmutation, local-reference copy transmutation, and raw-pointer move transmutation across distinct type keys with equal representations.
The native corpus passes 133 executions with behavior SHA-256 `98f068c183c27eb6a68e26f90f6ddface578c48662b591dc4aad04ae258f3120`.
The definition contains 104 equations, 159 machine rules, and one claim across 775 descriptors, and its direct K-Rust KORE SHA-256 is `2dde940d8d31c677bdc5e0901a9c54f7630d788ff6e405b8ba56f7882280c272`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 133 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 72 — KMIR traversal-based reference creation — complete; port incomplete

KMIR `rvalueRef` no longer constructs a same-frame `Reference` directly from a syntactic place.
It now enters the shared projection traversal with a reference-creation action, derives initial metadata from the local type and selected projections, and completes according to the resolved local, saved-stack, or allocation target.

Projection reconstruction now retains each field's `Ty` and distinguishes pointer-offset contexts from ordinary subslices.
The source-shaped `#projectionsFor` route freezes dynamic indices as front-relative constant indices and reconstructs field, subslice, pointer-offset, and transparent-wrapper projections in source order.
Dynamic metadata placeholders are replaced by the final concrete `Range` view length.
Dereferencing an allocation reference during reference creation restarts traversal from the allocation-memory value and completes as `AllocRef`, so allocation reborrowing is an operational path rather than preloaded constructor data.

Two new K-Rust executions qualify allocation-element reborrowing with a frozen projected identity and dynamic allocation-slice reborrowing with recomputed metadata.
The existing direct and dynamically indexed local-reference cases remain unchanged under the new traversal route.
The native corpus passes 135 executions with behavior SHA-256 `85b7a9f71879a3ff2cfba1fe068cbb57a49e8646b0e5a158271688f2e4b7a52a`.
The definition contains 122 equations, 163 machine rules, and one claim across 811 descriptors, and its direct K-Rust KORE SHA-256 is `f300a7a4685a952225e1cfca92f25f3239af9b599f99cea0c94c2bade4aebef1`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 135 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 73 — KMIR allocated-reference constants — complete; port incomplete

KMIR now retains the full source `operandConstant(constOperand(span, noUserTypeAnnotationIndex, mirConst(constantKindAllocated(allocation), ty, mirConstId)))` boundary for allocated reference constants.
The allocation retains its bytes, alignment, mutability, and singleton `provenanceMapEntry(offset, AllocId)` rather than accepting a predecoded `AllocRef` adapter.

Evaluation resolves the target `TypeInfo` and referenced allocation through the concrete `<types>` and `<memory>` maps.
A missing target type, pointee type, or allocation therefore remains undefined through the same partial lookup boundary as pinned KMIR.
An eight-byte reference derives thin metadata from the pointee type, while a sixteen-byte reference decodes the final eight bytes as an unsigned little-endian dynamic size and uses that value for both current and origin metadata.

Two new K-Rust executions qualify a thin allocated constant followed by scalar dereference and a fat allocated constant followed by both allocation-view truncation and dynamic metadata extraction.
The native corpus passes 137 executions with behavior SHA-256 `cebdcfc1125c999e2b22bed416cee35bbac4831847e5fda2667a7e3fc3f4afec`.
The definition contains 124 equations, 164 machine rules, and one claim across 820 descriptors, and its direct K-Rust KORE SHA-256 is `2e877f647f3031cf59e72176db3642dd2b90a65245d6ba8035a85ecbe3f0d898`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 137 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 74 — KMIR allocated scalar constants — complete; port incomplete

KMIR now decodes source-shaped allocated constants with empty provenance into Boolean and integer runtime values.
The selected `PrimitiveType` surface retains `primTypeBool`, every stable MIR signed integer kind from `isize` through `i128`, and every unsigned kind from `usize` through `u128`.
The pinned 64-bit target fixes `isize` and `usize` at 64 bits.

Decoding requires the allocation byte length to equal the target width, reads the bytes little-endian, and applies the existing signed or unsigned width truncation before constructing `Integer(value, width, signed)`.
Boolean decoding accepts only the one-byte encodings zero and one.
Missing type entries, invalid Boolean bytes, and mismatched integer byte lengths remain undefined rather than producing adapted values.

Three new K-Rust executions qualify source Boolean decoding followed by unary negation, negative `i16` decoding followed by addition, and `u128` decoding followed by multiplication.
The native corpus passes 140 executions with behavior SHA-256 `89fc0600509ac2aaf15842a9baf3d4f9bd38a9dd9d074f8359a3704c60dd64c8`.
The definition contains 140 equations, 165 machine rules, and one claim across 876 descriptors, and its direct K-Rust KORE SHA-256 is `eb1c23bb1cfc9bb19e48c33dcd30f73c4a11727f5a1686aadf0ee9bab11c6ad6`.
No shared KRS protocol or Definition IR change was required, and no K-Rust bug or missing feature was encountered.
The complete default KMIR gate passes at descriptor protocol 33 with 140 K-Rust executions.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 75 — KMIR aggregate allocation decoding — complete; port incomplete

KMIR now decodes source-shaped allocated fixed arrays, dynamic slices, and arbitrary-layout structs through the pinned `rt/decoding.md` contracts.
The fixed-array route decodes its element count from the existing allocation-backed `TyConst`, computes element sizes recursively, and succeeds only when exactly that many elements consume the allocation bytes.
The dynamic-slice route requires a positive element size and exact divisibility before using the same recursive element decoder.
The struct route retains declared field order while selecting each field's half-open byte interval from its machine-size offset and recursively computed field size.
Its allocation extent is the maximum offset-plus-size boundary, so reordered and padded layouts do not collapse into a packed adapter.

This tranche extends the shared typed Bytes surface with half-open `BYTES.substr` in descriptor protocol 34 and Definition IR schema 26.
The source emitter and reference expander use `substrBytes(BYTES, START, END)`, while the K-Rust adapter targets the pinned `substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int` identity.
Focused registry, arity, emitter, expansion, and native-adapter tests pass, and the complete Rust workspace suite passes with the externally pinned Z3 4.12.5 profile.

The independent expanded-source gate exposed one source-level constructor-order defect before qualification.
`DecodeAllocatedValue` declared its Rust fields in a different order from its authored syntax, so named readable construction was correct while expanded positional construction inferred one binding at both `Map` and `Bytes` sorts.
Aligning declaration order with syntax order restores exact independent expansion without changing emitted K, K-Rust KORE, or behavior.
This is a KRS source-authoring invariant, not a K-Rust backend defect.

Four new K-Rust executions qualify fixed `u16` array decoding followed by indexed projection, dynamic signed-integer slice decoding followed by indexed projection, reordered and padded struct decoding followed by field projection, and nested fixed-array decoding inside a struct followed by field and index projection.
The native corpus passes 144 executions with behavior SHA-256 `65a4ea10bef509f594ca874fe71743b859da0f6541120dc7ec3fd33638f688b8`.
The definition contains 158 equations, 165 machine rules, and one claim across 908 descriptors, and its direct K-Rust KORE SHA-256 is `7cf90d35642ce920677d83837ac1a976631342bbfbb856e43c00f496478a8a07`.
The complete default KMIR gate passes at descriptor protocol 34.

Because the serialized builtin-operation catalog changed, the compatibility refresh regenerated protocol/schema metadata and ran both complete downstream K-Rust gates.
KEVM passes 1,100 descriptors and 240 executions, and KWasm passes 60 descriptors and 32 executions, both at descriptor protocol 34.
Their emitted K, native KORE, and behavior pins remain unchanged.
No K-Rust bug or missing feature was encountered, so `K_RUST_UPSTREAM.toml` requires no Phase 75 entry.
No Java or Haskell backend was run; all final reference comparisons and proofs remain deferred to the optional `--java-reference` gates.

### Phase 76 — KMIR tuple allocation decoding — complete; port incomplete

KMIR now retains source-shaped `typeInfoTupleType(fields, layout)` metadata.
An empty tuple materializes `Aggregate(variantIdx(0), .List)` only from a zero-byte allocation, including the source `noLayoutShape` representation.
Nonempty tuples require an explicit arbitrary-field layout and reuse the qualified offset-based decoder, so physical field order and padding remain independent of declaration order.
Explicit-layout tuples also report their layout size through the recursive element-size boundary, allowing later aggregate decoders to contain tuples without a packed-layout assumption.

Two new K-Rust executions qualify zero-byte empty-tuple materialization followed by a whole-local copy and a padded, reordered tuple followed by field projection.
The native corpus passes 146 executions with behavior SHA-256 `50870e129b67dc27724aa8c7e7c7814c26d93e57b631a68896b7482d030bb190`.
The definition contains 162 equations, 165 machine rules, and one claim across 914 descriptors, and its direct K-Rust KORE SHA-256 is `de8c19c8ddabca7034c112e08f8766594a734979dc866fa6da248f583e209d2d`.
The independently expanded source also passes collection at all 914 descriptors.
The complete default KMIR gate passes at descriptor protocol 34.

This tranche changes no shared KRS source, descriptor schema, or Definition IR schema.
After refreshing only the shared coverage-ledger hash, the KEVM and KWasm preflights pass without regenerating or executing their semantic artifacts.
No K-Rust bug or missing feature was encountered, and `K_RUST_UPSTREAM.toml` requires no Phase 76 entry.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 77 — KMIR fieldless enum allocation decoding — complete; port incomplete

KMIR now retains source-shaped fieldless enum `TypeInfo`, per-variant `Tyss`, and discriminant-list surfaces.
The decoder proves that every variant field list is empty, reads the allocation bytes as one unsigned little-endian tag, and returns the index of the exact matching declared discriminant.
Nonconsecutive discriminants therefore preserve their declared variant indices, while an invalid tag remains undefined rather than selecting a fallback variant.

One new K-Rust execution decodes byte `0x09` against discriminants `5` and `9`, then qualifies the resulting `Aggregate(variantIdx(1), .List)` through whole-local copy and return.
The native corpus passes 147 executions with behavior SHA-256 `2b6f0a0d622b9954e556e2430e2aab6eb0b2b57db195adabc6398449fcc4eaea`.
The definition contains 169 equations, 165 machine rules, and one claim across 942 descriptors, and its direct K-Rust KORE SHA-256 is `2bda60eb10843794083c44ca812a93fcc38e0008d108c34d768213c2754d0c26`.
The independently expanded source passes collection at all 942 descriptors, and the complete default KMIR gate passes at descriptor protocol 34.

This tranche changes no shared KRS source, descriptor schema, or Definition IR schema.
After refreshing only the shared coverage-ledger hash, the KEVM and KWasm preflights pass without regenerating or executing their semantic artifacts.
No K-Rust bug or missing feature was encountered, and `K_RUST_UPSTREAM.toml` requires no Phase 77 entry.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 78 — KMIR direct-tag enum field decoding — complete; port incomplete

KMIR now retains the source `variantsShapeMultiple`, initialized integer scalar, direct tag encoding, integer-length, wrapping-range, and per-variant `LayoutShapes` surfaces.
The allocation decoder reads only the declared tag-width prefix as an unsigned little-endian integer, selects the exact declared discriminant, indexes the corresponding field-type list and variant layout, and decodes the selected fields from arbitrary machine-size offsets in declaration order.
Invalid tags, insufficient tag bytes, absent variant entries, and non-arbitrary selected layouts remain undefined through the existing partial allocation-decoding boundary.

Five new K-Rust executions qualify every supported integer tag width from I8 through I128.
They include signed and unsigned tag metadata, nonconsecutive and high-byte discriminants, per-variant field offsets, a three-variant layout selecting index two, and an I128 discriminant whose significant byte is at the far end of the 16-byte tag prefix.
The native corpus passes 152 executions with behavior SHA-256 `b0423a06bbc25ec390eddc2a19ebe0a8850412beb14f6032a8d6892eadec6bb5`.
The definition contains 181 equations, 165 machine rules, and one claim across 1,005 descriptors, and its direct K-Rust KORE SHA-256 is `c3728278320e165e23053afdada9e9d4acfa8ee3b9f1392359d0e69b2dfb543e`.
The independently expanded source passes collection and emission at all 1,005 descriptors, and the complete default KMIR gate passes at descriptor protocol 34.

Descriptor collection rejected two initial source-authoring name collisions: the new integer-length constructors duplicated existing integer-type constructor identities, and both initialized-scalar layers initially shared one identity.
Distinct Rust constructor identities with unchanged authored KMIR syntax resolved both collisions before semantic qualification.
These were KRS authoring defects caught by the existing graph checker, not K-Rust backend defects.

This tranche changes no shared KRS source, descriptor schema, or Definition IR schema.
After refreshing only the shared coverage-ledger hash, the KEVM and KWasm preflights pass without regenerating or executing their semantic artifacts.
No K-Rust bug or missing feature was encountered, and `K_RUST_UPSTREAM.toml` requires no Phase 78 entry.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 79 — KMIR niche-pointer None allocation decoding — complete; port incomplete

KMIR now retains the source pointer primitive, address space, niche tag encoding, wrapping range, and two-variant Option field-list layout required by pinned `rt/decoding.md`.
Exactly all-zero allocation bytes decode to `Aggregate(variantIdx(0), .List)` for the selected niche-pointer Option representation.
Nonzero pointer and reference payloads remain undefined because pinned KMIR explicitly states that they require a different encoding and supports only `None` at this boundary.

One new K-Rust execution qualifies the pinned eight-byte all-zero `Option<&u8>` representation through allocated-constant evaluation, whole-local copy, and return.
The native corpus passes 153 executions with behavior SHA-256 `37d7a4d00221aed7edc84d0cba5d09751d66eea089b20047432962dd7c3180a6`.
The definition contains 182 equations, 165 machine rules, and one claim across 1,013 descriptors, and its direct K-Rust KORE SHA-256 is `f053acfd96b4316c05758f9dfbed0548a79344d45e1c4388d1b7309ec44f1639`.
The independently expanded source passes collection and emission at all 1,013 descriptors, and the complete default KMIR gate passes at descriptor protocol 34.

This tranche changes no shared KRS source, descriptor schema, or Definition IR schema.
After refreshing only the shared coverage-ledger hash, the KEVM and KWasm preflights pass without regenerating or executing their semantic artifacts.
No K-Rust bug or missing feature was encountered, and `K_RUST_UPSTREAM.toml` requires no Phase 79 entry.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 80 — KMIR zero-sized constant materialization — complete; port incomplete

KMIR ordinary operands now retain the source `operandConstant(constOperand(span, mirConst(constantKindZeroSized, Ty, MirConstId)))` boundary in addition to the existing zero-sized function call target.
The decoder resolves the operand type through the concrete type map and implements all four pinned `rt/data.md` materializations.
Structs, tuples, and function items become `Aggregate(variantIdx(0), .List)`, while fixed zero-length arrays become `Range(.List)`.
The new `typeInfoFunType` value metadata remains distinct from function-table identity used during call setup.

Four new K-Rust executions qualify zero-sized struct, tuple, fixed zero-length array, and function-item constants through assignment and return.
The native corpus passes 157 executions with behavior SHA-256 `ce8c8b07ee4e65e54226d2230d2ed8986c63fbe82697b04cc0d513eb547a30e4`.
The definition contains 186 equations, 166 machine rules, and one claim across 1,024 descriptors, and its direct K-Rust KORE SHA-256 is `c028d6bd519ba2bf23a404ed52b53a803779c84ce178d9764f720aa87e4da18d`.
The independently expanded source passes collection and emission at all 1,024 descriptors, and the complete default KMIR gate passes at descriptor protocol 34.

This tranche changes no shared KRS source, descriptor schema, or Definition IR schema.
After refreshing only the shared coverage-ledger hash, the KEVM and KWasm preflights pass without regenerating or executing their semantic artifacts.
No K-Rust bug or missing feature was encountered, and `K_RUST_UPSTREAM.toml` requires no Phase 80 entry.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 81 — KMIR ordinary aggregate construction — complete; port incomplete

KMIR now retains the source `Rvalue::Aggregate` boundary for the complete ordinary ADT, array, tuple, and closure group from pinned `rt/data.md`.
Source-shaped aggregate kinds retain ADT definitions, nonzero variant indices, generic arguments, optional user-type annotations and union-field markers, array element types, and closure definitions.
Only ADTs with `noFieldIdx` enter the ordinary materializer; union-field and raw-pointer aggregate semantics remain separate as required by the authority.

Operand evaluation is staged left to right through the existing `EvalOperand` and `Continue` machinery and accumulates exact values in a builtin `List`.
ADT construction preserves the selected variant, array construction produces `Range`, and tuple and closure construction produce variant-zero `Aggregate` values.
The new executions jointly qualify order, copy preservation, whole-local move invalidation, an allocated constant inside `.Operands`, empty and nonempty nonzero ADT variants, array materialization, tuple materialization, closure captures, all three generic-argument constructors, and optional user-type annotation syntax.

Five new K-Rust executions extend the native corpus to 162 executions with behavior SHA-256 `32baec67c3e4d43043c29436e1178d9ca12937d2a63d40776c652b1a59d52a95`.
The definition contains 190 equations, 170 machine rules, and one claim across 1,072 descriptors, and its direct K-Rust KORE SHA-256 is `325ca37f4a84b3117bb96728173f1da72f5d6fe6916245d636dfe5adcb284ec8`.
The independently expanded source passes collection and emission at all 1,072 descriptors, and the complete default KMIR gate passes at descriptor protocol 34.

This tranche changes no shared KRS source, descriptor schema, or Definition IR schema.
After refreshing only the shared coverage-ledger hash, the KEVM and KWasm preflights pass without regenerating or executing their semantic artifacts.
No K-Rust bug or missing feature was encountered, and `K_RUST_UPSTREAM.toml` requires no Phase 81 entry.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 82 — KMIR array Repeat and Len rvalues — complete; port incomplete

KMIR now implements the complete array-rvalue pair from pinned `rt/data.md`.
`Rvalue::Repeat` evaluates its element through the existing operand machinery, reads the allocation-backed `TyConst` length as little-endian bytes, and constructs the exact `Range` through K's standard `LIST.make` hook.
`Rvalue::Len` copies an arbitrary whole or projected place through the existing traversal machinery and returns the selected `Range` length as an unsigned 64-bit `Integer`, matching the authority's `usize` representation.

The shared closed List catalog now exposes the already published `LIST.make` operation in descriptor protocol 35 and Definition IR schema 27.
Readable K emits `makeList(length, value)`, and the native adapter targets the pinned frontend's synthesized `makeList(_,_)_LIST_List_Int_KItem` production.
The pinned K-Rust backend already implements the hook; focused registry, wire-shape, adapter, and prelude-label tests pass without changing the dedicated k-rust checkout.

Five new K-Rust executions extend the native corpus to 167 executions with behavior SHA-256 `ec797f9afa443c8f61f60ab379bff57081414ca8300d60024627135b275b16d8`.
The cases qualify allocated, copied, and moved repeated elements; zero, two, and three-element lengths; copy preservation; move invalidation; whole-local length; and projected nested-range length.
The definition contains 190 equations, 174 machine rules, and one claim across 1,084 descriptors, and its direct K-Rust KORE SHA-256 is `7b2733bfca5d448764b18ef6d01ae7e109db10ad02b010007c538db538f07c01`.
The independently expanded source passes collection and emission at all 1,084 descriptors, and the complete default KMIR gate passes at descriptor protocol 35.

The shared feature is qualified through the root Rust suite and all three semantic gates.
Final root qualification also reconciled stale protocol/schema expectations and closed-registry fixtures exposed by the protocol-35 cutover, and the active Rust 1.98 warnings-denied Clippy gate passes.
The resulting semantic artifact refresh changed only the metadata-bearing Definition IR, descriptor-bundle, semantic-IR, and source-ledger JSON identities; all three emitted `definition.k` files, symbol catalogs, and `.krs-artifacts` markers remained byte-identical.
No K-Rust bug or missing feature was encountered, and `K_RUST_UPSTREAM.toml` requires no Phase 82 entry.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 83 — KMIR CopyForDeref and whole-local Discriminant rvalues — complete; port incomplete

KMIR now implements the selected remaining place-rvalue pair from pinned `rt/data.md`.
`Rvalue::CopyForDeref` reuses the complete ordinary copy traversal over arbitrary selected projections and does not invalidate the source.
`Rvalue::Discriminant` copies a whole enum local, resolves its exact `TypeInfo` through the local type and `<types>` map, and recursively selects the declared discriminant at the aggregate variant index.
The result is the authority-shaped flexible-width unsigned `Integer(discriminant, 0, false)`, including nonconsecutive user discriminants.
Projected discriminant type derivation remains deferred until the complete upstream `getTyOf` boundary is selected.

Three new K-Rust executions extend the native corpus to 170 executions with behavior SHA-256 `a722a8940b3d858e1bdfb4229a62c2138d7d66784213e049a678d23bfe94cecb`.
The cases qualify projected `CopyForDeref` without source mutation and whole-local enum discriminants at the first and third variants, including the nonconsecutive user discriminant `9090`.
The definition contains 193 equations, 177 machine rules, and one claim across 1,097 descriptors, and its direct K-Rust KORE SHA-256 is `4f8e4e7ffb21db226d8f906006be7d02601516fee51bf741eaedeb1fad7ddcdf`.
The independently expanded source passes collection and emission at all 1,097 descriptors, and the complete default KMIR gate passes at descriptor protocol 35.

This tranche changes no shared KRS source, descriptor schema, or Definition IR schema.
After refreshing only KMIR sources and the shared coverage-ledger hash, the KEVM and KWasm preflights pass without regenerating or executing their semantic artifacts.
No K-Rust bug or missing feature was encountered, and `K_RUST_UPSTREAM.toml` requires no Phase 83 entry.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 84 — KMIR projected type derivation and typed rvalues — complete; port incomplete

KMIR now retains the pinned `getTyOf` boundary for typed projected places without a port-local adapter.
`Ty` is a source-shaped subsort of `MaybeTy`, `TyUnknown` represents an absent type lookup, and total `pointeeTy`, `elemTy`, `getTyOf`, and `#lookupMaybeTy` functions traverse dereference, field, dynamic-index, constant-index, subslice, and downcast projections.
Projected `Discriminant` derives the selected enum type before resolving the exact declared discriminant.
Projected copy and move operands now preserve type-directed `PtrToPtr` casts and same-representation `Transmute` operations across the same traversal boundary, including move invalidation.

Five new K-Rust executions extend the native corpus to 175 executions with behavior SHA-256 `5ed9a35931cb55aa536d3dacb5d56a80666a5ce7011a8bc05279aca6b86e2864`.
The cases qualify projected discriminants through downcast and field, dynamic index, reference dereference, subslice and constant index, plus projected pointer casts and transmutation with move invalidation.
The definition contains 209 equations, 177 machine rules, and one claim across 1,124 descriptors, and its direct K-Rust KORE SHA-256 is `0fba375bd27d84f706ee9699f5a6745281ab1061899d82c3dc0db47aae4d8bec`.
The independently expanded source passes collection and emission at all 1,124 descriptors, rust-analyzer reports zero diagnostics with all six definition and hover probes resolved, and the complete default KMIR gate passes at descriptor protocol 35.

This tranche changes no shared KRS source, descriptor schema, or Definition IR schema.
All three KMIR, KEVM, and KWasm pin-ledger preflights pass without regenerating or executing the unchanged KEVM and KWasm semantic artifacts.
No K-Rust bug or missing feature was encountered, and `K_RUST_UPSTREAM.toml` requires no Phase 84 entry.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 85 — KMIR nullary size, alignment, and UB-check operations — complete; port incomplete

KMIR now implements the selected nullary-operation group from pinned `rt/data.md` and `rt/types.md` without a wrapper adapter.
`nullOpUbChecks` returns the pinned disabled value `BoolVal(false)`.
`nullOpSizeOf` and `nullOpAlignOf` return 64-bit unsigned `usize` values for signed and unsigned integers, F16/F32/F64/F128, Boolean, character, string, enum, struct, union, tuple, fixed and dynamic array, thin and fat pointer, and reference types.
Aggregate sizes and alignments retain the source `LayoutShape`, while fixed-array size uses the allocation-backed little-endian `TyConst` length already selected by KMIR.
Explicit void size and alignment queries remain undefined at the rvalue boundary, matching the pinned operational rule guard, and `nullOpOffsetOf` remains deferred.

Four new K-Rust executions extend the native corpus to 179 executions with behavior SHA-256 `35481020b29393b7c13299d78ebdb15e05a9f5ca13be70d01afb0d4883031b85`.
The cases qualify disabled UB checks, primitive size and alignment, aggregate-layout size and alignment, and array plus pointer/reference size and alignment.
The definition contains 250 equations, 180 machine rules, and one claim across 1,210 descriptors, and its direct K-Rust KORE SHA-256 is `eb284f6bcaa10519c722ce3cf3ed7251b3f341c56d75f7e2b84c0867bbc162b8`.
The independently expanded source passes collection and emission at all 1,210 descriptors, rust-analyzer reports zero diagnostics with all six definition and hover probes resolved, and the complete default KMIR gate passes at descriptor protocol 35.

This tranche changes no shared KRS source, descriptor schema, or Definition IR schema.
All three KMIR, KEVM, and KWasm pin-ledger preflights pass without regenerating or executing the unchanged KEVM and KWasm semantic artifacts.
No K-Rust bug or missing feature was encountered, and `K_RUST_UPSTREAM.toml` requires no Phase 85 entry.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 86 — KMIR active-field union construction and projection — complete; port incomplete

Pinned KMIR declares `nullOpOffsetOf` syntax but provides no operational rule beyond a bare heading, so KRS does not invent that behavior.
The next authority-backed ordinary-rvalue tranche instead retains source-shaped union ADT construction through `aggregateKindAdt(..., someFieldIdx(fieldIdx(FIELD)))` with exactly one evaluated operand.
The result is `Union(fieldIdx(FIELD), VALUE)`, distinct from ordinary `Aggregate` values as in pinned `rt/data.md`.
Same-active-field projection retains the source `CtxFieldUnion` reconstruction context for reads, persistent writes, projected moves, and reference creation.
Pinned KMIR marks cross-field reinterpretation as a TODO and supplies no rule, so requests for a different union field remain deliberately undefined.

Three new K-Rust executions extend the native corpus to 182 executions with behavior SHA-256 `76d83db16083e694e5d52101254782cabaf5b3ade3cded5fe886821b8f86e588`.
The cases qualify union construction followed by a same-field read, same-field persistent write plus projected move invalidation, and a mutable-reference write through a frozen union-field projection.
The definition contains 254 equations, 181 machine rules, and one claim across 1,219 descriptors, and its direct K-Rust KORE SHA-256 is `de02901cd6721bc582134c5a1b9e4f346aac03d5b76745d5a739c9a6bca2044f`.
The independently expanded source passes collection and emission at all 1,219 descriptors, rust-analyzer reports zero diagnostics with all six definition and hover probes resolved, and the complete default KMIR gate passes at descriptor protocol 35.

This tranche changes no shared KRS source, descriptor schema, or Definition IR schema.
All three KMIR, KEVM, and KWasm pin-ledger preflights pass without regenerating or executing the unchanged KEVM and KWasm semantic artifacts.
No K-Rust bug or missing feature was encountered, and `K_RUST_UPSTREAM.toml` requires no Phase 86 entry.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 87 — KMIR raw-pointer aggregate construction — complete; port incomplete

KMIR now retains the pinned `aggregateKindRawPtr(TY, MUTABILITY)` ordinary-rvalue boundary with ordered operand evaluation.
A local pointer followed by an unsigned 64-bit length produces a fat pointer with `dynamicSize(LENGTH)` and removes only a trailing zero `ConstantIndex` through the source `removeIndexTail` function.
A local pointer followed by an empty aggregate unit produces a thin pointer with `noMetadataSize` and retains its complete place.
Both forms apply the aggregate's requested mutability while preserving frame height, pointer offset, and origin size.
Pinned KMIR leaves the length, origin-size, slice-type, and index-tail validity guards commented out, so KRS does not invent stronger guards at this boundary.

Two new K-Rust executions extend the native corpus to 184 executions with behavior SHA-256 `e4bae64f34415d319cf2ac153f2972a8788cfefee66a7ece17e2e84b28ad36f9`.
The cases qualify fat-pointer construction with trailing zero-index removal and thin-pointer construction with absent size metadata, requested mutability, preserved provenance, copy preservation, and move invalidation.
The definition contains 259 equations, 181 machine rules, and one claim across 1,228 descriptors, and its direct K-Rust KORE SHA-256 is `58b4971b8b0cb21aeddef634d3c814ca326568645df8dbd7acdf5da75dbc36bb`.
The independently expanded source passes collection and emission at all 1,228 descriptors, rust-analyzer reports zero diagnostics with all six definition and hover probes resolved, and the complete default KMIR gate passes at descriptor protocol 35.

This tranche changes no shared KRS source, descriptor schema, or Definition IR schema.
All three KMIR, KEVM, and KWasm pin-ledger preflights pass without regenerating or executing the unchanged KEVM and KWasm semantic artifacts.
No K-Rust bug or missing feature was encountered, and `K_RUST_UPSTREAM.toml` requires no Phase 87 entry.
No Java or Haskell backend was run; the final reference comparison and proof remain deferred to the optional `--java-reference` gate.

### Phase 88 — freeze and qualify the recovered native baseline — complete

Feature development is frozen at the Phase 87 boundary while the accumulated recovered work is committed.
This phase adds no semantic descriptor, equation, machine rule, execution case, proof, protocol revision, or Definition IR revision.

The complete locked Rust workspace suite passes with the externally pinned Z3 4.12.5 library path, including all 24 `krs-k-rust` adapter tests.
The active-toolchain all-target Clippy gate passes with warnings denied.
Rust formatting, changed TOML and JSON parsing, Python harness compilation, and `git diff --check` pass.

The complete default native semantic gates pass without Java or Haskell execution:

- KEVM: 1,100 descriptors and 240 K-Rust executions, with eight Java reference proofs deferred;
- KMIR: 1,228 descriptors and 184 K-Rust executions, with one Java reference proof deferred;
- KWasm: 60 descriptors and 32 K-Rust executions, with one Java reference proof deferred.

The KEVM rust-analyzer probe remained CPU-active beyond its former 180-second diagnostic deadline and then completed with zero diagnostics and all six definition/hover probes resolved when given the same 240-second diagnostic budget already used by KMIR.
The gate now retains that four-minute inner deadline while allowing the outer subprocess enough time for cache priming plus diagnostics.
Both changes remain fail-closed and are included in the KEVM source ledger.

`K_RUST_MORE_SEMANTICS_REQUESTS.toml` records the K-Rust work that may be forwarded upstream without making those requests part of the KRS commit boundary.
The KRS-local adapter, external-solver policy, persistent runners, and current workarounds remain explicitly local.

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
| Make KRS work on IMP | Complete M4.1–M4.8 gate at protocol 20 and IR schema 13, including exact source projection, 1,206/1,206 native KORE parity, behavior hash `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`, all proofs, and compatibility hash `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6` | complete |
| Complete the KRS KWasm port | `semantics/coverage.toml`, canonical `semantics/kwasm`, and the fail-closed KWasm gate | incomplete: 8 equations and 8 machine rules qualify the arithmetic baseline against an 884-rule source inventory; recursive instruction and value-stack boundaries and deferred semantic surfaces remain |
| Complete the KRS KEVM port | `semantics/coverage.toml`, canonical `semantics/kevm`, and the fail-closed KEVM gate | incomplete: 321 equations and 280 machine rules qualify the Bytes-backed Shanghai load/copy, storage, account-query, log, SHA3, PUSH0, EXTCODEHASH, empty/absent and nonempty-code STATICCALL return/rollback, and address-1 ECREC/address-2 SHA-256/address-3 RIPEMD-160/address-4 identity/address-5 MODEXP/address-6 ECADD/address-7 ECMUL/address-8 ECPAIRING precompiles against a 3,440-rule source inventory; full repeated-account snapshots, other calls, creation, remaining account lifecycle, transactions, schedules, cryptographic hooks outside the selected precompile surface, and symbolic surfaces remain |
| Complete the KRS KMIR port | `semantics/coverage.toml`, canonical `semantics/kmir`, and the fail-closed KMIR gate | incomplete: 259 equations and 181 machine rules qualify block execution, typed local-list state, source-shaped allocated Boolean and all signed/unsigned integer constants, recursive fixed-array and dynamic-slice allocation decoding, arbitrary-layout struct and tuple allocation decoding, zero-byte empty-tuple materialization, exact-discriminant fieldless enum allocation decoding and direct-tag enum field decoding across I8/I16/I32/I64/I128 tag widths with per-variant arbitrary-offset layouts, all-zero niche-pointer Option None decoding, zero-sized struct/tuple/array/function-item constant materialization, ordinary ADT/array/tuple/closure, active-field union, and thin/fat raw-pointer aggregate construction with ordered operands, allocation-backed repeated arrays, whole or projected range lengths, projected `CopyForDeref` without source invalidation, whole-local and projected exact enum discriminants, source-shaped typed-place derivation through dereference, field, dynamic-index, constant-index, subslice, and downcast projections, nullary UB-check, size, and alignment queries across retained primitive, aggregate-layout, array, pointer, and reference types, shared read/write/move/reference projection traversal, aggregate field, same-active union field, and downcast plus dynamic, constant-index, subslice, pointer-offset, metadata-truncated range behavior, recursive array-cast SingletonArray projection, transparent-wrapper Field/WrapStruct projection with persistent reconstruction, source-shaped thin and fat allocated-reference constants, allocation-backed scalar, projected, and dynamically truncated reads plus reborrowing, unsizing, pointer-metadata extraction, and same-representation Transmute identity across local references, raw pointers, and allocation references, type-directed local/stack/allocation reference creation, same-frame raw-pointer creation, dereferencing, identity comparison, dynamic metadata extraction, bounded offset arithmetic, static-to-dynamic pointer/reference unsizing, concrete raw-pointer/reference type lookup, same-pointee and projected `PtrToPtr` across every raw-pointer/reference outer-type combination, projected `Transmute` across copy and move operands, source-first nested slice/array-to-element pointer conversion, allocation-backed fixed-array lengths with slice/static-array metadata conversion, material/void-ZST pointer projection with inverse cancellation, and singleton transparent-wrapper pointer conversion, width-aware ordinary/checked/unchecked integer arithmetic, checked-arithmetic assertions, Drop/Unreachable control, shifts and unary operations, integer/Boolean comparisons and bitwise operations, ordered `SwitchInt`, regular constant-target function calls with nested frames and constant/copy/move arguments, and stack-aware cross-frame reference/pointer transfer, nested read/write/move, and return behavior across 1,228 descriptors and 184 K-Rust executions against a 787-rule source inventory; `nullOpOffsetOf`, cross-field union reinterpretation, allocation mutation and remaining memory operations, indirect calls, intrinsics, and other semantic surfaces remain |
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

## Frozen continuation policy

Do not grow the supported semantic or authoring feature set until the Phase 88 baseline is committed and the user explicitly resumes feature development.
Treat the incomplete KEVM, KMIR, and KWasm inventory entries above as backlog rather than immediate work.
Do not add adapters, bypasses, relaxed pins, disabled checks, or temporary dependency changes to make the frozen baseline appear green.

Preserve the locked Rust workspace suite, warnings-denied Clippy gate, and all three native semantic gates while preparing commits.
The Java/Haskell reference paths remain deferred final validation and are not routine commit prerequisites for the native baseline.
Forward general K-Rust defects through `K_RUST_MORE_SEMANTICS_REQUESTS.toml`; do not repoint KRS to an unqualified shared checkout.
Do not reopen recovery forensics unless genuinely new evidence or media appears.

## Audit hygiene

The recovery evidence and `krs.RECOVERY_PROVENANCE.md` remain unchanged. This
audit is the mutable, committed record of decisions and qualification results;
update it whenever a recovery phase, environmental prerequisite, or gate
changes materially.
