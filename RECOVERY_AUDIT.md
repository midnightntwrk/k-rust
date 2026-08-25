# KRS recovery audit and continuation plan

Updated: 2026-08-25 JST

## Decision

Use this directory as the development repository and reconcile its signed,
verified recovery import forward into a green post-F7 baseline. Do not spend
more time trying to manufacture an exact checkout of `9d507b0`: the surviving
forensic routes have been exhausted. The implementation sources needed to
continue are present, but Phase 4 qualification proved that the imported tree
is missing the top-level M3D oracle package required by M4. Restore that package
with explicit reconstruction provenance before refreshing the M4 source
ledger.

The implementation seams are now reconstructed through the macro fixtures,
compiler, CLI, and native adapter, and qualification is green through C7/Q8.
Recovery has one bounded source-reconstruction package left: M3D's frozen
reference verifier, pins, fixtures, claims, and static corpus. Feature work
resumes only after that package and the full M4 oracle pass from a clean signed
commit. Then continue the interrupted readability program: finish the
normative `draft/readability/spec`, make its IMP specimen executable with
expansion and semantic parity, and qualify the same authoring layer on KWasm
before moving to larger K corpora.

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
  reconstruction.
- `d741692` — recovery audit advanced to the qualification sequence.

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

The current `tests/m4/pins.json` is an older 22-parse ledger. The displaced
`tests/m3c/m4/pins.json` is the best recovered post-C7 pre-F7 ledger: it has
267 source identities and the exact 23-parse evidence hash recorded above.

Qualification on 2026-08-25 confirmed that neither ledger is directly
runnable as imported. The current ledger correctly fails its corpus hash, and
the 267-entry ledger names M3D reference inputs that are absent from the tree.
Restore M3D before treating ledger refresh as an allowed operation.

After transfer artifacts are removed, use the 267-entry ledger as the
starting recovery oracle. Classify differences rather than copying all pinned
files over the current tree: some differences are intentional F7 additions,
some are later reconstructed work, and some are genuine historical outliers.
Refresh source pins only after the workspace is coherent and each changed
identity has a written reason. Behavioral evidence must still match the
post-C7 oracle; do not bless a new semantic hash merely because the tree now
builds.

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

Once the recovered post-F7 baseline is green, use the Tier 1 projects in this
order:

1. `wasm-semantics/` (KWasm, K 7.1.329) for the smallest readable
   real-language corpus and the first authoring/formatter portability check;
2. `mir-semantics/` (KMIR, K 7.1.337) for the freshest K conventions and
   larger multi-cell/rule-shape stress cases;
3. `evm-semantics/` (KEVM, K 7.1.337) for scale and production-semantic
   complexity;
4. `kontrol/` (K 7.1.337) for prover-as-a-product, Pyk orchestration, and CLI
   workflow design rather than KRS core reconstruction.

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

### Phase 4 — establish the new green recovery baseline — active

Qualification completed on 2026-08-25:

1. The full locked default-toolchain workspace test suite passes with all
   targets and no fail-fast masking.
2. Strict rustdoc and all workspace doc tests pass. Ambient Rust 1.98 workspace
   Clippy exposes four post-recovery style-lint categories in historical test
   code: `too_many_lines`, `disallowed_names`, `struct_excessive_bools`, and
   `items_after_test_module`. With only those classified categories exempted,
   every other warning remains denied and Clippy passes. Do not rewrite
   recovered logic merely to erase this tool-version distinction.
3. Rust 1.88 all-target workspace checking passes. Its rustfmt and Clippy
   components remain deliberately unavailable as recorded above.
4. The complete syntax suite passes on Rust 1.98 and Rust 1.88, including all
   seven F7 trivia/source-API tests.
5. `tests/c7/verify.py` passes under K 7.1.337 with the recorded Z3 4.12.5
   library environment: bare `!!true` parses, explicit same-tier `non_assoc`
   nesting is rejected, and emitted K contains the required associativity
   sentence.

M4 preflight then stopped before semantic execution. The current
`tests/m4/pins.json` is the known older 22-parse/36-source ledger and its corpus
hash differs from the recovered 23-parse `corpus.json`. Attempting the
mechanical source-ledger projection against the current tree fails because the
M3D reference source is absent. This is correct fail-closed behavior.

### Remaining Phase 4 source package — M3D oracle reconstruction

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

Proceed in this order:

1. Reconstruct the eight-file M3D package from the retained M3D authored
   slices, M4 reference-policy code, upstream pinned IMP sources, diagnostic
   contracts, and proof ledgers. Claim byte identity only for a file that
   matches its surviving SHA-256 or Git blob identity; otherwise label it a
   functional reconstruction.
2. Run the reconstructed standalone M3D source, execution, diagnostic, and
   proof gate under K 7.1.337. Preserve the old semantic pins where their
   complete values survive; do not infer proof success from exit status.
3. Promote the 267-entry post-C7 ledger as the M4 behavioral starting point,
   then mechanically refresh only source identities whose path-by-path reason
   is recorded. The root source-ledger path policy is newer than the 267-entry
   ledger, so path-set changes must be classified as well as hash changes.
4. Run the complete M4.1-M4.8 oracle inside the pinned K/Z3 environment.
5. If and only if all semantic evidence matches, commit the source-ledger
   reconciliation separately and repeat M4 from a clean tree.

The semantic target is the recorded 23/31/246/16 result, 21 bounded proofs,
seven compatibility probes, and evidence hash
`21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`.
Any semantic difference is a reconstruction defect until separately
explained; it is not a pin-refresh opportunity.

Commit coherent repairs separately, then mark the final fully green commit as
the reconstructed post-F7 baseline. This commit receives a new identity and
must not claim to be `9d507b0`.

### Phase 5 — finish the readability specification and qualify IMP

Only after Phase 4:

1. Treat `draft/readability/spec/imp.rs` as the normative surface,
   `decisions.md` as the implementation contract, and `open-questions.md` as
   an explicit decision boundary. Do not silently settle its genuinely open
   items.
2. Complete the specimen build list in the order already recorded by the spec:
   `sorts!`, grammar surface, wrapper-free configuration, `rules!`, map facade,
   formatter, then diagnostics. Preserve the four F3 method gates throughout.
3. Integrate the F7 trivia/source APIs into real collector re-parsing, enforce
   line-comments-only DSL bodies there, and prove semantic payloads, stable
   identities, provenance-key topology, and byte-exact anchors are unchanged.
4. Build formatter rendering and snapshots, bring the one remaining
   trailing-comment-column choice to the user with concrete snapshots, and
   then add `krs fmt`.
5. Make the normative IMP specimen compile; require deterministic `krs
   expand`, resolved-IR and emitted-K parity with the current hand-written M4
   port, and the full IMP behavior/search/proof qualification.

Exit criterion: the normative authoring specimen, its expansion, and the
complete IMP oracle are green from a clean signed commit.

### Phase 6 — extend the qualified authoring layer to WASM and larger corpora

1. Use KWasm first for the requested WASM qualification and the smallest
   real-language portability check.
2. Move next to KMIR for current-K multi-cell and rule-shape stress, then KEVM
   for scale.
3. Use Kontrol only when shaping product-facing proving and CLI workflows.

Each corpus is an acceptance oracle, not a source of silent KRS syntax changes;
record any new construct as a spec decision before implementing it.

The normative formatter target remains:

- `draft/readability/spec/imp.rs` first;
- `draft/readability/spec/decisions.md` second;
- `draft/readability/spec/open-questions.md` for genuinely unresolved items.

`draft/readability/result/` is historical design evolution, not the
implementation authority.

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

Proceed in this order, stopping on the first unexplained semantic failure:

1. Reconstruct and qualify the missing eight-file top-level M3D oracle package;
   keep exact and functional reconstructions explicitly distinct.
2. Promote and classify the recovered 267-entry post-C7 M4 ledger without
   changing behavioral pins.
3. Run the complete M4 oracle with the recorded K/Z3 environment, reconcile
   only justified source identities, and repeat from a clean tree.
4. Sign the resulting green commit as the reconstructed post-F7 baseline.
5. Begin Phase 5 at the normative readability spec, qualify the new surface on
   IMP, then execute the KWasm-first Phase 6 ladder.

## Audit hygiene

The recovery evidence and `krs.RECOVERY_PROVENANCE.md` remain unchanged. This
audit is the mutable, committed record of decisions and qualification results;
update it whenever a recovery phase, environmental prerequisite, or gate
changes materially.
