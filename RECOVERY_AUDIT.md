# KRS recovery audit and continuation plan

Updated: 2026-08-25 JST

## Decision

Use this directory as the development repository, preserve its verified
recovery state in an initial Git commit, and reconcile it forward into a green
post-F7 baseline. Do not spend more time trying to manufacture an exact
checkout of `9d507b0`: the surviving forensic routes have been exhausted, but
all authored source, documentation, configuration, and test paths needed to
continue are present.

Feature work resumes only after the reconstructed workspace passes the full
qualification sequence. The first feature package after that baseline is the
compiler-collector integration named in `LAST_KNOWN_PROMPT.md`.

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
| The stable macro expander was unavailable | An exact 6,300-line `fbccdc7` expander is present. The current 486-line file is only an old clean-prefix replay. |
| Sixty-seven clean-commit source paths might be absent | All 67 are materialized from other evidence. The only absent signed-commit paths are a debug archive and built executable. |
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
- A fresh check in this directory matched all 580 ledger entries by SHA-256.
  No ledger path is absent and no ledger path differs.
- `krs.RECOVERY_PROVENANCE.md` is deliberately outside that 580-file project
  ledger.
- `../recovery/evidence/krs-transfer-completeness-20260825.md` establishes that
  every authored source, documentation, configuration, and test path from the
  signed `9d507b0` tree is materialized.
- The only two signed-tree paths not transferred are `kore-exec.tar.gz` and
  `test`, both generated/debug build artifacts. They are not reconstruction
  inputs.

The extraction problem is checkpoint coherence, not missing authored files or
random corruption.

### Local extras

The current directory also contains files outside the authoritative ledger:

- nested `PaxHeader` files and directories;
- `.playwright-mcp/`;
- `agent-sandbox-test2/`;
- this audit, the last-known prompt, and the provenance note.

The first three groups are transfer/session artifacts and may be removed
before the first development commit because none is in the verified project
ledger. Their forensic counterparts remain in `../recovery/`. The three
recovery documents should be kept.

### Git state

This `.git` directory is an empty initialized repository:

- no commits or refs;
- no remotes;
- no loose or packed objects from the original repository;
- every current path is untracked.

Valid signed original commit objects survive in the evidence repository, but
their trees are incomplete and cannot serve as a checkout. Do not recreate
new commits under the old IDs, graft partial object stores into this
repository, or describe a new root commit as an original historical commit.

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

The current `crates/krs-macros/src/expand.rs` is the clearest bad checkpoint
choice:

- current: 486 lines, SHA-256
  `a8bc04a1118f989b7f11c1e7d2cd8ec29a5568a15dc1da1a0351d08070960801`;
- exact `fbccdc7` evidence:
  `../recovery/evidence/fbccdc7-exact-commit-files/crates/krs-macros/src/expand.rs`,
  6,300 lines, SHA-256
  `280318732b52cec0e240c4e3c96b39a879eb0930ca625bb071bc1f1a71877cbd`;
- expected post-C7 stable pin:
  `63ef847cd73d8d6fb236f0baeb441c86d1b199142daa7eb17b93359976d24e2a`.

The exact `fbccdc7` file defines all 28 functions called by the recovered final
`crates/krs-macros/src/lib.rs`; the current clean-prefix file is missing 27 of
them. Seven expander update events are recorded after the `fbccdc7` commit
time in
`../recovery/evidence/krs-transcript-replay/filechanges.tsv`. Their original
rollout payloads are not transferred as standalone patch files, but their
metadata and the final expected hash remain useful constraints.

Start macro reconstruction from the exact `fbccdc7` file. Prefer an exact
replay that reaches the final pin, but do not block functional recovery if the
untransferred patch payloads make that impossible. Any reimplementation must
be committed as a documented reconstruction and qualified by the macro,
workspace, C7, and M4 gates.

### Cargo dependency seam

The root `Cargo.lock` matches `Krs.lock`, but the recovered current
`crates/krs-k-rust/Cargo.toml` does not describe that locked graph. It uses a
Git dependency with default features disabled; the lock contains the earlier
path-style `k-rust` package with Z3 enabled.

The exact stable manifest is recoverable from command output in
`../recovery/evidence/krs-bash-events.jsonl`, event
`toolu_01E6c2pvU6U3vYsmM1TPW4Q3`. Extracting its complete section produces the
expected stable SHA-256
`dd61532f2c7426ad1fdab72414cfddcb14eb92e105d99ec8da035521a9405779`.
It uses:

```toml
k-rust = { version = "=0.3.0", path = "../../../inspirations/midnightntwrk/k-rust/crates/k-rust", default-features = false, features = ["z3-inference"] }
```

Restore that exact manifest before changing the lockfile. A successful
`cargo metadata --locked` should be treated as proof that the original lock
and manifest are coherent again; do not casually regenerate `Cargo.lock`.

### IR, compiler, and adapter

`crates/krs-ir/src/definition.rs` and `semantic.rs` are large compile-clean
transcript reconstructions with extensive direct-read corroboration. They are
not exact `9d507b0` blobs, but they preserve valuable later readable-language
work. Keep them as the forward model unless a stronger exact variant proves
both newer and coherent.

The prior disposable audit localized the remaining non-macro failures:

- `krs-ir`: old `m2_ir` and `m3_expression_ir` tests do not compile against
  the recovered later IR; other observed IR tests passed;
- `krs-compiler`: errors originate in `emit.rs` and `lowering.rs`, while the
  much larger `collect.rs`, `reference.rs`, and `semantic.rs` type-check;
- `krs-k-rust`: adapter code is written against a different Definition IR;
- `krs` and `krs-cli`: fail transitively.

Repair these seams forward in that order. A stable-ledger mismatch is a
classification signal, not authority to replace a later file wholesale.

### M4 ledgers

The current `tests/m4/pins.json` is an older 22-parse ledger. The displaced
`tests/m3c/m4/pins.json` is the best recovered post-C7 pre-F7 ledger: it has
267 source identities and the exact 23-parse evidence hash recorded above.

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
| `k-rust` checkout | Currently `3cce7a4`; required commit `58f33885b736148dae189623d1aac989ce9be475` exists locally and must be checked out. |
| Z3 | Correct, 4.12.5. |
| Ambient Rust | 1.98.0. |
| MSRV Rust | Required 1.88.0 toolchain is not installed yet. |
| K executables | Not ambient by design; enter `kup shell k.openssl --version v7.1.337`. |

The fresh machine did not yet have all Cargo registry entries cached, so no
new full build result is claimed by this update. The earlier disposable-build
results remain the current failure map until the dependency setup is complete.

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

### Phase 0 — establish a trustworthy development history

1. Keep `../recovery/` immutable.
2. Remove every `PaxHeader` path, `.playwright-mcp/`, and
   `agent-sandbox-test2/` from this development copy.
3. Verify all 580 project files against
   `../recovery/evidence/krs-extract-ready-identities.tsv` once more after
   cleanup.
4. Create a signed root commit that records the verified recovery import plus
   the three recovery documents. Clearly label it as a reconstructed import,
   not an original KRS commit. Tag it locally as the immutable comparison
   point.
5. In a follow-up housekeeping commit, extend `.gitignore` for
   transfer/session artifacts, AppleDouble files, Python caches, and build
   output. Keeping this separate preserves all 580 authoritative project bytes
   in the root import commit.

Exit criterion: a clean Git worktree, no Cargo-visible `PaxHeader` member, and
a root commit from which every repair is reviewable as an ordinary diff.

### Phase 1 — restore dependency and toolchain coherence

1. Check out the existing `k-rust` object
   `58f33885b736148dae189623d1aac989ce9be475` in the sibling inspiration
   repository.
2. Restore the exact stable `crates/krs-k-rust/Cargo.toml` described above.
3. Install/select Rust 1.88.0 alongside the ambient toolchain.
4. Enter the pinned K 7.1.337 shell and verify the executable, Pyk, backend,
   and Z3 versions expected by `Krs.lock`.
5. Run `cargo metadata --locked` without modifying `Cargo.lock`.

Exit criterion: the recovered lock resolves exactly, all pinned dependency
revisions are present, and both the default and MSRV toolchains are usable.

### Phase 2 — restore the macro implementation

1. Replace the 486-line clean-prefix expander with the exact `fbccdc7`
   expander as the reconstruction baseline.
2. Run `cargo check -p krs-macros` and the positive/negative macro fixtures.
3. Reconcile the seven known later transitions or reimplement their behavior
   against the final `lib.rs`, syntax APIs, final pin, and fixtures.
4. Run `cargo fmt --check`, Clippy with warnings denied, and all macro tests.

Exit criterion: the macro crate and fixtures are green. Reaching the final
stable expander hash is preferred exact recovery; a different hash requires a
documented functional-reconstruction commit.

### Phase 3 — reconcile the recovered late IR line

1. Make all `krs-ir` unit and integration targets compile and pass, updating
   old tests only where they demonstrably describe superseded IR shapes.
2. Align `krs-compiler/src/emit.rs` and `lowering.rs` with the retained
   Definition/Semantic IR while keeping `collect.rs`, `reference.rs`, and
   `semantic.rs` behavior stable.
3. Align `krs-k-rust` with the same Definition IR and the pinned native
   frontend.
4. Qualify `krs`, then `krs-cli`, without starting collector-trivia feature
   work.

Exit criterion: `cargo check --workspace --all-targets --locked` and the full
workspace test suite pass. No recovery-only compatibility shim remains
unexplained.

### Phase 4 — establish the new green recovery baseline

Run, in order:

1. formatting, workspace check, Clippy `-D warnings`, tests, docs, and doc
   tests on the default toolchain;
2. all required `cargo +1.88.0 check` gates;
3. the focused F7 syntax/trivia suite;
4. the isolated C7 pinned-K qualification;
5. the complete M4.1-M4.8 oracle inside the pinned K shell;
6. a second clean M4 run after any justified source-ledger refresh.

The semantic target is the recorded 23/31/246/16 result, 21 bounded proofs,
seven compatibility probes, and evidence hash
`21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`.
Any semantic difference is a reconstruction defect until separately
explained; it is not a pin-refresh opportunity.

Commit coherent repairs separately, then mark the final fully green commit as
the reconstructed post-F7 baseline. This commit receives a new identity and
must not claim to be `9d507b0`.

### Phase 5 — resume the interrupted project work

Only after Phase 4, implement the next package recorded by the final session:

1. switch byte-exact compiler-collector source re-parsing to the new
   trivia-aware syntax seams;
2. enforce line-comments-only DSL bodies during real collection;
3. prove descriptor semantics and provenance identities remain unchanged;
4. commit that package independently;
5. proceed to formatter rendering/snapshots, settle comment-column versus
   fixed-gutter placement from snapshot evidence, add `krs fmt`, and continue
   readable IMP parity;
6. after IMP is qualified, validate the authoring layer against KWasm, then
   KMIR, then KEVM-sized corpus slices; use Kontrol only when shaping the
   product-facing proving/CLI workflow.

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

Execute Phase 0, commit the verified import, and then restore the exact
`krs-k-rust` manifest and exact `fbccdc7` macro expander. Those two evidence
promotions should turn the present build from an undifferentiated broken
recovery into a much smaller, trustworthy IR/compiler reconciliation task.

## Audit hygiene

This update changed only `RECOVERY_AUDIT.md`. Project sources,
`krs.RECOVERY_PROVENANCE.md`, the recovery repository, dependency checkouts,
and Git history were not modified.
