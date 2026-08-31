# Rust upfront implementation package

Status: portable complete; native evidence gates deferred.

This package turns the frozen backend-neutral contracts into dependency-ordered Rust work that does not require complete KRS or k-rust evidence APIs.
The normative packet is [`work-package.toml`](work-package.toml).

The initial RU-05 audit and the completed RP-01 through RP-05 repair wave are recorded in [`completion-report.toml`](completion-report.toml).
The dependency-ordered [`repair-work-package.toml`](repair-work-package.toml) is complete: no portable failed clause remains, and the outstanding native evidence gates stay explicitly deferred.

The post-upstream reassessment is [`native-capability-reassessment.toml`](native-capability-reassessment.toml).
The active dependency-ordered implementation wave is [`native-readiness-work-package.toml`](native-readiness-work-package.toml), beginning with `handoffs/NR-00.toml`.
The first-wave acceptance repairs are specified by [`native-readiness-repair-work-package.toml`](native-readiness-repair-work-package.toml).
`handoffs/NR-01R.toml`, `handoffs/NR-02R.toml`, and the transaction-closure hardening in `handoffs/NR-R2.toml` passed the independent `NR-R3` gate recorded in `handoffs/NR-R3.toml`.
`NR-05R` completed its local adapter-index and pin-verification repair.
`NR-04A` completed the isolated-worker feasibility audit and proved that `NR-04` requires a delegated cgroup-v2 subtree plus a quota-backed writable-root authority that the current sandbox cannot supply, so `NR-04` is blocked without product implementation.
The positive-bounded `NR-06` observation/search adapter passed its repair, two-stage independent Sol review, and focused serialized validation; it grants no search-exhaustion, provenance, production-receipt, cache, or other upstream native authority.
`NR-07A` is implemented as a fixture-only bridge from the exact tracked KRS `definition_expr.json` Definition IR through a separately built KRS adapter process into the `NR-06` no-Z3 observed state/path adapter.
The gate selects `EXPR.expr.and-true`, independently checks its `And(true, B) => B` KORE semantics, instantiates `B` with `false`, and requires the resulting semantic binding in deterministic positive state/path observations.
Its disposable-clone gate excludes the live KRS checkout's unrelated untracked `docs-plan/` without weakening cleanliness, and it adds no KRS or `z3-inference` dependency to `kink-native`.
This narrow positive transport fixture does not qualify pattern search, discovery or tuples, mutation materialization, oracle decisions, receipts, publication, solver authority, provenance, exhaustive absence, or the remaining `NR-07` product boundary.
Its prior runtime fixture gate passed against exact clean KRS cff5e10 and dedicated k-rust 0de7983; that result remains historical fixture-level positive transport evidence with no provenance, exhaustion, or production authority.
The latest aligned-pin migration is `handoffs/NR-U5.toml`.
It selects clean KRS `be5f844` and dedicated/shared k-rust `c41caa8` as the current pins.
The k-rust delta adds accepted already-complete cell applications at `701ed1b`, workspace Rust 1.88 compatibility at `758a3a9`, semantic-downcast projection at `6ad2ea9`, and a deep simplification budget regression at `c41caa8`; KRS records passing adapter, M4, KEVM, KMIR, and KWasm requalification at the pair.
Those upstream results do not replace K-in-K2's gates.
The aligned-pin structural checks, current-pin `NR-07A` runtime gate, and `NR-07Q-T1` five-exercise component gate now pass at exact KRS be5f844 and k-rust c41caa8.
KRS `OriginMapping` remains unbridged, `ResultBound` has no frontier, no explicit `Exhausted` record exists, and the lowering, compiler/evaluator, sealed-issuer, and isolation holds are unchanged.
`NR-07Q-S` completed the setup-only closed selected-surface manifest at `crates/kink-native/tests/fixtures/nr_07q_selected_surface.toml` and its ordinary structural table-driven gate at `crates/kink-native/tests/nr_07q_selected_surface.rs`.
The manifest now pins the aligned candidate KRS be5f844, its unchanged descriptor protocol 35 and semantic/Definition IR schema 27, dedicated k-rust c41caa8, exact tracked evidence for every selected row, named gaps for unselected or missing cross-layer fixtures, and stage-specific structured stops.
Every qualification case remains disabled in the selected-surface inventory, the current-pin ordinary structural gate passes only structure and closed coverage, and `NR-07Q-S` accepts no qualification evidence, closes no `KRS-QUAL-001` clause, grants no provenance or production authority, and cannot unblock `NR-07I`.
`NR-07Q-T1` now implements the first executable selected-surface tranche in `verify-nr-07q-t1.sh`.
Its closed execution manifest replays every declared evidence test for the `application`, `literal`, and `reference` rows against ordinary clean clones at exact KRS be5f844 and dedicated k-rust c41caa8.
The five serialized exercises cover component evidence at `syntax_parse`, `semantic_ir`, `definition_ir`, and `native_adaptation`; they do not carry one artifact continuously across those stages.
The aligned-pin serialized one-job gate passes all five exercises, but these remain distinct component tests rather than one continuous artifact route; full `NR-07Q` remains open, and neither `KRS-QUAL-001` nor `NR-07I` is unblocked.
`NR-07Q-T2` passes a continuous current-pin expression route for `application`, `literal`, and `reference` through syntax parsing, descriptor collection, Semantic IR, Definition IR, OriginMapping, native adaptation, native preparation, frontend compilation, and KORE reparsing.
That positive route covers only 3 of 36 selected rows, runs no structured negative-failure row, retains `SidecarOnlyMissingBridge`, and grants no qualification or production authority.
`NR-07Q-T3` passes four exact current-pin component routes for `cell`, `list`, and `map`, including paired KRS compatibility and direct upstream complete-cell evidence plus paired KRS and upstream collection-projection evidence.
Those routes are distinct rather than continuous: no one KRS-authored cell or collection artifact crosses the full route, and KRS compatibility lowerings remain in place.
Full `NR-07Q` remains blocked on the remaining selected rows, structured failure cases, and continuous cell and collection routes; provenance-complete acceptance separately remains blocked on the KRS-to-k-rust bridge.
`NR-07I` then integrates positive-only K-owned discovery and separately qualified compiler/evaluator witnesses.
It may decode only K-produced mutation sites and joined tuples, may not construct a host Cartesian substitute, and keeps compiler/evaluator results behind sealed non-authoritative boundaries.
Final `NR-07` remains blocked production authority.
`NR-08A` is the interim local-readiness and residual-blocker audit; final `NR-08` follows both real `NR-04` isolation authority and final `NR-07` production authority.
The pinned adapter pre-consumer audit is `handoffs/NR-05A.toml`, and its accepted local repair evidence is `handoffs/NR-05R.toml`.
The original `NR-05` provenance boundary remains upstream-blocked: its KRS sidecar is non-authoritative until a qualified KRS-to-k-rust provenance bridge exists.

Agents must read the complete packet, the relevant sections of [`rust-stack-handoff.md`](../../../investigations/backend-agnostic-goal-closure/rust-stack-handoff.md), and directly applicable sections of [`contracts.md`](../../../investigations/backend-agnostic-goal-closure/contracts.md) before editing.
Each packet writes `handoffs/<packet-id>.toml` with the fields declared by `agent_protocol.handoff_fields`.

The implementation preserves three boundaries:

1. frozen vectors define portable semantics;
2. scripted or finite evidence is never native proof; and
3. missing upstream evidence returns a typed deferred, unknown, incomplete, or not-proven result.

The integrated gate is:

```sh
python3 investigations/backend-agnostic-goal-closure/verify.py
cargo fmt --all -- --check
cargo test --workspace --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
git diff --check
```

The active untracked `investigations/k-rust-target/k-rust-agent-requests.toml` is unrelated user work and must be preserved exactly.
For this package it is historical request input, not a current dispatch source: agents use the reconciled `investigations/k-rust-target/upstream-issues.toml` and `handoffs/NR-U5.toml` classifications so the retired `KRUST-UP-001` and `KRUST-UP-002` requests are not re-executed.

## Rust workspace and zero-backend conformance

The workspace contains the six product crates declared by `work-package.toml`.
The bootstrap conformance CLI resolves the frozen package from the repository that built it, independent of the process working directory.
An explicit repository root is accepted only as a resolution input for relocated checkouts and conformance adversaries.

Run the bootstrap importer from the repository root or any nested directory:

```sh
cargo run --locked -p kink-conformance -- list
cargo run --locked -p kink-conformance -- check
```

Run the RU-00 workspace gates with:

```sh
cargo fmt --all -- --check
cargo test --workspace --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
```

`check` validates the frozen canonicalization-vector envelope and imports its expected fields unchanged.
RU-01 owns restricted JSON semantic validation, canonical encoding, and digest evaluation against those expectations.
