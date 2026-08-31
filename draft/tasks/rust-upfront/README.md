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
`NR-04` and `NR-05R` are now ready; `NR-06` remains blocked on `NR-05R`, and no upstream native authority was granted.
The latest read-only upstream snapshot is `handoffs/NR-U2.toml`: clean KRS `cff5e10` qualifies complete nested cells against its dedicated k-rust pin, while shared k-rust `4fef6d7` changes parser performance without granting evidence authority.
The pinned adapter pre-consumer audit is `handoffs/NR-05A.toml`; its local `NR-05R` repairs must complete before the positive-bounded `NR-06` adapter begins.

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
