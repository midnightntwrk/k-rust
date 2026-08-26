# KRS k-rust handoff

Status: KRS dependency boundary established and qualified, 2026-08-27 JST

## Decision

KRS uses k-rust `0.4.0` from the dedicated worktree at `../inspirations/midnightntwrk/k-rust-krs`.
That worktree is detached at upstream commit `3cce7a47941c4dc0664e6e870d4e0529d74753c6`.
KRS must not depend on the shared `../inspirations/midnightntwrk/k-rust` main worktree.

The dedicated worktree carries one intentional local change in its root `Cargo.toml`:

```toml
z3 = "0.20.2"
```

Upstream currently enables `features = ["gh-release"]` at that location.
KRS disables that acquisition feature because its compatibility unit pins the externally supplied Z3 `4.12.5` library through Nix.
The `gh-release` path would otherwise select a different solver release at build time without a KRS-controlled artifact hash.

The shared k-rust main checkout may therefore be restored to upstream-clean state.
Its manifest and lockfile are no longer KRS inputs.
Do not apply KRS-specific Z3 policy changes to the shared checkout.

## KRS integration

The active dependency paths are owned by:

- `crates/krs-k-rust/Cargo.toml`;
- `tests/m4/native/Cargo.toml`;
- `tests/m4/oracle/artifact-probe/Cargo.toml`;
- `tests/m4/verify.py` and `tests/m4/pins.json`.

The adapter preserves its historical public `Backend::Haskell` name as a compatibility spelling and maps it to k-rust 0.4's `CompilationBackend::Rust` symbolic backend.
KRS claims carry explicit modalities, so the adapter sets `default_claims_to_all_path = false` rather than changing unqualified claim semantics implicitly.

`Krs.lock` pins all native inputs required by the new frontend-plus-backend graph:

```toml
[k_rust]
version = "0.4.0"
commit = "3cce7a47941c4dc0664e6e870d4e0529d74753c6"
tracked_crate_sha256 = "90585786b420471f1876f6a6d22fb9c13bab89e0420b579c94d690f1834b5535"
backend_version = "0.3.0"
tracked_backend_sha256 = "539816715fdca02419b9d8632075c0e324e900706ca2cd7f321e9c04ba505fef"
kore_version = "0.3.0"
tracked_kore_sha256 = "64e8e0088d13f76b266cff9237378fba100347a13c30e700cd85bf38130b7be7"
```

## Qualification evidence

The k-rust 0.4 migration passes all 17 `krs-k-rust` adapter tests.
The complete IMP M4.1-M4.8 gate passes at descriptor protocol 20 and Definition IR schema 13.
Native frontend parity remains 1,206/1,206 KORE sentences.
The behavior evidence remains `21e6ede2057cee3cdfc28d6893ddc64399a5ab333608addd5e217d72b9ea9f5c`.
All 21 proof specifications and 20 unique native claims pass.
The compatibility evidence remains `13ddab23139f1c64cc4bebf2402b4aa16c96c142f15310b9451113a7d4cc7fa6`.

The dependency-path isolation was subsequently qualified by rerunning the complete M4.1-M4.8 gate from `k-rust-krs` with the same results.
The final KEVM, KWasm, and KMIR gates also pass against the isolated setup.
These semantic preservation gates remain the authority for any later source change.

## Upstream follow-up policy

No k-rust functional bug was found during this migration.
The upstream design opportunity is to make Z3 acquisition selectable without editing the workspace dependency declaration:

- ordinary CLI builds may default to `gh-release` for installation convenience;
- reproducible consumers such as KRS must be able to select an externally pinned solver;
- reproducible downloadable-solver builds should use an exact checksummed artifact or exact source-built Z3.

Any future k-rust missing feature or defect found by KRS should be recorded with the exact revision, a minimal reproducer, expected and observed behavior, affected gate, and workaround status before it is passed upstream.
