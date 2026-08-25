# K-in-K2 recovery audit

Updated: 2026-08-26 JST

## Decision

Use this directory as the development repository.
It contains the best-available 2026-08-26 reconstruction from `/home/sebastiengllmt/recovery/k-in-k2-continuation-handoff-20260826/working-tree-best-available/`.
The recovered original tree and the chronologically replayed external `k-in-k2-*` worktrees are combined here.

The new Git history is a recovery checkpoint.
It must not be represented as the lost original history.

## Recovery boundary

The handoff supplied 814 files, one of which was transfer-only `.DS_Store` metadata.
The restored working tree began with 813 handoff payload files plus this audit.
Subsequent session-log reconstruction added two byte-exact final files that were absent from the handoff.
The handoff's blanket `0777` transfer permissions were normalized to `0644` for ordinary files, `0755` for shebang-bearing scripts, and `0755` for directories; that permission normalization did not change file bytes.

Post-import verification found that the assembled handoff had allowed older all-worktree replay variants to supersede 34 files in the byte-pinned backend investigation.
Those 34 paths were restored from the verified 618-file tree.
All 473 paths in `investigations/backend-agnostic-goal-closure/` that are covered by the final-session identity ledger now match it byte-for-byte.
Four additional historical query/witness files supplied by the external-worktree union remain present outside that 473-path ledger.

The underlying 618-file archive is preserved at `/home/sebastiengllmt/recovery/k-in-k2-continuation-handoff-20260826/original-artifact/k-in-k2-recovered-20260824.tar.gz` with SHA-256 `1b87e7160540cb7c9a608ce35413512dae6389b50028d1b0937635bb5fd410a8`.
The external-worktree recovery accounting is preserved at `/home/sebastiengllmt/recovery/k-in-k2-continuation-handoff-20260826/recovery-evidence/k-in-k2-external-worktree-audit-20260825.md`.

## Exact-final session-log recovery

The original Codex logs supplied after the reconciled checkpoint are preserved at `/home/sebastiengllmt/recovery/.codex/`.
The user-provided final-prompt anchor identifies session `01a0207c-f25c-76f2-85fb-96dc34226f91` and its rollout at `/home/sebastiengllmt/recovery/.codex/sessions/2026/08/21/rollout-2026-08-21T03-44-14-01a0207c-f25c-76f2-85fb-96dc34226f91.jsonl`.

That rollout records the final R3-G-04 field values and SHA-256 at `2026-08-21T04:27:58.256Z`.
A later complete logged snapshot supplied the unchanged remainder of the JSON and three subsequent policy fields.
Restoring the earlier two source hashes and omitting those three later fields reproduces `evidence/r3-g-04-k-native-rule-applied-next-event/results.json` with SHA-256 `b41ce0b69762320d02b5b7f55d1c0a1002ae932c1fc0cb0a5fcd660fff5cb873`.

The Java investigation logs record the target Git blob as 112,157 bytes.
The complete handoff extraction at `/home/sebastiengllmt/recovery/k-in-k2-continuation-handoff-20260826/recovery-evidence/k-in-k2-best-effort-missing-final-files-20260826/R3-G-02-RuleAppliedTraceDriver.intermediate.java` contains 112,156 identical bytes and lacks only the terminal newline.
Restoring that newline reproduces `spine/trace-configuration-composition/src/java/org/kframework/kink/trace/RuleAppliedTraceDriver.java` with SHA-256 `a42da3bf892215d11e2e23181388998b7d6ace7a9ef806c2907221c17bb94c9b`.

No known byte-exact final gaps remain.
The best-effort handoff evidence remains preserved as provenance but is superseded by these hash-matching files.

## Local verification

The reconciled tree passes `bun test oracle/test p1/test p2/test p3/test` with 10 tests and no failures.
All recovered shell scripts pass `bash -n`.
The backend investigation's official Draft 2020-12 schema and fixture validation passes when run with `jsonschema` 4.26.0 in an ephemeral Python 3.13 Nix environment.
The complete backend verifier passes 334,131 zero-backend checks.

## Provenance path translation

`k-in-k2.RECOVERY_PROVENANCE.md` is retained unchanged from the original 618-file recovery packet.
Its `../evidence/` references now resolve conceptually to `/home/sebastiengllmt/git/workspaces/starstream-fv/recovery/evidence/`.
The later 814-file continuation handoff supersedes its earlier statement that three spine paths and two draft histories remained unresolved.
The session-log reconstruction closes the two exact-final gaps that remained after that handoff.
