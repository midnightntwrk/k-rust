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
The restored project payload therefore contains 813 handoff files plus this audit and the unchanged original recovery provenance note.
The handoff's blanket `0777` transfer permissions were normalized to `0644` for ordinary files, `0755` for shebang-bearing scripts, and `0755` for directories; file bytes were not changed.

The underlying 618-file archive is preserved at `/home/sebastiengllmt/recovery/k-in-k2-continuation-handoff-20260826/original-artifact/k-in-k2-recovered-20260824.tar.gz` with SHA-256 `1b87e7160540cb7c9a608ce35413512dae6389b50028d1b0937635bb5fd410a8`.
The external-worktree recovery accounting is preserved at `/home/sebastiengllmt/recovery/k-in-k2-continuation-handoff-20260826/recovery-evidence/k-in-k2-external-worktree-audit-20260825.md`.

## Known exact-final gaps

Recovery exhausted the available Git-object, session, journal, and full raw-source routes without finding byte-exact final copies of these two files:

1. `spine/trace-configuration-composition/src/java/org/kframework/kink/trace/RuleAppliedTraceDriver.java`, expected SHA-256 `a42da3bf892215d11e2e23181388998b7d6ace7a9ef806c2907221c17bb94c9b`.
2. `evidence/r3-g-04-k-native-rule-applied-next-event/results.json`, expected SHA-256 `b41ce0b69762320d02b5b7f55d1c0a1002ae932c1fc0cb0a5fcd660fff5cb873`.

Neither path is present in this checkpoint.
The intermediate Java source, near-final JSON, partial final stdout, and their checksums remain in `/home/sebastiengllmt/recovery/k-in-k2-continuation-handoff-20260826/recovery-evidence/k-in-k2-best-effort-missing-final-files-20260826/`.
They may be used for an explicit forward reconstruction, but must not be described as byte-exact recovered finals.

## Provenance path translation

`k-in-k2.RECOVERY_PROVENANCE.md` is retained unchanged from the original 618-file recovery packet.
Its `../evidence/` references now resolve conceptually to `/home/sebastiengllmt/git/workspaces/starstream-fv/recovery/evidence/`.
The later 814-file continuation handoff supersedes its earlier statement that three spine paths and two draft histories remained unresolved; the two exact-final gaps above are the current boundary.
