# R3-G-05 resource stop checkpoint — 21 August 2026

Status: static implementation preserved; not accepted or integrated. This
checkpoint records why the delivery loop stopped before the sole full oracle.

## Preserved implementation

The isolated `agent/r3-g-05` branch contains static implementation checkpoint
`ad22549`. It owns only `spine/rule-applied-allowlist/**` and the one permitted
`package.json` entry. No R3-G-05 evidence is committed because the required
K/Java/full-backend oracle has not run.

The checkpoint includes the exact-two K contract, two safe-shape fixture rules,
an atomic one-traversal Java adapter, pair-wide idempotence and conflict checks,
negative/parser/runtime projector tests, cached evidence finalization, and a
task-local replay. Static shell and Python parsing, accepted pre-CF copy
normalization, the four-case zero-backend runtime adversary suite, fixture
literal scanning, and `git diff --check` passed. `bun run check` did not run in
the isolated worktree because that worktree has no installed `tsc`; no package
installation was attempted.

This commit is an implementation checkpoint, not a worker acceptance result.

## Resource incident and audit

No R3-G-05 raw command was authorized, proposed, or launched. The task build
directory and `/tmp/k-in-k2-backend.lock` do not exist, and no raw success,
compiler, or backend artifact was produced by the leaf.

Immediately before the interrupted session, an unrelated Lean process was
observed at approximately 13 GiB resident memory while all 10 GiB of swap was
occupied. That process later disappeared. The current account cannot retrieve
a kernel OOM record, so this observation is not a conclusive attribution.
After the session resumed, a VS Code K language-server JVM was also visible
with an 8 GiB configured maximum but approximately 169 MiB resident use; it
started after the earlier interruption and is not attributed to this leaf.

## Mandatory resume gate

Resume from `ad22549` without rebuilding accepted ancestors. Before any JVM,
the raw replay must:

- require explicit root authorization and a fresh task-local output path;
- acquire the nonblocking global K-in-K backend lock;
- refuse exhausted swap or less than 3 GiB available memory;
- reject inherited Java heap or processor-count flags;
- force a 1536 MiB heap and two active processors by default, with hard maxima
  of 2048 MiB and two processors;
- run every compiler/backend child serially under lowered priority and a
  two-CPU affinity; and
- leave report-only repairs to zero-backend cache finalization.

The root must additionally inspect live memory, swap, and unrelated K/Lean
processes immediately before authorization. A passing script preflight does not
override an unsafe live-process audit. If safe headroom is unavailable, keep
this checkpoint stopped rather than weakening the gate.

After one successful raw run, the remaining path is worker evidence
finalization and commit, root diff/raw-log audit, a fresh read-only Sol audit,
the routine zero-backend command, repository checks from a dependency-equipped
tree, and either R3-G-05 acceptance or a new stop checkpoint. R3-G-06 remains
inactive until then.
