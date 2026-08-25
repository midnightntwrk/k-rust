# R3-G-05E: whole-session teardown and secure terminal publication repair

Status: second resource-wrapper acceptance repair. The rejected waiting-launcher
implementation is clean commit `9da2ca65ede918f2d0c06f31afea126783da9c89`
over activation `c76b4fa2169b7f02de3856c8b67673be2756938f`.
No R3-G-05 compiler/backend output has been produced or used, so the substantive
full-oracle cycle count remains zero. The incomplete `cycle-1-r3-g-05c`
directory is preserved only as failed-launch provenance and is never reusable.

## Residual blockers

Do not run the proposed command from `9da2ca6`.

1. `timeout --foreground` does not time out descendants. Inner EXIT cleanup can
   then mark the watchdog done while a compiler/backend descendant survives.
2. The outer raw action removes its in-progress journal before final validation
   and has no durable two-phase terminal completion, leaving a publishable
   success-shaped window on validation failure or hard kill.
3. Output validation and later creation are separate, while predictable marker
   temporary files follow symlinks. A concurrent leaf or temp-file symlink can
   redirect writes outside the task build before later manifest rejection.
4. Watchdog-crash fallback signals only the original process group, although a
   raw session may contain multiple process groups.

## Secure output reservation and marker writes

Reserve the fresh raw output atomically before launching the session. Use a
descriptor-relative, no-follow implementation (or an equivalently strong
primitive) rooted at the already validated task build directory:

- reject lexical traversal and every symlink in ancestors;
- create the absent output leaf atomically and fail if it already exists;
- re-open and verify the created directory by descriptor/inode before use;
- pass only that reserved canonical directory to raw inner execution; and
- do not accept a check-then-later-create pathname sequence.

All stage, failure, outer-success, raw-success, and manifest temporary writes
must be exclusive/no-follow, use unpredictable task-directory temporary names,
fsync the file and directory, and atomically replace a verified non-symlink
target. Reject dangling symlinks and concurrent target swaps without opening or
truncating an outside file. Extend zero-backend adversaries to race/precreate
output leaves and marker temporaries and prove an outside sentinel is unchanged.

## Whole-session timeout and watchdog fallback

The waiting outer launcher must own the dedicated raw session identity. On
normal child exit, timeout, signal, watchdog failure, or launcher failure it
must enumerate and terminate every remaining PID in that session, across all
process groups, revalidate PID/session identity before signalling, wait for the
session to become empty, and fail if termination cannot be proven. Do not rely
on `timeout --foreground`, a single PGID, or waiting only for the direct child.

The watchdog must remain armed until the external waiting launcher has observed
successful raw-inner completion and verified the session is empty. Raw inner
must not create `watchdog.done` merely because its shell is exiting while other
session members may survive. The watchdog-crash fallback must use the same
whole-session enumeration/termination behavior as the watchdog proper.

Add a zero-backend process-tree test whose dedicated session contains multiple
process groups, including a TERM-ignoring descendant. Exercise bounded timeout
and watchdog/supervisor failure and prove all target-session PIDs die while an
unrelated process survives. Record and assert the propagated nonzero status.

## Two-phase outer terminal completion

Keep an in-progress outer journal through manifest validation. Publication and
finalization must require a separate terminal outer-success record binding the
validated integrity-manifest hash and exact inner status.

Use a fail-closed sequence with no publishable failure window:

1. inner success, raw-success, provisional evidence, and manifest exist while
   the outer journal still marks the invocation active;
2. the waiting outer launcher verifies child status, empty target session,
   watchdog completion, raw-success, and the manifest;
3. it atomically writes/fsyncs the terminal outer-success record binding that
   validation; and
4. it removes the active journal only after terminal outer success exists.

If killed before step 3, publication rejects missing outer success or the active
journal. If killed between steps 3 and 4, publication rejects the active
journal. After step 4, the already completed validation bound by outer success
is sufficient; no unrecorded validation remains. An outer EXIT/error path must
write durable failure provenance whenever completion has not crossed that
terminal boundary.

Cache create/finalize/publish/routine verification must reject missing or
malformed outer success, a failure marker, an active journal, a mismatched
manifest hash, or a nonempty target session. Add adversaries for every boundary,
including hard kills immediately before and after terminal record creation.

## Audit and oracle hold

Bind this packet and its activation into semantic inputs and the exact command
authorization. Retain all accepted mutation, cache/path, watchdog, refusal,
launcher, syntax, configuration-copy, package, and diff checks. Do not run K,
Java, `javac`, `kompile`, `krun`, Bun, a compiler/backend, or raw oracle. Return
a clean repair commit and a newly bound guarded command using a fresh output.
Root will complete-diff audit, commission a fresh read-only audit, and recheck
live resources before reauthorizing the still-first substantive cycle.

## Ownership and stop rule

Ownership remains only `spine/rule-applied-allowlist/**`, owned R3-G-05
evidence, and the existing package entry. Do not edit this packet, semantic
K/Java authority, accepted artifacts, checkpoints/roadmaps, lockfiles, or
external K. Stop rather than weaken no-follow reservation, whole-session
termination, two-phase terminal state, or R3-G-05 scope.
