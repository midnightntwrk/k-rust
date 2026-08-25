# R3-G-05D: waiting launcher and raw-failure provenance repair

Status: resource-wrapper acceptance repair after the first authorized launch.
The clean static implementation is
`4b47cac6d08f52ae6f1cfde4b44f5071bdecb086`. The exact authorized
outer command returned success immediately because `setsid` forked without
waiting; the detached inner session then terminated before compilation. The
ignored output contains only before-snapshots and a completed, non-firing
watchdog record with a 7300 KiB peak. It contains no K/Java/compiler/backend
log or artifact and will not be used to change semantic implementation or
evidence, so the substantive full-oracle cycle count remains zero.

## Required repair

Make the raw launcher synchronously and fail-closedly represent the dedicated
session it creates.

- The outer `raw` action must wait for the `setsid` child even when `setsid`
  must fork because its caller is already a process-group leader.
- It must return the exact inner-session exit status. Outer success is allowed
  only after the inner session completes successfully and the raw integrity
  manifest exists.
- Keep the dedicated session/process group, foreground bounded timeout,
  nonblocking lock, lowered priority, two-CPU limit, Java caps, and whole-session
  watchdog unchanged.
- Preserve stdout/stderr ownership for the lifetime of the inner session; the
  launcher must not detach into closed execution pipes.
- Record a durable task-build-only failure status containing the current named
  stage and exit status when raw inner execution fails. Do not record secrets,
  absolute user-specific evidence, or claim-bearing success fields.
- On success, remove or supersede the failure marker before manifest creation.
  Cache creation/publication must reject any failure marker or absent terminal
  raw-success record.
- Add a zero-backend self-test that invokes a synthetic dedicated-session child
  which exits nonzero after writing output, and proves the outer launcher waits,
  preserves the output, and propagates the nonzero status. Also test the success
  counterpart. The self-test must not invoke K, Java, a compiler, or a backend.

Bind the repair activation and this packet in semantic inputs and the exact
authorization material. A future raw attempt must use a fresh canonical output
path; never reuse, bless, finalize, or publish the incomplete prior directory.

## Audit and oracle hold

Retain and rerun all accepted R3-G-05 static, mutation, cache/path, watchdog,
refusal/publication, syntax, configuration-copy, package, and diff checks.
Do not run K, Java, `javac`, `kompile`, `krun`, Bun, a compiler/backend, or a
raw oracle. Return a clean repair commit and newly bound exact guarded command.
Root will perform a complete diff audit, a fresh read-only audit, and live
resource/process checks before reauthorizing the still-first substantive cycle.

## Ownership and stop rule

Ownership remains only:

- `spine/rule-applied-allowlist/**`;
- `evidence/r3-g-05-atomic-rule-applied-allowlist/**`; and
- the existing `r3:g:rule-applied-allowlist` package entry.

Do not edit this packet, K/Java semantic authority, accepted artifacts,
checkpoints/roadmaps, lockfiles, or external K. Stop rather than weaken exit
propagation, treat detached launch as success, reuse the incomplete output, or
broaden beyond the R3-G-05 resource wrapper.
