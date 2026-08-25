# R3-G-05F: first-writer terminal markers and complete session reaping repair

Status: third resource-wrapper acceptance repair. The rejected R3-G-05E
implementation is clean commit `e0375b3b7159dce460434649414a4555db1120f3`
over activation `3fc61ff24bea53f519005da66a98a6f148c00c8a`.
No R3-G-05 compiler/backend output has been produced or used, so the
substantive full-oracle cycle count remains zero. The incomplete
`cycle-1-r3-g-05c` directory remains failed-launch provenance and is never
reusable.

## Acceptance blockers

Do not run the command authorized by R3-G-05E.

1. `secure_io.atomic_write(..., require_absent=True)` checks absence before
   writing its temporary file but then unconditionally replaces the target. A
   regular marker created in that interval is silently overwritten, violating
   the required fresh, first-writer-wins terminal boundary.
2. `resource_watchdog.session_members()` filters zombies. The subreaping
   supervisor calls it before `waitpid`, so an adopted zombie can be omitted
   from both reaping and the claimed empty-session proof.
3. The supervisor creates `records/watchdog.done` whenever it proves the
   target session empty, including timeout, signal, inner failure, launcher
   failure, and descendant-survival paths. Those failures therefore receive
   success-shaped watchdog-disarm provenance even though disarm is permitted
   only after successful inner completion and an empty-session proof.

## Atomic first-writer-wins markers

Make `require_absent=True` atomic at the directory-entry operation, not a pair
of checks around replacement. Use a descriptor-relative no-replace primitive
such as linking the exclusively created, fsynced temporary inode into the
absent destination and then unlinking the temporary name, or an equivalently
strong kernel primitive. The destination operation must fail with the target
unchanged if any entry appears concurrently. Continue to reject symlinks and
non-regular targets and to fsync the containing directory after the committed
entry and temporary-name cleanup.

Do not weaken normal replace-mode writes used for nonterminal progress records.
Add a deterministic zero-backend adversary that pauses after the initial target
check, creates a regular destination with attacker bytes, resumes the writer,
and proves the absent-only write fails without changing those bytes. Cover the
terminal marker API used by raw stage/success, manifest, outer session/success,
and watchdog done; retain the existing symlink and temporary-name adversaries.

## Zombie-inclusive empty-session proof

Separate process enumeration from live-process signalling. Empty-session
enumeration must include every `/proc` member whose SID matches the owned
session, including zombies. The subreaper must repeatedly attempt nonblocking
`waitpid` for adopted/session children, rescan, and declare empty only when no
matching live or zombie member remains. Signalling may skip zombies, but that
must never make the empty proof skip them. The resource watchdog and external
supervisor must share compatible zombie-inclusive session membership semantics.

Add a bounded zero-backend test in which the session leader leaves an orphaned
descendant that exits and becomes an adopted zombie under the external
subreaper. Prove the supervisor reaps it before recording
`targetSessionEmpty: true`, leaves no matching SID member, and does not affect
an unrelated process. Retain multi-process-group and TERM-ignoring teardown
coverage.

## Success-only watchdog disarm

Create `records/watchdog.done` only after all of these are true: raw inner
returned zero, the reason is `inner-success`, and zombie-inclusive enumeration
proved the target session empty. Only that path may wait for a normal watchdog
completion and record `watchdogDisarmedAfterEmpty: true`.

Every failure path must keep the watchdog armed through target-session
termination and empty proof, then terminate/reap the watchdog without creating
the done marker. Its outer-session record must remain unmistakably non-success:
nonzero inner status, failure reason, false disarm flag, absent done digest, and
non-success watchdog status/provenance. Add zero-backend assertions for inner
failure, timeout, signal or injected launcher failure, surviving descendants,
and watchdog crash. Cache, finalization, publication, and routine verification
must continue to accept only the successful disarm shape and reject every
failure shape.

## Audit and oracle hold

Bind this packet and its activation into semantic inputs and exact command
authorization. Retain the entire R3-G-05 zero-backend acceptance suite,
including launcher, hard-kill, terminal-boundary, cache/path/symlink, mutation,
refusal, syntax, configuration-copy, package, and diff checks. Do not run K,
Java, `javac`, `kompile`, `krun`, Bun, a compiler/backend, or raw oracle. Do not
edit K or Java semantic authority. Return one clean repair commit and a newly
bound guarded command using a fresh output. Root will complete-diff audit,
commission a fresh read-only audit, and recheck live resources before
reauthorizing the still-first substantive cycle.

## Ownership and stop rule

Ownership remains only `spine/rule-applied-allowlist/**`, owned R3-G-05
evidence, and the existing package entry. Do not edit this packet,
checkpoints/roadmaps, accepted artifacts, lockfiles, or external K. Stop rather
than weaken atomic absence, zombie-inclusive reaping, success-only disarm,
whole-session termination, two-phase terminal publication, or R3-G-05 scope.
