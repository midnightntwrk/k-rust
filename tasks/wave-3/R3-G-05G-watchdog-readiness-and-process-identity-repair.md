# R3-G-05G: watchdog readiness and process-generation identity repair

Status: fourth resource-wrapper acceptance repair. The rejected R3-G-05F
implementation is clean commit `33af456fe6d1650848be70360467c10ed1a34916`
over activation `7bba98ba9ccb14c91c443f9a9f99c6c9154d8aa4`.
No R3-G-05 compiler/backend output has been produced or used, so the
substantive full-oracle cycle count remains zero. The incomplete
`cycle-1-r3-g-05c` directory remains failed-launch provenance and is never
reusable.

## Acceptance blockers

Do not run the command authorized by R3-G-05F.

1. The supervisor calls the watchdog armed immediately after `Popen`. A fast
   inner leader can exit before watchdog target validation, after which the
   supervisor can create `watchdog.done` and the watchdog rejects the vanished
   leader. An immediate `true` reproduction failed six of eight launches.
2. The supervisor can retain a stale `watchdog_status = None` when the watchdog
   exits during teardown, yielding a failure record without the required exact
   non-success status.
3. A child reaped earlier while the leader was still running remains in the
   launch-wide set and is later misclassified as a descendant that survived the
   leader's exit.
4. `/proc` validation and `os.kill(pid, ...)` are separated and bind only
   numeric PIDs/SIDs. PID reuse can redirect a signal, suppress owner-death
   fallback, or make a new unrelated session appear to be the completed target.
5. The first-writer adversary exercises the primitive with production-like
   basenames, but does not prove that every production terminal call site
   actually selects the absent-only operation.

## Validated-before-execution watchdog readiness

Do not permit the raw command to execute until the watchdog has validated and
durably acknowledged the exact target and owner generations. Launch the target
session through a minimal inherited-descriptor gate whose session-leader PID is
stable across `exec`. The gate waits without running the requested command.
Start the watchdog against that leader; require a descriptor-relative,
first-writer readiness record binding at least target PID/SID/start time,
launcher PID/start time, and watchdog PID/start time. Independently validate
the record and live identities, then release the gate exactly once. Missing,
malformed, mismatched, timed-out, or prematurely exited readiness is a launcher
failure: never release the raw command and never create `watchdog.done`.

Keep readiness bounded and include it in terminal/cache provenance. Add a
deterministic zero-backend immediate-success stress test with no artificial
sleep and enough repetitions to expose the reproduced race. Every iteration
must return zero with a validated readiness binding, exact successful disarm,
and an empty target session. Add readiness corruption, watchdog-exit-before-
ready, and gate-release failure adversaries proving the raw payload did not run.

## Exact watchdog status and disposition

Never serialize a cached poll result after a later poll/wait/kill decision.
Centralize watchdog disposition so each branch reaps the process and returns
its final exact status. Successful disarm requires readiness, zero inner status,
`inner-success`, zombie-inclusive empty proof, done creation, and final watchdog
status zero. Every failure requires an absent done marker, false disarm flag,
exact nonzero watchdog status, and an armed-failure disposition. Exercise the
natural watchdog-fired/pressure sequence, including watchdog exit while target
teardown is still completing, and reject `null` or zero failure status.

## Exit-time descendants versus historical reaping

Retain all adopted-child PIDs as audit evidence, but classify
`descendants-survived-inner-exit` only from members observed at or after the
leader's actual exit. A child adopted and reaped while the leader continues,
followed by a later zero-status exit with an empty session, must not cause a
false 72. Add both bounded cases: one orphan zombie present when the leader
exits and one orphan fully reaped before a deliberately delayed successful
leader exit. The first is failure-shaped; the second succeeds after normal
watchdog disarm. Both must record reaping evidence and leave no session member.

## PID and session generation binding

Extend process identity with Linux start time and use generation-safe signalling
(`pidfd_open` plus `pidfd_send_signal`, or an equivalently strong primitive).
Open/bind the generation before validation, verify its PID, SID, process group,
and start time, and signal only through that bound handle. Treat identity change
or disappearance as a completed/stale selection, never as authority to signal
the current numeric PID. Bind watchdog owner liveness to launcher start time,
not `ownerPid` alone.

Preserve the original target-session generation across leader exit. If the
numeric leader/SID is reused with a different start time after the owned session
became empty, do not count or signal that new session. Add deterministic
zero-backend injected-proc/identity adversaries for selection-to-signal PID
replacement, launcher PID replacement, and post-empty SID reuse. Prove the
replacement/unrelated processes are unchanged. Do not weaken the existing
multi-process-group, TERM-ignoring, zombie, timeout, hard-kill, or resource
watchdog tests.

## Production terminal call-site binding

Make first-writer semantics hard to omit: expose dedicated absent-only terminal
publication functions without a permissive default, and route initial journal,
raw success/failure, integrity manifest, outer session/success, watchdog ready,
and watchdog done through them. Keep ordinary progress replacement separate.
Add structural/static call-site checks plus deterministic high-level adversaries
that reach the production publishers (not only the low-level primitive), inject
a regular first writer at the commit boundary, and prove refusal with the
attacker bytes unchanged.

## Audit and oracle hold

Bind this packet and its activation into semantic inputs and exact command
authorization. Retain the entire R3-G-05 zero-backend acceptance suite. Do not
run K, Java, `javac`, `kompile`, `krun`, Bun, a compiler/backend, or raw oracle.
Do not edit K or Java semantic authority. Return one clean repair commit and a
newly bound guarded command using a fresh output. Root will complete-diff audit,
commission fresh read-only audits, and recheck live resources before
reauthorizing the still-first substantive cycle.

## Ownership and stop rule

Ownership remains only `spine/rule-applied-allowlist/**`, owned R3-G-05
evidence, and the existing package entry. Do not edit this packet,
checkpoints/roadmaps, accepted artifacts, lockfiles, or external K. Stop rather
than weaken readiness-before-execution, generation-safe signalling,
zombie-inclusive reaping, first-writer publication, success-only disarm,
whole-session termination, two-phase terminal publication, or R3-G-05 scope.
