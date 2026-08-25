# R3-G-05H: private watchdog gate and generation-safe session selection repair

Status: fifth resource-wrapper acceptance repair. The rejected R3-G-05G
implementation is clean commit `4de43b2aca44c213c2720d30adb7f1942234892a`
over activation `de8e5a89b6e0bfc51b4fc5f15581368760f8d630`.
No R3-G-05 compiler/backend output has been produced or used, so the
substantive full-oracle cycle count remains zero. The incomplete
`cycle-1-r3-g-05c` directory remains failed-launch provenance and is never
reusable.

## Acceptance blockers

Do not run the command authorized by R3-G-05G.

1. Public readiness JSON is forgeable. A stopped production watchdog plus an
   attacker-written exact record caused the supervisor to release and execute
   the payload before the watchdog ever published readiness.
2. Readiness validation and gate release are separate supervisor actions. A
   watchdog killed in that interval still allowed the payload to run with
   `rawCommandReleased: true` and watchdog status `-9`.
3. Successful watchdog disposal creates `watchdog.done` before the fallible
   absent-only `outer-session.json` commit. A preexisting outer-session first
   writer caused status 125 after the payload ran while leaving
   `watchdog.done`, a forbidden success-shaped residue.
4. Session generation checking is not atomic around `/proc` selection. A new
   SID leader with a different start time can appear after the single leader
   check, be enumerated, pidfd-bound using only its numeric SID, and signalled.
5. Reaping between two leader polls is treated as proof that the child existed
   at leader exit. A child proven `/proc`-absent before the leader exited was
   nevertheless recorded as an exit-time descendant and caused false status 72.

## Private watchdog-owned gate release

The public readiness record is durable evidence, not release authority. Add a
private inherited-descriptor protocol that an output-directory writer cannot
forge:

1. The gated target owns only the gate read end and cannot execute until it
   receives the release byte.
2. The watchdog validates and pidfd-binds target and owner generations,
   first-writer-publishes readiness, then sends the exact readiness digest and
   its generation over a private watchdog-to-supervisor descriptor.
3. The supervisor reads that private message, independently validates the
   record/digest and live generations, and sends a one-use approval over a
   separate private supervisor-to-watchdog descriptor.
4. Only the still-running, armed watchdog owns the gate write end. After it
   validates the approval, it writes the release byte and reports a private
   release acknowledgement. The target acknowledges receipt before `exec`.
5. The supervisor records release only after both acknowledgements match the
   bound readiness digest and exact generations.

Close every unused pipe end immediately in all three processes. Bound every
read/write with a short deadline and reject EOF, extra bytes, malformed frames,
digest mismatch, stopped/dead watchdog, or duplicate release. No supervisor
code path may write the gate release directly. Public readiness precreation,
watchdog stop/kill after readiness, private-channel EOF, and gate-ack failure
must all prove the payload never ran. Retain immediate-success stress and
watchdog-crash fallback after an authenticated release.

## Failed terminal-publication rollback

Treat successful watchdog disposal plus outer-session publication as one
fail-closed terminal transition. If outer-session first-writer publication
fails after `watchdog.done` was created, durably remove the done marker, discard
the success disposition, and force outer/raw failure. Never retain a legitimate
done marker without a legitimate bound outer-session record. Do not overwrite
an attacker first writer. Add the reproduced high-level adversary and prove:
payload status is nonzero, attacker bytes are unchanged, done is absent, active
journal/failure state blocks publication, and no success-shaped outer terminal
can be completed.

## Double-bracketed session-generation selection

Replace the check-then-enumerate PID list with a generation-bound selection
operation. Bracket `/proc` enumeration and pidfd binding with leader-generation
validation before and after. For every candidate, read its start time, open its
pidfd, and revalidate exact PID/start-time/SID/process-group fields before
returning the handle. If the numeric leader appears with a different start time
at either bracket, close all handles and treat the original generation as
complete/stale; never return or signal the replacement. Signal only through the
returned pidfds.

Use the same operation for signalling, RSS accounting, reaping/empty proof,
and watchdog fallback, with the completion latch preventing later rescans.
Add deterministic injected-reader tests where leader/SID and candidate PIDs
change before enumeration, during enumeration, during binding, and after the
final bracket. Prove all replacement and unrelated processes remain unchanged.

## Non-inferential exit-time descendant classification

Do not infer ordering from a child reaped between leader polls. Historical
reaping remains audit evidence only. Classify
`descendants-survived-inner-exit` exclusively from a generation-bound member
snapshot taken after the leader has been definitively observed exited; do not
retroactively add a prior reap merely because a later poll sees the leader
gone. A member in that post-exit snapshot remains failure-shaped and is then
reaped/terminated for the empty proof. A child proven gone before a delayed
leader exit must succeed and remain absent from `exitTimeDescendantPids`.

Add deterministic synchronization rather than fixed sleeps for both sides of
the boundary: descendant absent before leader exit, and descendant alive/zombie
in the post-exit snapshot. Retain exact reaping evidence and session emptiness.

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
than weaken private authenticated release, generation-safe signalling,
zombie-inclusive reaping, first-writer publication, success-only disarm,
whole-session termination, two-phase terminal publication, or R3-G-05 scope.
