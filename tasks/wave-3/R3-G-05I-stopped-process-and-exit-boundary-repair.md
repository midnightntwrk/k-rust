# R3-G-05I: stopped-process teardown and deterministic exit-boundary repair

Status: sixth resource-wrapper acceptance repair. The rejected R3-G-05H
implementation is clean commit `ff70636e0bac1aaae9f9e93b1f023dd61d926eae`
over activation `6c0c5dc6bc1c78b9101d1f46cf08dccb4bec2761`. No R3-G-05
compiler/backend output has been produced or used, so the substantive
full-oracle cycle count remains zero. The incomplete `cycle-1-r3-g-05c`
directory remains failed-launch provenance and is never reusable.

## Acceptance blockers

Do not run the command authorized by R3-G-05H.

1. `bound_process_alive` deliberately treats Linux stopped states `T`/`t` as
   non-operational for readiness and owner monitoring, but
   `signal_bound_process` reuses that predicate. Teardown therefore refuses to
   send TERM or KILL through the already generation-bound pidfd of a stopped
   raw member. A stopped session can survive the supervisor/watchdog failure
   path instead of being killed and proven empty.
2. Root's first full H replay failed in the adopted-zombie case. The test used
   timing rather than a true exit-boundary handshake; the descendant was reaped
   historically before leader exit, correctly omitted from the post-exit
   snapshot, and the run succeeded while the test demanded status 72. The
   worker's prior pass therefore does not provide stable evidence for both
   sides of the non-inferential boundary.

## Generation-current versus operational liveness

Separate these predicates explicitly:

- generation-current/signalable: the pidfd still denotes the exact validated
  PID/start-time/SID/process-group generation and the process is not gone or a
  zombie; stopped and traced-stopped states remain signalable;
- operationally alive: generation-current and not zombie/stopped, used only
  where forward progress is required, such as watchdog/owner/readiness
  handshakes.

`signal_bound_process` must validate generation-current identity and then send
TERM/KILL through the pidfd even for `T`/`t`. Session selection, RSS accounting,
and empty proof remain zombie-inclusive. Readiness must still reject a stopped
watchdog or stopped gate leader. Owner-stop fallback must treat the owner as
non-operational and kill every target member, including stopped members.

Add bounded zero-backend session tests with stopped leader and stopped
multi-process-group descendants. Exercise supervisor timeout, watchdog
pressure/owner failure, and hard-kill fallback. Prove TERM may leave a stopped
member pending but pidfd KILL removes every target generation, the exact session
is empty, and an unrelated stopped process is unchanged.

## Deterministic post-exit membership boundary

Replace fixed-delay exit tests with explicit synchronization:

- historical case: the leader must not exit until the supervisor has reaped
  the adopted child and `/proc/<child>` is confirmed absent; subsequent zero
  leader exit must succeed, retain the PID only in historical reaping evidence,
  and omit it from `exitTimeDescendantPids`;
- post-exit case: the descendant must remain alive until the session leader is
  definitively gone, or otherwise be held as an unreaped adopted zombie across
  that boundary. The generation-bound post-exit snapshot must contain it,
  classify status 72, then terminate/reap it and prove the session empty.

Run the launcher suite repeatedly under scheduler noise and require both cases
to remain stable. The implementation must continue to classify only the
post-exit snapshot; do not reintroduce poll/reap/poll inference merely to make a
test pass.

## Retained H contract

Retain the private one-use readiness/approval/release channels, watchdog-only
gate write end, target acknowledgement, public-record digest binding,
double-bracketed pidfd session selection, first-writer terminal publishers,
done-marker rollback on outer-session publication failure, zombie-inclusive
empty proof, exact final watchdog status, and all existing adversaries.

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
