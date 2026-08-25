# R3-G-05L: nested-child descriptor path split repair

Status: authorized R3-G-05 split repair after the original three-cycle cap.
Clean K implementation `d1523d8911523a6aa6603fb266e8c25c5ca1c449`
over activation `4006fac28ec20f47f136593fd135da36ccee4ea7` passes the
complete bounded zero-backend suite. Its fresh substantive cycle 3 passed the
driver and parser self-test, produced provisional configuration compiler
artifacts, and then failed at `configuration-compile`, status 113. Preserve all
three prior outputs as immutable failed-run provenance. None may be reused,
finalized, published, or treated as accepted evidence.

This split permits at most two additional substantive full-oracle cycles. Only
total cycle 4 is activated by this packet. A total cycle 5 requires a separate
root decision after cycle 4 demonstrates one narrow repair need within this
split; it is not silently authorized. R3-G-06 remains dependency-blocked.

## Exact cycle-3 blocker

Cycle 3 used fresh `build/cycle-3-r3-g-05k`. Its exact terminal diagnostic was:

```text
Cannot run program "kore-exec" (in directory
"/proc/self/fd/4/configuration-k-kompiled/."): error=2, No such file or directory
```

`kore-exec` is installed and runnable. The immediate raw shell can resolve its
inherited output descriptor as `/proc/self/fd/4`, and `kompile` creates
provisional artifacts below it. The JVM subsequently launches `kore-exec`
with a working directory below that spelling. The nested child does not retain
or cannot resolve the JVM's descriptor 4 at its working-directory boundary, so
the descriptor-rooted path disappears even though the original supervised raw
shell still owns the output descriptor.

## Required two-path contract

Retain `/proc/self/fd/<output-fd>` as the immediate secure path for publication
and descriptor-relative Python operations. Do not broadly replace it.

For compiler/build directories or arguments that a nested Java/K subprocess
may resolve, derive a stable owner-qualified spelling:

```text
/proc/<live-outer-wrapper-pid>/fd/<output-fd>
```

The outer raw wrapper, outside both the session supervisor and the killable
compiler session, must open and verify a dedicated fixed-number descriptor for
the reserved output directory. It must stay synchronously alive, retain that
descriptor without closing or rebinding it, and defer its own completion until
the supervisor has proved the exact target session terminated and was reaped.
The supervisor launch must explicitly close this owner descriptor in its child
inheritance path, proving neither raw inner nor its descendants inherit it.

Pass the outer owner's PID, `/proc` start-time generation, fixed descriptor
number, output device, and output inode through the authenticated launch
boundary. The raw inner process must verify that exact owner generation before
using the spelling. The existing independent watchdog must separately pidfd-
bind both the session supervisor (launcher owner) and outer descriptor owner,
retain both bindings through complete target-session teardown, and kill the
generation-bound target session if either owner dies or changes generation.
A pidfd is used only for generation-safe liveness and signaling; this packet
does not claim that it makes a numeric `/proc/<pid>` lookup atomic or prevents
PID reuse.

The owner PID, generation, and descriptor number are not a new trust root:
before the raw command is released, immediately before each compiler/backend
boundary, and immediately after its synchronous return, prove the descriptor
owner is the same live start-time generation and the stable owner path and
immediate secure path resolve to the same directory device and inode. No
compiler result or output may be consumed after a failed post-check. Continue
to hold the original descriptor and all existing session, first-writer,
no-follow, no-replace, and exact-output checks. Owner generation mismatch,
descriptor closure/rebinding, path identity mismatch, watchdog loss, outer
owner death, or supervisor death must fail closed, reject all provisional
results, and terminate and reap the exact target session.

Use one tested owner-path constructor and identity-check routine at every
nested-child path boundary, including
the configuration definition output and any later compiler/backend directory
or argument that a descendant must resolve. Immediate secure publication and
descriptor-relative validation continue through the inherited immediate
descriptor. The outer owner cannot normally exit between pre-check and nested
resolution because it is blocked waiting for the supervisor, whose successful
return requires the target session to be empty. If it is killed or replaced,
the independent watchdog and mandatory post-check make the entire cycle fail
closed; no provisional result is accepted or published. Do not fall back to
the canonical output pathname or any attacker-replaceable spelling.

## Zero-backend acceptance adversaries

Add bounded tests, requiring no Java, K, compiler, backend, or raw oracle, that
prove all of the following:

1. an outer wrapper owner outside both a synthetic supervisor and child session
   holds an output directory descriptor while a watcher binds both owner
   generations;
2. a grandchild that does not inherit that descriptor can `chdir` through
   `/proc/<owner-pid>/fd/<fd>` and write into the descriptor-bound directory;
3. the equivalent `/proc/self/fd/<fd>` spelling fails in that grandchild after
   descriptor closure;
4. renaming or replacing the canonical output path cannot redirect the
   grandchild, which still writes into the original descriptor-bound directory;
5. the owner descriptor is absent in the synthetic supervisor, child, and
   grandchild descriptor tables even though the grandchild can resolve it
   through the live owner's proc path;
6. owner exit before the grandchild's `chdir` makes the owner-qualified path
   fail closed, rejects any replacement generation, and terminates/reaps the
   exact child session;
7. injected PID-generation replacement is rejected while the pidfd-bound
   watcher never signals the replacement;
8. closing and rebinding the same numeric owner FD is rejected by the repeated
   device/inode check before a descendant can use it;
9. stable and immediate secure spellings have equal device and inode before
   release and on both sides of each nested compiler boundary;
10. outer owner and supervisor signals/failures retain the descriptor owner
    until the exact child session is empty, or fail the run without accepting
    provisional output; and
11. no-follow/no-replace publication and first-writer preservation remain
   unchanged.

Static acceptance must bind the tested owner-path constructor and repeated
identity-check routine to the exact values passed to every production
compiler/backend boundary. It must reject any use of the owner-qualified path
for publication, journals, manifests, validation, snapshots, failure recovery,
or other immediate descriptor-relative operations. It must bind the explicit
non-inheritance of the outer owner FD, the outer wait lifetime, separate
supervisor/owner watchdog pidfds, both-sided command checks, exact cycle policy,
and all process/path adversaries. Tests must reap their exact process trees and
remain safe on a resource-constrained development workstation.

## Cycle history and exact authorization

The R3-G-05L activation is the distinct clean checkout commit produced by
applying this complete root-owned packet/correction set atop `d1523d8`; it is
not prior K activation `4006fac`. Record that exact pre-worker HEAD before any
implementation change. Bind this packet and that distinct activation everywhere
K is bound: semantic inputs,
accepted pins, exact command authorization material, ancestry and packet-hash
preflight, raw-success inputs, final evidence, and verification. The initial
split invocation requires total substantive cycle count exactly 4 and fresh
output `spine/rule-applied-allowlist/build/cycle-4-r3-g-05l`.

For a cycle-4 pass, final evidence must retain the complete ledger:

- cycle 1: failed at `frontend-setup`, status 1, driver scope failure;
- cycle 2: failed at `frontend-setup`, status 1, no-op parser adversary;
- cycle 3: failed at `configuration-compile`, status 113, nested
  `/proc/self/fd` child working-directory failure; and
- cycle 4: pass with final evidence.

If cycle 4 instead exposes one narrow defect inside this packet and root writes
a separate cycle-5 repair/activation, cycle-5 final evidence must retain cycles
1 through 3 above, record cycle 4 as the exact narrow failed stage/status and
no final evidence, and record cycle 5 as pass. This packet itself authorizes
only the cycle-4 form and must reject cycle count 5.

The cycle-4 command must keep the existing raw controls: clean exact HEAD and
semantic digest authorization, a free `/tmp/k-in-k2-backend.lock`, serial
execution under `nice` and two-CPU affinity, default Java heap 1536 MiB and
hard maximum 2048 MiB, bounded timeout, fresh output only, and a watchdog
polling no slower than once per second. The watchdog must kill the exact
session above 6 GiB RSS, below 4 GiB available memory, or below 1 GiB free
swap, then terminate and reap that session completely. Root must confirm no
unrelated heavy K or Lean work immediately before launch.

Retain the entire bounded zero-backend suite. The implementation worker may
run those tests plus syntax/static checks, but must not run Bun, Java, `javac`,
K, `kompile`, `krun`, `kore-exec`, any compiler/backend command, or the raw
oracle. Return one clean repair commit and the newly bound guarded cycle-4
command. Root alone reviews, commissions fresh read-only audits, recomputes
the semantic digest and authorization, performs the live resource gate, and
decides whether to launch cycle 4.

## Ownership and terminal rule

Worker write ownership is only `spine/rule-applied-allowlist/**` (excluding
ignored raw build outputs). R3-G-05 evidence outside that directory, the
package entry, this packet, checkpoints, roadmaps, the delivery-loop record,
decisions, accepted artifacts, lockfiles, and external K are read-only. Do not
change K semantics, driver/parser authority, or unrelated behavior.

Stop rather than broaden scope, weaken secure publication, reuse any prior
output, activate R3-G-06, or run total cycle 5 without a new root decision. If
cycle 4 fails for anything other than one narrow defect in this split's
live-owner path contract, preserve it and write a stop checkpoint. If cycle 4
demonstrates such a narrow defect, root may package the one remaining split
repair before deciding whether to authorize total cycle 5.
