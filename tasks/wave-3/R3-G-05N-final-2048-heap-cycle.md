# R3-G-05N: final 2048 MiB split cycle

Status: explicit root authorization for the one remaining R3-G-05 split cycle.
Clean M implementation `017e5b68c60e92601f8d36df34a9db80a98050cd`
over activation `f5e07a4f47929ebbe76f9c5eb22f73ff39e65745` passes the
complete bounded zero-backend suite and two fresh audits. Total cycle 4 is a
preserved substantive failure; it is never reusable or finalizable. This packet
authorizes one fresh total cycle 5 at the already-established hard Java maximum
of exactly 2048 MiB. It does not authorize a sixth cycle.

This is a separate root decision required by L/M, not an inference from their
cycle-4 command. It stays within the user-authorized two-additional-cycle split
and within the existing 2048 MiB/two-processor ceiling. Two independent
read-only audits classify cycle 4 as a one-parameter heap-default boundary with
no competing observed blocker. The final attempt is proportionate but not
guaranteed to pass.

## Preserved cycle-4 evidence

Fresh `spine/rule-applied-allowlist/build/cycle-4-r3-g-05l` at exact clean head
`017e5b68c60e92601f8d36df34a9db80a98050cd` failed at
`positive-pair-transactions`, status 113. It passed overlay and driver Java
compilation, parser self-test, configuration and allowlist Haskell compiles,
and both baseline Haskell compiles. The first positive driver's nested
configuration `krun`/`kparse` then exhausted the enforced 1536 MiB Java heap.

The cycle validates L/M's path repairs: its failing nested arguments use the
stable owner-qualified configuration definition and Java scratch paths, while
the rejected driver record was published through the immediate descriptor
path. There is no ENOENT, descriptor post-check, `kore-exec`, watchdog, or
teardown failure.

The installed-JDK probe records `MaxHeapSize=1610612736` and two active
processors. The watchdog did not fire and observed only 1,888,964 KiB peak
session RSS against its 6 GiB ceiling. The exact session was fully reaped with
`targetSessionEmpty: true`; no descendants remain. System available memory and
swap floors were preserved. No raw success, manifest, outer success, finalized
evidence, or accepted R3-G-05 report exists.

Treat cycle 4 as immutable failed-run provenance. Do not edit, delete, reuse,
refresh, finalize, publish, or copy from it. Final evidence after a passing
cycle 5 must record it exactly as:

```text
cycle 4 / failed / positive-pair-transactions /
nested-krun-java-heap-oom-1536 / status 113 / finalEvidence false
```

## Exact final-cycle authorization

Change only the cycle/resource/binding/evidence machinery needed to require:

- total substantive full-oracle cycle count exactly 5;
- fresh output exactly
  `spine/rule-applied-allowlist/build/cycle-5-r3-g-05n`;
- Java maximum heap exactly 2048 MiB for non-test raw execution;
- active processor count exactly 2;
- the existing 7200-second bounded timeout;
- the existing 6 GiB session RSS, 4 GiB available-memory, and 1 GiB free-swap
  watchdog limits with polling no slower than once per second;
- the existing exact clean implementation-head gate, semantic digest, free
  backend lock, serial/nice/two-CPU execution, session isolation, and fresh
  output reservation; and
- no unrelated heavy K or Lean work immediately before root launch.

Bind this packet and its distinct activation everywhere M is bound: semantic
inputs, accepted pins, exact authorization material, ancestry and packet-hash
preflight, raw success, manifest/cache validation, final JSON/Markdown evidence,
and verification. Retain the dynamic exact implementation-head binding.

The complete five-cycle ledger on success is:

1. failed, `frontend-setup`, driver compilation, status 1, no final evidence;
2. failed, `frontend-setup`, parser canonicality self-test, status 1, no final
   evidence;
3. failed, `configuration-compile`, nested self-FD working directory, status
   113, no final evidence;
4. failed, `positive-pair-transactions`, nested `krun` Java heap OOM at 1536
   MiB, status 113, no final evidence; and
5. pass with final evidence.

Zero-backend acceptance must reject cycle count 4 or 6, heap other than 2048,
the cycle-4 or any non-exact output path, missing N activation/packet/head
bindings, or a ledger that omits or alters any prior failure.

## Scope and terminal rule

Worker write ownership is only `spine/rule-applied-allowlist/**` excluding all
ignored raw build outputs. Change no K semantics, Java production/parser/path
behavior, resource/session algorithm, publication contract, accepted ancestor,
external K, package entry, or evidence outside the task directory. This packet,
delivery-loop/checkpoint/roadmap/decision records, lockfiles, and all cycle
outputs are read-only to the worker.

The worker may run Python, shell syntax/static checks, and zero-backend tests
only. Do not run Java, `javac`, K, `kompile`, `krun`, `kore-exec`, any
compiler/backend command, or the raw oracle. Return one clean binding repair
commit, semantic digest, and exact final-cycle authorization command.

Root will review the complete diff, commission fresh read-only audits,
independently replay zero-backend acceptance, and alone decide whether the live
resource/exclusivity gate permits total cycle 5. If cycle 5 does not yield
accepted R3-G-05 evidence, preserve it and write the final stop checkpoint.
There is no repair, retry, or sixth cycle under this split. Do not activate
R3-G-06 before accepted R3-G-05 evidence.
