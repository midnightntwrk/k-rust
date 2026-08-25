# R3-G-05P: exact-timeout report verification

Status: pre-launch evidence-verification repair required by the second fresh
audit of R3-G-05O implementation
`0b8fb11967ff48f8482b78ff8dffe7336d215363`. Cycle 5 remains unstarted and
its output is absent. This packet spends no substantive cycle and does not
authorize a sixth cycle.

## Audit blocker

O correctly requires numeric `wallTimeoutSeconds: 7200` throughout raw launch,
authorization, raw success, manifest/cache, final JSON, and JSON verification.
Its finalizer also writes an exact 7200-second statement into the Markdown
report. However, `verify.py` does not require that exact report witness.

An altered report could replace the exact statement with a weaker phrase such
as “bounded timeout”; after updating the report hash in `results.json`, every
current Markdown witness and all exact JSON checks would still pass. That
violates O's requirement that finalized JSON and Markdown evidence both record
the exact timeout.

## Exact repair

Change only the task-local evidence binding and zero-backend refusal machinery
needed to ensure:

- final Markdown contains one stable, unambiguous witness that cycle 5 used the
  exact 7200-second wall timeout;
- `verify.py` requires that exact witness, not merely the word “bounded” or an
  indirect JSON field;
- zero-backend adversarial acceptance proves that removing or weakening the
  exact Markdown witness is rejected even when the attacker recomputes the
  report hash in the final JSON; and
- static acceptance proves the finalizer, verifier, and adversarial check stay
  mutually bound to the same exact witness.

Bind this packet and its implementation-line activation anywhere required for
the semantic digest, accepted pins, authorization, raw success, manifest,
final evidence, and verification to describe the exact accepted lineage.

Retain every N/O invariant unchanged: exact clean implementation HEAD, fresh
exact `cycle-5-r3-g-05n` output, exactly five cycles, Java heap exactly 2048
MiB, exactly two active processors, wall timeout exactly 7200 seconds, existing
watchdog thresholds and polling, serial lock, nice/two-CPU affinity,
watchdog/session/descriptor isolation, complete teardown, immutable cycle-4
failure provenance, and prohibition of cycle 6. Do not change runtime,
resource, Java, K, path, descriptor, or publication algorithms.

## Worker boundary and acceptance

Worker write ownership is only `spine/rule-applied-allowlist/**`, excluding all
ignored raw build outputs. This packet, delivery-loop/checkpoint/roadmap files,
external K, accepted ancestors, and every cycle output are read-only.

The worker may run Python, shell syntax/static checks, and bounded zero-backend
tests only. Do not run Java, `javac`, K, `kompile`, `krun`, `kore-exec`, any
compiler/backend command, or the raw oracle. Return exactly one clean repair
commit over this packet's implementation-line activation, with the semantic
digest and exact root authorization digest/command. Cycle 5 must remain absent.

Root will review the diff, replay zero-backend acceptance, and commission two
fresh read-only audits. Only unanimous acceptance plus a fresh live gate permits
the one N-authorized cycle 5. A failed cycle 5 is terminal for R3-G-05: preserve
it, write the stop checkpoint, and do not repair, retry, or run cycle 6.
R3-G-06 remains dependency-blocked until accepted R3-G-05 evidence exists.
