# R3-G-05O: exact final-cycle timeout binding

Status: pre-launch repair required by the fresh Linux/resource-policy audit of
R3-G-05N implementation `0e255de8d3c0bed497588514a08f22afee2c1552`.
That implementation is otherwise accepted, but total cycle 5 has not started
and its output remains absent. This packet spends no substantive cycle and
does not authorize a sixth cycle.

## Audit blocker

N requires the final raw cycle to use the existing timeout of exactly 7200
seconds. The implementation defaults to 7200, but non-test raw mode accepts
any integer from 60 through 14400 and binds the caller-selected value into the
authorization digest. Cache validation and final evidence then prove only that
the timeout was bounded. Static acceptance does not exercise an alternate
timeout refusal.

Consequently an invocation at (for example) 3600 or 14400 seconds could obtain
a matching root authorization and publish evidence that satisfies the current
validators. That is broader than the N packet and must be closed before cycle
5 reserves its output.

## Exact repair

Change only the task-local cycle/resource/binding/evidence machinery needed to
make 7200 seconds an exact final-cycle invariant:

- non-test `raw` and `raw-inner` execution must require the wall timeout to be
  exactly 7200 seconds;
- the authorization material must continue to bind that exact value;
- raw success, manifest/cache validation, finalized JSON/Markdown evidence,
  and verification must record and require `wallTimeoutSeconds: 7200` (or the
  existing field's equivalent exact numeric representation), not merely a
  truthy `boundedTimeout` claim;
- zero-backend static/adversarial acceptance must prove that at least one
  alternate in-range value is rejected and that evidence/cache records with
  an altered or missing exact timeout are rejected; and
- test mode may retain bounded alternate values only where necessary to run
  refusal and launcher tests without a backend. Test-mode flexibility must not
  weaken any non-test or published-evidence invariant.

Retain every accepted N binding unchanged: exact clean implementation HEAD,
N activation and packet hash, semantic and authorization digests, fresh exact
`cycle-5-r3-g-05n` output, exactly five cycles, Java heap exactly 2048 MiB,
exactly two active processors, the 6 GiB session RSS ceiling, 4 GiB available
memory floor, 1 GiB free-swap floor, serial lock, nice/two-CPU affinity,
watchdog/session/descriptor isolation, complete teardown, immutable cycle-4
failure provenance, and prohibition of cycle 6.

## Worker boundary and acceptance

Worker write ownership is only `spine/rule-applied-allowlist/**`, excluding all
ignored raw build outputs. Do not change K semantics, Java production/parser
or path behavior, resource limits, session algorithms, publication topology,
accepted ancestors, external K, this packet, delivery-loop/checkpoint/roadmap
records, or any cycle output.

The worker may run Python, shell syntax/static checks, and bounded zero-backend
tests only. Do not run Java, `javac`, K, `kompile`, `krun`, `kore-exec`, any
compiler/backend command, or the raw oracle. Return exactly one clean repair
commit over this packet's implementation-line activation, with the semantic
digest and exact root authorization digest/command. Cycle 5 must remain absent.

Root will inspect the complete diff, replay zero-backend acceptance, and
commission two fresh read-only audits. Only unanimous acceptance plus a fresh
live resource/exclusivity check permits the one N-authorized cycle 5. If that
cycle fails, preserve its output and write the final R3-G-05 stop checkpoint;
do not repair, retry, or run cycle 6. R3-G-06 remains dependency-blocked until
accepted R3-G-05 evidence exists.
