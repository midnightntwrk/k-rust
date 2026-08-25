# R3-G-05K: parser adversary binding and final-cycle repair

Status: eighth and final-cycle R3-G-05 acceptance repair. Clean J implementation
`940d90172f360fa48e9b848516e419b200e6756f` over activation
`698d92123d75b40cd5b12d19244829cae308f426` is accepted by the complete
zero-backend suite and two read-only audits. Root's fresh substantive cycle 2
used `build/cycle-2-r3-g-05j`, compiled the frontend overlay and task driver
cleanly, then failed the driver parser-canonicality self-test at
`frontend-setup`. Preserve cycle 1 and cycle 2 outputs as immutable failed-run
provenance; neither may be reused or finalized.

## Exact cycle-2 blocker

Cycle 2 produced no K definition, Haskell backend, `compiled.bin`,
`definition.kore`, or `backend.txt`. Its exact terminal failure is stage
`frontend-setup`, exit status 1. `driver-javac.stderr` contains only the forced
Java option line, proving the J scope repair compiled. `parser-self-test.stderr`
ends at `TraceResultParser.selfTest` line 2408 with:

```text
java.lang.AssertionError: noncanonical or malformed trace result was accepted
```

That line constructs the missing-delimiter negative with:

```java
canonical.replace(",\"lineage-a\",", "\"lineage-a\",")
```

The target substring is absent: lineage begins inside
`oAllowlistMember("lineage-a","content-a",...)`, so `String.replace` returns
the unchanged canonical result. The parser correctly accepts it; the self-test
incorrectly treats that as acceptance of a mutation. Cycles 1 and 2 are both
substantive because their frontend compilation/execution results drive repairs.
Exactly one cycle remains under the original cap.

## Bound parser adversaries

Replace the no-op delimiter mutation with a real malformed result, such as
removing the comma between the first lineage and content strings. Preserve the
parser grammar and canonical success encoding.

Make the self-test fail before parsing whenever any intended mutation equals
the canonical input. Route every derived negative through one helper that:

1. requires the mutated bytes differ from canonical;
2. parses the mutated bytes;
3. accepts only `ValidationException`; and
4. reports the named mutation if unchanged or unexpectedly accepted.

The canonical positive must still parse. Retain and bind all seven negatives:
leading-zero integer, negative-zero path, Unicode escape, missing delimiter,
multiple result, residual result, and unknown constructor. Add zero-backend
static witnesses that fail the J source: the old absent replacement literal is
forbidden, every negative uses the change-binding helper, and the helper checks
canonical inequality before parser rejection.

Do not change K authority, the Java production/mutation/atomicity algorithms,
the parser grammar, resource/session wrappers, secure failure recovery, or any
accepted I/J behavior.

## Cycle history and exact authorization

Bind this packet and its activation everywhere J is bound: semantic inputs,
accepted pins, exact command authorization, ancestry/hash preflight, raw
success inputs, final evidence, and verification. Require substantive cycle
count exactly 3. Final evidence must record:

- cycle 1: failed, `frontend-setup`, driver compilation, exit 1, no final evidence;
- cycle 2: failed, `frontend-setup`, parser canonicality self-test, exit 1, no
  final evidence; and
- cycle 3: pass with final evidence.

Retain the entire bounded zero-backend acceptance suite. Do not run Bun, K,
Java, `javac`, `kompile`, `krun`, a compiler/backend, parser self-test, or raw
oracle in the worker repair. Do not edit K semantic source or external K.

Return one clean repair commit and a newly bound guarded command for fresh
`build/cycle-3-r3-g-05k`, cycle count 3, 1536 MiB heap, and two CPUs. Root will
review the complete diff, commission fresh read-only audits, recheck unrelated
heavy work/resources, and alone decide whether to authorize the final cycle.

## Ownership and terminal stop rule

Ownership remains only `spine/rule-applied-allowlist/**`, owned R3-G-05
evidence, and the existing package entry. Do not edit this packet,
checkpoints/roadmaps/loop/decisions, accepted artifacts, lockfiles, or external
K. Stop rather than broaden scope, weaken parser or first-writer validation,
reuse either failed output, or activate R3-G-06 early.

If substantive cycle 3 does not yield accepted R3-G-05 evidence, do not run a
fourth cycle. Preserve the failure and return the required stop/split checkpoint
for root integration.
