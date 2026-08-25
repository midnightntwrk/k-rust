# R3-G-05 final five-cycle stop checkpoint — 22 August 2026

Status: terminally stopped at the explicitly authorized five-substantive-cycle
cap. R3-G-05 is not accepted, R3-G exit evidence is incomplete, and R3-G-06
is not active. No sixth R3-G-05 cycle, heap increase, repair, retry, cached
finalization, or evidence publication is authorized.

## Preserved implementation and outputs

The isolated implementation lineage is clean head
`c8f939d3f462457f36a16c66fdf9f50d5b6b66cb` on
`agent/r3-g-05-metadata-repair`, exactly one implementation commit over the
R3-G-05P activation `7a072969a09260a1e3263de94b84dc3d54fac5d2`.
Its full zero-backend replay, Python compilation, shell syntax, static
acceptance, adversarial refusal suite, and `git diff --check` passed before the
raw launch. Its semantic digest was
`67cfe95fc708cccdd9fcc29617f06b66660902f6d88d3ca917d022b8acf786c5`;
the exact cycle-5 authorization digest was
`6ea46095082d88733c25c64607714444514281399c2f6b6e34b68eb150cff51d`.

All five ignored build outputs in the isolated worktree are immutable failed
run provenance. Do not edit, delete, reuse, refresh, finalize, publish, or copy
accepted evidence from any of them. In particular, preserve:

```text
spine/rule-applied-allowlist/build/cycle-4-r3-g-05l
spine/rule-applied-allowlist/build/cycle-5-r3-g-05n
```

## Complete substantive-cycle ledger

| cycle | clean implementation head | fresh output | terminal boundary | result |
| ---: | --- | --- | --- | --- |
| 1 | `014d77690977805d06b9d4a1c3a334afb0fd5678` | `build/cycle-1-r3-g-05i` | `frontend-setup`, status 1 | driver compilation exposed a Java scope defect; no K definition/backend artifacts |
| 2 | `940d90172f360fa48e9b848516e419b200e6756f` | `build/cycle-2-r3-g-05j` | `frontend-setup`, status 1 | parser self-test exposed a no-op missing-delimiter adversary; no K definition/backend artifacts |
| 3 | `d1523d8911523a6aa6603fb266e8c25c5ca1c449` | `build/cycle-3-r3-g-05k` | `configuration-compile`, status 113 | nested compiler child could not resolve the immediate self-FD working directory |
| 4 | `017e5b68c60e92601f8d36df34a9db80a98050cd` | `build/cycle-4-r3-g-05l` | `positive-pair-transactions`, status 113 | stable owner-qualified paths succeeded, then nested configuration `krun`/`kparse` exhausted the enforced 1536 MiB Java heap |
| 5 | `c8f939d3f462457f36a16c66fdf9f50d5b6b66cb` | `build/cycle-5-r3-g-05n` | `positive-pair-transactions`, status 113 | the same nested configuration `krun`/`kparse` path exhausted the exact hard-maximum 2048 MiB Java heap |

Cycles 4 and 5 validate the stable descriptor-owner and Java-scratch repair:
the nested arguments use
`/proc/<outer-owner-pid>/fd/198/configuration-k-kompiled` and the sibling
owner-qualified `java-scratch` input, while immediate record publication
succeeded. Neither cycle shows ENOENT, descriptor post-check, `kore-exec`,
watchdog, or teardown failure.

## Final cycle-5 evidence

The exact clean launch waited until the unrelated KRS verifier had exited, the
backend lock was free, no heavy K/Lean workflow remained, about 22.5 GiB RAM
was available, and about 3.5 GiB swap was free. Non-test raw execution enforced
2048 MiB heap, two active processors, total cycle count five, exact 7200-second
timeout, lowered priority, two-CPU affinity, and the existing session watchdog.

The first-writer terminal record is:

```json
{"exitStatus":113,"schema":"R3-G-05-raw-failure-v1","stage":"positive-pair-transactions"}
```

The published `records/instrumented-a.json` localizes the failure before any
configuration or rule application:

```text
[Error] Internal: Uncaught exception thrown of type OutOfMemoryError.
(OutOfMemoryError: Java heap space)
[Error] kparse: ... --definition
/proc/3767765/fd/198/configuration-k-kompiled
/proc/3767765/fd/198/java-scratch/configuration-2235833284459069174.kink
[Error] krun: kparse --definition
/proc/3767765/fd/198/configuration-k-kompiled ...
```

The JDK probe and diagnostic both show `-Xmx2048m` and
`ActiveProcessorCount=2`. The rejected record reports zero configuration
applications, zero rule applications, zero pair transactions, zero rule
transformer traversals, no output definition, and no backend construction.

The watchdog did not fire. It observed a peak exact-session RSS of 2,423,740
KiB against the 6 GiB ceiling; the 4 GiB available-memory and 1 GiB free-swap
floors remained armed. The outer session records `innerStatus: 113`,
`reason: inner-failure`, `wallTimeoutSeconds: 7200`, and
`targetSessionEmpty: true`. All recorded launcher, descriptor-owner, target,
and watchdog PIDs are gone, with no exit-time descendants. Output device 2096
and inode 738196 agree across reservation/readiness/session records.

There is no raw success, integrity manifest, outer success, provisional
results/report, finalized evidence, or accepted R3-G-05 evidence.

## Terminal decision

The final permitted one-parameter retry disproved that the established 2048
MiB hard maximum was sufficient. The split explicitly forbids a sixth cycle
and any further repair or heap increase. Therefore the dependency-only path
cannot advance to R3-G-06, R3-G exit evidence, R4-G, or D1 under the current
authorization.

Until a new user-owned roadmap decision changes scope or constraints:

- R3-G-05 remains stopped and unaccepted;
- R3-G-06 through R4-G-05 and D1 remain dependency-blocked;
- no R3-G-05 compiler/backend cycle or cached evidence finalization is
  authorized; and
- C1, C2, optional leaves, and streaming monitors remain inactive.
