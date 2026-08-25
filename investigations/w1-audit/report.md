# W1-B Gate D capability and oracle audit

## Verdict

**Qualified pass for the bounded W1-B packet; fail for R0/Gate D readiness to
authorize implementation fan-out.**

The candidate matrix accounts for all 42 compiler census groups and adds the
G1 product work that the compiler census omitted. Every candidate row has a
track, dependencies, owner/cluster, demonstrated current oracle grade,
candidate target grade, evidence status, and explicit unknowns. The matrix is
machine-verified and the Gate B smoke relational contract replays.

The project is not build-ready: the 42 census rows are still mostly coarse
group proxies rather than independently estimable leaves, all 21 G1 rows lack
a deterministic leaf acceptance command, the official ingress/configuration
cut and transformed-definition egress remain unresolved, and most original
oracle grades describe candidate strength rather than current demonstrated
strength. Do not promote the matrix unchanged or begin C1/C2 fan-out.

## Starting revision

`9f30221d08de4b0f710061ce599b3c7f9f860273` on branch `agent/w1-audit`, clean
before task-owned evidence was created.

Pinned references resolved during the audit:

| reference | revision |
| --- | --- |
| K | `4a46d1231473b599c699160132fd6e76a5c46406` |
| K_TS | `120e1dba90adb04f4730f90d8c0c516b30822811` |
| OLD_KINK | `c72d76d16cf0987253a60f1954c40c79c84ba465` |

## Commands executed

Exact command families, working-directory assumptions, and results are in
`commands.md`. Material acceptance commands were:

```sh
bun run check
bun test oracle/test p1/test p2/test p3/test
bun run oracle smoke oracle/suites/smoke.json \
  --out investigations/w1-audit/evidence/smoke
bun investigations/w1-audit/verify.mjs
jq empty investigations/w1-audit/capabilities.json
```

`bun run check` failed before tests because `tsc` is unavailable (exit 127).
No dependency installation was made outside the owned directory. The direct
Bun test command passed 10/10 tests, and the smoke replay passed.

## Evidence paths and digests

| evidence | SHA-256 |
| --- | --- |
| `capabilities.json` | `d63b212828ec2127023f94835a902d1467a80628a574d85475ba1c68cbc30177` |
| `verify.mjs` | `0c4f17f01eeffbdcdb1ca65209bb10d577be1011e59f24d09b965a1a3a7659ca` |
| `findings.md` | `f57b22d23a04a82d8d6982b2dd54e27912b89d8fcb6810a3dc8799695f5cd34b` |
| `dependencies.md` | `024e18f5718f7df4645dc28e299aed815df2501b24f159348158a2a2bd211986` |
| `commands.md` | `f24b064a5917b1a23305e37fedb3cb93ea309132369198d7129e93cb56608d46` |
| `hash-drift.json` | `a88c5b8262798908c453e9df5c2f7d942308f0dc71b174cc581dc49dff6e7860` |
| `evidence/smoke/smoke-report.json` | `a1966de7adba5a7a6f7d12c32109fce93bcddd8b268d052324a4e6669829f577` |

The generated 43 MiB capture tree had sorted SHA-256-of-SHA-256 manifest digest
`dfe90860b80e7c1c6f89cab602c2cff0cc2b94e665ba71184d2522e5d003806e`.
To keep the evidence commit compact, reproducible raw compiler outputs,
caches/binaries/scanners, and duplicate normalized artifacts are not committed.
The exact capture command/output location and compact comparison report are
preserved in `commands.md` and `evidence/smoke/smoke-report.json`.
The compact report retains paths to the pruned bundles because it is the
verbatim runner output; replaying the recorded command recreates those paths.

## Acceptance checks passed and failed

| check | result | evidence |
| --- | --- | --- |
| All 42 top-level compiler groups represented | pass | verifier reports 42/42 |
| Candidate rows have required schema fields, track, evidence status, and explicit unknowns | pass | 69/69 rows, `jq empty`, verifier pass |
| G1 work is explicit rather than forced into frontend groups | pass | 20 new G1 product rows plus G1 PR-03 split |
| Immediate/conditional/optional classification is machine readable | pass | G1 21, C1 31, C2 8, optional 9 |
| Current grade separated from candidate target grade | pass | every row has both fields |
| Missing information remains explicit | pass | status/unknowns/missing-command markers |
| Existing focused unit tests | pass | 10 pass, 0 fail, 16 expectations |
| Gate B smoke repeat/mutation relational contract | pass | seven repeated boundaries equal; expected six mutation differences and macro equality |
| Full declared `bun run check` | fail (environment) | `tsc: command not found`, exit 127 |
| Every G1 build-ready leaf has deterministic acceptance command | fail | 0/21; all are `missing-command` |
| Every compiler census row is an independently testable leaf | fail | 18 rows explicitly retain `group-proxy`; additional bounded rows remain partial |
| Official ingress/configuration/egress boundary fixed | fail | unresolved and delegated to the W1-A investigation |
| Fresh P1/P2/P3 reproduction | not evaluated here | separate W1-C packet |

## Oracle audit

Across the 69 candidate rows, demonstrated current grades are O0=30, O1=14,
O2=4, O3=13, O4=8. Restricting to rows derived from the 42 compiler groups
after necessary cross-track splits gives O0=14, O1=10, O2=4, O3=13, O4=8.
These are candidate-matrix audit judgments with bounded evidence scopes, not a
canonical regrading decision.

The original plan's 2/4/20/16 distribution is useful as a target-oracle map,
but it is not demonstrated by checked-in commands for all groups. P2's O4
claim is justified narrowly for the checked SimpleSub/Z3 inference fixture;
the other final-tree cases are O3 absent an independent invariant. P1 and P3
support O4 only for their stated projections and fixtures, not their complete
parent groups.

The smoke replay found exactly three unique documented JSON hash drifts:

| artifact hash | documented | replayed |
| --- | --- | --- |
| parsed JSON (context and full) | `00b5708b...731f` | `0c69fe97...2066` |
| context-prefix compiled JSON | `62f1dd1f...82a1` | `a6dd755a...3eb1` |
| full compiled JSON | `fe95fafc...3243` | `c78dc247...53a` |

The definition, syntax, and macros Kore hashes exactly match the documented
hashes. The current run's repeated baselines are equal at all seven boundaries,
and mutation expectations pass. An audit-only comparison after recursively
removing all JSON `digest` fields still found structural differences in all
four JSON boundary pairs. The earlier raw bundle is absent, so the cause of
the byte-hash drift remains unknown. Exact values are in `hash-drift.json`.

## Material omissions and overclaims

The detailed source-referenced list is `findings.md`. The material items are:

1. The 42-group census omits the active G1 product capabilities.
2. Coarse and cross-track groups are not build leaves; several need splitting.
3. Candidate oracle availability was worded as current grade in the census.
4. P2 O4 is broader than the independent cross-check supports.
5. P1/P3 projections and official-K executions do not establish production
   K-in-K compiler completeness.
6. Required parser, metadata, prepared-module, and egress seams are missing.
7. Negative and interaction coverage is absent for major validation, caching,
   option, configuration, and G1 failure contracts.
8. Smoke `macros.kore` equality does not exercise macro behavior.
9. Prefix JSON comes from an explicitly accepted failed compilation and must
   never be described as successful backend completion.

## Newly discovered contracts

1. A promoted matrix needs separate `granularity`, `evidence_scope`,
   `current_oracle_grade`, and `candidate_target_oracle_grade`; parent groups
   must not masquerade as leaves.
2. Adapter dependence and semantic ownership are separate classifications. G1
   depends on official parsing/lowering without making IN/IP/CF/LO/KO active
   implementation work.
3. Evidence ledgers must distinguish exact byte hashes from relational
   acceptance (repeat equality, mutation sensitivity) and pin serializer plus
   normalization-policy versions.
4. G1 has one unavoidable serial boundary contract: ingress/configuration cut
   plus supported egress. SemanticInput cannot be frozen safely before it.
5. Grade promotion must state the bounded corpus slice; a single O4 probe case
   cannot upgrade its whole parent group.
6. Acceptance prose is not a deterministic task command. Each promoted G1 leaf
   needs a checked-in command and fixture before it is build-ready.

## Requested shared-contract changes

The full requests and ownership graph are in `dependencies.md`. Root
integration should:

- adopt the matrix-grade/granularity distinction;
- freeze the configuration cut and egress before SemanticInput v1;
- version identity/provenance/fingerprint stability;
- version canonical patches, edit addressing, overlap, atomic application,
  and failure outputs;
- share a layered validation/status taxonomy across both goal features;
- add parser-filter, configuration-metadata, and prepared-module seams before
  C2/C1 implementation; and
- record hash drift separately from relational oracle verdicts.

## Remaining unknowns

- Which structured artifact, API, or canonical regenerated source official K
  can accept after G1 transformation.
- Whether the initial SemanticInput boundary is before or after configuration
  generation, and which CF behavior is trusted temporarily.
- Whether official sentence IDs survive the chosen egress/recompile path; the
  stable-identity composition is not demonstrated.
- Exact leaf decomposition and corpus interactions inside remaining group
  proxies.
- The cause of the three JSON hash drifts.
- Fresh-agent reproducibility and any discrepancies for P1, P2, and P3
  (owned by W1-C).
- Raw parser/filter shapes, configuration metadata queries, and the prepared
  module before ModuleToKORE.
- Proof/specification scope and all optional F2/F3 compatibility work.

## Recommended next packet

Complete/integrate W1-A and W1-C first. Then issue one narrow R1 packet for an
**identity + sentence-provenance round-trip through the selected official-K
ingress/configuration/egress boundary**. Its prerequisite is a written boundary
decision from W1-A; its output must freeze the smallest SemanticInput slice,
identity mapping, manifest schema, and one deterministic acceptance command.
Do not start the observation/mutation branches or any C1/C2 implementation
until that round-trip either passes or returns a classified egress blocker.
