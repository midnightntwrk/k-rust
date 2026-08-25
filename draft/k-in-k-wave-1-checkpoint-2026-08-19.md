# K-in-K Wave 1 checkpoint — 19 August 2026

Status: accepted evidence checkpoint. This record summarizes the first
orchestration wave and authorizes only the next bounded adapter investigation.
It is not a live project-status page and does not rewrite the historical intent
snapshot.

## Starting point and integrated evidence

All Wave 1 workers began from baseline
`9f30221d08de4b0f710061ce599b3c7f9f860273` in isolated worktrees.

The root integrated:

| packet | verdict | worker commit | integrated commit | evidence |
| --- | --- | --- | --- | --- |
| W1-A ingress/configuration/egress | pass, narrow temporary route | `37b9b845ee0ce8869efe19040966748c3a2c469b` | `4ae8dfa` | `investigations/w1-egress/` |
| W1-B Gate D audit | qualified pass; fail for fan-out readiness | `581ecccfadee761377b62c5a5c13fabf20ff0aca` | `d0aa9d4` | `investigations/w1-audit/` |
| W1-C independent probe replay | pass | `be6e6eecaace62a4706b3d33ca170f972312162f` | `93edfcc` | `investigations/w1-replay/` |

After integration, `bun run check` passed with 10 tests and no failures.

## Accepted conclusions

### Reconnaissance replay

P1, P2, and P3 reproduce from the baseline using their documented commands.
No semantic discrepancy was found. The direct probe runners inherit and do not
record locale/timezone, unlike the oracle capture; this is a small harness
contract gap rather than a failed probe conclusion.

### Capability and oracle audit

The 42 compiler census groups are accounted for, but the census is not yet a
build-ready leaf matrix and omits the active G1 product capabilities. The
candidate audit matrix contains 69 rows:

- G1: 21;
- conditional C1: 31;
- C2: 8; and
- optional: 9.

The candidate matrix is evidence, not yet the canonical implementation matrix.
All 21 G1 rows currently lack deterministic leaf acceptance commands. Several
original oracle grades describe candidate target strength rather than current
demonstrated strength; the candidate matrix separates those fields.

The Gate B relational contract still passes. Three documented JSON hashes
drifted, while all three Kore hashes remained exact; repeated baselines and
mutation sensitivity still behaved as required. Track exact-byte drift
separately from relational oracle acceptance.

### Official-K transformation boundary

The hidden `--post-process` KAST v4 hook demonstrated:

- identity re-entry for Peano and P3;
- equal selected sentence identity/provenance projections;
- byte-identical final Kore and representative runtime behavior;
- one typed edit to an already-concretized P3 rule; and
- deterministic official compilation and execution after the edit.

This is a bounded temporary fallback, not the R2-G production boundary. It runs
after all official frontend passes and checks, is too late for configuration or
observation-cell augmentation, changes set-backed JSON array order, and leaves
`UNIQUE_ID` stale after a post-numbering body edit.

Official emitted `parsed.json` is observational rather than a lossless compiler
input: it trims `DEFAULT-CONFIGURATION` and omits inner `Production` attributes
needed by later checks/passes. The inspected paths exposed no canonical typed
definition-to-K-source emitter. An ordinary-source observation-cell fixture did
compile and execute deterministically, proving official configuration
generation can handle the additive cell but not providing typed egress.

## Boundary decision for the next packet

Retain official parsing, disambiguation, sort inference, and configuration
generation, including CF-01 through CF-03, for the initial G1 adapter.

Investigate a lossless in-process boundary over official `Definition` values:

```text
official parse/disambiguation/configuration generation
  -> lossless in-memory Definition
  -> K-in-K transformation adapter
  -> official KoreBackend.steps()
  -> ModuleToKORE/backend
```

Do not freeze `SemanticInput v1` until this composition has been demonstrated
or returned a classified blocker. Do not use emitted `parsed.json` as the
schema simply because it is available.

Stable sentence identity must be distinct from the content fingerprint. A
later contract must carry input fingerprint, output fingerprint, lineage or
parent identity, and transformation identity; surviving backend `UNIQUE_ID`
alone is insufficient validation.

## Authorization and hold points

The only newly authorized implementation packet is
`tasks/wave-1/W1-D-inprocess-adapter.md`.

Hold:

- `SemanticInput v1` finalization;
- observation and mutation implementation workstreams;
- pre-configuration observation augmentation;
- C1/C2 implementation fan-out; and
- forecast/concurrency expansion.

If W1-D passes, the root may write the concrete adapter ADR and issue one
identity/provenance transformation-spine packet. Pre-CF configuration
augmentation remains a separate packet. If W1-D is blocked, record an early
D1-style scope decision instead of silently expanding into official-K changes
or independent lowering.

