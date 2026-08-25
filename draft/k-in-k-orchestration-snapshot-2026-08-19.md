# K-in-K orchestration intent snapshot — 19 August 2026

Status: historical planning snapshot. This file records the orchestration idea
at the moment Wave 1 was authorized. It is not a live status page, an enduring
assignment of ownership, or authority to continue into later waves.

When this file disagrees with accepted evidence, later decision records, task
packets, or `draft/k-in-k-execution-roadmap.md`, the later accepted artifact
wins. Do not update this file merely to make it describe what eventually
happened; preserve it as the record of the original plan. Record departures in
the evidence ledger or a new dated snapshot.

## Why preserve this snapshot

The project is expected to cross agent and conversation-context boundaries.
This snapshot preserves the intended division of work, dependency order, and
conflict controls even if the originating conversation is compacted. Its value
is historical: it lets later reviewers compare the plan with the evidence and
understand why work was divided this way.

K is the committed implementation medium for the definition transformation.
Wave 1 contains no comparative investigation of whether a conventional AST
library would be a better product architecture.

## Operating model

Use at most three worker agents concurrently, leaving the root agent as the
integration and decision owner. The root agent owns:

- the roadmap and decision records;
- task-packet scope and acceptance;
- shared schema and adapter-contract approval;
- integration and merge order;
- the evidence ledger and forecast; and
- authorization of later waves.

Worker agents operate from the same immutable starting revision in isolated
Git worktrees. They do not spawn subagents. Each worker owns only the paths
listed in its task packet. Raw logs remain in task-specific artifact paths;
the root context receives a compact structured report.

No two agents concurrently redesign or edit:

- `SemanticInput` or another shared schema;
- official-K ingress or egress adapter contracts;
- the roadmap or decision records;
- root package manifests or lockfiles; or
- the canonical capability-matrix schema.

If an agent discovers that a shared contract must change, it records a
contract-change request rather than editing the contract outside its ownership.

## Wave 1: retire the planning blockers

Wave 1 begins from one baseline commit and runs three bounded investigations.
The executable task packets are under `tasks/wave-1/`.

### W1-A: ingress, configuration, and egress

One high-reasoning Sol agent investigates the decisive official-K round trip:

- the pre- versus post-configuration ingress cut;
- supported structured re-entry, if any;
- canonical generated-definition re-entry;
- a replayable fallback artifact if necessary; and
- identity plus one small transformation across structurally different
  fixtures.

This is the technical critical path. Its output is evidence and a recommended
adapter decision, not a silently adopted shared implementation. If the result
is usable, retaining this agent for the later transformation-spine task is
preferred because its boundary context is valuable.

### W1-B: Gate D capability and oracle audit

One Sol agent independently audits the capability census and classifies work as
G1-required, conditional C1, C2, or optional. It identifies dependency edges,
coupled ownership clusters, oracle grades, missing negative behavior, and
claims not justified by the current probes. It produces a candidate
machine-readable matrix in its isolated task path; the root decides whether and
how to promote it to the canonical matrix.

### W1-C: independent P1/P2/P3 replay

One fresh Sol agent receives the repository and its task packet rather than the
originating conversation. It replays P1, P2, and P3 from documented commands,
checks the generated evidence against the reports, and classifies discrepancies.
The first replay is diagnostic and may not repair tracked sources. A failure
becomes a smaller repair packet only after the evidence is preserved.

## Wave 1 integration gate

The three workers do not collectively decide the architecture. The root waits
for their reports, checks their starting revisions and evidence, and records an
accepted boundary decision or a classified blocker.

Wave 1 closes only when:

1. the probes reproduce or discrepancies are classified;
2. the G1/C1/C2/optional classification is independently reviewable;
3. the official-K egress path is demonstrated or its precise blocker is known;
4. the configuration trust boundary is explicit; and
5. the next shared contract can be expressed as a bounded task packet.

## Tentative later waves

These waves record intent only. They are not authorized by this snapshot.

### Wave 2: shared transformation spine

After the adapter decision, use one exclusive spine owner for minimal
`SemanticInput`, deterministic serialization, provenance, identity,
fingerprints, lookup, typed binding, and patch application. Two downstream
agents may work in parallel on observation and mutation fixtures/oracles
against a frozen schema revision. They request contract changes instead of
editing the schema.

Publish schema revisions at explicit integration points. Batch downstream
contract requests and avoid continuous rebasing against a moving API.

### Wave 3: fresh acceptance replay

Use fresh, minimally primed agents to replay identity/round-trip, observation,
and transactional-mutation acceptance from task packets. They validate rather
than repair unless separately authorized.

### Wave 4: estimation calibration

Run normalized capability packets in batches of at most three. Use a fresh
agent thread for each measurement sample; retained context is allowed only when
continuity is intentionally part of the task. Record first-pass acceptance,
oracle cycles, contract omissions, regressions, and replay outcome before
publishing range estimates or changing the concurrency ceiling.

## Worker return contract

Every worker report should contain:

```text
verdict
starting revision
commands executed
evidence paths and digests
acceptance checks passed and failed
newly discovered contracts
requested shared-contract changes
remaining unknowns
recommended next packet
```

The report should be concise. Raw compiler output, traces, and generated
artifacts belong in the referenced evidence directory rather than the report or
root conversation.

