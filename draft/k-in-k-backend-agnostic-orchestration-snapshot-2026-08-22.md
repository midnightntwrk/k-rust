# Backend-agnostic investigation orchestration snapshot — 22 August 2026

Status: historical tentative orchestration record. It preserves the working
idea at the start of the post-D1 closure loop so later compaction does not turn
the package outputs into the objective or erase why the work was ordered this
way. It is expected to become stale. Do not maintain it as a live status page;
later accepted packets, audits, and the roadmap take precedence.

## Objective understood at this point

Exhaust every reasonably valuable investigation for execution-pattern matching
and semantic mutation whose answer is independent of the future execution
stack. Stop only when each remaining material uncertainty inherently requires
Rust/backend execution or measurement, or a genuine product decision.

The closure package, fixtures, verifier, completion audit, and Rust handoff are
durable evidence and outputs of this work. Producing them is not itself the
goal. The retired backend is neither repaired nor used to define portable
semantics.

## Packet/build loop

Repeat one serial shared-schema epoch:

1. Root audits the residual uncertainty and fleshes out one bounded packet,
   including exact identities, derivations, adversaries, ownership, and the
   Rust-only proof boundary.
2. A fresh high-reasoning Sol context implements that packet against the
   integrated package. It does not edit roadmap/D1/goal records or run K, Java,
   Rust, a compiler, solver, backend, or network fetch.
3. Root integrates, independently checks scope and claims, runs the serial
   zero-backend verifier plus official Draft 2020-12 validation, confirms
   refresh idempotence and whitespace, and updates the next dependency packet.
4. A separate read-only Sol lane audits the next packet and cross-packet seams
   while the sole writer builds. It never edits shared package files.

One implementation writer owns the shared package at a time. Root may edit
non-overlapping packet/roadmap text while that writer works. A new writer does
not start until the previous packet has been integrated and reverified. Fresh
contexts are preferred because the packet is the context boundary; compact
worker reports return findings rather than raw logs.

## Tentative dependency path at capture time

The integrated foundation was BAG-02 through BAG-08. The tentative remaining
path was:

```text
BAG-09 terminal/crash semantics
  -> BAG-10 failure taxonomy and checked semantic evidence
  -> BAG-13 portable term/symbol/local-well-formedness boundary
  -> BAG-11 normalized query plan and exact witness denotation
  -> BAG-12 typed oracle declarations/operands/comparisons
  -> BAG-14 immutable attempt cache and completeness
  -> BAG-15 producing receipts and campaign derivation replay
  -> BAG-16 search policy and branch-trace collection completeness
  -> fresh residual audits and documentation/D1/handoff closure
```

BAG-13 was moved ahead of BAG-11/BAG-12 after audit showed that both would
otherwise freeze complete values over an overclaimed free-string term surface.
Later audits may split packets or move prerequisites, but should not activate a
leaf unrelated to exhausting backend-agnostic uncertainty.

## Conflict and resource policy

- Shared schemas, fixtures, refresh logic, catalog, and verifier have exactly
  one writer.
- Read-only audits may run concurrently and report contract-change requests to
  root.
- Root owns scope, task packets, integration, roadmap/D1, and the final residual
  classification.
- Commands remain lightweight and serial. Python verification is run at low
  priority on one CPU; no recursive builds, broad filesystem scans, or parallel
  verifier jobs are used. This policy follows prior machine OOM/freeze events.
- Work is not declared closed because the package is large or internally
  green. A final independent audit must show that every residual question is
  intrinsically stack-dependent or product-owned.

## Worker return contract

Each writer returns: implemented contract, files/surfaces changed, verifier and
schema results, adversaries added, claim boundary, unresolved questions, and
recommended next packet. Each auditor returns exact omissions, cross-packet
ownership/dependencies, permanent adversaries, and what must remain Rust-only.
