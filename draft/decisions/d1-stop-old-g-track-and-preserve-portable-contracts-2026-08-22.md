# D1: stop the old G track and preserve portable contracts for Rust

Status: accepted scope decision, 22 August 2026.

## Decision

Stop the official-K/Java/Haskell G-track implementation at the terminal
R3-G-05 checkpoint. Do not repair it, add a sixth cycle, or build temporary
executor/adapter abstractions around it. Complete backend-agnostic semantic
investigation and conformance evidence, then implement and prove those
contracts through the planned Rust-based stack.

This is a superseding user-owned stack/scope decision, not a selection of the
roadmap's evidence-driven `stop or redesign` outcome. The evidence does not
show that K-authored semantic transformation lacks useful advantage. The user
has independently committed the project to a different implementation stack,
so further work on the retired stack would not answer the remaining product
questions efficiently.

The newly authorized scope is
`investigations/backend-agnostic-goal-closure/`: contracts, canonicalization,
schemas, fixtures, vectors, failure/status semantics, evidence classification,
and a dependency-ordered Rust handoff. Rust implementation is a later scope.

## Answers to the six D1 questions

1. **Do both goals work end to end through the transformation kernel?** No.
   R3 proves one event/head match and exact same-origin adjacency only. R3-G-05
   is unaccepted, and R4 has no implementation exit evidence.
2. **Is the protocol reusable across two structurally different fixtures?**
   Transport identity crossed Peano and P3, but patch behavior was proven only
   on P3 and general observation/mutation protocols were not established.
3. **Which limitations are adapter versus transformation design?** The pinned
   adapter path surfaced a demonstrated scalability risk when nested textual
   ingress exhausted the enforced heap before application; the evidence does
   not isolate that mechanism as the sole cause. Independently, general
   identity derivation, overlap algebra, domain events, occurrence semantics,
   symbolic status, candidate enumeration, and reporting remain design
   questions. The portable package must resolve those that do not inherently
   require backend execution, without claiming implementation proof.
4. **Would owning a frontend stage materially help?** The planned Rust stack
   makes a native structured semantic boundary strategically preferable and
   avoids repeating the stopped textual projection. Existing evidence does not
   justify a finer claim about which Rust stage will improve performance or
   correctness; that requires RS-01/RS-03 measurements.
5. **Is compiler independence an explicit goal?** A Rust-based stack is the
   project direction supplied by the user. This D1 does not infer C1/C2 or
   exact artifact parity from the two product goals and does not activate
   independent Kore emission or parsing work.
6. **What measured cost separates the alternatives?** The repository has no
   credible comparative Rust implementation measurements yet. The old track
   consumed five R3-G-05 cycles and terminated at nested parser heap exhaustion
   before any pair transaction. RS packet evidence must replace speculative
   cost estimates.

## Evidence

- accepted R2 evidence under `evidence/r2-g-*` establishes the bounded identity
  and patch/transaction kernel;
- accepted R3 evidence under `evidence/r3-g-01*` through `r3-g-04*` establishes
  bounded typed-event, provenance, concrete head-match, and exact-adjacency
  vectors;
- `draft/k-in-k-r3-g-05-final-five-cycle-stop-checkpoint-2026-08-22.md`
  establishes the terminal negative result and absence of accepted R3-G-05
  evidence; and
- `investigations/backend-agnostic-goal-closure/evidence-inventory.json`
  states the precise portable, stack-specific, rejected, and Rust-open scopes.

## Held work

No current-backend repair, cached finalization, R3/R4 implementation leaf,
streaming monitor, backend-log product interface, C1/C2 work, persistent
external-K change, or unrelated optional expansion is authorized by this
decision. The Rust handoff orders later capability packets but does not
activate them.
