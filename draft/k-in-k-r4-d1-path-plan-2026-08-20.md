# K-in-K dependency-only path to R4-G exit and D1 — 20 August 2026

Status: historical tentative orchestration record, superseded on 22 August
2026 by the terminal R3-G-05 stop, the superseding D1 stack/scope decision, and
`investigations/backend-agnostic-goal-closure/rust-stack-handoff.md`. It is
retained to preserve the original orchestration idea across compaction. It is
not acceptance evidence or an executable queue; none of its downstream
current-backend leaves is active.

## Terminal outcome

Finish R3-G-04, then run the delivery loop continuously along only the
dependencies needed for:

1. accepted R3-G execution-pattern exit evidence;
2. accepted R4-G transactional semantic-mutation exit evidence; and
3. a committed D1 decision record answering the roadmap's six questions,
   selecting one permitted outcome, naming the evidence, and defining any
   newly authorized scope.

Do not activate C1, C2, or optional goal expansions before D1.

## Tentative serial packet sequence

| gate | bounded result | why it is on the dependency path |
| --- | --- | --- |
| R3-G-04 | exact two-event, same-origin `next-event` | accepted as `f4a64c1` + `5ce645d` |
| R3-G-05 | atomic explicit two-rule generic `RuleApplied` allowlist | active producer boundary before distinct/gapped events |
| R3-G-06 | typed `memoryWrite` and `memoryLoad` observation on one small IMP-like memory fixture | supplies distinct domain events and shared payloads |
| R3-G-07 | concrete trace reference with K-authored `next-event` and gap-allowing `eventually-after`, shared address, corpus witness | supplies the concrete ordered-subsequence result used downstream |
| R3-G-08 | bounded symbolic branch/status closure: sibling isolation plus honest `match`, exhaustive `no-match`, `unknown`, and `error` | closes required R3-G exit evidence |
| R4-G-01 | deterministic mutation candidates for `exact`, `each`, and coupled-tuple selection | establishes the mutation operator/candidate protocol |
| R4-G-02 | isolated exact/each single-rule mutants with canonical patches and ordinary-result kill | proves the single-rule mutation path |
| R4-G-03 | one atomic coupled two-rule mutant with all-or-none failures | proves coherent multi-rule mutation |
| R4-G-04 | isolated bounded runner and deterministic status/report boundary, including `invalid`, timeout/`unknown`, and `error` | supplies honest execution and score classification |
| R4-G-05 | integrated mutation-oracle exit: an unchanged-final-result mutant killed by an accepted execution-pattern witness | closes R4-G exit evidence |
| D1 | root-owned committed ADR-style decision with independent evidence review | terminal scope decision; no implementation leaf follows automatically |

The numbering after R3-G-04 is provisional until each packet is authored and
committed. A stop/split result may insert a narrower prerequisite, but it must
be a demonstrated dependency of the terminal outcome rather than a side leaf.

## Held work

Keep these inactive unless a required packet demonstrates that one is an
unavoidable prerequisite:

- streaming monitors and monitor optimization;
- alternatives, named-pattern product syntax, all-matches policy, coverage
  scheduling, cache work, and large-corpus expansion;
- backend/RPC trace compatibility, proofs, and exact product diagnostics;
- broad mutation operator families beyond exact, each, and coupled tuple;
- general `SemanticInput` expansion, independent Kore emission, C1, and C2;
- persistent changes to the external K checkout.

## Context and conflict policy

- One implementation writer at a time. Every writer starts from the previous
  accepted integration commit, never from an unintegrated worker branch.
- Root owns tasks, roadmaps, checkpoints, loop state, decisions, integration,
  and stop records. A worker owns one new task spine, its evidence directory,
  and one package script entry unless its packet says otherwise.
- A fresh read-only agent may probe or audit in parallel. It must not edit the
  active writer's paths or invent a downstream shared schema.
- Treat allowlist/observation, temporal witness/status, mutation
  candidate/patch, and runner/oracle reporting as four serial schema epochs.
- Freeze accepted fixtures. Downstream packets replay accepted work into their
  own ignored build trees instead of editing accepted sources or evidence.
- Each packet retains a three-substantive-full-oracle-cycle cap. Routine checks
  are zero-backend. Full-oracle work is limited to the changed leaf, serialized,
  resource-capped, and never recursively rebuilds the accepted ancestor chain.
  Reporting-only changes reproject a recorded successful raw run. Integrate
  only after scope audit, the packet command, `bun run check`, and
  `git diff --check` pass.

## D1 artifact boundary

“Written D1” means a durable committed record under `draft/decisions/`, not a
chat conclusion or a roadmap bullet. The record must:

- answer all six questions in the roadmap's D1 section;
- name the accepted R2-G, R3-G, and R4-G evidence and unresolved limitations;
- select exactly one permitted D1 outcome and explain rejected alternatives;
- state the precise scope newly authorized, if any, and what remains held; and
- avoid activating or implementing that new scope as part of D1 itself.
