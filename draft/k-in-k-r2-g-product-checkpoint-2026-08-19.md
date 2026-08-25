# R2-G product checkpoint — 19 August 2026

Status: accepted checkpoint after R2-G-01 through R2-G-07. This is the
product-goal check required by the packet delivery loop at the boundary from
observation state to the first trace-backed execution event.

## Accepted spine

| leaf | integrated commit | shared contract | demonstrated result |
| --- | --- | --- | --- |
| R2-G-01 | `085b86b` | `KDefinitionTransport-v1` | lossless typed projection, K structural selection, identity/provenance validation |
| R2-G-02 | `c1605d2` | `KDefinitionPatch-v1` | one K-proposed input-relative edit, trusted-small application, official lowering/runtime |
| R2-G-03 | `daca204` | `KDefinitionPatch-v2` | canonical two-rule transaction, original-input validation, all-or-none application |

R2-G-04 integrated as `39c514d` with no production contract. It classified the
pin's pre-CF midpoint and preserved executable negative/API evidence plus both
post-CF identity and ordinary-source observation controls.

R2-G-05 integrated as `a720a4e` with experimental
`OfficialConfigurationTransformHook-v0`. A temporary exact-source overlay
proves the missing hook can compose with the accepted post-CF adapter and
official CF generation without mutating the external K checkout/install.

R2-G-06 integrated as `985d8fa` with
`KConfigurationAugmentation-v1`. K now owns the branch-local observation-cell
authoring decision and idempotence classification; official K still owns
configuration parsing, validation, generation, lowering, and execution.

R2-G-07 integrated as `71379e4` with `KRuleObservation-v1`. K structurally
selects P3's coupled `bump`/state transition and declares the root insertion,
generated observation cell, and `0 => 1` update. Firing and non-firing programs
erase exactly to the configuration-only runtime; a second K pass is
`already-present`. Nine semantic negatives plus malformed/noncanonical result
tests fail closed before backend construction.

R2-G-02 was the first complete prepare/delegate/review/integrate loop. One Sol
worker used an isolated worktree, required no ownership expansion, passed
three full oracle cycles, and returned one task-owned commit. The root reviewed
the diff and independently replayed the exact task command before integration.
R2-G-03 repeated that loop in one worker oracle cycle; the root separately
replayed the nested regression, transaction compilation, runtime, negative
atomicity cases, source hashes, and all repository tests before integration.

## Product-goal assessment

Semantic mutation testing now has its exact single-site operator path:

```text
typed definition -> K structural operator -> canonical patch
  -> precondition validation -> official immutable edit -> compile/execute
```

Its coupled-atomicity prerequisite is now met. More patch operators, synthetic
terms, and overlap algebra are not the next shared-product dependency.

Execution semantic-pattern matching now has conservative branch-local state
and a one-rule atomic observation update. Its next blocker is not another
transport seam: it is demonstrating an inspectable typed `RuleApplied` event
in list-backed trace state. Additional patch operators do not unblock it.

## Next decision

R2-G-04 returned `pin-private-seam-needs-hook`. The exact typed midpoint is a
private local `Definition` containing official parsed `Configuration` values;
the existing protected method sees bubbles before it and generated sentences
after it. The post-CF adapter is healthy, ordinary-source observation fallback
works, and the public generator is usable when given the typed input, so there
is no evidence that observation state itself needs redesign.

Activate `R3-G-01` for one trace-backed `RuleApplied` event on the same
transition. A task-owned ordinary-source fixture declares the event syntax and
empty list trace, keeping the sole new contract at the proven post-CF adapter.
K must author the event term, stable rule identity/provenance payload, trace
cell insertion, and append update. Java remains a generic typed-term resolver
and immutable rebuilder.

The firing program must contain exactly one event and the non-firing program an
empty trace; both erase to the accepted program state. Reapplication must be
`already-present`. Keep K-authored trace configuration, domain events,
multi-rule instrumentation, matching, symbolic branching, and corpus reporting
out until this reference event is accepted.
