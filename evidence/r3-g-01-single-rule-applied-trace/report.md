# R3-G-01A checkout-stable RuleApplied evidence

Status: pass on 19 August 2026 against K v7.1.337 at
`4a46d1231473b599c699160132fd6e76a5c46406`.

## Acceptance

Run from a checkout without pre-existing acceptance output:

```sh
bun run r3:g:rule-applied-trace
```

The replay compiles the task-owned, uninstrumented trace fixture through
ordinary official K, projects its post-CF definition through the sole
`KRuleAppliedTrace-v1` contract, and continues through unchanged lowering and
the pinned Haskell backend. The semantic packet remains frozen at three
substantive full-oracle cycles. This checkout-stability repair used two
substantive full-oracle cycles.

## Runtime truth and portable evidence

The real runtime event still contains the selected official rule's absolute,
run-local `Source` and the lineage derived from that exact source. Before
backend acceptance, Java independently validates exact equality of all five
origin fields: lineage, label, module, source, and location. The independently
compiled ordinary-source oracle uses those same raw values, and its two full
runtimes are compared byte-for-byte with the transformed runtimes.

Only after `apply`, `already-present`, and exact raw-payload validation does
the replay produce committed evidence. That representation uses
`repo://spine/rule-applied-trace/fixtures/p3-trace.k` as an explicit logical
source identity; it is not the raw official `Source`. The projection re-encodes
and re-hashes all primary-rule lineages, source-aware typed term metadata,
rule bodies/conditions/content/attributes,
whole-definition fingerprints, request/result fingerprints, canonical
operations, generated production/metadata fingerprints, the ordinary-source
oracle, and runtime payload. No raw checkout-derived digest is relabeled as a
portable digest.

## Result

- K structurally selected the one `bump-state` transition and authored the
  complete target, path, trace-cell name, fresh typed variable, typed list
  append, singleton event, origin constructor, all five payload placements,
  and `apply`/`already-present`/conflict decisions.
- The payload is one `RuleApplied` origin containing the selected rule lineage,
  label, module, source, and location. Java contains none of the fixture,
  constructor, list-label, cell, target, or payload-order selection literals.
  The replay rejects bare, suffixed, or prefixed `ruleApplied` and `ruleOrigin`
  Java string literals.
- Java resolved only exact projected generated-cell, production, sort, and
  subsort descriptors, validated typed term and provenance witness paths, and
  immutably rebuilt one rule. Lineage, provenance, attributes, conditions, and
  every original body node were preserved.
- Reprojection returned one `already-present` candidate. Independent host
  validation found exactly one equal update, performed zero further
  applications, and retained the same instrumented definition reference.
- The firing program ended at `<k> 1`, `<state> 2` with exactly one event; the
  non-firing integer ended at `<k> 1`, `<state> 1` with `.List`. Erasure matches
  both the uninstrumented trace fixture and accepted P3 program state.
- Both full runtimes match an independently compiled ordinary-source oracle.
  The fresh repeat has stable request/result fingerprints, full and focused
  normalized Kore, syntax Kore, macros, event payload, and both runtimes.
- Stale content/provenance, zero/duplicate targets, invalid paths,
  missing/ambiguous cell and constructor metadata, unknown constructors,
  incompatible sorts, variable collisions, conflicting updates, false
  `already-present`, unsupported bodies, and malformed exact results all fail
  closed with zero applications and no known backend artifacts.

## Boundary

This proves only one event and the two concrete paths. It does not prove
symbolic branch isolation or absence, backend-independent rule application, or
general event semantics. It adds no matcher, monitor, temporal language,
corpus result, symbolic path, multi-rule facility, or domain event. There was
no ambiguity requiring a split.

The recommended follow-on is the K-authored trace-configuration composition
packet, reusing this stable event/append contract without a second host
boundary.
