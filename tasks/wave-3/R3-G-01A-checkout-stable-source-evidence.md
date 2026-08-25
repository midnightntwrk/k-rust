# R3-G-01A: checkout-stable RuleApplied source evidence

Status: accepted and integrated on 19 August 2026. Activation commit `af2dbf1`
was the accepted base; stopped prototype `c4ad784` was imported as `249c540`,
and the final checkout-stability repair was integrated as `1ac7bc1`.

## Why this packet exists

`R3-G-01` reached its three-cycle stop boundary with a semantically passing
`KRuleAppliedTrace-v1` implementation. Root and an independent read-only audit
then found one integration blocker: the committed evidence contains the
worker worktree's absolute fixture path. Official source provenance feeds the
stable rule lineage, content/request/result fingerprints, the generated
ordinary-source oracle, and the runtime event. Moving the same commit to the
master worktree therefore changes more than the visible source string and
causes the required evidence byte comparison to fail.

Preserve the stopped result; do not count another `R3-G-01` oracle cycle. This
repair packet begins a new, narrower cycle whose only product change is making
the accepted evidence reproducible from distinct checkout roots without
weakening exact runtime provenance.

## Objective

Make the imported one-event implementation pass unchanged acceptance from two
different absolute Git worktree roots. Each execution must still place the
selected official rule's exact run-local source and lineage into its actual
`RuleApplied` event and compare all five payload fields against that selected
rule. The committed evidence must use an explicit checkout-stable
representation for run-local provenance and every value derived from it.

Also close the audit's small enforcement gap by making the Java literal scan
reject bare or prefixed `ruleApplied` and `ruleOrigin` string literals, not
only forms followed by `(`.

This packet does not add a capability, event, rule, contract, host boundary,
configuration transform, matcher, monitor, or symbolic path.

## Starting inputs

- activation base descended from `6d7dcd2`;
- stopped prototype commit `c4ad784`, imported by root onto the repair branch;
- `tasks/wave-3/R3-G-01-single-rule-applied-trace.md` as the unchanged semantic
  contract and three-cycle record;
- the root audit captured in
  `draft/k-in-k-r3-g-01-audit-checkpoint-2026-08-19.md`;
- accepted R2-G-07 and its pinned official-K inputs; and
- K v7.1.337 at `4a46d1231473b599c699160132fd6e76a5c46406`.

External K remains read-only with the expected exact status ` M pyk/uv.lock`.

## Required invariant split

Keep these two identities distinct and explicit:

1. **Runtime truth:** the host projects the official selected rule's actual
   source, K copies that exact value and the source-derived lineage into the
   event, and the host/runtime oracle validates exact equality before backend
   acceptance.
2. **Portable evidence:** only after those checks pass, the replay emits a
   documented logical source identity and canonical representations for every
   checkout-derived value. A second checkout must regenerate byte-identical
   committed `results.json` and `report.md`.

Canonical evidence must not pretend that a logical source token was the raw
official `Source`. Record the mapping/method and the fact that raw equality was
validated. Do not merely replace the visible path while leaving path-derived
lineage, content, definition, request/result, operation, oracle, or payload
digests unstable. Do not discard the existing same-checkout repeat checks for
request/result fingerprints and runtimes.

The implementation may choose the smallest auditable mechanism: a portable
evidence projection after validation, a canonical identity used only for
evidence fingerprints, or another solution that maintains the invariant
split. If the solution changes the runtime payload away from the selected
official rule's exact source/lineage, it fails this packet.

## Ownership and compatibility

The repair worker may modify only:

- `spine/rule-applied-trace/**`;
- `evidence/r3-g-01-single-rule-applied-trace/**`; and
- the existing `r3:g:rule-applied-trace` entry in `package.json` if strictly
  necessary (no new root script entry is expected).

All tasks, roadmaps, checkpoints, loop records, accepted spines/evidence,
P1/P2/P3 fixtures, lockfiles, and external K are read-only. Raw output remains
under the ignored rule-applied-trace build tree.

Retain `KRuleAppliedTrace-v1` as the sole new contract and preserve the
prototype's semantic ownership:

- K owns structural selection, target/path/status, the fresh typed variable,
  list/event/origin constructors, payload order, and all witness paths.
- Java generically resolves exact official descriptors, validates the typed
  graph and provenance, and immutably rebuilds one rule.
- The generic post-CF `KItem` carrier rule may remain; it must not gain
  fixture-specific exceptions.

## Acceptance

Worker acceptance, from a clean repair worktree with no pre-existing output:

```sh
bun run r3:g:rule-applied-trace
bun run check
git diff --check
```

The replay must regenerate and byte-compare both committed evidence files,
retain all positive/idempotence/runtime/erasure/ordinary-source/repeat oracles
and all 16 negative groups, and fail closed on every previously pinned input.
It must additionally enforce the broader Java event-constructor literal scan.

Root acceptance is intentionally independent and mandatory: after the worker
returns a commit, root creates a fresh detached worktree at a different
absolute path, with no copied build output, and runs the same three commands.
Both evidence comparisons must pass. Passing only in the worker path is a
block, not a repair acceptance.

Record the repair packet's own substantive full-oracle cycle count separately
from R3-G-01's frozen count of three. The worker gets at most two repair
cycles; a path-stability failure after the second requires another stop/split.

## Return contract

Return one clean repair commit after the imported prototype commit. Report:

- activation, imported prototype, and actual starting revisions;
- repair verdict and repair-cycle count;
- the exact raw-runtime versus portable-evidence invariant;
- the canonicalization/mapping and all path-derived fields it covers;
- unchanged semantic contract, K/Java ownership, event payload validation,
  idempotence, runtime/erasure/source oracles, and negatives;
- literal-scan coverage;
- commands, evidence hashes, and remaining limitations; and
- whether the next packet can safely compose K-authored trace configuration.

Do not claim integration or cross-checkout acceptance; only root can make that
decision after the second-path replay.
