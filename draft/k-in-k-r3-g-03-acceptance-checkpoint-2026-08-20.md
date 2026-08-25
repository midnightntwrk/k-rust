# R3-G-03 acceptance checkpoint — 20 August 2026

Status: accepted and integrated. This checkpoint fixes the evidence boundary
before activating the first exact two-event matcher.

## Accepted composition

R3-G-03 is integrated as prototype `0a1a945` and acceptance-boundary repair
`6c88e2c`. The corresponding worker commits are `3a0b51f` and `3f65538`; the
final worker and integration trees are byte-identical. The earlier no-content
merge `90cea7f` keeps the original accepted R3-G-02A worker lineage reachable,
so replay's historical ancestry pins remain clone-stable.

Pinned `krun --pattern --output json` matched one exact
`RuleApplied(RuleOrigin)` at trace index zero. K bound the five typed origin
strings and the typed empty List tail. K also returned exact zero-argument
`#Bottom{GeneratedTopCell}` for the accepted empty trace and for a firing query
whose K pattern constrained the label to a known unequal value.

The host validated the official KAST v4 envelope, equality conjunction,
binding cardinality and sorts, exact generated completion-cell shapes,
canonical tokens, and `.List`. It compared all five raw fields with the
independent driver and runtime records before projecting the portable witness.
It did not parse pretty output, match a trace, search for an event, or turn a
malformed envelope into `no-match`.

## Root acceptance

The worker used one substantive full-oracle cycle. A worker-side adversarial
audit closed an unsafe acceptance-reuse mode, shallow completion validation,
and non-integral KAST-version acceptance before the prototype commit. Root's
independent audit then found two blockers: bare PATH-resolved `krun` invocation
and incomplete inner completion-cell validation. Repair `3f65538` pins the
resolved `krun` as the commit-bearing sibling of pinned `kompile`, invokes it
by absolute path, validates all three completion inner shapes, and expands the
zero-backend projector failure suite to 22 cases.

Root replayed exact repair commit `3f65538` from
`/home/sebdev20/Documents/git/workspaces/starstream-fv/k-in-k2-r3-g-03-root-replay`.
The replay regenerated the accepted composition, executed all six matcher
queries, reproduced committed evidence byte-for-byte, and passed:

```sh
bun run r3:g:rule-applied-head-match
bun run check
git diff --check
```

Repository checks were 10/10. External K remained exactly ` M pyk/uv.lock`.
Accepted evidence hashes are:

- results: `f80886548d4373cdff8ee73d182c89aab2856a6ae7d1059e08978f75d821595d`;
- report: `5bba00094746b226f33cd92d7164c88e12899b8319a629c60d319842df19d9ef`.

## Product-goal checkpoint and next leaf

The decisive new fact is that K, rather than a host parser, consumes accepted
branch-local event state and returns an exact typed provenance witness. The
next blocker is observed-event composition, not another transport seam or a
new event schema.

The accepted rule appends on every firing. Therefore `hold(bump) + bump` can
produce two events without changing the observer, configuration transform,
Java host, or external K. The unobserved `hold-value` rewrite occurs between
the two observed firings. Activate `R3-G-04` for an exact two-event pattern
whose event constructors are adjacent in the List and whose trace is
exhausted. This is a bounded `next-event` feasibility leaf over two occurrences
of one origin and the observed-event clock, not the semantic-transition clock.

Do not call it a general ordered subsequence: the events are intentionally the
same constructor and origin, and there is no intervening event. After this
leaf, introduce a separate atomic multi-rule producer/allowlist packet before
testing distinct-event order, an intervening-event gap, shared variables
across different payloads, domain events, symbolic paths, or a streaming
monitor.
