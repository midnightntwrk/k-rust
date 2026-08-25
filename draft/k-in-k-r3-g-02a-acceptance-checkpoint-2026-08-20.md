# R3-G-02A acceptance checkpoint — 20 August 2026

Status: accepted and integrated.

## Integrated result

The stopped R3-G-02 prototype is integrated as `8d657e5`, complete-clone and
failure-envelope repair as `daf4d60`, and checkout-stable raw-fingerprint
projection repair as `e5b5234`. They correspond to worker commits `478ea27`,
`bba487b`, and `1a3100f`. The activation base was `7c2e9c8`.

R3-G-02 used three substantive full-oracle cycles before it was stopped.
R3-G-02A then used its separate maximum of two repair cycles. The first repair
closed the two semantic audit blockers. Root's different-checkout replay found
that the new raw complete-clone digests were run-local and therefore could not
be copied into committed portable evidence. The second repair retained both
raw values in transient driver records, compared expected with installed and
fresh repeat with repeat before projection, and committed only the validation
facts plus independently rederived portable fingerprints.

## Accepted capability

`KTraceConfigurationAugmentation-v1` now owns exact apply/already-present/
conflict status over the complete typed trace-cell clone. Equality includes the
four-argument shell and metadata, both renamed name tokens with their original
sorts and attributes, the complete property subtree, the typed `.List : List`
initializer, and all node metadata. Java independently constructs the expected
clone from the declared template, name, and initializer and uses one complete
comparator for post-application and pass-2 validation.

Every configuration failure is validated against the exact schema, the closed
three-reason grammar, a canonical nonnegative count, and the reason/count
relationships before classification. Property-shape conflict, forced false
already-present, wrong schema, unknown reason, and negative count all fail at
their intended pre-CF boundaries with zero configuration applications, zero
post-CF calls, and filesystem-proven artifact absence.

The source configuration still contains only `k` and `state`. One pre-CF
operation clones the trace shell with the exact nullary list initializer,
official CF generates the trace cell, and unchanged `KRuleAppliedTrace-v1`
appends the same one provenance-bearing event. Firing/non-firing runtime,
erasure, ordinary-source, provenance, idempotence, repeat, and all unchanged
post-CF negative oracles pass.

## Root gate

An independent read-only Sol audit accepted the exact-shell and closed-failure
implementation, then separately accepted the cycle-2 projection-only repair.
Root's definitive replay used detached checkout
`/home/sebdev20/Documents/git/workspaces/starstream-fv/k-in-k2-r3-g-02a-root-replay3`
at worker revision `1a3100f` and passed:

```sh
bun run r3:g:trace-configuration
bun run check
git diff --check
```

The accumulated suite reported 10/10 tests. Committed evidence regenerated
byte-identically with SHA-256:

- results: `de653bc22adfff3fd9158155a2ae385a9019bf8231f98e5570a5cf126bbfb960`;
- report: `88c678b029071d630b5b1205efdc695e5cc014bcadd55aa4b1c23a3537bebde0`.

External K remained read-only at v7.1.337 / `4a46d123...`, with only the
pre-existing ` M pyk/uv.lock` status.

## Next leaf

The composition dependency is closed. The next packet may establish one
K-native concrete head match over the accepted single-event `RuleApplied`
trace, returning the exact origin as a witness and distinguishing the empty
trace. It must not add a domain event, another instrumented rule, temporal
composition, a monitor, corpus aggregation, or symbolic exploration.
