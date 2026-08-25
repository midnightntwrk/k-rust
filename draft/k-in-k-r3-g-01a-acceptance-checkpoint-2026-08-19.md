# R3-G-01A acceptance checkpoint — 19 August 2026

Status: accepted and integrated.

R3-G-01's three-cycle prototype is integrated as `249c540`; the checkout-stable
repair is integrated as `1ac7bc1`. The final tree exactly matches worker commit
`3e8e612` while preserving one clean repair commit after the imported prototype.

The first repair attempt passed in its worker checkout but failed root's fresh
detached replay at the portable request fingerprint. Independent audit found
two causes: primary rules were still ordered by raw source-derived lineage,
and typed-term production/attribute metadata had been hashed before source
normalization. It also rejected chained global replacement as insufficiently
fail-closed.

The final repair orders by portable lineage, normalizes typed metadata before
hashing, structurally rebuilds typed results/operations through unique official
descriptor mappings, and uses simultaneous non-cascading identity projection
with collision and residual checks. Raw runtime still validates the selected
official rule's exact absolute source and source-derived lineage across all
five event fields; committed evidence explicitly uses a repository-logical
projection only after that validation.

Acceptance passed:

- the worker's final second repair cycle;
- a fresh `/tmp` detached full replay with byte-identical evidence;
- a fresh workspace-aligned detached checkout running the full replay,
  `bun run check` (10/10), and `git diff --check` together; and
- a fresh read-only Sol audit of the hardened delta.

Evidence hashes are:

- results: `8a007ed2cce00517fcb0462b4f4bf7107abcf935c95e3f8cf861b3e609945519`;
- report: `31d1909b1cc16eda0db57a36962189edeea6d2cc56449c3d590bc6baeeab8213`.

The accepted capability is still deliberately small: one selected rule, one
typed list append, one `RuleApplied` event, and two concrete paths. It does not
prove symbolic branch isolation, backend-independent events, matching,
monitoring, multi-rule instrumentation, or domain-event semantics.

The next leaf is R3-G-02: keep event productions in ordinary source, remove
only the empty trace cell, author that configuration through one new pre-CF K
contract, and compose unchanged `KRuleAppliedTrace-v1` post-CF. Matching stays
on hold until that end-to-end composition is accepted.
