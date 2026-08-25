# R3-G-01 root audit checkpoint — 19 August 2026

Status: stopped and split; no R3-G-01 implementation is integrated.

Worker prototype `c4ad784` completed three substantive full-oracle cycles and
passed `bun run r3:g:rule-applied-trace` in its isolated worktree. The root
replayed that acceptance, ran the accumulated repository checks, compared the
generated and committed evidence byte-for-byte, reviewed semantic ownership,
and requested an independent read-only audit.

The semantic result is worth preserving: `KRuleAppliedTrace-v1` produced one
typed list-backed `RuleApplied` event for `bump-state`, exact five-field
provenance, firing/non-firing erasure, an ordinary-source runtime oracle,
apply/already-present idempotence, and 16 negative groups. K owns the complete
semantic term graph and Java remains a generic official-descriptor resolver.
The generic `KItem` compatibility rule is an official post-CF carrier rule,
not a fixture escape hatch.

Integration is blocked because official source provenance is an absolute
checkout path and participates in the rule lineage and further fingerprints.
The frozen results embed `/k-in-k2-r3-g-01/`; replaying after a fast-forward
under `/k-in-k2/` would change the source, lineage, request/result values,
ordinary-source oracle, and runtime event, then fail the evidence byte
comparison. A passing replay in the originating worktree is not sufficient
evidence of an integrable packet.

The audit also found a non-blocking enforcement gap: the replay's Java scan
catches `ruleApplied(` and `ruleOrigin(` string literals but not every bare or
prefixed form. Current Java contains no prohibited semantic-selection literal.

The R3-G-01 stop rule applies at three cycles. The implementation is preserved
on its worker branch and remains outside `master`. `R3-G-01A` is the only
active packet: make evidence checkout-stable while retaining exact run-local
source/lineage equality in the real event, harden the scan, and prove the
result from two distinct worktree roots. K-authored trace configuration stays
on hold.
