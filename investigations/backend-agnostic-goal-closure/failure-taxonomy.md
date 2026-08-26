# Closed failure disposition taxonomy v1

`failure-taxonomy.json`, validated by `failure-taxonomy.schema.json`, is the
single source of truth for every admitted `(stage, classification, context,
scope)` placement, retryability rule, evidence policy, and artifact-level
consequence. Its `taxonomyId` is the `k-in-k/failure-taxonomy/v1` digest of the
complete object with `taxonomyId` omitted. Entries and placements are
canonically ordered and have no fallback.

A failure requires distinct `stage`, `classification`, `context`, and `scope`
fields. BAG-09's oracle wrapper additionally uses `sourceSide`; it is not an
alias for failure context. A failure copied from a pattern result into a corpus
result retains `pattern-path` or `pattern-test` context.

The closed v1 contexts are observation installation, mutation discovery,
candidate generation, pattern path, pattern test, corpus shared setup,
baseline validation, baseline execution, baseline oracle gate, mutant
validation, mutant execution, oracle comparison, campaign, and report
publication. Every failure-bearing schema pointer references an exact context
definition. The portable verifier inventories those pointers and exhaustively
proves equality between the finite schema-legal placement set and taxonomy
placements in both directions. Broad raw references to `common.failure` are
forbidden.

`details` is diagnostic-only. Empty details are valid, arbitrary human or
backend diagnostics may appear there, and details affect containing content
identity, but no status, score, retryability, gate, classification, or
disposition may depend on them. Semantic evidence is instead a canonical
`semanticEvidence` array of BAG-08 artifact keys. It is empty for every
ordinary failure.

`lowering/lowering-nontermination` is the sole v1 evidence-bearing failure. It
requires exactly one `lowering-proof-check-receipt` key. The registered
`portable-finite-cycle-checker` version 1 resolves the proof and receipt,
through the campaign's manifest-declared BAG-08 keys and bundled artifact
catalog bytes, recomputes their identities and input bindings, and checks a nondegenerate
closed cycle against the independently frozen toy relation. A bare label,
digest, boolean, edge list, receipt verdict, or proof hidden in `details` is
not authority. The toy checker proves only this portable protocol; real
lowering nontermination remains a future native Rust proof obligation.

Semantic crashes remain typed BAG-09 terminal operands and never taxonomy
entries. `oracle/baseline-mismatch` is reachable only at the baseline-oracle
gate and derives `baseline-oracle-failed`. `oracle/incomparable-result` is
reachable only at oracle comparison and can never derive a kill. Bounded
lowering time/resource stops remain timeout/unknown, never presumed
nontermination.

The mandatory post-BAG-16 pointer inventory and bidirectional reachability
rerun is complete. The successor surface adds exactly five infrastructure
`pattern-test`/`test` placements with `error` consequence, and the complete 94
schema-reachable placements equal the active taxonomy placements across all 15
contexts. Historical v1 taxonomy and schema bytes remain unchanged.
