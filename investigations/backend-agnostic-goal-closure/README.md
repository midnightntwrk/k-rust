# Backend-agnostic goal closure

Status: active portable investigation package; the refreshed BAG-11 witness-order and complete-denotation repairs and BAG-12 typed-oracle and inline-expectation repairs are independently accepted.
BAG-14 per-attempt cache implementation and evidence were independently accepted after two finding-driven repair rounds, 26 August 2026.
BAG-15 operation receipts, result wrappers, recursive version provenance, and campaign receipt DAG evidence were independently accepted after two finding-driven implementation repair rounds, 26 August 2026.
BAG-16 collection-aware execution, pattern evaluation, corpus folding, and
successor version provenance were independently accepted after finding-driven
contract and implementation repair rounds, 26 August 2026. The accepted
`bag16.py` SHA-256 is
`0fea820d9ad7c082404d788bca2589ff2575316bf13dcc436628c8fb4c6f1e33`.
They make no native branch-discovery or execution claim.
The mandatory post-BAG-16 BAG-10 taxonomy/schema placement rerun was
independently accepted after closing the successor schema's broad failure
references. Its active 94-placement surface is exact in both directions while
the historical v1 taxonomy and schemas remain byte-frozen.

This package records the semantic work that can be completed before K-in-K
moves to its Rust-based execution stack. It deliberately does not preserve,
repair, or wrap the stopped Java/Haskell execution path.

All BAG-02 through BAG-16 task packets are explicit completion authorities.
In particular, BAG-05 closes the single `executionProfileDigest` identity and
`execution-profile` catalog role, while BAG-06 closes bounded agreement as
`survived` rather than equivalence. A future typed equivalence proof system,
additional operator families, subsumption/bounded-equivalence analysis, and
general equivalent-mutant detection retain separate product/scope decisions.

The package has three purposes:

1. separate portable conclusions from evidence that only proved them on the
   old pinned stack;
2. freeze backend-neutral conformance inputs and expected results before a new
   implementation can accidentally define the semantics by its behavior; and
3. identify the first point at which further evidence genuinely needs the
   Rust stack.

The normative portable contracts are in [contracts.md](contracts.md). The
machine-readable inventory is [evidence-inventory.json](evidence-inventory.json),
the closed failure vocabulary is [failure-taxonomy.md](failure-taxonomy.md),
and the future implementation order is [rust-stack-handoff.md](rust-stack-handoff.md).
Schemas and golden vectors are under `schemas/` and `vectors/`.
The typed patch oracle is `vectors/patch-application-vectors.json`; the
string-path data under `historicalRetiredStackShorthand` is retained solely to
identify bounded retired-stack evidence and is not an interchange format.

Run the zero-backend checks with:

```sh
python3 investigations/backend-agnostic-goal-closure/verify.py
```

That command reads repository files and uses the installed official Draft
2020-12 `jsonschema` validator in addition to the Python standard library. It
does not invoke K, Java, a compiler backend, a solver, or a Rust executor.

## Claim boundary

The verifier may check closed schemas, canonical encodings and digests,
referential integrity, declarative patch algebra, atomic failure outputs, and
status/score invariants. It also acts as a small trusted oracle over the
finite traces supplied in this package: it searches those vectors, derives
witnesses, and concludes absence only when their explicit finite-completeness
flags permit it. That oracle defines conformance expectations; it is not a
claim about traces produced by a backend. The verifier must not:

- discover semantic sites or interpret a K mutation operator;
- solve K-term constraints or infer symbolic feasibility;
- infer exhaustive absence from a backend trace merely because no recorded
  event matched;
- instrument, lower, execute, or prove erasure/conservativity; or
- translate debugger/backend logs into product events.

Passing this package means the portable inputs and expectations are internally
consistent. It is not evidence that a backend has implemented them. The
Rust-stack differential gates in the handoff are the future execution proof.

The BAG-12 repair resolves its corpus, observation vocabulary, typed oracle graph, terminal/crash provenance, and finite authorities only through the active catalog.
It publishes end-to-end agree/distinguish evidence for every built-in pair, positive inline expectations for all nine built-in projection/comparator pairs, both incomparable orientations, incomplete cases, and 36 one-to-one executable adversaries.
These are repair-gate results, not an acceptance claim.

The BAG-14 implementation replaces suite-level cache identity with cycle-free execution-attempt and oracle-evaluation request keys, immutable per-attempt records, schedule-specific campaign invocations, and schedule-specific mutation reports.
Its wholly bundled counter derivative proves exact first-kill/full prefix reuse, an absent first-kill suffix, later full suffix completion, exact bounded and diagnostic-only classifications, full same-key conflict quarantine, and byte-identical uncached, partial-hit, and full-hit folds.
The finite-vector rows hash only reviewed inputs and independently derive terminal/result outputs; every oracle operand has one explicit finite producer row.
This remains portable conformance evidence, not native production or cache-store evidence.

The BAG-15 implementation adds one generic `operation-receipt` family over seven closed operations and one cycle-free result-wrapper role per operation.
Every complete receipt publishes exactly one wrapper, including bounded and semantic-failure completions; only a failed producer publishes no wrapper or semantic terminal.
Execution wrappers preserve the exact BAG-14 key digest separately from the generic invocation digest and contain the exact terminal plus ordered produced artifacts.
Operand, admission, comparison, derivation, and publication edges consume both the preceding wrapper and its receipt, and the full and first-kill report closures are checked as globally acyclic DAGs.
The publication invocation contains no expected report bytes or digest, and a report may name its derivation receipt but never its own publication receipt.
The exact recursive schema/operation registry uses raw schema-byte SHA-256 values and rejects missing, surplus, duplicate, or altered entries.
The wholly bundled derivative proves portable finite production only; native adapter execution remains Rust-stack work.

## Artifact availability and current replay recipes

`artifact-role-specs.json` freezes the shared role, media, schema, domain, and executable semantic-projection registry.
`fixtures/artifact-catalog.json` supplies exact byte hashes and explicit resolver/availability metadata.
The bundled material is deliberately small synthetic conformance input.
`artifact://` entries are known, reviewed external pins for the future Rust artifact resolver; their locator spelling is not treated as local storage.

`fixtures/bag14-cache-artifact-catalog.json` is the authoritative resolver snapshot for BAG-14 evidence and is bound by `vectors/cache-semantics-vectors.json.artifactCatalogDigest`.
It is deliberately separate from BAG-12's active mutation catalog so a finite cache positive does not relabel historical `external-required` material as bundled.
Cache location, lookup provenance, hit/miss state, and current resolver availability are supplemental and absent from semantic cache-record, request-key, invocation, and report identities.

`fixtures/bag15-replay-artifact-catalog.json` is the separate wholly bundled BAG-15 resolver snapshot and is bound by `vectors/replay-provenance-vectors.json.artifactCatalogDigest`.
It contains derivative cache records whose accepted BAG-14 request keys, terminals, and produced artifacts are unchanged while their production-evidence arm names the exact BAG-15 receipt and operation-specific result wrapper.

`fixtures/bag16-artifact-role-specs.json` and
`fixtures/bag16-artifact-catalog.json` are the successor resolver authority for
`vectors/bag16-branch-collection-vectors.json`. The v2 dispatcher preserves exact
historical schema bytes, admits an explicit legacy-no-version arm only where a
frozen structured value lacks `schemaVersion`, and selects every other arm by
its exact top-level integer. `portable-closure-root/v1` embeds this authority,
the exact cache projection, and the recursive replay-version-registry/v2; it is
not itself cataloged or produced by another receipt.

None of the four current replay recipes is materially self-contained:
`replay-manifest.json`, `write-only-replay-manifest.json`,
`mutation-replay-manifest.json`, and `mutation-pattern-replay-manifest.json`
all have referential closure but retain at least one `external-required`
structured input. Their exact derived status is in
`fixtures/replay-closure.json`. They are frozen recipes, not locally executable
bundles, and all explicitly report execution conformance as `not-proven`.

Execution-pattern roots are deliberately split into opaque `pattern-source`, structured normalized `pattern-plan`, and structured named `pattern-query` keys.
Replay match steps and every result/corpus/mutation consumer bind the exact catalog-resolved triple.
Corpus and mutation selections preserve oracle order and repeated query roots.
Query-coupled execution-attempt keys bind the exact selected triple and search policy; oracle-evaluation keys bind the exact declaration and ordered semantic inputs.
There is no suite-level flattened cache root.
Plan variable declaration order is retained in witnesses, and side-condition table keys hash only the declared input subset, including the valid empty constant interface.
`pattern-plan.schema.json` is a finite conformance format, not K source or a Rust compiler IR; native K compiler and solver correctness remain future Rust-stack proof.

## Closure criteria

Backend-agnostic investigation is complete only when all of the following are
true together:

1. every MVP acceptance clause and material architecture/scope claim in both
   goal specifications has an exact source citation, positive derivation,
   permanent adversary, and exactly one of the six dispositions in
   `completion-checklist.json`;
2. identity, definition, operator, patch, observation, event, pattern,
   corpus, mutation, diff, replay, failure, and scoring boundaries have closed
   schemas or normative algorithms and at least one positive fixture;
3. golden vectors cover positive, negative, uncertain, atomic-failure, and
   deterministic-order cases across at least two structurally different
   semantic families;
4. the verifier recomputes all normative IDs and cross-references, executes the
   finite-trace denotation and declarative patch algebra, derives aggregation
   and scores, and rejects adversarial contradictions;
5. the evidence inventory includes every accepted or boundary-setting W1,
   R2-G, R3-G, and terminal-stop artifact relevant to the two goals;
6. D1, the roadmap, this package, and the Rust packet ordering agree about the
   superseding stack transition and do not claim that K was compared with a
   conventional AST library; and
7. the live cycle-free audit subject matches `subjectPackageDigest`; its root
   includes the normalized package inventory and content hashes, exact
   requirement-ledger digest, verifier digest, and package version while the
   manifest and audit record remain outside the root; and
8. three independent audits of the exact same subject accept execution/
   observation/query/corpus, mutation/patch/oracle/cache/receipt/campaign, and
   completion/D1/roadmap/handoff with no pending findings.

The verifier enforces the machine-checkable subset. The final completion audit
records the requirement-to-evidence review for the prose and scope criteria.
The only terminal dispositions are `portable-closed`,
`portable-closed-rust-proof-pending`, `retired-stack-bounded`,
`product-decision-held`, `product-decision-required`, and
`out-of-scope-by-recorded-decision`. A Rust-open entry names the exact native
fact and why finite backend-neutral evidence cannot establish it. Changing any
normative package file changes the live subject root and invalidates every
earlier audit binding.

## Versioning

The package is version `backend-agnostic-k-in-k-v1`. A semantic change to a
closed enum, canonicalization rule, outcome rule, patch conflict rule, or
golden expected result requires a new package version. Adding a vector that
does not change existing meanings is a compatible extension.
