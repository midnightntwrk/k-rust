# Dependency-ordered Rust-stack handoff

Status: portable capability handoff, 22 August 2026. This document constrains
observable semantics and evidence gates. It does not prescribe Rust crates,
process topology, internal data structures, ownership patterns, or a temporary
compatibility layer for the retired stack.

## Entry conditions

Before implementation starts, the Rust effort should consume this package as
an immutable v1 conformance input and run `verify.py`. The old R3-G-05 branch
and cycle outputs remain terminal failure provenance; they are not a codebase,
cache, or accepted result to port.

The new stack must expose a native structured boundary. A protocol that embeds
the complete definition and metadata into a textual K program and reparses it
repeats the stopped scalability risk. Every full-definition boundary needs a
measured size, allocation/peak-memory record, and explicit limit. A resource
failure must leave no partial accepted artifact.

## Packet order

### RS-01 — semantic identity and structured ingress

Required capability:

- enumerate the real supported K module/sentence/term/declaration/signature
  forms in the Rust IR and reject every unsupported or lossy native form;
- map the declared supported parsed-K/native-IR mutation and observation
  surface injectively into `portable-mutation-semantic-slice-v1`, including
  typed modules, sentences, terms, conditions, attributes, and
  source/generated provenance;
- derive portable `symbolId` from fully qualified native production identity
  and validate native declaration, arity, argument/result sort, and subsort
  obligations rather than treating local registry consistency as native proof;
- deterministic ordered/unordered collection semantics;
- v1 lineage/content/body/transformation identity domains, including
  destination-anchor identity for generated insertions; and
- one `executionProfileDigest` root for the complete execution-engine
  configuration, cataloged as `execution-profile` and kept distinct from
  compatibility, solver, options, and bounds identities; and
- a portable adapter to the schema fixtures without using pretty text as the
  semantic value or silently collapsing repeated/ordered native attributes.

Differential gates:

- every identity and canonicalization vector;
- the historical Peano/P3 transport identities plus the portable memory,
  counter, and generated-provenance definition fixtures;
- checkout relocation and duplicate-label cases; and
- bounded memory evidence for ingesting a representative full definition.

This packet does not instrument or mutate definitions.

### RS-02 — generic patch and atomic transaction boundary

Depends on RS-01. Required capability:

- typed original-relative paths or equivalently precise node identities;
- closed edit operations and deterministic insertion positions;
- immutable-baseline-seeded symbol signatures, sentence/path/operand variable
  scopes, Bool conditions, outer-sort preservation, and canonical attributes;
- destination module/path agreement and collision-free cross-module generated
  lineage for equal-side/equal-ordinal insertions;
- all preconditions validated against one immutable original;
- duplicate and ancestor/descendant overlap rejection;
- disjoint same-sentence and distinct-sentence atomic commit; and
- canonical patch/candidate/instance/mutant digests.

Differential gates:

- replay the accepted R2-G-02/R2-G-03 vectors through the Rust representation;
- run every patch case, including operations that lack old-stack proof;
- prove failures expose no output and zero applications; and
- repeat after permuting unordered transport collections.

Portable patch success proves only `applied-and-locally-well-formed`; native
IR/type validation remains `rust-proof-pending`. The existing campaign
`validation.outcome: valid` is report-contract data until BAG-15 supplies
native receipts.

This packet applies supplied patches. It does not discover mutation sites.

### RS-03 — conservative observation and atomic producer boundary

Depends on RS-01 and RS-02. Required capability:

- branch-local observation state;
- exact `lineage`, `label`, `attribute`, and declarative `structural-term`
  selections with complete definition-order results and closed cardinality;
- payload paths that resolve against every selected semantic sentence with the
  declared term sorts;
- semantic-site templates resolved for every selected lineage, with concrete
  event site IDs derived from the actual emitting lineage;
- atomic all-or-none installation across multiple selected transitions;
- generic `RuleApplied` plus fixed multi-event ordering; and
- an explicit supported transition-rule profile with fail-closed rejection.

Differential gates:

- observation selection/emission vectors;
- disabled-observer identity and concrete firing/non-firing erasure;
- program configuration, predicate, branch topology, and terminal-result
  erasure on a bounded branching fixture; and
- one two-rule allowlist success plus stale/unsupported-member atomic failure.

The portable `structural-term` subset is not arbitrary K matching. K-authored
observers with variables, recursive patterns, side conditions, negation, user
functions, or joins remain opaque digest-pinned artifacts. Their discovery
must run and be differentially checked in the Rust stack; native code may not
approximate them or route them through the declarative selector.

This is the first packet that closes the semantic capability R3-G-05 never
proved. It must be implemented natively; no sixth old-stack cycle is relevant.

### RS-04 — typed domain events and concrete occurrence semantics

Depends on RS-03. Required capability:

- K-facing `memoryWrite(Address, Value, Origin)` and
  `memoryLoad(Address, Value, Origin)` on a small memory fixture, mapped to
  interchange payload `[Address, Value]` plus the structured `origin` field;
- occurrence scanning anywhere in a branch-local event sequence;
- resolution of the exact constructor-canonical event-vocabulary digest;
- the closed flat nonrecursive DNF `pattern-plan` interchange, including
  single, ordered alternative, `next-event`, and `eventually-after` arms;
- complete per-arm typed bind/use checking, side conditions, and canonical
  witnesses that always carry `armOrdinal`, including zero; and
- structured `match`, exhaustive concrete `no-match`, and input `error`.

Differential gates:

- all complete concrete execution-pattern vectors, including prefix/suffix,
  gap, reverse, mismatch, overlap, and earliest witness cases;
- raw provenance to portable logical-source validation;
- trace-reference results versus the frozen expected results; and
- independent complete-denotation agreement with the portable fixture oracle,
  including omitted/extra/reordered witness rejection; and
- baseline/instrumented erasure for each concrete program.

The native K query compiler is a separate gate. Its receipt must bind the
exact `pattern-source`, normalized `pattern-plan`, entry module/exported name,
`pattern-compiler-profile` and version, and diagnostics. It must reproduce the
portable plan/query digests, reject a receipt for another source or plan, and
remain `not-proven` until K compilation and differential execution evidence
exists. Schema validation or a Python-built plan is not compiler proof.

The accepted R3-G-03/G-04 results are regression vectors, not sufficient exit
evidence: the Rust result must also cover distinct domain events and gaps.

### RS-05 — symbolic branching, constraints, and honest stops

Depends on RS-04 and the Rust executor/solver interfaces. Required capability:

- branch-local monitor/trace cloning and sibling isolation;
- complete symbolic bindings and path predicates on the declared supported
  portable surface, with unsupported or lossy native forms rejected;
- stable replay keys independent of worker scheduling;
- explicit exhaustive-finite evidence; and
- depth/time/branch/result/resource/solver stop classification.

Differential gates:

- sibling branches never combine;
- shared symbolic payload witness;
- finite absence `no-match`, bounded absence `unknown`, and malformed result
  `error`;
- aggregation truth table, including match over a truncated sibling; and
- replay of each witness from recorded inputs/options.

Only this packet can prove symbolic feasibility, branch isolation, and honest
absence for the new stack.

### RS-06 — mutation discovery and candidate protocol

Depends on RS-01 and RS-02; it may run in parallel with RS-04/RS-05 only after
the shared identity and patch schemas are frozen. Required capability:

- operator/site/instance/mutant separation;
- K-owned exact, each, tuple-each, and all-matches discovery;
- canonical site/tuple/candidate ordering, symmetric deduplication, and origin
  retention;
- positive candidate caps and incomplete-generation status;
- report/operator identity, policy, tuple arity/count, and cap correspondence;
- closed patch-template role interfaces and edit-to-source receipts, including
  exact tuple bindings and target/anchor authorization;
- unique manifest-ordered test plans; and
- deterministic patches from supplied semantic bindings.

Differential gates:

- every mutation selection vector;
- repeated and permuted-input candidate IDs/reports;
- missing/reordered/cross-origin edit receipts and same-lineage/different-path
  site identity;
- zero/one/excessive exact cardinality;
- coupled tuples supplied by K rather than a host Cartesian product; and
- two structurally different fixture families before claiming generality.

### RS-07 — isolated mutation execution, reporting, and cross-goal oracle

Depends on RS-04 and RS-06. RS-05 is an additional gate only for campaigns
that select symbolic tests or symbolic pattern oracles; concrete ordinary-result
and trace-pattern campaigns must not wait for symbolic closure. Required
capability:

- baseline gate, isolated mutant validation/compilation/execution, and resource
  limits;
- killed/survived/invalid/timeout/unknown/error separation;
- bounded complete agreement reported only as `survived`, with no equivalence
  claim unless a future version supplies a typed, scoped, checkable proof
  system;
- proven lowering nontermination versus lowering time/resource exhaustion;
- first-kill and full scheduling with identical classification;
- deterministic structural diffs, reports, mutation-specific replay manifests,
  resolved pattern witnesses, and score denominator; and
- execution-pattern results as mutation oracles;
- one ordered `oracle-declaration` per manifest test slot, with exact
  invocation/profile/bounds roots and no global oracle-definition join;
- kind-compatible typed operand production for exit-stop, final-result,
  concrete-output, reachability, execution-pattern, and structured-predicate;
- separate self-identified comparison and baseline-gate results, with every
  normalized value digest and outer side/failure relation rederived;
- strict semantic-output channel media types, byte hashes, UTF-8 decoding, and
  newline rules; finite reachability structural matching with optional exact
  predicate-query side conditions; and exact predicate input projections;
- a BAG-15 production receipt for each native-produced operand and a distinct
  matching `oracle-evaluator-conformance: conformant` authority for each
  K-authored projection, comparison, reachability query, or predicate used in
  a decision;
- typed normal/stuck/semantic-crash terminal results whose crash identity is
  derived from the pinned execution profile, normalized terminal
  configuration, and closed object-language classification rather than host
  exceptions; and
- distinct baseline admission and ordered baseline/mutant comparison
  reporting, including both crash policies and exact-source absent operands.

Differential gates:

- all mutation campaign and cross-feature vectors;
- one ordinary-result kill;
- one invalid mutant excluded rather than killed;
- timeout/unknown excluded rather than survived;
- complete/error/baseline campaign failure-state consistency and exact test
  plan scheduling;
- one atomic two-edit mutant counted once; and
- the unchanged-final-result mutant killed only by its pattern witness;
- a well-formed semantic crash path with and without a prior pattern witness;
  and
- symmetric mixed/different crash comparisons under both policies, with
  backend or worker failure on either side remaining `error`;
- agree and distinguish for every registered built-in pair, strict-output byte
  and newline cases, reached/exhaustive-not-reached/unknown reachability, and
  true/false/missing-row predicate cases; and
- rejection of every mandatory BAG-12 drift adversary after all enclosing
  self-IDs are refreshed, including declaration/result/query/profile drift and
  production receipts misused as evaluator conformance.

### RS-08 — streaming monitor optimization (held)

Depends on accepted RS-05. It is not needed to establish v1 product semantics.
If activated, every bounded finite execution vector must produce the same
outcome, canonical witness, bindings, and predicate under the trace reference
and streaming monitor. Performance evidence must justify activation.

## Evidence states at handoff

| capability | portable meaning resolved | old-stack bounded evidence | needs Rust proof |
| --- | --- | --- | --- |
| identity/fingerprint separation | yes | R2-G-01 | native derivation and ingress |
| one original-relative edit | yes | R2-G-02 | general path/value representation |
| two distinct-rule atomic edits | yes | R2-G-03 | native commit and broader edits |
| same-sentence overlap algebra | yes, v1 vectors | none | yes |
| branch-local observation and erasure | yes | one-rule concrete R2/R3 cases | general branch/constraint conservativity |
| typed RuleApplied provenance | yes | R3-G-01/02 | native event production |
| exact same-origin adjacency | yes | R3-G-04 | regression only |
| product occurrence and gapped domain events | yes, v1 vectors | none | yes |
| symbolic branch/status semantics | yes, v1 vectors | none | yes |
| candidate policies and score semantics | yes, v1 vectors | atomic patch kernel only | yes |
| pattern oracle killing same-result mutant | yes, cross vector | none | yes |
| all six typed oracle-kind comparators | yes, BAG-12 registry and vectors | none | native operand production and differential results |
| finite reachability/predicate authority | yes, exact fixture rows | none | BAG-16 collection and K evaluation |
| evaluator conformance versus production provenance | yes, distinct typed records | none | conformant native issuer and BAG-15 receipts |

## Questions intentionally left to stack evidence

These cannot be answered credibly by more prose or a Python fixture model:

- the Rust semantic IR's injective, coverage-checked mapping from parsed K over
  its explicitly declared supported surface, with unsupported or lossy forms
  rejected;
- the safe instrumentation point and supported rule shapes after Rust lowering;
- source maps and generated provenance actually retained by the new frontend;
- sort/IR/lowering validation of synthetic values;
- executor branch identity, solver constraint form, and proof of exhaustiveness;
- correctness of K pattern parsing, import/export lookup, normalized-plan
  compilation, receipt production, and equivalence to native side-condition
  evaluation;
- exact preservation of plan variable declaration order in native witness
  bindings, side-condition calls over only the declared ordered subset
  (including the empty constant interface), and catalog resolution of every
  consumer source/plan/query triple;
- preservation of corpus test/query repetitions and mutation
  test-then-`oracleDeclarations` slot flattening through native invocation and
  cache keys;
- exact sort-preserving reachability matching, side-condition evaluation over
  the declared binding interface, and complete witness-set ordering;
- exact predicate input/schema/projection provenance and finite-row lookup;
- whether each K-authored projection/comparator/query has a matching
  conformant evaluator record in addition to its operation-production receipt;
- actual stop reasons, resource enforcement, process isolation, and replay;
- real erasure equivalence for termination, topology, and constraints;
- compilation/runtime/cache inputs and performance; and
- whether/when streaming is materially better than the trace reference.

Optional debugger/backend-log adapters, cross-backend operational-step parity,
coverage scheduling, automatic higher-order mutation, C1/C2 compatibility, and
large-corpus optimization remain outside this handoff unless separately
authorized.

## Artifact ingress boundary

Rust ingress must consume the closed `artifact-role-specs.json` registry and
catalog metadata; it must not infer media type, content model, or location from
a reference. Fetching verifies raw `contentSha256` first. Canonical JSON then
uses strict UTF-8, duplicate-key rejection, the portable JSON preflight, exact
canonical-byte equality, schema/embedded-ID validation, and role-specific
semantic recomputation. Opaque bytes recompute the role/media/content-hash
envelope. A failure publishes no accepted artifact.

The future store resolver is named `rust-artifact-store-v1`, but this handoff
does not choose its API, cache, transport, directory layout, or process
topology. It must enforce the same normalized-tail rules and preserve complete
locator uniqueness. `external-required` and unbound requirements stay distinct:
the former has a reviewed identity pin, while the latter has no artifact
identity. Rust execution evidence may change `executionConformance` only by
publishing backend consumption and result evidence; catalog membership alone
cannot do so.
## BAG-10 native lowering proof handoff

Rust owns extraction of the real lowering relation, proof generation, native
checker correctness, and adapter mapping. It must bind the exact baseline or
mutant subject plus `loweringProfileDigest` and `executionProfileDigest`, and
must not reuse the portable toy relation as evidence about a real definition.
Until a registered native checker validates that relation, bounded attempts
are `time-limit` or `resource-limit`, not `lowering-nontermination`.

## BAG-12 native oracle handoff

Rust must consume the live per-test declaration graph directly. It must not
reconstruct the retired global `oracles`/`oracleIds` join or treat legacy
`oracle-projection`, `oracle-comparison`, or `oracle-value` entries in the
immutable execution-catalog snapshot as decision authority. For each selected
slot it resolves the exact declaration, produces at most one complete normal
operand for each side, and emits a BAG-15 receipt pointing forward to that
operand. Operand identity includes provenance; comparison resolves normalized
values and never uses operand-ID equality.

The portable registry is closed. Built-in algorithms may be implemented
natively and checked differentially against `oracle-semantics-vectors.json`.
K-authored operations are fail-closed: a production receipt alone establishes
only provenance. A decision additionally requires one matching conformant
`oracle-evaluator-conformance` record whose operation kind, typed roots,
compiler/evaluator versions, compatibility/execution/solver profiles, and
suite all match. The bundled nonconformant record is an explicit negative and
must never authorize a result.

For reachability, Rust must bind variables as complete portable terms of their
exact declared sorts, rederive the optional predicate-query side condition,
and publish all witnesses in finite-input order. `not-reached` requires a
complete BAG-16 collection; a bound or missing row is unknown. For structured
predicates, it must rederive the exact input role/schema/projection and ordered
binding digest. For concrete output, the declared channel name, exact
parameter-free `mediaType`, raw bytes, byte hash, and strict UTF-8 decode are
semantic inputs; worker stdout/stderr and diagnostics remain infrastructure.

Outer result construction follows the BAG-10 absence matrix exactly:
baseline-side failure retains no sides, mutant-side failure retains only the
baseline, ordinary comparison failure retains both sides but no comparison,
skipped retains none, and a pure comparison exists only with both complete
sides. The `incomparable-result` arm is the deliberate exception: it retains
both sides and the exact comparison artifact while also carrying the precise
taxonomy failure. Source side, context, scope, retryability, and disposition
must be derived from the selected active taxonomy; `resource-limit` is
unknown. `projection-invalid` and
missing input are errors; evaluator unavailable and solver unknown are
unknown. Only a validated `distinguish` can kill.

Before producing any native side, resolve the manifest's corpus and that
corpus's observation manifest through the active catalog and rederive the test
invocation. A normal side or semantic crash must bind the exact declaration,
baseline/mutant definition, profiles, terminal, test, and producing attempt.
K-authored projection and comparison roots use only their operation-specific
roles. A conformant evaluator record without the matching BAG-15 production
receipt remains insufficient authority.
