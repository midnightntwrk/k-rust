# BAG-11: pattern query plan and identity

Status: integrated and root-verified backend-agnostic closure packet; final
independent acceptance rerun is pending.

Accepted evidence: two ordinary refreshes are cache-clean and byte-idempotent
at package hash `9f16d94e52e2fe92a4e5e2f650573dd4936ff301525d349577886c5e5c92bb1e`;
official Draft 2020-12 validation and `804443` zero-backend verifier checks
pass.

## Objective

Freeze the portable identity and denotation input for a named K-authored
execution query. The package currently interprets an ad hoc `queries` object
inside `execution-pattern-vectors.json`, but that object has no schema or
digest, side-condition outcomes are supplied independently of condition
identity, and corpus manifests identify a pattern artifact without identifying
the named query selected from it. A different query can therefore retain the
same corpus/cache roots.

This packet defines a normalized conformance plan produced from K source. It
does not make JSON the authoring language, implement the K compiler in the
host, or prove that Rust compiled a K pattern correctly.

## Normative model

Keep three identities distinct and represent every artifact reference as a
BAG-08 `{role, digest}` key:

1. The `pattern-source` key identifies the K-authored source artifact under
   BAG-08's role/content rules.
2. `patternPlanDigest` uses `k-in-k/pattern-plan/v1` over the complete closed
   normalized plan without its self-ID.
3. `queryId` uses `k-in-k/pattern-query/v1` over pattern source digest, plan
   digest, entry module, and exported query name.

Do not retain generic `pattern`, `patternDigest`, or an untyped source/plan
digest alias in v1 consumers. A source file, compiled plan, and selected entry
query are not interchangeable identities.

After BAG-08, add structured `pattern-plan`, `pattern-query`, and
`side-condition-conformance-table` roles. Add opaque `pattern-source`,
`pattern-side-condition`, and `pattern-compiler-profile` roles; remove generic
`pattern`. The self-identified query record is exactly
`{patternSource, patternPlan, entryModule, exportedName, queryId}`, with the
first two values BAG-08 keys. `queryId` deliberately excludes the compiler
implementation/profile: source, normalized plan, module, and exported name
define semantic query identity. Preserve the exact strings; portable code does
not invent K identifier syntax.

Give the observation event vocabulary its own semantic identity in
`k-in-k/event-vocabulary/v1`. Treat it as a constructor mapping, not accidental
manifest list order: constructor entries are unique and canonical by name, and
their payload sorts plus origin mode are covered. The plan binds this exact
digest and resolves it through one observation manifest.

Add a Draft 2020-12 schema for the normalized MVP plan. It is an interchange
and conformance value, not an internal Rust IR. Its closed algebra covers:

- an event atom with constructor and ordered payload positions;
- typed variable bind/use declarations, each with one name and sort;
- `next-event` and `eventually-after` between atoms;
- ordered alternatives;
- an optional K side-condition artifact digest over the bound variables; and
- explicit declaration order for every tie-break that affects witnesses.

Every payload position is a nonnegative integer within the constructor's
declared arity, its sort equals the event-vocabulary sort at that position,
each variable is bound before use, repeated names retain one sort, and unused
or multiply introduced variables reject. Empty patterns, zero-length
components, recursion, negation, universal temporal claims, and arbitrary
extensions remain outside the MVP plan.

### Resolved flat v1 plan algebra

Use a flat nonrecursive DNF, not recursive expression nodes:

```text
plan = {
  schemaVersion, patternPlanDigest, eventVocabularyDigest,
  variables: [{name, sort}],
  arms: [{
    atoms: [{constructor,
             payload: [{position, mode: bind|use, variable}]}],
    relations: [next-event|eventually-after]
  }],
  sideCondition: null | {
    artifact: pattern-side-condition key,
    resultSort: Bool,
    inputVariables: [name]
  }
}
```

Arms are nonempty and declaration-ordered; identical arms remain legal because
arm order breaks overlapping-witness ties. Every arm has at least one atom and
`len(relations) == len(atoms) - 1`. Payload clauses are strictly increasing by
unique position, resolve within the constructor arity, and have the vocabulary
sort of that position. `next-event` requires the next matched event index to
equal the previous index plus one; `eventually-after` requires it to be
strictly greater.

Top-level variables are the stable witness-binding interface. Every arm binds
each declared variable exactly once, uses only declared variables, and returns
the same name/sort interface. Bind-before-use order is the exact
`(atomOrdinal, payloadPosition)` order, permitting same-event equality only
after an earlier payload position binds the variable. The side-condition input
list is a canonical subset of those variables and its result sort is the
constant `Bool`. There are no hidden local variables in v1.

The plan resolves against exactly one versioned event vocabulary from the
observation manifest. Cover that vocabulary's semantic digest in the plan.
Unknown constructors, arity/sort drift, and a plan compiled for another
vocabulary reject before execution.

K module imports, exported names, and entry lookup remain K-facing source
semantics. The portable boundary requires the compiler receipt to bind source,
entry module/name, normalized plan, compiler profile/version, and diagnostics.
Only future Rust/K evidence can prove that receipt. The zero-backend package
checks the plan and its finite denotation, not K parsing or compilation.

## Side conditions

A side condition is identified by its K artifact digest and declared Bool
result sort. The finite conformance package evaluates it through a small
closed oracle table keyed by side-condition digest, canonical binding digest,
and path-predicate digest, returning exactly `true`, `false`, or `unknown`.
This replaces the current free-floating per-case `sideConditionResult`.

The table defines expected denotation for fixtures only. Native solver
evaluation, feasibility, and equivalence to the K-authored condition remain
Rust-stack proof. Missing table entries are `unknown`, never false.

The table key is exactly the condition artifact digest, a canonical bindings
digest in `k-in-k/bindings/v1`, and a canonical path-predicate digest in
`k-in-k/path-predicate/v1`. A row for different bindings or a different path
predicate is not evidence. Compiler conformance is either `not-proven` or an
unbound future requirement; a schema-shaped receipt cannot promote it.

For every finite fixture, rederive the complete persisted denotation from the
resolved plan, vocabulary, side-condition table, and trace. Derive rather than
trust the exact witness set, bindings, arm ordinal, event order, and path
status. Every witness carries its arm ordinal, including arm zero. Reject an
omitted or extra witness, self-asserted bindings/status, a different arm, or a
different canonical order even when the top-level match/no-match outcome is
unchanged.

## Invocation and replay closure

Add the pattern-source key, pattern-plan key, and derived pattern-query key to
every result, replay, mutation test invocation, cache key, and
execution-pattern oracle root. Every enclosing manifest/invocation/result ID
must cover them. Query identity belongs to each execution-pattern oracle:
several oracles in one test may intentionally select different queries. A
corpus therefore covers the exact ordered query-key set selected by its
oracles rather than pretending there is one global test query. Sharing a
source artifact across several named queries produces distinct oracle roots,
replay invocations, and cache keys.

BAG-08's catalog role table must distinguish `pattern-source` and
`pattern-plan`. The replay match step consumes the event trace plus the
normalized plan/query identity, while the source and compiler receipt remain
provenance roots. A valid plan without a native compiler receipt can satisfy
portable denotation conformance but not native K-authoring conformance.

## Required evidence

- schema-shaped single, next-event, eventually-after, ordered-alternative,
  shared-variable, and side-condition plans reproduce the existing finite
  expected results;
- two query names in one source artifact derive different query IDs, corpus
  manifests, replay invocations, and cache keys;
- changing only the normalized plan changes plan/query and all enclosing
  identities;
- condition true/false/unknown results resolve from the finite oracle key, not
  from a case-local assertion;
- memory and counter vocabularies both resolve through the generic plan
  validator; and
- K compiler conformance remains explicitly `not-proven` or an unbound future
  requirement rather than self-asserted by the portable fixture;
- every persisted result equals the complete denotation independently derived
  from its resolved plan and traces, including arm-zero witness ordinals; and
- retired `legacy-exact-trace` or whole-trace evidence remains historical and
  cannot enter the MVP plan, query, witness, or comparison semantics.

Permanent adversaries must reject unknown fields/kinds/operators,
empty/recursive/negative/universal plans, unknown constructor, payload index
out of range, duplicate index where disallowed, arity or sort mismatch,
unbound/rebound/unused/cross-sort variables, alternative reordering,
condition artifact/result-sort drift, a condition oracle row keyed to another
binding or predicate, missing entry name, source/plan/query digest drift,
corpus/replay/cache omission of any per-oracle query identity, a global query
substituted for two oracle-local queries, omitted/extra/reordered or
self-asserted witnesses/bindings/arm/path status, a witness that omits arm zero,
retired whole-trace evidence entering plan semantics, and a compiler receipt
for another source or plan.

## Ownership

The worker may add pattern-plan and finite-side-condition schemas/vectors,
replace the ad hoc query table, and modify contracts, corpus/pattern/replay,
mutation manifest/cache schemas and fixtures, artifact roles/catalog after
BAG-08, verifier, refresh helper, completion evidence, and Rust handoff query
compiler notes. Integrate after BAG-04, BAG-05, BAG-08, and BAG-10 because
canonicalization, execution identity, artifacts, and failure dispositions are
shared. Do not edit goals/D1/roadmap, define K surface syntax, compile K,
evaluate a solver, or run backend code.

## Acceptance

- normalized query plans have one closed schema, digest, and finite denotation;
- K source, normalized plan, and selected named query have distinct identities;
- every invocation/replay/cache consumer covers the selected query;
- variable, event-vocabulary, ordering, and side-condition relations are
  derived and adversarially checked;
- portable plan conformance is not misreported as K compilation proof;
- all mandatory adversaries reject through schema or semantic validation;
- zero-backend and official Draft 2020-12 validation pass;
- no K, Java, Rust executor, compiler, backend, or solver command is run;
- checks are tiny and serial; and
- `git diff --check` passes.

## Stop rule

Stop rather than making JSON the user language, trusting a self-asserted K
compiler receipt, interpreting arbitrary K side conditions in Python, or
claiming native solver/compilation correctness.
