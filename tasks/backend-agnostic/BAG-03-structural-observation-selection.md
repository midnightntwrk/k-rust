# BAG-03: structural observation selection

Status: integrated backend-agnostic closure packet.

## Objective

Resolve the contradiction between the execution-pattern goal's structural
observation selection and the closed observation manifest, which currently
rejects the only structural selector represented by the abstract vectors.

Freeze a small declarative `structural-term` selector whose matches can be
derived exactly from `portable-semantic-definition-v1`. Distinguish that
bounded conformance surface from arbitrary K-authored discovery, which remains
future Rust-stack execution work.

This packet defines portable selection, cardinality, and semantic-site identity
only. It does not interpret arbitrary K patterns, instrument a definition, run
an executor, or claim observation conservativity.

## Starting inputs

- `draft/goal/execution-pattern-matching.md`, especially sections 4.1, 9, and
  12;
- `investigations/backend-agnostic-goal-closure/contracts.md`;
- `investigations/backend-agnostic-goal-closure/schemas/observation-manifest.schema.json`;
- `investigations/backend-agnostic-goal-closure/schemas/event-trace.schema.json`;
- the observation manifest/installation fixtures and both portable definition
  families;
- `investigations/backend-agnostic-goal-closure/vectors/observation-vectors.json`;
  and
- `investigations/backend-agnostic-goal-closure/verify.py`.

## Normative selector

Add a closed observation selector kind named `structural-term` with these
fields:

- `kind`: exactly `structural-term`;
- `sentenceKinds`: a nonempty, sorted, duplicate-free subset of the portable
  sentence-kind enum;
- `label`: a nonempty string or null. Null means no label restriction;
- `termPath`: a typed original-relative path from the selected sentence value;
- `termSort`: the exact required sort of the resolved portable term; and
- `termHeadLabel`: a nonempty string or null. Null accepts any term node of the
  declared sort; a non-null value requires an application node with exactly
  that label.

The definition-order match algorithm is normative:

1. traverse modules by module ordinal and sentences by their stored order;
2. retain only declared `sentenceKinds`;
3. when `label` is non-null, retain only that exact provenance label;
4. resolve `termPath` against the lossless sentence value;
5. require a `portable-term-v1` value with exactly `termSort`;
6. when `termHeadLabel` is non-null, require an application with that head; and
7. return the retained sentence lineages in traversal order.

A missing path, non-term value, wrong sort, or wrong head is a non-match for
that sentence, not permission to trust a self-asserted lineage. Malformed path
syntax is an input error. `matchedLineages` must equal the complete derived
list exactly and `expectedCardinality` must equal its length. Zero or excessive
matches relative to the declaration fail atomically with
`cardinality-mismatch`; no partial observation transformation is published.

`lineage`, `label`, and `attribute` selectors remain supported and continue to
derive their own exact match lists. The new selector must use the same
cardinality and canonical-order machinery rather than a vector-only code path.

## Bounded subset versus arbitrary K discovery

`structural-term` is deliberately not an encoding of arbitrary K matching. It
has no unification variables, recursive pattern syntax, side conditions,
negation, user functions, or K-defined joins. The host-independent reference
verifier may derive this closed subset because every operation above is part of
the portable definition/path contract.

An arbitrary K-authored structural observer remains an opaque, digest-pinned
observer artifact whose discovery must be executed and differentially checked
by the future Rust stack. It may not be relabeled `structural-term`, and the
host may not approximate it with source text, regular expressions, or a
conventional AST heuristic. Extending the interchange format for arbitrary
K-discovery results requires a later versioned decision.

Remove or replace the abstract `structural-pattern` positive vector. The v1
schema must continue rejecting an opaque `structural-pattern` selector so it
cannot bypass the declarative subset.

## Multi-match semantic-site identity

The current observation manifest places one concrete `siteId` in an emission,
which only works when a selection matches one lineage. Structural selection
can legitimately match several sentences, so the manifest emission instead
declares a semantic-site **template**:

```text
{ role, termPath }
```

or null for an `emitting-sentence` event. The template path is resolved against
every matched sentence during manifest validation. For an
`emitting-sentence-and-semantic-site` event, the concrete event-origin site is
derived for the actual emitting lineage using:

```text
k-in-k/observation-site/v1 over
{ observerDigest, observerVersion, definitionDigest,
  targetLineage, role, termPath }
```

The event still carries `{siteId, role, termPath}`. The manifest does not carry
one self-asserted site ID that could be incorrectly reused for several
lineages. A selection with N matches therefore authorizes N distinct concrete
semantic-site identities from one template.

For each matched lineage, every semantic-site and payload-binding path must
resolve, and resolved payload sorts must agree with the event declaration. One
failure rejects the whole observation installation. Duplicate or overlapping
selections remain invalid.

This is a portable manifest/identity decision, not proof that the Rust
instrumentation point is safe. Native installation and conservativity remain
Rust-required.

## Required changes

1. Add `structural-term` to the observation schema with the exact closed fields
   and nullable label/head semantics above.
2. Use one semantic validator for lineage, label, attribute, and structural
   selectors. It must derive exact lineage lists and enforce cardinality,
   canonical definition order, uniqueness, and atomic failure.
3. Change manifest semantic sites from concrete IDs to role/path templates and
   derive event-origin site IDs per matched lineage. Update contract prose,
   schema, fixtures, and semantic validation consistently.
4. Add a dedicated schema-shaped structural observation fixture, preferably on
   the counter family, rather than proving the feature only through abstract
   supplied-match vectors.
5. Preserve one schema-shaped multi-match case. It must prove definition-order
   lineage output and distinct concrete semantic-site IDs when site-carrying
   events are declared.
6. Refresh dependent manifest/result identities using the bounded fixture
   helper only after any active BAG-02 mutation integration is complete. Do not
   hand-edit or race its mutation schemas, registries, campaign, or vectors.
7. State explicitly in the contract and Rust handoff that arbitrary K-authored
   structural discovery is outside the declarative v1 reference subset and
   still requires native Rust-stack proof.

## Schema-shaped positive evidence

Add permanent positive cases for:

- a label-free counter selector resolving a typed RHS term by path, sort, and
  application head;
- a labeled structural selector that derives exactly one lineage;
- a multi-match structural selector returning all lineages in definition
  order;
- a null `termHeadLabel` accepting any portable term of the declared sort;
- a null semantic-site template for an `emitting-sentence` event; and
- one site-carrying emission template deriving a different concrete site ID for
  every matched lineage.

The multi-match fixture may be a small dedicated portable definition fixture
or a bounded in-memory schema-shaped derivative. It must pass the real
observation schema and semantic validator, not only compare abstract strings.

## Mandatory adversaries

Each of these must reject through the production-equivalent portable semantic
validator or schema:

- retain the old opaque `structural-pattern` selector;
- add an undeclared field or K-pattern escape hatch to `structural-term`;
- make `sentenceKinds` empty, duplicate, unsorted, or contain an unsupported
  kind;
- self-assert a missing, extra, duplicate, or reordered matched lineage;
- alter `expectedCardinality` after refreshing the manifest ID;
- use a malformed or out-of-range typed path;
- claim a path result with the wrong sort or application head;
- change nullable label semantics so null means “only unlabeled”;
- reuse one concrete semantic-site ID for two matched lineages;
- change a semantic-site role/path without changing the derived event site ID;
- leave one selected lineage without a resolvable semantic-site or payload
  binding;
- emit a site for an `emitting-sentence` constructor or omit one for an
  `emitting-sentence-and-semantic-site` constructor; and
- publish a partially installed observation result after any selector,
  cardinality, binding, or site failure.

Refreshing `manifestId`, `transformationId`, output identity, trace identity,
or result identity must not make any adversary acceptable.

## Ownership

The worker may modify only:

- `investigations/backend-agnostic-goal-closure/contracts.md`;
- `investigations/backend-agnostic-goal-closure/schemas/observation-manifest.schema.json`;
- `investigations/backend-agnostic-goal-closure/schemas/event-trace.schema.json`
  only if the concrete event-origin site shape must be clarified;
- observation fixtures plus a new dedicated structural observation fixture;
- `investigations/backend-agnostic-goal-closure/vectors/observation-vectors.json`;
- `investigations/backend-agnostic-goal-closure/verify.py`;
- `investigations/backend-agnostic-goal-closure/refresh_fixture_ids.py` only
  after BAG-02 integration is stable; and
- artifact catalog, completion inventory, and Rust handoff entries only where
  this packet adds a mechanical reference or the explicit arbitrary-K boundary.

Do not modify mutation operator/site-registry/campaign schemas, fixtures, or
vectors owned by BAG-02. Do not edit goal specifications, D1, roadmaps,
historical checkpoints, retired-backend evidence, or Rust implementation code.
If integration requires refreshing a mutation-owned dependent fixture, stop
and return that exact root-owned refresh request rather than crossing ownership.

## Acceptance

- the zero-backend verifier passes after serial integration;
- official Draft 2020-12 validation accepts every positive observation fixture
  and rejects every schema-negative adversary;
- every mandatory adversary rejects in a small permanent or in-memory check;
- structural matches and multi-match event sites are derived rather than
  self-asserted;
- zero/excess cardinality and any per-lineage binding/site failure leave no
  installed output;
- the old abstract contradiction is removed: the vector and schema agree on
  `structural-term`, while opaque `structural-pattern` remains rejected;
- arbitrary K discovery is explicitly left to Rust differential proof rather
  than silently approximated by the portable verifier;
- no K, Java, Rust executor, compiler, backend, or solver command is run;
- all fixtures and adversaries remain tiny and memory-bounded; and
- `git diff --check` passes for owned changes.

## Return contract

Return a concise report containing the verdict, files changed, commands run,
zero-backend check count, Draft 2020-12 result, positive structural selectors,
mandatory adversary results, semantic-site template migration, any root-owned
dependent refresh request, and the remaining arbitrary-K/Rust proof boundary.
Do not commit; root owns integration.

## Stop rule

Stop and report rather than interpreting arbitrary K patterns, adding an opaque
escape hatch, trusting supplied match lists, weakening exact cardinality,
editing BAG-02 mutation files, claiming native observation conservativity, or
running backend commands.

Direct in-memory canonicalization hardening is unrelated to structural
observation selection and is intentionally reserved for a separate portable
leaf.
