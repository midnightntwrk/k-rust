# BAG-02: policy-derived mutation generation

Status: integrated backend-agnostic closure packet.

## Objective

Make mutation generation a deterministic derivation from a resolved mutation
site registry and the operator's declared policy. A complete campaign must not
omit, reorder, split, combine, or substitute discovered sites while still
claiming complete generation.

This packet freezes portable selection and report semantics. It does not run a
K operator, evaluate a patch template, apply a patch in Rust, compile a mutant,
or execute an oracle.

## Starting inputs

- `draft/goal/semantic-mutation-testing.md`, especially sections 6, 7, and 12;
- `investigations/backend-agnostic-goal-closure/contracts.md`;
- `investigations/backend-agnostic-goal-closure/schemas/mutation-operator.schema.json`;
- `investigations/backend-agnostic-goal-closure/schemas/mutation-site-registry.schema.json`;
- `investigations/backend-agnostic-goal-closure/schemas/mutation-campaign.schema.json`;
- the mutation operator, site-registry, and campaign fixtures;
- `investigations/backend-agnostic-goal-closure/vectors/mutation-vectors.json`;
- `investigations/backend-agnostic-goal-closure/refresh_fixture_ids.py`; and
- `investigations/backend-agnostic-goal-closure/verify.py`.

## Normative model

### Discovery is separate from policy derivation

The site registry records discovery evidence, not report candidates:

- `sites` is the canonical ordered list of structural matches;
- `tuples` is the canonical ordered list emitted by the declared join;
- a null join produces exactly one singleton discovery tuple per site;
- a non-null join produces tuples in its declared role order; and
- the registry records whether discovery was exhaustive. A resource-bounded
  prefix must never be indistinguishable from exhaustive discovery.

The host must not invent a Cartesian product. Actual selector, join, and patch
template evaluation remains K-authored work for the future Rust stack. The
portable verifier may independently derive the deliberately small conformance
fixtures, but that reference logic is not a production host selector.

Policy then derives one canonical **instance-tuple sequence** from the registry:

| policy | compatibility | derived instance tuples |
| --- | --- | --- |
| `exact` | null unary join or declared N-role join | the registry's joined tuples, only after exact count and arity validation |
| `each` | null join and unary discovery tuples only | one singleton instance per site, in registry site order |
| `tuple-each` | non-null join only | one instance per joined tuple, in registry tuple order |
| `all-matches` | null join and unary discovery tuples only | no instance when there are no sites; otherwise one instance whose `siteTuple` is every site ID in registry order |

`expectedTupleArity` describes a discovery tuple. For `all-matches` it is one;
the derived aggregate instance may contain more than one site. Campaign
validation must therefore not apply the unary discovery arity to the aggregate
`all-matches` instance.

This explicit aggregate instance is the v1 representation of `all-matches`.
It has one `instanceId`, one patch, one candidate before patch deduplication,
and at most one mutant, regardless of site or edit count. Splitting it into
independent instances is invalid.

The aggregate must not collapse bindings from different discovery tuples.
If two sites bind the same variable name to different terms, the campaign must
retain those bindings per source discovery tuple (or use an equivalently
lossless, unambiguous representation). A single flat `bindings` array is valid
only for an ordinary one-tuple instance. Instance identity covers the complete
per-tuple binding evidence as well as the aggregate site order.

### Cardinality and completeness

Validation happens in this order:

1. validate registry identity, site uniqueness, tuple membership/order, and
   discovery completeness evidence;
2. validate policy/join compatibility and discovery tuple arity;
3. for `exact`, compare the full discovered tuple count with
   `expectedTupleCount` before any cap is applied;
4. derive the canonical instance-tuple sequence;
5. retain the canonical prefix permitted by the candidate cap; and
6. evaluate and deduplicate patches while retaining every originating
   instance in canonical order.

An exhaustive `exact` discovery with zero or excessive tuples is
`cardinality-mismatch`. A wrong tuple arity or incompatible policy/join shape
is `invalid-join`. Either is a terminal selection failure: it produces no
candidates, mutants, or score and must have a distinct non-success campaign
disposition rather than masquerading as `complete` or as a resource-truncated
generation. If the existing campaign status vocabulary cannot express this
without calling it a generic infrastructure `error`, add a closed
`selection-failed` disposition.

Zero exhaustive discoveries under `each`, `tuple-each`, or `all-matches` are a
valid complete empty generation, not a cardinality mismatch. The resulting
complete campaign may have a zero score denominator after the baseline gate.

If discovery is not exhaustive, or a positive candidate cap retains fewer
derived instances than exist, generation is incomplete. It must:

- retain only the canonical prefix;
- carry `incomplete-generation` evidence;
- publish no complete score; and
- never claim that omitted suffix instances do not exist.

For `all-matches`, non-exhaustive discovery may retain one aggregate over the
known canonical site prefix for diagnostic purposes, but it remains an
incomplete, unscored hypothesis. It is not the complete all-matches mutant.

The cap applies to the policy-derived instance sequence before identical-patch
deduplication. Deduplication cannot be used to hide cap truncation. Because
`all-matches` derives at most one instance, discovery exhaustion—not candidate
count—is what proves that its aggregate contains all sites.

### Canonical report order and patch deduplication

For every retained instance, derive `instanceId` from the complete aggregate or
ordinary site tuple, canonical bindings, policy, patch ID, operator identity,
and baseline identity as already specified.

If multiple instances produce the same canonical patch:

- emit one candidate keyed by that patch;
- retain all originating instances exactly once;
- order those origins by their order in the derived instance sequence; and
- order candidates by the ordinal of their first origin, breaking an impossible
  tie by `candidateId`.

Candidate rejections and mutants must follow that same candidate order. A
report-ID refresh does not legitimize a permuted report.

This packet validates edit IDs and origin retention, but it does not attempt to
reimplement the K patch template. Edit-to-site/template provenance is a
separate portable packet.

## Required changes

1. Align the contract, operator/site-registry/campaign schemas, and verifier
   with the normative model above. Introduce explicit discovery-exhaustion
   evidence and, if needed, a typed `selection-failed` campaign disposition.
2. Implement one policy-derivation function used by positive fixtures and
   campaign semantic validation. Do not leave policy logic split between
   unrelated vector-only and fixture-only checks.
3. Compare a complete campaign's retained origins with the entire derived
   sequence. For an incomplete campaign, compare them with exactly the allowed
   canonical prefix.
4. Enforce policy/join compatibility, exact full-discovery count/arity,
   `all-matches` aggregation, canonical candidate/origin order, and retained
   origin coverage after patch deduplication.
   The campaign representation must preserve per-discovery-tuple bindings for
   aggregate instances; do not merge same-named bindings from different sites.
5. Add schema-shaped positive evidence for:
   - unary `exact` with one site;
   - multi-site `each`;
   - N-role `tuple-each` using only supplied join tuples;
   - multi-site `all-matches` as one aggregate instance; and
   - two distinct origins producing one deduplicated patch.
6. Add schema-shaped failure evidence for exhaustive `exact` zero/excess and
   wrong arity, plus incomplete canonical-prefix evidence caused by a cap or
   non-exhaustive discovery.
7. Refresh all dependent identities through the existing bounded refresh
   helper. Do not hand-edit a partial digest graph.

## Mandatory adversaries

Each adversary must be rejected by the same semantic validator used for the
canonical campaign, not only by an abstract vector assertion:

- change a unary `each` operator to use a non-null joined registry;
- change `tuple-each` to a null unary registry;
- omit the middle or final instance from a complete `each` campaign;
- reorder complete `each` or `tuple-each` origins/candidates;
- select an arbitrary expected-count subset from an excessive `exact`
  discovery;
- publish candidates after exact zero/excess cardinality failure;
- split one multi-site `all-matches` aggregate into several instances;
- reorder or omit a site inside the `all-matches` aggregate;
- mark a non-exhaustive or cap-truncated prefix complete;
- apply the cap after patch deduplication instead of before it;
- discard one origin when identical patches deduplicate; and
- permute deduplicated origins or candidates and refresh the report ID.

Permanent vectors must also prove the positive inverse of each major rule.

## Ownership

The worker may modify only:

- `investigations/backend-agnostic-goal-closure/contracts.md`;
- the three mutation schemas named in the starting inputs;
- mutation operator, site-registry, and campaign fixtures, including new
  schema-shaped fixtures directly needed by this packet;
- `investigations/backend-agnostic-goal-closure/vectors/mutation-vectors.json`;
- `investigations/backend-agnostic-goal-closure/refresh_fixture_ids.py`;
- `investigations/backend-agnostic-goal-closure/verify.py`; and
- artifact catalog/completion inventory files only where new packet artifacts
  or refreshed identities require a mechanical reference update.

Do not edit goal specifications, D1, roadmaps, historical checkpoints, Rust
implementation code, or retired-backend evidence. Record any required
out-of-scope correction in the worker report.

## Acceptance

- the zero-backend verifier passes after the package is internally stable;
- every mandatory adversary above rejects in a bounded in-memory check;
- official Draft 2020-12 validators accept every positive schema-shaped
  fixture and reject the schema-negative cases;
- exact zero/excess cannot publish candidates or a score;
- complete non-exact generation cannot omit or reorder a derived instance;
- incomplete generation is precisely a canonical prefix and is unscored;
- multi-site `all-matches` is one aggregate instance and at most one mutant;
- identical-patch deduplication retains every canonical origin;
- no K, Java, Rust executor, compiler, backend, or solver command is run;
- the packet remains bounded to small JSON fixtures and in-memory adversaries;
  and
- `git diff --check` passes for owned changes.

## Return contract

Return a concise report containing the verdict, files changed, commands run,
zero-backend check count, schema-validator result, positive policy fixtures,
mandatory adversary results, any still-open edit-to-site provenance question,
and the recommended next portable packet. Do not commit; root owns integration.

## Stop rule

Stop and report rather than evaluating K-authored discovery/template code,
claiming Rust execution proof, weakening a policy to fit the current campaign
shape, or treating a green verifier as proof of omitted policy coverage.
