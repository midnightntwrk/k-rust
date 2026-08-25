# BAG-10: closed failure disposition and semantic-evidence boundary

Status: integrated and independently audited, 22 August 2026 (493,112
zero-backend checks, including official Draft 2020-12 validation). Placement
closure remains provisional until the mandatory BAG-15/BAG-16 rerun.

## Objective

Make the failure taxonomy itself a closed, machine-validated contract and
prevent semantically decisive labels from standing in for evidence. The
current package has no schema for `failure-taxonomy.json`, validates only
classification-set unions, permits conflicting or context-incomplete rules,
and accepts `lowering-nontermination` with empty `details` despite requiring
affirmative proof in the normative prose.

This packet does not require bespoke diagnostic payloads for every ordinary
failure. It closes disposition, semantic-evidence linkage, and the boundary
between portable report validation and future native proof.

## Normative model

Add a Draft 2020-12 schema for the taxonomy and make each failure entry the
single source of truth for:

- exact `(stage, classification)` identity;
- allowed scopes for that classification, not merely for its whole stage;
- its one retryability rule;
- every artifact context in which it may appear; and
- exactly one disposition, or one explicitly named policy/gate delegation,
  in each admitted context.

Use a closed context vocabulary covering at least pattern path, pattern test,
corpus shared setup, candidate generation, baseline validation, baseline
oracle gate, mutant validation, mutant execution, oracle comparison, campaign,
and report publication. A schema permitting a failure placement and a
taxonomy lacking its context mapping is invalid. Conversely, a taxonomy rule
for an unreachable stage/class/scope/context combination is invalid.

Disposition is artifact-level, not a generic status string. It names the
actual consequence appropriate to its context, such as pattern `unknown`,
pattern `error`, candidate `rejected`, baseline `baseline-invalid`, baseline
`baseline-oracle-failed`, mutant `invalid`/`timeout`/`unknown`/`error`, or
unpublishable report. BAG-09 owns semantic-termination operands and the crash
policy; after BAG-09, no generic `semantic-crash` failure or special taxonomy
escape remains. `baseline-mismatch` maps only through the baseline-oracle gate.

`details` remains canonical diagnostic metadata. It may be empty and may
change a containing report's content identity, but no outcome, retryability,
score, gate, or semantic classification may depend on a key inside it. Human
text, native exception fields, stderr, and backend-specific counters belong
there only as non-semantic diagnostics.

### Resolved v1 taxonomy and reachability surface

Add required `context` to `common.failure`. Keep `stage`, `classification`,
`context`, `scope`, and BAG-09's outer oracle `sourceSide` distinct: they mean
where the failure occurred, what occurred, which artifact operation derives a
consequence, which entity is affected, and which comparison side failed,
respectively. A copied corpus failure retains its original pattern context;
copying it does not reclassify the failure.

The closed initial contexts are `observation-installation`,
`mutation-discovery`, `candidate-generation`, `pattern-path`, `pattern-test`,
`corpus-shared-setup`, `baseline-validation`, `baseline-execution`,
`baseline-oracle-gate`, `mutant-validation`, `mutant-execution`,
`oracle-comparison`, `campaign`, and `report-publication`. BAG-14/BAG-15 may
add their versioned cache/receipt contexts, followed by the mandatory final
reachability rerun after BAG-16; BAG-10 must not claim permanent closure over
schemas that do not exist yet.

Replace `scopeRules`, `outcomeRules`, `retryabilityRules`, and bare entries
with one canonically ordered entry-centric model and a derived `taxonomyId`:

```text
entry = {
  stage, classification, retryability,
  placements: [{context, scope, consequence}],
  evidencePolicy
}
```

Each `(stage, classification)` occurs once, ordered by the frozen stage order
then classification. Placements are nonempty, unique, and ordered by frozen
context/scope order. `consequence` is exactly one tagged value: either an
artifact-level `disposition` from the closed vocabulary or a named versioned
`delegation`; it can never contain both. `evidencePolicy` is `none` except for
the exact lowering-nontermination policy. There is no `all-other`, repeated
scope table, overlapping classification union, or unchecked fallback.
Allowed scopes are derived from placements. Top-level `detailsPolicy` is the
constant `diagnostic-only`. `taxonomyId` is
`k-in-k/failure-taxonomy/v1` over the complete object without `taxonomyId`,
and BAG-08 gains the structured `failure-taxonomy` role.

Make schema reachability real. Define context-specific failure `$defs` that
constrain context, scope, and admitted stage/classification pairs, and make
every failure-bearing artifact location reference its exact def. Maintain a
closed inventory of all such schema JSON pointers and reject any new raw
`common.schema.json#/$defs/failure` placement. The verifier exhaustively
enumerates the finite `(context, scope, stage, classification)` product through
those schema fragments and proves equality with taxonomy placements in both
directions. Thus every schema-legal placement has one consequence, every
taxonomy placement is reachable, and every failure location is inventoried.

Selection needs an explicit seam: pre-candidate cardinality/invalid-join
failure derives `selection-failed`, while retained-prefix exhaustion derives
`incomplete-generation`. Split their contexts or use one closed
`generation-completeness-policy-v1` delegation whose relational rule derives
the two cases; never let one placement silently mean both.

BAG-09 seam rules are fixed. `semantic-crash` has no taxonomy entry.
`oracle/baseline-mismatch` exists only at `baseline-oracle-gate` and derives
`baseline-oracle-failed`. `oracle/incomparable-result` from BAG-09's comparison
source exists only at `oracle-comparison` and derives error/exclusion, never a
kill. Missing/dangling/untrusted crash artifacts use existing input, report,
or infrastructure failures. The reachability audit includes failures nested
inside BAG-09's side/source wrapper, not only legacy top-level fields.

## Semantic evidence

Evidence that authorizes a semantic disposition is a canonical array of
BAG-08 keys outside `details`. Ordinary failures require it to be empty.
`lowering-nontermination` requires exactly one checked-receipt key; proof-like
keys hidden in `details` remain diagnostics and authorize nothing.

Add structured roles/schemas `lowering-cycle-proof` and
`lowering-proof-check-receipt`, plus the previously missing opaque
`lowering-profile` identity. Do not overload `executionProfileDigest`: the
lowering pipeline and execution engine are distinct. Propagate
`loweringProfileDigest` through the mutation manifest now; BAG-14 attempt/cache
keys and BAG-15 operation receipts must consume it.

The proof subject is a closed union so baseline and mutant failures are both
representable:

- baseline: `{role: baseline, definitionDigest}`; or
- mutant: `{role: mutant, baselineDefinitionDigest, mutantId,
  mutantDefinitionDigest}`.

The proof and receipt bind that exact subject, lowering profile, execution
profile, proof/checker versions, and artifact keys. V1 admits only
`finite-cycle-witness-v1`; another proof kind requires a later schema/checker
version, not an open string.

Freeze one tiny finite relation in the conformance package. The registered
portable checker independently recomputes that the cycle is nonempty, its
first state equals its last, every state resolves in the frozen relation, and
every adjacent pair is an actual relation edge. Relation, proof, subject, and
profile roots must equal the receipt. The checker ID/version and derived result
are covered by the receipt ID. A supplied `verified: true`, `cycle-confirmed`,
edge list, or receipt result is never authority; an unknown checker or one the
portable verifier cannot run does not authorize the classification.

A relation supplied alongside its witness cannot validate itself merely by
repeating the same edges. This package's positive case uses the independently
frozen toy relation/checker and proves only the proof/receipt protocol. A real
baseline or mutant cannot be classified `invalid` for lowering
nontermination until the future registered native checker validates the real
relation and exact subject. Until then, a bounded attempt is `time-limit` or
`resource-limit`, never presumed nontermination.

BAG-09's typed semantic-crash operands obey the same principle: their terminal
evidence is semantic input to the oracle result, never an entry in diagnostic
`details`. Preserve an adversary for the old behavior where an equal-valued,
witness-free oracle became a kill by adding only a bare crash label.

## Required evidence

- the taxonomy validates against its own closed schema;
- every schema-legal failure placement has exactly one derived disposition or
  one named delegation, and every taxonomy placement is schema-reachable;
- a tiny valid lowering cycle produces `lowering-nontermination` and mutant
  `invalid` only after its receipt is checked;
- a broken/missing/unresolved cycle proof cannot produce that classification
  or disposition;
- ordinary failures demonstrate that empty `details` remain legal and
  irrelevant to outcomes; and
- BAG-09 crash operands and `baseline-mismatch` use their typed policy/gate
  paths rather than verifier exceptions.

Permanent adversaries must reject duplicate or unknown taxonomy entries,
stage/class pair drift from `common.schema.json`, invalid scopes or
retryability, unknown context/disposition/delegation names, duplicate
conflicting rules, missing per-context coverage, unreachable mappings,
outcome changes caused only by `details`, evidence hidden in `details`, empty
or dangling nontermination evidence, a cycle with an invalid edge or unequal
endpoints, input/profile/checker drift, a self-asserted unchecked proof, and
the equal-valued witness-free crash-label kill.

Also reject noncanonical/empty/conflicting placements; multiple consequences;
a broad failure reference at an uninventoried schema pointer; context/scope
drift after refreshing report IDs; a copied corpus failure whose origin
context changes; classification/retryability/status/score changes caused only
by `details`; ordinary failures carrying semantic evidence; wrong-role,
dangling, extra, or missing proof/receipt keys; baseline/mutant subject
reversal; definition/lowering/execution-profile drift; unknown proof kind or
checker/version; a self-asserted receipt verdict; empty, nonclosing,
degenerate, missing-state, broken-edge, or reordered cycles; toy-relation
drift; a valid receipt attached to another failure; baseline nontermination in
a mutant-only receipt; and a time/resource stop relabeled nontermination.

## Ownership

The worker may add the taxonomy schema and proof/receipt schema, modify failure
taxonomy JSON/prose, common/mutation campaign schemas, minimal taxonomy and
lowering-proof vectors/fixtures, contracts, artifact role table/catalog after
BAG-08, verifier, refresh helper, completion evidence, and Rust handoff proof
notes. Integrate after BAG-06, BAG-08, and BAG-09. Do not create a broad
backend-log schema, type every diagnostic detail, edit goals/D1/roadmap, claim
native proof, or run backend code.

BAG-10 owns taxonomy identity/schema, the context-specific placement surface,
the details/evidence boundary, the lowering proof protocol, and its registered
toy checker. BAG-09 owns terminal/crash operands and baseline crash policy;
BAG-11/BAG-12 add query/oracle placements while reusing this taxonomy;
BAG-14/BAG-15 add cache/receipt contexts and bind `taxonomyId` plus
`loweringProfileDigest`; and BAG-16 participates in the final placement audit.
Rust owns real lowering-relation extraction, native checker correctness,
proof generation, and adapter mapping.

## Acceptance

- taxonomy structure, reachability, uniqueness, and context disposition are
  fully schema/semantically checked rather than set-unioned;
- no verifier exception substitutes for a missing taxonomy mapping;
- `details` is explicitly non-semantic;
- semantically decisive lowering nontermination requires checked, resolvable,
  input-bound evidence;
- bounded failure to prove nontermination remains timeout/unknown;
- all mandatory adversaries reject through schema or semantic validation;
- zero-backend and official Draft 2020-12 validation pass;
- no K, Java, Rust executor, compiler, backend, or solver command is run;
- checks are tiny and serial; and
- `git diff --check` passes.

This packet's initial placement closure is explicitly provisional: rerun the
complete failure-site inventory and bidirectional taxonomy reachability audit
after BAG-15 and BAG-16 land before declaring the backend-agnostic goal closed.

## Stop rule

Stop rather than trusting a bare label/digest/boolean as semantic proof,
parsing diagnostics to derive status, or claiming the future Rust checker has
validated a real lowering relation.
