# BAG-13: portable semantic slice and local well-formedness

Status: integrated and independently audited backend-agnostic closure packet.

Accepted evidence: ordinary refresh is cache-clean and byte-idempotent at
package hash `35aa4ba3037f71a3ca11b6b9b1afb50718ff25917da1c33cf0215e2d2d98ab14`;
official Draft 2020-12 validation and `601178` zero-backend verifier checks pass.

## Objective

State honestly what `portable-semantic-definition-v1` represents and enforce
the local typing/provenance invariants it can decide without a native K
declaration table. The current contracts call the format a lossless typed K
term/definition boundary, but the schema contains only mutation-facing
modules/sentences and free-string term sorts/labels. Its validator accepts
same-name variables at different sorts, non-Bool conditions, inconsistent
application signatures, ambiguous generated status/ordinals, and attribute
order that patch application later normalizes silently.

This packet closes the portable mutation-facing semantic slice. It does not
guess a complete K production/signature/configuration schema or claim
whole-definition adapter injectivity before the Rust IR exists.

## Scope boundary

Define the current envelope in data, schemas, and identity with required
`representation: portable-mutation-semantic-slice-v1`. Cover that field in the
definition role projection and every definition identity. The slice represents
the normalized modules, imports, semantic
sentences, terms, conditions, attributes, and provenance that the two MVPs
consume, subject to the closed local rules below. It does not represent every
K module item, sort/production declaration, module attribute, configuration
metadata form, macro/alias detail, or compiler-internal sentence.

Update contracts, completion evidence, and RS-01 wording to say:

- the portable slice and its local invariants are closed now;
- Rust must enumerate the real supported K forms and declaration/signature
  tables;
- Rust must prove parsed-K/native-IR to portable-slice coverage and injectivity
  for the supported mutation/observation surface; and
- unsupported or lossy native forms reject rather than disappearing from the
  slice.

Do not weaken the requirement for a future lossless native adapter over its
declared supported surface; move that proof to the correct boundary. Remove
claims that arbitrary other K constructs can simply be encoded as applications.

## Local term well-formedness

Enforce these backend-independent rules recursively across every definition,
patch value, event payload, binding, predicate, and result operand:

1. `encoding`, sort, node kind, and all required children remain closed.
2. Within one semantic sentence, a variable name has exactly one sort across
   body, requires, ensures, and attribute term values. The variable identity
   is `(sentence lineage, name, sort)`; same spelling in another sentence is a
   different scope.
3. Non-null `requires` and `ensures` have sort `Bool`.
4. A rewrite's left and right children have the same sort. Its wrapper/body
   sort is retained independently because v1 has no native production table.
5. An injection's child/wrapper sorts continue to equal `fromSort`/`toSort`.
6. Application heads use a digest-shaped stable `symbolId` separate from their
   supplemental display label. Across one definition/slice graph, repeated `symbolId` use
   has one outer result sort, argument arity, ordered argument sorts, and
   display label. Different symbol IDs may share a display label, preserving
   overload/parameterization distinction.
7. A sequence is ordered; do not infer undeclared subsort/signature laws for
   its items in the portable checker.

`symbolId` is a portable identity field, not proof that it came from a real K
production. The future Rust adapter derives it from fully qualified native
symbol/production identity and proves the mapping. Portable fixtures use
explicit test symbol identities and can validate consistency only.

Derive one signature registry keyed by `symbolId`, whose value is exactly
`(displayLabel, resultSort, arity, argumentSorts)`. Make each validation graph
explicit. A definition graph covers every body, condition, and attribute term
across the whole definition. Patch validation seeds signatures from the
immutable baseline, then validates every patch term and complete output against
that seed. A trace/path graph adds all path predicates, event payloads, and
bindings to its referenced-definition signatures. An oracle/result graph adds
its complete operand. A fresh symbol ID with one consistent use may be locally
well formed but remains native-declaration-validation pending and never proves
native well-typedness.

Variable scope is one sentence for body/conditions/attributes, one complete
path for path predicate plus all events and bindings on that path, and one
operand for an oracle value. The same spelling may have another sort in a
different sentence/path/operand. BAG-11 query-interface names remain a
different namespace.

Patch validation applies the same local checker before mutation and to the
entire derived output. A replacement with a fresh arbitrary symbol/sort cannot
be called well-typed merely because it is structurally valid. Where native
declaration/subsort knowledge is required, portable application may prove
structural atomicity but leaves IR-validity `rust-proof-pending`; it must not
manufacture an `invalid` or `valid` native conclusion.

Before publishing any output or diff, require `replace-term` and
`original-reference` replacement to preserve the target term's outer sort,
and require every `replace-condition` value (including replacing null) to have
sort `Bool`. Seed symbol signatures from the baseline and validate the complete
output and sentence scopes after all edits. For add/replace-attribute, the
value name equals the target path name unless a future distinct rename
operation exists; preflight name collision and canonical-order consequences
atomically.

Persist the honest boundary as
`{portableApplication: applied-and-locally-well-formed,
nativeIrValidation: rust-proof-pending}`. Existing campaign
`validation.outcome: valid` remains report-contract data awaiting BAG-15 native
receipts, not evidence emitted by this checker.

## Attributes

Sentence attributes are a name-keyed set in v1, serialized as a list sorted by
attribute name in Unicode code-point order. Names are unique. Input definition
validation rejects unsorted/duplicate attributes before identity derivation;
it does not silently normalize them. Add/remove/replace preserves canonical
ordering, so an edit never changes unrelated attribute order.

If native K admits semantically repeated or ordered attributes, the Rust
adapter must either map them to a future versioned representation or reject
them for this slice; it may not collapse them silently.

## Generated provenance

Sentence semantic `kind` and source/generated status are orthogonal. Remove
`generated-rule` from the kind enum; a generated rule is `kind: rule` with
generated provenance. Generated claims, contexts, aliases, and configuration
sentences remain representable when supported by the future adapter.

Make source occurrence ordinal input-only. Require
`sourceOccurrenceOrdinal`: a nonnegative integer for source-authored sentences
and explicit null for generated sentences. Source requires `generated: false`
and null `generatedIdentity`; generated requires `generated: true`, a
`generatedIdentity` object, and null source ordinal. A generated sentence's
`generatedIdentity.ordinal` is its only generation ordinal and is covered by
lineage/content/definition identity. Do not retain an ignored wrapper ordinal
that can change bytes without changing semantic identity.

Require generated parent lineages to be unique and canonical unless a future
operation explicitly makes their order meaningful. Validate parents and anchor
against the transformation input/destination and require the last
`transformationChain` member to equal `transformationId`. Remove
`generated-rule` from common sentence/provenance kinds and every operator,
site-registry, observation, vector, and verifier enum; all-transition selection
checks `kind: rule` independent of generated status.

Add at least one persisted generated-definition fixture whose transformation
chain, parent/anchor identities, kind, ordinal, lineage, content, and
definition digests all recompute.

## Required evidence

- locally well-formed memory and counter definitions remain valid;
- repeated symbol use proves stable ID/signature consistency while two
  overloaded display labels retain distinct IDs;
- source and generated rule/claim cases demonstrate kind/status orthogonality;
- a generated sentence's sole ordinal changes every dependent identity; and
- patch application distinguishes portable structural success from future
  native IR/type validation.

Permanent adversaries must reject same-sentence variable sort drift, non-Bool
requires/ensures, rewrite child sort mismatch, injection mismatch,
symbol-ID result/arity/argument-sort/label drift, missing symbol ID,
unsorted/duplicate attributes, source-authored `generated-rule`, generated
sentence with a source occurrence ordinal, source sentence without one,
generated identity/chain/ordinal drift, and any completion claim that calls
the slice a complete/lossless K definition adapter.

Also reject same-path variable sort drift while accepting the same spelling at
another sort in another sentence; a baseline-known signature changed after its
last original occurrence is replaced; overloads collapsed by label;
replace-term/original-reference outer-sort drift; non-Bool replacement
conditions; attribute target/value-name mismatch or rename collision;
contradictions hidden only in an attribute/event/binding/predicate/terminal/
oracle term; checker normalization of unsorted input; noncanonical generated
parents or stale dependent IDs after generation-ordinal change; a singleton
fresh symbol reported native-valid; unsupported native forms silently dropped;
an invented homogeneous sequence law; or a rewrite wrapper forced to its child
sort.

## Ownership

The worker may modify common/semantic definition/identity and patch schemas,
memory/counter plus one generated fixture, identity and patch vectors,
contracts, verifier, refresh helper, completion matrix/checklist/audit, and
Rust handoff RS-01/RS-02 notes. Integrate after BAG-04 and before BAG-11/BAG-12.
Refresh the already integrated BAG-08 registry/catalog and BAG-09 terminal
values because term, identity, artifact, crash, pattern, and oracle values
depend on the shared representation. Do not edit goals/D1/
roadmap, invent a full K declaration grammar, infer native subsorting,
implement a Rust adapter, or run backend code.

## Acceptance

- the portable format is accurately scoped as a mutation-facing semantic
  slice, without weakening future native losslessness requirements;
- every locally decidable term, attribute, kind/status, and ordinal invariant
  is schema/semantically enforced;
- symbol identity is distinct from display label and supports overloads;
- generated provenance has one unambiguous ordinal and permanent evidence;
- native declaration coverage/injectivity/IR validity remain explicitly
  Rust-proof-pending;
- all mandatory adversaries reject through schema or semantic validation;
- zero-backend and official Draft 2020-12 validation pass;
- no K, Java, Rust executor, compiler, backend, or solver command is run;
- checks are tiny and serial; and
- `git diff --check` passes.

## Stop rule

Stop rather than claiming whole-K losslessness from this slice, guessing K
production/subsort rules, accepting local contradictions, or claiming native
IR validation from the portable structural checker.
