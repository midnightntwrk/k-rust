# BAG-06: mutation equivalence status boundary

Status: integrated backend-agnostic closure packet.

## Objective

Remove the contradiction in which `unclassified-equivalent` both claims an
equivalence classification and is justified by a dangling, unvalidated proof
digest. Freeze what bounded oracle agreement can and cannot establish before
the Rust campaign reporter adopts the status vocabulary.

This packet defines report semantics. It does not build an equivalence prover,
execute mutants, or claim semantic equivalence from a finite test corpus.

## Normative decision

In v1, complete agreement on every selected test/oracle classifies a valid
mutant as `survived`. It does not prove equivalence. The report already binds
the exact corpus, bounds, profiles, options, and oracle manifest needed to
interpret that bounded result.

Remove `unclassified-equivalent` and its `equivalenceEvidence` field from the
v1 campaign schema, score exclusions, fixtures, vectors, contracts, and
verifier. A non-null opaque digest is not proof, and “unclassified” is not a
sound positive classification.

A future `proven-equivalent` status is permitted only in a later version that
defines all of the following:

- a typed proof-artifact schema and catalog role;
- proof scope binding operator, baseline, mutant, and semantic profile;
- a trusted proof checker or explicitly named proof system/version;
- referential integrity and digest derivation; and
- sound score treatment.

Until that exists, no proof-shaped placeholder is accepted. A syntactic
no-change result remains the existing pre-execution `no-change` candidate
rejection, not semantic equivalence.

## Required changes

1. Remove the status, field, score bucket, and dangling proof vector from all
   closed v1 artifacts.
2. Reclassify the current bounded-agreement status vector as `survived` with
   no equivalence evidence.
3. Require every `survived` mutant to be valid and to have complete `agree`
   outcomes for every selected test and declared oracle under the report's
   schedule rules.
4. Add adversaries showing that an opaque proof field, the removed status, a
   survived mutant with skipped/inconclusive evidence, and an equivalence
   claim based only on equal final output all reject.
5. Document the future versioned proof boundary in the Rust handoff without
   implying that Rust implementation alone supplies a proof system.

## Ownership

The worker may modify mutation campaign/status schema, fixtures, status and
mutation vectors, contracts, Rust handoff, completion classifications directly
affected by equivalence, and the corresponding verifier code. Integrate only
after BAG-02 because both touch the campaign schema/fixture/verifier. Do not
change selection policy, observation semantics, canonical JSON, execution
profiles, goals, D1, roadmaps, historical evidence, or backend code.

## Acceptance

- the v1 schema rejects `unclassified-equivalent` and
  `equivalenceEvidence`;
- bounded full agreement materializes only as `survived`;
- incomplete, skipped, unknown, timeout, error, or incomparable evidence
  cannot produce `survived`;
- no opaque digest is treated as an equivalence proof;
- score counts and exclusions derive exactly from the reduced status set;
- zero-backend verification and official Draft 2020-12 validation pass;
- no backend command is run; and
- `git diff --check` passes.

## Return contract

Return the migrated statuses/fields, updated score semantics, adversaries,
verifier count, schema-validator result, and the exact future proof-system
boundary left open. Do not commit; root owns integration.

## Stop rule

Stop rather than designing an unsound proof placeholder, treating finite
agreement as equivalence, inventing a proof checker, or running backend
commands.
