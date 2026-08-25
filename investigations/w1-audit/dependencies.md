# Dependency and ownership summary

## Active G1 serial spine

```text
configuration-cut decision + supported official egress decision
  -> G1 ingress
  -> SemanticInput v1
  -> stable identity/provenance/fingerprints
  -> K transform + structural selection
  -> canonical patch + validation + atomic applier
  -> official-K egress/compilation
  -> deterministic manifest/replay
```

The two product branches then diverge without changing the spine:

```text
selection -> observation spec -> conservative instrumentation
          -> trace reference -> symbolic branch/status semantics
          -> streaming monitor -> witnesses/reports

selection -> operator discovery -> single-site patch
          -> coupled atomic patch -> isolated compile/test runner
          -> result + execution-pattern oracle -> mutant report
```

Recommended owners until contracts stabilize:

- `G1-adapter-boundary`: ingress, configuration cut, and egress as one owner;
- `G1-transformation-spine`: SemanticInput, identity, lookup, and selection;
- `G1-patch-validation`: patch schema, validation, atomic application;
- `G1-observation-monitor`: instrumentation, trace reference, symbolic and
  streaming monitors;
- `G1-mutation`: operator discovery and single/coupled mutation semantics;
- `G1-validation-replay`: runner statuses, manifests, diagnostics, isolation;
- `G1-goal-integration`: shared result/pattern oracle and reporting.

No G1 branch can reach backend acceptance before the egress contract is
demonstrated. Corpus/oracle work may proceed independently, but it must not
invent a competing IR or patch schema.

## Conditional C1 serial spine

```text
outer/source adapter + module closure
  -> parsed/disambiguated sentence adapter
  -> configuration parse/generation
  -> configuration/label/sort metadata
  -> semantic lowering in pinned order
  -> cell concretization
  -> prepared module (injections/unit/minimization)
  -> declarations + structural/rule/backend axioms
  -> Kore parse/backend validation/execution
```

Retain the four coupled compiler owners from the plan, with two refinements:

- configuration/context owns CF-01..04, LO-02, LO-06, LO-07 and the versioned
  metadata API;
- sort/symbol owns LO-03/04 and KO-01..05;
- rule/axiom owns LO-01/05 and KO-06..08;
- backend policy/validation owns LO-08/09 and the pinned PR-01 profile.

KO-07 must be split before work: ordinary rules/aliases are C1, while claims
depend on the optional SP-01 proof decision. Validation groups must likewise
separate valid-input safety from optional F3 diagnostic parity.

## Conditional C2 serial spine

```text
versioned grammar/scanner IR
  -> generated grammar
  -> scanner/token stream
  -> shared parse forest
  -> cleanup/priority/KApp conversion
  -> prefer/avoid + inference + overload/list/bracket ordered filters
  -> all-kind bubble dispatch
  -> cache/remapping correctness
  -> SemanticInput equivalence with the adapter
```

Keep one coherent parser owner until intermediate snapshots exist. Safe
parallel work is limited to seams, corpora, scanner fixtures, negative cases,
and inference cross-checks.

## Requested shared-contract changes

1. Define matrix fields for `granularity`, `current_oracle_grade`,
   `candidate_target_oracle_grade`, and bounded `evidence_scope`.
2. Freeze `SemanticInput v1` only after the ingress/configuration/egress
   decision; include the supported sentence subset and deterministic encoding.
3. Freeze stable identity as a tuple of project ID, official/generated ID,
   module/label/source provenance, and structural fingerprint; specify which
   components may change after transformation.
4. Version the patch schema, edit addressing, overlap rules, failure output,
   and trusted-small atomic applier.
5. Version the layered status/diagnostic taxonomy shared by mutation,
   observation, runner, and replay manifests.
6. Add explicit parser-filter, configuration-metadata, and prepared-module
   observation contracts before C2/C1 fan-out.
7. Separate byte-hash evidence from relational oracle acceptance in the
   evidence ledger; record normalization-policy and serializer versions and
   classify hash drift without weakening repeat/mutation assertions.
