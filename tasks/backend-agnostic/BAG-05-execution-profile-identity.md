# BAG-05: one execution-profile identity

Status: integrated backend-agnostic closure packet.

## Objective

Give the digest that identifies executor configuration one portable name and
one semantic payload across corpus, pattern-result, replay, mutation-cache, and
artifact-catalog artifacts. The current package calls the same digest
`backendProfileDigest`, `executionProfileDigest`, and `profileDigest` while its
verifier silently requires equality. A Rust adapter must not have to guess
whether those fields hash the same inputs.

This packet freezes interchange identity only. It does not choose a Rust
runtime, define backend implementation internals, execute a backend, or claim
cross-backend behavioral equivalence.

## Normative decision

Use `executionProfileDigest` everywhere. It identifies the complete,
canonical, execution-engine configuration that can change observable
execution for an otherwise identical definition, program, options, solver
profile, and bounds. It is distinct from:

- `compatibilityProfileDigest`, which identifies semantic-family compatibility;
- `solverProfileDigest`, which identifies solver configuration and may be null;
- per-test `optionsDigest`; and
- explicit execution bounds.

The artifact-catalog role remains `execution-profile`. Do not retain aliases
inside v1 artifacts: multiple names invite partial population and ambiguous
cache keys. Backend-specific implementations may construct the portable
execution-profile artifact, but its digest and catalog role are
backend-agnostic interchange identity.

Every invocation identity, replay identity, pattern input, corpus root, and
mutation cache key must refer to the exact same digest. Changing only this
digest must change every enclosing derived identity that covers it.

## Required changes

1. Rename `backendProfileDigest` and generic `profileDigest` fields to
   `executionProfileDigest` in the closed schemas, fixtures, contracts, refresh
   helper, and verifier. Do not add compatibility aliases.
2. State the payload boundary above in the contract and Rust handoff. If the
   concrete profile artifact payload is not yet specified, mark that payload
   schema as Rust-owned while preserving the unambiguous digest role.
3. Ensure corpus invocations, replay manifests, pattern results, mutation
   execution policy/cache keys, and artifact catalog requirements all resolve
   the `execution-profile` role and compare the same digest.
4. Add permanent adversaries changing the digest in each consumer while
   refreshing only that consumer's enclosing IDs. Every drift must reject.
5. Add a missing-catalog-root adversary and prove that the generic validation
   path, not only the canonical fixture path, rejects it.

## Ownership

The worker may modify execution-profile fields and directly dependent IDs in
contracts, Rust handoff, relevant schemas/fixtures, artifact catalog,
`refresh_fixture_ids.py`, and `verify.py`. Do not change mutation policy
semantics, observation selectors, canonical JSON rules, goal specifications,
D1, roadmaps, historical evidence, or backend code. Integrate only after
BAG-02 through BAG-04 are stable because the refresh helper and verifier are
shared.

## Acceptance

- no live v1 field named `backendProfileDigest` or generic `profileDigest`
  remains for this identity;
- every consumer resolves one `execution-profile` catalog root;
- drift in any consumer rejects even after its local IDs are refreshed;
- existing valid semantic inputs retain their profile artifact digest;
- the zero-backend verifier and official Draft 2020-12 validation pass;
- no K, Java, Rust executor, compiler, backend, or solver command is run;
- checks remain tiny and serial; and
- `git diff --check` passes.

## Return contract

Return the fields migrated, identities refreshed, adversaries added, verifier
count, schema-validator result, and any still-unspecified Rust-owned profile
payload. Do not commit; root owns integration.

## Stop rule

Stop rather than inventing a Rust engine configuration, treating the solver or
compatibility profile as part of this digest, keeping v1 aliases, weakening
cross-artifact equality, or running backend commands.
