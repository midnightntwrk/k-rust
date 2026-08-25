# BAG-08: artifact identity and resolution boundary

Status: integrated and independently reverified, 22 August 2026 (185,411
zero-backend checks, including official Draft 2020-12 validation).

## Objective

Make role-typed artifact roots independently meaningful and honestly
resolvable. The package currently says every digest is domain-separated
canonical JSON, while the artifact catalog also declares `opaque-bytes`
entries and supplies synthetic `artifact://` paths without a named resolver.
Catalog membership therefore proves neither how an opaque digest was derived
nor that replay inputs can be retrieved.

This packet closes the portable identity, storage-integrity, and availability
contract. It does not choose a Rust object store, transport, cache, or process
topology.

## Normative model

Keep two identities distinct:

1. `digest` is the role-typed semantic root used by manifests and replay
   graphs. It remains a domain-separated canonical-JSON digest.
2. `contentSha256` is lowercase raw SHA-256 over the exact bytes returned by
   the locator. It proves storage/transport integrity but is not a semantic
   object identity.

For a closed canonical-JSON artifact, `digest` continues to use the owning
object's documented semantic domain and payload. It is not inferred by hashing
the pretty-printed file bytes. Retrieval must first match `contentSha256`, then
pass the shared canonical-JSON preflight, then recompute the owning semantic
identity from the decoded object. Because this content model is named
`canonical-json`, the retrieved bytes must also equal the package's canonical
serialization exactly: no BOM, insignificant whitespace, trailing newline,
duplicate keys, or alternate escaping. A decodable but noncanonical byte
representation is not a canonical-JSON artifact.

Freeze one closed role-to-identity table shared by the catalog and every
artifact reference. For each structured role, the table names its schema,
semantic digest domain, and exact payload projection, including any self-ID
removal. Entries cannot invent identity domains or payload projections. The
role vocabulary must cover supplied and replayed outputs as well as roots,
including event traces, pattern results, baseline/mutant oracle values,
instrumented/mutant definitions, and provenance receipts where BAG-07 adds
them. Reconcile current aliases such as `projection` versus
`oracle-projection` rather than accepting both silently.

For an otherwise opaque byte artifact, define `digest` as
`k-in-k/opaque-artifact/v1` over the exact closed envelope:

```json
{
  "role": "<catalog role>",
  "mediaType": "<normalized media type>",
  "contentSha256": "<raw byte hash>"
}
```

The role is included so identical bytes used as, for example, a program and a
solver profile do not share semantic identity accidentally. Media types use a
single frozen lowercase ASCII representation with no parameters in v1; reject
rather than normalizing aliases or parameters differently across
implementations.

Catalog entries declare `availability` as one of:

- `bundled`: the package's zero-backend resolver must dereference the locator
  and verify both byte integrity and the applicable semantic identity; or
- `external-required`: the catalog freezes expected identity and location,
  but the package does not possess the bytes and must not describe the
  corresponding replay as locally executable or materially closed.

`logicalPath` is a logical locator, not evidence of existence. Freeze the v1
resolution rules for each admitted scheme. `repo://` resolves beneath the
repository root after rejecting absolute paths, empty segments, `.`/`..`,
backslashes, percent-encoded separator/traversal spellings, and symlink escape.
`artifact://` is admitted only with an explicitly named resolver identifier;
the spelling alone never implies a content-addressed store. Schemes without a
resolver available to the zero-backend package must be
`external-required`. Locator uniqueness is scoped to the complete normalized
locator, while artifact uniqueness remains `(role, digest)`.

The catalog itself remains identified by
`k-in-k/artifact-catalog/v1` over the complete catalog without `catalogId`, so
content hashes, availability, and resolver declarations are covered by its
identity.

### Resolved v1 schema and resolver surface

Use one exact concrete catalog-entry shape:

```json
{
  "role": "program",
  "digest": "<semantic digest>",
  "contentModel": "opaque-bytes",
  "mediaType": "application/octet-stream",
  "contentSha256": "<raw byte SHA-256>",
  "availability": "bundled",
  "logicalPath": "repo://investigations/backend-agnostic-goal-closure/material/program.bin",
  "resolverId": "repo-v1"
}
```

The closed resolver registry in v1 is:

- `repo-v1`: scheme `repo`, available to the zero-backend verifier; and
- `rust-artifact-store-v1`: scheme `artifact`, named but unavailable to the
  zero-backend verifier.

`repo://` entries must be `bundled` and use `repo-v1`. `artifact://` entries
must be `external-required` and use `rust-artifact-store-v1`; v1 does not
pretend that spelling an artifact locator supplies a local object store.
Reject every other resolver/scheme/availability combination.

For both schemes the path tail is already its normalized spelling: require
nonempty ASCII segments and reject controls, backslashes, all percent escapes,
absolute tails, empty segments, `.` and `..`. `repo-v1` resolves from the
real repository root, requires a regular file, and rejects any resolved target
outside the real root, including symlink escape. `artifact://` is checked
lexically but never dereferenced by this package. Complete normalized locators
are unique.

All concrete entries require `contentSha256`. For an absent
`external-required` object, the portable verifier can check only that this pin
is well formed and consistently referenced; it cannot prove that the absent
bytes once existed or that the pin was honestly obtained. External identity
provenance is therefore a reviewed/documented input. If no user-owned or
supplier-owned byte hash is actually known, represent the dependency as an
`unboundRequirement` with a unique slug-like `requirementId` and closed role,
outside the concrete catalog. It has no digest and proves neither referential
nor material closure. A manifest field that requires a concrete digest cannot
be silently rewritten to such a requirement.

Make the catalog the sole metadata authority. The shared reference is exactly
an `artifactKey` containing `{role, digest}`. Remove repeated media type,
content model, and locator fields from references. Replace replay's parallel
digest/role arrays with paired `inputArtifacts` and `expectedArtifacts` arrays
of keys, so role typing cannot be lost by set operations or unequal array
lengths. Where recipe templates genuinely permit unbound inputs, use a closed
`artifactUse` union of an artifact key or `{role, requirementId}`; outputs and
completed manifests remain concrete keys.

Create one normative role-spec registry consumed by catalog/reference
semantic validation. Do not create a self-cataloging regress. Each spec fixes
the role, content model, media type, schema if structured, digest domain, and
exact payload projection. Schema fields may use the shared closed role
vocabulary, but verifier startup must prove that every schema role and every
role-spec key agree exactly. BAG-07 receipts stay embedded in `instanceId` and
are not a new artifact role.

At minimum the structured `application/json` roles are definition,
instrumented-definition, mutant-definition, transformation,
compatibility-profile, observation-manifest, mutation-operator,
mutation-selector, mutation-join, mutation-site-registry, patch,
structural-diff, event-trace, pattern-result, and replay-manifest when supplied.
Use their already documented domains/projections and validate embedded self
IDs when present. Add any other actually supplied structured output found by
the reference inventory rather than coercing it to opaque bytes. The opaque
`application/octet-stream` roles are observer, program, parser,
execution-profile, solver-profile, options, pattern, mutation-module,
precondition, postcondition, patch-template, oracle-projection,
oracle-comparison, and oracle-value. Remove `projection`/`comparison` aliases.
Execution-pattern values use `pattern-result`; other projected operands use
`oracle-value`. Do not use distinct baseline/mutant opaque roles: role-separated
opaque digests would make byte-identical agreement operands unequal.

For byte verification, perform raw SHA-256 first. A `canonical-json` object is
then strict UTF-8 decoded with duplicate-key detection and the shared portable
JSON preflight, schema/semantic validated, and reserialized; its exact bytes
must equal the input. Freeze the existing serializer spelling explicitly:
short escapes `\\b`, `\\t`, `\\n`, `\\f`, and `\\r` for U+0008, U+0009,
U+000A, U+000C, and U+000D; lowercase `\\u00xx` for other controls; required
quote and reverse-solidus escaping; direct non-ASCII scalar UTF-8; and no BOM,
solidus escaping, non-ASCII escaping, whitespace, or trailing newline.
Only then recompute the role-specific semantic digest. Opaque bytes recompute
the frozen role/media/content-hash envelope digest.

The catalog is authoritative for artifact metadata. Prefer references that
contain only `(role, digest)`. If a reference continues to repeat media type,
content model, or locator, each repeated value must exactly equal the unique
catalog entry; it is never an unchecked alternate location. The existing
replay, oracle, and catalog fixtures currently disagree on several such names,
media types, and locators, and must be reconciled rather than grandfathered.

## Replay closure

Separate three claims that are currently easy to conflate:

- **referential closure**: every role/digest root resolves to exactly one
  catalog entry;
- **material closure**: every replay input root required before execution is
  `bundled` and successfully dereferenceable; and
- **execution conformance**: a backend consumed those bytes and produced the
  declared results.

The portable verifier may prove the first two for bundled fixtures. Only the
future Rust stack can prove execution conformance. A replay with any
`external-required` input may remain a valid frozen recipe, but it is not a
self-contained replay bundle and cannot satisfy a completion claim that
requires material replay evidence.

An `external-required` artifact still has known identity: its
`contentSha256`, semantic `digest`, media type, and resolver location are all
frozen even though the bytes are absent locally. An arbitrary placeholder hex
value with no known bytes is not an artifact identity and cannot appear as a
catalog entry. Model such a dependency, if it is worth retaining, as an
explicit unbound recipe requirement/template with no claim of referential or
material closure. A manifest that requires a concrete digest cannot be
silently downgraded to that template form.

Generated outputs named only in replay steps need no pre-existing catalog
entry. Any output also cited as a supplied fixture, expected-result artifact,
or later replay input must have a role-consistent catalog entry and obey the
same availability rules.

Publish a derived replay-closure record containing the replay ID,
`referentialClosure`, `materialClosure`, sorted unresolved concrete keys,
external-required input keys, and unbound inputs. Referential closure requires
every concrete required/supplied key to resolve uniquely. Material closure
additionally requires no unbound pre-execution input and successful bundled
verification for every pre-execution input. An internally generated output is
not a pre-execution material requirement merely because it is consumed later,
but it must still be a typed DAG output; if it is separately supplied or used
as an expected-result artifact, catalog it and verify it normally.
`executionConformance` is always explicitly `not-proven` in this package,
never `true`.

## Required evidence

- one bundled canonical-JSON artifact whose semantic digest differs from its
  exact-byte `contentSha256`, and whose identity and bytes both verify;
- one bundled opaque artifact whose semantic digest derives from the frozen
  envelope and whose bytes verify;
- identical bytes under two different roles produce different semantic
  digests;
- an `external-required` artifact proves referential closure but not material
  closure;
- every replay fixture has an explicit derived referential/material-closure
  result rather than inheriting one from catalog membership; and
- package prose names which current replay recipes are self-contained and
  which still require future Rust-stack artifacts;
- shared role vocabulary and metadata agree across catalog, replay, pattern,
  oracle, campaign, and supplied-output references; and
- arbitrary repeated placeholder roots are replaced by real test bytes and
  refreshed identities or are honestly modeled as unbound recipe
  requirements, never as resolved artifacts.

Permanent adversaries must reject byte-hash drift, semantic-digest drift,
role/media-type envelope drift, a canonical object that decodes but resolves
to another semantic identity, noncanonical-but-decodable JSON bytes, duplicate
`(role, digest)` entries, duplicate normalized locators, reference/catalog
role/media/model/locator drift, an unknown or aliased role, opaque identity
reuse across roles, a supplied output absent from the catalog, a missing or
unknown `artifact://` resolver, a `bundled` missing target,
traversal/symlink escape, an opaque external entry without a known content
hash, and a claim of material closure with any unresolved or unbound input.

## Ownership

The worker may modify the artifact-catalog and shared artifact-reference
schemas, catalog and minimal byte fixtures, contracts, replay closure vectors,
verifier, refresh helper, README/completion evidence, and Rust handoff artifact
ingress notes. Integrate after BAG-04 and BAG-05 because canonical preflight
and execution-profile naming affect the same roots; integrate after BAG-07 if
that packet adds a provenance artifact role. Do not edit goals/D1/roadmap,
invent backend-produced bytes, choose a Rust storage API, or run backend code.

Prefer a small representative materialized catalog plus explicit
`external-required` entries over fabricating bytes for every historical
placeholder. Do not silently relabel repeated placeholder hex strings as
verified content.

## Acceptance

- semantic identity and exact-byte integrity are distinct in schema, prose,
  fixtures, and validation;
- opaque semantic roots have one deterministic, role-separated derivation;
- every admitted locator has explicit resolution and availability semantics;
- referential and material replay closure are separately derived and tested;
- no synthetic path is treated as proof that bytes are bundled;
- the shared role table covers all supplied roots/outputs and reference
  metadata cannot contradict its catalog entry;
- unknown-byte placeholders are unbound requirements, not fake artifacts;
- all mandatory adversaries reject through schema or semantic validation;
- zero-backend and official Draft 2020-12 validation pass;
- no K, Java, Rust executor, compiler, backend, solver, or network fetch is
  run;
- checks are tiny and serial; and
- `git diff --check` passes.

## Stop rule

Stop rather than claiming external bytes exist, fetching network artifacts,
conflating semantic and storage hashes, weakening role separation, or choosing
the future Rust resolver/cache implementation.
