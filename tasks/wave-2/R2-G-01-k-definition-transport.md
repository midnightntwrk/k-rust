# R2-G-01: K-facing definition identity/provenance transport

Status: accepted on 19 August 2026 against the pinned K toolchain.

## Objective

Establish the smallest versioned K-facing definition transport that lets a K
semantics receive a supported subset of the lossless official definition as
typed data, preserve identity/provenance, and return an identity result through
`OfficialDefinitionAdapter v1`.

This packet introduces at most one shared contract: the minimal K-facing
transport. It does not freeze the full `SemanticInput v1`, add general patch or
transaction semantics, implement observation/mutation features, or own
official lowering.

## Starting inputs

- the root revision containing this packet;
- `draft/decisions/official-definition-adapter-v1.md`;
- W1-D's driver, replay, records, and structural oracle;
- the Peano and P3 fixtures; and
- the pinned toolchain and Haskell-backend profile.

## Required supported subset

Represent only what is required to preserve and select the supported source
semantic sentences in Peano and P3:

- module and import identity;
- sentence kind and deterministic module-local occurrence;
- rule body, `requires`, and `ensures` as typed K terms;
- sentence attributes required by the fixtures;
- sort/production metadata required to preserve those terms;
- source, location, optional label, and adapter lineage; and
- deterministic input/content fingerprints.

Anything not faithfully represented must remain attached to the original
official object and pass through unchanged. Do not grow the transport merely
to anticipate Kore emission or C1.

## Required behavior

1. Project the supported subset from the lossless in-memory official
   `Definition` without KAST JSON/source round-tripping.
2. Invoke a K semantics over that typed projection.
3. Have the K semantics perform identity plus one deterministic structural
   selection of the P3 `start-program` rule.
4. Return a typed identity/selection result to the adapter.
5. Validate lineage and content fingerprints against the original definition.
6. Return the original official definition unchanged for identity.
7. Continue through official lowering, Kore emission, and execution.
8. Reject at least stale lineage/content and unexpected selector cardinality
   at a named pre-backend boundary.

The TypeScript/Java host may orchestrate transport and validation, but it may
not implement the structural meaning of the K selection.

## Owned paths

The activated packet owned:

- `spine/definition-transport/**` for the versioned transport, adapter driver,
  and deterministic replay;
- `evidence/r2-g-01-definition-transport/**` for compact accepted evidence;
- this packet for activation and closeout;
- the `r2:g:transport` entry in `package.json`; and
- the narrow generated-build exclusions in `.gitignore`.

Existing investigations, goals, official K, and unrelated production paths
remained read-only. The execution roadmap received only a checkpoint update.

## Acceptance command

From a checkout without an existing
`spine/definition-transport/build/replay` directory, run:

```sh
bun run r2:g:transport
```

The checked-in command:

- builds the adapter and K transport semantics;
- runs Peano and P3 identity;
- verifies the K-authored structural selection;
- verifies lineage/content validation failures;
- compares the scoped normalized Kore and runtime oracles; and
- emits a compact machine-readable manifest at
  `spine/definition-transport/build/replay/results.json`.

The accepted evidence snapshot is in
`evidence/r2-g-01-definition-transport/`.

## Accepted implementation boundary

`KDefinitionTransport-v1` projects supported source rules from the lossless
in-memory official `Definition` into typed K data. The K module owns the
structural `start => add(read(), bump())` selection and returns typed lineage,
content, and body fingerprints. The Java adapter validates that result against
the original official objects at `post-k-selection-pre-backend` and returns the
same `Definition` reference for identity.

The adapter does not reconstruct a definition from transport data, consume
official `parsed.json`, apply patches, or own official lowering. Peano is the
zero-selection control; P3 provides the one-selection case. Stale lineage,
stale content, and unexpected selector cardinality are rejected before backend
Kore emission.

## Stop rule

Stop and split the packet if it requires:

- a second shared contract such as canonical patches;
- full-definition reconstruction from the transport;
- pre-CF configuration augmentation;
- general source formatting;
- independent official frontend passes or Kore emission; or
- broader sentence/term coverage than Peano and P3 require for identity and
  selection.
