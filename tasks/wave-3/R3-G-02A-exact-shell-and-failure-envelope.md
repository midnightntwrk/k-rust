# R3-G-02A: exact cloned shell and failure envelope repair

Status: activated repair packet on 19 August 2026. The activation commit
containing this file is the accepted base. Root imports stopped prototype
commit `478ea271f7295e8eed4bafd6ea4fd13a5fbe1ffc` as the first branch-only
commit before delegation; the worker must record the resulting starting
revision.

## Why this packet exists

R3-G-02 completed three full-oracle cycles and produced a semantically working
composition, but root audit found two fail-closed gaps. K and Java accepted a
same-name `.List` trace cell without proving it was the complete expected clone
of the declared template shell, and Java accepted configuration failure results
without validating their schema/reason/count semantics.

Preserve the stopped result; do not count another R3-G-02 cycle. This repair is
a narrower contract-hardening cycle. It adds no capability and does not change
the accepted post-CF contract.

## Objective

Make `KTraceConfigurationAugmentation-v1` own exact apply/already-present/
conflict status over the complete expected cloned shell, and make the Java host
reject every malformed or semantically invalid configuration failure result at
the envelope before classification or transformation.

Retain the exact typed nullary `.List : List` initializer, paths, immutable
application, identity baseline, official CF, unchanged `KRuleAppliedTrace-v1`,
runtime/erasure/source/repeat oracles, checkout-stable evidence, and all prior
failures.

## Starting inputs

- activation base containing this packet;
- stopped prototype `478ea271f7295e8eed4bafd6ea4fd13a5fbe1ffc`, imported by
  root onto the repair branch;
- `tasks/wave-3/R3-G-02-k-authored-trace-configuration.md` as the unchanged
  capability contract and three-cycle record;
- `draft/k-in-k-r3-g-02-audit-checkpoint-2026-08-19.md`;
- accepted R2-G-06 and R3-G-01A contracts/evidence; and
- K v7.1.337 at `4a46d1231473b599c699160132fd6e76a5c46406`.

External K remains read-only with exact expected status ` M pyk/uv.lock`.

## Repair 1: complete expected-clone equality

For the declared template, name, and initializer, the expected trace cell is
the exact structural clone that application would construct:

- the same four-argument `#configCell` application label and node metadata;
- start/end name tokens with only their string values changed to the declared
  name, preserving token sort and attributes exactly;
- the template properties term and its complete typed subtree by identity/
  structure, including metadata;
- the declared typed initializer as the body; and
- no other shell, property, token, or metadata change.

K must derive apply/already-present/conflict from projected typed structure:

- `apply` only when the structural target exists and no same-name cell exists;
- `already-present` only when exactly one same-name cell equals that complete
  expected clone; and
- conflict when any same-name cell has different body, shape, properties,
  name-token typing/attributes, application metadata, or other node metadata.

Java must independently construct the expected clone from only the declared
template/name/initializer, require exactly one same-name cell at the declared
parent, and require that cell to be the one complete structural match. Use the
same complete comparator in post-application delta validation and pass-2
idempotence validation. It may compare canonical typed structure only after
validating the declared paths and exact official descriptors. A name/body-only
counter is insufficient. Java still may not choose or search for fixture
semantics.

Add two focused failures:

- `config-conflict-shape`: a same-name cell with the exact resolved `.List`
  initializer but a generically altered property term must produce K failure
  `conflicting-existing-state` with count one; and
- `config-false-already-shape`: force an `already-present` result over that
  altered shell and require independent Java expected-clone rejection.

Add trusted-small comparator self-tests that independently mutate properties,
start/end token sort or attributes, and top-level application/node metadata;
each must compare unequal. Both compiler negatives have zero configuration
applications, zero post-CF calls, and no backend artifacts.

## Repair 2: closed failure-envelope semantics

Every parsed `cTraceAugmentationFailure` must be validated before its reason is
used. Require:

- schema exactly `KTraceConfigurationAugmentation-v1`;
- reason in the closed set emitted by this contract:
  `structural-target-cardinality`, `initializer-descriptor-cardinality`, or
  `conflicting-existing-state`;
- a canonical nonnegative integer count;
- structural-target and initializer-descriptor counts not equal to one; and
- conflict count greater than zero.

The injected one-conflict oracle must additionally require the exact expected
count of one. Unknown schema/reason, negative count, and invalid reason/count
relationships are envelope failures, not selection/conflict classifications.

Add actual K-authored negative modes `config-failure-wrong-schema`,
`config-failure-unknown-reason`, and `config-failure-invalid-count`, using a
canonical negative integer for the invalid count. Extend Java semantic
self-tests for structural/initializer count one and conflict count zero. They
must fail before configuration application, transformed-definition return,
post-CF invocation, or backend artifacts. Retain all canonical parser tests.

Use one shared failure validator from both ordinary result handling and the
conflict helper. Evidence must enumerate the actual malformed-failure records;
do not synthesize their outcomes.

## Repair evidence

Record one raw expected-clone fingerprint and installed-cell fingerprint and
require equality. Independently rederive portable expected/installed
fingerprints from repository-logical metadata and require equality there too.
Pass 2 must validate one full clone and return the same `Definition` reference
with zero further applications. Fresh repeats compare both raw and portable
clone fingerprints.

Record both content-conflict and property/shape-conflict outcomes, all three
malformed failure records, their exact classifications/counts, and filesystem-
derived artifact absence. Pre-CF negative output directories contain no
staging/backend files. Unchanged post-CF negatives retain only their pinned
frontend staging allowance and no backend artifacts.

## Frozen behavior and ownership

No new contract, operation, hook, adapter, fixture capability, or host boundary
is allowed. Keep:

- `KTraceConfigurationAugmentation-v1` as the sole repaired contract;
- unchanged copied `KRuleAppliedTrace-v1` K semantics and post-CF behavior;
- K ownership of target/cardinality/status/conflict, paths, name, and exact
  typed initializer;
- Java ownership of canonical projection/parsing, exact descriptor/path and
  expected-clone validation, immutable rebuild, and delta/idempotence checks;
- the two-cell fixture and ordinary-source event syntax;
- raw-validation-first portable evidence, structural oracle/payload rendering,
  collision/residual checks, and portable ordering; and
- every positive, identity, runtime, erasure, ordinary-source, repeat,
  provenance, literal-scan, pre-CF, and post-CF oracle from the prototype.

The repair worker may modify only:

- `spine/trace-configuration-composition/**`;
- `evidence/r3-g-02-k-authored-trace-configuration/**`; and
- the existing `r3:g:trace-configuration` package entry only if strictly
  necessary.

Tasks, roadmaps/checkpoints/loop/goal/ADR files, accepted spines/evidence,
P1/P2/P3 fixtures, lockfiles, and external K are read-only.

## Acceptance

From a clean repair worktree with no pre-existing build output:

```sh
bun run r3:g:trace-configuration
bun run check
git diff --check
```

Replay must regenerate and byte-compare both evidence files, record the repair
cycle count separately from R3-G-02's frozen count of three, and fail closed on
all pinned inputs. Root repeats all commands from a fresh workspace-aligned
detached worktree at a different absolute path.

The worker gets at most two substantive repair cycles. Stop again if exact
shell equality cannot remain one operation/one edit, if failure validation
requires a new contract/boundary, or if acceptance would change the post-CF
contract, runtime payload, event/configuration syntax ownership, external K,
matcher/domain/symbolic scope, or any prior portable evidence invariant.

## Return contract

Return one clean repair commit after the imported prototype. Report activation,
prototype, starting revision, repair cycles, exact shell equality, closed
failure grammar/count rules, new negative classifications/artifact absence,
unchanged initializer/event/idempotence/runtime/erasure/source/repeat evidence,
commands, evidence hashes, limitations, and whether R3-G-02 can integrate.
Do not claim root replay or integration.
