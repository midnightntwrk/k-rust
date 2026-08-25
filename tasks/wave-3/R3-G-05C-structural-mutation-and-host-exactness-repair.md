# R3-G-05C: structural mutation evidence and host exactness repair

Status: third static acceptance repair. The rejected R3-G-05B implementation
is clean commit `2927325e98267aebed07dd41ef9add5949119ea8`; no R3-G-05
K, Java, compiler, or backend oracle has run, so the substantive full-oracle
cycle count remains zero. Cherry-pick this packet onto that commit and record
the resulting exact repair activation before editing.

## Why cycle 1 remains unauthorized

The R3-G-05B K authority is structurally sound enough to retain: K constructs
the expected existing trace graph from independently projected authority and
compares it by exact term equality. Two host/evidence defects still make the
current static green result a false positive.

First, `mutation_sensitivity.py` mutates a standalone flat dictionary that is
not connected to `constructMalformedExistingInput`. Cached validation trusts a
claimed field name plus opaque whole-rule hashes. Java then includes that
claimed field and member index in `mutationFingerprint`, so two aliases can be
made artificially distinct. Several branches also erase a complete `Att` to
claim a single production defect, changing sort, production, and metadata
together.

Second, Java's independent `already-present` validation compares rewrite
children but not rewrite metadata. The wrong-rewrite negative exits as soon as
K reports conflict, so it never establishes the required independent host
rejection.

Do not run the proposed guarded command from `2927325`.

## Required structural mutation repair

Bind every malformed-existing claim to the actual typed graph constructed by
Java. Introduce a task-owned structured existing-graph snapshot/projection
that is derived from the real prepared or constructed K term, not from the
defect name and not from a parallel synthetic dictionary.

For each of the 25 fields and both member positions:

- snapshot the exact valid trace graph before mutation;
- construct the named mutation through the production mutator;
- re-project the actual malformed graph after construction;
- compute the changed structured-field paths from those two projections;
- require the changed-field set to equal exactly the one field declared for
  the case (or an explicitly modeled structural graph operation for partial,
  duplicate, and extra);
- record per-field before/after canonical values or hashes plus whole-graph
  before/after hashes; and
- derive the mutation fingerprint from the actual member-independent
  structural delta and graph hashes. Do not salt it with the claimed defect
  name or member index merely to manufacture uniqueness.

The committed/raw validator must recompute or validate that structured delta,
reject a mismatched field claim, reject aliases that produce the same actual
delta, and require the exact 50-case matrix. A static checker may inspect
source witnesses, but a toy data model unshared with the production mutator is
not evidence.

Make each primitive mutation narrow. A production mutation must replace only
the selected production authority while preserving the independently declared
sort and metadata fields, or else name the actual more-specific field being
changed. A metadata mutation must preserve production and sort. Marker term,
variable, token, payload, partial, duplicate, and extra cases must likewise
project to their exact declared structural delta. Do not use fixture label
searches or source parsing to choose or construct mutations.

## Required independent host repair

Java's complete existing-graph validator must compare the same authority as K
without depending on K's classification. At minimum it must compare:

- operation-root and both parent layers, including exact metadata and child
  placement;
- generated cell and both markers, including terms, productions, sorts, and
  metadata;
- rewrite left, right, sort, production fingerprint, and metadata fingerprint;
- variable name, sort, and metadata;
- append, singleton, event, and origin production descriptors and metadata;
- all five token sorts, metadata, payload values, and literal placement; and
- exact absence of partial, duplicate, and extra graph members.

Add a host-only validation path/test for each structured malformed graph that
is reached even when K correctly reports conflict. Every case must prove that
the independent host validator also rejects it with zero pair transaction,
zero applications, zero transformer traversals, and no output/backend
construction. Record both `kConflictBeforePairTransaction` and
`hostIndependentRejection` as distinct facts.

## Static audit and oracle hold

Extend the zero-backend acceptance checks to reject `2927325` specifically:

- reject whole-rule-only mutation fingerprints and fingerprints salted by the
  declared field/member;
- reject a synthetic checker that is unbound to the real Java graph
  projection/mutator;
- require actual structured before/after field deltas and alias rejection;
- reject `Att.empty()` as a broad substitute for a one-field production or
  metadata mutation;
- require rewrite metadata in `countExactGeneratedUpdates` or its replacement;
  and
- require independent host rejection evidence for every one of the 50 cases.

Retain and rerun the accepted cache/path/watchdog/refusal tests, shell/Python
syntax, configuration-copy check, package assertion, and `git diff --check`.
Do not run K, Java, `javac`, `kompile`, `krun`, a backend, or Bun. Return a
clean static repair commit and a newly bound exact guarded command. Root will
perform a complete diff audit and commission another fresh read-only audit
before deciding whether cycle 1 is authorized.

## Ownership and stop rule

Ownership remains only:

- `spine/rule-applied-allowlist/**`;
- `evidence/r3-g-05-atomic-rule-applied-allowlist/**`; and
- the existing `r3:g:rule-applied-allowlist` package entry.

Do not edit this packet, accepted artifacts, checkpoints/roadmaps, lockfiles,
or external K. Preserve the R3-G-05B K-owned exact authority unless a narrowly
necessary correction is found. Stop rather than weaken exact classification,
invent evidence from names, add a second contract, or broaden beyond R3-G-05.
