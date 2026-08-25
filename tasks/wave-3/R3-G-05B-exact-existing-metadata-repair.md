# R3-G-05B: exact existing-metadata and negative-sensitivity repair

Status: second static acceptance repair. Base implementation is clean worker
head `f14366a`; no R3-G-05 K/Java/compiler/backend oracle has run, so the
substantive cycle count remains zero. The worker base is the activation commit
created by cherry-picking this packet onto `f14366a`; record the supplied exact
revision.

## Residual blockers

Do not run the proposed cycle-one command from `f14366a`.

First, K's `#oIsExactTrace` binds metadata variables but validates them only
with `#oMetaComplete`, which checks for nonempty fingerprints. It does not prove
that cell, marker, append, singleton, event, origin, token, variable, rewrite,
or parent metadata equals the independently K-declared operation authority.
Consequently a wrong-but-nonempty typed graph can still be classified
`already-present` by K and rejected only later by Java.

Second, `malformedExistingNegative` accepts a requested defect name but always
constructs the same single-member bad before/before rewrite. The named wrong
cell, parent/cell/marker/event/origin production, marker term, payload,
variable/sort, partial, duplicate, and extra graph cases therefore do not
exercise distinct mutations. Classification strings and a large record set are
not mutation sensitivity.

## Required repair

### Exact K-owned metadata comparison

Represent enough generic typed metadata in the task-owned v1 input/operation
contract for K to construct an expected complete existing trace graph without
copying metadata from the candidate graph being classified.

At minimum, the expected graph must independently bind and compare:

- official operation-root/parent and generated-cell metadata;
- left/right marker productions, terms, and metadata;
- append, singleton, event, and origin productions and metadata;
- rewrite metadata;
- fresh variable name, sort, and metadata;
- every String token sort and metadata; and
- all five exact payload strings and literal child placement.

Production-bearing `CMeta` values must equal the selected `OProduction` result
sort, production fingerprint, and metadata fingerprint, not merely be
nonempty. Non-production term metadata must come from an independent generic
convention/table projected in the request or be derivable from the typed
operation; K may not accept and echo candidate metadata as its own authority.

The same expected authority must be carried in each result operation and
validated exactly by Java. If this needs one additional field or table inside
the still-unaccepted `KRuleAppliedAllowlist-v1` request/result, that is allowed;
do not create a second contract or change accepted shared sources.

K must return `already-present` only for the complete exact graph and
`conflicting-existing-state` for every wrong metadata/graph case. Java remains
an independent complete validator rather than the owner of classification.

### Distinct mutation sensitivity

Implement a separate generic mutation for every required first/second case:

- wrong generated-cell descriptor metadata;
- wrong parent production;
- wrong cell production;
- wrong left/right marker production;
- wrong left/right marker term;
- wrong append/singleton/event/origin production;
- wrong rewrite, variable, token sort/metadata;
- wrong one of the five payload fields;
- partial graph;
- duplicate graph; and
- extra graph.

The test record for each case must state the mutated structural field and carry
before/after mutation fingerprints. Require all mutation fingerprints to be
distinct except an explicitly justified first/second symmetry pair. Prove that
each mutation changes the intended typed field and that K returns conflict
before the pair transaction. Application count, transformer traversal count,
output-definition construction, and backend construction remain zero.

Do not use fixture label searches or source parsing to create mutations.

## Static audit and oracle hold

Extend the zero-backend acceptance checker so it fails the `f14366a` pattern:

- forbid `#oMetaComplete` as the sole condition in exact existing matching;
- require exact metadata-to-authority comparison witnesses for every node kind;
- require the defect argument to select distinct mutation implementations;
- generate synthetic structured graphs proving each distinct mutation changes
  only its intended field; and
- reject duplicate mutation fingerprints or generic aliases.

Retain and rerun the accepted cache/path/watchdog/refusal tests, shell/Python
syntax, configuration-copy check, package assertion, and `git diff --check`.
Do not run K, Java, `javac`, `kompile`, `krun`, a backend, or Bun. Return a clean
static repair commit and a newly computed exact guarded command; root will run
a fresh read-only audit before deciding whether to authorize cycle 1.

## Ownership and stop rule

Ownership remains only:

- `spine/rule-applied-allowlist/**`;
- `evidence/r3-g-05-atomic-rule-applied-allowlist/**`; and
- the existing `r3:g:rule-applied-allowlist` package entry.

Do not edit this packet, accepted artifacts, checkpoints/roadmaps, lockfiles, or
external K. Stop rather than weaken K-owned classification, collapse negatives
to aliases, add a second shared contract, or exceed R3-G-05 scope.
