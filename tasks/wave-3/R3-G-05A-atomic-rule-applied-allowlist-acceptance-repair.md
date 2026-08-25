# R3-G-05A: atomic allowlist acceptance repair

Status: acceptance-repair packet. The static prototype is worker commit
`ad22549` over activation `22af27d`. It has never run a K/Java/full-backend
oracle and is not accepted. The worker base is the repair-activation commit
created by cherry-picking this packet onto `ad22549`; record the exact supplied
base revision before editing.

## Why repair instead of replay

A fresh read-only Sol audit rejected the static prototype before a backend
cycle. The prototype has useful exact-two and one-traversal scaffolding, but it
does not yet satisfy the packet's K/host authority boundary, real idempotence,
cache integrity, or artifact/resource isolation. Do not spend a substantive
oracle cycle until every defect below is closed statically.

This packet repairs only `R3-G-05`. It does not add domain events, temporal
matching, symbolic execution, mutation behavior, a general allowlist, C1, or
C2.

## Required semantic repairs

### 1. K owns the complete typed operation

Revise the unaccepted `KRuleAppliedAllowlist-v1` result so each member's one
`appendGeneratedCellTerm` operation explicitly carries everything the host
uses to validate and construct the edit:

- the exact non-root parent path to the official `#cells` insertion point;
- the complete selected generated trace-cell descriptor, including name,
  label, cell/body sorts, production identity/fingerprint, and metadata
  fingerprint;
- every required parent/cell/marker and event-payload production descriptor,
  including module, label, result/argument sorts, production fingerprint,
  label fingerprint, and metadata fingerprint;
- the fresh variable, before term, after term, and complete five-field witness;
  and
- K-authored canonical result-identity material that binds schema,
  transformation, definition fingerprint, count, homogeneous status, canonical
  member order, both targets, and both operations. The host may hash the exact
  parsed canonical identity, but may not invent or omit identity fields.

K must derive those fields after recognizing the supported structural rule
shape and the unique typed metadata. Java may only resolve each complete
descriptor by exact equality and cardinality one. It may not search by cell
name, infer marker constructors from an existing term, choose a parent, fill a
descriptor, or construct a payload omitted by K.

Remove the root `cSequence(KCELL, STATECELL)` positive candidate. Supported
fresh and already-present shapes must yield valid non-root paths whose resolved
parent is exactly the K-declared typed `#cells` insertion point. Unsupported
root/bare/ambiguous shapes must be K failures or zero-candidate results, never
an `apply` result that Java later rejects.

### 2. Exact fail-closed existing instrumentation

K's `already-present` matcher must compare the complete typed graph emitted by
the operation: metadata at every relevant node, exact production descriptors,
sorts, marker terms, variable, rewrite, append/singleton/event/origin graph,
five string payloads, and literal surrounding shape. A same-label wrapper,
wrong metadata, wrong sort, wrong markers, extra payload, or partial graph is a
conflict.

Java must independently validate that same complete graph by exact descriptor,
attributes, arity, child placement, and typed term equality. Label/arity plus
middle-rewrite counting is insufficient. Delete or narrow any broad
`any-exact-trace` rule that suppresses conflict for malformed instrumentation.

Add generic first-member and second-member failures for wrong cell metadata,
wrong parent/cell/marker production, wrong marker term, wrong event/origin
production, wrong payload, wrong variable/sort, partial graph, duplicate graph,
and extra graph. Every case applies zero edits and constructs no output or
backend artifact.

### 3. Exercise the real pair transaction twice

Factor one host operation that accepts any input `Definition` and one parsed K
pair outcome:

- `apply`: prepare both replacements against the same original definition,
  then perform one exact-two transformer traversal;
- `already-present`: independently validate both complete existing operations,
  perform zero transformer traversals and zero applications, and return the
  exact input `Definition` reference; and
- mixed, false, stale, duplicate, overlap, conflict, or partial: reject with
  zero applications and no output definition.

The positive oracle must invoke that operation once on fresh input and again on
the transformed output. Record independent first/second call counters,
statuses, validation counts, application counts, transformer traversal counts,
input/output identity checks, and returned-reference checks. Do not set
same-reference flags merely because a local variable is returned.

Forced preparation failure for either member must still prove that no
transformer traversal or externally visible definition occurred.

## Evidence and cache integrity repair

The raw action may write only beneath one canonical, ignored task build
directory. Resolve the output and task-build paths physically; reject `..`,
symlink, or prefix tricks. Raw mode must not write committed evidence.

At raw success, create a deterministic integrity manifest binding:

- every semantic input and accepted source/tree pin;
- every driver record, parser/runtime self-test record, runtime projection,
  normalized/focused/full Kore comparison input, log needed for a claim, and
  repository/external-K before/after snapshot; and
- provisional `results.json` and `report.md` generated under the raw build.

Cache finalization must first validate the manifest and all current semantic
input hashes. It must validate actual fields in every failure record: rejected
status, classification, zero applications, zero traversal, no output
definition, and no backend construction. Parser canonicality tests must emit a
structured record with exact cases and zero-backend facts; log existence alone
is not evidence.

Snapshot the repository with untracked files included and the external K tree
before and after raw execution; require exact equality. Artifact absence claims
must be derived from those snapshots and explicit expected-path scans, not
hard-coded. A separate zero-backend publish step may copy manifest-validated
provisional evidence from the ignored build into the owned committed evidence
directory. Reporting-only repairs regenerate and republish from the same
validated raw cache without compiler/backend work.

Routine `verify.sh` remains zero-backend and validates all committed source and
evidence hashes, schemas, exact failure sets, resource facts, report hash, and
static authority witnesses. It must fail while evidence is absent.

## Whole-oracle resource boundary

The prior workstation OOM was not caused by an R3-G-05 raw run, but it makes a
whole-oracle guard mandatory. Keep the existing nonblocking global lock,
serial execution, `nice`, two-CPU affinity, explicit root authorization,
1536 MiB/two-processor defaults, 2048 MiB/two-processor hard maxima, inherited
Java-option rejection, and pre-JVM memory/swap refusal.

In addition, raw mode must run in a dedicated session/process group and enforce
a lightweight whole-session pressure watchdog. At least once per second it
must sum resident memory for the oracle session and terminate the entire
session before it exceeds 6 GiB RSS, before system available memory falls below
4 GiB, or before swap free falls below 1 GiB. Record the thresholds, peak
observed session RSS, and whether the watchdog fired. Require a bounded
wall-clock timeout. The watchdog and timeout must not apply to zero-backend
finalize/publish modes.

No K, Java, compiler, or backend command may run until the worker sends root
the exact guarded command, root rechecks live memory/swap and unrelated
K/Lean processes, and root explicitly authorizes that exact invocation. Never
replay an accepted ancestor or use LLVM.

## Required zero-backend repair tests

Before proposing a raw command, prove without K/Java/backend processes:

- canonical output resolution rejects traversal and symlink escapes;
- raw mode refuses missing authorization, exhausted-resource fixtures, a
  non-dedicated session, conflicting Java options, lock contention, and an
  existing output;
- a synthetic watchdog process tree exceeding its tiny test threshold is
  terminated without touching unrelated processes;
- cache finalization rejects every single-file manifest mutation, missing
  record, nonzero failure counter, changed semantic input, and malformed parser
  self-test record;
- publish refuses unvalidated or stale provisional evidence;
- K/Java static scans witness the complete descriptor/result identity fields,
  exact existing graph, real two-call host operation, and absence of Java
  fixture selection; and
- shell/Python syntax, task-local adversarial tests, package entry, and
  `git diff --check` pass.

These tests must use temporary task-owned or `/tmp` paths and clean up only
their own explicit files.

## Ownership

The repair worker may modify only:

- `spine/rule-applied-allowlist/**`;
- `evidence/r3-g-05-atomic-rule-applied-allowlist/**`; and
- the existing `r3:g:rule-applied-allowlist` entry in `package.json`.

The worker must not edit this packet, accepted spines/evidence, roadmaps,
checkpoints, lockfiles, external K, or any other package entry.

## Acceptance and stop rule

Return one or more clearly ordered repair commits, with a final clean worker
head. The full-oracle cycle count is still zero at activation. At most three
substantive R3-G-05 full-oracle cycles are allowed.

After one guarded successful raw run and zero-backend publication, these must
pass from the worker and integrated trees without compiler/backend processes:

```sh
bun run r3:g:rule-applied-allowlist
bun run check
git diff --check
```

Stop with a new checkpoint instead of broadening if repair requires a second
shared contract, sequential unary edits, Java-owned selection/construction,
more or fewer than exactly two targets, an accepted-source change, an oracle
above the resource ceilings, or scope beyond R3-G-05.

The return report must distinguish static repair, raw cycle provenance,
published evidence, limitations, and root integration status. Do not claim
R3-G-05 acceptance, R3-G exit, or typed domain events before root review.
