# R3-G-03: K-native `RuleApplied` head match

Status: activated implementation packet on 20 August 2026. The activation
commit containing this file is the worker base and must be recorded exactly.

## Why this is the next leaf

R3-G-02A accepted the complete pre-CF trace-cell clone composed with the
unchanged post-CF `RuleApplied` append. The firing execution now has one exact
typed event at trace index zero; the non-firing execution has an empty trace.
The next dependency is not another observer or more instrumentation. It is
proof that ordinary K matching can consume that accepted branch-local event
state and return a typed provenance witness.

This packet is the degenerate first ordered matcher: match one
`RuleApplied(RuleOrigin)` at the head of one concrete final trace. It does not
claim an ordered subsequence, `eventually-after`, `next-event`, shared payload
variables, a streaming monitor, or any absence result beyond an exhaustive
terminating concrete execution.

## Objective

Run one K-authored configuration pattern against the accepted composed
definition through pinned `krun --pattern --output json`:

```k
<trace>
  ListItem(ruleApplied(ruleOrigin(
    ID:String, LABEL:String, MODULE:String, SOURCE:String, LOCATION:String)))
  REST:List
</trace>
```

For the accepted firing input, K must return one substitution whose five
origin bindings equal the exact run-local accepted `RuleApplied` origin and
whose `REST` binding is `.List`. Project that validated substitution to one
checkout-stable witness at event index zero. For the accepted non-firing
input, K must return exact `#Bottom`.

Run a second K-authored pattern that constrains the label to a known unequal
string. The firing execution must also return exact `#Bottom`. This proves the
payload constraint belongs to K matching rather than to a host-side filter.

## Fixed inputs

- activation base containing this packet;
- accepted R3-G-02A integration and
  `draft/k-in-k-r3-g-02a-acceptance-checkpoint-2026-08-20.md`;
- accepted `spine/trace-configuration-composition/**` and
  `evidence/r3-g-02-k-authored-trace-configuration/**`;
- `draft/goal/execution-pattern-matching.md`, especially sections 2, 3.2,
  4.3, 5, and 8;
- the existing firing `p3/fixtures/program.exp` and accepted task-owned
  non-firing integer;
- K v7.1.337 at
  `4a46d1231473b599c699160132fd6e76a5c46406`; and
- the pinned Haskell backend.

External K remains read-only with exact expected status ` M pyk/uv.lock`.
Pin the activation packet, acceptance checkpoint, accepted composition spine
tree/evidence tree and critical files, inputs, projector sources, K frontend,
and toolchain revision before running.

## No new shared semantic contract

This packet uses official K pattern matching and official KAST JSON as a
bounded feasibility boundary. Its normalized `match`/`no-match` records are
task evidence, not a product compatibility schema. Do not introduce a new
K-in-K transformation contract, observer contract, monitor API, temporal
syntax, or general result protocol.

The pattern files are ordinary K patterns. K owns:

- matching the `<trace>` cell and head `ListItem`/`ruleApplied`/`ruleOrigin`
  constructor graph;
- binding all five typed `String` payload fields and the typed `List` tail;
- enforcing the wrong-label payload constraint; and
- returning a substitution or `#Bottom`.

The task-owned host projector owns only:

- exact KAST envelope/version/node validation;
- flattening official `#And`/`#Equals` substitution structure;
- requiring exactly one binding for each named pattern variable;
- allowing only official anonymous/generated completion variables besides
  those six names;
- typed token decoding, exact `.List` tail validation, and canonical JSON;
- comparison with the independently captured accepted runtime/driver record;
  and
- raw-validation-first portable witness projection and evidence capture.

It may not match a trace, search for an event, interpret pretty output, infer a
missing binding, choose fixture semantics, or turn malformed output into
`no-match`.

## Composition reuse

Do not copy or modify the accepted composition implementation. Invoke its
accepted replay script with a task-owned output directory so that it
regenerates and byte-compares the accepted evidence while leaving the accepted
spine build tree untouched. Consume only that task-owned replay's two fresh
composed definitions, runtime projections, and driver records.

Run the head, empty-trace, and wrong-label queries against both independently
compiled composition repeats. Raw query results must repeat byte-for-byte
within one checkout. The matcher adds no definition transformation and no
runtime transition.

## Match and witness invariants

For each firing repeat require:

- official KAST JSON `format`/`version` exactly as pinned;
- a conjunction of exact equality bindings, never `#Bottom`;
- `ID`, `LABEL`, `MODULE`, `SOURCE`, and `LOCATION` exactly once with sort
  `String` and canonical K string-token encoding;
- `REST` exactly once with sort `List` and value `.List`;
- no other non-anonymous pattern binding;
- exact raw five-field equality with the accepted composition driver target
  and runtime event origin;
- event index zero, constructor `RuleApplied`, and no remaining event; and
- equality across both fresh composition repeats.

Only after those checks, form the committed witness from the composition
driver's independently rederived portable target fields and compare it with
the accepted portable runtime event. Do not relabel the raw ID or source.
Committed evidence must contain no checkout root, raw official source, or raw
source-derived ID.

For both non-firing repeats and both wrong-label firing queries require the
exact official zero-argument `#Bottom{GeneratedTopCell}` KAST shape. A
malformed substitution is `error` at the projector envelope, never
`no-match`. In this finite concrete packet, `#Bottom` after normal termination
is evidence status `no-match`; do not generalize that statement to bounded or
symbolic exploration.

## Independent checks and required failures

The accepted composition replay remains the independent runtime,
ordinary-source, erasure, provenance, and instrumentation oracle. Add focused
projector self-tests or fixtures for at least:

- duplicate, missing, or unexpected named binding;
- wrong variable or token sort;
- malformed/noncanonical string token;
- non-empty or malformed `REST`;
- wrong raw origin field after an otherwise valid K substitution;
- malformed `#Bottom` and residual KAST content; and
- trailing JSON or an unsupported KAST version/node.

All projector failures occur after zero new compiler/backend invocations and
must be recorded as envelope errors, not semantic no-matches. The real empty
and wrong-label no-match queries are backend executions over already compiled
accepted definitions and must retain their normal successful invocation
status.

Use an independent trusted-small structural oracle over the official KAST JSON
to confirm that the five witness terms and empty tail occur in the actual K
substitution. Do not make the production projector validate itself by
re-encoding its own result.

## Evidence

Commit compact checkout-stable `results.json` and `report.md` under
`evidence/r3-g-03-k-native-rule-applied-head-match/`, including:

- activation revision, all pins and source hashes, cycle count, and verdict;
- exact K pattern texts/hashes and K/runtime ownership;
- official invocation modes and successful exit classification;
- positive `match` with portable five-field witness and event index zero;
- empty-trace and wrong-label `no-match` results;
- exact `.List` tail, constructor, binding sorts, and repeat invariants;
- explicit raw five-field validation with raw values omitted from committed
  evidence;
- projector failures and zero-extra-invocation evidence;
- inherited composition/runtime/erasure/provenance oracle hashes;
- limitations, ambiguity, and the recommended next ordered-matcher leaf.

Raw KAST, runtime, driver, and compiler output stays below the ignored
task-owned build tree.

## Ownership

The worker may modify only:

- `spine/rule-applied-head-match/**`;
- `evidence/r3-g-03-k-native-rule-applied-head-match/**`; and
- one new `r3:g:rule-applied-head-match` script entry in `package.json`.

Tasks, roadmaps/checkpoints/loop/goal/ADR files, accepted spines/evidence,
P1/P2/P3 fixtures, lockfiles, and external K are read-only. Generated output
must not be placed in an accepted spine's build directory.

## Acceptance

From a clean isolated worktree with no pre-existing task build output:

```sh
bun run r3:g:rule-applied-head-match
bun run check
git diff --check
```

Replay must regenerate and byte-compare both evidence files, fail closed on
every pin/envelope mismatch, and run the accepted composition replay into the
new task's build tree. Root repeats all commands from a fresh
workspace-aligned detached worktree at a different absolute path before
integration.

The worker gets at most three substantive full-oracle cycles. A retry caused
solely by an ephemeral session or environmental disk failure does not consume
a cycle if source/evidence did not change.

## Stop/split rule

Stop and return evidence instead of expanding if acceptance requires:

- modifying or weakening the accepted composition, configuration, trace, or
  official hook/adapter boundary;
- parsing pretty-printed execution output or matching/searching in the host;
- a new shared semantic contract, runtime cell, transition, event constructor,
  instrumented rule, or definition transformation;
- more than one runtime event, an event not at index zero, or a non-empty tail;
- temporal operators, subsequence scanning, alternatives, shared variables,
  domain events, a monitor, corpus aggregation, symbolic execution, search,
  solver reasoning, `unknown`, or universal/no-path claims;
- external-K modification, backend-log dependence, general `SemanticInput`,
  C1, or C2; or
- inability to distinguish exact K substitution from exact `#Bottom` through
  official KAST JSON without an ad-hoc semantic parser.

## Return contract

Return one clean worker commit and report activation/start revision, cycle
count, exact patterns, K/host ownership, positive witness, both no-match
classes, raw/portable validation, repeat and inherited oracles, failure
coverage, commands, evidence hashes, limitations, ambiguity, and whether the
next ordered-subsequence packet is dependency-unblocked. Do not claim root
replay or integration.
