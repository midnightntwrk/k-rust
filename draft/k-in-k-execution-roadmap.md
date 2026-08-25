# Modern K-in-K: execution roadmap

Status: redirected on 22 August 2026 after the terminal R3-G-05 stop and the
planned Rust-stack transition.

The old official-K/Java/Haskell G-track implementation is stopped. Its bounded
accepted evidence remains valid only at the scopes stated below. Active work
is the backend-agnostic closure package at
`investigations/backend-agnostic-goal-closure/`; the future implementation
order is its `rust-stack-handoff.md`. No current-backend R3/R4 leaf is active.

The active objective is broader than producing either of those documents:
exhaust every reasonably valuable investigation for the two product goals
whose answer is independent of the future execution stack. The closure package
and Rust handoff are evidence and durable outputs of that investigation, not
the objective itself. Closure is justified only when each remaining material
uncertainty inherently requires Rust/backend execution or measurement, or a
genuine product decision. This avoids both rebuilding portable reasoning in
the new stack and spending effort on conclusions tied to the retired stack.

The remainder of this document preserves the original controlled build
sequence and its accepted evidence. Where that historical sequence conflicts
with the active objective above, the backend-agnostic closure objective and D1
supersede it.

The evidence behind this roadmap is in:

- `draft/k-in-k-complexity-plan.md`;
- `draft/k-in-k-oracles.md`;
- `draft/k-in-k-probe-p1.md`;
- `draft/k-in-k-probe-p2.md`;
- `draft/k-in-k-probe-p3.md`.

The end-product motivations that this compiler architecture is intended to
support are specified separately in `draft/goal/README.md`: execution
semantic-pattern matching and transactional semantic mutation testing.

## 1. Direction

The reconnaissance originally assumed that the next decisive outcome was
K-in-K-emitted Kore. The product goals do not imply that assumption. Both
execution-pattern matching and semantic mutation testing first require a
smaller common capability: represent a parsed K definition as typed data and
transform it with K rules while preserving identity and provenance.

Use one immediate product track and retain the original compiler-independence
track behind an explicit decision gate.

### Delivery G1: definition-transformation kernel behind adapters

Use official K initially for parsing, remaining frontend lowering, Kore
emission, and backend execution. K-in-K owns:

- the versioned semantic-definition IR;
- K-authored structural selection over semantic sentences;
- conservative observation instrumentation and branch-local K monitors;
- canonical, atomic single- and multi-sentence mutation patches; and
- provenance, validation, replay, and transformation manifests.

G1 is successful when an identity transformation and both goal vertical slices
round-trip through official K with deterministic, behaviorally validated
results. G1 is still genuine K-in-K: K definitions are represented as data and
rewritten by K. It does not claim independent compilation.

### Decision D1: product kernel or independent compiler

After G1, decide from evidence whether to continue primarily as a
definition-transformation product, take ownership of selected frontend stages,
or pursue the complete compiler-independence track below. Independent Kore
emission must be justified as an explicit research/product objective or by a
demonstrated limitation of the adapter path; it is not a proxy for generality.

### Delivery C1: semantic frontend behind a parsing adapter

This retains the roadmap's original L1. Target F1 semantic compilation for the
pinned Haskell-backend Kore profile. Use a replaceable adapter for generalized
parsing, disambiguation, and sort inference. Implement the meaning-bearing
lowering stages and Kore generation explicitly, with selected F2 artifacts
used as oracles.

C1 is successful when its own emitted Kore, rather than official K's Kore,
passes representative execution and proof checks. It is not an independent K
frontend while parsing remains trusted.

### Delivery C2: independent parser-enabled frontend

This retains the roadmap's original L2. Replace the parser adapter with an
independently implemented grammar, scanner, parse forest, disambiguation, and
inference pipeline. Begin this only after C1's semantic IR and downstream
behavior are stable and parser-filter observation seams exist.

F2 artifact parity and F3 product parity remain separately selectable targets.
They are not silently included in any delivery.

### First-principles guardrails

Goal alignment should shorten feedback, not hard-code the motivating examples.
Therefore:

- the core IR contains K sentences, terms, conditions, attributes, and
  provenance—not memory-specific concepts;
- event vocabularies and mutation operators live in separate user modules;
- patterns use K-native, branch-local observation state (option (b)); backend
  or debugger traces are optional oracles, never the product interface;
- official-K ingress and egress remain replaceable adapters with recorded trust
  boundaries;
- identity, erasure, and structural-diff oracles test transformations
  independently of the motivating features; and
- at least two structurally different fixtures must cross a shared contract
  before that contract is called general.

This revision does not decide that thin K-in-K is the final architecture, that
independent compilation lacks research value, or that these two features are
the only future uses. It changes the order of evidence: first validate the
shared definition-rewriting idea, then buy additional compiler ownership only
with a named reason. If R1 shows that official-K egress is fundamentally
unsuitable, hold an early D1-style decision rather than forcing R2-G or jumping
silently to C1.

## 2. Decisions to lock before production implementation

The following decisions are defaults unless evidence from the first two waves
invalidates them.

| decision | default |
| --- | --- |
| Compatibility pin | K v7.1.337 at `4a46d1231473b599c699160132fd6e76a5c46406` |
| Backend profile | Haskell-backend Kore, one explicit option profile |
| First parser boundary | Replaceable official-K parsed-KAST adapter |
| Immediate product boundary | K-authored transformation of parsed semantic-definition IR |
| Downstream compiler in G1 | Official K behind a replaceable egress/compilation adapter |
| Implementation host | K for semantic transformations; TypeScript for adapters, orchestration, comparison, and evidence capture |
| Primary acceptance | Stage-local structural differential plus an independent invariant or backend behavior |
| First corpus | Feature isolates, then Peano/Foobar and a small integrated IMP-like language |
| Execution-pattern architecture | Option (b): definition instrumentation plus branch-local K monitor state |
| Backend/debugger traces | Optional experimental and differential oracles; not a compatibility boundary |
| Mutation boundary | Parsed source-semantic sentences before meaning-bearing lowering; one instance is one atomic patch |
| Diagnostics | Structured project diagnostics, but not exact official wording in G1 or C1 |
| Proof specifications | A separate scope decision after ordinary rule execution is stable |

One boundary still requires an explicit decision record. "Parsed KAST" can
mean a post-`DefinitionParsing` artifact in which official K has already
generated configuration sentences, or it can mean parsed configuration terms
before that generation. G1 must declare which configuration behavior is
trusted and also how transformed IR is handed back to official K. Its preferred
initial boundary is:

```text
adapter supplies parsed and disambiguated source sentences/configuration terms
  -> K-in-K owns observation/mutation transformations
  -> egress adapter supplies an accepted definition artifact
  -> official K owns remaining lowering and Kore emission
```

The accepted egress could be a supported structured API, a canonical generated
definition, or another replayable artifact; the roadmap must not assume
round-trip support before probing it. If the pinned compiler cannot expose the
desired input cleanly, use a temporary post-configuration adapter, label CF-01
through CF-03 as trusted, and add the earlier observation seam as a named
migration task.

If D1 selects C1, the preferred end state changes to K-in-K-owned configuration
generation, semantic lowering, and Kore emission. Trusted official output must
always be labeled as such and must not be counted as an independent K-in-K
implementation.

## 3. Work unit and duration model

The unit of work remains a validated agent episode (VAE): one fresh attempt at
a versioned task packet, ending in an accepted artifact or a classified,
replayable blocker.

Each task packet must contain:

1. one capability leaf, or a deliberately coupled set of leaves;
2. exact input and output schema versions;
3. upstream source references and compatibility pin;
4. declared dependencies and non-goals;
5. feature-isolated fixtures and mutations;
6. a deterministic acceptance command;
7. a stopping condition that causes the work to split instead of expanding.

An episode should normally fit in one coherent agent context and expose no
more than one new shared contract. After three substantive full-oracle cycles
without acceptance, the default action is to preserve the evidence and split
or redesign the packet. The count of cycles is a stop rule, not a claim that a
fourth attempt could never work.

Project duration is recorded in two dimensions:

- **total VAEs**, which measure breadth and rework;
- **serial integration waves**, which measure the dependency depth that more
  agents cannot remove.

A wave closes only when its contracts, accepted artifacts, integration suite,
and evidence records are green. Calendar forecasts should use measured wave
latency only after repeated fresh-agent episodes exist.

## 4. Roadmap

### R0: make the reconnaissance independently auditable

Purpose: close Gate D before using the current forecasts to authorize
parallel implementation.

Work:

- freeze a revision or content digest for this workspace and all three
  references; the workspace repository was initialized at
  `9f30221d08de4b0f710061ce599b3c7f9f860273`, closing the earlier absence of
  Git metadata;
- have a fresh agent replay P1, P2, and P3 from files and commands only;
- audit all 42 top-level capability groups against the pinned K pipeline and
  classify each as G1-required, C1-only, C2-only, or optional;
- challenge normalization rules, reuse credit, and missing negative behavior;
- write the exact ingress, configuration, and egress adapter decisions
  described in section 2;
- split the capability inventory into machine-readable leaves with dependency,
  oracle, track, and ownership fields.

Exit evidence:

- all three probes reproduce, or discrepancies are classified;
- no material conclusion depends on conversation history;
- every G1 build-ready leaf has a deterministic acceptance command;
- C1/C2 complexity remains recorded without being pulled into G1 by default;
- unknown behavior remains visible rather than being assigned optimistic
  effort.

Expected scale: 1–2 serial waves and approximately 4–8 VAEs, including the
three fresh replays. This is a forecast, not a calibrated percentile.

### R1: calibrate task packets before fan-out

Purpose: measure how agents perform on normalized work rather than extrapolate
from three bespoke probes.

Run 6–12 packets sampled across both goal risk and compiler-independence risk:

- one lossless ingress/identity/egress round-trip through official K;
- one sentence-identity and provenance task across the same round-trip;
- one structural rule-selection and typed-binding task;
- one canonical single-sentence patch and one atomic two-sentence patch;
- one conservative observation-instrumentation task;
- one concrete K-native trace/monitor task and one symbolic branch/`unknown`
  task;
- one oracle-improvement task for an O1/O2 boundary; and
- one representative C1 lowering/emission task retained as a comparison point,
  not silently made a G1 dependency.

For every packet, record first-attempt acceptance, oracle cycles, regressions,
contract omissions, classified failures, and fresh replay outcome. Do not use
tokens or elapsed wall time as the headline estimate, though both remain
useful telemetry.

Exit evidence:

- VAE task sizes are comparable enough to aggregate;
- there is an observed first-pass/rework distribution;
- at least one high-coupling packet has been replayed independently;
- the official-K egress path is demonstrated or its precise blocker is known;
- evidence states whether C1 is required for either end goal;
- forecasts can state their sample count and uncertainty;
- the initial concurrency ceiling can be chosen from integration evidence.

Expected scale: 1–3 serial waves and 6–12 VAEs.

### R2-G: establish the production definition-transformation spine

Purpose: replace the probe-specific projections with the smallest shared
contract that both product goals require.

Build:

```text
source definition
  -> official-K ingress adapter
  -> SemanticInput v1
  -> K transformation protocol
  -> canonical patch and/or instrumented SemanticInput v1
  -> official-K egress/compilation adapter
  -> backend validation and execution
```

The first contracts should cover:

- modules, imports, sentence kinds, rule bodies, side conditions, attributes,
  and enough sort/configuration metadata to transform supported rules safely;
- stable sentence identity, source provenance, and structural fingerprints;
- deterministic lookup, structural selection, and typed bindings from K;
- canonical non-overlapping edit values and atomic patch application;
- identity and normalization behavior;
- observation-cell/configuration augmentation; and
- explicit adapter trust boundaries and inspectable artifacts.

Do not add declarations, axioms, or Kore-emission fields merely because C1 may
eventually need them. Add them when a G1 transformation requires them or when
D1 explicitly selects C1.

Checkpoint on 19 August 2026: `R2-G-01` accepted
`KDefinitionTransport-v1`. The lossless in-memory official `Definition` is
projected to typed K data; K owns structural selection; the adapter validates
lineage/content/body fingerprints; and identity returns the original official
object before official lowering. Peano and P3 pass normalized Kore and runtime
identity oracles. Stale lineage, stale content, and duplicate selector
cardinality fail at the named pre-backend boundary. This closes only
identity/provenance transport, not canonical patches, general
`SemanticInput v1`, or R2-G as a whole.

Checkpoint on 19 August 2026: `R2-G-02` accepted
`KDefinitionPatch-v1`. K structurally proposes one canonical input-relative
P3 term edit; the trusted-small host validates typed paths and fingerprints,
reuses the original official replacement node, and immutably rebuilds only
its ancestors. The result matches the W1-D focused Kore/runtime oracle. Stale
content and unsupported paths fail with zero applications before output
construction or backend artifacts.

Checkpoint on 19 August 2026: `R2-G-03` accepted
`KDefinitionPatch-v2`. K canonically proposes two input-relative edits in two
P3 rules; the host validates and prepares both against the original official
definition before one immutable transformer call. Stale-first, stale-second,
and duplicate-target transactions produce no output definition or backend
artifacts. The two edits compile and change both focused runtime behaviors as
declared while retaining syntax Kore, macros, provenance, attributes, and side
conditions.

Patch infrastructure now covers the bounded mutation prerequisite. `R2-G-04`
classified the pre-CF observation/configuration seam as
`pin-private-seam-needs-hook`: the typed `Configuration` midpoint exists, but
the pin's protected wrapper encloses a private parse/check/generate method and
`Kompile` directly constructs its private-final `DefinitionParsing`. The
accepted post-CF adapter and ordinary-source observation fallback both remain
healthy, localizing the blocker to composition at that midpoint.

`R2-G-05` accepted `OfficialConfigurationTransformHook-v0` as a source-bound
two-file classpath overlay. The backward-compatible default and explicit
identity paths match the official baseline. A fixture-specific Java callback
adds one typed inert observation cell, official cell checks/CF generation
consume it, the unchanged post-CF adapter runs, and erased runtime matches.
Null, exception, unauthorized-sentence, and duplicate-`<k>` negatives fail at
their intended pre-CF boundaries without backend artifacts.

`R2-G-06` accepted `KConfigurationAugmentation-v1`. K structurally selects the
P3 configuration and authors one canonical clone-from-input operation; the
generic host applies it through the pre-CF hook. A second K pass validates
`already-present` without rebuilding. Official CF generation produces the
observation state, runtime erasure matches, two independent oracles agree, and
six negative classifications return no transformed definition or backend
artifacts.

`R2-G-07` is accepted as `71379e4`: one explicit transition and a K-authored
observation latch update occur in one official rule application, with exact
erasure, idempotence, provenance, and fail-closed evidence.

`R3-G-01A` is accepted as prototype `249c540` plus repair `1ac7bc1`. One
list-backed `RuleApplied` event now retains exact run-local official provenance
while committed evidence is structurally portable across checkout roots.
`R3-G-02A` is accepted as integrated prototype `8d657e5`, semantic repair
`daf4d60`, and projection repair `e5b5234`. K authors the exact empty trace-cell
clone before CF, Java independently validates its complete shell, unchanged
`KRuleAppliedTrace-v1` appends the event after CF, and malformed failure
envelopes fail closed. `R3-G-03` is accepted as prototype `0a1a945` plus
acceptance-boundary repair `6c88e2c`. Pinned K matching consumes the accepted
single-event trace, returns exact typed provenance bindings for its head, and
returns exact `#Bottom` for both the empty trace and a K-authored unequal-label
constraint. Raw provenance is validated before portable projection, and the
host does not match or search the trace.

`R3-G-04` is accepted as prototype `f4a64c1` plus repair `5ce645d`. The already
instrumented `bump-state` rule fires twice, and K matches the exact exhausted
two-event trace with shared typed origin variables. This is the deliberately
degenerate first `next-event` boundary; it does not claim distinct-event order,
a general subsequence, or gap semantics. The next leaf is an atomic explicit
two-rule generic `RuleApplied` allowlist. Domain events, temporal gaps,
monitors, corpus orchestration, and symbolic branches remain held.

Exit evidence:

- an identity transformation crosses ingress and egress and produces the same
  selected backend behavior as the baseline;
- Peano/Foobar and an IMP-like rule/configuration fixture use the same IR and
  transformation protocol;
- stable sentence identity and provenance survive the round-trip;
- one exact single-sentence patch and one atomic two-sentence patch validate,
  apply, and compile through official K;
- one selected ordinary rule can be conservatively augmented with internal K
  observation state;
- reapplying an idempotent transformation does not duplicate instrumentation or
  edits; and
- malformed, stale, overlapping, and unsupported transformations fail at the
  closest intended boundary.

This—not independent Kore emission—is the next decisive technical milestone.
It directly tests whether K-in-K supplies unique leverage for the product
goals. Assign a scale only after R1 measures the ingress/egress and K-transform
work; the old compiler forecast is not a valid estimate for this narrower
track.

### R3-G: execution semantic-pattern vertical slice

Current disposition: incomplete and stopped on the old stack. R3-G-01 through
R3-G-04 supply bounded portable oracle vectors, but R3-G-05 produced terminal
negative resource evidence before any multi-rule transaction. The remaining
semantic meanings are frozen in the backend-agnostic vectors and require Rust
implementation proof.

Purpose: demonstrate the canonical option-(b) architecture without making a
debugger or backend trace format part of the product.

Build:

- generic `RuleApplied` observation for an explicit transition-rule allowlist;
- typed `memoryWrite` and `memoryLoad` events declared outside the core IR;
- trace-backed, branch-local K observation state as the inspectable reference;
- a K-authored ordered-subsequence matcher with shared payload variables;
- concrete corpus orchestration and bounded symbolic path exploration;
- `match`, exhaustive `no-match`, `unknown`, and `error` outcomes; and
- replayable witnesses with rule and source provenance.

Then introduce a streaming K monitor only after it is differentially equivalent
to the trace-backed reference on bounded finite traces.

Exit evidence is the acceptance list in
`draft/goal/execution-pattern-matching.md`, including sibling-branch isolation,
symbolic constraints, bounded-absence honesty, and observation erasure. Kore
RPC rewrite logs may be used as a disposable diagnostic oracle but are not a
required input or compatibility contract.

### R4-G: transactional semantic-mutation vertical slice

Current disposition: no old-stack implementation leaf was activated. R2's
patch kernel is reusable bounded evidence; selection, runner, reporting, and
cross-goal oracle semantics are portable contracts awaiting Rust proof.

Purpose: demonstrate that manual K meta-rules can describe both local and
coherent multi-rule semantic faults without source-text rewriting.

Build:

- exact, `each`, and coupled-tuple structural selection policies;
- K-authored operators that emit canonical patch values;
- precondition fingerprints and all-or-none patch application;
- isolated official-K compilation and bounded corpus execution;
- result and execution-pattern oracles; and
- deterministic candidate, diff, validation, and score reports.

Exit evidence is the acceptance list in
`draft/goal/semantic-mutation-testing.md`, including one single-rule mutant, one
atomic two-rule mutant, invalid/timeout classification, and a mutant killed by
an execution-pattern oracle despite an unchanged final result.

### D1: reassess scope from first principles

Decision recorded on 22 August 2026 in
`draft/decisions/d1-stop-old-g-track-and-preserve-portable-contracts-2026-08-22.md`.
It records a superseding user-owned stack/scope decision: stop the old G track,
complete every reasonably valuable backend-agnostic investigation, and defer
stack-specific implementation evidence to the planned Rust stack. It does not
claim that K-authored transformation lacks useful advantage, and it does not
activate C1/C2 or Rust implementation.

Do not automatically continue from R4-G into compiler reimplementation. Record
a decision using at least these questions:

1. Do both end goals work end to end through the transformation kernel?
2. Are the IR and transformation protocol demonstrably reusable across at
   least two structurally different fixtures rather than tailored to memory?
3. Which limitations come from official-K ingress/egress, and which come from
   the transformation design itself?
4. Would owning a particular frontend stage materially improve semantic
   control, correctness evidence, performance, or user experience?
5. Is independent semantic compilation an explicit research/product goal even
   if it is not required by the two product features?
6. What measured rework and maintenance cost separates targeted stage
   ownership, full C1, and remaining on G1?

Permitted outcomes are:

- continue hardening the transformation product while retaining official K;
- take ownership of one demonstrated blocking stage behind the same adapters;
- pursue C1 as an explicit compiler-independence/research delivery; or
- stop or redesign if K-authored definition transformation provides no useful
  advantage over a conventional AST library.

A later explicit user-owned change of implementation stack or product scope
may supersede this evidence-driven outcome set. Such a decision must say that
it is superseding the set rather than selecting an outcome whose premise the
evidence does not establish.

The decision record must name the evidence and the newly authorized scope.

### R2-C1: establish the independent semantic-compilation spine

Purpose: after D1 selects C1, replace official-K semantic lowering and emission
with versioned K-in-K-owned contracts. This section preserves the original R2
compiler milestone.

Build:

```text
source/reference artifact
  -> TypeScript adapter
  -> SemanticInput v1
  -> K semantic lowering pipeline
  -> SemanticModule v1
  -> Kore emitter
  -> kore-parser/backend validation and execution
```

The first contracts should cover:

- modules, imports, sorts, productions, labels, and attributes;
- parsed rules, functions, contexts, and side conditions;
- cell hierarchy and configuration metadata;
- stable source provenance and generated-entity provenance;
- explicit pass names and inspectable intermediate results;
- deterministic Kore names, declarations, axioms, and rules.

P1 and P3 are evidence and fixture sources, not production modules to join by
copying their projections together. Their useful behavior should be moved
behind the shared schemas and accepted again.

Exit evidence:

- Peano/Foobar declarations, structural axioms, functions, and ordinary
  rewrites flow through the shared pipeline;
- the P3 nested-cell/context example flows through the same pipeline;
- K-in-K's emitted Kore parses and passes backend validation;
- at least one program executes from K-in-K-emitted Kore with the expected
  result;
- a second application reaches the declared normalization fixed point;
- semantic mutations fail at the closest intended boundary.

This is the decisive C1 technical milestone. It tests the independent-compiler
architecture that isolated P1 and P3 could not test.

Archived C1 forecast from the original, pre-goal sequencing: roughly 4–7 serial
waves and 15–30 VAEs cumulatively from R0. It is a comparison baseline, not a
forecast for continuing after R4-G. D1 must estimate remaining C1 work from the
then-current state; G-track work counts as completed C1 behavior only where it
passes the C1 oracle.

### R3-C1: complete and harden the serial semantic clusters

Purpose: expand the spine in dependency order while keeping shared state under
coherent ownership.

Recommended order:

1. configuration generation and metadata variants;
2. strictness, explicit contexts, and function-with-configuration behavior;
3. cell completion, multiplicity, fragments, open cells, and sorting;
4. sort, symbol, injection, predicate, projection, and constructor axioms;
5. functions, macros, constants, side conditions, `owise`, and simplification;
6. ordinary rules, priorities, aliases, and backend-specific generated
   axioms;
7. claims, only if proof specifications are admitted to the selected F1
   profile.

Each cluster first grows with feature-isolated fixtures, then interaction
pairs, and only then real-language corpus cases. When a pass creates syntax
consumed by an earlier-looking pass, preserve the pinned upstream order rather
than forcing an artificial one-pass design.

Exit evidence for broad adapter-based F1:

- every in-scope leaf is accepted or explicitly excluded;
- every accepted leaf has at least O3 feedback, with O4 on critical semantics;
- the integrated negative and mutation suites remain sensitive;
- small languages and the selected real-language soak corpus compile;
- representative executions agree with official K;
- no official frontend transformation after the declared adapter boundary is
  required to produce the tested Kore.

Archived pre-goal C1 cumulative forecast: 10–16 serial waves and 45–90 VAEs.
D1 must replace rather than mechanically extend it.

### R4-C2: independent parser project

Purpose: turn adapter-based semantic completeness into an independent
frontend.

Prerequisites:

- exportable snapshots after raw parsing, priority/associativity,
  `prefer`/`avoid`, inference, overload resolution, list completion, and
  bracket removal;
- a versioned grammar/scanner IR;
- adversarial parse and negative corpora;
- stable SemanticInput, so parser work cannot churn the lowering pipeline.

Develop the ordered cluster under one coherent implementation owner until the
forest and filter interfaces are stable. Parallel work is initially safest on
oracle seams, corpora, scanner fixtures, and independent SimpleSub/Z3
cross-checking—not on competing changes to the filter pipeline.

Exit evidence:

- the exact P2 cases pass without invoking official parsing;
- configuration, rule, claim, context, and alias bubbles all cross the new
  boundary with locations intact;
- SimpleSub and Z3 agree on the checked corpus;
- adapter and independent-parser builds produce equivalent SemanticInput on
  the compatibility corpus;
- the complete R3-C1 integration suite remains green.

Archived pre-goal C2 cumulative forecast: 18–30 serial waves and 90–180 VAEs
for independent F1. Re-estimate it from C1 evidence if C2 is authorized.

### R5-C3: optional compatibility expansions

F2 adds normalized intermediate and emitted-artifact parity. Its archived
pre-goal cumulative forecast is 22–36 waves and 120–240 VAEs.

F3 adds the compiler product surface: CLI options, cache behavior, filesystem
layout, source diagnostics, invalid-definition behavior, compatibility flags,
and downstream tool assumptions. Its archived pre-goal cumulative forecast is
30–50 waves and 200–400 VAEs.

These ranges are retained as historical planning evidence. They become active
forecasts only after a selected C-track is re-estimated from measured VAEs.

## 5. Concurrency policy

Concurrency should follow stable contracts, not the number of available
agents.

| state | maximum useful implementation concurrency |
| --- | ---: |
| R0 audit and boundary decisions | 1 lead plus independent reviewers/replayers |
| R1 calibration | 2–3 isolated packets |
| R2-G transformation spine | 1 transformation-spine owner, with at most 1 adapter/oracle worker |
| R3-G/R4-G goal slices | 1 shared-spine owner plus 1 isolated corpus/oracle workstream |
| D1 scope decision | 1 lead plus independent evidence reviewers; no speculative implementation fan-out |
| R2-C1 shared IR and first independent emission | 1 semantic-spine owner, with at most 1 oracle/corpus worker |
| Stable R3-C1 contracts | 3–5 workstreams across different clusters |
| R4-C2 independent parser cluster | 1 coherent parser owner plus 1–2 oracle/corpus workstreams |
| F2/F3 long tail | 4–7 only while integration remains continuously green |

Increase concurrency by one only after three consecutive accepted packets
integrate without an undeclared shared-contract change. Reduce it when two
packets in the same wave collide on an IR/index contract or when integration
rework exceeds leaf implementation work.

Coupled clusters retain named owners. Other agents may add fixtures, mutations,
oracle projections, or downstream behavioral checks without concurrently
redesigning that cluster's shared API.

## 6. Wave acceptance and evidence ledger

Every wave should publish a small machine-readable ledger containing:

```text
wave ID and starting revision
roadmap track and authorized scope
accepted and failed task-packet IDs
input/output schema versions
commands and artifact digests
oracle grades and mutations exercised
integration regressions and resolutions
new or changed shared contracts
remaining blockers and forecast change
```

A wave is not accepted merely because all target code was generated. It must
pass:

1. unit and schema tests;
2. transformation validation, including identity/erasure/atomicity as relevant;
3. feature-isolated implementation differentials against the applicable
   portable vectors and accepted historical evidence;
4. at least one independent invariant or behavioral check for critical work;
5. the accumulated integration suite;
6. replay from the recorded starting revision and task packets.

## 7. Immediate queue

The next actions, in order, are:

1. finish and independently audit the backend-agnostic contracts, schemas,
   fixtures, vectors, taxonomy, and evidence classification;
2. preserve the terminal R3-G-05 outputs and run no current-backend retry;
3. when Rust implementation is separately activated, follow RS-01 through
   RS-07 and keep RS-08 held as specified in `rust-stack-handoff.md`; and
4. activate streaming optimization, compiler-independence expansions, or
   backend-log adapters only after their named prerequisites and a new scope
   decision.

The current checkpoint is portable investigation closure. The old packet
sequence remains historical context, not an executable queue.
