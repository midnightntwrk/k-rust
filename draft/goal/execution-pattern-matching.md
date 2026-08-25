# Execution semantic-pattern matching

Status: proposed feature contract, 19 August 2026.

## 1. Goal

Given a corpus of programs for a K-defined language, find whether a semantic
event pattern occurs along an execution path and return a replayable witness.
The motivating example is:

```text
on some path, a memory write occurs and a matching memory load occurs later
```

The two events may be consecutive or separated by arbitrarily many other
steps. Their payloads may be concrete or symbolic, and a variable bound by the
first event may constrain the second.

The feature is an occurrence finder first. Proving that no path can contain a
pattern is a stronger proof feature and must not be implied by an incomplete
search.

## 2. Define what “semantics appears” means

Three things can otherwise be conflated:

1. **A state shape:** a K pattern matches one reachable configuration.
2. **A rule application:** a particular semantic sentence was used.
3. **A domain event:** the execution performed an operation meaningful to the
   analysis, such as a memory write with an address and value.

The product supports the latter two as events. State patterns remain useful as
event guards or ordinary K search patterns, but a relationship such as “then”
is a property of one path and cannot be recovered from a single state unless
history or monitor state is made explicit.

The core event classes are:

- `RuleApplied`, carrying stable sentence identity, label, module, and source
  provenance; and
- user-defined domain events, whose constructors and payloads are ordinary K
  syntax, for example `memoryWrite(Address, Value, Origin)` and
  `memoryLoad(Address, Value, Origin)`.

Transition-rule events are in scope first. Function, simplification, macro,
hook, and SMT activity can depend on backend strategy and optimization. Those
are diagnostic events unless a later compatibility profile gives them a
stable meaning.

## 3. Evaluation of the design choices

### 3.1 Parse execution output with an ad-hoc language

This is suitable only for a disposable prototype. It couples correctness to a
printer, recreates K term parsing and sort handling, and makes symbolic terms,
constraints, branches, and source identity difficult to preserve.

Decision: do not make printed output or an ad-hoc parser the semantic
interface.

### 3.2 Match directly with K

K already matches terms and reachable configurations. This is the right
foundation, but a raw K state has no past. Direct state matching solves
“configuration C is reachable”; it does not by itself solve “A happened and B
happened later on the same path.”

Decision: use K patterns and rewrite rules after reifying the relevant path
history as typed event/monitor state.

This remains option (b), not an output-analysis variant of option (c). There
are two K-level moments:

1. K-in-K matches the definition as data and instruments the semantic rules
   that constitute relevant events.
2. During program execution, generated K updates advance a branch-local K
   monitor, and ordinary K search finds an accepting monitor state.

The event may be consumed immediately by the monitor. It need never be printed
or serialized as an execution trace.

### 3.3 Match symbolic-debugger output using a K semantics of the format

This is technically possible but is the wrong primary boundary. In the pinned
K toolchain, Kore RPC can return ordered successful-rewrite logs with rule IDs
and, when enabled, rewritten terms. Symbolic branching responses also expose
successor states and rule IDs. However:

- the log describes backend attempts and applications, not a stable domain
  event vocabulary;
- simplification and fallback behavior varies across Kore, Booster, and LLVM;
- rule substitutions are explicitly diagnostic rather than a reasoning API;
- reconstructing branch-local paths is client work; and
- logging payloads and costs are backend options.

The logs are valuable for differential validation and disposable experiments.
An experimental adapter may normalize them into the same typed event
vocabulary, but it has weaker fidelity and stability guarantees. User-authored
patterns must not mention RPC fields, backend origins, fallback records,
simplification attempts, or other debugger concepts.

Decision: option (c) is not part of the canonical architecture. A backend-log
adapter, if built, is an optional oracle/diagnostic component that can be
removed without changing observation specifications or patterns.

### 3.4 Recommended K-native architecture

Transform the definition to emit typed K events, and evaluate K-authored
monitors over those events during execution. Keep TypeScript responsible for
running the backend, traversing branches, enforcing bounds, and aggregating
corpus results.

This is option (b) with explicit K-level history. The backend protocol remains
an execution mechanism rather than a new semantics, and TypeScript consumes
structured match/stop results rather than interpreting a semantic trace.

The same design works with either project scope. Full K-in-K can instrument
and lower the resulting definition itself. Thin K-in-K can instrument the
parsed definition and hand it back to official K for compilation. The scope
choice changes who performs lowering, not the pattern architecture.

## 4. Architecture

```text
SemanticInput + ObservationSpec (K)
  -> observation transformation (K-in-K)
  -> instrumented SemanticInput + observation manifest
  -> normal lowering and Kore emission
  -> concrete run or symbolic path exploration
  -> branch-local K monitor state
  -> structured per-path result and witness
  -> corpus aggregation
```

### 4.1 Observation specification

An observation specification is a K module compiled against the target
definition's semantic IR and event vocabulary. It can:

- select transition sentences by stable ID, label, attribute, or structural K
  pattern;
- bind terms from a selected rule;
- declare the domain event emitted when that rule applies; and
- define K rules/functions that advance a monitor when an event arrives.

Selecting a rule and constructing the payload is a compile-time meta-operation
over `SemanticInput`; it must not scrape source text. A generated observation
manifest records every selected sentence and the event constructor attached to
it. A selector that finds zero or an unexpected number of sites is an error,
not a silently empty observer.

`RuleApplied` needs no domain-specific selector: it can be generated for every
in-scope transition or for an explicit allowlist.

The authoring experience should remain recognizably K. For example, after the
concrete IR constructors are fixed, the monitor for the motivating query should
be expressible in the following schematic style rather than in a parser owned
by the TypeScript runner:

```k
rule advance(memoryWrite(A, _V, O), start)
  => afterWrite(A, O)

rule advance(memoryLoad(A, _V, O2), afterWrite(A, O1))
  => accepted(writeAt(O1), loadAt(O2))

rule advance(_OTHER, S:MonitorState) => S [owise]
```

This is illustrative, not a frozen surface syntax. The real API must define
overlap, priority, and symbolic side-condition behavior precisely before such
modules become a compatibility contract.

### 4.2 Instrumentation contract

Instrumentation adds observation state to the configuration and augments
selected rules so that the semantic transition and event update are one
logical step. It must preserve:

- the original rule's applicability and program-state result after erasing
  observation cells;
- original priority relationships;
- branch structure, modulo observation terms;
- sentence provenance; and
- behavior when observation is disabled.

An event should not be printed as an impure side effect and reparsed. It is a K
term carried by the configuration or passed directly to a K monitor.

The transformation must reject instrumentation it cannot make conservative,
including unsupported rule shapes. It must also distinguish rules that model
language transitions from function/simplification rules.

An event payload may only use variables that are well sorted and bound at the
point the original rule fires. If an operation exists only as evaluation of a
K function, the MVP requires an explicit transition-level observation point;
it does not pretend that backend-dependent simplification logging is the same
event.

### 4.3 Trace-backed reference implementation

The first vertical slice may append events to a branch-local `<trace>` cell.
This provides the simplest inspectable reference semantics. Conceptually, a
matching trace contains:

```text
<trace> ListItem(memoryWrite(A, V, O1))
        ...
        ListItem(memoryLoad(A, V2, O2)) ... </trace>
```

K rules/functions over the trace, followed by an ordinary K search/output
pattern over their result, can then match configurations containing the event
relationship. This proves the representation is usable from K and produces a
full witness without assuming that the displayed `...` above is itself the
final query syntax.

This trace is part of the instrumented K configuration; it is not debugger
output and does not require a K semantics of an external trace format.

It is not the desired large-run implementation. A growing trace changes state
size, inhibits state merging, and can make symbolic exploration much more
expensive.

### 4.4 Streaming monitor

The production form advances a branch-local monitor on each event and retains
only:

- the set of active match states;
- K-term bindings and their path constraints;
- whether the pattern has accepted; and
- the minimum event data required for a witness.

The monitor transition is defined in K and must be total and deterministic for
the supported pattern fragment. It is applied atomically with the observed
semantic step so monitor housekeeping does not become visible as extra
language transitions.

The trace-backed matcher is the oracle for the streaming implementation: for
bounded finite traces, both must return the same match status and bindings.

## 5. Required pattern semantics

The first supported fragment is deliberately smaller than a general temporal
logic. It needs:

- a single event pattern;
- ordered sequence on one path;
- `next-event`, meaning consecutive **observed events**;
- `eventually-after`, allowing zero or more intervening observed events;
- alternatives;
- variables shared between event patterns;
- K side conditions over bound payload terms;
- named patterns and imports; and
- existential occurrence reporting.

“Adjacent” must always say which clock it uses. `next-event` ignores semantic
steps that emit no event. A later `next-transition` operator may count every
language transition, but the two must never be conflated.

The payload matcher is native K matching over declared event constructors.
Temporal composition may use a small library of K constructors, but its
meaning is itself defined in K; no client parses a textual execution language.

The following are later extensions:

- bounded gaps and repetition;
- negation between two events;
- event counts and aggregation;
- call/return nesting or other scoped events;
- universal path queries; and
- temporal proof claims.

Unbounded absence, liveness, and universal symbolic properties require a proof
story, not merely a larger execution limit.

## 6. Symbolic execution and branching

Every monitor belongs to one path. When symbolic execution branches, its
monitor state and bindings branch with the configuration. Events from sibling
branches must never be combined into one match.

An event payload may contain symbolic K terms. A match result therefore
includes the path predicate under which the event sequence is feasible. Shared
variables such as the address in a write/load pair are related using K/Kore
constraints and the configured solver, not host-language string equality.

Per query and test, the result is one of:

| status | meaning |
| --- | --- |
| `match` | A feasible path with a witness was found. |
| `no-match` | Exploration was exhaustive for the declared finite search space and no witness exists. |
| `unknown` | A depth, time, branch, solver, or backend limit prevented an absence conclusion. |
| `error` | The definition, observer, pattern, program, or backend invocation was invalid. |

`unknown` is essential. A depth-bounded run that finds nothing is not
`no-match`.

The MVP query is existential: “does any explored path match?” Universal path
quantification is out of scope until the project can state and discharge the
corresponding proof obligation.

## 7. Corpus contract

A corpus manifest names:

- the target definition and compatibility pin;
- the observation and pattern modules;
- program files and parser/start-symbol options;
- concrete or symbolic execution mode;
- solver and backend profile;
- depth, time, branch, and result bounds; and
- the aggregation question.

The initial aggregation questions are:

- which tests have at least one matching path? and
- does at least one test in the corpus have a matching path?

Results remain available per test and per explored path. Corpus aggregation
must not erase `unknown` results or reinterpret them as false.

## 8. Witness and report

A match report contains:

- definition, observer, pattern, program, and backend digests;
- execution options and bounds;
- test ID and path/KCFG identity;
- ordered matched-event indices;
- event constructors and payload K terms;
- sentence ID, label, module, and source location for every matched event;
- variable bindings and path predicate;
- terminal/stop reason; and
- enough invocation data to replay the witness.

Reports use a versioned JSON schema. Pretty-printed K is supplemental; Kore or
KAST JSON is the lossless payload.

## 9. Minimum viable slice

Use a small IMP-like fixture with explicit memory rules and implement:

1. `memoryWrite(Address, Value, Origin)` and
   `memoryLoad(Address, Value, Origin)` events;
2. exact-ID/label observation selectors with cardinality checks;
3. conservative trace-cell instrumentation of ordinary transition rules;
4. a K-authored write-then-load pattern with a shared address variable;
5. concrete corpus execution;
6. one bounded symbolic branch example;
7. `match`/`no-match`/`unknown` reports with a witness; and
8. baseline-versus-instrumented erasure checks for results and branch outcomes.

Comparing generic `RuleApplied` events with successful-rewrite IDs from Kore
RPC is a useful optional diagnostic, but the slice does not depend on that log
interface.

The slice is accepted when:

- consecutive and separated matches are both found;
- reversed event order does not match;
- events from sibling branches do not match each other;
- a shared symbolic address produces the expected constraint;
- a depth-limited absence is `unknown`;
- erasing trace state yields the baseline program result and branch outcomes;
- an observer whose selector cardinality changes fails before execution; and
- repeated runs produce identical normalized artifacts and reports.

## 10. Feasibility evidence in the pinned toolchain

The proposal relies on interfaces present in K v7.1.337, the version pinned by
this workspace:

- `krun --pattern` matches an output configuration, and the search modes expose
  final, interim, and one-step reachable states;
- Kore RPC execution results distinguish branching, depth bounds, timeouts,
  terminal rules, and other stop reasons;
- optional Kore RPC rewrite logs preserve application order and rule IDs and
  can include rewritten terms;
- `pyk.kore.rpc` exposes those states, stop reasons, logs, and branch results as
  structured values; and
- pyk's definition/coverage APIs relate `UNIQUE_ID` attributes back to K
  sentences.

The execution/search interfaces establish that K-native monitors can be driven
and queried. The logging interfaces only establish that an optional
differential oracle is available. They do not define the event model, remove
the need for typed domain-event instrumentation, or prove that the proposed
monitor transformation is conservative.

## 11. Explicit non-goals for the MVP

- interpreting debugger prose;
- treating any backend trace schema or operational step vocabulary as a stable
  pattern interface;
- inferring domain events from arbitrary state diffs;
- observing builtin function evaluation as stable semantic behavior;
- retaining unbounded full traces in the production implementation;
- universal temporal claims;
- proving observation conservativity for every K construct before the first
  supported subset is useful; and
- promising cross-backend event equivalence beyond the selected profile.
