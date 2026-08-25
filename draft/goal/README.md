# End-goal product features

Status: proposed feature contract, 19 August 2026.

This folder turns two motivating uses of K-in-K into product requirements:

1. find ordered semantic behavior in concrete or symbolic executions; and
2. define and run manual, possibly coupled, mutations of a K semantics.

The detailed proposals are:

- [Execution semantic-pattern matching](execution-pattern-matching.md)
- [Semantic mutation testing](semantic-mutation-testing.md)

They are end goals, not claims about the current probes. The current workspace
only establishes frontend/oracle feasibility. Both goals depend on the shared
semantic spine proposed in `draft/k-in-k-execution-roadmap.md`.

## Product thesis

K-in-K should treat a K definition as typed, provenance-bearing data and
support two controlled transformations of it:

```text
                         +-> observed definition -> execution -> event matches
parsed K definition ----+
                         +-> mutated definition  -> compilation -> test results
```

The important common foundation is not a text parser. It is a stable
representation of modules, sentences, terms, attributes, and source
provenance on which K rewrite rules can operate.

## Decisions

| concern | decision |
| --- | --- |
| What is the canonical execution-pattern architecture? | Option (b): K-in-K instruments the semantics, and K-authored branch-local monitors recognize temporal patterns during execution. |
| What is matched during execution? | Typed semantic events on a single execution path, not debugger text and not arbitrary diffs between printed configurations. |
| Where are patterns defined? | In K modules over the event vocabulary. TypeScript supplies execution, bounds, artifact capture, and corpus aggregation. |
| How are events obtained? | By an observation transformation over the semantic IR. Generic rule-application events are automatic; domain events such as memory writes explicitly declare their payload. |
| How are temporal relationships represented? | The execution carries branch-local observation state. An initial trace-backed implementation may materialize events; the production form uses a streaming K monitor and retains only a witness. |
| What is the role of debugger/backend traces? | Optional experimentation, diagnostics, and differential validation only. Their schemas and operational step vocabulary are not a product compatibility boundary. |
| What is a semantic mutation? | A K meta-rule over the semantic IR that proposes one atomic patch. The patch may edit one or several sentences. |
| How are multiple-rule mutations handled? | One named mutation instance contains all participating edits and either applies completely or does not apply. Independent single-site mutations are not silently combined. |
| What remains outside K? | Scheduling processes, resource limits, caching, corpus manifests, backend invocation, and machine-readable reports. |

This execution-pattern decision does not depend on choosing a full or thin
K-in-K. A full implementation can own instrumentation and subsequent lowering;
a thin implementation can instrument parsed semantic IR and return it to the
official compiler. Both are option (b). Neither requires option (c).

## Shared required contracts

Both features require the following contracts from the production semantic
spine:

- a versioned `SemanticInput` representation with complete parsed rule bodies,
  conditions, attributes, modules, and configuration metadata;
- stable sentence identity that survives observation, mutation, lowering, and
  Kore emission;
- source and generated-entity provenance;
- deterministic serialization and content fingerprints;
- a K-facing definition API for looking up and replacing sentences without
  depending on source formatting;
- validation before and after a transformation;
- an artifact manifest recording the input definition, transformation module,
  K compatibility pin, options, and output digest.

Stable identity is especially important. A source label is useful to people
but is optional and need not be unique. A generated sentence ID is unique but
may change when the frontend changes. Reports therefore carry both, plus the
source location and a structural fingerprint.

## How the goals reinforce each other

Execution patterns become mutation-test oracles. For example, a mutant can be
killed because it removes the only path containing a `memoryWrite` followed by
a `memoryLoad`, even when the final program result is unchanged.

Mutation testing in turn validates observation conservativity. Mutations that
change an observed semantic action should change the event result, while
mutations outside the observation boundary should not cause spurious matches.

The observation transformation and mutation engine should consequently share
the same patch, provenance, validation, and replay infrastructure.

## Delivery order

1. Stabilize `SemanticInput v1`, sentence identity, provenance, and
   deterministic definition rewriting.
2. Build one concrete-execution vertical slice with two explicit domain events
   and an ordered-subsequence query.
3. Run the same slice through bounded symbolic branching and report
   `match`/`no-match`/`unknown` correctly.
4. Build one exact-site single-rule mutant and one atomic two-rule mutant over
   the same fixture.
5. Allow trace-pattern assertions to kill those mutants.
6. Add structural mutation-site discovery, streaming monitors, coverage-based
   test selection, and larger corpora only after the vertical slice is
   replayable.

These are product capabilities layered on the roadmap rather than a reason to
broaden its initial compiler scope. The first slice should use only semantic
constructs already accepted by the R2 spine.

## Common non-goals for the first delivery

- parsing human-oriented debugger output;
- defining user-authored patterns in terms of a debugger, Kore RPC, Booster,
  LLVM, or another backend's trace schema;
- claiming that a bounded search proves absence;
- arbitrary temporal logic or liveness proofs;
- observing every backend simplification or builtin evaluation;
- automatic generation of all higher-order mutant combinations;
- classifying semantic equivalence of mutants in general;
- preserving the original whitespace and comments of a mutated source file;
- mutating generated Kore axioms without a separate, explicitly selected
  mutation phase.
