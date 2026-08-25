# P3 report: configuration, contexts, and cell concretization

Status: bounded probe completed on 19 August 2026 against K v7.1.337,
commit `4a46d1231473b599c699160132fd6e76a5c46406`.

## Result

P3 is a passing vertical slice for the configuration/context coupling cluster.
The source fixture contains:

- a nested, non-preconcretized `<T>` configuration with `<k>` and `<state>`;
- a binary `seqstrict` operation;
- an independent explicit `hold(HOLE)` context;
- a function-context rule that reads `<state>`;
- a state-changing rewrite with nontrivial `requires` and `ensures`;
- ordinary value and startup rules.

The executable K model matched official K for three parent edges, six generated
heating/cooling rules, five concretized source rules, configuration injection
into the `read` call, and the presence of both side conditions. Its normalized
projection was a fixed point.

All eleven selected rules appeared in final Kore: ten rewrites and the
configuration-reading function equation. Executing `start` produced
`<k> 1 </k>` and `<state> 2 </state>`.

## Observed boundaries

The manifest `oracle/manifests/p3-coupled.json` captures:

| boundary | evidence |
| --- | --- |
| configuration expansion | `parsed.json`, including generated cell syntax and initializers |
| through `resolveContexts` | `compiled.json` with four seqstrict and two explicit-context rules; `bump-state` still mentions only `k,state` |
| through `concretizeCells` | `compiled.json`; `bump-state` now mentions `generatedTop,T,k,state` and matches the K model |
| full frontend | compiled JSON plus main, syntax, and macro Kore |

As with Gate B, prefix selection does not stop backend emission. The context
prefix exits 1 on missing `GeneratedTopCell`; the cell prefix exits 1 at the
later incomplete-pipeline `None.get`. Both diagnostics and required artifacts
are exact manifest contracts, not ignored failures.

## Minimum stable metadata API

This slice required a shared API containing at least:

1. child-to-parent cell edges and the generated top;
2. the main computation cell and its sequence behavior;
3. strict positions, evaluation order, result-sort predicate, and stable
   generated labels/freezers;
4. explicit context identity and hole sort;
5. rule cell occurrences plus open/closed-cell information;
6. function-context capture and call-site configuration injection;
7. typed `requires`/`ensures` retained through completion.

These are shared inputs, not independent passes. Context generation needs the
computation-cell contract; concretization needs the complete parent graph;
function-context lowering changes both the function declaration/equation and
every call site that occurs in a rule.

## Reproduction

```sh
bun run p3

bun run oracle capture oracle/manifests/p3-coupled.json \
  --out oracle/results/p3-coupled-new
```

The model and runner are under `p3/`. `p3/build/probe-result.json` records exact
projections, selected final Kore axiom classes, execution, and command timing.

## Limitations

The K model emits a canonical dependency/fact projection, not complete compiled
KAST or textual Kore. It covers one fixed-arity cell tree, one binary
`seqstrict` production, one explicit context, and one function-context call.
Multiplicity, cell collections/fragments, optional/star cells, open-cell
sorting, nested rewrites, priorities, and arbitrary strictness arity remain
outside this bounded slice.

Consequently P3 proves feasibility and exposes the shared contract; it does not
justify marking CF-03, LO-02, or LO-07 feature-complete.

## Agent-complexity telemetry

One lead-agent episode produced the accepted slice. Before acceptance, three
useful diagnostics exposed hidden contracts: strictness requires a `KResult`
predicate/sort, a function-context function cannot be called directly in the
initial configuration, and deeply nested projection constructors were brittle
to parse until fact generation was factored into helpers. The first complete
differential cycle then passed.

This is one VAE candidate without fresh-agent replay. The accepted P3 runner's
external commands take tens of seconds, but evaluation latency is telemetry,
not a VAE estimate.

## Complexity implication

P3 confirms that configuration expansion, contexts, function-with-config, and
cell concretization form one serial cluster. They should share one owner and
one versioned metadata API until the full variants stabilize. Parallel work is
safe around fixtures, projections, and backend behavior tests; independently
implementing these passes before the API exists would create integration
rework.

Together with P1, P3 removes the earlier reason that ordinary source rewrites
could only be compared before concretization. It does not yet merge the two
probe models into a production frontend—that integration is precisely part of
the remaining implementation estimate.
