# Finding structural optimizations

This is the method for performance work that changes which algorithms run, in which order, or on which representation, as opposed to tuning one function.
It records what found real gains in the 2026-09-23 exercise, in which two agents independently found the same two changes: a definedness cache that, with a construction-time macro flag, made the largest `krun` ladder runs 6 to 19 times faster, and a Z3 sort-inference encoding that halved the WASM compile.

## Tools

| Tool | Gives | Blind to |
|---|---|---|
| `scripts/algo-receipt.sh --workload NAME` over `scripts/algo-workloads.toml` | per-algorithm span counts, self and total time, counters, phase timings, output check, wall time and peak RSS of an untraced run | code no card names, and work outside spans |
| `scripts/algo-receipt.sh --workload NAME --profile` (`algo-graph profile`) | per algorithm: sampled self and total shares of an untraced `samply` run; per workspace function no card site contains: its leaf and inclusive share and the algorithm it runs under | code outside the workspace, charged to its innermost workspace caller; frames beyond samply's stack copy on deep recursion (the profile reports truncated stacks); work below a card site that is a driver function, which that algorithm's self share absorbs |
| `algo-graph atlas --index atlas.toml` | per workload: self-time shares, Amdahl ceilings, observed nesting, and, for profiled receipts, sampled shares beside them and an uncarded hot code table; per ladder: growth exponents beside the card's bound, and uncarded inclusive shares per profiled parameter | tracing overhead in its traced times; code outside spans in its traced shares |
| `algo-graph diff --before … --after …` | per-algorithm deltas, exact for counts and counters, noise-classified for time | the same |
| `samply load profile.json.gz` on a profiled receipt, or `scripts/profile.sh` | every function and its call tree, no tracing overhead | algorithm boundaries |
| `algo-graph query show ID` | a card's cost modes, variables, sites | anything measured |

Receipts use the `profiling` profile with the `measure` feature; debug-build costs are not evidence.
`samply` needs `perf_event_open`, so profiles are recorded under the host UID only, with `taskset -c 0-15` and outside any cgroup memory limit (see `scripts/algo-receipt.sh --help`).

## Procedure

1. **Rank by share.** Read the atlas's per-workload tables. An algorithm's Amdahl ceiling, `1 / (1 - share)`, is the most the workload can gain from it; skip anything whose ceiling does not matter on a workload that matters.
   Record the workloads that matter with `--profile`, so each table also shows sampled shares, algorithms without spans, and the uncarded hot code.
2. **Look for growth, not only size.** On a ladder, a per-call slope above zero means one invocation's own time grows with the input: the algorithm re-walks something that grows. This is how the definedness cost was found: its span count grew linearly with the loop bound but its self time as n^1.5 (IMP) and n^2.7 (FUN). A card bound that is linear in term size, applied to a term that grows every step, explains such a slope; `query show` gives the bound and its variables.
3. **Profile untraced before trusting a time.** Aggregate tracing costs about 60 % on long `krun` runs and inflates algorithms with many short spans. The sampled shares of an untraced `profiling` run are the numbers to quote. Read the uncarded hot code table next: in the exercise, three of five mechanisms (`Pattern::macro_or_alias_symbol`, `rule::find_k_cells`, `provenance::record_generated_origins`) had no span or no card, and only a profile showed them. A function whose inclusive share grows along a ladder's sampled table is a walk that grows with the input.
4. **Find what grows.** When a per-call cost grows, dump the state (`krun --depth N`) and look at which part of it grows. In the IMP loop the `<k>` cell gained one `{}` per iteration, and every walk over the configuration paid for it.
5. **Separate building from solving.** When a solver dominates, check where its time goes. In Z3 sort inference, solving was about 1 % of the time; building and asserting a disjunction over the whole subsort relation for every constraint was the rest. The fix was the encoding, not fewer solver calls.
6. **Prefer facts computed once over facts recomputed.** Both backend wins are the same shape: a property of an immutable, shared term (definedness obligations, the presence of a macro or alias head, the number of k cells) was recomputed by a walk on every rule attempt. Computing it when the term is built, or memoizing it on the shared node, turns each walk into a lookup. The change is sound when the property depends only on the term and the fixed definition; state that dependency in the code.
7. **Prototype behind a switch and measure alone and combined.** Mechanisms interact: the macro flag alone gained 16–28 %, and on top of the definedness cache it took the FUN ladder from 15.3 s to 3.9 s. Measure each change by itself and together before ranking them.
8. **Validate.** Compare outputs byte for byte against the unchanged binary on every workload. Compare counters and span counts with `algo-graph diff`: an unexpected count change is a behaviour change. Then run the reference differential gates (`README.md`, "Compatibility evidence") before proposing the change for review.

## Reporting a proposal

State the change and the algorithms and representations it touches (`file::symbol`), the evidence (workload, share or count, and how it was measured), the ceiling per workload with its arithmetic, the measured gain if prototyped, the properties it must preserve and how each was checked, and the risk.
