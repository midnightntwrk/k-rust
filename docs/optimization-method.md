# Finding structural optimizations

This is the method for performance work that changes which algorithms run, in which order, or on which representation, as opposed to tuning one function.
It records what found real gains in the 2026-09-23 exercise, in which two agents independently found the same two changes: a definedness cache that, with a construction-time macro flag, made the largest `krun` ladder runs 6 to 19 times faster, and a Z3 sort-inference encoding that halved the WASM compile.

## Tools

| Tool | Gives | Blind to |
|---|---|---|
| `scripts/algo-receipt.sh --workload NAME` over `scripts/algo-workloads.toml` | per-algorithm span counts, self and total time, counters, phase timings, output check, wall time and peak RSS of an untraced run | code no card names, and work outside spans |
| `algo-graph atlas --index atlas.toml` | per workload: self-time shares, Amdahl ceilings, observed nesting; per ladder: growth exponents beside the card's bound | the same, plus tracing overhead in its times |
| `algo-graph diff --before … --after …` | per-algorithm deltas, exact for counts and counters, noise-classified for time | the same |
| `samply` (`scripts/profile.sh`, or `samply record` on a `profiling` build) | every function, no tracing overhead | algorithm boundaries |
| `algo-graph query show ID` | a card's cost modes, variables, sites | anything measured |

Receipts use the `profiling` profile with the `measure` feature; debug-build costs are not evidence.
`samply` needs `perf_event_open`, so it runs under the host UID only, with `taskset -c 0-15` (see `scripts/profile.sh --help`).

## Procedure

1. **Rank by share.** Read the atlas's per-workload tables. An algorithm's Amdahl ceiling, `1 / (1 - share)`, is the most the workload can gain from it; skip anything whose ceiling does not matter on a workload that matters.
2. **Look for growth, not only size.** On a ladder, a per-call slope above zero means one invocation's own time grows with the input: the algorithm re-walks something that grows. This is how the definedness cost was found: its span count grew linearly with the loop bound but its self time as n^1.5 (IMP) and n^2.7 (FUN). A card bound that is linear in term size, applied to a term that grows every step, explains such a slope; `query show` gives the bound and its variables.
3. **Profile untraced before trusting a time.** Aggregate tracing costs about 60 % on long `krun` runs and inflates algorithms with many short spans. A `samply` profile of the untraced `profiling` binary gives the numbers to quote, and it shows code the atlas cannot: in the exercise, three of five mechanisms (`Pattern::macro_or_alias_symbol`, `rule::find_k_cells`, `provenance::record_generated_origins`) had no span or no card.
4. **Find what grows.** When a per-call cost grows, dump the state (`krun --depth N`) and look at which part of it grows. In the IMP loop the `<k>` cell gained one `{}` per iteration, and every walk over the configuration paid for it.
5. **Separate building from solving.** When a solver dominates, check where its time goes. In Z3 sort inference, solving was about 1 % of the time; building and asserting a disjunction over the whole subsort relation for every constraint was the rest. The fix was the encoding, not fewer solver calls.
6. **Prefer facts computed once over facts recomputed.** Both backend wins are the same shape: a property of an immutable, shared term (definedness obligations, the presence of a macro or alias head, the number of k cells) was recomputed by a walk on every rule attempt. Computing it when the term is built, or memoizing it on the shared node, turns each walk into a lookup. The change is sound when the property depends only on the term and the fixed definition; state that dependency in the code.
7. **Prototype behind a switch and measure alone and combined.** Mechanisms interact: the macro flag alone gained 16–28 %, and on top of the definedness cache it took the FUN ladder from 15.3 s to 3.9 s. Measure each change by itself and together before ranking them.
8. **Validate.** Compare outputs byte for byte against the unchanged binary on every workload. Compare counters and span counts with `algo-graph diff`: an unexpected count change is a behaviour change. Then run the reference differential gates (`README.md`, "Compatibility evidence") before proposing the change for review.

## Reporting a proposal

State the change and the algorithms and representations it touches (`file::symbol`), the evidence (workload, share or count, and how it was measured), the ceiling per workload with its arithmetic, the measured gain if prototyped, the properties it must preserve and how each was checked, and the risk.
