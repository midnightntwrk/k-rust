# IMP with an LLM-written corpus

This directory runs the kink-flow loop (root README, "Using kink-flow") on IMP,
the K tutorial's `pl-tutorial/1_k/2_imp/lesson_4` (flow packet F-09).
The corpus and the mutation list were written by an LLM driving the loop.

| File | Content |
| --- | --- |
| `imp.k` | The lesson's definition, unchanged below a header naming its source path and revision (K `4a46d123`). |
| `LICENSE-K.md` | The K framework's licence (BSD 3-Clause), which covers `imp.k`. |
| `FLOW.toml` | The corpus: the lesson's three programs with reduced bounds, and four programs written for survivors. |
| `programs/` | The program files. |
| `MUTATIONS.toml` | 21 mutations: 18 single edits and 3 correlated ones. |

Run it from this directory:

```sh
kink-flow check FLOW.toml
kink-flow results FLOW.toml
kink-flow run FLOW.toml MUTATIONS.toml
```

## Results at k-rust 927b9ce6

- `results`: every one of the 17 rules is covered by a comparable program; the lesson's three programs alone cover them.
- `run`: 20 mutations are killed; `add-commuted` survives and is equivalent
  (`+Int` is commutative and the rule only fires on two `Int` values), so it is kept as the one explained survivor.
- Killers: `sum` 8, `primes` 5, `arith` 3, `and` 2, `divzero` 1, `redeclare` 1.
  `divzero` and `redeclare` kill through the exit-stop oracle, not the final configuration:
  the baseline is stuck, and the mutant's rule now applies with an undefined result (`1 /Int 0`, a map with a repeated key).
- `collatz` is `timeout` (see below) and cannot kill a mutant.

## Cost: strict operators multiply the paths

kink compares the set of final configurations, so it explores every evaluation order.
IMP's `+` and `/` are `strict`, and k-rust does not merge equal intermediate states
(k-rust request KINK-01, `pathset-state-dedup`), so each loop iteration multiplies the paths.
Measured with the release binary (wall time of `results` for one program with time_ms = 60000, compile included; host load about 10):

| Program | Bound | Wall | Peak RSS |
| --- | --- | --- | --- |
| sum | n = 3 | 1.6 s | 0.1 GiB |
| sum | n = 6 | 7.9 s | 1.1 GiB |
| primes | m = 4 | 4.3 s | 0.2 GiB |
| primes | m = 5 | did not end within 60 s | 2.8 GiB |
| collatz | m = 3 | 36 s | 2.3 GiB |

At the lesson's own bounds (sum n = 100, collatz m = 10, primes m = 10) the growth above rules out a run (not attempted),
so the seed programs use n = 3, m = 3 and m = 4.

A mutant that loops where the baseline ends multiplies its paths without end.
With `time_ms = 10000`, a cold `run` of this list peaked at 16.4 GiB resident;
an earlier attempt with `time_ms = 120000` reached 58 GiB before it was stopped.
Run kink-flow under a memory limit, for example
`systemd-run --user --scope -p MemoryMax=24G -p MemorySwapMax=0 kink-flow run ...`,
and keep `time_ms` small.

## Re-runs: the outcome cache

`kink-flow run` caches every proved outcome of a mutation on a program (flow F-14),
so re-checking this list costs far less than the first run.
Measured with the release binary on scratch copies of this directory,
each run under `systemd-run --user --scope -p MemoryMax=24G -p MemorySwapMax=0` (peak = the scope's `memory.peak`; host load 21-37):

| Scenario | Wall | Peak | Campaign calls (one mutant compile each) | Result |
| --- | --- | --- | --- | --- |
| cold run, fresh cache | 216.5 s | 12.7 GiB | 21, over 126 programs | killed 20, survived 1 (`add-commuted`); the killers above; 39 outcomes cached |
| warm re-run, no change | 4.9 s | 0.11 GiB | 0 | 20 killed from the cache, `add-commuted` from its 6 cached agreements |
| one program added (`added`: `x = 1 + 2; y = x / 2;`) | 5.7 s | 0.10 GiB | 1, over `added` alone | its baseline, then `add-commuted` on it; the killed mutations untouched |
| comment-only edit of `imp.k` (a line appended) | 69.7 s | 0.40 GiB | 21: one per killed mutation over its last killer, and `add-commuted` over the 6 comparable programs | every baseline again; the specification digest changed, so no cached outcome applies (until k-rust's KINK-14 execution digest) |
| real edit of the unary minus rule (`0 -Int I1` becomes `0 -Int I1 +Int 0`) | 94.7 s | 10.8 GiB | 21: 19 over the last killer alone; `neg-drops-sign` (its rule's text changed, so its hint no longer applies) and `add-commuted` over the 6 comparable programs | statuses and killers equal to a cold run of the edited copy (227.8 s) |
| `run --verify` after the cold run | 209.5 s | 14.5 GiB | 21, over 126 programs | every one of the 39 cached outcomes re-proved; no mismatch |

A rebuilt `kink-flow` starts a new outcome context (the cache key includes the executable's digest),
so the first run after a rebuild re-proves each killed mutation with one call over its last killer,
as after the comment-only edit above, but without running the baselines again (their results are still current).
