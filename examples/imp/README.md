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
- Killers (since flow F-13 the search tries the cheapest programs first): `sum` 7, `arith` 6, `and` 3, `redeclare` 2, `divzero` 1, `primes` 1.
  In the manifest's order (`--order corpus`, as before F-13) they are `sum` 8, `primes` 5, `arith` 3, `and` 2, `divzero` 1, `redeclare` 1;
  the statuses are the same in both orders.
  `divzero` and `redeclare` kill through the exit-stop oracle, not the final configuration
  (the report's `slots` show `exit-stop` distinguishing, `["normal"]` against `["undefined-step"]`):
  the baseline is stuck, and the mutant's rule now applies with an undefined result (`1 /Int 0`, a map with a repeated key).
- `collatz` is `timeout` (see below) and cannot kill a mutant. Its cause shows path explosion:
  `when the bound fired k-rust returned 1287 leaves (stuck 1286, cancelled 1), the deepest at depth 505; those leaves had applied 15 of the 17 rules a run can observe`,
  where a mutant that loops forever shows one cancelled leaf tens of thousands of steps deep.
- Every rule is targeted by some mutation except the two unlabelled rules on lines 55 and 65 (`untargeted_rules` in the report).

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

Since flow F-12 each program's baseline runs at most once per command:
the result update and every campaign call of a command share one in-memory baseline session,
so a call reuses the baseline runs this command already made (the run document's `baseline_runs: {live, reused}`).
Measured with the release binary before (F-14, `e7f5347`) and after F-12, same host session, each run under the 24 GiB scope above;
statuses, killers, killer sources and calls are equal in every scenario:

| Scenario | Before F-12 | After F-12 | Baseline runs after (live / reused) |
| --- | --- | --- | --- |
| cold run, fresh cache | 229.8 s (load 39) | 128.8 s (load 27) | 7 / 126: each program once, in the result update; every call reuses them |
| warm re-run, no change | 6.6 s | 6.2 s | 0 / 0: no campaign call |
| `outcomes/` deleted (each killed mutation one call over its hint) | 50.5 s | 24.9 s | 6 / 20 |
| comment-only edit of `imp.k` | 83.5 s | 47.9 s | 7 / 26 |

The cold run's peak memory comes from the mutants that loop until `time_ms` (6.8 GiB before and 15.5 GiB after here,
12.7 GiB in the F-14 table above): it depends on how far they get in 10 s on a loaded host, not on the baseline runs.

A rebuilt `kink-flow` starts a new outcome context (the cache key includes the executable's digest),
so the first run after a rebuild re-proves each killed mutation with one call over its last killer,
as after the comment-only edit above, but without running the baselines again (their results are still current).

## Cheaper killers first (flow F-13)

Inside each group of the kill search (the programs that reach an edited rule, then the rest) the programs run cheapest first,
by the wall time of their baseline run (`wall_ms` in `results`): here `redeclare`, `arith`, `and` and `divzero` take about 1 ms,
`sum` about 0.1 s and `primes` about 3.5 s. The order never changes a status, only which killer is found first and the cost.
Measured with the release binary on scratch copies, each run under the 24 GiB scope above (host load 19-25):

| Scenario | Cost order (default) | Corpus order (`--order corpus`) |
| --- | --- | --- |
| cold run, fresh cache | 38.1 s, peak 0.42 GiB; calls take 16.8 s in all | 120.1 s, peak 14.0 GiB; calls take 98.4 s in all |
| warm re-run, no change | 4.2 s, no campaign call | (as cost order: no call) |
| `outcomes/` deleted: each killed mutation one call over its hint | 20.7 s; a call takes 0.39 s on average, 0.70 s at most | 28.6 s; 0.96 s on average, 5.6 s at most (`primes`) |

Statuses are equal in every scenario (20 killed, `add-commuted` survived); five mutations get another killer
(`arith`, `redeclare` or `and` instead of `primes` or `sum`).
The cold run is cheaper mostly because a mutant that loops is now killed by a fast program before it can run a slow one to `time_ms`:
in corpus order six (mutation, program) runs time out after 10 s each and make the 14 GiB peak; in cost order none does.
