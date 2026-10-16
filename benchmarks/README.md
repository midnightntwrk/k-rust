# krust benchmarks

`kbench` (`crates/k-rust-bench`) measures the release `krust` CLI on every workload of the benchmark registry and prints one report in a fixed format.
The report compares krust with reference K (K 7.1.337 and its Haskell and LLVM backends, at the pins of `scripts/reference-differential.toml`), whose figures come from a cache that is measured once per workload.

| Part | Location |
|:--|:--|
| Registry: what is measured, how, and how its output is checked | `benchmarks/registry/*.toml`, schema in [`registry/SCHEMA.md`](registry/SCHEMA.md) |
| Inputs and generators that no checkout provides | `benchmarks/programs/<semantics>/` |
| Cached reference K measurements | `benchmarks/reference.toml` |
| A run's samples and report | `target/kbench/runs/<run id>/results.toml` and `report.md` |
| Run history, one directory per run | `<main checkout>/draft-personal/benchmarks/<run id>/` |

## Running

Build the binary outside the timed region, then run a tier:

```sh
with-z3-static-4.16.0 cargo build --release -p k-rust --no-default-features --features cli --locked --bin krust
cargo run --release -p k-rust-bench -- run --tier standard
```

The report goes to standard output, to `target/kbench/runs/<run id>/report.md`, and to the history directory.
Progress and failures go to standard error.
The exit status is 0 when every selected workload passed its check, 1 when one failed, and 2 on a usage or setup error.

| Tier | Contents | Approximate cost |
|:--|:--|:--|
| `quick` | IMP, FUN, and small definitions; small ladders | minutes |
| `standard` | `quick` plus the KEVM, KWASM, and KMIR compiles and proofs | tens of minutes |
| `heavy` | everything: long ladders, KMIR execution, large KEVM runs | hours, many GiB |

`--only PREFIX` (repeatable; `*` matches anything) narrows a run, for example `--only imp/ --only '*/compile'`.
`--set NAME` (repeatable) runs the workloads of a named set whatever their tier (`kbench sets` lists the sets; [Comparing two builds](#comparing-two-builds) describes them).
A filtered run still lists every workload; the unselected ones say "not run".
`kbench list [--set NAME]` lists the registry, `kbench validate` checks it and the cache, `kbench run --dry-run` prints the resolved krust commands, and `kbench report RESULTS [--baseline RESULTS]` re-renders a report.

The checkouts default to the ignored `k/`, `imp-semantics/`, `wasm-semantics/`, `evm-semantics/`, and `mir-semantics/` links of the checkout and are overridden by `K_CHECKOUT`, `IMP_SEMANTICS_CHECKOUT`, `WASM_SEMANTICS_CHECKOUT`, `EVM_SEMANTICS_CHECKOUT`, and `MIR_SEMANTICS_CHECKOUT`.
Each workload names the pins its checkouts must be at; a checkout at another revision, or with modifications, fails that workload instead of measuring something else.
`K_KOMPILE` selects the reference K `bin` directory (default `k/result/bin`) and `KRUST_BIN` or `--krust` the krust binary (default `target/release/krust`).

## Reference cache

Reference K is slow to run and does not change between krust commits, so a run never measures it.
`kbench reference` measures the reference side of every paired workload that has no cached measurement, once, and records it in `benchmarks/reference.toml`, which is tracked.
A measurement is keyed by the SHA-256 of its reference command, its prepare steps, the reference runtime options (`K_OPTS`, no `GHCRTS`), the K version, and the pins of its checkouts.
A key that no longer matches (because the registry entry or a pin changed) shows as "stale" in the report; only then is `kbench reference --only ID` worth running again.
`--force` re-measures a cached workload and should be used only when the cached figure is known to be wrong, for example after it was measured on a loaded host.
A reference that fails or times out is cached with that outcome, so it is not retried either.

Measure the reference on an otherwise idle host: the cached figure is the denominator of every later speedup.

## Report format

The report has the same sections, columns, row order, and number formats every time, so two reports compare line by line:

1. A header: run id, tier, krust commit and binary digest, reference version and options, baseline run, host and load average before and after, and the measurement method.
2. **Coverage**: one row per semantics and one column per operation (`parse`, `compile`, `spec-compile`, `load`, `execute`, `search`, `prove`, `rpc`); each cell counts the workloads by reference status (● cached pair, ◐ pair not measured yet, ○ krust only, ? pairing not written).
3. **One table per semantics** in the order IMP, FUN, SIMPLE, KOOL, LAMBDA, small definitions, KEVM, KWASM, KMIR, KRS, rows sorted by operation then id, with the columns: workload, operation, krust wall, CPU, and peak; reference wall, CPU, and peak; speedup (reference wall / krust wall); memory ratio (krust peak / reference peak); and the change in krust wall and peak since the baseline.
   A workload the reference cannot run says why, with a reason code (`no-counterpart`, `missing-hook`, `ref-fails`, `ref-timeout`, `no-claims`).
4. **Scaling ladders**: every size of every ladder, with the growth exponent of wall time and peak memory.
5. **Failures**, the reason codes, the reference notes, and **what each workload measures**: one sentence per workload, with its origin.

Wall, CPU, and peak are medians over the timed runs; `results.toml` keeps every sample.
Times have three significant digits, memory is in MiB.

## History and baselines

Every run is copied to `draft-personal/benchmarks/<run id>/` of the main checkout (its own jj repository, ignored by Git), unless `--no-history` is given or `--history DIR` names another directory.
The baseline of a run is the latest history run of the same tier without a filter; `--baseline FILE` names another.
The run id is the UTC start time and the krust commit, with `-dirty` when the checkout has modifications.

## Comparing two builds

`kbench compare` decides whether a change makes krust cheaper without changing what it computes.
It runs the krust side of the selected workloads with two binaries and never runs reference K:

```sh
kbench compare --base A --candidate B (--set NAME | --only ID …) [--runs N] [--counters] [--output DIR]
```

Build both binaries outside the timed region and copy them to fixed paths first, so a rebuild cannot replace one during the comparison:

```sh
git worktree add ~/worktrees/k-rust-base main      # the base; the candidate is your branch's checkout
(cd ~/worktrees/k-rust-base && with-z3-static-4.16.0 cargo build --release -p k-rust --no-default-features --features cli --locked --bin krust)
with-z3-static-4.16.0 cargo build --release -p k-rust --no-default-features --features cli --locked --bin krust
mkdir -p /var/tmp/cmp && cp ~/worktrees/k-rust-base/target/release/krust /var/tmp/cmp/base && cp target/release/krust /var/tmp/cmp/candidate
cargo run --release -p k-rust-bench -- compare --base /var/tmp/cmp/base --candidate /var/tmp/cmp/candidate --set slowness-search
```

What it does:

- **Same work for both.** Each binary prepares its own definitions (its prepared root is keyed by its SHA-256, so a `kcompile` change reaches the execution workloads too); both read the same generated inputs and the same `${run}` directory.
- **Interleaved runs.** Every point (a plain workload, or one ladder value) runs A B, then B A, and so on, `--runs` times each (default 5), so a change in host load affects both alike; run `i` of A and run `i` of B form a pair.
  A plain quick-tier workload first runs its usual warmup pair.
- **Identical output.** Every timed run's output (standard output and the files its check names, with each binary's own prepared root and path replaced by placeholders) is hashed; all digests of a point, of A and of B, must be equal.
  A difference is reported at the top of the report (**Output: DIFFERS**) and makes the exit status 1.
  Output that varies between runs of the same binary (an RPC request's wall time, for example) is left out only by a `[workload.compare]` entry with a reason ([`registry/SCHEMA.md`](registry/SCHEMA.md)).
- **Checks.** Every run must pass its workload's check; a failure on either side stops that workload's ladder for both and makes the exit status 1.
- **Ladders.** Both binaries run the same values.
  A set's `ladder_max` caps a ladder for compare (`--full-ladders` ignores it); once either binary's median wall at a value exceeds the ladder's `stop_seconds`, neither runs a larger value, and the report says so.
  The report gives each binary's growth exponent of CPU time and of peak memory.
- **Per metric, per point.** CPU (user + system time of the whole process tree, the primary metric: it moves less with host load than wall), wall, and peak memory: each binary's median, the ratio B/A of the medians, the interval of the paired ratios, and a verdict.
- **Counters.** With `--counters`, each binary also runs once per point with `KRUST_COUNTERS` set, outside the timed runs (counting costs time).
  Both binaries must be `measure` builds (`cargo build --profile profiling -p k-rust --features cli,measure --bin krust`); `kbench` refuses otherwise.
  To time release builds and count with measure builds, name the latter with `--counters-base` and `--counters-candidate` (either implies `--counters`).
  The report shows every counter side by side at each workload's summary point, lists every counter that differs at any point (an unexpected difference is a behaviour change), and derives the cost per step: `rewrite.steps` (the states the execution loop visited, one rewrite step each; in a search, merged arrivals included), `execution.states_merged`, microseconds of CPU per step, and allocations per step.

### Verdicts and the noise band

The interval is the sign-test confidence interval of the median of the paired ratios B/A: with n pairs it runs from the k-th smallest to the k-th largest ratio, with the largest k whose coverage is at least 90 % (at 5 runs, the smallest to the largest ratio, 93.8 %).
It assumes nothing about the distribution of run times, which on a loaded host is skewed: a run that collides with another job is slow, never fast.
A metric is **better** (or **worse**) when the whole interval lies below (above) 1 and B/A moves by more than `--min-effect` (default 3 %); otherwise it is **within noise**.
The threshold keeps a tiny steady difference from being called a change, and the interval keeps one noisy run from being called one.
The report's Noise band section gives, per workload, the widest interval half-width: a change larger than it plus the threshold gets a verdict.

NOISE-VALIDATION

`kbench compare-report RESULTS [--min-effect PCT] [--first N]` renders a results file again, optionally judged with another threshold or with only the first N pairs, which shows what fewer runs would have concluded.

### Output

`results.toml` (every sample, digest, and counter) and `report.md` go to `--output` (default `target/kbench/compare/<timestamp>/`), and the report is printed.
The report has the same sections, columns, row order, and number formats every time: a header (binaries, selection, host load before and after, method, statistics); **Verdict** (output, checks, the count of better, worse, and within-noise points per metric, counters, exit status); **Summary** (one row per workload at the largest point both completed); **Ladders** (values run, growth exponents of each binary, why the ladder ended); **Every point**; **Noise band**; with `--counters`, **Cost per step**, **Counter differences**, and **Counters at the summary point**; **Failures**; **Notes** (skipped workloads and output opt-outs).
The exit status is 0 when every output is identical and every check passed, 1 otherwise, and 2 on a usage or setup error.
A workload whose measured command does not run the krust binary (the KRS tools) is listed as not compared.

### Sets

Named sets live in [`registry/sets.toml`](registry/sets.toml); `kbench sets` lists them.
The budgets are for a compare at the default five runs on a host at load 5 to 10.

| Set | Contents | Compare budget |
|:--|:--|--:|
| `slowness-concrete` | the long concrete runs: `imp/krun-tutorial-collatz-300`, `imp/krun-tutorial-primes-1000`, `imp/krun-sum`, `simple/krun-collatz-input` (to m = 80), `fun/krun-tail-recursion-ladder` and `fun/krun-callcc-loop-ladder` (to n = 4000), `toy/growth-map-update-control` | about 9 min |
| `slowness-search` | `krun --search-final` on strict-heated semantics: `imp/search-kink-sum` (to n = 1000), `imp/search-strict-heating` (to 2048), `imp/search-strict-heating-control`, `imp/search-kink-wide8` (to r = 256), `imp/search-kink-collatz`, `imp/search-kink-primes`, `simple/search-collatz-input` (to m = 30), `imp/search-sum` (to n = 3000) | about 8 min |
| `slowness-frontend` | `toy/parse-dn-ambiguous` (to n = 50), `toy/compile-list-literal`, `toy/growth-ambiguous-chain` (to n = 100), `imp/parse-statements` | about 3 min |
| `slowness-simplifier` | `toy/growth-predicate-ornot-chain` (to d = 8000), `toy/growth-predicate-implies-chain` (to d = 32,000), `toy/shared-rpc-simplify` | about 2 min |
| `slowness` | the four above | about 22 min |
| `regression` | 38 fast workloads: parse, compile, spec-compile, load, execute, search, prove, and rpc on IMP, FUN, SIMPLE, KOOL, KEVM, KWASM, and KMIR | about 13 min |

The caps drop the values that cost 15 to 35 s per run and keep at least three sizes above 0.05 s for each growth exponent; `--full-ladders` runs the registry's ladders.
A change is decided on its topic's set and shown harmless on `regression`.

## Measurement method

Each run of a command (or of a short sequence of commands timed as one unit) gets a fresh cgroup v2 child of a delegated user systemd scope, which `kbench` enters by re-running itself under `systemd-run --user --scope -p Delegate=yes`.
Before the run starts, `kbench` moves itself into the run's cgroup, outside the timed region, so every process the run forks starts there and no process changes cgroup while it is timed.
Its figures are:

- wall time from the first process start to the last exit;
- CPU time, the cgroup's `cpu.stat` user plus system time, which includes every process of the tree;
- peak memory, the cgroup's `memory.peak`: every process of the tree that is resident at the same moment, summed, plus the page cache the run itself brings in (files written, and files read that were not cached yet).

The tree-wide peak matters for reference K: `kompile` and `kprove` are a JVM that starts backend children (`kore-exec`, `z3`, a C compiler) while it is still resident, and the largest single process undercounts their sum.
Pages already in the page cache, such as executables and JARs after the first run, stay charged to the cgroup that read them first and are not counted.
The run's cgroup also carries the workload's memory limit (`memory_gib`, default 16 GiB, no swap), so a run that exceeds it is killed and reported as out of memory; a timeout kills the run's process group.
If `kbench` runs inside a memory-limited cgroup, the tightest limits of that cgroup and its ancestors are copied onto the new scope.
Where no user systemd manager can delegate a scope (an `agent-N` sandbox, for example), or with `--no-cgroup`, wall and CPU time are still measured and peak memory is reported as unknown.

The reference JVM runs with `-Xmx4096m`; a JVM grows its heap toward its limit before it collects hard, so the reference peak reflects that limit as well as the data the workload keeps live.

## Operations

| Operation | krust | Reference K |
|:--|:--|:--|
| `parse` | `krust kast` of a program | `kast` |
| `compile` | `krust kcompile` of a semantics | `kompile` (`--backend haskell`, or `llvm` for execution) |
| `spec-compile` | compile a spec against prepared semantics into a proof-ready bundle | none: `kprove` always compiles its spec |
| `load` | read a proof-ready bundle and internalize the backend, no proof | none |
| `execute` | concrete execution: `krust krun` or `krust kore-exec` (or a tool built on krust) | `krun` on a prepared definition (LLVM or Haskell) |
| `search` | `krust krun --search-*` | `krun --search` |
| `prove` | `krust kprove` of a source spec against prepared semantics; or, krust only, of a proof-ready bundle (ids `*/execute-*`) | `kprove` (always from a source spec) |
| `rpc` | `krust kore-rpc` on a request file | `kore-rpc-booster` |

A pair compares the same work only where the table says so: a paired `prove` row includes the spec compile on both sides, while a bundle proof (`imp/execute-*`, `kevm/execute-trivial-claim`) measures krust alone on prepared work that the reference has no counterpart for.

## Adding a workload

Add a `[[workload]]` to the registry file of its semantics (schema in [`registry/SCHEMA.md`](registry/SCHEMA.md)).
Give it a stable id (history is keyed by it), a title a reader understands without context, one sentence on what it stresses and why it is in the suite, where it came from, a tier, the pins of its checkouts, and a check that fails on a wrong result.
Put inputs that no checkout provides, and their generators, under `benchmarks/programs/<semantics>/` with a README naming their origin.
Pair it with reference K where reference K can run it, run `kbench reference --only ID` once on an idle host, and commit the registry entry together with the cache entry; otherwise state why with a reason code.
A program that drove an optimization belongs here, so the optimization's effect stays visible in later reports.

## Profiling

Hyperfine says how long a whole invocation takes; a sampling profile says where the time goes.
`scripts/profile.sh` records one of the benchmark's krust workloads under
[samply](https://github.com/mstange/samply) and writes a profile the Firefox Profiler opens.

Build the binary once with the `profiling` Cargo profile:

```sh
cargo build --profile profiling -p k-rust --bin krust --locked
```

`[profile.profiling]` inherits `release` and adds line tables (`debug = "line-tables-only"`, `strip = "none"`), so the machine code is what `release` runs and every inlined frame still resolves to a source line.
`lto` stays at the release default, unlike `dist`, because the differential gates and `kbench` run `release` builds.

Record a workload:

```sh
taskset -c 0-15 scripts/profile.sh --workload imp-compile
taskset -c 0-15 scripts/profile.sh --workload imp-prove --claim IMP-SIMPLE-SPEC.sum-loop
taskset -c 0-15 scripts/profile.sh --workload kevm-compile --dry-run
```

### Native-host samply setup

Sampling is host-only on this machine. An `agent-N` sandbox is deliberately denied
`perf_event_open` by its seccomp policy, so it must not try to record a profile.
The host UID must also use the machine's CPU-affinity workaround:

```sh
taskset -c 0-15 scripts/profile.sh --workload kevm-compile
```

The native host exposes 32 logical CPUs, while `kernel.perf_event_mlock_kb = 516`
does not permit samply's approximately 1 MiB perf ring buffer on every CPU.
Without the affinity mask, the ring-buffer `mmap` eventually returns `EPERM` and
samply reports only `mmap failed`. The `0-15` mask is the machine's documented
configuration and is sufficient for these single-threaded workloads.

Run the first profile attempt from a plain host shell. Do not put samply itself
inside `systemd-run --user --scope -p MemoryMax=...`; that is a cgroup resource
limit, not a sandbox, but it can confound profiler-startup failures. If the
workload needs a memory guard, use a separately recorded `--skip-profile` run for
timings, RSS, and counters. A minimal smoke test is:

```sh
taskset -c 0-15 samply record --save-only --rate 100 \
  --output /tmp/samply-smoke.json.gz -- true
```

The workloads are the krust commands of registry workloads: `imp-compile` is `imp/compile`, `kevm-compile` is `kevm/compile`, and `imp-prove` is `imp/execute-sum-loop`, `kprove` on a prepared bundle (default claim `IMP-SIMPLE-SPEC.sum-loop`).
The script checks the checkouts' pins itself and accepts `--allow-unpinned` for exploratory runs; `KRUST_BIN` defaults to `target/profiling/krust` and must carry line tables.
Prepared proof bundles live under `target/profiles/work/<suite>/` and are reused by the same binary only; set `PROFILE_WORK_ROOT` to a fresh directory after a source or option change.

Each run writes `target/profiles/<timestamp>-<workload>/` (or `--output DIR`) with:

- `profile.json.gz`, the samply profile; open it with `samply load DIR/profile.json.gz`.
- `command.txt`, the exact preparation, unprofiled, and record commands.
- `metadata.json`: revisions, tool versions, the binary's sha256, host, sampling rate and sample count, and the wall time and peak RSS of both runs.
- `unprofiled.*` and `profiled.*`: stdout, stderr, and `meta.toml` of the two runs, from `scripts/conformance/measure.py`.
- `timings.json` from `kprove --timings` (and from `kcompile --timings` once the binary supports it), and `counters.json` when the binary was built with the `measure` feature (`KRUST_COUNTERS` is exported for every run and ignored otherwise).

The workload runs twice: once unprofiled, for the baseline wall time and peak RSS, and once under `samply record`.
The profiled run's numbers are also recorded but include samply's own work, so quote the unprofiled ones.
The script fails when the profile holds zero samples; the first run on a new host is the check that `perf_event` delivers software-clock samples there.
Where profiling is unavailable, `--skip-profile` records everything except the profile. On this machine that fallback is for sandbox runs or for a host that has not been given the documented affinity; it does not mean the K-Rust workload failed.

`kevm-compile` needs gigabytes of memory. Its unprofiled and `--skip-profile` runs may use `scripts/reference-memory-guard.sh` or `systemd-run --user --scope -p MemoryMax=16G`; do not apply that wrapper to the first samply attempt.
As an `agent-N` user the script prints the resolved command and exits 3 unless `--allow-sandbox-kevm` is given, so an agent does not start it by accident.

Profiles are machine-local artifacts like benchmark results: they live under the ignored `target/` tree, `cargo clean` removes them, and a profile worth keeping is copied elsewhere together with its `metadata.json`.

