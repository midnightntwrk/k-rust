# krust versus canonical K benchmarks

This suite compares the release-mode `krust` CLI with the pinned canonical K frontend and its
Haskell backend. It measures whole tool invocations with
[Hyperfine](https://github.com/sharkdp/hyperfine), rather than using Criterion inside one process.
That keeps process startup, frontend work, backend initialization, and solver work visible in the
same way users experience them. A separate instrumented invocation also records Rust's actual
proof-engine time with `kprove --timings`.

The matrix contains:

- IMP compilation, prepared-definition loading, and small symbolic, branching, and loop-invariant
  proofs.
- KEVM functional-specification compilation, prepared-definition loading, and a concrete
  bit-operation proof.
- Raw per-run timings and process-tree peak memory in Hyperfine JSON, a Markdown comparison, exact
  commands, untimed preflight logs, source revisions, tool versions, host information, and runtime
  settings.

## Prerequisites

Build krust once outside the timed region:

```sh
cargo build --release -p k-rust --bin krust --locked
```

Install Hyperfine and `jq`. Both suites compile with `kompile` from the standalone K version pinned
in `scripts/reference-differential.toml` and prove with its matching `kprove` Haskell backend. The
KEVM workload is deliberately an independently provable functional claim rather than an APR
claim: this compares proof workflows without including KEVM's Python orchestration or
LLVM booster. The benchmark rejects mismatched K, IMP, KEVM, plugin, and tool versions by default.
Checkouts default to the ignored `k/`,
`imp-semantics/`, and `evm-semantics/` directories and can be overridden with `K_CHECKOUT`,
`IMP_SEMANTICS_CHECKOUT`, and `EVM_SEMANTICS_CHECKOUT`.

If canonical K is not on `PATH`, select its matching executables explicitly:

```sh
K_KOMPILE=/path/to/k/bin/kompile \
K_KPROVE=/path/to/k/bin/kprove \
scripts/benchmark.sh --suite imp
```

Use `scripts/benchmark.sh --list` to see every case and `--dry-run` to inspect the exact resolved
commands without requiring the external toolchains.

## Running benchmarks

Run the complete matrix:

```sh
scripts/benchmark.sh
```

Run one manageable slice while iterating:

```sh
scripts/benchmark.sh --suite imp --phase prove \
  --claim IMP-SIMPLE-SPEC.addition-var --runs 3 --warmup 1
scripts/benchmark.sh --suite kevm --phase compile --runs 1 --warmup 0
scripts/benchmark.sh --suite imp --phase spec-compile --runs 1 --warmup 0
scripts/benchmark.sh --suite imp --phase load --runs 5
scripts/benchmark.sh --suite imp --phase execute --claim IMP-SIMPLE-SPEC.sum-loop --runs 5
```

Results are written under `target/benchmarks/results/<timestamp>/`. The top-level `summary.md`
reports both means, the peak memory of each side, and the `krust / canonical` ratios; values below
one mean krust was faster or smaller. Each case retains its full sample distribution, including the
per-run memory samples, in `results.json`. Keep the generated `metadata.json`
beside it: timings without revisions, hardware, and runtime settings are not meaningful
comparisons.

## Peak memory

Each timed run's peak memory is measured over its whole process tree. Canonical `kompile` and
`kprove` are a JVM that starts backend children (`kore-exec`, `z3`, a C compiler), and those run while
the JVM is still resident, so the figure must sum processes that are resident at the same time.
The harness therefore runs each Hyperfine invocation inside a delegated user systemd scope
(`systemd-run --user --scope -p Delegate=yes`) and creates one empty cgroup v2 child per expected run
before Hyperfine starts. Each run's `--prepare` step, which Hyperfine does not time, first reads the
previous run's `memory.peak` and the page cache still charged to it (`file` in `memory.stat`), then
moves Hyperfine itself into the next empty child. The command Hyperfine forks next therefore starts in
that child, and no process changes cgroup inside the timed region: moving a process can wait for an
RCU grace period, which added about 10 ms per run on a busy host when the run moved itself. With the
move in the prepare step, interleaved runs of `imp/load` with and without it differed by less than
their noise (24 to 30 ms either way). The last run is read after Hyperfine exits. Warmup samples are
dropped.

`results.json` gains, per command, a `peak_memory` object (`tree_peak_bytes` per timed run, its
median and maximum, and `tree_page_cache_at_exit_bytes`), a top-level `memory_method`, and, for paired
cases, `krust_over_canonical` with the time and median-memory ratios. `summary.md` shows the median
with the maximum in parentheses, in MiB, next to the mean time.

What the figure includes: anonymous and kernel memory of every process in the tree, summed at the
moment of the peak, plus page cache the run itself brings in (files read that were not cached and
files written). It includes the harness's own `sh` and `bash` wrapper around each command, about
3 MiB on either side. Pages that were already cached, such as executables, shared libraries, and JARs after
the first run, stay charged to the cgroup that read them first and are not counted. In one sampled
run of `imp/prove-sum-loop` (2026-09-24), canonical `kprove` peaked at 1264 MiB with the JVM (about
253 MiB resident) and `kore-exec` (about 1011 MiB resident) alive together; a largest-process figure
would have reported only the 1011 MiB child.

Hyperfine's own `memory_usage_byte` stays in `results.json` but is not reported. It behaves as
`getrusage(RUSAGE_CHILDREN)`: the largest single process Hyperfine has reaped so far. It is not a
sum over the tree, and a command benchmarked after a larger one inherits that command's figure
(with Hyperfine 1.20, `true` measured after a 300 MiB allocation reports 309 MiB).

The canonical JVM's peak depends on its heap limit (`-Xmx4096m` in the default `REFERENCE_K_OPTS`):
a JVM grows its heap toward the limit before it collects hard. `summary.md` states the limit in force.
The harness does not tune it for either side; a comparison at another limit must say so.

If the benchmark itself runs inside a memory-limited cgroup, the tightest `memory.max`,
`memory.high`, and `memory.swap.max` of that cgroup and its ancestors are copied onto the new scope, so
a guard such as `systemd-run --user --scope -p MemoryMax=16G scripts/benchmark.sh` still applies.
Where no user systemd manager can delegate a scope with the memory controller (an `agent-N`
sandbox, for example), or with `BENCHMARK_MEMORY_METHOD=none`, the benchmark still runs and reports
peak memory as `unknown`.

## Finding local benchmark results

Benchmark result sets are intentionally machine-local generated artifacts rather than tracked
source. Inspect `target/benchmarks/README.md` first when it exists: it identifies the baseline that
the current workspace considers most relevant. Otherwise, enumerate
`target/benchmarks/results/*/REPORT.md` for curated reports and
`target/benchmarks/results/*/summary.md` for harness-generated tables. Each case directory retains
the exact commands, metadata, preflight logs, and raw Hyperfine JSON needed to interpret or compare
the measurement.

The repository ignores the entire `target/` tree, and `cargo clean` removes it. A benchmark result
that must survive workspace cleanup must be copied to durable storage or committed separately.

Defaults deliberately reflect the cost of the workloads: IMP compile/spec-compile uses three runs,
IMP loads and proofs use five, KEVM compile/spec-compile uses one run, and KEVM proofs and loads use three. Loads and proofs
get one warmup; compilation gets none. Override these counts for publication-quality runs,
especially KEVM compilation where one sample cannot estimate variance.

Every measured proof first runs once outside Hyperfine and must produce the expected successful
verdict. `--skip-preflight` exists for repeated local experiments, but should not be used for
recorded results. `--allow-unpinned` is likewise intended only for explicitly exploratory runs.

## Profiling

Hyperfine says how long a whole invocation takes; a sampling profile says where the time goes.
`scripts/profile.sh` records one of the benchmark's krust workloads under
[samply](https://github.com/mstange/samply) and writes a profile the Firefox Profiler opens.

Build the binary once with the `profiling` Cargo profile:

```sh
cargo build --profile profiling -p k-rust --bin krust --locked
```

`[profile.profiling]` inherits `release` and adds line tables (`debug = "line-tables-only"`, `strip = "none"`), so the machine code is what `release` runs and every inlined frame still resolves to a source line.
`lto` stays at the release default, unlike `dist`, because the differential gates and this benchmark run `release` builds.

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

The workloads are the benchmark's own commands: `imp-compile` and `kevm-compile` are the `compile` phase's krust command, `imp-prove` is the `execute` phase's `kprove` on a prepared bundle (default claim `IMP-SIMPLE-SPEC.sum-loop`).
Checkouts, pin checks, and `--allow-unpinned` work as for `scripts/benchmark.sh`; `KRUST_BIN` defaults to `target/profiling/krust` and must carry line tables.
Prepared proof bundles live under `target/profiles/work/<suite>/` and are reused like `BENCHMARK_WORK_ROOT`; set `PROFILE_WORK_ROOT` to a fresh directory after a compiler or option change.

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

## Interpreting the numbers

| Phase | Timed work | Comparison |
|:--|:--|:--|
| `compile` | Compile semantics from source and write artifacts | canonical / krust |
| `spec-compile` | Compile a new spec against parsed semantics; write a proof-ready bundle | krust only |
| `load` | Read and parse proof-ready KORE, then internalize the backend; no solver or proof | krust only |
| `execute` | Load the same proof-ready bundle, initialize the solver, and prove a claim | krust only |
| `prove` | Compile a fresh spec against prepared semantics, then load and prove it | canonical / krust |

`compile` runs canonical `kompile --backend haskell` and Rust `kcompile --for-proving` with the
same semantics main module. Fresh-output cleanup is outside the timed region. `spec-compile`
reuses `krust-definition/parsed.json` and `krust.json`; source parsing is skipped for prepared
semantics, but compiler transformations still run on the combined AST. Repeated spec compilation
overwrites the same output files and does not cache new spec parsing. This remains a substantial
cost for KEVM and is not a fully incremental compiler.

Preparation is outside `load`, `execute`, and `prove`. `load` and `execute` use
`krust-specification/definition.kore`, which includes the claims. Their Hyperfine results include
process startup and teardown. Do **not** subtract their averages to report actual proof time.
Each `execute` case additionally writes `phase-timings.json` and `timed-proof.log` from a separate
instrumented proof. Its `proof_seconds` measures only calls to `prove_claim`; `input_seconds`,
`internalize_seconds`, and `proof_setup_seconds` record input loading, backend internalization,
and solver/claim setup separately. Per-claim durations and verdicts are included. This is one
diagnostic sample, not the Hyperfine sample distribution, and excludes output and teardown.
Trusted claims and claims restored from saved proofs appear with `trusted` and `saved` statuses and zero proof time.

`krust kcompile --timings FILE` and `krust krun --timings FILE` write the same kind of diagnostic sample for compilation and execution.
The kcompile file lists every entry-source resolution, load, compile, and artifact-write phase in execution order under `phases`, with `load_seconds`, `compile_seconds`, and `write_seconds` as the sums of top-level phases. The corresponding `*_wall_seconds` fields record each group's wall-clock span, while `*_unattributed_seconds` reports the span not claimed by a top-level phase; `total_wall_seconds` is their sum. Nested phases carry a `depth` field and are excluded from the group sums.
The krun file nests that object under `compile` (its `write_seconds` is zero because nothing is written) and adds `program_parse_seconds`, `config_vars_parse_seconds`, `internalize_seconds`, `execute_seconds`, and `output_seconds`.
The benchmark cases do not write these two files; the flags are for one-off diagnosis of where a compile or run spends its time.

Only `prove` compares fresh-spec command latency: both tools receive a source spec and prepared
semantics. Canonical `kprove` still compiles the spec, so comparing it to Rust's `execute` would
give Rust an unfair preparation advantage. There is no canonical load-only or isolated proof
timing in this harness; Rust-only rows intentionally have no ratio. These measurements do not
establish an isolated Haskell-kernel-versus-Rust-kernel speedup.

Prepared artifacts are reused under `target/benchmarks/work/<suite>/`. They are not automatically
invalidated by source, compiler, or option changes. Use a fresh `BENCHMARK_WORK_ROOT` after such
changes. Result metadata records whether the krust worktree was dirty, but it is not an artifact
content hash.

For stable measurements, use an otherwise idle machine, fixed power/performance settings, the same
solver configuration, and sequential backend execution. The harness limits the canonical
frontend's Scala thread pool to one worker by default. `GHCRTS` is left unset because some
canonical K distributions use non-threaded Haskell executables that reject `-N1`; set it only when
the selected distribution supports the requested RTS options. Both values are captured in metadata
and can be overridden explicitly.
