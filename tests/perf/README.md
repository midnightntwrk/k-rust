# Compile-performance harness

`tests/perf/bench.py` measures the KRS definition pipeline (`krs check`, `krs emit-k`, `krs build`) and isolated Cargo stages over the KWasm, KMIR, and KEVM semantics ports.
It writes one versioned receipt per measured run and compares receipt sets.
It is measurement infrastructure only: it never changes KRS outputs, and it is not a pass/fail gate.
CI runs only its unit tests and `--dry-run`; wall time is never gated.

Run everything from the repository root.

```sh
python3 tests/perf/bench.py --list                      # ports, stages, scenarios, profiles
python3 tests/perf/bench.py --dry-run                   # the full matrix; verifies the edit anchors
python3 tests/perf/bench.py --port kwasm --runs 3       # measure every KWasm cell
python3 tests/perf/bench.py --port kevm --stage collector-build --scenario cold \
    --env CARGO_PROFILE_DEV_DEBUG=0 --label debug0      # one cell with a build override
python3 tests/perf/bench.py summary RECEIPTS...         # one table per port
python3 tests/perf/bench.py compare A B                 # A and B are receipt directories or files
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/perf -t tests
```

`--port`, `--stage`, and `--scenario` are repeatable and default to everything.
`--runs N` sets the repetitions of every scenario (default 3) and `--cold-runs N` overrides it for `cold`.
`--no-reuse` passes the same option to KRS commands, so `no-op` receipts can measure the full collector and compiler pipeline.
`--krs PATH` measures an existing `krs` executable; otherwise the harness builds the release `krs` of this checkout into `<checkout scratch>/perf-krs-target` (`KRS_PERF_KRS_TARGET` overrides) with `cargo +stable`.
`--keep` keeps the scratch workspace and Cargo targets, which are otherwise deleted after each cell.

## Matrix

Stages:

- `krs-check`: `krs check`, which builds and runs the generated collector, lowers, and checks.
- `krs-emit-k`: `krs emit-k`, which builds and runs the collector, lowers, and emits K and JSON.
- `krs-build`: `krs build`, which builds and runs the collector, lowers, and runs the k-rust native frontend.
- `cargo-check`: an isolated host-target `cargo check` of the semantics crate with `--timings`.
- `collector-build`: `cargo build --timings` of the generated collector package alone.
  The harness generates the package with `krs expand` behind a `cargo` shim that stops at `cargo build`, so generation does not build it.

Scenarios, in execution order within a cell:

- `cold`: an empty Cargo target for every repetition.
- `warm`: a built target from which `cargo clean -p` has removed the semantics crate only, so dependencies stay built.
- `no-op`: a built target and no source change.
- `touch`: a built target and a new mtime on the port's `src/lib.rs`.
- `edit-rule`: a built target and one changed rule-body token.
- `edit-enum`: a built target and one changed constructor-enum token.

Edits are defined per port in [`matrix.toml`](matrix.toml).
Each `old` string must occur exactly once in the port source; `--dry-run` checks this against the repository.
Repetitions of an edit scenario alternately apply and revert the edit, so each recompiles the same one-token change; the receipt records the direction.
Every scenario after `cold` starts from a built target: when a preceding step changed the source, an unmeasured settle run rebuilds it first.

## Isolation and environment

Every run uses a scratch copy of the semantics workspace (`semantics/Cargo.toml`, `Cargo.lock`, and the member sources, with the `../../crates/` paths made absolute) under `<checkout scratch>/perf-work/<run id>/`, where `<checkout scratch>` is `checkout_scratch()` from `tests/support/tools.py`.
Edits apply to that copy only; the repository's `semantics/` is never written.
Each cell has its own Cargo target under the same directory.

Every command receives `CARGO_NET_OFFLINE=true`, `RUSTUP_TOOLCHAIN=stable`, and the qualified Z3 library paths from `tests/support`.
Ambient variables that change Cargo or rustc behavior (`RUSTFLAGS`, `RUSTC_WRAPPER`, `CARGO_INCREMENTAL`, `CARGO_PROFILE_*`, `CARGO_BUILD_*`, `RUSTC_BOOTSTRAP`, and similar) are removed and listed in each receipt.
`--env KEY=VALUE` sets one back explicitly for every command of the run, including the settle runs, and is recorded as an override.
`RUSTC_BOOTSTRAP` is reserved for profiling modes: `--env RUSTC_BOOTSTRAP=...` is rejected without one.

## Measurement

The harness re-executes itself under `systemd-run --user --scope -p Delegate=yes`, copying the tightest `memory.max`, `memory.high`, and `swap.max` of its current cgroup and ancestors onto the scope.
Each measured command runs in its own child cgroup, entered between `fork` and `exec`.
After every process of the command has exited, the harness reads the child's `memory.peak` (the peak of the whole process tree: Cargo, every rustc, build scripts, the collector, and linkers) and the user and system CPU of `cpu.stat`.
Wall time is the monotonic time from spawn to reap.
Neither hyperfine's nor GNU `time`'s memory figure is used: each reports one process's maximum resident set, not the tree.

Without cgroup delegation (or with `--memory-method rusage`) the harness records wall time and the `wait4` user and system CPU of the reaped tree, and reports peak memory as `null`.

Runs are strictly serial.
The harness takes an exclusive lock (`<gate scratch root>/krs-perf.lock`, `KRS_PERF_LOCK` overrides) and refuses to start while another harness run or a `tests/<gate>/verify.py` verifier is running (`--allow-busy` overrides the latter check).
The KEVM, KMIR, and KWasm gates are memory heavy; do not run them alongside the harness, and in a memory-limited agent sandbox check the envelope before a KEVM or KMIR cold run.
Wall numbers from a loaded host are not comparable with numbers from an idle one; every receipt records the load average before and after its run.

`krs` stages pass `--timings FILE` when `krs --help` lists that option (and `--counters FILE` likewise), and ingest both documents into the receipt.
A `krs` without the option is measured the same way, with `krs_timings_status = "unsupported"`.
Cargo stages keep Cargo's `--timings` HTML report beside the receipts and extract the per-unit rows of the semantics crate and the generated collector.

## Receipts

Receipts are written to `<checkout scratch>/perf-receipts/<revision>[-dirty]/<run id>/<port>.<stage>.<scenario>.<repetition>.json`, beside `logs/`, `timings/`, and `cargo/` subdirectories.
`<checkout scratch>/perf-receipts/index.jsonl` lists every run by revision.
`--receipts DIR` writes a run elsewhere.
Receipts are never committed.

A receipt is one JSON object; its fields are:

```toml
schema = "krs-perf-receipt/1"
run_id = "UTC timestamp and harness pid; shared by every receipt of one invocation"
label = "--label, or null"
created = "UTC start time of the run"
revision = "{ commit, dirty, dirty_paths } of this checkout"
pins = "the parsed Krs.lock"
toolchain = "{ rustc_vv (rustc -vV as a table), cargo_version, rustup_toolchain, linker { configured, cc, ld }, cargo_home_config }"
host = "{ cpu_model, logical_cpus, usable_cpus, memory_bytes, kernel, machine, python }"
environment = "{ overrides (--env), stripped (ambient variables removed), fixed }"
flags = "the harness argv"
profiling = "true only for receipts from a profiling mode"
profile = "the profiling mode name, or null"
krs_binary = "{ path, sha256, accepts_timings, accepts_counters }, or null for Cargo-only runs"
port = "kwasm | kmir | kevm"
package = "the semantics package name"
stage = "krs-check | krs-emit-k | krs-build | cargo-check | collector-build"
scenario = "cold | warm | no-op | touch | edit-rule | edit-enum"
repetition = "1-based"
scenario_detail = "the edit and its direction, or the cleaned package"
command = "{ argv, cwd, target }"
exit_status = "exit code, or the negative signal number"
timed_out = "boolean"
wall_seconds = "number"
user_seconds = "number"
sys_seconds = "number"
peak_memory_bytes = "cgroup memory.peak of the whole tree, or null"
measurement_method = "cgroup-v2 | wait4-rusage"
load_average = "{ before, after }: the 1, 5, and 15 minute load averages"
krs_timings_status = "collected | missing | invalid | unsupported | not-applicable"
krs_timings = "{ schema, total_wall_seconds, unattributed_seconds, spans [{ id, seconds, depth }], counters { name = number }, document (the original) }, or null"
krs_counters_status = "collected | missing | invalid | unsupported | not-applicable"
krs_counters = "{ schema, counters { dotted name = number }, document (the original krs-counters document) }, or null"
cargo_timings = "{ html, total_seconds, units [{ name, target, mode, start, duration }] } for Cargo stages, or null"
log = "combined stdout and stderr, relative to the receipt directory"
rustc_profile = "only in `rustc` and `rustc-trace` modes: { status, measureme { status, version, note }, flags, invocations [{ crate, exit_status, wall_seconds, time_passes [{ pass, seconds, rss_start_mb, rss_end_mb }], time_passes_total_seconds, macro_stats [{ macro, uses, lines, bytes }], self_profile { total_seconds, queries [{ label, self_seconds, seconds, invocations, cache_hits, incremental_load_seconds }], artifact_sizes }, phases { categories, sum_seconds, span_seconds, top_level, llvm_passes_worker_seconds }, phases_method, trace }] }"
sampled_profile = "only in `samply` mode: { status, profile, summary, folded, rate_hz, cpus, processes [{ process, binary, samples, cpu_seconds, named_fraction, binary_fraction, attributed_fraction, top_self, spans }] }"
```

## Comparison

`compare A B` groups each side's receipts by (port, stage, scenario) and follows the k-rust `algo-graph diff` rule:

- a side's value is the median of its repetitions (the mean of the middle two for an even count) with the min..max range;
- a time or memory quantity is `unreplicated` when either side has fewer than two repetitions, `within noise` when the two closed ranges overlap, and otherwise `faster` or `slower` (`lower` or `higher` for memory);
- exit status and `krs` counters are deterministic and compared exactly: `exact`, `changed`, or `varies` when a side's repetitions disagree;
  in edit scenarios, repetitions are compared only with repetitions of the same edit direction, because applying and reverting the edit legitimately change counters.

Compared quantities are exit status, wall, user, and system time, peak memory, the Cargo time of the semantics crate, each `krs` span id (summed per id), `total_wall_seconds`, `unattributed_seconds`, and every counter.
Ranges are run-to-run spread under one sequence, not confidence intervals, and there are no statistical tests.
Profiled receipts are never compared with unprofiled ones.
A warning names cells whose environment overrides differ, which is expected when the overrides are the subject of the comparison.

## Profiling modes

`PROFILES` in `bench.py` registers profiling modes, selected with `--profile NAME`.
A mode names the stages it applies to and the environment it adds (the only route by which `RUSTC_BOOTSTRAP` reaches a command); its receipts carry `profiling = true`.
A mode may also rewrite each measured command (`wrap`) and add a field to its receipt afterwards (`collect`, stored under the mode's `receipt_field`: `sampled_profile` or `rustc_profile`).

## Sampled profiles

The `samply` mode (`tests/perf/sample.py`) applies to the `krs` stages.
It runs each measured command as `taskset -c 0-15 samply record --save-only --unstable-presymbolicate --rate 1000`; samply follows child processes, so one profile holds `krs`, Cargo, and the collector executable.
The CPU mask avoids samply's `mmap failed` on this 32-CPU host (`KRS_PERF_SAMPLY_CPUS` and `KRS_PERF_SAMPLY_RATE` override the mask and the rate).
`perf_event_open` must be permitted (`kernel.perf_event_paranoid` at most 2 for one's own processes); an `agent-N` sandbox refuses it.

After each run the profile is folded beside the receipt, under `profiles/`:

- `<cell>.samply.json.gz` and `<cell>.samply.json.syms.json.gz`: the profile and its symbol sidecar (`samply load` opens the profile);
- `<cell>.folded.gz`: folded stacks, one `process;outermost;...;innermost count` line per stack;
- `<cell>.summary.json` (`krs-perf-sampled-profile/1`): per process, the on-CPU sample count, CPU seconds, the fraction of samples whose leaf frame is named (`named_fraction`; unnamed leaves are mostly in a stripped `libc`), the fraction with at least one named frame of the process's own executable (`attributed_fraction`), the top self and inclusive functions, the innermost KRS or k-rust function of each sample (`top_first_party`), self and inclusive shares by crate, and the inclusive share of the functions that implement each `--timings` span (`SPAN_FUNCTIONS`).

Only on-CPU samples count: samply also emits samples of sleeping threads, with a zero CPU delta.
Names come from samply's sidecar; for every executable still on disk (`krs` and the collector), `addr2line -i` also restores inlined calls from the line tables.
Generic argument lists are dropped, so the instances of one generic function aggregate.
The crate of a function is the first path segment of its demangled name (the receiver type's crate for `<Type as Trait>::method`); `core`, `alloc`, and `std` are `std`, and a foreign symbol is filed under its library.

A profiled run's wall and CPU include samply and are not quoted.
`sample.py run` performs the k-rust `scripts/profile.sh` discipline: it builds a profiling `krs` (the release profile with `debug = "line-tables-only"` and `strip = "none"`, as Cargo environment overrides, into `<checkout scratch>/perf-krs-profiling-target`), runs the selection unprofiled with that executable (the companion, labelled `<label>-<collector>-companion`, whose numbers are quoted), then again with `--profile samply`:

```sh
flock /tmp/krs-perf-heavy.lock python3 tests/perf/sample.py run --port kevm --stage krs-build --scenario no-op --runs 1
python3 tests/perf/sample.py run ... --collector optimized     # collector at opt-level 3 with line tables
python3 tests/perf/sample.py show <receipts>/profiles/<cell>.summary.json
python3 tests/perf/sample.py fold PROFILE.samply.json.gz [--binary EXE]
```

`--collector` selects the collector build through `--env` overrides of its `dev` profile: `as-is` (opt-level 0, full debuginfo, what `krs` runs), `line-tables` (`CARGO_PROFILE_DEV_DEBUG=line-tables-only`), or `optimized` (also `CARGO_PROFILE_DEV_OPT_LEVEL=3`).
The overrides reach every command of both runs, including the settle builds, and are recorded in the receipts.

## Scaling ladders

`tests/perf/ladder.py` measures one `krs` stage (default `krs-build`) at ascending values of a size parameter and fits each metric's growth exponent.
Ladders are defined in [`ladders.toml`](ladders.toml):

- `truncate` ladders (`kevm-fraction`, `kmir-fraction`) keep 1/8, 1/4, 1/2, and all of a port's rewrite rules (the statements of its `k::rules!` blocks) and equations (its `#[k::equation]` functions), evenly spread and nested, and every declaration ([`truncate.py`](truncate.py)).
  They run in a scratch copy of the semantics workspace whose `warnings = "deny"` lints become `"warn"`, since removed rules can leave unused imports.
- `synthetic` ladders run a generated single-crate definition ([`synth.py`](synth.py)) that grows one aspect: many small rules, few large rules, deep terms, wide constructor enums, deep and dense `k::sorts!` hierarchies (the membership ancestor closure), and provenance anchors per rule.
  The crate reuses the lock file of `tests/tour-minimal` and is generated into scratch only.

```sh
python3 tests/perf/ladder.py --list
python3 tests/perf/ladder.py --dry-run [--ladder NAME ...]          # generates every rung in memory
python3 tests/perf/ladder.py --ladder sorts-deep --values 16,64,256 --runs 2 --llvm-lines
python3 tests/perf/ladder.py report RECEIPTS... [--all-metrics] [--json] [--write DIR]
python3 tests/perf/ladder.py generate --ladder kevm-fraction --value 2 --out DIR
```

Ladders of one family (`semantics` or `synth`) share a Cargo target within an invocation; an unmeasured settle run builds its dependencies once.
Before every measured repetition the definition crate and the generated collectors are removed with `cargo clean -p`, so each rung compiles the definition from scratch against built dependencies.
A rung whose median wall time exceeds `stop_seconds` (or `--stop-seconds`), or whose every repetition fails, ends its ladder.
`--llvm-lines` runs `cargo llvm-lines --lib` on the definition crate after each rung (an extra, unmeasured compile) and stores the total and the 200 largest functions.

Receipts are ordinary `krs-perf-receipt/1` receipts with scenario `ladder:<name>:<value>`, port `synth` for synthetic ladders, and an extra `ladder` object (definition, value, generated source size, truncation counts, LLVM IR lines).
Receipts of the same ladder from two revisions therefore compare with `bench.py compare`.

The fit ([`growth.py`](growth.py)) follows k-rust's atlas: ordinary least squares of ln(metric) on ln(size) over the successful rungs' medians, with R² and the top slope between the two largest sizes.
Fitted metrics are wall, CPU, and whole-tree peak memory, every `krs --timings` span, every `krs --counters` counter (bundle bytes among them), the generated source size, and the LLVM IR lines.
Wall, CPU, peak memory, and LLVM IR lines are also fitted against the counters `descriptors.total`, `provenance.anchors`, `provenance.origin_frames`, `bundle.bytes`, and `definition.sentences`, and against the source size.
A slope above 1.2 (fit or top slope; `--threshold`) is flagged with its stage: the span for a span metric, and for a whole-run metric the leaf span that grew most between the two largest values.
Flags also name the `cargo llvm-lines` function group (hashes and numbers normalized) that grew most between those values, when LLVM IR lines were collected.
Time metrics whose largest median is below 0.1 s are fitted but never flagged.
Peak memory is the whole process tree's; it is not attributed per stage.
Each run writes `ladder-report.md` and `ladder-report.json` beside its receipts.

## rustc profiling

The `rustc` and `rustc-trace` modes ([`rustc_profile.py`](rustc_profile.py)) apply to the `collector-build` stage (the collector's dev-profile, host-target build, in which the semantics crate is a dependency) and the `cargo-check` stage (an isolated host-target `cargo check`).
They set `RUSTC_WRAPPER` to a generated POSIX `sh` wrapper that forwards every rustc invocation unchanged except the semantics crate's (matched by `--crate-name`), which it runs with `RUSTC_BOOTSTRAP=1 -Ztime-passes -Zmacro-stats -Zself-profile=<dir>`.
`RUSTC_BOOTSTRAP` thus reaches one rustc process only: dependencies compile as in an unprofiled run, and in particular proc-macro2's build probe never sees it (with it, proc-macro2 enables its nightly span support and rebuilds every macro crate).
The wrapper streams rustc's stderr through `tee`, so Cargo's pipelining is unchanged; it keeps argv, start and end times, stdout, and stderr per invocation.

```sh
python3 tests/perf/rustc_profile.py tools     # build or locate measureme summarize and crox (automatic on first use)
flock /tmp/krs-perf-heavy.lock python3 tests/perf/bench.py --profile rustc --port kevm \
    --stage collector-build --scenario warm --runs 1
python3 tests/perf/bench.py --port kevm --stage collector-build --scenario warm --runs 3   # unprofiled reference
python3 tests/perf/rustc_profile.py report PROFILED_RECEIPTS --reference UNPROFILED_RECEIPTS
```

After each measured run the mode records, in the receipt's `rustc_profile`: the `-Ztime-passes` passes with RSS, the `-Zmacro-stats` table, measureme `summarize` query totals (the 60 largest by self time), and a phase decomposition.
The decomposition reads the `crox` trace of the driver thread: its top-level events tile the thread's busy time, containers (`analysis`, `resolver_for_lowering_raw`) are replaced by their children, and each event is filed as expansion, resolve, type checking, borrow checking, other analysis, metadata, codegen, llvm (the driver's `finish_ongoing_codegen` wait; LLVM's worker-thread time overlaps codegen and is reported separately), link, incremental, profiler (the self-profiler writing its strings), or other.
`report` prints the decomposition of each profiled cell and compares its sum with the median Cargo unit time of the semantics crate in unprofiled receipts of the same cell.
`-Ztime-passes` does not print nesting, so its passes are listed but not summed; the time-passes decomposition is used only when no trace is available.

`summarize` and `crox` are not packaged; the mode builds them once with `cargo install --locked --git https://github.com/rust-lang/measureme --tag <version>` into `<checkout scratch>/perf-tools/measureme-<version>/` (`KRS_PERF_TOOLS` moves it), at the measureme version linked into `librustc_driver` (12.0.3 for rustc 1.98), with lints capped because measureme denies warnings that newer compilers raise.
The build needs the network once; without the tools the mode records time-passes and macro-stats only.
`rustc-trace` additionally keeps the full Chrome trace (`profile/<cell>/trace.json`, several hundred MB for KEVM; open it in Perfetto) and the raw `.mm_profdata` beside the receipts.

The self-profile's own overhead is small with the default event set; the `touch` and `edit-*` scenarios profile an incremental rebuild, in which unchanged queries are loaded from the incremental cache and type and borrow checking nearly vanish.
`warm` (`cargo clean -p`, which also removes the crate's incremental directory) profiles a full compilation of the crate.

## Generated-code attribution

[`attribution.py`](attribution.py) groups the cost of one port's semantics crate by generated item, by source construct, and by macro kind:

```sh
flock /tmp/krs-perf-heavy.lock python3 tests/perf/attribution.py run --port kevm --registration both
python3 tests/perf/attribution.py report <out>/attribution.json [--top 25]
```

KRS macros name generated items `__krs_<kind>_<nonce>[_<n>]`; the 16-hex nonce identifies one construct (a `rules!` clause, a `#[k::rule]` or `#[k::equation]` sentence, a constructor, a constructor-enum variant, a sort, ...).
In a scratch copy, `run` builds the port's generated collector three times through the rustc wrapper:

1. with `-Zself-profile-events=default,args`, so that query events carry their item: per-item self time of `typeck_root`, `mir_borrowck`, `optimized_mir`, and the MIR queries they force, per-codegen-unit codegen and LLVM time, and `expand_proc_macro` time and source span per macro invocation; then `nm -S --size-sort -C` and `readelf -SW` of the collector executable (symbol bytes per section and the `.init_array` entry count);
2. after `cargo clean -p`, non-incrementally with `--emit=llvm-ir`, read by `cargo llvm-lines --files` (IR lines and copies per function);
3. `cargo check` with `-Zunpretty=expanded`, whose factories name their construct (`HostItemId::from_macro_context(.., name, ItemKind)`) and whose `HostSourceAnchor::new(..)` or `__KrsRawAnchor { .. }` expressions are the provenance anchors.

Every quantity is then grouped by item prefix, by construct, by generated construct kind, and by source macro (the innermost proc-macro invocation whose span covers the construct's invocation anchor, or the attribute macro just above it).
rustc performs codegen and LLVM per codegen unit, not per item, so codegen time is distributed over items in proportion to their IR lines (`codegen s*`); it is an estimate, not a measurement.
Provenance anchors are inline in their factories, so their cost is estimated by a least-squares fit, over all descriptor factories, of IR lines on expanded anchor lines and other expanded lines.
Query times come from a profiled build with query keys recorded, which inflates them; use them as shares.

`--registration explicit` (or `both`) repeats the measurement in `RegistrationMode::Explicit`: an inventory census of the port (as `tests/explicit-registration` takes one) yields the crate-root registration table, which is appended to the scratch source, every member's `krs` dependency gets `default-features = false` (feature unification is workspace-wide), and the collector is generated with `krs expand --registration explicit`.
The report then compares `.init_array` entries, binary and `.text` size, and the registration group's IR lines, expanded lines, and type-checking time between the two modes.
`attribution.json` (`krs-perf-attribution/1`) holds every table; it is written under `<checkout scratch>/perf-attribution/` unless `--out` names a directory.
