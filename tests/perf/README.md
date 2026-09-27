# Compile-performance harness

`tests/perf/bench.py` measures the KRS definition pipeline (`krs check`, `krs emit-k`, `krs build`) and the isolated Cargo stages inside it, over the KWasm, KMIR, and KEVM semantics ports.
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
`--krs PATH` measures an existing `krs` executable; otherwise the harness builds the release `krs` of this checkout into `<checkout scratch>/perf-krs-target` (`KRS_PERF_KRS_TARGET` overrides) with `cargo +stable`.
`--keep` keeps the scratch workspace and Cargo targets, which are otherwise deleted after each cell.

## Matrix

Stages:

- `krs-check`: `krs check`, which runs a host-target `cargo check`, builds and runs the generated collector, lowers, and checks.
- `krs-emit-k`: `krs emit-k`, which builds and runs the collector, lowers, and emits K and JSON.
- `krs-build`: `krs build`, which builds and runs the collector, lowers, and runs the k-rust native frontend.
- `cargo-check`: the host-target `cargo check` of the semantics crate that `krs check` runs, alone, with `--timings`.
- `collector-build`: `cargo build --timings` of the generated collector package alone.
  The harness generates the package with `krs expand` behind a `cargo` shim that stops at `cargo run`, so generation does not build it.

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
No mode is registered yet.
