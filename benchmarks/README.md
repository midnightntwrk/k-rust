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
- Raw per-run timings in Hyperfine JSON, a Markdown comparison, exact commands, untimed preflight
  logs, source revisions, tool versions, host information, and runtime settings.

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
reports both means and the `krust / canonical` ratio; values below one mean krust was faster. Each
case retains its full sample distribution in `results.json`. Keep the generated `metadata.json`
beside it: timings without revisions, hardware, and runtime settings are not meaningful
comparisons.

Defaults deliberately reflect the cost of the workloads: IMP compile/spec-compile uses three runs,
IMP loads and proofs use five, KEVM compile/spec-compile uses one run, and KEVM proofs and loads use three. Loads and proofs
get one warmup; compilation gets none. Override these counts for publication-quality runs,
especially KEVM compilation where one sample cannot estimate variance.

Every measured proof first runs once outside Hyperfine and must produce the expected successful
verdict. `--skip-preflight` exists for repeated local experiments, but should not be used for
recorded results. `--allow-unpinned` is likewise intended only for explicitly exploratory runs.

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
