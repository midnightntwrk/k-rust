# krust versus canonical K benchmarks

This suite compares the release-mode `krust` CLI with the pinned canonical K frontend and its
Haskell backend. It measures whole tool invocations with
[Hyperfine](https://github.com/sharkdp/hyperfine), rather than using Criterion inside one process.
That keeps process startup, frontend work, backend initialization, and solver work visible in the
same way users experience them.

The matrix contains:

- IMP compilation plus small symbolic, branching, and loop-invariant proofs.
- KEVM functional-specification compilation plus a concrete bit-operation proof.
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
claim: this compares the proof engines directly without including KEVM's Python orchestration or
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
```

Results are written under `target/benchmarks/results/<timestamp>/`. The top-level `summary.md`
reports both means and the `krust / canonical` ratio; values below one mean krust was faster. Each
case retains its full sample distribution in `results.json`. Keep the generated `metadata.json`
beside it: timings without revisions, hardware, and runtime settings are not meaningful
comparisons.

Defaults deliberately reflect the cost of the workloads: IMP compile uses three runs, IMP proofs
use five, and KEVM compilation and proving use one run. IMP proofs get one warmup; the other cases
get none. A krust KEVM proof currently reloads a very large source closure, so additional samples
must be requested explicitly. Override these counts for publication-quality runs, especially KEVM
where one sample cannot estimate variance.

Every measured proof first runs once outside Hyperfine and must produce the expected successful
verdict. `--skip-preflight` exists for repeated local experiments, but should not be used for
recorded results. `--allow-unpinned` is likewise intended only for explicitly exploratory runs.

## Validated baseline

The harness was validated on an Apple M3 Max with 128 GiB RAM using krust 0.4.0, Rust 1.97.1, and
K 7.1.337. IMP proofs used five measured runs after one warmup. The KEVM proof used one measured
run and no warmup because of its current cost; treat that number as a baseline, not a variance
estimate.

| Suite | Case | Canonical mean | krust mean | krust / canonical |
|:--|:--|--:|--:|--:|
| IMP | compile (one sample) | 4.477 s | 2.653 s | 0.59x |
| IMP | addition-var | 1.930 s | 3.096 s | 1.60x |
| IMP | branching-program | 1.941 s | 3.090 s | 1.59x |
| IMP | sum-loop | 2.146 s | 3.147 s | 1.47x |
| KEVM | gfob-min (one sample) | 12.895 s | 974.529 s | 75.57x |

The KEVM proof itself reaches only two krust states. Its ratio is dominated by `krust kprove`
loading and compiling the entire KEVM source closure on every invocation, while canonical
`kprove` receives a prepared definition. It identifies prepared-definition reuse as the first
optimization required before interpreting this as a backend-kernel comparison.

## Interpreting the numbers

The compile phase compares preparation of the artifact each implementation needs for symbolic
execution from the same source and selected module. Canonical K runs `kompile --backend haskell`;
krust emits the KORE consumed by its in-process backend. Cleanup into fresh output directories runs
through Hyperfine's per-command `--prepare` hook and is not included in the timing. The generated
artifacts are architecturally different, so this is time-to-proof-ready-artifact rather than a
microbenchmark of one identical compiler pass.

The proof phase measures **user-facing proof command latency**, not an isolated backend kernel.
Canonical `kprove` consumes a prepared Haskell definition and kompiles the selected specification.
The current `krust kprove` command loads and compiles its source closure before proving in process.
Those architectural differences are part of the reported command time. Do not describe these
numbers as isolated Haskell-kernel-versus-Rust-
kernel execution until both backends are driven through an equivalent prepared KORE/RPC entry
point.

For stable measurements, use an otherwise idle machine, fixed power/performance settings, the same
solver configuration, and sequential backend execution. The harness limits the canonical
frontend's Scala thread pool to one worker by default. `GHCRTS` is left unset because some
canonical K distributions use non-threaded Haskell executables that reject `-N1`; set it only when
the selected distribution supports the requested RTS options. Both values are captured in metadata
and can be overridden explicitly.
