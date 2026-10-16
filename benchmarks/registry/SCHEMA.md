# Benchmark registry schema (version 1)

Every `*.toml` file in this directory is one part of the benchmark registry that `kbench` reads.
A file holds `version = 1`, any number of `[[prepare]]` steps, `[[workload]]` entries, and `[[gap]]` entries.
Names of prepare steps and workload ids are global across all files and must be unique.
Files are grouped by semantics for readers; the grouping carries no meaning for `kbench`.

## Placeholders

Strings in `argv`, `creates`, `stdin`, `env` values, `files`, check strings, and ladder inputs expand these placeholders:

| Placeholder | Value |
|:--|:--|
| `${workspace}` | the k-rust checkout root |
| `${k}` | the K checkout (`K_CHECKOUT`, default `${workspace}/k`) |
| `${imp}` | `IMP_SEMANTICS_CHECKOUT`, default `${workspace}/imp-semantics` |
| `${wasm}` | `WASM_SEMANTICS_CHECKOUT`, default `${workspace}/wasm-semantics` |
| `${evm}` | `EVM_SEMANTICS_CHECKOUT`, default `${workspace}/evm-semantics` |
| `${mir}` | `MIR_SEMANTICS_CHECKOUT`, default `${workspace}/mir-semantics` |
| `${builtin}` | `${k}/k-distribution/include/kframework/builtin` |
| `${programs}` | `${workspace}/benchmarks/programs` |
| `${krust}` | the krust binary being measured (`--krust`, `KRUST_BIN`, default `${workspace}/target/release/krust`) |
| `${kbin}` | the reference K `bin` directory (directory of `K_KOMPILE`, default `${workspace}/k/result/bin`) |
| `${prepared}` | the engine's prepare root: keyed by the krust binary's SHA-256 for `krust` steps and by the K version for `reference` steps |
| `${run}` | the measured run's scratch directory, emptied before every run outside the timed region |
| `${input}` | the generated input file of a ladder value |
| `${<param>}` | the ladder parameter (for example `${n}`) |
| `${expect}` | the value of `check.expect` or `check.expect_out` |

## `[[prepare]]`

An unmeasured step run before the first workload that names it.
It is skipped when `creates` exists.
A step named by a ladder workload runs for each ladder value and may use the ladder parameter and `${input}` (give `creates` a path that contains them).
A ladder parameter must not be named like a placeholder above.

| Key | Meaning |
|:--|:--|
| `name` | unique step name |
| `engine` | `krust` (argv follows the krust binary), `reference` (argv\[0\] is a tool in `${kbin}`; the reference runtime options apply), or `command` (argv\[0\] is a path or a program on `PATH`) |
| `argv` | arguments |
| `creates` | a file the step creates |
| `prepare` | optional names of steps this one needs first |
| `env` | optional extra environment |
| `timeout_seconds` | optional, default 3600 |

## `[[workload]]`

| Key | Meaning |
|:--|:--|
| `id` | `<semantics>/<slug>`, stable forever: history is keyed by it. Renaming a workload is a new workload. |
| `semantics` | `imp`, `fun`, `simple`, `kool`, `lambda`, `toy`, `kevm`, `kwasm`, `kmir`, `krs` |
| `operation` | `parse`, `compile`, `spec-compile`, `load`, `execute`, `search`, `prove`, `rpc` |
| `title` | plain-words name shown in the report, for example "Prove sum-loop (the loop is its own invariant)" |
| `stresses` | one sentence: the behaviour this workload exercises and why it is in the suite |
| `origin` | optional: where it came from (a commit, a ticket, a former script) |
| `tier` | `quick` (seconds), `standard` (up to a few minutes), `heavy` (long or many GiB; runs only with `--tier heavy`) |
| `runs`, `warmup` | optional overrides; defaults below |
| `timeout_seconds` | optional per-run wall limit, default 600 (heavy: 3600) |
| `memory_gib` | optional per-run memory limit of the run's cgroup, default 16 |
| `pins` | `[reference.*]` sections of `scripts/reference-differential.toml` whose checkouts must be at their pinned revision: `k`, `imp`, `kevm`, `kevm-plugin`, `wasm`, `mir` |

Default runs: `quick` 5, `standard` 3, `heavy` 1; ladders run each value once.
Default warmup: 1 for `parse`, `load`, `execute`, `search`, `prove`, `rpc` in the quick tier, otherwise 0.

### `[workload.krust]` and `[workload.reference]`

Each side is one engine invocation, or a short sequence timed as one unit.

| Key | Meaning |
|:--|:--|
| `engine` | measured side only: `krust` (default) or `command`, for a tool built on k-rust such as `krs` whose argv\[0\] is a path |
| `argv` | one invocation (krust: after the binary; reference: argv\[0\] is a tool in `${kbin}`; command: argv\[0\] is a path) |
| `steps` | instead of `argv`: a list of argv lists run in order inside the timed region; their standard output is concatenated, and the check reads the concatenation |
| `prepare` | names of `[[prepare]]` steps |
| `stdin` | optional file for standard input, default `/dev/null` |
| `env` | optional extra environment |
| `check` | the output check (below) |

`[workload.reference]` additionally has:

| Key | Meaning |
|:--|:--|
| `status` | `paired` (argv given; measured once with `kbench reference` and cached in `benchmarks/reference.toml`), `unsupported` (reference K cannot run it; `reason` required), or `untested` (a pairing may exist but nobody has written it) |
| `reason` | for `unsupported`, one of: `no-counterpart` (reference K has no comparable operation, e.g. krust-only `load`), `missing-hook` (the reference backend lacks a hook the program needs), `ref-fails` (the reference errors on it), `ref-timeout` (the reference does not finish in the workload's limits), `no-claims` (no proof claims exist for the semantics) |
| `note` | plain-words detail for the reason, shown in the report |
| `backend` | for reference execution: `haskell` or `llvm`, shown in the report |

### `check`

| Key | Meaning |
|:--|:--|
| `exit` | expected exit status, default 0 |
| `stdout` | substrings standard output must contain |
| `stdout_squeezed` | substrings that standard output with all whitespace removed must contain |
| `stdout_absent` | substrings standard output must not contain |
| `files` | files that must exist and be non-empty after the run |
| `expect` | an integer expression over ladder parameters (`+ - * //`, parentheses) bound to `${expect}` |
| `expect_out` | a file whose `#Equals <int>` value is bound to `${expect}` |

### `[workload.ladder]`

The same workload at growing sizes; the report gives a growth exponent.

| Key | Meaning |
|:--|:--|
| `param` | parameter name |
| `values` | ascending values |
| `stop_seconds` | a value slower than this ends the ladder (default 120) |
| `input` | template written to `${input}` for each value |
| `generator` | instead of `input`: an argv (expanded) whose standard output becomes `${input}` |

## `[[gap]]`

A semantics and operation that has no workload on either side, so the report's coverage grid says why instead of showing an empty cell.

| Key | Meaning |
|:--|:--|
| `semantics`, `operation` | the cell |
| `reason` | a reference reason code, or `no-workload` when nothing measurable exists yet |
| `note` | plain-words detail shown in the report's Gaps section |

## Reference runtime options

Reference steps run with `K_OPTS='-Xmx4096m -Xss4m -Dscala.concurrent.context.numThreads=1 -Dscala.concurrent.context.maxThreads=1'` and without `GHCRTS`.
These are part of the cache key of `benchmarks/reference.toml`.
