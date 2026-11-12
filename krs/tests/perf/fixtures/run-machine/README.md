# The long-run `krs run` benchmark

A register machine written for the `krs/run-machine-*` workloads of `benchmarks/registry/krs.toml`.
It has the shape of a user workload measured on 2026-11-12, a CPU definition running a cartridge for 100,000 to 2,000,000 steps under `krs run`, and none of its content: the instruction set, the opcode map, the definition and the program are written here.

## Shape

| Part | Where | What it reproduces |
|:--|:--|:--|
| CPU as a cell group | `cpu/src/lib.rs`, `Cpu` and `k::rules! { for Cpu; .. }` | rules typed by a group, framed by the definition that holds it |
| Holder | `machine/src/lib.rs`, `Machine` | a `Bytes` program input, an `Int`-keyed `memory` map that starts with three I/O registers |
| Bus request and answer | `cpu::Bus`; `bus_read`, `bus_read_rom`, `bus_write`, `irq_sample` of `Machine` | an item the group leaves open and a holder rule answers, each its own step |
| Event log | the `log` cell, `List<BusEvent>` | one element appended per bus cycle |
| Instruction boundary | `boundary_sample`, `irq_sample`, `boundary_fetch` | three steps before every opcode fetch |
| Decoder | `cpu/src/decode.rs`, `Decode` | 39 equations in opcode-map order, 22 of them bit templates, 5 with a condition of their own, with three index tables beside it |
| Program | `benchmarks/programs/krs/run-machine/program.py` | a memory-clearing loop of 4,096 iterations, then a loop that polls an I/O register nothing writes |

## Steps

Every step is a rewrite step of the definition, so these counts are properties of the definition and the program, not of the host.

An opcode fetch is six steps for one bus cycle: `boundary_sample`, `irq_sample`, `boundary_fetch`, `fetch`, `bus_read_rom`, `fetched`.
Each further read is four steps: `load_t_immediate`, `read_t`, `bus_read_rom` (or `bus_read`), `latch_t`.
An instruction then takes one step to become its micro-operations and one step per register transfer.

| Instruction of the program | Steps | Bus cycles |
|:--|--:|--:|
| `liw r, nn` | 16 | 3 |
| `st [r4], r0` | 11 | 2 |
| `inc r`, `dec r` | 10 | 1 |
| `jr nz, n` taken (not taken) | 13 (12) | 3 (2) |
| `ldh r0, [n]` | 16 | 3 |
| `cmp r0, n` | 12 | 2 |

The clearing loop is 44 steps for 4 instructions, and ends after 180,255 steps; the polling loop is 41 steps for 3 instructions.

| Depth | Instructions | Bus cycles | Steps per instruction | Steps per bus cycle | Equation applications per step |
|--:|--:|--:|--:|--:|--:|
| 100,000 | 9,090 | 15,910 | 11.0 | 6.29 | |
| 400,000 | 32,465 | 71,554 | 12.3 | 5.59 | 0.80 |
| 1,000,000 | 76,367 | 188,626 | 13.1 | 5.30 | |

The rows at 100,000 and 400,000 steps are counted by `krs run --coverage --output none`; the row at 1,000,000 steps follows from the loop lengths.
The measured workload took 11.7 steps per instruction at 100,000 steps and 13.1 at 400,000, 5.84 and 5.45 steps per bus cycle, and 1.08 equation applications per step.

## Measurements

The figures below were taken on a shared host under load (32 logical CPUs, load average 9 to 11, other sessions building), with the release `krs` of `c0b075bb5`.
They show that the fixture has the measured workload's shape; they are not a baseline, and no comparison should be made against them.

```toml
[measured]
host = "x86_64 desktop, shared, load average 9 to 11"
baseline = false
date = "2026-11-12"

[measured."krs/run-machine-start"]
wall_seconds = 0.544
peak_mib = 102

[measured."krs/run-machine-100k"]
wall_seconds = 3.61
peak_mib = 153

[measured."krs/run-machine-1m"]
wall_seconds = 28.1
peak_mib = 786
steps_per_second = 36700      # (1,000,000 - 100,000) steps over the difference of the two walls
kib_per_step = 0.72           # the difference of the two peaks over the same steps

[measured."krs/run-machine-pretty-10k"]
wall_seconds = 3.04
peak_mib = 2991               # 1,591 log elements
```

Profile of a 400,000-step run (`perf record -F 1999 --call-graph fp` on a build with frame pointers, shares of the `krs-exec` thread, 27,469 samples), beside the measured workload's:

| Frame | Fixture | Measured workload |
|:--|--:|--:|
| `Execution::run` | 92.5 % | 94.5 % |
| `rewrite_step_any` | 82.5 % | 86.5 % |
| `simplify_lineage` | 61.7 % | 56.0 % |
| `apply_equation` | 48.3 % | 43.2 % |
| `apply_rule_phases` | 44.7 % | 51.2 % |
| `normalize_successor` | 32.8 % | 31.7 % |
| `evaluate_equation_condition` | 24.6 % | 21.9 % |
| `match_terms_reporting_bindings` | 22.3 % | 23.4 % |
| `instances_to_scan` | 19.3 % | 16.6 % |

Where the fixture differs from the measured workload:

- Start-up is 0.5 s, not 4.0 s: the definition is about a tenth of the size, so the frontend's share of a run is not reproduced.
- A step takes about 27 µs on this host, where the measured workload took 40 µs: the fixture's functions are fewer and their equation lists shorter, outside the decoder.
- Memory grows by 0.72 KiB per step, as the measured workload's did (0.70).

## Recording the baseline

The baseline is a `kbench` run on the baseline machine, kept in a history directory that outlives the checkout's `target/`:

```sh
cargo build --release -p k-rust --no-default-features --features cli --locked --bin krust
cargo run --release -p k-rust-bench -- run --tier standard --only krs/run-machine- --history "$KBENCH_HISTORY"
```

The run's `results.toml` holds every sample; steps per second and KiB per step are the differences of `krs/run-machine-1m` and `krs/run-machine-100k` over 900,000 steps.
`krs/run-machine-pretty-10k` is in the heavy tier, so that command does not run it; `--tier heavy --only krs/run-machine-pretty-10k` does.

## Memory limits

`kbench` runs every workload in a cgroup with the workload's `memory_gib` and no swap, and reports a run that exceeds it as out of memory (`benchmarks/README.md`, "Measurement method").
The limits are 2 GiB for the start and the 100,000-step row, 4 GiB for the 1,000,000-step row, and 6 GiB for the pretty row.
Where no user systemd manager can delegate a scope, `kbench` measures without a cgroup and enforces no limit: wrap it in a limit of the caller's there.
A run of `krs run` on this machine outside `kbench` has no limit of its own; `--output pretty` at 100,000 steps needs more memory than a desktop has.

## Running by hand

```sh
python3 benchmarks/programs/krs/run-machine/program.py >/tmp/program.bin
krs run /tmp/program.bin --depth 100000 --output none \
  --manifest-path krs/tests/perf/fixtures/run-machine/Cargo.toml \
  --package krs-perf-run-machine --definition main --dependency krs-perf-run-cpu:cpu
```
