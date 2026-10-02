# KWasm acceptance gate

Run `python3 tests/kwasm/verify.py` from the repository root to check the pinned KWasm corpus with the native K-Rust route.
The gate compiles Definition IR to KORE through the pinned K-Rust frontend, executes the corpus with the K-Rust backend, checks each expected outcome, and checks the native behavior digest against `pins.toml`.
This route does not require the Java K toolchain.

Each case declares what it observes and expects as data, in the format `tests/support/behavior.py` describes.
KWasm cases check `instrs` and `valstack`; `instrs` defaults to `.K` and trap cases override both cells.
The `expected_type`, `expected_value`, and `expected_outcome` case fields supply the pinned outcome report through `native.py`.
The `i32-add` and `i32-div-u-zero` cases set `search = true`, so the gate also checks the session's final-state search against the native execution of a value and a trap case.

Run `python3 tests/kwasm/verify.py --java-reference` to add the upstream K reference route.
The gate kompiles the emitted K definition, runs each case with `krun --output kore`, and passes the resulting KORE states to the `kore.read` session operation and checks them with the same structural expectations and outcome builder as the native route.
Both routes build each outcome from the corpus case once its expectations are met, so the routes agree exactly when every Java state meets the expectations its native peer meets.
The gate requires one Java outcome per native case id.
The Java-kompiled definition remains pinned, while reference behavior is checked against the corpus expectations.

The `--artifacts-only` option checks pinned emitted artifacts and native KORE without executing the behavior corpus.
The `--record` option updates measured output pins only after the complete selected gate passes; review any pin change before accepting it.
