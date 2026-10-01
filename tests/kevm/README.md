# KEVM acceptance gate

Run `python3 tests/kevm/verify.py` from the repository root to check the pinned KEVM corpus with the native K-Rust route.
The gate compiles Definition IR to KORE through the pinned K-Rust frontend, executes every corpus case with the K-Rust backend, checks each expected outcome, and checks the native behavior digest against `pins.toml`.
This route does not require the Java K toolchain.

Each case declares what it observes and expects as data, in the format `tests/support/behavior.py` describes.
KEVM requires the single execution leaf to stop with the top-level `reason = "stuck"`.
Case `observe` lists select additional storage, account, log, and state-stack checks.
Expectations that depend on configuration inputs must be declared explicitly in each case; corpus defaults supply constant expectations.
Top-level `[report]` names the outcome field of each reported cell.

Run `python3 tests/kevm/verify.py --java-reference` to add the upstream K reference route.
The gate kompiles the emitted K definition, runs supported cases with `krun --output kore`, and passes the resulting KORE states to the `kore.read` session operation and checks them with the same structural expectations and outcome builder as the native route.
Both routes build each outcome from the corpus case once its expectations are met, so the routes agree exactly when every Java state meets the expectations its native peer meets.
The Java reference route skips only the cases named with reasons in `HASKELL_BACKEND_GAPS`; every other native case must be compared.
The Java-kompiled definition remains pinned, while reference behavior is checked against the corpus expectations.

The `--artifacts-only` option checks pinned emitted artifacts and native KORE without executing the behavior corpus.
The `--record` option updates measured output pins only after the complete selected gate passes; review any pin change before accepting it.
