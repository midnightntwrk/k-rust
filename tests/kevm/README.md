# KEVM acceptance gate

Run `python3 tests/kevm/verify.py` from the repository root to check the pinned KEVM corpus with the native K-Rust route.
The gate compiles Definition IR to KORE through the pinned K-Rust frontend, executes every corpus case with the K-Rust backend, checks each expected outcome, and checks the native behavior digest against `pins.toml`.
This route does not require the Java K toolchain.

Run `python3 tests/kevm/verify.py --java-reference` to add the upstream K reference route.
The gate kompiles the emitted K definition, runs supported cases with `krun --output kore`, and parses the resulting KORE states through the same observer and outcome checks as the native route.
It compares each Java outcome with the native outcome of the same case id and reports the first differing key if they disagree.
The Java reference route skips only the cases named with reasons in `HASKELL_BACKEND_GAPS`; every other native case must be compared.
The Java-kompiled definition remains pinned, while reference behavior is checked by case agreement.

The `--artifacts-only` option checks pinned emitted artifacts and native KORE without executing the behavior corpus.
The `--record` option updates measured output pins only after the complete selected gate passes; review any pin change before accepting it.
