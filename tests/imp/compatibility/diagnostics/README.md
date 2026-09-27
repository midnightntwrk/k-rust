# Diagnostic-boundary adversaries

Each of the first three subdirectories owns one intentional failure and an
exact authored anchor.
The fixtures do not accept a raw collector path, generated `.k` location, or
unstructured backend string as a substitute for an authored Rust range.

- `rust-expansion` is runnable now and checks rustc's primary macro span.
  The release runner must additionally issue the same document diagnostic
  through rust-analyzer.
- `krs-analysis` contains a cross-item emitted-symbol collision. The production
  CLI returns one schema-1 `analysis`/`symbol-name-collision` JSON envelope
  selecting the exact second authored `Collision` byte range.
- `k-frontend` supplies a sidecar-driven mutation probe over the emitted
  `spec.k`. It accepts only an exact generated range with an exact ranged
  authored origin and requires K's four-coordinate `Location` to select that
  generated range before mapping it back.
- `native-frontend` statically audits the structured native diagnostic seam:
  the adapter's diagnostic fields and the CLI's authored-origin translation and
  JSON rendering. It has no dynamic adversary.

`probe.py` is the static release audit. The analysis probe accepts `--krs PATH`
to exercise the production CLI end to end.
