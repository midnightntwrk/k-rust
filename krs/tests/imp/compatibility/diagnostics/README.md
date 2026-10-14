# Diagnostic-boundary adversaries

Each subdirectory owns one intentional failure and an exact authored anchor.
The fixtures do not accept a raw collector path, generated `.k` location, or
unstructured backend string as a substitute for an authored Rust range.

- `rust-expansion` checks rustc's primary macro span, and its `lsp_probe.py`
  requires rust-analyzer to issue the same document diagnostic.
- `krs-analysis` contains a cross-item emitted-symbol collision.
  The production CLI returns one schema-1 `analysis`/`krs::analysis::symbol-name-collision` JSON envelope selecting the exact second authored `Collision` byte range.
- `k-frontend` supplies a sidecar-driven mutation probe over the emitted
  `spec.k`. It accepts only an exact generated range with an exact ranged
  authored origin and requires K's four-coordinate `Location` to select that
  generated range before mapping it back.

The native boundary is covered in Rust rather than here:
`crates/krs-cli/tests/cli_commands.rs` builds an authored equation that k-rust
rejects on both backends and requires one schema-1 `native` JSON envelope
selecting the exact authored item.

The IMP gate runs every probe here; there is no separate static audit. The
analysis probe accepts `--krs PATH` to exercise the production CLI end to end.
