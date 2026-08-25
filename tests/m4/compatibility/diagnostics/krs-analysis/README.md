# KRS analysis boundary

Both modules are ordinary Rust and both macro expansions are locally valid.
Collection/semantic analysis must reject their duplicate emitted production
identity and report the second authored `Collision` token with a stable KRS
analysis code. `probe.py --krs PATH` requires exactly one schema-1
`analysis`/`symbol-name-collision` JSON envelope at `src/lib.rs` bytes
672..681 and rejects any generated collector path.
