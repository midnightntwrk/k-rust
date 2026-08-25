# Rust-authored guarded rules

This standalone package exercises protocol-v11 `requires` through the complete
production path. `ordinary_positive` is an ordinary structured term rewrite;
`configuration_within` is a simultaneous fixed-configuration rewrite. Both
conditions are typed object-language `Bool` terms and use only bindings from
their pre-patterns.

The adjunct verifier runs ordinary Cargo gates, deterministic production CLI
`expand` and `emit-k`, and structured native `build`. The handwritten K files
in the parent directory remain the independent semantic oracle and are never
inputs to KRS.

