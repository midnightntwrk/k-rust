# Collector planning

`suite.rs` checks the `krs-cli` collector planner against the small Cargo
packages under `fixtures/`: byte-identical plans for reordered metadata and
requests, explicit aliases, collisions, and dependency-only facets, path-free
canonical selection, explicit host-target and cfg inputs, rejection of missing
and ambiguous selections, and a generated collector that compiles.
It has no standalone verifier; `crates/krs-cli/tests/collector_planning.rs`
includes it as an integration test.

Run it from the repository root with:

```sh
cargo +stable test -p krs-cli --test collector_planning
```
