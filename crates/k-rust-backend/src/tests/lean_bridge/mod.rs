//! Model conformance: the proved definitions of `lean/KRust` run against the Rust they model.
//!
//! `driver` sends generated cases through the `krust-bridge` executable of `lean/` (library
//! `KRustBridge`, which evaluates the imported `KRust` definitions) and compares its answers
//! with the Rust's. `term_json` is the JSON form of the term model, and `generators` builds terms
//! through the public constructors. Each model has one test module.
//!
//! Opt-in: the tests are skipped with a message unless `K_RUST_LEAN_BRIDGE=1`; with the switch
//! set, a missing `lake` is a failure. `scripts/lean-check.sh --bridge` sets it.

mod attributes;
mod driver;
pub(super) mod generators;
mod term_json;
mod walks;
