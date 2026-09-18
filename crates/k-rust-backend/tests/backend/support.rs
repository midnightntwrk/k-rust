//! Fixture helpers shared by more than one module of the `backend` target.

use k_rust_backend::{definition::BackendDefinition, term::Term};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

/// A single-constructor cell sort collected in a hooked set, with rewrite rules that add either
/// a distinct, unresolved cell value or an exact duplicate.
pub fn ground_cell_set_definition() -> BackendDefinition {
    let syntax = parse_definition(include_str!("../fixtures/ground-cell-set.kore"))
        .expect("ground cell set fixture should parse");
    BackendDefinition::internalize(&syntax, "GROUND-CELL-SET")
        .expect("ground cell set fixture should internalize")
}

/// A strict-list overload and `isKResult` equation pair used to distinguish concrete lowering
/// from symbolic sort membership.
pub fn ground_overload_definition() -> BackendDefinition {
    let syntax = parse_definition(include_str!("../fixtures/ground-overload.kore"))
        .expect("ground overload fixture should parse");
    BackendDefinition::internalize(&syntax, "GROUND-OVERLOAD")
        .expect("ground overload fixture should internalize")
}

/// Parse a KORE pattern and internalize it as a term of `definition`.
pub fn internal_term(definition: &BackendDefinition, source: &str) -> Term {
    let syntax = parse_pattern(source).expect("term should parse");
    definition
        .internalize_term(&syntax, &[])
        .expect("term should internalize")
}
