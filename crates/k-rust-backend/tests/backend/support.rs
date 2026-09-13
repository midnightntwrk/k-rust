//! Fixture helpers shared by more than one module of the `backend` target.

use k_rust_backend::{definition::BackendDefinition, term::Term};
use k_rust_kore::kore::parser::parse_pattern;

/// Parse a KORE pattern and internalize it as a term of `definition`.
pub fn internal_term(definition: &BackendDefinition, source: &str) -> Term {
    let syntax = parse_pattern(source).expect("term should parse");
    definition
        .internalize_term(&syntax, &[])
        .expect("term should internalize")
}
