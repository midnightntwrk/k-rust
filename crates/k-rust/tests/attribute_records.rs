//! The keys `AttributeKey::is_source_position` and `AttributeKey::is_provenance_only` classify
//! are the only ones that move when text before a sentence moves: a definition and the same
//! definition with a blank line inserted load to sentences whose attributes differ, and are
//! equal once those keys are removed.

use std::collections::BTreeMap;

use k_rust::definition::AttributeKey;
use k_rust::outer::{ResolvedSource, load};
use serde_json::Value;

const DEFINITION: &str = r#"module SHIFT
  syntax S ::= "a" [symbol(a)] | "b" [symbol(b)]
  syntax S ::= f(S) [function, symbol(f)]
  rule f(a) => b
  rule [named]: f(b) => a
endmodule
"#;

/// The attribute maps of the main module's sentences, in order, each with or without the keys
/// that record positions or provenance.
fn sentence_attributes(source: &str, without_records: bool) -> Vec<BTreeMap<String, Value>> {
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
    let loaded = load(
        ResolvedSource::new("shift.k", source),
        "SHIFT",
        &mut resolver,
    )
    .unwrap();
    loaded
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .map(|sentence| {
            let mut entries = sentence.attributes().entries();
            if without_records {
                entries.retain(|key, _| {
                    !AttributeKey::from_name(key)
                        .is_some_and(|key| key.is_source_position() || key.is_provenance_only())
                });
            }
            entries
        })
        .collect()
}

#[test]
fn a_blank_line_moves_only_source_position_and_provenance_keys() {
    let shifted = DEFINITION.replacen("  rule f(a)", "\n  rule f(a)", 1);
    assert_ne!(
        sentence_attributes(DEFINITION, false),
        sentence_attributes(&shifted, false),
        "the inserted line moves the positions of the rules after it"
    );
    assert_eq!(
        sentence_attributes(DEFINITION, true),
        sentence_attributes(&shifted, true)
    );
}
