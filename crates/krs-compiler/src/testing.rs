//! Contract assertions for semantic lowering and canonical K emission.

use krs_ir::testing::assert_canonical_contract;
use krs_ir::{OriginFrame, RangedOriginKind, SemanticTheory, TransformationOriginKind};

use crate::{EmittedK, LoweredDefinition, SourceMap, emit_k, lower_semantic_theory};

/// Asserts canonical IR, deterministic lowering and emission, and complete provenance frames.
///
/// Returns the first lowered definition and emission for fixture-specific assertions.
/// The semantic theory must be valid for both lowering and emission.
///
/// # Panics
///
/// Panics if the theory is not canonical, lowering or emission fails, their results differ
/// between runs, or a source-map entry lacks the required provenance frames.
#[must_use]
pub fn assert_lowering_contract(theory: &SemanticTheory) -> (LoweredDefinition, EmittedK) {
    assert_canonical_contract(theory);

    let lowered = lower_semantic_theory(theory).expect("semantic theory must lower");
    let repeated = lower_semantic_theory(theory).expect("semantic theory must lower again");
    assert_eq!(
        lowered.definition().to_canonical_json().unwrap(),
        repeated.definition().to_canonical_json().unwrap(),
        "DefinitionIr changed between lowering runs"
    );
    assert_eq!(
        lowered.source_map().to_canonical_json().unwrap(),
        repeated.source_map().to_canonical_json().unwrap(),
        "source map changed between lowering runs"
    );
    assert_eq!(
        lowered.symbol_map().to_canonical_json().unwrap(),
        repeated.symbol_map().to_canonical_json().unwrap(),
        "symbol map changed between lowering runs"
    );
    assert_canonical_contract(lowered.definition());
    assert_origin_frames(lowered.source_map(), "lowered");

    let emitted = emit_k(&lowered).expect("lowered definition must emit");
    let reemitted = emit_k(&lowered).expect("lowered definition must emit again");
    assert_eq!(
        emitted.source(),
        reemitted.source(),
        "K source changed between emissions"
    );
    assert_eq!(
        emitted.spec(),
        reemitted.spec(),
        "K specification changed between emissions"
    );
    assert_eq!(
        emitted.source_map().to_canonical_json().unwrap(),
        reemitted.source_map().to_canonical_json().unwrap(),
        "emitted source map changed between emissions"
    );
    assert_eq!(
        emitted.symbol_map().to_canonical_json().unwrap(),
        reemitted.symbol_map().to_canonical_json().unwrap(),
        "emitted symbol map changed between emissions"
    );
    assert_origin_frames(emitted.source_map(), "emitted");

    (lowered, emitted)
}

fn assert_origin_frames(map: &SourceMap, phase: &str) {
    for entry in map.entries() {
        assert!(
            matches!(
                entry.origin().frames().first(),
                Some(OriginFrame::Ranged {
                    kind: RangedOriginKind::Authored,
                    ..
                })
            ),
            "{phase} source-map entry {} must start with an authored frame",
            entry.key()
        );
        assert!(
            matches!(
                entry.origin().frames().last(),
                Some(OriginFrame::Transformation {
                    kind: TransformationOriginKind::DefinitionIr,
                    ..
                })
            ),
            "{phase} source-map entry {} must end with a DefinitionIr frame",
            entry.key()
        );
    }
}
