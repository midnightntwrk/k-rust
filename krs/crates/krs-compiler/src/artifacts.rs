//! Names and ownership contract for emitted source artifacts.

/// The executable K source artifact.
pub const DEFINITION_ARTIFACT: &str = "definition.k";
/// The claims-only K source artifact.
pub const SPEC_ARTIFACT: &str = "spec.k";
/// The versioned descriptor bundle artifact.
pub const DESCRIPTOR_ARTIFACT: &str = "descriptor-bundle.json";
/// The versioned semantic theory artifact.
pub const SEMANTIC_ARTIFACT: &str = "semantic-ir.json";
/// The versioned Definition IR artifact.
pub const DEFINITION_IR_ARTIFACT: &str = "definition-ir.json";
/// The compiler symbol sidecar artifact.
pub const SYMBOLS_ARTIFACT: &str = "symbols.json";
/// The compiler source sidecar artifact.
pub const SOURCES_ARTIFACT: &str = "sources.json";
/// The directory ownership marker filename.
pub const ARTIFACT_MARKER_FILE: &str = ".krs-artifacts";
/// Exact contents required for a directory to be owned by KRS.
pub const ARTIFACT_MARKER: &str = "KRS artifact directory schema 1; safe to update.\n";

/// The artifacts `emit-k` writes only on request (`--ir`): KRS's three internal levels, in lexical
/// order. The default set is the K and the two maps that carry it back to the authored source.
pub const IR_ARTIFACTS: [&str; 3] = [
    DEFINITION_IR_ARTIFACT,
    DESCRIPTOR_ARTIFACT,
    SEMANTIC_ARTIFACT,
];

/// Returns the exact artifact filenames of an `emit-k` output directory in lexical order.
/// `has_claims` controls whether the claims-only source must be emitted, and `ir` whether the
/// directory holds [`IR_ARTIFACTS`] (`emit-k --ir`).
#[must_use]
pub fn emitted_artifact_names(has_claims: bool, ir: bool) -> Vec<&'static str> {
    let mut names = vec![
        ARTIFACT_MARKER_FILE,
        DEFINITION_ARTIFACT,
        SOURCES_ARTIFACT,
        SYMBOLS_ARTIFACT,
    ];
    if ir {
        names.extend(IR_ARTIFACTS);
    }
    if has_claims {
        names.push(SPEC_ARTIFACT);
    }
    names.sort_unstable();
    names
}
