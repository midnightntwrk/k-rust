//! Private productions in proof modules (KF-045).
//!
//! A production whose Rust item is not `pub` is K `private`: only its own
//! module sees it. Every proof module imports the definition, so none can
//! name a private production of any package: K parses a proof module's
//! sentences with that module's grammar, which leaves imported private
//! syntax out. The proof modules are the generated `<MAIN>-SPEC`, which holds
//! the claims outside every spec module, and the author spec modules
//! (KF-041), whose claims and simplification lemmas are both checked.

use krs_ir::StableItemId;
use krs_ir_levels::{SemanticModule, SemanticRule};

use super::error::DescriptorLoweringError;
use crate::partition::{is_private, production_display_name};

/// Rejects the first proof-module sentence, in stable module and rule order,
/// that names a private production: any claim, and any sentence of an
/// author spec module.
pub(super) fn check_proof_visibility(
    modules: &[SemanticModule],
) -> Result<(), DescriptorLoweringError> {
    let private = modules
        .iter()
        .flat_map(SemanticModule::productions)
        .filter(|production| is_private(production))
        .map(|production| Ok((serde_json::to_value(production.id())?, production.id())))
        .collect::<Result<Vec<_>, serde_json::Error>>()
        .map_err(json_error)?;
    if private.is_empty() {
        return Ok(());
    }
    for (module, rule) in modules.iter().flat_map(|module| {
        module
            .rules()
            .iter()
            .filter(|rule| module.is_spec() || rule.claim().is_some())
            .map(move |rule| (module, rule))
    }) {
        // The sentence's serialized form holds every declaration it names,
        // in terms, conditions, and binders, so the search covers every
        // shape.
        let sentence = serde_json::to_value(rule).map_err(json_error)?;
        if let Some(production) = private
            .iter()
            .find(|(id, _)| contains(&sentence, id))
            .map(|(_, production)| *production)
        {
            return Err(DescriptorLoweringError::PrivateProductionInSpec {
                production: Box::new(production.clone()),
                sentence: Box::new(rule.id().clone()),
                kind: sentence_kind(rule),
                module: module.is_spec().then(|| module.id().as_str().into()),
                range: rule.origin().origin().exact_authored_range().map(Box::new),
            });
        }
    }
    Ok(())
}

/// How the diagnostic's note names the offending sentence.
fn sentence_kind(rule: &SemanticRule) -> &'static str {
    if rule.claim().is_some() {
        "claim"
    } else if rule.simplification().is_some() {
        "simplification lemma"
    } else {
        "rule"
    }
}

/// The message of [`DescriptorLoweringError::PrivateProductionInSpec`].
pub(super) fn private_production_message(production: &StableItemId) -> String {
    format!(
        "`{}` is private to {}; K's private syntax is invisible to proof modules. Make it `pub` and mark it `internal`",
        production_display_name(production),
        production.package().k_namespace()
    )
}

fn contains(value: &serde_json::Value, needle: &serde_json::Value) -> bool {
    value == needle
        || match value {
            serde_json::Value::Array(items) => items.iter().any(|item| contains(item, needle)),
            serde_json::Value::Object(members) => {
                members.values().any(|member| contains(member, needle))
            }
            _ => false,
        }
}

#[expect(
    clippy::needless_pass_by_value,
    reason = "Used as a `map_err` adapter that receives the error by value."
)]
fn json_error(error: serde_json::Error) -> DescriptorLoweringError {
    DescriptorLoweringError::UnsupportedShape {
        node: "proof sentence",
        detail: format!("cannot inspect a proof sentence's references: {error}"),
    }
}
