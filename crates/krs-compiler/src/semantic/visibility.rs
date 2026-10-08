//! Private productions in proof modules (KF-045).
//!
//! A production whose Rust item is not `pub` is K `private`: only its own
//! module sees it. Claims are emitted into the generated `<MAIN>-SPEC`, which
//! imports the main module, so a claim cannot name a private production of
//! any package; K would reject the claim when it parses it.

use krs_ir::StableItemId;
use krs_ir_levels::SemanticModule;

use super::error::DescriptorLoweringError;
use crate::partition::{is_private, production_display_name};

/// Rejects the first claim, in stable module and rule order, that names a
/// private production.
pub(super) fn check_claim_visibility(
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
    for rule in modules
        .iter()
        .flat_map(SemanticModule::rules)
        .filter(|rule| rule.claim().is_some())
    {
        // The claim's serialized form holds every declaration it names, in
        // terms, conditions, and binders, so the search covers every shape.
        let claim = serde_json::to_value(rule).map_err(json_error)?;
        if let Some(production) = private
            .iter()
            .find(|(id, _)| contains(&claim, id))
            .map(|(_, production)| *production)
        {
            return Err(DescriptorLoweringError::PrivateProductionInSpec {
                production: Box::new(production.clone()),
                claim: Box::new(rule.id().clone()),
                range: rule.origin().origin().exact_authored_range().map(Box::new),
            });
        }
    }
    Ok(())
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
        node: "claim",
        detail: format!("cannot inspect a claim's references: {error}"),
    }
}
