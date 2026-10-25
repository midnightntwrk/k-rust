use krs_ir::{
    Descriptor, DescriptorCellIdentity, NodeOrigin, OriginFrame, ProvenanceKey, SemanticId,
    SourceMapKey, StableItemId, StableText, TransformationOriginKind, lower_hex,
};
use krs_syntax::ProvenanceRole;
use sha2::{Digest, Sha256};

use super::error::DescriptorLoweringError;

pub(super) fn generated_semantic_id(
    family: &str,
    owner: &StableItemId,
    field: Option<&str>,
) -> Result<SemanticId, DescriptorLoweringError> {
    let mut seed = stable_item_text(owner);
    if let Some(field) = field {
        seed.push('\0');
        seed.push_str(field);
    }
    let digest = Sha256::digest(seed.as_bytes());
    Ok(SemanticId::new(format!(
        "{family}.{}.{}",
        owner.item_name(),
        lower_hex(&digest[..8])
    ))?)
}

pub(super) fn semantic_cell_id(
    identity: &DescriptorCellIdentity,
) -> Result<SemanticId, DescriptorLoweringError> {
    generated_semantic_id("cell", &identity.owner, Some(&identity.field))
}

#[expect(
    clippy::needless_pass_by_value,
    reason = "Accepts owned provenance keys constructed by semantic lowering callers."
)]
pub(super) fn semantic_origin(
    descriptor: &Descriptor,
    key: ProvenanceKey,
    role: &str,
) -> Result<NodeOrigin, DescriptorLoweringError> {
    let origin = descriptor.provenance().origin_for(&key).ok_or_else(|| {
        DescriptorLoweringError::ParserReferenceDisagreement {
            id: Box::new(descriptor.id().clone()),
            detail: format!(
                "missing parser origin `{}#{}` for semantic {role}",
                key.role().as_str(),
                key.ordinal()
            ),
            range: None,
        }
    })?;
    semantic_origin_from_stack(descriptor, origin, role, Some(&key))
}

/// The exact authored range of the node `key` names in `descriptor`, if it has one.
pub(super) fn key_range(
    descriptor: &Descriptor,
    key: &ProvenanceKey,
) -> Option<krs_ir::SourceRange> {
    descriptor
        .provenance()
        .origin_for(key)
        .and_then(krs_ir::OriginStack::exact_authored_range)
}

/// The exact authored range of a descriptor's item, the last fallback of an error's location.
pub(super) fn item_range(descriptor: &Descriptor) -> Option<krs_ir::SourceRange> {
    descriptor
        .provenance()
        .primary_origin()
        .exact_authored_range()
}

pub(super) fn semantic_origin_from_primary(
    descriptor: &Descriptor,
    role: &str,
) -> Result<NodeOrigin, DescriptorLoweringError> {
    semantic_origin_from_stack(
        descriptor,
        descriptor.provenance().primary_origin(),
        role,
        Some(descriptor.provenance().primary_key()),
    )
}

fn semantic_origin_from_stack(
    descriptor: &Descriptor,
    origin: &krs_ir::OriginStack,
    role: &str,
    key: Option<&ProvenanceKey>,
) -> Result<NodeOrigin, DescriptorLoweringError> {
    let mut seed = stable_item_text(descriptor.id());
    seed.push('\0');
    seed.push_str(role);
    if let Some(key) = key {
        seed.push('\0');
        seed.push_str(key.role().as_str());
        seed.push('\0');
        seed.push_str(&key.ordinal().to_string());
    }
    let digest = Sha256::digest(seed.as_bytes());
    let source_key = SourceMapKey::new(format!("sem.{role}.{}", lower_hex(&digest[..12])))?;
    let mut origin = origin.clone();
    origin.push(OriginFrame::Transformation {
        kind: TransformationOriginKind::SemanticIr,
        item: Some(descriptor.id().clone()),
        label: Some(role.to_owned()),
    });
    Ok(NodeOrigin::new(source_key, origin))
}

pub(super) fn role_key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    role.key(ordinal)
}

fn stable_item_text(id: &StableItemId) -> String {
    let mut text = String::new();
    push_component(&mut text, id.package().k_namespace());
    push_component(&mut text, id.package().cargo_name());
    push_component(&mut text, id.package().cargo_version());
    push_component(&mut text, id.package().cargo_source());
    for component in id.module_path() {
        push_component(&mut text, component);
    }
    push_component(&mut text, id.item_name());
    push_component(&mut text, &id.item_kind().stable_text());
    push_component(&mut text, id.disambiguator());
    text
}

fn push_component(output: &mut String, value: &str) {
    output.push_str(&value.len().to_string());
    output.push(':');
    output.push_str(value);
}
