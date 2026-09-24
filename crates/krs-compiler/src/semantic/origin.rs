use krs_ir::{
    Descriptor, DescriptorCellIdentity, NodeOrigin, OriginFrame, ProvenanceKey, SemanticId,
    SourceMapKey, StableItemId, TransformationOriginKind,
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
        hex_encode(&digest[..8])
    ))?)
}

pub(super) fn semantic_cell_id(
    identity: &DescriptorCellIdentity,
) -> Result<SemanticId, DescriptorLoweringError> {
    generated_semantic_id("cell", &identity.owner, Some(&identity.field))
}

#[allow(clippy::needless_pass_by_value)]
pub(super) fn semantic_origin(
    descriptor: &Descriptor,
    key: ProvenanceKey,
    role: &str,
) -> Result<NodeOrigin, DescriptorLoweringError> {
    let origin = descriptor.provenance.origin_for(&key).ok_or_else(|| {
        DescriptorLoweringError::ParserReferenceDisagreement {
            id: Box::new(descriptor.id.clone()),
            detail: format!(
                "missing parser origin `{}#{}` for semantic {role}",
                key.role(),
                key.ordinal()
            ),
        }
    })?;
    semantic_origin_from_stack(descriptor, origin, role, Some(&key))
}

pub(super) fn semantic_origin_from_primary(
    descriptor: &Descriptor,
    role: &str,
) -> Result<NodeOrigin, DescriptorLoweringError> {
    semantic_origin_from_stack(
        descriptor,
        descriptor.provenance.primary_origin(),
        role,
        Some(descriptor.provenance.primary_key()),
    )
}

fn semantic_origin_from_stack(
    descriptor: &Descriptor,
    origin: &krs_ir::OriginStack,
    role: &str,
    key: Option<&ProvenanceKey>,
) -> Result<NodeOrigin, DescriptorLoweringError> {
    let mut seed = stable_item_text(&descriptor.id);
    seed.push('\0');
    seed.push_str(role);
    if let Some(key) = key {
        seed.push('\0');
        seed.push_str(key.role());
        seed.push('\0');
        seed.push_str(&key.ordinal().to_string());
    }
    let digest = Sha256::digest(seed.as_bytes());
    let source_key = SourceMapKey::new(format!("sem.{role}.{}", hex_encode(&digest[..12])))?;
    let mut origin = origin.clone();
    origin.push(OriginFrame::Transformation {
        kind: TransformationOriginKind::SemanticIr,
        item: Some(descriptor.id.clone()),
        label: Some(role.to_owned()),
    });
    Ok(NodeOrigin::new(source_key, origin))
}

pub(super) fn role_key(
    role: ProvenanceRole,
    ordinal: u32,
) -> Result<ProvenanceKey, DescriptorLoweringError> {
    role.key(ordinal).map_err(|error| {
        DescriptorLoweringError::InvalidGeneratedIdentity(format!(
            "cannot generate parser provenance key: {error}"
        ))
    })
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
    push_component(&mut text, &format!("{:?}", id.item_kind()));
    push_component(&mut text, id.disambiguator());
    text
}

fn push_component(output: &mut String, value: &str) {
    output.push_str(&value.len().to_string());
    output.push(':');
    output.push_str(value);
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}
