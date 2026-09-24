//! Materialization of descriptor provenance from reparsed authored invocations.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    AnchorPrecision, DescriptorNodeOrigin, DescriptorProvenance, HostDescriptor,
    HostDescriptorPayload, HostGrammarDescriptor, HostProductionOwner, HostProvenance,
    HostSourceAnchor, ItemKind, OriginFrame, OriginStack, ProvenanceKey, RangedOriginKind,
    RustVisibility, SourceRange, StableItemId, TransformationOriginKind,
};
use krs_syntax::{ProvenanceRole, TokenRange};

use super::invocation::{ParsedInvocation, validate_reparsed_payload};
use super::source::{SourceDocument, load_source_document, normalize_display_file};
use super::{PreparedContext, display_item};
use crate::{CollectionError, CollectionErrorKind};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Coordinates {
    start_line: u32,
    start_column: u32,
    end_line: u32,
    end_column: u32,
}

pub(super) fn materialize_descriptor_provenance(
    host: &HostDescriptor,
    payload: &HostDescriptorPayload,
    id: &StableItemId,
    context_index: usize,
    contexts: &[PreparedContext],
    source_cache: &mut BTreeMap<(usize, String), SourceDocument>,
) -> Result<
    (
        DescriptorProvenance,
        RustVisibility,
        Option<krs_ir::ExplicitSymbol>,
    ),
    CollectionError,
> {
    let primary = payload_primary_key(payload, id.item_kind())?;
    let (parsed, origins) = materialize_invocation(
        &host.provenance,
        &primary,
        id.item_name(),
        descriptor_label(id.item_kind()),
        id,
        context_index,
        contexts,
        source_cache,
    )?;
    validate_reparsed_payload(payload, &parsed, id)?;

    let provenance = DescriptorProvenance::new(primary, origins).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::ProvenanceMismatch,
            format!(
                "invalid materialized provenance for `{}`: {error}",
                display_item(id)
            ),
        )
    })?;
    Ok((provenance, parsed.visibility, parsed.explicit_symbol))
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn materialize_invocation(
    provenance: &HostProvenance,
    primary_key: &ProvenanceKey,
    expected_item_name: &str,
    label: &str,
    id: &StableItemId,
    context_index: usize,
    contexts: &[PreparedContext],
    source_cache: &mut BTreeMap<(usize, String), SourceDocument>,
) -> Result<(ParsedInvocation, Vec<DescriptorNodeOrigin>), CollectionError> {
    let display_file = provenance.invocation().display_file();
    let relative = normalize_display_file(display_file)?;
    let cache_key = (context_index, relative.clone());
    if !source_cache.contains_key(&cache_key) {
        let document = load_source_document(&contexts[context_index], &relative)?;
        source_cache.insert(cache_key.clone(), document);
    }
    let invocation_document = source_cache.get(&cache_key).ok_or_else(|| {
        CollectionError::new(
            CollectionErrorKind::HostIo,
            "internal source cache insertion failed",
        )
    })?;
    let invocation_range = source_range(invocation_document, provenance.invocation())?;

    let mut authored_documents = BTreeMap::new();
    for authored in provenance.authored() {
        let authored_relative = normalize_display_file(authored.anchor().display_file())?;
        let authored_cache_key = (context_index, authored_relative.clone());
        if !source_cache.contains_key(&authored_cache_key) {
            let document = load_source_document(&contexts[context_index], &authored_relative)?;
            source_cache.insert(authored_cache_key.clone(), document);
        }
        authored_documents.insert(authored.key().clone(), authored_cache_key);
    }

    let mut materialized = BTreeMap::new();
    for authored in provenance.authored() {
        let authored_cache_key = authored_documents
            .get(authored.key())
            .expect("every authored key has a loaded document");
        let document = source_cache.get(authored_cache_key).ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::HostIo,
                "internal authored source cache insertion failed",
            )
        })?;
        materialized.insert(
            authored.key().clone(),
            source_range(document, authored.anchor())?,
        );
    }
    let primary_host = provenance
        .authored()
        .iter()
        .find(|anchor| anchor.key() == primary_key)
        .ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::ProvenanceMismatch,
                format!(
                    "descriptor `{}` lacks primary provenance key `{}`#{}",
                    display_item(id),
                    primary_key.role(),
                    primary_key.ordinal()
                ),
            )
        })?;
    let primary_coordinates = host_coordinates(primary_host.anchor());
    let primary_cache_key = authored_documents
        .get(primary_key)
        .expect("the primary authored key has a loaded document");
    let primary_document = source_cache.get(primary_cache_key).ok_or_else(|| {
        CollectionError::new(
            CollectionErrorKind::HostIo,
            "internal primary source cache insertion failed",
        )
    })?;
    let primary_candidates = primary_document
        .invocations
        .iter()
        .enumerate()
        .filter(|invocation| {
            let invocation = invocation.1;
            (id.item_kind() == ItemKind::Grammar || invocation.item_name == expected_item_name)
                && &invocation.primary == primary_key
                && invocation.anchors.get(primary_key) == Some(&primary_coordinates)
        })
        .collect::<Vec<_>>();
    let (primary_invocation_index, invocation) = match primary_candidates.as_slice() {
        [] => {
            return Err(CollectionError::new(
                CollectionErrorKind::StaleAnchor,
                format!(
                    "primary anchor for `{}` does not match the reparsed `{}` source",
                    display_item(id),
                    relative
                ),
            ));
        }
        [invocation] => *invocation,
        _ => {
            return Err(CollectionError::new(
                CollectionErrorKind::AmbiguousAnchor,
                format!(
                    "primary anchor for `{}` matches multiple shared-parser invocations",
                    display_item(id)
                ),
            ));
        }
    };
    if id.item_kind() != ItemKind::Grammar && invocation.item_name != expected_item_name {
        return Err(CollectionError::new(
            CollectionErrorKind::StaleAnchor,
            format!(
                "reparsed item name `{}` does not match host identity `{}`",
                invocation.item_name, expected_item_name
            ),
        ));
    }
    let host_keys = provenance
        .authored()
        .iter()
        .map(|anchor| anchor.key().clone())
        .collect::<BTreeSet<_>>();
    let mut parser_keys = BTreeSet::new();
    let mut matched_invocations = BTreeSet::new();
    for authored in provenance.authored() {
        if authored.anchor().precision() != AnchorPrecision::Exact {
            return Err(CollectionError::new(
                CollectionErrorKind::ImpreciseAuthoredAnchor,
                format!(
                    "authored provenance `{}`#{} for `{}` is not leaf-exact",
                    authored.key().role(),
                    authored.key().ordinal(),
                    display_item(id)
                ),
            ));
        }
        let authored_cache_key = authored_documents
            .get(authored.key())
            .expect("every authored key has a loaded document");
        let document = source_cache.get(authored_cache_key).ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::HostIo,
                "internal authored source cache lookup failed",
            )
        })?;
        let coordinates = host_coordinates(authored.anchor());
        let candidate_hits = if authored_cache_key == primary_cache_key
            && invocation.anchors.get(authored.key()) == Some(&coordinates)
        {
            vec![(primary_invocation_index, invocation)]
        } else {
            document
                .invocations
                .iter()
                .enumerate()
                .filter(|(_, candidate)| {
                    candidate.anchors.get(authored.key()) == Some(&coordinates)
                })
                .collect::<Vec<_>>()
        };
        let (invocation_index, parsed_invocation) = match candidate_hits.as_slice() {
            [] => {
                return Err(CollectionError::new(
                    CollectionErrorKind::StaleAnchor,
                    format!(
                        "anchor `{}`#{} for `{}` no longer matches reparsed source",
                        authored.key().role(),
                        authored.key().ordinal(),
                        display_item(id)
                    ),
                ));
            }
            [candidate] => *candidate,
            _ => {
                return Err(CollectionError::new(
                    CollectionErrorKind::AmbiguousAnchor,
                    format!(
                        "anchor `{}`#{} for `{}` matches multiple shared-parser invocations",
                        authored.key().role(),
                        authored.key().ordinal(),
                        display_item(id)
                    ),
                ));
            }
        };
        if matched_invocations.insert((authored_cache_key.clone(), invocation_index)) {
            parser_keys.extend(parsed_invocation.anchors.keys().cloned());
        }
    }
    if host_keys != parser_keys {
        return Err(CollectionError::new(
            CollectionErrorKind::ProvenanceMismatch,
            format!(
                "macro and shared parser disagree about provenance keys for `{}`",
                display_item(id)
            ),
        ));
    }

    let origins = materialized
        .into_iter()
        .map(|(key, range)| {
            let mut origin = OriginStack::authored(range);
            origin.push(OriginFrame::Ranged {
                kind: RangedOriginKind::MacroInvocation,
                range: invocation_range.clone(),
                item: Some(id.clone()),
                label: Some(label.to_owned()),
            });
            origin.push(OriginFrame::Transformation {
                kind: TransformationOriginKind::GeneratedDescriptor,
                item: Some(id.clone()),
                label: Some(format!("{label}.{}#{}", key.role(), key.ordinal())),
            });
            DescriptorNodeOrigin::new(key, origin)
        })
        .collect();
    Ok((invocation.clone(), origins))
}

pub(super) fn token_coordinates(range: TokenRange) -> Result<Coordinates, CollectionError> {
    let start = range.start();
    let end = range.end();
    Ok(Coordinates {
        start_line: u32::try_from(start.line).map_err(|_| coordinate_overflow())?,
        start_column: u32::try_from(start.column + 1).map_err(|_| coordinate_overflow())?,
        end_line: u32::try_from(end.line).map_err(|_| coordinate_overflow())?,
        end_column: u32::try_from(end.column + 1).map_err(|_| coordinate_overflow())?,
    })
}

pub(super) fn coordinate_overflow() -> CollectionError {
    CollectionError::new(
        CollectionErrorKind::SourcePositionOutOfBounds,
        "source coordinate exceeds protocol limits",
    )
}

fn host_coordinates(anchor: &HostSourceAnchor) -> Coordinates {
    Coordinates {
        start_line: anchor.start().line(),
        start_column: anchor.start().scalar_column(),
        end_line: anchor.end().line(),
        end_column: anchor.end().scalar_column(),
    }
}

pub(super) fn source_range(
    document: &SourceDocument,
    anchor: &HostSourceAnchor,
) -> Result<SourceRange, CollectionError> {
    let start = position_to_byte(
        &document.text,
        anchor.start().line(),
        anchor.start().scalar_column(),
    )?;
    let end = position_to_byte(
        &document.text,
        anchor.end().line(),
        anchor.end().scalar_column(),
    )?;
    if start >= end {
        return Err(CollectionError::new(
            CollectionErrorKind::SourcePositionOutOfBounds,
            "materialized source anchor is empty or reversed",
        ));
    }
    SourceRange::new(
        document.file.clone(),
        u32::try_from(start).map_err(|_| coordinate_overflow())?,
        u32::try_from(end).map_err(|_| coordinate_overflow())?,
    )
    .map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::SourcePositionOutOfBounds,
            error.to_string(),
        )
    })
}

pub(super) fn position_to_byte(
    text: &str,
    line: u32,
    scalar_column: u32,
) -> Result<usize, CollectionError> {
    let requested_line = usize::try_from(line).map_err(|_| coordinate_overflow())?;
    let requested_column = usize::try_from(scalar_column).map_err(|_| coordinate_overflow())?;
    let line_start = if requested_line == 1 {
        0
    } else {
        text.match_indices('\n')
            .nth(requested_line - 2)
            .map(|(offset, _)| offset + 1)
            .ok_or_else(|| {
                CollectionError::new(
                    CollectionErrorKind::SourcePositionOutOfBounds,
                    format!("source line {line} is outside the exact file revision"),
                )
            })?
    };
    let line_end = text[line_start..]
        .find('\n')
        .map_or(text.len(), |offset| line_start + offset);
    let line_text = &text[line_start..line_end];
    if requested_column == 0 {
        return Err(CollectionError::new(
            CollectionErrorKind::SourcePositionOutOfBounds,
            "source scalar columns are one-based",
        ));
    }
    if requested_column == 1 {
        return Ok(line_start);
    }
    line_text
        .char_indices()
        .nth(requested_column - 1)
        .map(|(offset, _)| line_start + offset)
        .or_else(|| {
            (requested_column == line_text.chars().count() + 1).then_some(line_end)
        })
        .ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::SourcePositionOutOfBounds,
                format!(
                    "source scalar column {scalar_column} is outside line {line} of the exact file revision"
                ),
            )
        })
}

fn payload_primary_key(
    payload: &HostDescriptorPayload,
    kind: ItemKind,
) -> Result<ProvenanceKey, CollectionError> {
    let role = match payload {
        HostDescriptorPayload::Grammar(grammar) => match grammar.as_ref() {
            HostGrammarDescriptor::Production(production) => match production.owner {
                HostProductionOwner::Constructor { .. } => ProvenanceRole::ConstructorDeclaration,
                HostProductionOwner::TokenSort { .. } => ProvenanceRole::TokenDeclaration,
                HostProductionOwner::BracketSort { .. } => ProvenanceRole::BracketDeclaration,
            },
            HostGrammarDescriptor::Subsort { .. } => ProvenanceRole::SubsortDeclaration,
            HostGrammarDescriptor::Precedence { .. } => ProvenanceRole::PrecedenceDeclaration,
            HostGrammarDescriptor::Associativity { .. } => ProvenanceRole::AssociativityDeclaration,
        },
        HostDescriptorPayload::StructuredRule(_) => ProvenanceRole::RuleDeclaration,
        _ => return primary_key(kind),
    };
    role.key(0).map_err(|error| invalid_provenance_key(&error))
}

fn primary_key(kind: ItemKind) -> Result<ProvenanceKey, CollectionError> {
    let role = match kind {
        ItemKind::Sort => ProvenanceRole::SortDeclaration,
        ItemKind::Constructor => ProvenanceRole::ConstructorSort,
        ItemKind::Configuration | ItemKind::Cell => ProvenanceRole::ConfigurationDeclaration,
        ItemKind::Rule | ItemKind::Equation | ItemKind::Simplification | ItemKind::Alias => {
            ProvenanceRole::RuleDeclaration
        }
        ItemKind::Claim => ProvenanceRole::ClaimDeclaration,
        ItemKind::ContextAlias => ProvenanceRole::ContextAliasDeclaration,
        ItemKind::Grammar => {
            return Err(CollectionError::new(
                CollectionErrorKind::ProvenanceMismatch,
                "grammar primary provenance depends on its typed payload",
            ));
        }
    };
    role.key(0).map_err(|error| invalid_provenance_key(&error))
}

fn invalid_provenance_key(error: &krs_ir::HostProvenanceError) -> CollectionError {
    CollectionError::new(
        CollectionErrorKind::ProvenanceMismatch,
        format!("cannot construct primary provenance key: {error}"),
    )
}

fn descriptor_label(kind: ItemKind) -> &'static str {
    match kind {
        ItemKind::Sort => "sort",
        ItemKind::Constructor => "constructor",
        ItemKind::Configuration => "configuration",
        ItemKind::Cell => "cell",
        ItemKind::Rule => "rule",
        ItemKind::Equation => "equation",
        ItemKind::Simplification => "simplification",
        ItemKind::Alias => "alias",
        ItemKind::ContextAlias => "context alias",
        ItemKind::Claim => "claim",
        ItemKind::Grammar => "grammar",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn configuration_cell_items_use_the_configuration_declaration_lane() {
        assert_eq!(descriptor_label(ItemKind::Cell), "cell");
        assert_eq!(
            primary_key(ItemKind::Cell).unwrap(),
            ProvenanceRole::ConfigurationDeclaration.key(0).unwrap()
        );
    }
}
