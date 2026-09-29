//! Compact, versioned collector pipe representation.

use std::collections::BTreeMap;
use std::io::{self, Write};

use serde::de::{Error as _, IgnoredAny, SeqAccess, Visitor};
use serde::ser::SerializeTuple;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{
    Descriptor, DescriptorBundle, DescriptorDeclaration, DescriptorNodeOrigin, DescriptorPayload,
    DescriptorProvenance, OriginFrame, OriginStack, ProvenanceKey, RangedOriginKind, SchemaVersion,
    SourceFileId, SourceRange, StableItemId, TransformationOriginKind,
};

/// The collector wire version.
/// Its wire bytes are pinned by `crates/krs-ir/tests/golden/collector_*.json`.
/// The schema sample is pinned by `crates/krs-ir/tests/schema/collector-<version>.json`.
/// A shape change must advance this version independently of the canonical descriptor schema.
pub const VERSION: u32 = 40;

#[derive(Serialize)]
struct CollectorRef<'a> {
    protocol_version: u32,
    schema: SchemaVersion,
    files: Vec<SourceFileId>,
    items: Vec<StableItemId>,
    descriptors: Vec<DescriptorRef<'a>>,
    declarations: &'a [DescriptorDeclaration],
}

#[derive(Serialize)]
struct DescriptorRef<'a> {
    id: &'a StableItemId,
    cfg: &'a BTreeMap<String, Option<String>>,
    provenance: ProvenanceRef<'a>,
    payload: &'a DescriptorPayload,
}

struct ProvenanceRef<'a> {
    primary_key: &'a ProvenanceKey,
    origins: Vec<OriginRef<'a>>,
}

impl Serialize for ProvenanceRef<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        #[derive(Serialize)]
        struct Fields<'a> {
            primary_key: &'a ProvenanceKey,
            origins: &'a [OriginRef<'a>],
        }
        let _scope = crate::measure::ProvenanceScope::enter();
        Fields {
            primary_key: self.primary_key,
            origins: &self.origins,
        }
        .serialize(serializer)
    }
}

#[derive(Serialize)]
struct OriginRef<'a> {
    key: &'a ProvenanceKey,
    origin: Vec<FrameRef<'a>>,
}

enum FrameRef<'a> {
    Ranged((u8, usize, u32, u32, Option<usize>, Option<&'a str>)),
    Transformation((u8, Option<usize>, Option<&'a str>)),
}

impl Serialize for FrameRef<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Ranged((kind, file, start, end, item, label)) => {
                let mut tuple = serializer.serialize_tuple(6)?;
                tuple.serialize_element(kind)?;
                tuple.serialize_element(file)?;
                tuple.serialize_element(start)?;
                tuple.serialize_element(end)?;
                tuple.serialize_element(item)?;
                tuple.serialize_element(label)?;
                tuple.end()
            }
            Self::Transformation((kind, item, label)) => {
                let mut tuple = serializer.serialize_tuple(3)?;
                tuple.serialize_element(kind)?;
                tuple.serialize_element(item)?;
                tuple.serialize_element(label)?;
                tuple.end()
            }
        }
    }
}

fn intern<T: Clone + Ord>(
    value: &T,
    table: &mut Vec<T>,
    indexes: &mut BTreeMap<T, usize>,
) -> usize {
    if let Some(index) = indexes.get(value) {
        *index
    } else {
        let index = table.len();
        table.push(value.clone());
        indexes.insert(value.clone(), index);
        index
    }
}

fn encode(bundle: &DescriptorBundle) -> CollectorRef<'_> {
    let mut files = Vec::new();
    let mut items = Vec::new();
    let mut file_indexes = BTreeMap::new();
    let mut item_indexes = BTreeMap::new();
    let mut descriptors = Vec::with_capacity(bundle.descriptors.len());
    for descriptor in &bundle.descriptors {
        let mut origins = Vec::with_capacity(descriptor.provenance.origins().len());
        for node in descriptor.provenance.origins() {
            let mut frames = Vec::with_capacity(node.origin.frames().len());
            for frame in node.origin.frames() {
                let encoded = match frame {
                    OriginFrame::Ranged {
                        kind,
                        range,
                        item,
                        label,
                    } => FrameRef::Ranged((
                        match kind {
                            RangedOriginKind::Authored => 0,
                            RangedOriginKind::MacroInvocation => 1,
                            RangedOriginKind::GeneratedArtifact => 2,
                            RangedOriginKind::FrontendDiagnostic => 3,
                        },
                        intern(&range.file, &mut files, &mut file_indexes),
                        range.start_byte,
                        range.end_byte,
                        item.as_ref()
                            .map(|item| intern(item, &mut items, &mut item_indexes)),
                        label.as_deref(),
                    )),
                    OriginFrame::Transformation { kind, item, label } => {
                        FrameRef::Transformation((
                            match kind {
                                TransformationOriginKind::GeneratedDescriptor => 4,
                                TransformationOriginKind::SemanticIr => 5,
                                TransformationOriginKind::DefinitionIr => 6,
                            },
                            item.as_ref()
                                .map(|item| intern(item, &mut items, &mut item_indexes)),
                            label.as_deref(),
                        ))
                    }
                };
                frames.push(encoded);
            }
            origins.push(OriginRef {
                key: &node.key,
                origin: frames,
            });
        }
        descriptors.push(DescriptorRef {
            id: &descriptor.id,
            cfg: &descriptor.cfg,
            provenance: ProvenanceRef {
                primary_key: descriptor.provenance.primary_key(),
                origins,
            },
            payload: &descriptor.payload,
        });
    }
    CollectorRef {
        protocol_version: VERSION,
        schema: SchemaVersion::CURRENT,
        files,
        items,
        descriptors,
        declarations: &bundle.declarations,
    }
}

/// Writes one canonical bundle in collector format.
pub(crate) fn write(bundle: &DescriptorBundle, writer: impl Write) -> serde_json::Result<()> {
    serde_json::to_writer(writer, &encode(bundle))
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CollectorOwned {
    protocol_version: u32,
    schema: SchemaVersion,
    files: Vec<SourceFileId>,
    items: Vec<StableItemId>,
    descriptors: Vec<DescriptorOwned>,
    declarations: Vec<DescriptorDeclaration>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DescriptorOwned {
    id: StableItemId,
    cfg: BTreeMap<String, Option<String>>,
    provenance: ProvenanceOwned,
    payload: DescriptorPayload,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProvenanceOwned {
    primary_key: ProvenanceKey,
    origins: Vec<OriginOwned>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct OriginOwned {
    key: ProvenanceKey,
    origin: Vec<FrameOwned>,
}

enum FrameOwned {
    Ranged((u8, usize, u32, u32, Option<usize>, Option<String>)),
    Transformation((u8, Option<usize>, Option<String>)),
}

impl<'de> Deserialize<'de> for FrameOwned {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct FrameVisitor;

        impl<'de> Visitor<'de> for FrameVisitor {
            type Value = FrameOwned;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("a collector frame array")
            }

            fn visit_seq<A: SeqAccess<'de>>(
                self,
                mut sequence: A,
            ) -> Result<Self::Value, A::Error> {
                let code: u8 = sequence
                    .next_element()?
                    .ok_or_else(|| A::Error::invalid_length(0, &self))?;
                let frame = match code {
                    0..=3 => {
                        let file = sequence
                            .next_element()?
                            .ok_or_else(|| A::Error::invalid_length(1, &self))?;
                        let start = sequence
                            .next_element()?
                            .ok_or_else(|| A::Error::invalid_length(2, &self))?;
                        let end = sequence
                            .next_element()?
                            .ok_or_else(|| A::Error::invalid_length(3, &self))?;
                        let item = sequence
                            .next_element()?
                            .ok_or_else(|| A::Error::invalid_length(4, &self))?;
                        let label = sequence
                            .next_element()?
                            .ok_or_else(|| A::Error::invalid_length(5, &self))?;
                        Self::Value::Ranged((code, file, start, end, item, label))
                    }
                    4..=6 => {
                        let item = sequence
                            .next_element()?
                            .ok_or_else(|| A::Error::invalid_length(1, &self))?;
                        let label = sequence
                            .next_element()?
                            .ok_or_else(|| A::Error::invalid_length(2, &self))?;
                        Self::Value::Transformation((code, item, label))
                    }
                    _ => {
                        return Err(A::Error::custom(format!(
                            "unknown collector frame code {code}"
                        )));
                    }
                };
                if sequence.next_element::<IgnoredAny>()?.is_some() {
                    return Err(A::Error::custom("collector frame has extra fields"));
                }
                Ok(frame)
            }
        }

        deserializer.deserialize_seq(FrameVisitor)
    }
}

fn invalid(message: impl std::fmt::Display) -> serde_json::Error {
    serde_json::Error::io(io::Error::new(
        io::ErrorKind::InvalidData,
        message.to_string(),
    ))
}

/// Decodes the current collector format, validating each expanded bundle contract.
pub(crate) fn decode(bytes: &[u8]) -> serde_json::Result<DescriptorBundle> {
    let wire: CollectorOwned = crate::json::from_slice(bytes)?;
    if wire.protocol_version != VERSION {
        return Err(invalid(format!(
            "unsupported collector protocol {}; expected {VERSION}",
            wire.protocol_version
        )));
    }
    if wire.schema != SchemaVersion::CURRENT {
        return Err(invalid(format!(
            "unsupported collector schema {}; expected {}",
            wire.schema.0,
            SchemaVersion::CURRENT.0
        )));
    }
    let mut descriptors = Vec::with_capacity(wire.descriptors.len());
    for descriptor in wire.descriptors {
        let mut origins = Vec::with_capacity(descriptor.provenance.origins.len());
        for node in descriptor.provenance.origins {
            let mut frames = Vec::with_capacity(node.origin.len());
            for frame in node.origin {
                let expanded = match frame {
                    FrameOwned::Ranged((kind, file, start, end, item, label)) => {
                        let kind = match kind {
                            0 => RangedOriginKind::Authored,
                            1 => RangedOriginKind::MacroInvocation,
                            2 => RangedOriginKind::GeneratedArtifact,
                            3 => RangedOriginKind::FrontendDiagnostic,
                            _ => return Err(invalid(format!("unknown ranged frame code {kind}"))),
                        };
                        let file = wire
                            .files
                            .get(file)
                            .ok_or_else(|| invalid(format!("invalid file index {file}")))?
                            .clone();
                        let range = SourceRange::new(file, start, end)
                            .map_err(|error| invalid(error.to_string()))?;
                        let item = item
                            .map(|index| {
                                wire.items
                                    .get(index)
                                    .cloned()
                                    .ok_or_else(|| invalid(format!("invalid item index {index}")))
                            })
                            .transpose()?;
                        OriginFrame::Ranged {
                            kind,
                            range,
                            item,
                            label,
                        }
                    }
                    FrameOwned::Transformation((kind, item, label)) => {
                        let kind = match kind {
                            4 => TransformationOriginKind::GeneratedDescriptor,
                            5 => TransformationOriginKind::SemanticIr,
                            6 => TransformationOriginKind::DefinitionIr,
                            _ => {
                                return Err(invalid(format!(
                                    "unknown transformation frame code {kind}"
                                )));
                            }
                        };
                        let item = item
                            .map(|index| {
                                wire.items
                                    .get(index)
                                    .cloned()
                                    .ok_or_else(|| invalid(format!("invalid item index {index}")))
                            })
                            .transpose()?;
                        OriginFrame::Transformation { kind, item, label }
                    }
                };
                frames.push(expanded);
            }
            origins.push(DescriptorNodeOrigin::new(
                node.key,
                OriginStack::try_from_frames(frames).map_err(invalid)?,
            ));
        }
        let provenance = DescriptorProvenance::new(descriptor.provenance.primary_key, origins)
            .map_err(invalid)?;
        descriptors.push(Descriptor {
            id: descriptor.id,
            cfg: descriptor.cfg,
            provenance,
            payload: descriptor.payload,
        });
    }
    for descriptor in &descriptors {
        descriptor.validate_grammar_contract().map_err(invalid)?;
        descriptor.validate_state_contract().map_err(invalid)?;
    }
    DescriptorBundle::with_declarations(descriptors, wire.declarations).map_err(invalid)
}
