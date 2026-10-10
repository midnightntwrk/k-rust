//! The compiled stage: what [`crate::Semantics`] takes from the native frontend, in a form a caller can cache.
//!
//! Compiling Definition IR through k-rust is the slow part of loading a definition; everything after it (loading the KORE into the backend, building the program grammar and the printer) is cheap.
//! A [`CompiledStage`] holds exactly the frontend's outputs that [`crate::Semantics::from_stage`] reads, and [`CompiledStage::encode`] writes them as bytes that [`CompiledStage::decode`] reads back.
//! The crate stays filesystem-free: where the bytes live, and what key they are stored under, is the caller's business (`krs` keys them by the Definition IR digest).

use std::collections::BTreeMap;

use k_rust::definition::json as definition_json;
use k_rust::kast::Sort as KastSort;
use k_rust::provenance::SourceTable;
use krs_ir::measure::Timings;
use krs_ir_levels::DefinitionIr;
use krs_k_rust::{CompiledArtifacts, NativeDefinition, SentenceProvenance};
use serde::{Deserialize, Serialize};

use crate::{ExecError, compile_definition};

/// The format name of [`CompiledStage::encode`]'s bytes; a change to the encoding or to what the stage holds changes it.
pub const STAGE_FORMAT: &str = "krs-exec-stage/1";

/// The native frontend's outputs for one Definition IR, from which [`crate::Semantics::from_stage`] builds a [`crate::Semantics`].
#[derive(Clone, Debug)]
pub struct CompiledStage {
    pub(crate) definition_kore: String,
    pub(crate) syntax_definition_kore: String,
    pub(crate) macros_kore: String,
    pub(crate) provenance: SentenceProvenance,
    pub(crate) frontend_definition: NativeDefinition,
    /// Only for encoding: the frontend definition's origin receipts index it.
    pub(crate) source_table: SourceTable,
    pub(crate) configuration_variables: BTreeMap<String, KastSort>,
}

impl CompiledStage {
    /// Compile Definition IR through the native frontend in the symbolic dialect, recording `native.*` spans.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Compile`] when the native frontend rejects the definition.
    pub fn compile(definition: &DefinitionIr, timings: &mut Timings) -> Result<Self, ExecError> {
        let (artifacts, context) =
            compile_definition(definition, timings).map_err(ExecError::Compile)?;
        let CompiledArtifacts {
            definition_kore,
            syntax_definition_kore,
            macros_kore,
            sentence_provenance,
            ..
        } = artifacts;
        Ok(Self {
            definition_kore,
            syntax_definition_kore,
            macros_kore,
            provenance: sentence_provenance,
            frontend_definition: context.frontend_definition,
            source_table: context.source_table,
            configuration_variables: context.configuration_variables,
        })
    }

    /// The compiled KORE definition text.
    #[must_use]
    pub fn definition_kore(&self) -> &str {
        &self.definition_kore
    }

    /// Encode the stage as [`STAGE_FORMAT`] bytes.
    ///
    /// The prepared frontend definition is written in k-rust's `KRUST-PROVENANCE` JSON, which keeps its origin receipts and term metadata.
    /// Returns `None` when the stage has no faithful encoding: the encoding is kept only when decoding it gives back an equal stage.
    /// A caller that gets `None` simply does not cache the stage.
    #[must_use]
    pub fn encode(&self) -> Option<Vec<u8>> {
        let frontend =
            definition_json::to_provenance_string(&self.frontend_definition, &self.source_table)
                .ok()?;
        let header = Header {
            format: STAGE_FORMAT.to_owned(),
            sections: [
                self.definition_kore.len(),
                self.syntax_definition_kore.len(),
                self.macros_kore.len(),
                frontend.len(),
            ],
            provenance: self.provenance.clone(),
            configuration_variables: self
                .configuration_variables
                .iter()
                .map(|(name, sort)| (name.clone(), WireSort::from(sort)))
                .collect(),
        };
        let header = serde_json::to_vec(&header).ok()?;
        let mut bytes = Vec::with_capacity(
            8 + header.len()
                + self.definition_kore.len()
                + self.syntax_definition_kore.len()
                + self.macros_kore.len()
                + frontend.len(),
        );
        bytes.extend_from_slice(&(header.len() as u64).to_le_bytes());
        bytes.extend_from_slice(&header);
        for section in [
            &self.definition_kore,
            &self.syntax_definition_kore,
            &self.macros_kore,
            &frontend,
        ] {
            bytes.extend_from_slice(section.as_bytes());
        }
        Self::decode(&bytes)
            .is_some_and(|decoded| decoded.same_outputs(self))
            .then_some(bytes)
    }

    /// Whether `other` holds the same frontend outputs; the source table is an encoding aid whose internal layout a round trip need not keep.
    fn same_outputs(&self, other: &Self) -> bool {
        self.definition_kore == other.definition_kore
            && self.syntax_definition_kore == other.syntax_definition_kore
            && self.macros_kore == other.macros_kore
            && self.provenance == other.provenance
            && self.frontend_definition == other.frontend_definition
            && self.configuration_variables == other.configuration_variables
    }

    /// Decode [`STAGE_FORMAT`] bytes written by [`Self::encode`].
    ///
    /// Returns `None` for anything else: another format, a truncated or malformed document, or a frontend definition k-rust cannot read.
    #[must_use]
    pub fn decode(bytes: &[u8]) -> Option<Self> {
        let length = usize::try_from(u64::from_le_bytes(bytes.get(..8)?.try_into().ok()?)).ok()?;
        let body_start = 8usize.checked_add(length)?;
        let header: Header = serde_json::from_slice(bytes.get(8..body_start)?).ok()?;
        if header.format != STAGE_FORMAT {
            return None;
        }
        let mut rest = bytes.get(body_start..)?;
        let mut sections = Vec::with_capacity(header.sections.len());
        for length in header.sections {
            let section = rest.get(..length)?;
            sections.push(std::str::from_utf8(section).ok()?.to_owned());
            rest = &rest[length..];
        }
        if !rest.is_empty() {
            return None;
        }
        let [
            definition_kore,
            syntax_definition_kore,
            macros_kore,
            frontend,
        ] = <[String; 4]>::try_from(sections).ok()?;
        let frontend = definition_json::from_provenance_str(&frontend).ok()?;
        Some(Self {
            definition_kore,
            syntax_definition_kore,
            macros_kore,
            provenance: header.provenance,
            frontend_definition: frontend.definition,
            source_table: frontend.source_table,
            configuration_variables: header
                .configuration_variables
                .into_iter()
                .map(|(name, sort)| (name, KastSort::from(sort)))
                .collect(),
        })
    }
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    format: String,
    /// Byte lengths of `definition.kore`, `syntaxDefinition.kore`, `macros.kore`, and the frontend definition's KAST JSON, which follow the header in that order.
    sections: [usize; 4],
    provenance: SentenceProvenance,
    configuration_variables: BTreeMap<String, WireSort>,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct WireSort {
    name: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    parameters: Vec<WireSort>,
}

impl From<&KastSort> for WireSort {
    fn from(sort: &KastSort) -> Self {
        Self {
            name: sort.name.clone(),
            parameters: sort.parameters.iter().map(Self::from).collect(),
        }
    }
}

impl From<WireSort> for KastSort {
    fn from(sort: WireSort) -> Self {
        Self::with_parameters(
            sort.name,
            sort.parameters.into_iter().map(Self::from).collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::definition::{Attributes, FlatModule};

    fn stage() -> CompiledStage {
        CompiledStage {
            definition_kore: "[] module MAIN endmodule []".to_owned(),
            syntax_definition_kore: "[] module MAIN-SYNTAX endmodule []".to_owned(),
            macros_kore: String::new(),
            provenance: SentenceProvenance::default(),
            frontend_definition: NativeDefinition {
                main_module: "MAIN".to_owned(),
                modules: vec![FlatModule {
                    name: "MAIN".to_owned(),
                    imports: Vec::new(),
                    local_sentences: Vec::new(),
                    attributes: Attributes::default(),
                }],
                attributes: Attributes::default(),
            },
            source_table: SourceTable::default(),
            configuration_variables: BTreeMap::from([
                ("PGM".to_owned(), KastSort::new("Pgm")),
                (
                    "ENV".to_owned(),
                    KastSort::with_parameters(
                        "Map",
                        vec![KastSort::new("Id"), KastSort::new("Int")],
                    ),
                ),
            ]),
        }
    }

    #[test]
    fn a_stage_round_trips_through_its_encoding() {
        let stage = stage();
        let bytes = stage.encode().expect("the stage has a faithful encoding");
        let decoded = CompiledStage::decode(&bytes).expect("its own encoding decodes");
        assert!(decoded.same_outputs(&stage));
        assert_eq!(decoded.encode(), Some(bytes));
    }

    #[test]
    fn anything_but_a_whole_stage_of_this_format_is_refused() {
        let bytes = stage().encode().unwrap();
        assert!(CompiledStage::decode(&bytes[..bytes.len() - 1]).is_none());
        let mut longer = bytes.clone();
        longer.push(b' ');
        assert!(CompiledStage::decode(&longer).is_none());
        assert!(CompiledStage::decode(&bytes[..4]).is_none());
        let text = String::from_utf8_lossy(&bytes).into_owned();
        let other_format = text.replacen(STAGE_FORMAT, "krs-exec-stage/0", 1);
        assert_ne!(other_format, text);
        assert!(CompiledStage::decode(other_format.as_bytes()).is_none());
    }
}
