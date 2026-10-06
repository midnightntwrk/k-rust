//! Exact k-rust provenance artifacts at the loaded stage.
//!
//! Round-trip equality and a canonical fixed point are k-rust properties measured
//! over 35/35 definitions at revision 927b9ce6. Load diagnostics are not part of
//! this artifact (SI-T03); reading supplies no files or diagnostics.

use crate::{Baseline, Sha256Digest, sha256};
use k_rust::{
    definition::{Definition, json},
    outer::{LoadedDefinition, LoadedParts},
    provenance::SourceTable,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticInput {
    text: String,
    digest: Sha256Digest,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SemanticInputError {
    Encode(String),
    Decode(String),
    NonCanonical,
    Relink(String),
}

impl std::fmt::Display for SemanticInputError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for SemanticInputError {}

impl SemanticInput {
    pub fn text(&self) -> &str {
        &self.text
    }
    pub const fn digest(&self) -> Sha256Digest {
        self.digest
    }

    pub fn of(baseline: &Baseline) -> Result<Self, SemanticInputError> {
        Self::of_definition(baseline.definition(), baseline.loaded().source_table())
    }

    pub fn of_definition(
        definition: &Definition,
        source_table: &SourceTable,
    ) -> Result<Self, SemanticInputError> {
        let text = json::to_provenance_string(definition, source_table)
            .map_err(|e| SemanticInputError::Encode(e.to_string()))?;
        Ok(Self {
            digest: sha256(text.as_bytes()),
            text,
        })
    }

    pub fn read(text: &str) -> Result<(Self, Baseline), SemanticInputError> {
        let parts = json::from_provenance_str(text)
            .map_err(|e| SemanticInputError::Decode(e.to_string()))?;
        let input = Self::of_definition(&parts.definition, &parts.source_table)?;
        if input.text != text {
            return Err(SemanticInputError::NonCanonical);
        }
        let loaded = LoadedDefinition::from_loaded_parts(LoadedParts {
            files: Vec::new(),
            source_table: parts.source_table,
            definition: parts.definition,
            diagnostics: Vec::new(),
        })
        .map_err(|e| SemanticInputError::Relink(e.to_string()))?;
        Ok((input, Baseline::new(loaded)))
    }
}
