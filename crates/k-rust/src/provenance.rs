//! Stable source identities and provenance shared by the semantic frontend.

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

/// Relocation-stable identity for one logical source and exact contents.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LogicalSourceId {
    pub logical: String,
    pub content_hash: [u8; 32],
}

impl LogicalSourceId {
    pub fn new(logical: impl Into<String>, contents: &[u8]) -> Self {
        Self {
            logical: logical.into(),
            content_hash: Sha256::digest(contents).into(),
        }
    }

    /// Resolve a project-relative logical name inside one concrete checkout.
    pub fn resolve_under(&self, project_root: impl AsRef<Path>) -> PathBuf {
        project_root.as_ref().join(&self.logical)
    }
}

/// Definition-local index into a [`SourceTable`].
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SourceId(pub usize);

/// Interned logical sources referenced by semantic metadata.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SourceTable {
    sources: Vec<LogicalSourceId>,
}

impl SourceTable {
    pub fn intern(&mut self, source: LogicalSourceId) -> SourceId {
        if let Some(index) = self
            .sources
            .iter()
            .position(|candidate| candidate == &source)
        {
            return SourceId(index);
        }
        let id = SourceId(self.sources.len());
        self.sources.push(source);
        id
    }

    pub fn get(&self, id: SourceId) -> Option<&LogicalSourceId> {
        self.sources.get(id.0)
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = &LogicalSourceId> {
        self.sources.iter()
    }

    pub fn is_empty(&self) -> bool {
        self.sources.is_empty()
    }
}
