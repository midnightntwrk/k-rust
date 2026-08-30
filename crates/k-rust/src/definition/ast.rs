//! The flat, serializable K definition model.

use std::collections::BTreeMap;

use serde_json::Value;

use crate::kast::{Label, Sort, Term};
use crate::provenance::{ORIGIN_ATTRIBUTE, SourceId};

pub const LOCATION_ATTRIBUTE: &str = "org.kframework.attributes.Location";
pub const SOURCE_ATTRIBUTE: &str = "org.kframework.attributes.Source";
pub const SOURCE_ID_ATTRIBUTE: &str = "org.kframework.attributes.SourceId";
pub const SENTENCE_START_OFFSET_ATTRIBUTE: &str = "org.krust.provenance.SentenceStartOffset";
pub const SENTENCE_END_OFFSET_ATTRIBUTE: &str = "org.krust.provenance.SentenceEndOffset";

pub(super) fn is_provenance_only_attribute(key: &str) -> bool {
    matches!(
        key,
        ORIGIN_ATTRIBUTE | SENTENCE_START_OFFSET_ATTRIBUTE | SENTENCE_END_OFFSET_ATTRIBUTE
    )
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Location {
    pub start_line: u32,
    pub start_column: u32,
    pub end_line: u32,
    pub end_column: u32,
}

/// Definition attributes as represented by KAST JSON.
///
/// Values remain JSON values because the Java frontend emits a mixture of
/// strings and typed values, and unknown internal attributes must round-trip.
/// Semantic equality ignores the reserved origin receipt while [`Self::entries`]
/// continues to expose it to provenance consumers.
#[derive(Clone, Debug, Default)]
pub struct Attributes {
    entries: BTreeMap<String, Value>,
}

/// One attribute key whose distinct values cannot be represented by the semantic map.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AttributeConflict {
    pub key: String,
    pub values: Vec<Value>,
}

/// Typed loss report paired with the Java-compatible merge result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AttributeMergeError {
    pub merged: Attributes,
    pub conflicts: Vec<AttributeConflict>,
}

impl std::fmt::Display for AttributeMergeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "attribute merge has {} conflicting key(s): {}",
            self.conflicts.len(),
            self.conflicts
                .iter()
                .map(|conflict| conflict.key.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl std::error::Error for AttributeMergeError {}

impl PartialEq for Attributes {
    fn eq(&self, other: &Self) -> bool {
        self.entries
            .iter()
            .filter(|(key, _)| !is_provenance_only_attribute(key))
            .eq(other
                .entries
                .iter()
                .filter(|(key, _)| !is_provenance_only_attribute(key)))
    }
}

impl Eq for Attributes {}

impl Attributes {
    pub fn new(entries: BTreeMap<String, Value>) -> Self {
        Self { entries }
    }

    pub fn entries(&self) -> &BTreeMap<String, Value> {
        &self.entries
    }

    pub fn get(&self, key: &str) -> Option<&Value> {
        self.entries.get(key)
    }

    pub fn get_str(&self, key: &str) -> Option<&str> {
        self.get(key).and_then(Value::as_str)
    }

    pub fn insert(&mut self, key: impl Into<String>, value: Value) -> Option<Value> {
        self.entries.insert(key.into(), value)
    }

    pub fn remove(&mut self, key: &str) -> Option<Value> {
        self.entries.remove(key)
    }

    pub fn is_empty(&self) -> bool {
        self.entries
            .keys()
            .all(|key| is_provenance_only_attribute(key))
    }

    /// Merge attributes using Scala `Att.mergeAttributes` semantics.
    ///
    /// Equal key/value entries survive deduplication. If one key has multiple
    /// distinct values, every value for that key is omitted from the result.
    pub fn merge<'a>(
        attributes: impl IntoIterator<Item = &'a Self>,
    ) -> Result<Self, AttributeMergeError> {
        let mut values = BTreeMap::<String, Vec<Value>>::new();
        for attributes in attributes {
            for (key, value) in attributes.entries() {
                let candidates = values.entry(key.clone()).or_default();
                if !candidates.contains(value) {
                    candidates.push(value.clone());
                }
            }
        }
        let mut merged = BTreeMap::new();
        let mut conflicts = Vec::new();
        for (key, mut values) in values {
            if values.len() == 1 {
                merged.insert(key, values.pop().expect("length was one"));
            } else {
                conflicts.push(AttributeConflict { key, values });
            }
        }
        let merged = Self::new(merged);
        if conflicts.is_empty() {
            Ok(merged)
        } else {
            Err(AttributeMergeError { merged, conflicts })
        }
    }

    pub fn source(&self) -> Option<&str> {
        self.get_str(SOURCE_ATTRIBUTE)
    }

    pub fn source_id(&self) -> Option<SourceId> {
        self.get(SOURCE_ID_ATTRIBUTE)?
            .as_u64()
            .and_then(|value| usize::try_from(value).ok())
            .map(SourceId)
    }

    pub fn location(&self) -> Option<Location> {
        let values = self.get(LOCATION_ATTRIBUTE)?.as_array()?;
        let [start_line, start_column, end_line, end_column] = values.as_slice() else {
            return None;
        };
        Some(Location {
            start_line: u32::try_from(start_line.as_u64()?).ok()?,
            start_column: u32::try_from(start_column.as_u64()?).ok()?,
            end_line: u32::try_from(end_line.as_u64()?).ok()?,
            end_column: u32::try_from(end_column.as_u64()?).ok()?,
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Associativity {
    Left,
    Right,
    NonAssoc,
    Unspecified,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProductionItem {
    NonTerminal {
        sort: Sort,
        name: Option<String>,
    },
    RegexTerminal {
        precede_regex: Option<String>,
        regex: String,
        follow_regex: Option<String>,
    },
    Terminal(String),
}

impl ProductionItem {
    pub fn regex(regex: impl Into<String>) -> Self {
        Self::RegexTerminal {
            precede_regex: None,
            regex: regex.into(),
            follow_regex: None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Sentence {
    SyntaxSort {
        parameters: Vec<Sort>,
        sort: Sort,
        attributes: Attributes,
    },
    SortSynonym {
        new_sort: Sort,
        old_sort: Sort,
        attributes: Attributes,
    },
    SyntaxLexical {
        name: String,
        regex: String,
        attributes: Attributes,
    },
    Production {
        label: Option<Label>,
        parameters: Vec<Sort>,
        sort: Sort,
        items: Vec<ProductionItem>,
        attributes: Attributes,
    },
    SyntaxAssociativity {
        associativity: Associativity,
        tags: Vec<String>,
        attributes: Attributes,
    },
    SyntaxPriority {
        priorities: Vec<Vec<String>>,
        attributes: Attributes,
    },
    ContextAlias {
        body: Term,
        requires: Term,
        attributes: Attributes,
    },
    Context {
        body: Term,
        requires: Term,
        attributes: Attributes,
    },
    Rule {
        body: Term,
        requires: Term,
        ensures: Term,
        attributes: Attributes,
    },
    Claim {
        body: Term,
        requires: Term,
        ensures: Term,
        attributes: Attributes,
    },
    Configuration {
        body: Term,
        ensures: Term,
        attributes: Attributes,
    },
    Bubble {
        sentence_type: String,
        contents: String,
        attributes: Attributes,
    },
}

impl Sentence {
    pub fn attributes(&self) -> &Attributes {
        match self {
            Self::SyntaxSort { attributes, .. }
            | Self::SortSynonym { attributes, .. }
            | Self::SyntaxLexical { attributes, .. }
            | Self::Production { attributes, .. }
            | Self::SyntaxAssociativity { attributes, .. }
            | Self::SyntaxPriority { attributes, .. }
            | Self::ContextAlias { attributes, .. }
            | Self::Context { attributes, .. }
            | Self::Rule { attributes, .. }
            | Self::Claim { attributes, .. }
            | Self::Configuration { attributes, .. }
            | Self::Bubble { attributes, .. } => attributes,
        }
    }

    pub fn attributes_mut(&mut self) -> &mut Attributes {
        match self {
            Self::SyntaxSort { attributes, .. }
            | Self::SortSynonym { attributes, .. }
            | Self::SyntaxLexical { attributes, .. }
            | Self::Production { attributes, .. }
            | Self::SyntaxAssociativity { attributes, .. }
            | Self::SyntaxPriority { attributes, .. }
            | Self::ContextAlias { attributes, .. }
            | Self::Context { attributes, .. }
            | Self::Rule { attributes, .. }
            | Self::Claim { attributes, .. }
            | Self::Configuration { attributes, .. }
            | Self::Bubble { attributes, .. } => attributes,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FlatImport {
    pub name: String,
    pub public: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FlatModule {
    pub name: String,
    pub imports: Vec<FlatImport>,
    pub local_sentences: Vec<Sentence>,
    pub attributes: Attributes,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Definition {
    pub main_module: String,
    pub modules: Vec<FlatModule>,
    pub attributes: Attributes,
}

impl Definition {
    pub fn main_module(&self) -> Option<&FlatModule> {
        self.modules
            .iter()
            .find(|module| module.name == self.main_module)
    }
}
