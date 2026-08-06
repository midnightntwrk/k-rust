//! The flat, serializable K definition model.

use std::collections::BTreeMap;

use serde_json::Value;

use crate::kast::{Label, Sort, Term};

pub const LOCATION_ATTRIBUTE: &str = "org.kframework.attributes.Location";
pub const SOURCE_ATTRIBUTE: &str = "org.kframework.attributes.Source";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Attributes {
    entries: BTreeMap<String, Value>,
}

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

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Merge attributes using Scala `Att.mergeAttributes` semantics.
    ///
    /// Equal key/value entries survive deduplication. If one key has multiple
    /// distinct values, every value for that key is omitted from the result.
    pub fn merge<'a>(attributes: impl IntoIterator<Item = &'a Self>) -> Self {
        let mut values = BTreeMap::<String, Vec<Value>>::new();
        for attributes in attributes {
            for (key, value) in attributes.entries() {
                let candidates = values.entry(key.clone()).or_default();
                if !candidates.contains(value) {
                    candidates.push(value.clone());
                }
            }
        }
        Self::new(
            values
                .into_iter()
                .filter_map(|(key, mut values)| {
                    (values.len() == 1).then(|| (key, values.pop().expect("length was one")))
                })
                .collect(),
        )
    }

    pub fn source(&self) -> Option<&str> {
        self.get_str(SOURCE_ATTRIBUTE)
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
