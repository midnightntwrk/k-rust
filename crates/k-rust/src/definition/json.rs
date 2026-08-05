//! KAST JSON version 4 serialization for flat K definitions.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::ast::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, ProductionItem, Sentence,
};
use crate::kast::json::{self as term_json, JsonLabel, JsonSort, JsonTerm};

#[derive(Debug)]
pub enum Error {
    Json(serde_json::Error),
    Term(term_json::Error),
    UnsupportedFormat(String),
    UnsupportedVersion(u32),
    UnsupportedSentence(&'static str),
    MissingMainModule(String),
    DuplicateMainModule(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Json(error) => error.fmt(formatter),
            Self::Term(error) => error.fmt(formatter),
            Self::UnsupportedFormat(format) => {
                write!(formatter, "unsupported KAST format {format:?}")
            }
            Self::UnsupportedVersion(version) => {
                write!(formatter, "unsupported KAST version {version}")
            }
            Self::UnsupportedSentence(node) => {
                write!(
                    formatter,
                    "{node} is not representable in KAST JSON version 4"
                )
            }
            Self::MissingMainModule(name) => {
                write!(formatter, "main module {name:?} was not found")
            }
            Self::DuplicateMainModule(name) => {
                write!(formatter, "main module {name:?} is not unique")
            }
        }
    }
}

impl std::error::Error for Error {}

impl From<serde_json::Error> for Error {
    fn from(error: serde_json::Error) -> Self {
        Self::Json(error)
    }
}

impl From<term_json::Error> for Error {
    fn from(error: term_json::Error) -> Self {
        Self::Term(error)
    }
}

#[derive(Serialize, Deserialize)]
struct Envelope {
    format: String,
    version: u32,
    term: JsonDefinition,
}

pub fn from_str(input: &str) -> Result<Definition, Error> {
    let envelope: Envelope = serde_json::from_str(input)?;
    if envelope.format != term_json::FORMAT {
        return Err(Error::UnsupportedFormat(envelope.format));
    }
    if envelope.version != term_json::VERSION {
        return Err(Error::UnsupportedVersion(envelope.version));
    }

    let definition: Definition = envelope.term.try_into()?;
    let main_module_count = definition
        .modules
        .iter()
        .filter(|module| module.name == definition.main_module)
        .count();
    match main_module_count {
        0 => Err(Error::MissingMainModule(definition.main_module)),
        1 => Ok(definition),
        _ => Err(Error::DuplicateMainModule(definition.main_module)),
    }
}

pub fn to_string(definition: &Definition) -> Result<String, Error> {
    serialize(definition, serde_json::to_string)
}

pub fn to_string_pretty(definition: &Definition) -> Result<String, Error> {
    serialize(definition, serde_json::to_string_pretty)
}

fn serialize(
    definition: &Definition,
    serializer: impl FnOnce(&Envelope) -> Result<String, serde_json::Error>,
) -> Result<String, Error> {
    serializer(&Envelope {
        format: term_json::FORMAT.into(),
        version: term_json::VERSION,
        term: definition.try_into()?,
    })
    .map_err(Into::into)
}

#[derive(Clone, Serialize, Deserialize)]
struct JsonAttributes {
    node: AttributeNode,
    att: BTreeMap<String, Value>,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum AttributeNode {
    KAtt,
}

impl From<&Attributes> for JsonAttributes {
    fn from(attributes: &Attributes) -> Self {
        Self {
            node: AttributeNode::KAtt,
            att: attributes.entries().clone(),
        }
    }
}

impl From<JsonAttributes> for Attributes {
    fn from(attributes: JsonAttributes) -> Self {
        Self::new(attributes.att)
    }
}

#[derive(Serialize, Deserialize)]
struct JsonDefinition {
    node: DefinitionNode,
    #[serde(rename = "mainModule")]
    main_module: String,
    modules: Vec<JsonFlatModule>,
    att: JsonAttributes,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum DefinitionNode {
    KDefinition,
}

impl TryFrom<&Definition> for JsonDefinition {
    type Error = Error;

    fn try_from(definition: &Definition) -> Result<Self, Self::Error> {
        Ok(Self {
            node: DefinitionNode::KDefinition,
            main_module: definition.main_module.clone(),
            modules: definition
                .modules
                .iter()
                .map(TryInto::try_into)
                .collect::<Result<_, _>>()?,
            att: (&definition.attributes).into(),
        })
    }
}

impl TryFrom<JsonDefinition> for Definition {
    type Error = Error;

    fn try_from(definition: JsonDefinition) -> Result<Self, Self::Error> {
        Ok(Self {
            main_module: definition.main_module,
            modules: definition
                .modules
                .into_iter()
                .map(TryInto::try_into)
                .collect::<Result<_, _>>()?,
            attributes: definition.att.into(),
        })
    }
}

#[derive(Serialize, Deserialize)]
struct JsonFlatModule {
    node: FlatModuleNode,
    name: String,
    imports: Vec<JsonImport>,
    #[serde(rename = "localSentences")]
    local_sentences: Vec<JsonSentence>,
    att: JsonAttributes,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum FlatModuleNode {
    KFlatModule,
}

impl TryFrom<&FlatModule> for JsonFlatModule {
    type Error = Error;

    fn try_from(module: &FlatModule) -> Result<Self, Self::Error> {
        Ok(Self {
            node: FlatModuleNode::KFlatModule,
            name: module.name.clone(),
            imports: module.imports.iter().map(Into::into).collect(),
            local_sentences: module
                .local_sentences
                .iter()
                .map(TryInto::try_into)
                .collect::<Result<_, _>>()?,
            att: (&module.attributes).into(),
        })
    }
}

impl TryFrom<JsonFlatModule> for FlatModule {
    type Error = Error;

    fn try_from(module: JsonFlatModule) -> Result<Self, Self::Error> {
        Ok(Self {
            name: module.name,
            imports: module.imports.into_iter().map(Into::into).collect(),
            local_sentences: module
                .local_sentences
                .into_iter()
                .map(TryInto::try_into)
                .collect::<Result<_, _>>()?,
            attributes: module.att.into(),
        })
    }
}

#[derive(Serialize, Deserialize)]
struct JsonImport {
    node: ImportNode,
    name: String,
    #[serde(rename = "isPublic")]
    public: bool,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum ImportNode {
    KImport,
}

impl From<&FlatImport> for JsonImport {
    fn from(import: &FlatImport) -> Self {
        Self {
            node: ImportNode::KImport,
            name: import.name.clone(),
            public: import.public,
        }
    }
}

impl From<JsonImport> for FlatImport {
    fn from(import: JsonImport) -> Self {
        Self {
            name: import.name,
            public: import.public,
        }
    }
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum JsonAssociativity {
    Left,
    Right,
    NonAssoc,
    Unspecified,
}

impl From<Associativity> for JsonAssociativity {
    fn from(associativity: Associativity) -> Self {
        match associativity {
            Associativity::Left => Self::Left,
            Associativity::Right => Self::Right,
            Associativity::NonAssoc => Self::NonAssoc,
            Associativity::Unspecified => Self::Unspecified,
        }
    }
}

impl From<JsonAssociativity> for Associativity {
    fn from(associativity: JsonAssociativity) -> Self {
        match associativity {
            JsonAssociativity::Left => Self::Left,
            JsonAssociativity::Right => Self::Right,
            JsonAssociativity::NonAssoc => Self::NonAssoc,
            JsonAssociativity::Unspecified => Self::Unspecified,
        }
    }
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "node")]
#[allow(clippy::enum_variant_names)] // Variant names mirror the external KAST schema.
enum JsonProductionItem {
    KNonTerminal {
        sort: JsonSort,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        name: Option<String>,
    },
    KRegexTerminal {
        #[serde(
            rename = "precedeRegex",
            default,
            skip_serializing_if = "Option::is_none"
        )]
        precede_regex: Option<String>,
        regex: String,
        #[serde(
            rename = "followRegex",
            default,
            skip_serializing_if = "Option::is_none"
        )]
        follow_regex: Option<String>,
    },
    KTerminal {
        value: String,
    },
}

impl From<&ProductionItem> for JsonProductionItem {
    fn from(item: &ProductionItem) -> Self {
        match item {
            ProductionItem::NonTerminal { sort, name } => Self::KNonTerminal {
                sort: sort.into(),
                name: name.clone(),
            },
            ProductionItem::RegexTerminal {
                precede_regex,
                regex,
                follow_regex,
            } => Self::KRegexTerminal {
                precede_regex: precede_regex.clone(),
                regex: regex.clone(),
                follow_regex: follow_regex.clone(),
            },
            ProductionItem::Terminal(value) => Self::KTerminal {
                value: value.clone(),
            },
        }
    }
}

impl From<JsonProductionItem> for ProductionItem {
    fn from(item: JsonProductionItem) -> Self {
        match item {
            JsonProductionItem::KNonTerminal { sort, name } => Self::NonTerminal {
                sort: sort.into(),
                name,
            },
            JsonProductionItem::KRegexTerminal {
                precede_regex,
                regex,
                follow_regex,
            } => Self::RegexTerminal {
                precede_regex,
                regex,
                follow_regex,
            },
            JsonProductionItem::KTerminal { value } => Self::Terminal(value),
        }
    }
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "node")]
#[allow(clippy::enum_variant_names)] // Variant names mirror the external KAST schema.
enum JsonSentence {
    KSyntaxSort {
        sort: JsonSort,
        params: Vec<JsonSort>,
        att: JsonAttributes,
    },
    KSortSynonym {
        #[serde(rename = "newSort")]
        new_sort: JsonSort,
        #[serde(rename = "oldSort")]
        old_sort: JsonSort,
        att: JsonAttributes,
    },
    KSyntaxLexical {
        name: String,
        regex: String,
        att: JsonAttributes,
    },
    KProduction {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        klabel: Option<JsonLabel>,
        #[serde(rename = "productionItems")]
        production_items: Vec<JsonProductionItem>,
        params: Vec<JsonSort>,
        sort: JsonSort,
        att: JsonAttributes,
    },
    KSyntaxAssociativity {
        assoc: JsonAssociativity,
        tags: Vec<String>,
        att: JsonAttributes,
    },
    KSyntaxPriority {
        priorities: Vec<Vec<String>>,
        att: JsonAttributes,
    },
    KContext {
        body: JsonTerm,
        requires: JsonTerm,
        att: JsonAttributes,
    },
    KRule {
        body: JsonTerm,
        requires: JsonTerm,
        ensures: JsonTerm,
        att: JsonAttributes,
    },
    KClaim {
        body: JsonTerm,
        requires: JsonTerm,
        ensures: JsonTerm,
        att: JsonAttributes,
    },
    KConfiguration {
        body: JsonTerm,
        ensures: JsonTerm,
        att: JsonAttributes,
    },
    KBubble {
        #[serde(rename = "sentenceType")]
        sentence_type: String,
        contents: String,
        att: JsonAttributes,
    },
}

impl TryFrom<&Sentence> for JsonSentence {
    type Error = Error;

    fn try_from(sentence: &Sentence) -> Result<Self, Self::Error> {
        Ok(match sentence {
            Sentence::SyntaxSort {
                parameters,
                sort,
                attributes,
            } => Self::KSyntaxSort {
                sort: sort.into(),
                params: parameters.iter().map(Into::into).collect(),
                att: attributes.into(),
            },
            Sentence::SortSynonym {
                new_sort,
                old_sort,
                attributes,
            } => Self::KSortSynonym {
                new_sort: new_sort.into(),
                old_sort: old_sort.into(),
                att: attributes.into(),
            },
            Sentence::SyntaxLexical {
                name,
                regex,
                attributes,
            } => Self::KSyntaxLexical {
                name: name.clone(),
                regex: regex.clone(),
                att: attributes.into(),
            },
            Sentence::Production {
                label,
                parameters,
                sort,
                items,
                attributes,
            } => Self::KProduction {
                klabel: label.as_ref().map(Into::into),
                production_items: items.iter().map(Into::into).collect(),
                params: parameters.iter().map(Into::into).collect(),
                sort: sort.into(),
                att: attributes.into(),
            },
            Sentence::SyntaxAssociativity {
                associativity,
                tags,
                attributes,
            } => Self::KSyntaxAssociativity {
                assoc: (*associativity).into(),
                tags: tags.clone(),
                att: attributes.into(),
            },
            Sentence::SyntaxPriority {
                priorities,
                attributes,
            } => Self::KSyntaxPriority {
                priorities: priorities.clone(),
                att: attributes.into(),
            },
            Sentence::ContextAlias { .. } => {
                return Err(Error::UnsupportedSentence("KContextAlias"));
            }
            Sentence::Context {
                body,
                requires,
                attributes,
            } => Self::KContext {
                body: body.into(),
                requires: requires.into(),
                att: attributes.into(),
            },
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } => Self::KRule {
                body: body.into(),
                requires: requires.into(),
                ensures: ensures.into(),
                att: attributes.into(),
            },
            Sentence::Claim {
                body,
                requires,
                ensures,
                attributes,
            } => Self::KClaim {
                body: body.into(),
                requires: requires.into(),
                ensures: ensures.into(),
                att: attributes.into(),
            },
            Sentence::Configuration {
                body,
                ensures,
                attributes,
            } => Self::KConfiguration {
                body: body.into(),
                ensures: ensures.into(),
                att: attributes.into(),
            },
            Sentence::Bubble {
                sentence_type,
                contents,
                attributes,
            } => Self::KBubble {
                sentence_type: sentence_type.clone(),
                contents: contents.clone(),
                att: attributes.into(),
            },
        })
    }
}

impl TryFrom<JsonSentence> for Sentence {
    type Error = Error;

    fn try_from(sentence: JsonSentence) -> Result<Self, Self::Error> {
        Ok(match sentence {
            JsonSentence::KSyntaxSort { sort, params, att } => Self::SyntaxSort {
                parameters: params.into_iter().map(Into::into).collect(),
                sort: sort.into(),
                attributes: att.into(),
            },
            JsonSentence::KSortSynonym {
                new_sort,
                old_sort,
                att,
            } => Self::SortSynonym {
                new_sort: new_sort.into(),
                old_sort: old_sort.into(),
                attributes: att.into(),
            },
            JsonSentence::KSyntaxLexical { name, regex, att } => Self::SyntaxLexical {
                name,
                regex,
                attributes: att.into(),
            },
            JsonSentence::KProduction {
                klabel,
                production_items,
                params,
                sort,
                att,
            } => Self::Production {
                label: klabel.map(Into::into),
                parameters: params.into_iter().map(Into::into).collect(),
                sort: sort.into(),
                items: production_items.into_iter().map(Into::into).collect(),
                attributes: att.into(),
            },
            JsonSentence::KSyntaxAssociativity { assoc, tags, att } => Self::SyntaxAssociativity {
                associativity: assoc.into(),
                tags,
                attributes: att.into(),
            },
            JsonSentence::KSyntaxPriority { priorities, att } => Self::SyntaxPriority {
                priorities,
                attributes: att.into(),
            },
            JsonSentence::KContext {
                body,
                requires,
                att,
            } => Self::Context {
                body: body.try_into()?,
                requires: requires.try_into()?,
                attributes: att.into(),
            },
            JsonSentence::KRule {
                body,
                requires,
                ensures,
                att,
            } => Self::Rule {
                body: body.try_into()?,
                requires: requires.try_into()?,
                ensures: ensures.try_into()?,
                attributes: att.into(),
            },
            JsonSentence::KClaim {
                body,
                requires,
                ensures,
                att,
            } => Self::Claim {
                body: body.try_into()?,
                requires: requires.try_into()?,
                ensures: ensures.try_into()?,
                attributes: att.into(),
            },
            JsonSentence::KConfiguration { body, ensures, att } => Self::Configuration {
                body: body.try_into()?,
                ensures: ensures.try_into()?,
                attributes: att.into(),
            },
            JsonSentence::KBubble {
                sentence_type,
                contents,
                att,
            } => Self::Bubble {
                sentence_type,
                contents,
                attributes: att.into(),
            },
        })
    }
}
