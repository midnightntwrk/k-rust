//! KAST JSON version 4 serialization.

use serde::{Deserialize, Serialize};

use super::ast::{Label, Sort, Term};

pub const FORMAT: &str = "KAST";
pub const VERSION: u32 = 4;

#[derive(Debug)]
pub enum Error {
    Json(serde_json::Error),
    UnsupportedFormat(String),
    UnsupportedVersion(u32),
    InvalidArity {
        node: &'static str,
        declared: usize,
        actual: usize,
    },
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Json(error) => error.fmt(formatter),
            Self::UnsupportedFormat(format) => {
                write!(formatter, "unsupported KAST format {format:?}")
            }
            Self::UnsupportedVersion(version) => {
                write!(formatter, "unsupported KAST version {version}")
            }
            Self::InvalidArity {
                node,
                declared,
                actual,
            } => write!(
                formatter,
                "{node} declares arity {declared}, but contains {actual} children"
            ),
        }
    }
}

impl std::error::Error for Error {}

impl From<serde_json::Error> for Error {
    fn from(error: serde_json::Error) -> Self {
        Self::Json(error)
    }
}

#[derive(Serialize, Deserialize)]
struct Envelope {
    format: String,
    version: u32,
    term: JsonTerm,
}

pub fn from_str(input: &str) -> Result<Term, Error> {
    let envelope: Envelope = serde_json::from_str(input)?;
    if envelope.format != FORMAT {
        return Err(Error::UnsupportedFormat(envelope.format));
    }
    if envelope.version != VERSION {
        return Err(Error::UnsupportedVersion(envelope.version));
    }
    envelope.term.try_into()
}

pub fn to_string(term: &Term) -> Result<String, Error> {
    Ok(serde_json::to_string(&Envelope {
        format: FORMAT.into(),
        version: VERSION,
        term: term.into(),
    })?)
}

pub fn to_string_pretty(term: &Term) -> Result<String, Error> {
    Ok(serde_json::to_string_pretty(&Envelope {
        format: FORMAT.into(),
        version: VERSION,
        term: term.into(),
    })?)
}

#[derive(Clone, Serialize, Deserialize)]
struct JsonSort {
    node: SortNode,
    name: String,
    params: Vec<JsonSort>,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum SortNode {
    KSort,
}

#[derive(Clone, Serialize, Deserialize)]
struct JsonLabel {
    node: LabelNode,
    name: String,
    params: Vec<JsonSort>,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum LabelNode {
    KLabel,
}

impl From<&Sort> for JsonSort {
    fn from(sort: &Sort) -> Self {
        Self {
            node: SortNode::KSort,
            name: sort.name.clone(),
            params: sort.parameters.iter().map(Into::into).collect(),
        }
    }
}

impl From<JsonSort> for Sort {
    fn from(sort: JsonSort) -> Self {
        Self {
            name: sort.name,
            parameters: sort.params.into_iter().map(Into::into).collect(),
        }
    }
}

impl From<&Label> for JsonLabel {
    fn from(label: &Label) -> Self {
        Self {
            node: LabelNode::KLabel,
            name: label.name.clone(),
            params: label.parameters.iter().map(Into::into).collect(),
        }
    }
}

impl From<JsonLabel> for Label {
    fn from(label: JsonLabel) -> Self {
        Self {
            name: label.name,
            parameters: label.params.into_iter().map(Into::into).collect(),
        }
    }
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "node")]
enum JsonTerm {
    KToken {
        sort: JsonSort,
        token: String,
    },
    KApply {
        label: JsonLabel,
        arity: usize,
        args: Vec<JsonTerm>,
    },
    KSequence {
        arity: usize,
        items: Vec<JsonTerm>,
    },
    KVariable {
        name: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        sort: Option<JsonSort>,
    },
    KRewrite {
        lhs: Box<JsonTerm>,
        rhs: Box<JsonTerm>,
    },
    KAs {
        pattern: Box<JsonTerm>,
        alias: Box<JsonTerm>,
    },
    InjectedKLabel {
        label: JsonLabel,
    },
}

impl From<&Term> for JsonTerm {
    fn from(term: &Term) -> Self {
        match term {
            Term::Token { token, sort } => Self::KToken {
                sort: sort.into(),
                token: token.clone(),
            },
            Term::Apply { label, arguments } => Self::KApply {
                label: label.into(),
                arity: arguments.len(),
                args: arguments.iter().map(Into::into).collect(),
            },
            Term::Sequence(items) => Self::KSequence {
                arity: items.len(),
                items: items.iter().map(Into::into).collect(),
            },
            Term::Variable { name, sort } => Self::KVariable {
                name: name.clone(),
                sort: sort.as_ref().map(Into::into),
            },
            Term::Rewrite { left, right } => Self::KRewrite {
                lhs: Box::new(left.as_ref().into()),
                rhs: Box::new(right.as_ref().into()),
            },
            Term::As { pattern, alias } => Self::KAs {
                pattern: Box::new(pattern.as_ref().into()),
                alias: Box::new(alias.as_ref().into()),
            },
            Term::InjectedLabel(label) => Self::InjectedKLabel {
                label: label.into(),
            },
        }
    }
}

impl TryFrom<JsonTerm> for Term {
    type Error = Error;

    fn try_from(term: JsonTerm) -> Result<Self, Self::Error> {
        fn boxed(term: JsonTerm) -> Result<Box<Term>, Error> {
            Ok(Box::new(term.try_into()?))
        }
        fn terms(values: Vec<JsonTerm>) -> Result<Vec<Term>, Error> {
            values.into_iter().map(TryInto::try_into).collect()
        }
        fn checked(
            node: &'static str,
            declared: usize,
            values: Vec<JsonTerm>,
        ) -> Result<Vec<Term>, Error> {
            if declared != values.len() {
                return Err(Error::InvalidArity {
                    node,
                    declared,
                    actual: values.len(),
                });
            }
            terms(values)
        }

        Ok(match term {
            JsonTerm::KToken { sort, token } => Self::Token {
                token,
                sort: sort.into(),
            },
            JsonTerm::KApply { label, arity, args } => Self::Apply {
                label: label.into(),
                arguments: checked("KApply", arity, args)?,
            },
            JsonTerm::KSequence { arity, items } => {
                Self::Sequence(checked("KSequence", arity, items)?)
            }
            JsonTerm::KVariable { name, sort } => Self::Variable {
                name,
                sort: sort.map(Into::into),
            },
            JsonTerm::KRewrite { lhs, rhs } => Self::Rewrite {
                left: boxed(*lhs)?,
                right: boxed(*rhs)?,
            },
            JsonTerm::KAs { pattern, alias } => Self::As {
                pattern: boxed(*pattern)?,
                alias: boxed(*alias)?,
            },
            JsonTerm::InjectedKLabel { label } => Self::InjectedLabel(label.into()),
        })
    }
}
