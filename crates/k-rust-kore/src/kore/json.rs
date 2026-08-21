//! KORE JSON version 1 serialization.

use serde::{Deserialize, Serialize};

use super::ast::{Associativity, Pattern, Sort, Symbol, Variable, VariableKind};

pub const FORMAT: &str = "KORE";
pub const VERSION: u32 = 1;

#[derive(Debug)]
pub enum Error {
    Json(serde_json::Error),
    UnsupportedFormat(String),
    UnsupportedVersion(u32),
    EmptyAssociativeApplication,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Json(error) => error.fmt(f),
            Self::UnsupportedFormat(format) => write!(f, "unsupported KORE JSON format {format:?}"),
            Self::UnsupportedVersion(version) => {
                write!(f, "unsupported KORE JSON version {version}")
            }
            Self::EmptyAssociativeApplication => {
                f.write_str("associative application requires at least one argument")
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

#[derive(Serialize, Deserialize)]
struct Envelope {
    format: String,
    version: u32,
    term: JsonPattern,
}

pub fn from_str(input: &str) -> Result<Pattern, Error> {
    let envelope: Envelope = serde_json::from_str(input)?;
    decode_envelope(envelope)
}

/// Decode KORE JSON without serde_json's nesting limit.
///
/// Callers must provide enough stack for deeply nested syntax. The regular [`from_str`] remains
/// bounded for untrusted and stack-constrained environments.
pub fn from_str_unbounded(input: &str) -> Result<Pattern, Error> {
    let mut deserializer = serde_json::Deserializer::from_str(input);
    deserializer.disable_recursion_limit();
    let envelope = Envelope::deserialize(&mut deserializer)?;
    decode_envelope(envelope)
}

fn decode_envelope(envelope: Envelope) -> Result<Pattern, Error> {
    if envelope.format != FORMAT {
        return Err(Error::UnsupportedFormat(envelope.format));
    }
    if envelope.version != VERSION {
        return Err(Error::UnsupportedVersion(envelope.version));
    }
    envelope.term.try_into()
}

pub fn to_string(pattern: &Pattern) -> Result<String, Error> {
    Ok(serde_json::to_string(&Envelope {
        format: FORMAT.into(),
        version: VERSION,
        term: pattern.into(),
    })?)
}

pub fn to_string_pretty(pattern: &Pattern) -> Result<String, Error> {
    Ok(serde_json::to_string_pretty(&Envelope {
        format: FORMAT.into(),
        version: VERSION,
        term: pattern.into(),
    })?)
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(tag = "tag")]
enum JsonSort {
    SortVar { name: String },
    SortApp { name: String, args: Vec<JsonSort> },
}

impl From<&Sort> for JsonSort {
    fn from(sort: &Sort) -> Self {
        match sort {
            Sort::Variable(name) => Self::SortVar { name: name.clone() },
            Sort::Application { name, arguments } => Self::SortApp {
                name: name.clone(),
                args: arguments.iter().map(Into::into).collect(),
            },
        }
    }
}

impl From<JsonSort> for Sort {
    fn from(sort: JsonSort) -> Self {
        match sort {
            JsonSort::SortVar { name } => Self::Variable(name),
            JsonSort::SortApp { name, args } => Self::Application {
                name,
                arguments: args.into_iter().map(Into::into).collect(),
            },
        }
    }
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "tag")]
enum JsonPattern {
    String {
        value: String,
    },
    EVar {
        name: String,
        sort: JsonSort,
    },
    SVar {
        name: String,
        sort: JsonSort,
    },
    App {
        name: String,
        sorts: Vec<JsonSort>,
        args: Vec<JsonPattern>,
    },
    Top {
        sort: JsonSort,
    },
    Bottom {
        sort: JsonSort,
    },
    And {
        sort: JsonSort,
        #[serde(flatten)]
        arguments: JsonArguments,
    },
    Or {
        sort: JsonSort,
        #[serde(flatten)]
        arguments: JsonArguments,
    },
    Not {
        sort: JsonSort,
        arg: Box<JsonPattern>,
    },
    Next {
        sort: JsonSort,
        dest: Box<JsonPattern>,
    },
    Implies {
        sort: JsonSort,
        first: Box<JsonPattern>,
        second: Box<JsonPattern>,
    },
    Iff {
        sort: JsonSort,
        first: Box<JsonPattern>,
        second: Box<JsonPattern>,
    },
    Rewrites {
        sort: JsonSort,
        source: Box<JsonPattern>,
        dest: Box<JsonPattern>,
    },
    Exists {
        sort: JsonSort,
        var: String,
        #[serde(rename = "varSort")]
        var_sort: JsonSort,
        arg: Box<JsonPattern>,
    },
    Forall {
        sort: JsonSort,
        var: String,
        #[serde(rename = "varSort")]
        var_sort: JsonSort,
        arg: Box<JsonPattern>,
    },
    Mu {
        var: String,
        #[serde(rename = "varSort")]
        var_sort: JsonSort,
        arg: Box<JsonPattern>,
    },
    Nu {
        var: String,
        #[serde(rename = "varSort")]
        var_sort: JsonSort,
        arg: Box<JsonPattern>,
    },
    Ceil {
        #[serde(rename = "argSort")]
        arg_sort: JsonSort,
        sort: JsonSort,
        arg: Box<JsonPattern>,
    },
    Floor {
        #[serde(rename = "argSort")]
        arg_sort: JsonSort,
        sort: JsonSort,
        arg: Box<JsonPattern>,
    },
    Equals {
        #[serde(rename = "argSort")]
        arg_sort: JsonSort,
        sort: JsonSort,
        first: Box<JsonPattern>,
        second: Box<JsonPattern>,
    },
    In {
        #[serde(rename = "argSort")]
        arg_sort: JsonSort,
        sort: JsonSort,
        first: Box<JsonPattern>,
        second: Box<JsonPattern>,
    },
    DV {
        sort: JsonSort,
        value: String,
    },
    LeftAssoc {
        symbol: String,
        sorts: Vec<JsonSort>,
        argss: Vec<JsonPattern>,
    },
    RightAssoc {
        symbol: String,
        sorts: Vec<JsonSort>,
        argss: Vec<JsonPattern>,
    },
}

#[derive(Serialize, Deserialize)]
#[serde(untagged)]
enum JsonArguments {
    Variadic {
        patterns: Vec<JsonPattern>,
    },
    Binary {
        first: Box<JsonPattern>,
        second: Box<JsonPattern>,
    },
}

impl JsonArguments {
    fn into_patterns(self) -> Vec<JsonPattern> {
        match self {
            Self::Variadic { patterns } => patterns,
            Self::Binary { first, second } => vec![*first, *second],
        }
    }
}

impl From<&Pattern> for JsonPattern {
    fn from(pattern: &Pattern) -> Self {
        fn sorts(sort: &Sort) -> JsonSort {
            sort.into()
        }
        fn pat(pattern: &Pattern) -> Box<JsonPattern> {
            Box::new(pattern.into())
        }
        match pattern {
            Pattern::String(value) => Self::String {
                value: value.clone(),
            },
            Pattern::Variable(variable) => match variable.kind {
                VariableKind::Element => Self::EVar {
                    name: variable.name.clone(),
                    sort: sorts(&variable.sort),
                },
                VariableKind::Set => Self::SVar {
                    name: variable.name.clone(),
                    sort: sorts(&variable.sort),
                },
            },
            Pattern::Application { symbol, arguments } => Self::App {
                name: symbol.name.clone(),
                sorts: symbol.sort_parameters.iter().map(Into::into).collect(),
                args: arguments.iter().map(Into::into).collect(),
            },
            Pattern::Top { sort } => Self::Top { sort: sorts(sort) },
            Pattern::Bottom { sort } => Self::Bottom { sort: sorts(sort) },
            Pattern::And { sort, arguments } => Self::And {
                sort: sorts(sort),
                arguments: JsonArguments::Variadic {
                    patterns: arguments.iter().map(Into::into).collect(),
                },
            },
            Pattern::Or { sort, arguments } => Self::Or {
                sort: sorts(sort),
                arguments: JsonArguments::Variadic {
                    patterns: arguments.iter().map(Into::into).collect(),
                },
            },
            Pattern::Not { sort, argument } => Self::Not {
                sort: sorts(sort),
                arg: pat(argument),
            },
            Pattern::Next { sort, argument } => Self::Next {
                sort: sorts(sort),
                dest: pat(argument),
            },
            Pattern::Implies { sort, left, right } => Self::Implies {
                sort: sorts(sort),
                first: pat(left),
                second: pat(right),
            },
            Pattern::Iff { sort, left, right } => Self::Iff {
                sort: sorts(sort),
                first: pat(left),
                second: pat(right),
            },
            Pattern::Rewrites { sort, left, right } => Self::Rewrites {
                sort: sorts(sort),
                source: pat(left),
                dest: pat(right),
            },
            Pattern::Exists {
                sort,
                variable,
                body,
            } => Self::Exists {
                sort: sorts(sort),
                var: variable.name.clone(),
                var_sort: sorts(&variable.sort),
                arg: pat(body),
            },
            Pattern::Forall {
                sort,
                variable,
                body,
            } => Self::Forall {
                sort: sorts(sort),
                var: variable.name.clone(),
                var_sort: sorts(&variable.sort),
                arg: pat(body),
            },
            Pattern::Mu { variable, body } => Self::Mu {
                var: variable.name.clone(),
                var_sort: sorts(&variable.sort),
                arg: pat(body),
            },
            Pattern::Nu { variable, body } => Self::Nu {
                var: variable.name.clone(),
                var_sort: sorts(&variable.sort),
                arg: pat(body),
            },
            Pattern::Ceil {
                operand_sort,
                result_sort,
                argument,
            } => Self::Ceil {
                arg_sort: sorts(operand_sort),
                sort: sorts(result_sort),
                arg: pat(argument),
            },
            Pattern::Floor {
                operand_sort,
                result_sort,
                argument,
            } => Self::Floor {
                arg_sort: sorts(operand_sort),
                sort: sorts(result_sort),
                arg: pat(argument),
            },
            Pattern::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            } => Self::Equals {
                arg_sort: sorts(operand_sort),
                sort: sorts(result_sort),
                first: pat(left),
                second: pat(right),
            },
            Pattern::In {
                operand_sort,
                result_sort,
                left,
                right,
            } => Self::In {
                arg_sort: sorts(operand_sort),
                sort: sorts(result_sort),
                first: pat(left),
                second: pat(right),
            },
            Pattern::DomainValue { sort, value } => Self::DV {
                sort: sorts(sort),
                value: value.clone(),
            },
            Pattern::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } => {
                let fields = (
                    symbol.name.clone(),
                    symbol.sort_parameters.iter().map(Into::into).collect(),
                    arguments.iter().map(Into::into).collect(),
                );
                match associativity {
                    Associativity::Left => Self::LeftAssoc {
                        symbol: fields.0,
                        sorts: fields.1,
                        argss: fields.2,
                    },
                    Associativity::Right => Self::RightAssoc {
                        symbol: fields.0,
                        sorts: fields.1,
                        argss: fields.2,
                    },
                }
            }
        }
    }
}

impl TryFrom<JsonPattern> for Pattern {
    type Error = Error;

    fn try_from(pattern: JsonPattern) -> Result<Self, Error> {
        fn variable(kind: VariableKind, name: String, sort: JsonSort) -> Variable {
            Variable {
                kind,
                name,
                sort: sort.into(),
            }
        }
        fn boxed(pattern: JsonPattern) -> Result<Box<Pattern>, Error> {
            Ok(Box::new(pattern.try_into()?))
        }
        fn patterns(values: Vec<JsonPattern>) -> Result<Vec<Pattern>, Error> {
            values.into_iter().map(TryInto::try_into).collect()
        }
        fn symbol(name: String, sorts: Vec<JsonSort>) -> Symbol {
            Symbol {
                name,
                sort_parameters: sorts.into_iter().map(Into::into).collect(),
            }
        }
        Ok(match pattern {
            JsonPattern::String { value } => Self::String(value),
            JsonPattern::EVar { name, sort } => {
                Self::Variable(variable(VariableKind::Element, name, sort))
            }
            JsonPattern::SVar { name, sort } => {
                Self::Variable(variable(VariableKind::Set, name, sort))
            }
            JsonPattern::App { name, sorts, args } => Self::Application {
                symbol: symbol(name, sorts),
                arguments: patterns(args)?,
            },
            JsonPattern::Top { sort } => Self::Top { sort: sort.into() },
            JsonPattern::Bottom { sort } => Self::Bottom { sort: sort.into() },
            JsonPattern::And { sort, arguments } => Self::And {
                sort: sort.into(),
                arguments: patterns(arguments.into_patterns())?,
            },
            JsonPattern::Or { sort, arguments } => Self::Or {
                sort: sort.into(),
                arguments: patterns(arguments.into_patterns())?,
            },
            JsonPattern::Not { sort, arg } => Self::Not {
                sort: sort.into(),
                argument: boxed(*arg)?,
            },
            JsonPattern::Next { sort, dest } => Self::Next {
                sort: sort.into(),
                argument: boxed(*dest)?,
            },
            JsonPattern::Implies {
                sort,
                first,
                second,
            } => Self::Implies {
                sort: sort.into(),
                left: boxed(*first)?,
                right: boxed(*second)?,
            },
            JsonPattern::Iff {
                sort,
                first,
                second,
            } => Self::Iff {
                sort: sort.into(),
                left: boxed(*first)?,
                right: boxed(*second)?,
            },
            JsonPattern::Rewrites { sort, source, dest } => Self::Rewrites {
                sort: sort.into(),
                left: boxed(*source)?,
                right: boxed(*dest)?,
            },
            JsonPattern::Exists {
                sort,
                var,
                var_sort,
                arg,
            } => Self::Exists {
                sort: sort.into(),
                variable: variable(VariableKind::Element, var, var_sort),
                body: boxed(*arg)?,
            },
            JsonPattern::Forall {
                sort,
                var,
                var_sort,
                arg,
            } => Self::Forall {
                sort: sort.into(),
                variable: variable(VariableKind::Element, var, var_sort),
                body: boxed(*arg)?,
            },
            JsonPattern::Mu { var, var_sort, arg } => Self::Mu {
                variable: variable(VariableKind::Set, var, var_sort),
                body: boxed(*arg)?,
            },
            JsonPattern::Nu { var, var_sort, arg } => Self::Nu {
                variable: variable(VariableKind::Set, var, var_sort),
                body: boxed(*arg)?,
            },
            JsonPattern::Ceil {
                arg_sort,
                sort,
                arg,
            } => Self::Ceil {
                operand_sort: arg_sort.into(),
                result_sort: sort.into(),
                argument: boxed(*arg)?,
            },
            JsonPattern::Floor {
                arg_sort,
                sort,
                arg,
            } => Self::Floor {
                operand_sort: arg_sort.into(),
                result_sort: sort.into(),
                argument: boxed(*arg)?,
            },
            JsonPattern::Equals {
                arg_sort,
                sort,
                first,
                second,
            } => Self::Equals {
                operand_sort: arg_sort.into(),
                result_sort: sort.into(),
                left: boxed(*first)?,
                right: boxed(*second)?,
            },
            JsonPattern::In {
                arg_sort,
                sort,
                first,
                second,
            } => Self::In {
                operand_sort: arg_sort.into(),
                result_sort: sort.into(),
                left: boxed(*first)?,
                right: boxed(*second)?,
            },
            JsonPattern::DV { sort, value } => Self::DomainValue {
                sort: sort.into(),
                value,
            },
            JsonPattern::LeftAssoc {
                symbol: name,
                sorts,
                argss,
            } => associative(Associativity::Left, symbol(name, sorts), patterns(argss)?)?,
            JsonPattern::RightAssoc {
                symbol: name,
                sorts,
                argss,
            } => associative(Associativity::Right, symbol(name, sorts), patterns(argss)?)?,
        })
    }
}

fn associative(
    associativity: Associativity,
    symbol: Symbol,
    arguments: Vec<Pattern>,
) -> Result<Pattern, Error> {
    if arguments.is_empty() {
        Err(Error::EmptyAssociativeApplication)
    } else {
        Ok(Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kore::parser::parse_pattern;

    #[test]
    fn accepts_binary_and_or_fields_from_legacy_version_one_producers() {
        let decoded = from_str(
            r#"{
                "format": "KORE",
                "version": 1,
                "term": {
                    "tag": "And",
                    "sort": { "tag": "SortApp", "name": "SortK", "args": [] },
                    "first": {
                        "tag": "EVar",
                        "name": "X",
                        "sort": { "tag": "SortApp", "name": "SortK", "args": [] }
                    },
                    "second": {
                        "tag": "EVar",
                        "name": "Y",
                        "sort": { "tag": "SortApp", "name": "SortK", "args": [] }
                    }
                }
            }"#,
        )
        .unwrap();

        assert_eq!(
            decoded,
            parse_pattern(r"\and{SortK{}}(X:SortK{}, Y:SortK{})").unwrap()
        );
    }

    #[test]
    fn serializes_variadic_and_or_fields_without_collapsing_arity() {
        let pattern = parse_pattern(r"\or{SortK{}}()").unwrap();
        let encoded = to_string(&pattern).unwrap();

        assert!(encoded.contains(r#""patterns":[]"#));
        assert!(!encoded.contains(r#""first""#));
        assert_eq!(from_str(&encoded).unwrap(), pattern);
    }

    #[test]
    fn explicitly_decodes_deep_kore_json_without_the_default_limit() {
        let sort = r#"{"tag":"SortApp","name":"SortK","args":[]}"#;
        let mut term = format!(r#"{{"tag":"Top","sort":{sort}}}"#);
        for _ in 0..140 {
            term = format!(r#"{{"tag":"Not","sort":{sort},"arg":{term}}}"#);
        }
        let source = format!(r#"{{"format":"KORE","version":1,"term":{term}}}"#);

        assert!(from_str(&source).is_err());
        assert!(from_str_unbounded(&source).is_ok());
    }
}
