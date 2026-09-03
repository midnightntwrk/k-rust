//! KORE JSON version 1 serialization.

use serde::{Deserialize, Serialize};

use super::{
    ast::{Associativity, Pattern, Sort, Symbol, Variable, VariableKind},
    lexical::{self, Problem},
};

pub const FORMAT: &str = "KORE";
pub const VERSION: u32 = 1;

#[derive(Debug)]
pub enum Error {
    Json(serde_json::Error),
    Shape(String),
    Lexical {
        kind: &'static str,
        text: String,
        problems: Vec<Problem>,
    },
    UnsupportedFormat(String),
    UnsupportedVersion(u32),
    EmptyAssociativeApplication,
    EmptyMultiOr,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Json(error) => error.fmt(f),
            Self::Shape(message) => f.write_str(message),
            Self::Lexical {
                kind,
                text,
                problems,
            } => {
                write!(
                    f,
                    "Lexical {} in {kind} : {text}",
                    if problems.len() == 1 {
                        "error"
                    } else {
                        "errors"
                    }
                )?;
                for problem in problems {
                    write!(f, " * {problem}")?;
                }
                Ok(())
            }
            Self::UnsupportedFormat(format) => write!(f, "unsupported KORE JSON format {format:?}"),
            Self::UnsupportedVersion(version) => {
                write!(f, "unsupported KORE JSON version {version}")
            }
            Self::EmptyAssociativeApplication => {
                f.write_str("associative application requires at least one argument")
            }
            Self::EmptyMultiOr => f.write_str("MultiOr requires at least one argument"),
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
    deserializer.end()?;
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

fn require_lexical(kind: &'static str, text: &str, problems: Vec<Problem>) -> Result<(), Error> {
    if problems.is_empty() {
        Ok(())
    } else {
        Err(Error::Lexical {
            kind,
            text: text.to_owned(),
            problems,
        })
    }
}

pub fn to_string(pattern: &Pattern) -> Result<String, Error> {
    Ok(serde_json::to_string(&Envelope {
        format: FORMAT.into(),
        version: VERSION,
        term: pattern.into(),
    })?)
}

/// Convert a KORE pattern to a JSON value without serde_json's nesting limit.
///
/// Callers must provide enough stack for deeply nested syntax.
pub fn to_value(pattern: &Pattern) -> Result<serde_json::Value, Error> {
    let encoded = to_string(pattern)?;
    let mut deserializer = serde_json::Deserializer::from_str(&encoded);
    deserializer.disable_recursion_limit();
    let value = serde_json::Value::deserialize(&mut deserializer)?;
    deserializer.end()?;
    Ok(value)
}

pub fn to_string_pretty(pattern: &Pattern) -> Result<String, Error> {
    Ok(serde_json::to_string_pretty(&Envelope {
        format: FORMAT.into(),
        version: VERSION,
        term: pattern.into(),
    })?)
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(tag = "tag", deny_unknown_fields)]
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
#[serde(tag = "tag", deny_unknown_fields)]
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
        #[serde(skip_serializing_if = "Option::is_none")]
        patterns: Option<Vec<JsonPattern>>,
        #[serde(skip_serializing_if = "Option::is_none")]
        first: Option<Box<JsonPattern>>,
        #[serde(skip_serializing_if = "Option::is_none")]
        second: Option<Box<JsonPattern>>,
    },
    Or {
        sort: JsonSort,
        #[serde(skip_serializing_if = "Option::is_none")]
        patterns: Option<Vec<JsonPattern>>,
        #[serde(skip_serializing_if = "Option::is_none")]
        first: Option<Box<JsonPattern>>,
        #[serde(skip_serializing_if = "Option::is_none")]
        second: Option<Box<JsonPattern>>,
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
    MultiOr {
        assoc: LeftRight,
        sort: JsonSort,
        argss: Vec<JsonPattern>,
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
enum LeftRight {
    Left,
    Right,
}

impl JsonPattern {
    fn check_lexical(&self) -> Result<(), Error> {
        match self {
            Self::String { value } => {
                require_lexical("string literal", value, lexical::latin1_problems(value))
            }
            Self::EVar { name, .. } => {
                require_lexical("element variable", name, lexical::identifier_problems(name))
            }
            Self::SVar { name, .. } => {
                require_lexical("set variable", name, lexical::set_variable_problems(name))
            }
            Self::App { name, .. } => {
                require_lexical("app symbol", name, lexical::symbol_problems(name))
            }
            Self::Exists { var, .. } | Self::Forall { var, .. } => require_lexical(
                "quantifier variable",
                var,
                lexical::identifier_problems(var),
            ),
            Self::Mu { var, .. } | Self::Nu { var, .. } => require_lexical(
                "fixpoint expression variable",
                var,
                lexical::set_variable_problems(var),
            ),
            Self::DV { value, .. } => require_lexical(
                "domain value string",
                value,
                lexical::latin1_problems(value),
            ),
            Self::LeftAssoc { symbol, .. } | Self::RightAssoc { symbol, .. } => require_lexical(
                "left-assoc symbol",
                symbol,
                lexical::symbol_problems(symbol),
            ),
            _ => Ok(()),
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
                patterns: Some(arguments.iter().map(Into::into).collect()),
                first: None,
                second: None,
            },
            Pattern::Or { sort, arguments } => Self::Or {
                sort: sorts(sort),
                patterns: Some(arguments.iter().map(Into::into).collect()),
                first: None,
                second: None,
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
        pattern.check_lexical()?;
        match pattern {
            JsonPattern::And {
                sort,
                patterns: variadic,
                first,
                second,
            } => Ok(Self::And {
                sort: sort.into(),
                arguments: patterns(json_arguments(variadic, first, second)?)?,
            }),
            JsonPattern::Or {
                sort,
                patterns: variadic,
                first,
                second,
            } => Ok(Self::Or {
                sort: sort.into(),
                arguments: patterns(json_arguments(variadic, first, second)?)?,
            }),
            JsonPattern::MultiOr { assoc, sort, argss } => {
                multi_or(assoc, sort.into(), patterns(argss)?)
            }
            JsonPattern::Not { sort, arg } => Ok(Self::Not {
                sort: sort.into(),
                argument: boxed(*arg)?,
            }),
            pattern => convert_regular_pattern(pattern),
        }
    }
}

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

fn convert_regular_pattern(pattern: JsonPattern) -> Result<Pattern, Error> {
    Ok(match pattern {
        JsonPattern::String { value } => Pattern::String(value),
        JsonPattern::EVar { name, sort } => {
            Pattern::Variable(variable(VariableKind::Element, name, sort))
        }
        JsonPattern::SVar { name, sort } => {
            Pattern::Variable(variable(VariableKind::Set, name, sort))
        }
        JsonPattern::App { name, sorts, args } => Pattern::Application {
            symbol: symbol(name, sorts),
            arguments: patterns(args)?,
        },
        JsonPattern::Top { sort } => Pattern::Top { sort: sort.into() },
        JsonPattern::Bottom { sort } => Pattern::Bottom { sort: sort.into() },
        JsonPattern::Next { sort, dest } => Pattern::Next {
            sort: sort.into(),
            argument: boxed(*dest)?,
        },
        JsonPattern::Implies {
            sort,
            first,
            second,
        } => Pattern::Implies {
            sort: sort.into(),
            left: boxed(*first)?,
            right: boxed(*second)?,
        },
        JsonPattern::Iff {
            sort,
            first,
            second,
        } => Pattern::Iff {
            sort: sort.into(),
            left: boxed(*first)?,
            right: boxed(*second)?,
        },
        JsonPattern::Rewrites { sort, source, dest } => Pattern::Rewrites {
            sort: sort.into(),
            left: boxed(*source)?,
            right: boxed(*dest)?,
        },
        JsonPattern::Exists {
            sort,
            var,
            var_sort,
            arg,
        } => Pattern::Exists {
            sort: sort.into(),
            variable: variable(VariableKind::Element, var, var_sort),
            body: boxed(*arg)?,
        },
        JsonPattern::Forall {
            sort,
            var,
            var_sort,
            arg,
        } => Pattern::Forall {
            sort: sort.into(),
            variable: variable(VariableKind::Element, var, var_sort),
            body: boxed(*arg)?,
        },
        JsonPattern::Mu { var, var_sort, arg } => Pattern::Mu {
            variable: variable(VariableKind::Set, var, var_sort),
            body: boxed(*arg)?,
        },
        JsonPattern::Nu { var, var_sort, arg } => Pattern::Nu {
            variable: variable(VariableKind::Set, var, var_sort),
            body: boxed(*arg)?,
        },
        JsonPattern::Ceil {
            arg_sort,
            sort,
            arg,
        } => Pattern::Ceil {
            operand_sort: arg_sort.into(),
            result_sort: sort.into(),
            argument: boxed(*arg)?,
        },
        JsonPattern::Floor {
            arg_sort,
            sort,
            arg,
        } => Pattern::Floor {
            operand_sort: arg_sort.into(),
            result_sort: sort.into(),
            argument: boxed(*arg)?,
        },
        JsonPattern::Equals {
            arg_sort,
            sort,
            first,
            second,
        } => Pattern::Equals {
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
        } => Pattern::In {
            operand_sort: arg_sort.into(),
            result_sort: sort.into(),
            left: boxed(*first)?,
            right: boxed(*second)?,
        },
        JsonPattern::DV { sort, value } => Pattern::DomainValue {
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
        JsonPattern::And { .. }
        | JsonPattern::Or { .. }
        | JsonPattern::Not { .. }
        | JsonPattern::MultiOr { .. } => {
            unreachable!("special JSON pattern handled before regular conversion")
        }
    })
}

fn json_arguments(
    patterns: Option<Vec<JsonPattern>>,
    first: Option<Box<JsonPattern>>,
    second: Option<Box<JsonPattern>>,
) -> Result<Vec<JsonPattern>, Error> {
    if let Some(patterns) = patterns {
        if first.is_some() {
            return Err(Error::Shape("unknown field `first`".into()));
        }
        if second.is_some() {
            return Err(Error::Shape("unknown field `second`".into()));
        }
        return Ok(patterns);
    }

    let first = first.ok_or_else(|| Error::Shape("missing field `first`".into()))?;
    let second = second.ok_or_else(|| Error::Shape("missing field `second`".into()))?;
    Ok(vec![*first, *second])
}

fn multi_or(
    associativity: LeftRight,
    sort: Sort,
    arguments: Vec<Pattern>,
) -> Result<Pattern, Error> {
    let mut arguments = arguments.into_iter();
    let first = arguments.next().ok_or(Error::EmptyMultiOr)?;

    Ok(match associativity {
        LeftRight::Left => arguments.fold(first, |left, right| Pattern::Or {
            sort: sort.clone(),
            arguments: vec![left, right],
        }),
        LeftRight::Right => {
            let mut arguments = std::iter::once(first).chain(arguments).rev();
            let last = arguments.next().expect("MultiOr has at least one argument");
            arguments.fold(last, |right, left| Pattern::Or {
                sort: sort.clone(),
                arguments: vec![left, right],
            })
        }
    })
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
    use serde_json::{Value, json};

    fn sort() -> Value {
        json!({ "tag": "SortApp", "name": "S", "args": [] })
    }

    fn app(name: &str) -> Value {
        json!({ "tag": "App", "name": name, "sorts": [], "args": [] })
    }

    fn document(term: Value) -> String {
        json!({ "format": "KORE", "version": 1, "term": term }).to_string()
    }

    fn decode(term: Value) -> Result<Pattern, Error> {
        from_str(&document(term))
    }

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

    #[test]
    fn converts_deep_kore_patterns_to_json_values_without_the_default_limit() {
        let sort = Sort::Application {
            name: "SortK".into(),
            arguments: Vec::new(),
        };
        let pattern = (0..160).fold(Pattern::Top { sort: sort.clone() }, |argument, _| {
            Pattern::Not {
                sort: sort.clone(),
                argument: Box::new(argument),
            }
        });

        assert!(to_value(&pattern).is_ok());
    }

    #[test]
    fn rejects_reference_lexical_errors() {
        let cases = [
            (
                json!({ "tag": "SVar", "name": "X", "sort": sort() }),
                "Lexical errors in set variable : X",
            ),
            (
                json!({ "tag": "EVar", "name": "foo bar", "sort": sort() }),
                "Lexical error in element variable : foo bar",
            ),
            (
                json!({ "tag": "EVar", "name": "é", "sort": sort() }),
                "Lexical error in element variable : é",
            ),
            (
                json!({ "tag": "App", "name": "a b", "sorts": [], "args": [] }),
                "Lexical error in app symbol : a b",
            ),
            (
                json!({ "tag": "App", "name": "", "sorts": [], "args": [] }),
                "Lexical error in app symbol : ",
            ),
            (
                json!({ "tag": "DV", "sort": sort(), "value": "≤" }),
                "Lexical error in domain value string : ≤",
            ),
            (
                json!({ "tag": "String", "value": "Ā" }),
                "Lexical error in string literal : Ā",
            ),
            (
                json!({ "tag": "Mu", "var": "X", "varSort": sort(), "arg": app("a") }),
                "Lexical errors in fixpoint expression variable : X",
            ),
        ];

        for (term, expected_prefix) in cases {
            let error = decode(term).expect_err("reference lexical error must be rejected");
            assert!(
                error.to_string().starts_with(expected_prefix),
                "expected {expected_prefix:?}, got {error}"
            );
        }
    }

    #[test]
    fn rejects_unknown_fields_below_the_envelope_only() {
        assert!(
            decode(json!({ "tag": "Top", "sort": sort(), "bogus": 1 }))
                .unwrap_err()
                .to_string()
                .contains("unknown field")
        );
        assert!(
            decode(json!({
                "tag": "Top",
                "sort": { "tag": "SortApp", "name": "S", "args": [], "bogus": 1 }
            }))
            .unwrap_err()
            .to_string()
            .contains("unknown field")
        );
        assert!(
            decode(json!({
                "tag": "And",
                "sort": sort(),
                "patterns": [app("a")],
                "first": app("b")
            }))
            .unwrap_err()
            .to_string()
            .contains("unknown field `first`")
        );

        let source = json!({
            "format": "KORE",
            "version": 1,
            "term": { "tag": "Top", "sort": sort() },
            "extra": 1
        })
        .to_string();
        assert!(from_str(&source).is_ok());
    }

    #[test]
    fn decodes_multi_or_as_the_reference_expands_it() {
        let multi_or = |assoc: &str, argss: Vec<Value>| json!({ "tag": "MultiOr", "assoc": assoc, "sort": sort(), "argss": argss });
        let left = decode(multi_or("Left", vec![app("a"), app("b"), app("c")])).unwrap();
        let right = decode(multi_or("Right", vec![app("a"), app("b"), app("c")])).unwrap();
        let one = decode(multi_or("Left", vec![app("a")])).unwrap();

        assert_eq!(
            left,
            parse_pattern(r"\or{S{}}(\or{S{}}(a{}(), b{}()), c{}())").unwrap()
        );
        assert_eq!(
            right,
            parse_pattern(r"\or{S{}}(a{}(), \or{S{}}(b{}(), c{}()))").unwrap()
        );
        assert_eq!(one, parse_pattern("a{}()").unwrap());
        assert_eq!(
            decode(multi_or("Left", Vec::new()))
                .unwrap_err()
                .to_string(),
            "MultiOr requires at least one argument"
        );
        assert!(decode(multi_or("Middle", vec![app("a")])).is_err());
    }

    #[test]
    fn accepted_names_round_trip_through_text() {
        for term in [
            json!({ "tag": "EVar", "name": "X-1'", "sort": sort() }),
            json!({ "tag": "SVar", "name": "@X-1'", "sort": sort() }),
            json!({ "tag": "App", "name": "\\foo", "sorts": [], "args": [] }),
        ] {
            let pattern = decode(term).unwrap();
            assert_eq!(parse_pattern(&pattern.to_string()).unwrap(), pattern);
        }
    }
}
