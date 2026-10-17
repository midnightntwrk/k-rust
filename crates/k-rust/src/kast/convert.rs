//! Conversion from parsed KORE patterns to user-facing K terms.

use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};

use crate::kore::ast::{Pattern, Sort as KoreSort, Symbol, Variable, VariableKind};
use crate::kore::normalize;
use crate::kore::string::LiteralEncoding;
use crate::names::{BuiltinSort, WellKnownSymbol};

use super::ast::{Label, Sort, Term, TermParts};
use super::identifier::{self, DecodeError};
use super::names::{FrontendSort, InternalLabel};
use super::string;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConversionError(pub String);

impl Display for ConversionError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for ConversionError {}

impl From<DecodeError> for ConversionError {
    fn from(error: DecodeError) -> Self {
        Self(error.to_string())
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Converter<'a> {
    sort_hooks: &'a HashMap<String, String>,
}

impl<'a> Converter<'a> {
    pub fn new(sort_hooks: &'a HashMap<String, String>) -> Self {
        Self { sort_hooks }
    }

    pub fn convert(&self, pattern: &Pattern) -> Result<Term, ConversionError> {
        self.pattern(&normalize::for_kast(pattern))
    }

    // stack-accepted(kore-to-kast): one level per pattern level, in a library API that no product path calls. See docs/backend-port.md#stack-bounds.
    fn pattern(&self, pattern: &Pattern) -> Result<Term, ConversionError> {
        match pattern {
            Pattern::Variable(variable) => self.variable(variable),
            Pattern::Application { symbol, arguments } => self.application(symbol, arguments),
            Pattern::Top { sort } => Ok(Term::Apply {
                label: Label::with_parameters(InternalLabel::Top.as_str(), vec![self.sort(sort)?]),
                arguments: Vec::new(),
            }),
            Pattern::Bottom { sort } => Ok(Term::Apply {
                label: Label::with_parameters(
                    InternalLabel::Bottom.as_str(),
                    vec![self.sort(sort)?],
                ),
                arguments: Vec::new(),
            }),
            Pattern::And { sort, arguments } => self.associative(
                InternalLabel::And.as_str(),
                InternalLabel::Top.as_str(),
                sort,
                arguments,
            ),
            Pattern::Or { sort, arguments } => self.associative(
                InternalLabel::Or.as_str(),
                InternalLabel::Bottom.as_str(),
                sort,
                arguments,
            ),
            Pattern::Not { sort, argument } => {
                self.ml(InternalLabel::Not.as_str(), [sort], [argument.as_ref()])
            }
            Pattern::Implies { sort, left, right } => self.ml(
                InternalLabel::Implies.as_str(),
                [sort],
                [left.as_ref(), right.as_ref()],
            ),
            Pattern::Rewrites { left, right, .. } => Ok(Term::Rewrite {
                left: Box::new(self.pattern(left)?),
                right: Box::new(self.pattern(right)?),
            }),
            Pattern::Exists {
                sort,
                variable,
                body,
            } => Ok(Term::Apply {
                label: Label::with_parameters(
                    InternalLabel::Exists.as_str(),
                    vec![self.sort(&variable.sort)?, self.sort(sort)?],
                ),
                arguments: vec![self.variable(variable)?, self.pattern(body)?],
            }),
            Pattern::Forall {
                sort,
                variable,
                body,
            } => Ok(Term::Apply {
                label: Label::with_parameters(
                    InternalLabel::Forall.as_str(),
                    vec![self.sort(&variable.sort)?, self.sort(sort)?],
                ),
                arguments: vec![self.variable(variable)?, self.pattern(body)?],
            }),
            Pattern::Ceil {
                operand_sort,
                result_sort,
                argument,
            } => self.ml(
                InternalLabel::Ceil.as_str(),
                [operand_sort, result_sort],
                [argument.as_ref()],
            ),
            Pattern::Floor {
                operand_sort,
                result_sort,
                argument,
            } => self.ml(
                InternalLabel::Floor.as_str(),
                [operand_sort, result_sort],
                [argument.as_ref()],
            ),
            Pattern::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            } => self.ml(
                InternalLabel::Equals.as_str(),
                [operand_sort, result_sort],
                [left.as_ref(), right.as_ref()],
            ),
            Pattern::DomainValue {
                sort: kore_sort,
                value,
            } => {
                let sort = self.sort(kore_sort)?;
                // The payload holds code points by the encoding of the KORE sort's name
                // (`LiteralEncoding`), and the hook says what they are.
                let encoding = LiteralEncoding::of_domain_value(kore_sort);
                let token = match self.sort_hooks.get(&sort.name).map(String::as_str) {
                    Some("STRING.String") => string::quote(&encoding.code_points(value)),
                    Some("BYTES.Bytes") => {
                        let bytes = match encoding {
                            LiteralEncoding::Bytes => value.as_bytes().to_vec(),
                            LiteralEncoding::Utf8 => encoding
                                .code_points(value)
                                .chars()
                                .map(|character| u8::try_from(u32::from(character)).ok())
                                .collect::<Option<Vec<u8>>>()
                                .ok_or_else(|| {
                                    ConversionError(format!(
                                        "domain value of sort {} holds a code point above U+00FF, which is no byte",
                                        sort.name
                                    ))
                                })?,
                        };
                        format!("b{}", string::quote_bytes(&bytes))
                    }
                    _ => value.as_utf8().map(str::to_owned).map_err(|_| {
                        ConversionError(format!(
                            "domain value of sort {} is not valid UTF-8",
                            sort.name
                        ))
                    })?,
                };
                Ok(Term::Token { token, sort })
            }
            Pattern::String(value) => Ok(Term::Token {
                token: value.as_utf8().map(str::to_owned).map_err(|_| {
                    ConversionError("KORE string pattern is not valid UTF-8".into())
                })?,
                sort: Sort::frontend(FrontendSort::KString),
            }),
            Pattern::Iff { .. } => {
                Err(ConversionError("Iff patterns currently unsupported".into()))
            }
            Pattern::In { .. } => Err(ConversionError("In patterns currently unsupported".into())),
            Pattern::Next { .. } => Err(ConversionError(
                "Next patterns currently unsupported".into(),
            )),
            Pattern::Mu { .. } => Err(ConversionError("Mu patterns currently unsupported".into())),
            Pattern::Nu { .. } => Err(ConversionError("Nu patterns currently unsupported".into())),
            Pattern::AssociativeApplication { .. } => unreachable!("normalization expands these"),
        }
    }

    fn sort(&self, sort: &KoreSort) -> Result<Sort, ConversionError> {
        match sort {
            KoreSort::Variable(_) => Ok(Sort::builtin(BuiltinSort::K)),
            KoreSort::Application { name, arguments } => Ok(Sort::with_parameters(
                identifier::decode_sort_name(name)?,
                arguments
                    .iter()
                    .map(|sort| self.sort(sort))
                    .collect::<Result<_, _>>()?,
            )),
        }
    }

    fn variable(&self, variable: &Variable) -> Result<Term, ConversionError> {
        let (kind, name) = identifier::decode_variable(&variable.name);
        let prefix = match kind {
            VariableKind::Element => "",
            VariableKind::Set => "@",
        };
        Ok(Term::Variable {
            name: format!("{prefix}{}", name?),
            sort: Some(self.sort(&variable.sort)?),
        })
    }

    fn application(&self, symbol: &Symbol, arguments: &[Pattern]) -> Result<Term, ConversionError> {
        match symbol.name.as_str() {
            name if name == WellKnownSymbol::Inj.as_str() => {
                self.pattern(arguments.first().ok_or_else(|| {
                    ConversionError("inj application requires an argument".into())
                })?)
            }
            name if name == WellKnownSymbol::KSeq.as_str()
                || name == WellKnownSymbol::Append.as_str() =>
            {
                Ok(Term::sequence(
                    arguments
                        .iter()
                        .map(|argument| self.pattern(argument))
                        .collect::<Result<Vec<_>, _>>()?,
                ))
            }
            name if name == WellKnownSymbol::DotK.as_str() => Ok(Term::Sequence(Vec::new())),
            _ => Ok(Term::Apply {
                label: Label {
                    name: identifier::decode_label(&symbol.name)?,
                    parameters: symbol
                        .sort_parameters
                        .iter()
                        .map(|sort| self.sort(sort))
                        .collect::<Result<_, _>>()?,
                },
                arguments: arguments
                    .iter()
                    .map(|argument| self.pattern(argument))
                    .collect::<Result<_, _>>()?,
            }),
        }
    }

    fn ml<'b, const S: usize, const P: usize>(
        &self,
        name: &str,
        sorts: [&'b KoreSort; S],
        patterns: [&'b Pattern; P],
    ) -> Result<Term, ConversionError> {
        Ok(Term::Apply {
            label: Label::with_parameters(
                name,
                sorts
                    .into_iter()
                    .map(|sort| self.sort(sort))
                    .collect::<Result<_, _>>()?,
            ),
            arguments: patterns
                .into_iter()
                .map(|pattern| self.pattern(pattern))
                .collect::<Result<_, _>>()?,
        })
    }

    fn associative(
        &self,
        name: &str,
        unit: &str,
        sort: &KoreSort,
        arguments: &[Pattern],
    ) -> Result<Term, ConversionError> {
        let label = Label::with_parameters(name, vec![self.sort(sort)?]);
        let unit = Label::with_parameters(unit, vec![self.sort(sort)?]);
        let mut flattened = Vec::new();
        for argument in arguments {
            let argument = self.pattern(argument)?;
            match argument.into_parts() {
                TermParts::Apply {
                    label: child,
                    arguments,
                } if child == label => {
                    flattened.extend(arguments);
                }
                TermParts::Apply {
                    label: child,
                    arguments,
                } if child == unit && arguments.is_empty() => {}
                argument => flattened.push(Term::from(argument)),
            }
        }
        Ok(Term::Apply {
            label,
            arguments: flattened,
        })
    }
}

/// The sort hooks of a definition as [`Converter::new`] takes them: the KAST name of each hooked
/// sort with its hook, from the KORE name and hook of each sort declaration.
///
/// A domain value's KAST token depends on its sort's hook (a `BYTES.Bytes` payload is a byte
/// string, not text), and only the definition states the hooks. A KORE sort name that does not
/// decode names no sort a converted pattern can have, since the conversion of such a sort fails
/// first, and is left out.
pub fn sort_hooks<'a>(
    kore_sorts: impl IntoIterator<Item = (&'a str, &'a str)>,
) -> HashMap<String, String> {
    kore_sorts
        .into_iter()
        .filter_map(|(name, hook)| {
            Some((identifier::decode_sort_name(name).ok()?, hook.to_owned()))
        })
        .collect()
}

pub fn convert_sort(sort: &KoreSort) -> Result<Sort, ConversionError> {
    Converter::new(&HashMap::new()).sort(sort)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::kore::parser::parse_pattern;

    use super::{Converter, sort_hooks};

    /// The conversion of a pattern that holds no domain value, which needs no sort hook.
    fn convert(
        pattern: &crate::kore::ast::Pattern,
    ) -> Result<crate::kast::Term, super::ConversionError> {
        Converter::new(&HashMap::new()).convert(pattern)
    }

    #[test]
    fn converts_labels_sequences_and_rewrites() {
        let pattern = parse_pattern(
            r"\rewrites{SortK{}}(kseq{}(Lbl'UndsPlus'Int'Unds'{}(), X:SortInt{}), dotk{}())",
        )
        .unwrap();
        assert_eq!(
            convert(&pattern).unwrap().to_string(),
            r"`_+Int_`(.KList)~>X=>.K"
        );
    }

    #[test]
    fn converts_string_domain_values_using_hooks() {
        let pattern = parse_pattern(r#"\dv{SortString{}}("hello")"#).unwrap();
        let hooks = HashMap::from([("String".into(), "STRING.String".into())]);
        let term = Converter::new(&hooks).convert(&pattern).unwrap();
        assert_eq!(term.to_string(), r#"#token("\"hello\"","String")"#);
    }

    /// A Bytes domain value is a byte string, one byte per code point U+0000 to U+00FF, rendered
    /// by its hook whether or not it is valid UTF-8; a String one is quoted. The hooks are read
    /// from KORE sort declarations.
    #[test]
    fn converts_bytes_and_string_domain_values_with_the_definitions_hooks() {
        let hooks = sort_hooks([
            ("SortBytes", "BYTES.Bytes"),
            ("SortString", "STRING.String"),
            ("NotASort", "INT.Int"),
        ]);
        assert_eq!(
            hooks,
            HashMap::from([
                ("Bytes".to_owned(), "BYTES.Bytes".to_owned()),
                ("String".to_owned(), "STRING.String".to_owned()),
            ])
        );
        let converter = Converter::new(&hooks);
        let bytes = parse_pattern(r#"\dv{SortBytes{}}("\x80\xff")"#).unwrap();
        assert_eq!(
            converter.convert(&bytes).unwrap().to_string(),
            r#"#token("b\"\\x80\\xff\"","Bytes")"#
        );
        let string = parse_pattern(r#"\dv{SortString{}}("a")"#).unwrap();
        assert_eq!(
            converter.convert(&string).unwrap().to_string(),
            r#"#token("\"a\"","String")"#
        );
    }

    #[test]
    fn preserves_set_variable_names() {
        let pattern = parse_pattern("@VarX:SortSet{}").unwrap();
        assert_eq!(
            convert(&pattern).unwrap(),
            crate::kast::Term::Variable {
                name: "@X".into(),
                sort: Some(crate::kast::Sort::new("Set")),
            }
        );
    }
}
