//! Conversion from parsed KORE patterns to user-facing K terms.

use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};

use crate::kore::ast::{Pattern, Sort as KoreSort, Symbol, Variable};
use crate::kore::normalize;

use super::ast::{Label, Sort, Term};
use super::string;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConversionError(pub String);

impl Display for ConversionError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for ConversionError {}

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

    fn pattern(&self, pattern: &Pattern) -> Result<Term, ConversionError> {
        match pattern {
            Pattern::Variable(variable) => self.variable(variable),
            Pattern::Application { symbol, arguments } => self.application(symbol, arguments),
            Pattern::Top { sort } => Ok(Term::Apply {
                label: Label::with_parameters("#Top", vec![self.sort(sort)?]),
                arguments: Vec::new(),
            }),
            Pattern::Bottom { sort } => Ok(Term::Apply {
                label: Label::with_parameters("#Bottom", vec![self.sort(sort)?]),
                arguments: Vec::new(),
            }),
            Pattern::And { sort, arguments } => self.associative("#And", "#Top", sort, arguments),
            Pattern::Or { sort, arguments } => self.associative("#Or", "#Bottom", sort, arguments),
            Pattern::Not { sort, argument } => self.ml("#Not", [sort], [argument.as_ref()]),
            Pattern::Implies { sort, left, right } => {
                self.ml("#Implies", [sort], [left.as_ref(), right.as_ref()])
            }
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
                    "#Exists",
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
                    "#Forall",
                    vec![self.sort(&variable.sort)?, self.sort(sort)?],
                ),
                arguments: vec![self.variable(variable)?, self.pattern(body)?],
            }),
            Pattern::Ceil {
                operand_sort,
                result_sort,
                argument,
            } => self.ml("#Ceil", [operand_sort, result_sort], [argument.as_ref()]),
            Pattern::Floor {
                operand_sort,
                result_sort,
                argument,
            } => self.ml("#Floor", [operand_sort, result_sort], [argument.as_ref()]),
            Pattern::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            } => self.ml(
                "#Equals",
                [operand_sort, result_sort],
                [left.as_ref(), right.as_ref()],
            ),
            Pattern::DomainValue { sort, value } => {
                let sort = self.sort(sort)?;
                let token = match self.sort_hooks.get(&sort.name).map(String::as_str) {
                    Some("STRING.String") => string::quote(value),
                    Some("BYTES.Bytes") => format!("b{}", string::quote(value)),
                    _ => value.clone(),
                };
                Ok(Term::Token { token, sort })
            }
            Pattern::String(value) => Ok(Term::Token {
                token: value.clone(),
                sort: Sort::new("KString"),
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
            KoreSort::Variable(_) => Ok(Sort::new("K")),
            KoreSort::Application { name, arguments } => {
                let name = name.strip_prefix("Sort").ok_or_else(|| {
                    ConversionError(format!("compound KORE sort {name:?} lacks Sort prefix"))
                })?;
                Ok(Sort::with_parameters(
                    name,
                    arguments
                        .iter()
                        .map(|sort| self.sort(sort))
                        .collect::<Result<_, _>>()?,
                ))
            }
        }
    }

    fn variable(&self, variable: &Variable) -> Result<Term, ConversionError> {
        let (prefix, name) = variable
            .name
            .strip_prefix('@')
            .map_or(("", variable.name.as_str()), |name| ("@", name));
        let encoded = name.strip_prefix("Var").unwrap_or(name);
        Ok(Term::Variable {
            name: format!("{prefix}{}", decode_identifier(encoded)?),
            sort: Some(self.sort(&variable.sort)?),
        })
    }

    fn application(&self, symbol: &Symbol, arguments: &[Pattern]) -> Result<Term, ConversionError> {
        match symbol.name.as_str() {
            "inj" => {
                self.pattern(arguments.first().ok_or_else(|| {
                    ConversionError("inj application requires an argument".into())
                })?)
            }
            "kseq" | "append" => Ok(Term::sequence(
                arguments
                    .iter()
                    .map(|argument| self.pattern(argument))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            "dotk" => Ok(Term::Sequence(Vec::new())),
            _ => Ok(Term::Apply {
                label: Label {
                    name: decode_label(&symbol.name)?,
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
            match argument {
                Term::Apply {
                    label: child,
                    arguments,
                } if child == label => {
                    flattened.extend(arguments);
                }
                Term::Apply {
                    label: child,
                    arguments,
                } if child == unit && arguments.is_empty() => {}
                argument => flattened.push(argument),
            }
        }
        Ok(Term::Apply {
            label,
            arguments: flattened,
        })
    }
}

pub fn convert(pattern: &Pattern) -> Result<Term, ConversionError> {
    Converter::new(&HashMap::new()).convert(pattern)
}

pub fn convert_sort(sort: &KoreSort) -> Result<Sort, ConversionError> {
    Converter::new(&HashMap::new()).sort(sort)
}

fn decode_label(name: &str) -> Result<String, ConversionError> {
    decode_identifier(name.strip_prefix("Lbl").unwrap_or(name))
}

fn decode_identifier(encoded: &str) -> Result<String, ConversionError> {
    let mut output = String::new();
    let mut literal = true;
    let mut offset = 0;
    while offset < encoded.len() {
        let character = encoded[offset..].chars().next().unwrap();
        if character == '\'' {
            literal = !literal;
            offset += 1;
        } else if literal {
            output.push(character);
            offset += character.len_utf8();
        } else {
            let end = offset + 4;
            let code = encoded.get(offset..end).ok_or_else(|| {
                ConversionError(format!("truncated encoded identifier {encoded:?}"))
            })?;
            if u16::from_str_radix(code, 16).is_ok() {
                output.push_str("\\u");
                output.push_str(code);
            } else {
                output.push_str(decode_code(code).ok_or_else(|| {
                    ConversionError(format!("unknown KORE identifier code {code:?}"))
                })?);
            }
            offset = end;
        }
    }
    if literal {
        Ok(output)
    } else {
        Err(ConversionError(format!(
            "unterminated encoded identifier {encoded:?}"
        )))
    }
}

fn decode_code(code: &str) -> Option<&'static str> {
    Some(match code {
        "Spce" => " ",
        "Bang" => "!",
        "Quot" => "\"",
        "Hash" => "#",
        "Dolr" => "$",
        "Perc" => "%",
        "And-" => "&",
        "Apos" => "'",
        "LPar" => "(",
        "RPar" => ")",
        "Star" => "*",
        "Plus" => "+",
        "Comm" => ",",
        "Stop" => ".",
        "Slsh" => "/",
        "Coln" => ":",
        "SCln" => ";",
        "-LT-" => "<",
        "Eqls" => "=",
        "-GT-" => ">",
        "Ques" => "?",
        "-AT-" => "@",
        "LSqB" => "[",
        "RSqB" => "]",
        "Bash" => "\\",
        "Xor-" => "^",
        "Unds" => "_",
        "BQuo" => "`",
        "LBra" => "{",
        "Pipe" => "|",
        "RBra" => "}",
        "Tild" => "~",
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::kore::parser::parse_pattern;

    use super::{Converter, convert};

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
