//! Alpha-normal form of compiled KORE.
//!
//! A KORE variable is its kind, name and sort, and `\exists`, `\forall`, `\mu` and `\nu` bind
//! exactly their own variable in their body (`k_rust::kore` `Pattern::free_variables`). The
//! normal form of an axiom or claim renames each free variable by its first occurrence in a
//! preorder walk of the pattern and then of the attributes, and each binder by its position in
//! that walk, so two sentences have equal normal forms exactly when they are alpha-equivalent
//! (with the free variables matched in order of occurrence). A canonical name keeps the encoded
//! prefix of the K name it replaces (`Var`, and the sigil and `_` codes such as `'Ques'` or
//! `'Unds'`), since the renamings of the harness keep sigils and `_` prefixes.

use std::collections::BTreeMap;

use k_rust::kore::{
    ast::{Pattern, Sentence, Variable, VariableKind},
    parser::{parse_definition, parse_pattern},
    printer::Printer,
};

/// One sentence of a compiled definition in alpha-normal form.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NormalSentence {
    pub module: String,
    /// A short name for reports: the sentence's `label` or `UNIQUE'Unds'ID` attribute, or its
    /// position.
    pub name: String,
    pub text: String,
    /// An axiom's `UNIQUE'Unds'ID` attribute, kept out of `text`: it is a digest of the
    /// sentence, so it is compared on its own. A claim's is not compared, so it is `None`.
    pub id: Option<String>,
}

/// The encoded sigil and `_` prefix of a KORE variable name: `Var'QuesUnds'` for `?_Gen1`,
/// `Var'Ques'` for `?X`, `Var` for `X`, or the empty prefix for a name the K encoding did not
/// produce.
fn prefix(name: &str) -> &str {
    let Some(rest) = name.strip_prefix("Var") else {
        return "";
    };
    if let Some(quoted) = rest.strip_prefix('\'')
        && let Some(end) = quoted.find('\'')
    {
        let codes = &quoted[..end];
        let mut remaining = codes;
        while !remaining.is_empty() {
            let Some(code) = ["Ques", "Bang", "Unds", "At"]
                .into_iter()
                .find(|code| remaining.starts_with(code))
            else {
                return "Var";
            };
            remaining = &remaining[code.len()..];
        }
        return &name[..3 + 1 + end + 1];
    }
    "Var"
}

struct Normaliser {
    free: BTreeMap<Variable, String>,
    binders: usize,
}

impl Normaliser {
    fn canonical(&mut self, variable: &Variable, scope: &[(Variable, String)]) -> Variable {
        let name = if let Some((_, name)) = scope.iter().rev().find(|(bound, _)| bound == variable)
        {
            name.clone()
        } else {
            let next = self.free.len();
            self.free
                .entry(variable.clone())
                .or_insert_with(|| format!("{}F{next}", prefix(&variable.name)))
                .clone()
        };
        Variable {
            kind: variable.kind,
            name,
            sort: variable.sort.clone(),
        }
    }

    fn bind(&mut self, variable: &Variable) -> String {
        self.binders += 1;
        let kind = if variable.kind == VariableKind::Set {
            "S"
        } else {
            "B"
        };
        format!("{}{kind}{}", prefix(&variable.name), self.binders)
    }

    fn pattern(&mut self, pattern: &Pattern, scope: &mut Vec<(Variable, String)>) -> Pattern {
        let list = |this: &mut Self, arguments: &[Pattern], scope: &mut Vec<_>| {
            arguments
                .iter()
                .map(|argument| this.pattern(argument, scope))
                .collect::<Vec<_>>()
        };
        let boxed = |this: &mut Self, argument: &Pattern, scope: &mut Vec<_>| {
            Box::new(this.pattern(argument, scope))
        };
        match pattern {
            Pattern::Variable(variable) => Pattern::Variable(self.canonical(variable, scope)),
            Pattern::String(_)
            | Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::DomainValue { .. } => pattern.clone(),
            Pattern::Application { symbol, arguments } => Pattern::Application {
                symbol: symbol.clone(),
                arguments: list(self, arguments, scope),
            },
            Pattern::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } => Pattern::AssociativeApplication {
                associativity: *associativity,
                symbol: symbol.clone(),
                arguments: list(self, arguments, scope),
            },
            Pattern::And { sort, arguments } => Pattern::And {
                sort: sort.clone(),
                arguments: list(self, arguments, scope),
            },
            Pattern::Or { sort, arguments } => Pattern::Or {
                sort: sort.clone(),
                arguments: list(self, arguments, scope),
            },
            Pattern::Not { sort, argument } => Pattern::Not {
                sort: sort.clone(),
                argument: boxed(self, argument, scope),
            },
            Pattern::Next { sort, argument } => Pattern::Next {
                sort: sort.clone(),
                argument: boxed(self, argument, scope),
            },
            Pattern::Implies { sort, left, right } => Pattern::Implies {
                sort: sort.clone(),
                left: boxed(self, left, scope),
                right: boxed(self, right, scope),
            },
            Pattern::Iff { sort, left, right } => Pattern::Iff {
                sort: sort.clone(),
                left: boxed(self, left, scope),
                right: boxed(self, right, scope),
            },
            Pattern::Rewrites { sort, left, right } => Pattern::Rewrites {
                sort: sort.clone(),
                left: boxed(self, left, scope),
                right: boxed(self, right, scope),
            },
            Pattern::Ceil {
                operand_sort,
                result_sort,
                argument,
            } => Pattern::Ceil {
                operand_sort: operand_sort.clone(),
                result_sort: result_sort.clone(),
                argument: boxed(self, argument, scope),
            },
            Pattern::Floor {
                operand_sort,
                result_sort,
                argument,
            } => Pattern::Floor {
                operand_sort: operand_sort.clone(),
                result_sort: result_sort.clone(),
                argument: boxed(self, argument, scope),
            },
            Pattern::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            } => Pattern::Equals {
                operand_sort: operand_sort.clone(),
                result_sort: result_sort.clone(),
                left: boxed(self, left, scope),
                right: boxed(self, right, scope),
            },
            Pattern::In {
                operand_sort,
                result_sort,
                left,
                right,
            } => Pattern::In {
                operand_sort: operand_sort.clone(),
                result_sort: result_sort.clone(),
                left: boxed(self, left, scope),
                right: boxed(self, right, scope),
            },
            Pattern::Exists {
                sort,
                variable,
                body,
            }
            | Pattern::Forall {
                sort,
                variable,
                body,
            } => {
                let name = self.bind(variable);
                let bound = Variable {
                    kind: variable.kind,
                    name: name.clone(),
                    sort: variable.sort.clone(),
                };
                scope.push(((**variable).clone(), name));
                let body = boxed(self, body, scope);
                scope.pop();
                if matches!(pattern, Pattern::Exists { .. }) {
                    Pattern::Exists {
                        sort: sort.clone(),
                        variable: Box::new(bound),
                        body,
                    }
                } else {
                    Pattern::Forall {
                        sort: sort.clone(),
                        variable: Box::new(bound),
                        body,
                    }
                }
            }
            Pattern::Mu { variable, body } | Pattern::Nu { variable, body } => {
                let name = self.bind(variable);
                let bound = Variable {
                    kind: variable.kind,
                    name: name.clone(),
                    sort: variable.sort.clone(),
                };
                scope.push(((**variable).clone(), name));
                let body = boxed(self, body, scope);
                scope.pop();
                if matches!(pattern, Pattern::Mu { .. }) {
                    Pattern::Mu {
                        variable: Box::new(bound),
                        body,
                    }
                } else {
                    Pattern::Nu {
                        variable: Box::new(bound),
                        body,
                    }
                }
            }
        }
    }
}

/// The alpha-normal form of one pattern (a result state), printed compactly.
pub fn normal_pattern(pattern: &Pattern) -> String {
    let mut normaliser = Normaliser {
        free: BTreeMap::new(),
        binders: 0,
    };
    Printer::compact().print_pattern(&normaliser.pattern(pattern, &mut Vec::new()))
}

fn string_attribute(attributes: &[Pattern], wanted: &str) -> Option<String> {
    attributes.iter().find_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments } if symbol.name == wanted => {
            match arguments.first() {
                Some(Pattern::String(value)) => Some(value.as_utf8().unwrap_or("?").to_owned()),
                _ => None,
            }
        }
        _ => None,
    })
}

/// A sentence's name for reports and signatures: its `label`; else its source file's name and
/// start position (`domains.md:1088:3`), which no compiler change moves; else its
/// `UNIQUE'Unds'ID`.
fn attribute_name(attributes: &[Pattern]) -> Option<String> {
    if let Some(label) = string_attribute(attributes, "label") {
        return Some(label);
    }
    let location = string_attribute(
        attributes,
        "org'Stop'kframework'Stop'attributes'Stop'Location",
    );
    let source = string_attribute(
        attributes,
        "org'Stop'kframework'Stop'attributes'Stop'Source",
    );
    if let (Some(location), Some(source)) = (location, source) {
        let file = source
            .trim_start_matches("Source(")
            .trim_end_matches(')')
            .rsplit('/')
            .next()
            .unwrap_or_default()
            .to_owned();
        let position = location
            .trim_start_matches("Location(")
            .trim_end_matches(')')
            .split(',')
            .take(2)
            .collect::<Vec<_>>()
            .join(":");
        return Some(format!("{file}:{position}"));
    }
    string_attribute(attributes, "UNIQUE'Unds'ID")
}

fn unique_id(attribute: &Pattern) -> Option<String> {
    match attribute {
        Pattern::Application { symbol, arguments } if symbol.name == "UNIQUE'Unds'ID" => {
            match arguments.first() {
                Some(Pattern::String(value)) => Some(value.as_utf8().unwrap_or("?").to_owned()),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The prefix of the symbols the compiler mints for a `#fun` or `#let`: their names carry the
/// spelling of a variable argument as a hint (`#lambdaLETARG__`), so a renaming renames them.
const LAMBDA: &str = "Lbl'Hash'lambda";

/// Rename every minted lambda symbol of `sentences` by its first occurrence: the symbols are
/// fresh names, so a consistent renaming of them keeps the definition, and two symbols merged
/// into one (or one split into two) still show.
fn normalise_lambdas(sentences: &mut [NormalSentence]) {
    let mut names = BTreeMap::<String, String>::new();
    for sentence in sentences {
        let mut out = String::with_capacity(sentence.text.len());
        let mut rest = sentence.text.as_str();
        while let Some(at) = rest.find(LAMBDA) {
            out.push_str(&rest[..at]);
            let tail = &rest[at..];
            let end = tail.find(['{', '(', ' ', ',', ')']).unwrap_or(tail.len());
            let next = names.len();
            out.push_str(
                names
                    .entry(tail[..end].to_owned())
                    .or_insert_with(|| format!("{LAMBDA}#{next}")),
            );
            rest = &tail[end..];
        }
        out.push_str(rest);
        sentence.text = out;
    }
}

/// Every sentence of the definition `kore` in alpha-normal form, in order.
pub fn normal_definition(kore: &str) -> Result<Vec<NormalSentence>, String> {
    let definition = parse_definition(kore).map_err(|error| error.to_string())?;
    let mut sentences = Vec::new();
    for module in &definition.modules {
        for (index, sentence) in module.sentences.iter().enumerate() {
            let normal = match sentence {
                Sentence::Axiom {
                    parameters,
                    pattern,
                    attributes,
                }
                | Sentence::Claim {
                    parameters,
                    pattern,
                    attributes,
                } => {
                    let mut normaliser = Normaliser {
                        free: BTreeMap::new(),
                        binders: 0,
                    };
                    let pattern = Box::new(normaliser.pattern(pattern, &mut Vec::new()));
                    let attributes = k_rust::kore::ast::Attributes(
                        attributes
                            .0
                            .iter()
                            .filter(|attribute| unique_id(attribute).is_none())
                            .map(|attribute| normaliser.pattern(attribute, &mut Vec::new()))
                            .collect(),
                    );
                    if matches!(sentence, Sentence::Axiom { .. }) {
                        Sentence::Axiom {
                            parameters: parameters.clone(),
                            pattern,
                            attributes,
                        }
                    } else {
                        Sentence::Claim {
                            parameters: parameters.clone(),
                            pattern,
                            attributes,
                        }
                    }
                }
                other => other.clone(),
            };
            let name = match sentence {
                Sentence::Axiom { attributes, .. } | Sentence::Claim { attributes, .. } => {
                    attribute_name(&attributes.0)
                }
                _ => None,
            }
            .unwrap_or_else(|| format!("#{index}"));
            // A claim's `UNIQUE_ID` is kept spelling-based (FU-44): an identifier only has to
            // tell a claim apart within its definition, so two alpha-equivalent claims with
            // distinct identifiers give the same answers. Only an axiom's is compared.
            let id = match sentence {
                Sentence::Axiom { attributes, .. } => attributes.0.iter().find_map(unique_id),
                _ => None,
            };
            sentences.push(NormalSentence {
                module: module.name.clone(),
                name,
                text: Printer::compact().print_sentence(&normal),
                id,
            });
        }
    }
    normalise_lambdas(&mut sentences);
    Ok(sentences)
}

/// The first difference between two normal forms, as a report line, or `None` when they are
/// equal.
pub fn first_difference(base: &[NormalSentence], variant: &[NormalSentence]) -> Option<String> {
    for (index, (left, right)) in base.iter().zip(variant).enumerate() {
        if left.text != right.text {
            let common = left
                .text
                .char_indices()
                .zip(right.text.chars())
                .find(|((_, a), b)| a != b)
                .map_or(left.text.len().min(right.text.len()), |((at, _), _)| at);
            let window = |text: &str| {
                let start = text[..common.min(text.len())]
                    .char_indices()
                    .rev()
                    .nth(160)
                    .map_or(0, |(at, _)| at);
                let shown: String = text[start..].chars().take(480).collect();
                format!("{}{shown}", if start > 0 { "..." } else { "" })
            };
            return Some(format!(
                "sentence {index} ({}.{}) differs:\n    base:    {}\n    variant: {}",
                left.module,
                left.name,
                window(&left.text),
                window(&right.text)
            ));
        }
    }
    if base.len() != variant.len() {
        return Some(format!(
            "the base has {} sentences and the variant {}",
            base.len(),
            variant.len()
        ));
    }
    None
}

/// The distinguishing text of the first difference between two normal forms: the differing
/// sentence's module and name, and the text of each side from 24 characters before the first
/// differing character, 64 characters long; or the difference in the number of sentences. It
/// names no sentence position, so a change elsewhere in the definition (the prelude) keeps it.
pub fn difference_signature(base: &[NormalSentence], variant: &[NormalSentence]) -> Option<String> {
    for (left, right) in base.iter().zip(variant) {
        if left.text != right.text {
            let at = left
                .text
                .char_indices()
                .zip(right.text.chars())
                .find(|((_, a), b)| a != b)
                .map_or(left.text.len().min(right.text.len()), |((at, _), _)| at);
            let window = |text: &str| -> String {
                let start = text[..at.min(text.len())]
                    .char_indices()
                    .rev()
                    .nth(23)
                    .map_or(0, |(start, _)| start);
                text[start..].chars().take(64).collect()
            };
            return Some(format!(
                "{}.{}: base «{}» variant «{}»",
                left.module,
                left.name,
                window(&left.text),
                window(&right.text)
            ));
        }
    }
    (base.len() != variant.len()).then(|| {
        format!(
            "the variant has {} more sentences than the base",
            variant.len() as i64 - base.len() as i64
        )
    })
}

/// The distinguishing text of the first `UNIQUE'Unds'ID` difference: the sentence's module and
/// name.
pub fn id_signature(base: &[NormalSentence], variant: &[NormalSentence]) -> Option<String> {
    base.iter()
        .zip(variant)
        .find(|(left, right)| left.id != right.id)
        .map(|(left, _)| {
            format!(
                "{}.{}: UNIQUE_ID not alpha-invariant",
                left.module, left.name
            )
        })
}

/// The first sentence whose `UNIQUE'Unds'ID` differs between two normal forms whose texts are
/// equal, as a report line.
pub fn first_id_difference(base: &[NormalSentence], variant: &[NormalSentence]) -> Option<String> {
    base.iter().zip(variant).enumerate().find(|(_, (left, right))| left.id != right.id).map(
        |(index, (left, right))| {
            format!(
                "sentence {index} ({}.{}) is alpha-equivalent, and its UNIQUE_ID differs: base {}, variant {}",
                left.module,
                left.name,
                left.id.as_deref().unwrap_or("none"),
                right.id.as_deref().unwrap_or("none")
            )
        },
    )
}

#[test]
fn alpha_equivalent_axioms_have_one_normal_form_and_others_do_not() {
    let normal = |text: &str| normal_pattern(&parse_pattern(text).unwrap());
    let sort = "SortInt{}";
    let forall = |binder: &str, body: &str| format!("\\forall{{{sort}}}({binder}:{sort}, {body})");
    let neq = |left: &str, right: &str| format!("Lblneq{{}}({left}:{sort}, {right}:{sort})");
    // Renaming a bound variable, and the free ones consistently, keeps the normal form.
    assert_eq!(
        normal(&forall("VarY", &neq("VarX", "VarY"))),
        normal(&forall("VarZ", &neq("VarW", "VarZ")))
    );
    // A binder that captures the free variable is a different pattern.
    assert_ne!(
        normal(&forall("VarY", &neq("VarX", "VarY"))),
        normal(&forall("VarY", &neq("VarY", "VarY")))
    );
    // A vacuous binder is not the binder of its body's variable.
    assert_ne!(
        normal(&forall("VarY", &neq("VarX", "VarY"))),
        normal(&forall("VarY", &neq("VarX", "VarZ")))
    );
    // A sigil is kept: `?X` and `X` are not interchangeable.
    assert_ne!(
        normal(&neq("Var'Ques'X", "VarY")),
        normal(&neq("VarX", "VarY"))
    );
    assert_eq!(prefix("Var'QuesUnds'Gen1"), "Var'QuesUnds'");
    assert_eq!(prefix("Var'Unds'Gen1"), "Var'Unds'");
    assert_eq!(prefix("VarX'Unds'Y"), "Var");
    assert_eq!(prefix("X0"), "");
}
