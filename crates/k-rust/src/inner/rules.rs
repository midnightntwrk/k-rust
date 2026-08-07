//! Resolution of rule-like bubbles with K's implicit rule syntax.

use std::collections::BTreeSet;
use std::fmt;

use crate::definition::{
    Attributes, Definition, Location, ModuleId, ProductionItem, ResolveError, ResolvedDefinition,
    Sentence,
};
use crate::kast::{Label, Sort, Term};

use super::config::{add_k_syntax, add_semantic_cast, add_subsort, nonterminal, truth};
use super::parser::{Grammar, ParseError};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RuleError {
    Definition(ResolveError),
    Parse(Box<RuleParseError>),
    IllegalEnsures {
        module: String,
        sentence_type: String,
        source: Option<String>,
        location: Option<Location>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuleParseError {
    pub module: String,
    pub sentence_type: String,
    pub source: Option<String>,
    pub location: Option<Location>,
    pub error: ParseError,
}

impl fmt::Display for RuleError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Definition(error) => error.fmt(formatter),
            Self::Parse(error) => write!(
                formatter,
                "could not parse {} in module {:?}: {}",
                error.sentence_type, error.module, error.error
            ),
            Self::IllegalEnsures {
                module,
                sentence_type,
                ..
            } => write!(
                formatter,
                "{sentence_type} in module {module:?} cannot contain an ensures clause"
            ),
        }
    }
}

impl std::error::Error for RuleError {}

/// Replace local rule, claim, context, and context-alias bubbles with KAST sentences.
///
/// This is the syntax-only first slice of Java's non-configuration bubble
/// resolution. Priority and associativity filter the concrete parse forest;
/// inputs that remain genuinely ambiguous are reported explicitly.
pub fn resolve_rule_bubbles(definition: &Definition) -> Result<Definition, RuleError> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(RuleError::Definition)?;
    let mut transformed = definition.clone();

    for module in &mut transformed.modules {
        if !module.local_sentences.iter().any(is_rule_bubble) {
            continue;
        }
        let module_id = resolved
            .module_id(&module.name)
            .expect("every flat module was added to the resolved definition");
        let grammar = rule_grammar(&resolved, module_id).map_err(|error| {
            RuleError::Parse(Box::new(RuleParseError {
                module: module.name.clone(),
                sentence_type: "rule-like sentence".into(),
                source: module.attributes.source().map(str::to_owned),
                location: module.attributes.location(),
                error,
            }))
        })?;

        for sentence in &mut module.local_sentences {
            let Sentence::Bubble {
                sentence_type,
                contents,
                attributes,
            } = sentence
            else {
                continue;
            };
            if !is_rule_sentence_type(sentence_type) {
                continue;
            }
            let parsed = grammar
                .parse(&Sort::new("#RuleContent"), contents)
                .map_err(|error| bubble_error(&module.name, sentence_type, attributes, error))?;
            *sentence = up_sentence(&module.name, sentence_type, parsed, attributes.clone())?;
        }
    }

    Ok(transformed)
}

fn is_rule_bubble(sentence: &Sentence) -> bool {
    matches!(
        sentence,
        Sentence::Bubble { sentence_type, .. } if is_rule_sentence_type(sentence_type)
    )
}

fn is_rule_sentence_type(sentence_type: &str) -> bool {
    matches!(sentence_type, "rule" | "claim" | "context" | "alias")
}

fn bubble_error(
    module: &str,
    sentence_type: &str,
    attributes: &Attributes,
    error: ParseError,
) -> RuleError {
    RuleError::Parse(Box::new(RuleParseError {
        module: module.to_owned(),
        sentence_type: sentence_type.to_owned(),
        source: attributes.source().map(str::to_owned),
        location: attributes.location(),
        error,
    }))
}

fn up_sentence(
    module: &str,
    sentence_type: &str,
    parsed: Term,
    attributes: Attributes,
) -> Result<Sentence, RuleError> {
    let Term::Apply { label, arguments } = parsed else {
        return Err(bubble_error(
            module,
            sentence_type,
            &attributes,
            ParseError::NoParse {
                position: 0,
                expected: vec!["#RuleContent".into()],
            },
        ));
    };
    let (body, requires, ensures) = match (label.name.as_str(), arguments.as_slice()) {
        ("#ruleNoConditions", [body]) => (body.clone(), truth(), truth()),
        ("#ruleRequires", [body, requires]) => (body.clone(), requires.clone(), truth()),
        ("#ruleEnsures", [body, ensures]) => (body.clone(), truth(), ensures.clone()),
        ("#ruleRequiresEnsures", [body, requires, ensures]) => {
            (body.clone(), requires.clone(), ensures.clone())
        }
        _ => {
            return Err(bubble_error(
                module,
                sentence_type,
                &attributes,
                ParseError::NoParse {
                    position: 0,
                    expected: vec!["rule content".into()],
                },
            ));
        }
    };

    match sentence_type {
        "rule" => Ok(Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        }),
        "claim" => Ok(Sentence::Claim {
            body,
            requires,
            ensures,
            attributes,
        }),
        "context" | "alias" => {
            if label.name == "#ruleEnsures" || label.name == "#ruleRequiresEnsures" {
                return Err(RuleError::IllegalEnsures {
                    module: module.to_owned(),
                    sentence_type: sentence_type.to_owned(),
                    source: attributes.source().map(str::to_owned),
                    location: attributes.location(),
                });
            }
            if sentence_type == "context" {
                Ok(Sentence::Context {
                    body,
                    requires,
                    attributes,
                })
            } else {
                Ok(Sentence::ContextAlias {
                    body,
                    requires,
                    attributes,
                })
            }
        }
        _ => unreachable!("callers filter sentence types"),
    }
}

fn rule_grammar(resolved: &ResolvedDefinition, module: ModuleId) -> Result<Grammar, ParseError> {
    let visible = resolved.sentences(module);
    let parsing_sentences = visible
        .iter()
        .filter(|sentence| {
            !matches!(
                sentence,
                Sentence::Production { attributes, .. } if attributes.get("cell").is_some()
            )
        })
        .map(|sentence| (*sentence).clone())
        .collect::<Vec<_>>();
    let mut grammar = Grammar::from_sentences(parsing_sentences.iter())?;
    let concrete_sorts = concrete_sorts(&visible);

    add_k_syntax(&mut grammar)?;
    add_rule_k_syntax(&mut grammar, &concrete_sorts)?;
    add_rule_cells(&mut grammar, &visible)?;

    for sort in concrete_sorts {
        add_subsort(&mut grammar, "KItem", sort.clone())?;
        grammar.add(sort.clone(), vec![nonterminal("KBott")], None, false, true)?;
        add_semantic_cast(&mut grammar, sort.clone())?;
        add_rule_sort(&mut grammar, &sort)?;
    }

    Ok(grammar)
}

fn concrete_sorts(sentences: &[&Sentence]) -> BTreeSet<Sort> {
    sentences
        .iter()
        .flat_map(|sentence| match sentence {
            Sentence::Production { sort, items, .. } => std::iter::once(sort.clone())
                .chain(items.iter().filter_map(|item| match item {
                    ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                    _ => None,
                }))
                .collect::<Vec<_>>(),
            Sentence::SyntaxSort { sort, .. } => vec![sort.clone()],
            _ => Vec::new(),
        })
        .filter(|sort| {
            sort.parameters.is_empty()
                && !sort.name.starts_with('#')
                && !matches!(
                    sort.name.as_str(),
                    "K" | "KItem" | "KBott" | "KConfigVar" | "Cell" | "Bag"
                )
        })
        .collect()
}

fn add_rule_k_syntax(
    grammar: &mut Grammar,
    concrete_sorts: &BTreeSet<Sort>,
) -> Result<(), ParseError> {
    add_subsort(grammar, "KBott", Sort::new("#KVariable"))?;
    add_subsort(grammar, "KBott", Sort::new("KConfigVar"))?;
    add_subsort(grammar, "KItem", Sort::new("KBott"))?;
    grammar.add(
        Sort::new("K"),
        vec![
            nonterminal("K"),
            ProductionItem::Terminal("~>".into()),
            nonterminal("K"),
        ],
        Some(Label::new("#KSequence")),
        false,
        false,
    )?;
    add_rule_sort(grammar, &Sort::new("K"))?;
    grammar.add(
        Sort::new("#RuleBody"),
        vec![ProductionItem::NonTerminal {
            sort: rule_sort(&Sort::new("K")),
            name: None,
        }],
        None,
        false,
        true,
    )?;
    for sort in concrete_sorts {
        grammar.add_bracket(
            sort.clone(),
            vec![
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: sort.clone(),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
        )?;
    }
    grammar.add(
        Sort::new("#RuleBody"),
        vec![
            ProductionItem::Terminal("[[".into()),
            ProductionItem::NonTerminal {
                sort: rule_sort(&Sort::new("K")),
                name: None,
            },
            ProductionItem::Terminal("]]".into()),
            nonterminal("Bag"),
        ],
        Some(Label::new("#withConfig")),
        false,
        false,
    )
}

fn add_rule_sort(grammar: &mut Grammar, sort: &Sort) -> Result<(), ParseError> {
    let result = rule_sort(sort);
    let child = ProductionItem::NonTerminal {
        sort: sort.clone(),
        name: None,
    };
    grammar.add(result.clone(), vec![child.clone()], None, false, true)?;
    grammar.add(
        result,
        vec![child.clone(), ProductionItem::Terminal("=>".into()), child],
        Some(Label::new("#KRewrite")),
        false,
        false,
    )?;
    grammar.add(
        rule_sort(sort),
        vec![
            ProductionItem::NonTerminal {
                sort: sort.clone(),
                name: None,
            },
            ProductionItem::Terminal("#as".into()),
            nonterminal("#KVariable"),
        ],
        Some(Label::new("#KAs")),
        false,
        false,
    )
}

fn rule_sort(sort: &Sort) -> Sort {
    Sort::new(format!("#Rule{}", sort.name))
}

fn add_rule_cells(grammar: &mut Grammar, sentences: &[&Sentence]) -> Result<(), ParseError> {
    grammar.add(
        Sort::new("#OptionalDots"),
        vec![ProductionItem::Terminal("...".into())],
        Some(Label::new("#dots")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("#OptionalDots"),
        Vec::new(),
        Some(Label::new("#noDots")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("Bag"),
        vec![nonterminal("Cell"), nonterminal("Bag")],
        Some(Label::new("#cells")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("Bag"),
        vec![nonterminal("Cell")],
        None,
        false,
        true,
    )?;

    let cell_sorts = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                sort, attributes, ..
            } if attributes.get("cell").is_some() => Some(sort.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let collection_sorts = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::SyntaxSort {
                sort, attributes, ..
            } if attributes.get("cellCollection").is_some() => Some(sort.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();

    for sentence in sentences {
        match sentence {
            Sentence::Production {
                label,
                sort,
                items,
                attributes,
                ..
            } if attributes.get("cell").is_some() => {
                let (Some(label), Some(first), Some(last)) =
                    (label.clone(), items.first().cloned(), items.last().cloned())
                else {
                    continue;
                };
                let middle = &items[1..items.len().saturating_sub(1)];
                let body = match middle {
                    [ProductionItem::NonTerminal { sort, .. }]
                        if !cell_sorts.contains(sort) && !collection_sorts.contains(sort) =>
                    {
                        ProductionItem::NonTerminal {
                            sort: rule_sort(sort),
                            name: None,
                        }
                    }
                    _ => nonterminal("Bag"),
                };
                grammar.add(
                    sort.clone(),
                    vec![
                        first,
                        nonterminal("#OptionalDots"),
                        body,
                        nonterminal("#OptionalDots"),
                        last,
                    ],
                    Some(label),
                    false,
                    false,
                )?;
                grammar.add(
                    Sort::new("Cell"),
                    vec![ProductionItem::NonTerminal {
                        sort: sort.clone(),
                        name: None,
                    }],
                    None,
                    false,
                    true,
                )?;
            }
            Sentence::Production {
                sort, attributes, ..
            } if attributes.get("cellFragment").is_some() => {
                grammar.add(
                    Sort::new("Cell"),
                    vec![ProductionItem::NonTerminal {
                        sort: sort.clone(),
                        name: None,
                    }],
                    None,
                    false,
                    true,
                )?;
            }
            _ => {}
        }
    }
    Ok(())
}
