//! Resolution of rule-like bubbles with K's implicit rule syntax.

use std::collections::BTreeSet;
use std::fmt;

use crate::definition::{
    Attributes, Definition, Location, ModuleId, ProductionItem, ResolveError, ResolvedDefinition,
    Sentence,
};
use crate::kast::{Label, Sort, Term};

use super::config::{add_casts, add_k_syntax, add_subsort, nonterminal, truth};
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
            Self::Parse(error) => {
                match (&error.source, error.location) {
                    (Some(source), Some(location)) => write!(
                        formatter,
                        "{source}:{}:{}: ",
                        location.start_line, location.start_column
                    )?,
                    (Some(source), None) => write!(formatter, "{source}: ")?,
                    _ => {}
                }
                write!(
                    formatter,
                    "could not parse {} in module {:?}: {}",
                    error.sentence_type, error.module, error.error
                )
            }
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
            let is_anywhere = [
                "anywhere",
                "simplification",
                "macro",
                "macro-rec",
                "alias",
                "alias-rec",
            ]
            .iter()
            .any(|key| attributes.get(key).is_some());
            let parsed = grammar
                .parse_with_context(&Sort::new("#RuleContent"), contents, is_anywhere)
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
    let Term::Apply { label, arguments } = parsed.into_unannotated() else {
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
    let concrete_sorts = concrete_sorts(&visible);
    let mut parsing_sentences = visible
        .iter()
        .filter(|sentence| {
            !matches!(
                sentence,
                Sentence::Production { attributes, .. } if attributes.get("cell").is_some()
            )
        })
        .map(|sentence| (*sentence).clone())
        .collect::<Vec<_>>();
    parsing_sentences.extend(concrete_sorts.iter().filter_map(|sort| {
        let predicate = format!("is{sort}");
        (!visible.iter().any(|sentence| {
            matches!(sentence, Sentence::Production { label: Some(label), .. } if label.name == predicate)
        }))
        .then(|| sort_predicate_production(sort))
    }));
    if !parsing_sentences
        .iter()
        .any(|sentence| matches!(sentence, Sentence::SyntaxSort { sort, .. } if sort.name == "Bag"))
    {
        parsing_sentences.push(Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new("Bag"),
            attributes: Attributes::default(),
        });
    }
    #[cfg(feature = "z3-inference")]
    add_builtin_rule_sentences(&mut parsing_sentences);
    let source_catalog = resolved.production_catalog(module);
    // The reference rule grammar imports DEFAULT-LAYOUT explicitly, independently
    // of the layout used to parse programs in the language being compiled.
    let mut grammar = Grammar::from_rule_sentences(parsing_sentences.iter(), &source_catalog)?;
    let bracket_sorts = visible
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                sort, attributes, ..
            } if attributes.get("bracket").is_some() => Some(sort.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let klabel_terminals = visible
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                items,
                ..
            } if items.iter().any(
                |item| matches!(item, ProductionItem::Terminal(value) if value == &label.name),
            ) =>
            {
                Some(label.name.clone())
            }
            _ => None,
        })
        .collect::<BTreeSet<_>>();

    add_k_syntax(&mut grammar)?;
    add_rule_k_syntax(
        &mut grammar,
        &concrete_sorts,
        &bracket_sorts,
        &klabel_terminals,
    )?;
    add_rule_cells(&mut grammar, &visible)?;
    #[cfg(not(feature = "z3-inference"))]
    add_rule_sort(&mut grammar, &Sort::new("Bag"))?;

    for sort in concrete_sorts {
        #[cfg(not(feature = "z3-inference"))]
        add_rule_sort(&mut grammar, &sort)?;
        if sort.name != "Bool" {
            add_subsort(&mut grammar, "KItem", sort.clone())?;
            grammar.add(sort.clone(), vec![nonterminal("KBott")], None, false, true)?;
            add_casts(&mut grammar, Sort::new("K"), sort.clone(), sort.clone())?;
        }
    }

    Ok(grammar)
}

fn sort_predicate_production(sort: &Sort) -> Sentence {
    let label = Label::new(format!("is{sort}"));
    let mut attributes = Attributes::default();
    attributes.insert("function", serde_json::json!(""));
    attributes.insert("total", serde_json::json!(""));
    attributes.insert("generatedRuleSyntax", serde_json::json!(""));
    Sentence::Production {
        label: Some(label.clone()),
        parameters: Vec::new(),
        sort: Sort::new("Bool"),
        items: vec![
            ProductionItem::Terminal(label.name),
            ProductionItem::Terminal("(".into()),
            ProductionItem::NonTerminal {
                sort: Sort::new("K"),
                name: None,
            },
            ProductionItem::Terminal(")".into()),
        ],
        attributes,
    }
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
    bracket_sorts: &BTreeSet<Sort>,
    klabel_terminals: &BTreeSet<String>,
) -> Result<(), ParseError> {
    add_subsort(grammar, "KBott", Sort::new("#KVariable"))?;
    add_subsort(grammar, "KBott", Sort::new("KConfigVar"))?;
    add_subsort(grammar, "KItem", Sort::new("KBott"))?;
    grammar.add(
        Sort::new("KLabel"),
        vec![ProductionItem::regex(
            r"`(?:\\`|\\\\|[^`\\\n\r])+`|[a-z][a-zA-Z0-9]*|#[a-z][a-zA-Z0-9]*",
        )],
        None,
        true,
        false,
    )?;
    for label in klabel_terminals {
        grammar.add(
            Sort::new("KLabel"),
            vec![ProductionItem::Terminal(label.clone())],
            None,
            true,
            false,
        )?;
    }
    grammar.add(
        Sort::new("KList"),
        vec![nonterminal("K")],
        None,
        false,
        true,
    )?;
    grammar.add(
        Sort::new("KList"),
        vec![ProductionItem::Terminal(".KList".into())],
        Some(Label::new("#EmptyKList")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("KList"),
        vec![
            nonterminal("KList"),
            ProductionItem::Terminal(",".into()),
            nonterminal("KList"),
        ],
        Some(Label::new("#KList")),
        false,
        false,
    )?;
    grammar.add_left_associative("#KList");
    grammar.add(
        Sort::new("KString"),
        vec![ProductionItem::regex(
            r#"[\"](([^\"\n\r\\])|([\\][nrtf\"\\])|([\\][x][0-9a-fA-F]{2})|([\\][u][0-9a-fA-F]{4})|([\\][U][0-9a-fA-F]{8}))*[\"]"#,
        )],
        None,
        true,
        false,
    )?;
    grammar.add(
        Sort::new("KBott"),
        vec![
            ProductionItem::Terminal("#token".into()),
            ProductionItem::Terminal("(".into()),
            nonterminal("KString"),
            ProductionItem::Terminal(",".into()),
            nonterminal("KString"),
            ProductionItem::Terminal(")".into()),
        ],
        Some(Label::new("#KToken")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("KBott"),
        vec![
            ProductionItem::Terminal("#klabel".into()),
            ProductionItem::Terminal("(".into()),
            nonterminal("KLabel"),
            ProductionItem::Terminal(")".into()),
        ],
        Some(Label::new("#WrappedKLabel")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("KBott"),
        vec![
            nonterminal("KLabel"),
            ProductionItem::Terminal("(".into()),
            nonterminal("KList"),
            ProductionItem::Terminal(")".into()),
        ],
        Some(Label::new("#KApply")),
        false,
        false,
    )?;
    // `K` is intentionally absent from `concrete_sorts`, but rule bodies still need a concrete
    // bracket production. Relying only on KSEQ's parametric bracket leaves a parenthesized
    // polymorphic rewrite unable to complete before a cell's trailing `...`.
    grammar.add_bracket(
        Sort::new("K"),
        vec![
            ProductionItem::Terminal("(".into()),
            nonterminal("K"),
            ProductionItem::Terminal(")".into()),
        ],
    )?;
    // `KItem` is also excluded from `concrete_sorts`. Materialize KAST's
    // parametric bracket for it so a parenthesized lookup can inhabit a
    // collection operation's KItem-valued field.
    grammar.add_bracket(
        Sort::new("KItem"),
        vec![
            ProductionItem::Terminal("(".into()),
            nonterminal("KItem"),
            ProductionItem::Terminal(")".into()),
        ],
    )?;
    // Collection cells use parenthesized Bag rewrites immediately before their
    // trailing cell dots. Keep a parse-only concrete bracket for the same reason
    // as K above: the imported polymorphic bracket cannot always complete the
    // rewrite at this boundary.
    grammar.add_bracket(
        Sort::new("Bag"),
        vec![
            ProductionItem::Terminal("(".into()),
            nonterminal("Bag"),
            ProductionItem::Terminal(")".into()),
        ],
    )?;
    for sort in [Sort::new("Bag"), Sort::new("Cell")] {
        add_casts(grammar, Sort::new("K"), sort.clone(), sort)?;
    }
    #[cfg(not(feature = "z3-inference"))]
    add_rule_sort(grammar, &Sort::new("K"))?;
    let rule_body_sort = rule_sort(&Sort::new("K"));
    grammar.add(
        Sort::new("#RuleBody"),
        vec![ProductionItem::NonTerminal {
            sort: rule_body_sort.clone(),
            name: None,
        }],
        None,
        false,
        true,
    )?;
    for sort in concrete_sorts {
        if bracket_sorts.contains(sort) {
            continue;
        }
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
            ProductionItem::Terminal("[".into()),
            ProductionItem::Terminal("[".into()),
            ProductionItem::NonTerminal {
                sort: rule_body_sort,
                name: None,
            },
            ProductionItem::Terminal("]".into()),
            ProductionItem::Terminal("]".into()),
            nonterminal("Bag"),
        ],
        Some(Label::new("#withConfig")),
        false,
        false,
    )
}

#[cfg(not(feature = "z3-inference"))]
fn add_rule_sort(grammar: &mut Grammar, sort: &Sort) -> Result<(), ParseError> {
    let result = rule_sort(sort);
    let child = ProductionItem::NonTerminal {
        sort: sort.clone(),
        name: None,
    };
    grammar.add(result.clone(), vec![child.clone()], None, false, true)?;
    grammar.add(
        result.clone(),
        vec![
            child.clone(),
            ProductionItem::Terminal("=>".into()),
            child.clone(),
        ],
        Some(Label::new("#KRewrite")),
        false,
        false,
    )?;
    grammar.add(
        result,
        vec![
            child,
            ProductionItem::Terminal("#as".into()),
            nonterminal("#KVariable"),
        ],
        Some(Label::new("#KAs")),
        false,
        false,
    )
}

#[cfg(not(feature = "z3-inference"))]
fn rule_sort(sort: &Sort) -> Sort {
    Sort::new(format!("#Rule{}", sort.name))
}

#[cfg(feature = "z3-inference")]
fn rule_sort(sort: &Sort) -> Sort {
    sort.clone()
}

#[cfg(feature = "z3-inference")]
fn add_builtin_rule_sentences(sentences: &mut Vec<Sentence>) {
    let labels = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.name.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let has_label = |name: &str| labels.contains(name);
    let has_rewrite = has_label("#KRewrite");
    let has_as = has_label("#KAs");
    let parameter = Sort::new("Sort");
    let mut generated_attributes = Attributes::default();
    generated_attributes.insert("generatedRuleSyntax", serde_json::Value::Null);
    if !has_rewrite {
        sentences.push(Sentence::Production {
            label: Some(Label::with_parameters("#KRewrite", vec![parameter.clone()])),
            parameters: vec![parameter.clone()],
            sort: parameter.clone(),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal("=>".into()),
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
            ],
            attributes: generated_attributes.clone(),
        });
    }
    if !has_as {
        sentences.push(Sentence::Production {
            label: Some(Label::with_parameters("#KAs", vec![parameter.clone()])),
            parameters: vec![parameter.clone()],
            sort: parameter.clone(),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal("#as".into()),
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
            ],
            attributes: generated_attributes.clone(),
        });
    }
    if !has_label("#fun2") {
        let mut attributes = generated_attributes.clone();
        attributes.insert("prefer", serde_json::Value::String(String::new()));
        sentences.push(Sentence::Production {
            label: Some(Label::with_parameters("#fun2", vec![parameter.clone()])),
            parameters: vec![parameter.clone()],
            sort: parameter.clone(),
            items: vec![
                ProductionItem::Terminal("#fun".into()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            attributes,
        });
    }
    let result_parameter = Sort::new("Sort1");
    let argument_parameter = Sort::new("Sort2");
    if !has_label("#fun3") {
        sentences.push(Sentence::Production {
            label: Some(Label::with_parameters(
                "#fun3",
                vec![result_parameter.clone(), argument_parameter.clone()],
            )),
            parameters: vec![result_parameter.clone(), argument_parameter.clone()],
            sort: result_parameter.clone(),
            items: vec![
                ProductionItem::Terminal("#fun".into()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: argument_parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal("=>".into()),
                ProductionItem::NonTerminal {
                    sort: result_parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: argument_parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            attributes: generated_attributes.clone(),
        });
    }
    if !has_label("#let") {
        sentences.push(Sentence::Production {
            label: Some(Label::with_parameters(
                "#let",
                vec![result_parameter.clone(), argument_parameter.clone()],
            )),
            parameters: vec![result_parameter.clone(), argument_parameter.clone()],
            sort: result_parameter,
            items: vec![
                ProductionItem::Terminal("#let".into()),
                ProductionItem::NonTerminal {
                    sort: argument_parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal("=".into()),
                ProductionItem::NonTerminal {
                    sort: argument_parameter,
                    name: None,
                },
                ProductionItem::Terminal("#in".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("Sort1"),
                    name: None,
                },
            ],
            attributes: generated_attributes.clone(),
        });
    }
    for (label, terminal) in [("_:=K_", ":=K"), ("_:/=K_", ":/=K")] {
        if has_label(label) {
            continue;
        }
        let mut attributes = generated_attributes.clone();
        attributes.insert("function", serde_json::Value::String(String::new()));
        attributes.insert("total", serde_json::Value::String(String::new()));
        sentences.push(Sentence::Production {
            label: Some(Label::new(label)),
            parameters: Vec::new(),
            sort: Sort::new("Bool"),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: Sort::new("K"),
                    name: None,
                },
                ProductionItem::Terminal(terminal.into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("K"),
                    name: None,
                },
            ],
            attributes,
        });
    }
    if !sentences.iter().any(|sentence| {
        matches!(sentence, Sentence::SyntaxAssociativity { tags, .. } if tags.iter().any(|tag| tag == "#KRewrite"))
    }) {
        sentences.push(Sentence::SyntaxAssociativity {
            associativity: crate::definition::Associativity::NonAssoc,
            tags: vec!["#KRewrite".into()],
            attributes: Attributes::default(),
        });
    }
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
                    _ => ProductionItem::NonTerminal {
                        sort: rule_sort(&Sort::new("Bag")),
                        name: None,
                    },
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
