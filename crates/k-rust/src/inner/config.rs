//! Resolution of configuration bubbles with K's implicit configuration syntax.

use std::fmt;

use crate::definition::{
    Attributes, Definition, Location, ModuleId, ProductionItem, ResolveError, ResolvedDefinition,
    Sentence, sentence_equivalent,
};
use crate::kast::{Label, Sort, Term};
use crate::provenance::SourceId;

use super::parser::{Grammar, ParseError};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConfigError {
    Definition(ResolveError),
    Parse {
        module: String,
        source: Option<String>,
        location: Option<Location>,
        error: Box<ParseError>,
    },
    IllegalRequires {
        module: String,
        source: Option<String>,
        location: Option<Location>,
    },
}

impl fmt::Display for ConfigError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Definition(error) => error.fmt(formatter),
            Self::Parse { module, error, .. } => {
                write!(
                    formatter,
                    "could not parse configuration in module {module:?}: {error}"
                )
            }
            Self::IllegalRequires { module, .. } => write!(
                formatter,
                "configuration in module {module:?} cannot contain a requires clause"
            ),
        }
    }
}

impl std::error::Error for ConfigError {}

/// Replace local `config` bubbles with structured configuration sentences.
///
/// This corresponds to the parsing half of Java's `resolveConfigBubbles`.
/// Generating cell productions and initializer rules remains a subsequent
/// compilation pass.
pub fn resolve_configuration_bubbles(definition: &Definition) -> Result<Definition, ConfigError> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(ConfigError::Definition)?;
    let mut transformed = definition.clone();

    for module in &mut transformed.modules {
        if !module.local_sentences.iter().any(is_configuration_bubble) {
            continue;
        }
        let module_id = resolved
            .module_id(&module.name)
            .expect("every flat module was added to the resolved definition");
        let grammar =
            configuration_grammar(&resolved, module_id).map_err(|error| ConfigError::Parse {
                module: module.name.clone(),
                source: module.attributes.source().map(str::to_owned),
                location: module.attributes.location(),
                error: Box::new(error),
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
            if sentence_type != "config" {
                continue;
            }
            let parsed = grammar
                .parse_with_provenance(
                    &Sort::new("#RuleContent"),
                    contents,
                    attributes.source_id().unwrap_or(SourceId(0)),
                    content_start_offset(attributes),
                )
                .map_err(|error| bubble_error(&module.name, attributes, error))?;
            *sentence = up_configuration(&module.name, parsed, attributes.clone())?;
        }
    }

    Ok(transformed)
}

fn content_start_offset(attributes: &Attributes) -> usize {
    attributes
        .get("contentStartOffset")
        .and_then(serde_json::Value::as_u64)
        .and_then(|offset| usize::try_from(offset).ok())
        .unwrap_or(0)
}

fn is_configuration_bubble(sentence: &Sentence) -> bool {
    matches!(
        sentence,
        Sentence::Bubble { sentence_type, .. } if sentence_type == "config"
    )
}

fn bubble_error(module: &str, attributes: &Attributes, error: ParseError) -> ConfigError {
    ConfigError::Parse {
        module: module.to_owned(),
        source: attributes.source().map(str::to_owned),
        location: attributes.location(),
        error: Box::new(error),
    }
}

fn up_configuration(
    module: &str,
    parsed: Term,
    attributes: Attributes,
) -> Result<Sentence, ConfigError> {
    let Term::Apply { label, arguments } = parsed.into_unannotated() else {
        return Err(bubble_error(
            module,
            &attributes,
            ParseError::NoParse {
                position: 0,
                expected: vec!["#RuleContent".into()],
            },
        ));
    };
    match (label.name.as_str(), arguments.as_slice()) {
        ("#ruleNoConditions", [body]) => Ok(Sentence::Configuration {
            body: body.clone(),
            ensures: truth(),
            attributes,
        }),
        ("#ruleEnsures", [body, ensures]) => Ok(Sentence::Configuration {
            body: body.clone(),
            ensures: ensures.clone(),
            attributes,
        }),
        ("#ruleRequires" | "#ruleRequiresEnsures", _) => Err(ConfigError::IllegalRequires {
            module: module.to_owned(),
            source: attributes.source().map(str::to_owned),
            location: attributes.location(),
        }),
        _ => Err(bubble_error(
            module,
            &attributes,
            ParseError::NoParse {
                position: 0,
                expected: vec!["configuration body".into()],
            },
        )),
    }
}

fn configuration_grammar(
    resolved: &ResolvedDefinition,
    module: ModuleId,
) -> Result<Grammar, ParseError> {
    let mut visible = resolved.signature_sentences(module);
    add_implicit_ml_syntax(resolved, &mut visible);
    // The reference configuration grammar imports DEFAULT-LAYOUT explicitly,
    // even when the language declares a program-specific `#Layout` sort.
    let mut grammar = Grammar::from_configuration_sentences(visible.iter().copied())?;
    let mut concrete_sorts = visible
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
        .collect::<std::collections::BTreeSet<_>>();

    add_config_cells(&mut grammar)?;
    grammar.add_matching_terminal_tokens(Sort::new("#CellName"), is_cell_name)?;
    add_k_syntax(&mut grammar, BuiltinTokenGrammar::Configuration)?;

    // K is implicit in configuration grammar seeds, including KSEQ brackets.
    // Keep concrete seeds so their inferred types match the rest of this grammar.
    let default_bracket = implicit_kseq_bracket(resolved);
    for sort in
        concrete_sorts
            .iter()
            .cloned()
            .chain([Sort::new("K"), Sort::new("KItem"), Sort::new("Bag")])
    {
        if sort.name.starts_with('#') {
            continue;
        }
        grammar.add_bracket(
            sort.clone(),
            vec![
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal { sort, name: None },
                ProductionItem::Terminal(")".into()),
            ],
            default_bracket,
        )?;
    }

    concrete_sorts.retain(|sort| {
        !matches!(
            sort.name.as_str(),
            "K" | "KItem" | "KBott" | "KConfigVar" | "Cell" | "Bag" | "#RuleBody" | "#RuleContent"
        ) && !sort.name.starts_with('#')
    });
    for sort in concrete_sorts {
        if sort.name != "Bool" {
            add_subsort(&mut grammar, "KItem", sort.clone())?;
            add_subsort(&mut grammar, sort.name.as_str(), Sort::new("KConfigVar"))?;
            add_subsort(&mut grammar, sort.name.as_str(), Sort::new("#KVariable"))?;
            add_casts(&mut grammar, Sort::new("K"), sort.clone(), sort)?;
        }
    }
    add_synonym_casts(&mut grammar, &visible)?;

    Ok(grammar)
}

pub(super) fn implicit_kseq_bracket(resolved: &ResolvedDefinition) -> Option<&Attributes> {
    let kseq = resolved.module_id("KSEQ")?;
    resolved
        .module(kseq)
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Production { attributes, .. } if attributes.get("bracket").is_some() => {
                Some(attributes)
            }
            _ => None,
        })
}

/// The reference rule and configuration grammar seed imports `K`, whose
/// `KSEQ-SYMBOLIC` import contributes `ML-SYNTAX` independently of the user
/// module signature. The hand-built seed models the rest of that syntax.
pub(super) fn add_implicit_ml_syntax<'a>(
    resolved: &'a ResolvedDefinition,
    visible: &mut Vec<&'a Sentence>,
) {
    let Some(module) = resolved.module_id("ML-SYNTAX") else {
        return;
    };
    for sentence in resolved.signature_sentences(module) {
        if !visible
            .iter()
            .any(|existing| sentence_equivalent(existing, sentence))
        {
            visible.push(sentence);
        }
    }
}

fn is_cell_name(value: &str) -> bool {
    let mut characters = value.chars();
    characters
        .next()
        .is_some_and(|character| character.is_ascii_alphabetic())
        && characters.all(|character| character.is_ascii_alphanumeric() || character == '-')
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum BuiltinTokenGrammar {
    Rule,
    Configuration,
}

const BUILTIN_LEXEMES: [(&str, &str, &str); 7] = [
    ("#LowerId", r"[a-z][a-zA-Z0-9]*", "2"),
    ("#UpperId", r"[A-Z][a-zA-Z0-9]*", "2"),
    (
        "KString",
        r#"[\"](([^\"\n\r\\])|([\\][nrtf\"\\])|([\\][x][0-9a-fA-F]{2})|([\\][u][0-9a-fA-F]{4})|([\\][U][0-9a-fA-F]{8}))*[\"]"#,
        "0",
    ),
    ("KLabel", r"`(\\`|\\\\|[^`\\\n\r])+`", "0"),
    ("KLabel", r"[#a-z][a-zA-Z0-9]*", "1"),
    (
        "#KVariable",
        r"(\!|\?|@)?([A-Z][A-Za-z0-9'_]*|_|_[A-Z][A-Za-z0-9'_]*)",
        "1",
    ),
    ("KConfigVar", r"(\$)([A-Z][A-Za-z0-9'_]*)", "0"),
];

/// Lexemes and token subsorts imported from `kast.md` by every rule grammar.
pub(super) fn add_builtin_tokens(
    grammar: &mut Grammar,
    which: BuiltinTokenGrammar,
) -> Result<(), ParseError> {
    for (sort, regex, precedence) in BUILTIN_LEXEMES {
        grammar.add_token_with_precedence(
            Sort::new(sort),
            ProductionItem::regex(regex),
            precedence,
        )?;
    }
    grammar.add_token_subsort("KLabel", "#LowerId")?;
    grammar.add_token_subsort("#KVariable", "#UpperId")?;
    if which == BuiltinTokenGrammar::Configuration {
        grammar.add_token_with_precedence(
            Sort::new("#CellName"),
            ProductionItem::regex(r"[a-zA-Z][a-zA-Z0-9\-]*"),
            "1",
        )?;
        grammar.add_token_subsort("#CellName", "#LowerId")?;
        grammar.add_token_subsort("#CellName", "#UpperId")?;
    }
    Ok(())
}

pub(super) fn add_k_syntax(
    grammar: &mut Grammar,
    which: BuiltinTokenGrammar,
) -> Result<(), ParseError> {
    add_builtin_tokens(grammar, which)?;
    add_subsort(grammar, "K", Sort::new("KItem"))?;
    add_subsort(grammar, "KItem", Sort::new("Bag"))?;
    add_subsort(grammar, "KItem", Sort::new("Bool"))?;
    add_subsort(grammar, "KItem", Sort::new("KConfigVar"))?;
    add_subsort(grammar, "KItem", Sort::new("#KVariable"))?;
    add_subsort(grammar, "#RuleBody", Sort::new("K"))?;

    grammar.add(
        Sort::new("K"),
        vec![ProductionItem::Terminal(".K".into())],
        Some(Label::new("#EmptyK")),
        false,
        false,
    )?;
    // KSEQ retains `.` as a deprecated spelling of the empty K sequence. It is
    // deliberately parse-only in the reference frontend (`unparseAvoid`), so
    // both spellings lower to the same KAST node and printers continue to emit
    // the canonical `.K` form.
    grammar.add(
        Sort::new("K"),
        vec![ProductionItem::Terminal(".".into())],
        Some(Label::new("#EmptyK")),
        false,
        false,
    )?;
    // Configuration initializers and rule bodies share the same concrete K-sequence syntax.
    // Keep it here so rule grammar construction does not install a duplicate production.
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
    // KSEQ declares left associativity; adding the opposite edge would make
    // a visible KSEQ declaration prohibit both associations.
    grammar.add_left_associative("#KSequence");
    grammar.add(
        Sort::new("Bag"),
        vec![ProductionItem::Terminal(".Bag".into())],
        Some(Label::new("#cells")),
        false,
        false,
    )?;
    add_casts(grammar, Sort::new("K"), Sort::new("Bag"), Sort::new("Bag"))?;
    add_casts(grammar, Sort::new("K"), Sort::new("K"), Sort::new("K"))?;
    add_casts(
        grammar,
        Sort::new("K"),
        Sort::new("KItem"),
        Sort::new("KItem"),
    )?;
    add_casts(
        grammar,
        Sort::new("KLabel"),
        Sort::new("KLabel"),
        Sort::new("KLabel"),
    )?;
    add_casts(
        grammar,
        Sort::new("KList"),
        Sort::new("KList"),
        Sort::new("KList"),
    )?;
    for value in ["true", "false"] {
        grammar.add(
            Sort::new("Bool"),
            vec![ProductionItem::Terminal(value.into())],
            None,
            true,
            false,
        )?;
    }
    add_subsort(grammar, "Bool", Sort::new("#KVariable"))?;
    add_subsort(grammar, "Bool", Sort::new("KConfigVar"))?;
    add_casts(
        grammar,
        Sort::new("K"),
        Sort::new("Bool"),
        Sort::new("Bool"),
    )?;
    grammar.add(
        Sort::new("#RuleContent"),
        vec![nonterminal("#RuleBody")],
        Some(Label::new("#ruleNoConditions")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("#RuleContent"),
        vec![
            nonterminal("#RuleBody"),
            ProductionItem::Terminal("requires".into()),
            nonterminal("Bool"),
        ],
        Some(Label::new("#ruleRequires")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("#RuleContent"),
        vec![
            nonterminal("#RuleBody"),
            ProductionItem::Terminal("ensures".into()),
            nonterminal("Bool"),
        ],
        Some(Label::new("#ruleEnsures")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("#RuleContent"),
        vec![
            nonterminal("#RuleBody"),
            ProductionItem::Terminal("requires".into()),
            nonterminal("Bool"),
            ProductionItem::Terminal("ensures".into()),
            nonterminal("Bool"),
        ],
        Some(Label::new("#ruleRequiresEnsures")),
        false,
        false,
    )
}

fn add_config_cells(grammar: &mut Grammar) -> Result<(), ParseError> {
    grammar.add(
        Sort::new("#CellProperty"),
        vec![
            nonterminal("#CellName"),
            ProductionItem::Terminal("=".into()),
            nonterminal("KString"),
        ],
        Some(Label::new("#cellProperty")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("#CellProperties"),
        vec![nonterminal("#CellProperty"), nonterminal("#CellProperties")],
        Some(Label::new("#cellPropertyList")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("#CellProperties"),
        Vec::new(),
        Some(Label::new("#cellPropertyListTerminator")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("Cell"),
        vec![
            ProductionItem::Terminal("<".into()),
            nonterminal("#CellName"),
            nonterminal("#CellProperties"),
            ProductionItem::Terminal(">".into()),
            nonterminal("K"),
            ProductionItem::Terminal("</".into()),
            nonterminal("#CellName"),
            ProductionItem::Terminal(">".into()),
        ],
        Some(Label::new("#configCell")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("Cell"),
        vec![
            ProductionItem::Terminal("<".into()),
            nonterminal("#CellName"),
            ProductionItem::Terminal("/>".into()),
        ],
        Some(Label::new("#externalCell")),
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
    add_subsort(grammar, "Bag", Sort::new("Cell"))
}

pub(super) fn add_subsort(
    grammar: &mut Grammar,
    result: &str,
    child: Sort,
) -> Result<(), ParseError> {
    grammar.add(
        Sort::new(result),
        vec![ProductionItem::NonTerminal {
            sort: child,
            name: None,
        }],
        None,
        false,
        true,
    )
}

/// RuleGrammarGenerator adds casts for visible synonyms separately from concrete sorts.
/// Keep the alias in the source spelling and the target in semantic cast labels and operands.
pub(super) fn add_synonym_casts(
    grammar: &mut Grammar,
    visible: &[&Sentence],
) -> Result<(), ParseError> {
    for sentence in visible {
        if let Sentence::SortSynonym {
            new_sort, old_sort, ..
        } = sentence
        {
            add_casts(grammar, Sort::new("K"), new_sort.clone(), old_sort.clone())?;
        }
    }
    Ok(())
}

pub(super) fn add_casts(
    grammar: &mut Grammar,
    inner_sort: Sort,
    cast_sort: Sort,
    label_sort: Sort,
) -> Result<(), ParseError> {
    grammar.add(
        cast_sort.clone(),
        vec![
            ProductionItem::NonTerminal {
                sort: label_sort.clone(),
                name: None,
            },
            ProductionItem::Terminal(format!("::{cast_sort}")),
        ],
        Some(Label::new("#SyntacticCast")),
        false,
        false,
    )?;
    grammar.add(
        cast_sort.clone(),
        vec![
            ProductionItem::Terminal("{".into()),
            ProductionItem::NonTerminal {
                sort: label_sort.clone(),
                name: None,
            },
            ProductionItem::Terminal("}".into()),
            ProductionItem::Terminal(format!("::{cast_sort}")),
        ],
        Some(Label::new("#SyntacticCastBraced")),
        false,
        false,
    )?;
    let semantic_cast_items = vec![
        ProductionItem::NonTerminal {
            sort: label_sort.clone(),
            name: None,
        },
        ProductionItem::Terminal(format!(":{cast_sort}")),
    ];
    if label_sort == Sort::new("K") && cast_sort == Sort::new("K") {
        grammar.add_with_source_text(
            label_sort.clone(),
            semantic_cast_items,
            Some(Label::new("#SemanticCastToK")),
            false,
            false,
            "syntax K ::= K \":K\" [format(%1%2), org.kframework.kore.Sort(K)]",
        )?;
    } else {
        grammar.add(
            label_sort.clone(),
            semantic_cast_items,
            Some(Label::new(format!("#SemanticCastTo{label_sort}"))),
            false,
            false,
        )?;
    }
    grammar.add(
        label_sort,
        vec![
            ProductionItem::Terminal("{".into()),
            ProductionItem::NonTerminal {
                sort: inner_sort,
                name: None,
            },
            ProductionItem::Terminal("}".into()),
            ProductionItem::Terminal(format!(":>{cast_sort}")),
        ],
        Some(Label::new("#OuterCast")),
        false,
        false,
    )
}

pub(super) fn nonterminal(sort: &str) -> ProductionItem {
    ProductionItem::NonTerminal {
        sort: Sort::new(sort),
        name: None,
    }
}

pub(super) fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn regex(regex: &str) -> String {
        format!("r{regex:?}")
    }

    #[test]
    fn scanner_winner_table_matches_scanner_get_tokens() {
        for precedence in 0..=3 {
            let mut grammar = Grammar::default();
            add_k_syntax(&mut grammar, BuiltinTokenGrammar::Rule).unwrap();
            grammar
                .add_token_with_precedence(
                    Sort::new("Id"),
                    ProductionItem::regex(r"[A-Za-z_][A-Za-z_0-9]*"),
                    &precedence.to_string(),
                )
                .unwrap();

            let user_id = r"[A-Za-z_][A-Za-z_0-9]*";
            assert_eq!(
                grammar.scanner().winner_description("foo"),
                Some(regex(if precedence < 2 {
                    r"[a-z][a-zA-Z0-9]*"
                } else {
                    user_id
                }))
            );
            assert_eq!(
                grammar.scanner().winner_description("Foo"),
                Some(regex(if precedence < 3 {
                    r"[A-Z][a-zA-Z0-9]*"
                } else {
                    user_id
                }))
            );
            assert_eq!(
                grammar.scanner().winner_description("foo_bar"),
                Some(regex(user_id))
            );
            assert_eq!(
                grammar.scanner().winner_description("X'"),
                Some(regex(
                    r"(\!|\?|@)?([A-Z][A-Za-z0-9'_]*|_|_[A-Z][A-Za-z0-9'_]*)"
                ))
            );
            assert_eq!(
                grammar.scanner().winner_description("`foo`"),
                Some(regex(r"`(\\`|\\\\|[^`\\\n\r])+`"))
            );
            assert_eq!(
                grammar.scanner().winner_description("#foo"),
                Some(regex(r"[#a-z][a-zA-Z0-9]*"))
            );
            assert_eq!(
                grammar.scanner().winner_description("$PGM"),
                Some(regex(r"(\$)([A-Z][A-Za-z0-9'_]*)"))
            );
            assert_eq!(
                grammar.scanner().winner_description("_"),
                Some(regex(if precedence < 2 {
                    r"(\!|\?|@)?([A-Z][A-Za-z0-9'_]*|_|_[A-Z][A-Za-z0-9'_]*)"
                } else {
                    user_id
                }))
            );
        }
    }

    #[test]
    fn builtin_lexemes_declared_by_the_definition_are_not_registered_twice() {
        let mut attributes = Attributes::default();
        attributes.insert("token", serde_json::json!(""));
        attributes.insert("prec", serde_json::json!("2"));
        let sentences = [Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new("#UpperId"),
            items: vec![ProductionItem::regex(r"[A-Z][a-zA-Z0-9]*")],
            attributes,
        }];
        let mut grammar = Grammar::from_sentences(&sentences).unwrap();

        add_k_syntax(&mut grammar, BuiltinTokenGrammar::Rule).unwrap();

        assert_eq!(
            grammar.equivalent_production_count(
                &Sort::new("#UpperId"),
                &[ProductionItem::regex(r"[A-Z][a-zA-Z0-9]*")],
                true,
            ),
            1
        );
    }

    #[test]
    fn builtin_lexemes_declared_with_another_precedence_are_rejected() {
        let mut attributes = Attributes::default();
        attributes.insert("token", serde_json::json!(""));
        attributes.insert("prec", serde_json::json!("1"));
        let sentences = [Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new("#UpperId"),
            items: vec![ProductionItem::regex(r"[A-Z][a-zA-Z0-9]*")],
            attributes,
        }];
        let mut grammar = Grammar::from_sentences(&sentences).unwrap();

        assert!(matches!(
            add_builtin_tokens(&mut grammar, BuiltinTokenGrammar::Rule),
            Err(ParseError::InconsistentTokenPrecedence { .. })
        ));
    }
}
