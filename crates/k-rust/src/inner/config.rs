//! Resolution of configuration bubbles with K's implicit configuration syntax.

use std::fmt;

use crate::definition::{
    Attributes, Definition, Location, ModuleId, ProductionItem, ResolveError, ResolvedDefinition,
    Sentence,
};
use crate::kast::{Label, Sort, Term};

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
                .parse(&Sort::new("#RuleContent"), contents)
                .map_err(|error| bubble_error(&module.name, attributes, error))?;
            *sentence = up_configuration(&module.name, parsed, attributes.clone())?;
        }
    }

    Ok(transformed)
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
    let Term::Apply { label, arguments } = parsed else {
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
    let visible = resolved.sentences(module);
    let mut grammar = Grammar::from_sentences(visible.iter().copied())?;
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
    add_k_syntax(&mut grammar)?;

    concrete_sorts.retain(|sort| {
        !matches!(
            sort.name.as_str(),
            "K" | "KItem" | "KBott" | "Cell" | "Bag" | "#RuleBody" | "#RuleContent"
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

    Ok(grammar)
}

pub(super) fn add_k_syntax(grammar: &mut Grammar) -> Result<(), ParseError> {
    add_subsort(grammar, "K", Sort::new("KItem"))?;
    add_subsort(grammar, "KItem", Sort::new("Bag"))?;
    add_subsort(grammar, "KItem", Sort::new("Bool"))?;
    add_subsort(grammar, "KItem", Sort::new("KConfigVar"))?;
    add_subsort(grammar, "KItem", Sort::new("#KVariable"))?;
    add_subsort(grammar, "#RuleBody", Sort::new("K"))?;

    grammar.add(
        Sort::new("KConfigVar"),
        vec![ProductionItem::regex(r"\$[A-Z][A-Za-z0-9'_]*")],
        None,
        true,
        false,
    )?;
    grammar.add(
        Sort::new("#KVariable"),
        vec![ProductionItem::regex(
            r"(?:!|\?|@)?(?:[A-Z][A-Za-z0-9'_]*|_|_[A-Z][A-Za-z0-9'_]*)",
        )],
        None,
        true,
        false,
    )?;
    grammar.add(
        Sort::new("K"),
        vec![ProductionItem::Terminal(".K".into())],
        Some(Label::new("#EmptyK")),
        false,
        false,
    )?;
    grammar.add(
        Sort::new("Bag"),
        vec![ProductionItem::Terminal(".Bag".into())],
        Some(Label::new("#cells")),
        false,
        false,
    )?;
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
        Sort::new("#CellName"),
        vec![ProductionItem::regex(r"[a-zA-Z][a-zA-Z0-9\-]*")],
        None,
        true,
        false,
    )?;
    grammar.add(
        Sort::new("KString"),
        vec![ProductionItem::regex(r#""(?:[^"\\\n\r]|\\.)*""#)],
        None,
        true,
        false,
    )?;
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
    grammar.add(
        label_sort.clone(),
        vec![
            ProductionItem::NonTerminal {
                sort: label_sort.clone(),
                name: None,
            },
            ProductionItem::Terminal(format!(":{cast_sort}")),
        ],
        Some(Label::new(format!("#SemanticCastTo{label_sort}"))),
        false,
        false,
    )?;
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
