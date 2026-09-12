//! Deterministic rendering of the Bison grammar used by standalone program parsers.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::{self, Write};

use crate::definition::{
    Attributes, ProductionId, ProductionItem, Sentence, SortCatalog, SortHead,
    compute_associativities, compute_overloads, compute_priorities, compute_subsorts,
    sentence_equivalent,
};
use crate::kast::{Label, Sort};
use crate::kompile::{encode_kore_label, encode_kore_sort};

use super::scanner::{Scanner, TokenKey};
use super::{Error, Mode, PARSING_ONLY_SUBSORT_ATTRIBUTE, quote_c_string};

#[derive(Clone, Debug, Eq, PartialEq)]
enum GrammarError {
    CircularPriority(Vec<String>),
    CircularSubsort(Vec<Sort>),
    CircularOverload(Vec<ProductionId>),
    MissingStartProduction { sort: Sort },
    MissingSemanticAction { sort: Sort },
    InvalidBracket { sort: Sort },
    InvalidSubsort { sort: Sort },
    InvalidUserListMetadata { sort: Sort },
    InvalidUserList { sort: Sort, message: String },
    Scanner(String),
}

impl fmt::Display for GrammarError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CircularPriority(path) => {
                write!(formatter, "circular syntax priority: {}", path.join(" > "))
            }
            Self::CircularSubsort(path) => write!(
                formatter,
                "circular subsort relation: {}",
                path.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" < ")
            ),
            Self::CircularOverload(path) => write!(
                formatter,
                "circular overload relation: {}",
                path.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" < ")
            ),
            Self::MissingStartProduction { sort } => {
                write!(
                    formatter,
                    "program start sort {sort} has no Bison production"
                )
            }
            Self::MissingSemanticAction { sort } => {
                write!(
                    formatter,
                    "production for {sort} has no Bison semantic action"
                )
            }
            Self::InvalidBracket { sort } => write!(
                formatter,
                "bracket production for {sort} must contain exactly one nonterminal"
            ),
            Self::InvalidSubsort { sort } => write!(
                formatter,
                "subsort production for {sort} must contain exactly one nonterminal"
            ),
            Self::Scanner(message) => formatter.write_str(message),
            Self::InvalidUserListMetadata { sort } => write!(
                formatter,
                "user-list terminator bridge for {sort} requires string userList and userListTerminator labels"
            ),
            Self::InvalidUserList { sort, message } => {
                write!(formatter, "invalid user list {sort}: {message}")
            }
        }
    }
}

impl std::error::Error for GrammarError {}

#[derive(Clone, Debug)]
struct GrammarProduction {
    result: Sort,
    items: Vec<ProductionItem>,
    /// The unmodified production controls the semantic action after priority
    /// expansion changes only grammar-side sorts.
    source: Sentence,
}

#[derive(Clone, Debug)]
pub(super) struct PreparedGrammar {
    sentences: Vec<Sentence>,
    productions: Vec<GrammarProduction>,
}

impl PreparedGrammar {
    pub(super) fn scanner_sentences(&self) -> Vec<Sentence> {
        let mut sentences = self
            .sentences
            .iter()
            .filter(|sentence| !matches!(sentence, Sentence::Production { .. }))
            .cloned()
            .collect::<Vec<_>>();
        sentences.extend(self.productions.iter().map(|production| {
            let mut sentence = production.source.clone();
            let Sentence::Production {
                parameters,
                sort,
                items,
                ..
            } = &mut sentence
            else {
                unreachable!()
            };
            parameters.clear();
            *sort = production.result.clone();
            *items = production.items.clone();
            sentence
        }));
        sentences
    }
}

pub(super) fn prepare(sentences: &[Sentence]) -> Result<PreparedGrammar, Error> {
    Ok(PreparedGrammar {
        sentences: sentences.to_vec(),
        productions: prepare_user_lists(sentences)
            .map_err(|error| Error::render(error.to_string()))?,
    })
}

/// Render a complete deterministic `parser.y`.
///
/// `sentences` is the prepared program parsing grammar. Callers must use the
/// same token table for this renderer and the Flex renderer.
pub(super) fn render(
    prepared: &PreparedGrammar,
    scanner: &Scanner,
    start: &Sort,
    mode: Mode,
    stack_depth: u64,
) -> Result<String, Error> {
    render_inner(prepared, scanner, start, mode, stack_depth)
        .map_err(|error| Error::render(error.to_string()))
}

fn render_inner(
    prepared: &PreparedGrammar,
    scanner: &Scanner,
    start: &Sort,
    mode: Mode,
    stack_depth: u64,
) -> Result<String, GrammarError> {
    let sentences = &prepared.sentences;
    let productions =
        transform_priority_and_associativity(sentences, prepared.productions.clone())?;
    if !productions
        .iter()
        .any(|production| &production.result == start)
    {
        return Err(GrammarError::MissingStartProduction {
            sort: start.clone(),
        });
    }
    let reachable = reachable_sorts(&productions, start);
    let sort_catalog = SortCatalog::from_visible(sentences.iter());
    let semantic_sentences = || {
        sentences.iter().filter(|sentence| {
            !matches!(sentence, Sentence::Production { attributes, .. }
                if attributes.get(PARSING_ONLY_SUBSORT_ATTRIBUTE).is_some())
        })
    };
    let subsorts = compute_subsorts(semantic_sentences(), false)
        .map_err(|cycle| GrammarError::CircularSubsort(cycle.path))?;
    let overloads = compute_overloads(semantic_sentences(), &subsorts)
        .map_err(|cycle| GrammarError::CircularOverload(cycle.path))?;

    let mut output = String::new();
    write_prologue(&mut output, mode, stack_depth);

    for token in scanner.tokens_by_kind() {
        let description = match &token.key {
            TokenKey::Literal(value) => value.clone(),
            TokenKey::Regex(_) => token
                .key
                .pattern()
                .map_err(|error| GrammarError::Scanner(error.to_string()))?,
        };
        writeln!(
            output,
            "%token TOK_{} {} {}",
            token.kind,
            token.kind + 1,
            quote_c_string(&description)
        )
        .expect("writing to a string cannot fail");
    }
    for sort in &reachable {
        writeln!(output, "%nterm {}", encode_bison_sort(sort))
            .expect("writing to a string cannot fail");
    }
    output.push_str("%start top\n\n%%\n");
    writeln!(
        output,
        "top: {} {{ result = $1.nterm; }} ;",
        encode_bison_sort(start)
    )
    .expect("writing to a string cannot fail");

    let mut grouped = BTreeMap::<Sort, Vec<&GrammarProduction>>::new();
    for production in &productions {
        if reachable.contains(&production.result) {
            grouped
                .entry(production.result.clone())
                .or_default()
                .push(production);
        }
    }
    for alternatives in grouped.values_mut() {
        alternatives.sort_by_key(|production| structural_key(production));
    }

    for sort in &reachable {
        let Some(alternatives) = grouped.get(sort) else {
            continue;
        };
        writeln!(output, "{}:", encode_bison_sort(sort)).expect("writing to a string cannot fail");
        for (index, production) in alternatives.iter().enumerate() {
            output.push_str(if index == 0 { "  " } else { "  |" });
            write_production(
                &mut output,
                production,
                sentences,
                scanner,
                &sort_catalog,
                &subsorts,
                &overloads,
                mode == Mode::Glr,
            )?;
        }
        output.push_str(";\n");
    }
    output.push_str(
        "\n%%\n\nvoid yyerror (YYLTYPE *loc, void *scanner, const char *s) {\n\
         \x20   fprintf (stderr, \"%s:%d:%d:%d:%d:%s\\n\", loc->filename, loc->first_line,\n\
         \x20       loc->first_column, loc->last_line, loc->last_column, s);\n\
         }\n",
    );
    Ok(output)
}

fn transform_priority_and_associativity(
    sentences: &[Sentence],
    mut sources: Vec<GrammarProduction>,
) -> Result<Vec<GrammarProduction>, GrammarError> {
    let priorities = compute_priorities(sentences.iter())
        .map_err(|cycle| GrammarError::CircularPriority(cycle.path))?;
    let associativities = compute_associativities(sentences.iter());
    sources.sort_by_key(structural_key);

    let mut ordinals = BTreeMap::<BTreeSet<String>, usize>::new();
    let mut pending = BTreeSet::<(Sort, BTreeSet<String>)>::new();
    let mut productions = Vec::new();
    for source in sources {
        let Sentence::Production {
            label, parameters, ..
        } = &source.source
        else {
            unreachable!()
        };
        if !parameters.is_empty() {
            // The combined program grammar retains formal productions alongside the concrete
            // instances produced by lowering. Bison can consume only the latter.
            continue;
        }
        let mut transformed = source.items.clone();
        if let Some(label) = label {
            if matches!(
                transformed.first(),
                Some(ProductionItem::NonTerminal { .. })
            ) {
                constrain_side(
                    0,
                    &label.name,
                    &mut transformed,
                    &priorities,
                    &associativities.right,
                    &mut ordinals,
                    &mut pending,
                );
            }
            let last = transformed.len().saturating_sub(1);
            if last != 0
                && matches!(
                    transformed.get(last),
                    Some(ProductionItem::NonTerminal { .. })
                )
            {
                constrain_side(
                    last,
                    &label.name,
                    &mut transformed,
                    &priorities,
                    &associativities.left,
                    &mut ordinals,
                    &mut pending,
                );
            }
        }
        productions.push(GrammarProduction {
            result: source.result,
            items: transformed,
            source: source.source,
        });
    }

    let base = productions.clone();
    let mut queue = pending.iter().cloned().collect::<VecDeque<_>>();
    let mut expanded = BTreeSet::new();
    while let Some((sort, excluded)) = queue.pop_front() {
        if !expanded.insert((sort.clone(), excluded.clone())) {
            continue;
        }
        let ordinal = ordinals[&excluded];
        let restricted = restricted_sort(&sort, ordinal);
        for production in base.iter().filter(|production| production.result == sort) {
            if let Some(child) = grammar_subsort_child(production) {
                let child = child.clone();
                if pending.insert((child.clone(), excluded.clone())) {
                    queue.push_back((child.clone(), excluded.clone()));
                }
                productions.push(GrammarProduction {
                    result: restricted.clone(),
                    items: vec![ProductionItem::NonTerminal {
                        sort: child,
                        name: nonterminal_name(&production.items).map(str::to_owned),
                    }],
                    source: production.source.clone(),
                });
            } else if production_label(&production.source)
                .is_none_or(|label| !excluded.contains(&label.name))
            {
                productions.push(GrammarProduction {
                    result: restricted.clone(),
                    items: production.items.clone(),
                    source: production.source.clone(),
                });
            }
        }
    }
    productions.sort_by_key(structural_key);
    productions.dedup_by_key(|production| structural_key(production));
    Ok(productions)
}

fn prepare_user_lists(sentences: &[Sentence]) -> Result<Vec<GrammarProduction>, GrammarError> {
    let mut lists = BTreeMap::<Sort, Vec<&Sentence>>::new();
    let mut productions = Vec::new();
    for sentence in sentences {
        let Sentence::Production {
            sort,
            items,
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        if attributes.get_str("userList").is_some()
            && attributes.get("userListTerminator").is_none()
        {
            lists.entry(sort.clone()).or_default().push(sentence);
        } else {
            productions.push(GrammarProduction {
                result: sort.clone(),
                items: items.clone(),
                source: sentence.clone(),
            });
        }
    }

    for (sort, members) in lists {
        if members.iter().any(|sentence| {
            matches!(sentence, Sentence::Production { parameters, .. } if !parameters.is_empty())
        }) {
            productions.extend(members.into_iter().map(|sentence| {
                let Sentence::Production { sort, items, .. } = sentence else {
                    unreachable!()
                };
                GrammarProduction {
                    result: sort.clone(),
                    items: items.clone(),
                    source: sentence.clone(),
                }
            }));
            continue;
        }

        let recursive = members
            .iter()
            .copied()
            .filter(|sentence| production_nonterminal_count(sentence) == 2)
            .collect::<Vec<_>>();
        let terminators = members
            .iter()
            .copied()
            .filter(|sentence| production_nonterminal_count(sentence) == 0)
            .collect::<Vec<_>>();
        let ([recursive], [terminator]) = (recursive.as_slice(), terminators.as_slice()) else {
            return Err(GrammarError::InvalidUserList {
                sort,
                message: "expected one recursive and one terminator production".into(),
            });
        };
        let recursive = (*recursive).clone();
        let terminator = (*terminator).clone();
        let Sentence::Production {
            label: Some(cons),
            items: recursive_items,
            attributes: recursive_attributes,
            ..
        } = &recursive
        else {
            return Err(GrammarError::InvalidUserList {
                sort,
                message: "recursive production has no constructor label".into(),
            });
        };
        let Sentence::Production {
            label: Some(nil),
            attributes: terminator_attributes,
            ..
        } = &terminator
        else {
            return Err(GrammarError::InvalidUserList {
                sort,
                message: "terminator production has no constructor label".into(),
            });
        };
        let list_kind = recursive_attributes.get_str("userList");
        if !matches!(list_kind, Some("+") | Some("*"))
            || terminator_attributes.get_str("userList") != list_kind
        {
            return Err(GrammarError::InvalidUserList {
                sort,
                message: "recursive and terminator productions must have the same `+` or `*` userList attribute".into(),
            });
        }
        let non_empty = list_kind == Some("+");
        let arguments = nonterminal_sorts(recursive_items);
        let (child, left_associative) = match arguments.as_slice() {
            [list, child] if *list == &sort => ((*child).clone(), true),
            [child, list] if *list == &sort => ((*child).clone(), false),
            _ => {
                return Err(GrammarError::InvalidUserList {
                    sort,
                    message: "recursive production must contain the list sort on exactly one side"
                        .into(),
                });
            }
        };
        if left_associative && !non_empty {
            return Err(GrammarError::InvalidUserList {
                sort,
                message: "left-associative `List` is not supported by K's Bison transform".into(),
            });
        }

        let terminator_sort =
            Sort::with_parameters(format!("{}#Terminator", sort.name), sort.parameters.clone());
        productions.push(GrammarProduction {
            result: terminator_sort.clone(),
            items: vec![ProductionItem::Terminal(String::new())],
            source: terminator.clone(),
        });

        if left_associative {
            productions.push(GrammarProduction {
                result: sort.clone(),
                items: recursive_items.clone(),
                source: recursive.clone(),
            });
            let mut attributes = recursive_attributes.clone();
            attributes.remove("userList");
            attributes.insert("userList", serde_json::Value::String(cons.name.clone()));
            attributes.insert(
                "userListTerminator",
                serde_json::Value::String(nil.name.clone()),
            );
            let source = Sentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: sort.clone(),
                items: vec![ProductionItem::NonTerminal {
                    sort: child,
                    name: None,
                }],
                attributes,
            };
            let Sentence::Production { items, .. } = &source else {
                unreachable!()
            };
            productions.push(GrammarProduction {
                result: sort,
                items: items.clone(),
                source,
            });
            continue;
        }

        let nonempty_sort =
            Sort::with_parameters(format!("Ne#{}", sort.name), sort.parameters.clone());
        let recursive_grammar_items = recursive_items
            .iter()
            .map(|item| match item {
                ProductionItem::NonTerminal {
                    sort: item_sort,
                    name,
                } if item_sort == &sort => ProductionItem::NonTerminal {
                    sort: nonempty_sort.clone(),
                    name: name.clone(),
                },
                item => item.clone(),
            })
            .collect();
        productions.push(GrammarProduction {
            result: nonempty_sort.clone(),
            items: recursive_grammar_items,
            source: recursive.clone(),
        });
        productions.push(GrammarProduction {
            result: nonempty_sort.clone(),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: child,
                    name: None,
                },
                ProductionItem::Terminal(String::new()),
                ProductionItem::NonTerminal {
                    sort: terminator_sort.clone(),
                    name: None,
                },
            ],
            source: recursive.clone(),
        });
        productions.push(transparent_production(sort.clone(), nonempty_sort));
        if !non_empty {
            productions.push(transparent_production(sort.clone(), terminator_sort));
        }
    }
    Ok(productions)
}

fn transparent_production(result: Sort, child: Sort) -> GrammarProduction {
    let mut attributes = Attributes::default();
    attributes.insert("notInjection", serde_json::Value::String(String::new()));
    let items = vec![ProductionItem::NonTerminal {
        sort: child,
        name: None,
    }];
    GrammarProduction {
        result: result.clone(),
        items: items.clone(),
        source: Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: result,
            items,
            attributes,
        },
    }
}

fn production_nonterminal_count(sentence: &Sentence) -> usize {
    let Sentence::Production { items, .. } = sentence else {
        return 0;
    };
    items
        .iter()
        .filter(|item| matches!(item, ProductionItem::NonTerminal { .. }))
        .count()
}

#[allow(clippy::too_many_arguments)]
fn constrain_side(
    index: usize,
    parent: &str,
    items: &mut [ProductionItem],
    priorities: &crate::definition::PartialOrder<String>,
    associativity: &BTreeSet<(String, String)>,
    ordinals: &mut BTreeMap<BTreeSet<String>, usize>,
    pending: &mut BTreeSet<(Sort, BTreeSet<String>)>,
) {
    let mut excluded = priorities
        .relations_from(&parent.to_owned())
        .cloned()
        .unwrap_or_default();
    excluded.extend(
        associativity
            .iter()
            .filter(|(outer, _)| outer == parent)
            .map(|(_, inner)| inner.clone()),
    );
    if excluded.is_empty() {
        return;
    }
    let next = ordinals.len();
    let ordinal = *ordinals.entry(excluded.clone()).or_insert(next);
    let ProductionItem::NonTerminal { sort, .. } = &mut items[index] else {
        unreachable!("caller checked the production item")
    };
    let original = sort.clone();
    *sort = restricted_sort(&original, ordinal);
    pending.insert((original, excluded));
}

fn restricted_sort(sort: &Sort, ordinal: usize) -> Sort {
    Sort::with_parameters(format!("{}#{ordinal}", sort.name), sort.parameters.clone())
}

fn reachable_sorts(productions: &[GrammarProduction], start: &Sort) -> BTreeSet<Sort> {
    let mut reachable = BTreeSet::new();
    let mut pending = vec![start.clone()];
    while let Some(sort) = pending.pop() {
        if !reachable.insert(sort.clone()) {
            continue;
        }
        for production in productions
            .iter()
            .filter(|production| production.result == sort)
        {
            pending.extend(production.items.iter().filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                _ => None,
            }));
        }
    }
    reachable
}

#[allow(clippy::too_many_arguments)]
fn write_production(
    output: &mut String,
    production: &GrammarProduction,
    module_sentences: &[Sentence],
    scanner: &Scanner,
    sort_catalog: &SortCatalog<'_>,
    subsorts: &crate::definition::PartialOrder<Sort>,
    overloads: &crate::definition::OverloadOrder<'_>,
    glr: bool,
) -> Result<(), GrammarError> {
    let mut nonterminals = Vec::new();
    let mut rhs_position = 0usize;
    for item in &production.items {
        match item {
            ProductionItem::NonTerminal { sort, .. } => {
                rhs_position += 1;
                write!(output, "{} ", encode_bison_sort(sort))
                    .expect("writing to a string cannot fail");
                nonterminals.push(rhs_position);
            }
            ProductionItem::Terminal(value) if value.is_empty() => {}
            terminal => {
                rhs_position += 1;
                let kind = scanner
                    .kind(terminal)
                    .map_err(|error| GrammarError::Scanner(error.to_string()))?;
                write!(output, "TOK_{kind} ").expect("writing to a string cannot fail");
            }
        }
    }

    let Sentence::Production {
        label,
        sort,
        items,
        attributes,
        ..
    } = &production.source
    else {
        unreachable!("grammar productions retain a production sentence")
    };
    let has_location = sort_attributes(sort_catalog, sort)
        .get("locations")
        .is_some();
    // K's Production.isSubsort requires both a unary nonterminal shape and no
    // klabel. A labeled unary production is an ordinary constructor.
    let is_subsort = label.is_none() && subsort_child(items).is_some();

    if attributes.get("token").is_some() && !is_subsort {
        write_token_action(output, sort, sort_catalog, has_location);
    } else if attributes.get("token").is_none()
        && is_subsort
        && attributes.get("notInjection").is_none()
    {
        write_subsort_action(output, sort, items, attributes, has_location)?;
    } else if attributes.get("token").is_some() && is_subsort {
        write_token_subsort_action(output, sort, has_location);
    } else if is_subsort && attributes.get("notInjection").is_some() {
        let [child] = nonterminals.as_slice() else {
            return Err(GrammarError::InvalidSubsort { sort: sort.clone() });
        };
        writeln!(output, "{{\n  $$ = ${child};\n}}").expect("writing to a string cannot fail");
    } else if let Some(label) = label {
        write_labeled_action(
            output,
            label,
            sort,
            items,
            attributes,
            &nonterminals,
            module_sentences,
            sort_catalog,
            subsorts,
            overloads,
            has_location,
        );
    } else if attributes.get("bracket").is_some() {
        let [child] = nonterminals.as_slice() else {
            return Err(GrammarError::InvalidBracket { sort: sort.clone() });
        };
        writeln!(output, "{{\n  $$ = ${child};\n}}").expect("writing to a string cannot fail");
    } else {
        return Err(GrammarError::MissingSemanticAction { sort: sort.clone() });
    }

    if glr {
        let precedence = if attributes.get("prefer").is_some() {
            3
        } else if attributes.get("avoid").is_some() {
            1
        } else {
            2
        };
        writeln!(output, "%merge <mergeAmb> %dprec {precedence}")
            .expect("writing to a string cannot fail");
    }
    output.push('\n');
    Ok(())
}

fn write_token_action(
    output: &mut String,
    sort: &Sort,
    sort_catalog: &SortCatalog<'_>,
    has_location: bool,
) {
    let hook = sort_attributes(sort_catalog, sort).get_str("hook");
    let symbol = match hook {
        Some("STRING.String") => "$1.token",
        Some("BYTES.Bytes") => "$1.token+1",
        _ => "enquote($1.token)",
    };
    let sort = c_kore_sort(sort);
    writeln!(
        output,
        "{{\n  node *n = malloc(sizeof(node));\n  n->symbol = {symbol};\n  n->str = true;\n  n->location = @$;\n  n->hasLocation = 0;\n  n->nchildren = 0;\n  node *n2 = malloc(sizeof(node) + sizeof(node *));\n  n2->symbol = \"\\\\dv{{{sort}}}\";\n  n2->sort = \"{sort}\";\n  n2->str = false;\n  n2->location = @$;\n  n2->hasLocation = {};\n  n2->nchildren = 1;\n  n2->children[0] = n;\n  value_type value = {{.nterm = n2}};\n  $$ = value;\n}}",
        u8::from(has_location)
    )
    .expect("writing to a string cannot fail");
}

fn write_subsort_action(
    output: &mut String,
    result: &Sort,
    items: &[ProductionItem],
    attributes: &Attributes,
    has_location: bool,
) -> Result<(), GrammarError> {
    let child = subsort_child(items).ok_or_else(|| GrammarError::InvalidSubsort {
        sort: result.clone(),
    })?;
    let result_kore = c_kore_sort(result);
    let child_kore = c_kore_sort(child);
    writeln!(
        output,
        "{{\n  node *n = malloc(sizeof(node) + sizeof(node *));\n  n->str = false;\n  n->location = @$;\n  n->hasLocation = {};\n  n->nchildren = 1;\n  n->sort = \"{result_kore}\";\n  if (!$1.nterm->str && strncmp($1.nterm->symbol, \"inj{{\", 4) == 0) {{\n    char *childSort = $1.nterm->children[0]->sort;\n    n->symbol = injSymbol(childSort, n->sort);\n    n->children[0] = $1.nterm->children[0];\n  }} else {{\n    n->symbol = \"inj{{{child_kore}, {result_kore}}}\";\n    n->children[0] = $1.nterm;\n  }}",
        u8::from(has_location)
    )
    .expect("writing to a string cannot fail");

    if attributes.get("userListTerminator").is_some() {
        let nil = attributes.label("userListTerminator").ok_or_else(|| {
            GrammarError::InvalidUserListMetadata {
                sort: result.clone(),
            }
        })?;
        let cons =
            attributes
                .label("userList")
                .ok_or_else(|| GrammarError::InvalidUserListMetadata {
                    sort: result.clone(),
                })?;
        let nil = c_kore_label(&nil);
        let cons = c_kore_label(&cons);
        writeln!(
            output,
            "  node *n2 = malloc(sizeof(node));\n  n2->symbol = \"{nil}\";\n  n2->str = false;\n  n2->location = @$;\n  n2->hasLocation = 0;\n  n2->nchildren = 0;\n  n2->sort = \"{result_kore}\";\n  node *n3 = malloc(sizeof(node) + 2*sizeof(node *));\n  n3->symbol = \"{cons}\";\n  n3->str = false;\n  n3->location = @$;\n  n3->hasLocation = {};\n  n3->nchildren = 2;\n  n3->children[0] = n2;\n  n3->children[1] = $1.nterm;\n  n3->sort = \"{result_kore}\";\n  value_type value = {{.nterm = n3}};\n  $$ = value;\n}}",
            u8::from(has_location)
        )
        .expect("writing to a string cannot fail");
    } else {
        output.push_str("  value_type value = {.nterm = n};\n  $$ = value;\n}\n");
    }
    Ok(())
}

fn write_token_subsort_action(output: &mut String, sort: &Sort, has_location: bool) {
    let sort = c_kore_sort(sort);
    writeln!(
        output,
        "{{\n  node *n = malloc(sizeof(node) + sizeof(node *));\n  n->symbol = \"\\\\dv{{{sort}}}\";\n  n->sort = \"{sort}\";\n  n->str = false;\n  n->location = @$;\n  n->hasLocation = {};\n  n->nchildren = 1;\n  n->children[0] = $1.nterm->children[0];\n  value_type value = {{.nterm = n}};\n  $$ = value;\n}}",
        u8::from(has_location)
    )
    .expect("writing to a string cannot fail");
}

#[allow(clippy::too_many_arguments)]
fn write_labeled_action(
    output: &mut String,
    label: &Label,
    result: &Sort,
    items: &[ProductionItem],
    attributes: &Attributes,
    rhs_nonterminals: &[usize],
    module_sentences: &[Sentence],
    sort_catalog: &SortCatalog<'_>,
    subsorts: &crate::definition::PartialOrder<Sort>,
    overloads: &crate::definition::OverloadOrder<'_>,
    has_location: bool,
) {
    writeln!(
        output,
        "{{\n  node *n = malloc(sizeof(node) + sizeof(node *)*{});\n  n->str = false;\n  n->location = @$;\n  n->nchildren = {};",
        rhs_nonterminals.len(),
        rhs_nonterminals.len()
    )
    .expect("writing to a string cannot fail");

    let greater_ids = overloads
        .productions()
        .filter(|(_, candidate)| {
            sentence_equivalent(
                candidate,
                &Sentence::Production {
                    label: Some(label.clone()),
                    parameters: Vec::new(),
                    sort: result.clone(),
                    items: items.to_vec(),
                    attributes: attributes.clone(),
                },
            )
        })
        .map(|(id, _)| id)
        .collect::<Vec<_>>();
    for lesser in overloads.order().sorted_elements() {
        if !greater_ids
            .iter()
            .any(|greater| overloads.order().less_than(lesser, greater))
        {
            continue;
        }
        let Sentence::Production {
            label: Some(lesser_label),
            sort: lesser_result,
            items: lesser_items,
            ..
        } = overloads.production(*lesser)
        else {
            continue;
        };
        let greater_arguments = nonterminal_sorts(items);
        let lesser_arguments = nonterminal_sorts(lesser_items);
        output.push_str("  if (true");
        for ((greater, lesser), rhs) in greater_arguments
            .iter()
            .zip(&lesser_arguments)
            .zip(rhs_nonterminals)
        {
            if greater == lesser {
                continue;
            }
            let candidates = module_subsorts(module_sentences, subsorts, lesser);
            write!(
                output,
                " && strncmp(${rhs}.nterm->symbol, \"inj{{\", 4) == 0 && (false"
            )
            .expect("writing to a string cannot fail");
            for candidate in candidates {
                write!(
                    output,
                    " || strcmp(${rhs}.nterm->children[0]->sort, \"{}\") == 0",
                    c_kore_sort(&candidate)
                )
                .expect("writing to a string cannot fail");
            }
            output.push(')');
        }
        output.push_str(") {\n");
        writeln!(
            output,
            "    n->symbol = \"{}\";\n    n->sort = \"{}\";\n    n->hasLocation = {};",
            c_kore_label(lesser_label),
            c_kore_sort(lesser_result),
            u8::from(
                sort_attributes(sort_catalog, lesser_result)
                    .get("locations")
                    .is_some()
            )
        )
        .expect("writing to a string cannot fail");
        for (index, ((greater, lesser), rhs)) in greater_arguments
            .iter()
            .zip(&lesser_arguments)
            .zip(rhs_nonterminals)
            .enumerate()
        {
            if greater == lesser {
                writeln!(output, "    n->children[{index}] = ${rhs}.nterm;")
                    .expect("writing to a string cannot fail");
            } else {
                let lesser_sort = c_kore_sort(lesser);
                writeln!(
                    output,
                    "    {{\n      node *origChild = ${rhs}.nterm;\n      char *lesserSort = \"{lesser_sort}\";\n      if (strcmp(origChild->children[0]->sort, lesserSort) == 0) {{\n        n->children[{index}] = origChild->children[0];\n      }} else {{\n        node *inj = malloc(sizeof(node) + sizeof(node *));\n        inj->symbol = injSymbol(origChild->children[0]->sort, lesserSort);\n        inj->str = false;\n        inj->location = origChild->location;\n        inj->nchildren = 1;\n        inj->sort = lesserSort;\n        inj->hasLocation = origChild->hasLocation;\n        inj->children[0] = origChild->children[0];\n        n->children[{index}] = inj;\n      }}\n    }}"
                )
                .expect("writing to a string cannot fail");
            }
        }
        writeln!(
            output,
            "    node *n2 = malloc(sizeof(node) + sizeof(node *));\n    n2->str = false;\n    n2->location = @$;\n    n2->nchildren = 1;\n    n2->sort = \"{}\";\n    n2->hasLocation = {};\n    n2->symbol = injSymbol(n->sort, n2->sort);\n    n2->children[0] = n;\n    value_type value = {{.nterm = n2}};\n    $$ = value;\n  }} else",
            c_kore_sort(result),
            u8::from(has_location)
        )
        .expect("writing to a string cannot fail");
    }

    writeln!(
        output,
        "  {{\n    n->symbol = \"{}\";\n    n->sort = \"{}\";\n    n->hasLocation = {};",
        c_kore_label(label),
        c_kore_sort(result),
        u8::from(has_location)
    )
    .expect("writing to a string cannot fail");
    for (index, rhs) in rhs_nonterminals.iter().enumerate() {
        writeln!(output, "    n->children[{index}] = ${rhs}.nterm;")
            .expect("writing to a string cannot fail");
    }
    output.push_str("    value_type value = {.nterm = n};\n    $$ = value;\n  }\n}\n");
}

fn module_subsorts(
    sentences: &[Sentence],
    subsorts: &crate::definition::PartialOrder<Sort>,
    upper: &Sort,
) -> BTreeSet<Sort> {
    let mut sorts = BTreeSet::new();
    for sentence in sentences {
        match sentence {
            Sentence::Production { sort, items, .. } => {
                sorts.insert(sort.clone());
                sorts.extend(nonterminal_sorts(items).into_iter().cloned());
            }
            Sentence::SyntaxSort { sort, .. } => {
                sorts.insert(sort.clone());
            }
            _ => {}
        }
    }
    sorts
        .into_iter()
        .filter(|candidate| subsorts.less_than_eq(candidate, upper))
        .collect()
}

fn write_prologue(output: &mut String, mode: Mode, stack_depth: u64) {
    write!(
        output,
        "%{{\n#include <stdio.h>\n#include <string.h>\n#include \"node.h\"\n#include \"parser.tab.h\"\nint yylex(YYSTYPE *, YYLTYPE *, void *);\nvoid yyerror(YYLTYPE *, void *, const char *);\nchar *enquote(char *);\nchar *injSymbol(char *, char *);\nYYSTYPE mergeAmb(YYSTYPE x0, YYSTYPE x1);\nnode *result;\nextern char *filename;\n# define YYMAXDEPTH {}\n",
        stack_depth
    )
    .expect("writing to a string cannot fail");
    output.push_str(
        r#"# define YYLLOC_DEFAULT(Cur, Rhs, N)                      \
do                                                        \
  if (N)                                                  \
    {                                                     \
      (Cur).filename     = YYRHSLOC(Rhs, 1).filename;     \
      (Cur).first_line   = YYRHSLOC(Rhs, 1).first_line;   \
      (Cur).first_column = YYRHSLOC(Rhs, 1).first_column; \
      (Cur).last_line    = YYRHSLOC(Rhs, N).last_line;    \
      (Cur).last_column  = YYRHSLOC(Rhs, N).last_column;  \
    }                                                     \
  else                                                    \
    {                                                     \
      (Cur).filename     = YYRHSLOC(Rhs, 0).filename;     \
      (Cur).first_line   = (Cur).last_line =             \
        YYRHSLOC(Rhs, 0).last_line;                       \
      (Cur).first_column = (Cur).last_column =           \
        YYRHSLOC(Rhs, 0).last_column;                     \
    }                                                     \
while (0)
"#,
    );
    output.push_str(
        "%}\n\n%define api.value.type {union value_type}\n%define api.pure\n%define lr.type ielr\n%lex-param {void *scanner} \n%parse-param {void *scanner} \n%locations\n%initial-action {\n  @$.filename = filename;\n  @$.first_line = @$.first_column = @$.last_line = @$.last_column = 1;\n}\n",
    );
    if mode == Mode::Glr {
        output.push_str("%glr-parser\n");
    }
    output.push_str("%define parse.error verbose\n");
}

fn encode_bison_sort(sort: &Sort) -> String {
    let mut output = String::from("Sort");
    encode_bison_identifier(&sort.name, &mut output);
    output.push('_');
    for (index, parameter) in sort.parameters.iter().enumerate() {
        if index != 0 {
            output.push('_');
        }
        output.push_str(&encode_bison_sort(parameter));
    }
    output.push('_');
    output
}

fn encode_bison_identifier(name: &str, output: &mut String) {
    for character in name.chars() {
        if character.is_ascii_alphanumeric() {
            output.push(character);
        } else {
            write!(output, "_u{:x}_", u32::from(character))
                .expect("writing to a string cannot fail");
        }
    }
}

fn escape_c_string(value: &str) -> String {
    let mut output = String::new();
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\t' => output.push_str("\\t"),
            '\r' => output.push_str("\\r"),
            '\u{0c}' => output.push_str("\\f"),
            character if character.is_ascii_control() || character == '\u{7f}' => {
                write!(output, "\\{:03o}", u32::from(character))
                    .expect("writing to a string cannot fail");
            }
            character => output.push(character),
        }
    }
    output
}

fn c_kore_label(label: &Label) -> String {
    escape_c_string(&encode_kore_label(label).to_string())
}

fn c_kore_sort(sort: &Sort) -> String {
    escape_c_string(&encode_kore_sort(sort).to_string())
}

fn sort_attributes<'a>(catalog: &'a SortCatalog<'_>, sort: &Sort) -> &'a Attributes {
    static EMPTY: std::sync::OnceLock<Attributes> = std::sync::OnceLock::new();
    catalog
        .attributes_for(&SortHead::from(sort))
        .unwrap_or_else(|| EMPTY.get_or_init(Attributes::default))
}

fn production_label(sentence: &Sentence) -> Option<&Label> {
    match sentence {
        Sentence::Production { label, .. } => label.as_ref(),
        _ => None,
    }
}

fn grammar_subsort_child(production: &GrammarProduction) -> Option<&Sort> {
    production_label(&production.source)
        .is_none()
        .then(|| subsort_child(&production.items))
        .flatten()
}

fn subsort_child(items: &[ProductionItem]) -> Option<&Sort> {
    match items {
        [ProductionItem::NonTerminal { sort, .. }] => Some(sort),
        _ => None,
    }
}

fn nonterminal_name(items: &[ProductionItem]) -> Option<&str> {
    match items {
        [ProductionItem::NonTerminal { name, .. }] => name.as_deref(),
        _ => None,
    }
}

fn nonterminal_sorts(items: &[ProductionItem]) -> Vec<&Sort> {
    items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => Some(sort),
            _ => None,
        })
        .collect()
}

fn structural_key(production: &GrammarProduction) -> String {
    format!(
        "{}|{}|{}",
        sort_key(&production.result),
        items_key(&production.items),
        source_structural_key(&production.source)
    )
}

fn source_structural_key(sentence: &Sentence) -> String {
    let Sentence::Production {
        label,
        parameters,
        sort,
        items,
        attributes,
    } = sentence
    else {
        return String::new();
    };
    let label = label
        .as_ref()
        .map(|label| format!("{}{:?}", label.name, label.parameters))
        .unwrap_or_default();
    let attributes = attributes
        .semantic_entries()
        .iter()
        .map(|(key, value)| format!("{}:{value}", length_prefix(key)))
        .collect::<Vec<_>>()
        .join(";");
    format!(
        "{}|{:?}|{}|{}|{}",
        length_prefix(&label),
        parameters,
        sort_key(sort),
        items_key(items),
        attributes
    )
}

fn sort_key(sort: &Sort) -> String {
    format!("{}{:?}", length_prefix(&sort.name), sort.parameters)
}

fn items_key(items: &[ProductionItem]) -> String {
    items
        .iter()
        .map(|item| match item {
            ProductionItem::NonTerminal { sort, name } => {
                format!("N{}{:?}", sort_key(sort), name)
            }
            ProductionItem::RegexTerminal {
                precede_regex,
                regex,
                follow_regex,
            } => format!("R{precede_regex:?}{}{follow_regex:?}", length_prefix(regex)),
            ProductionItem::Terminal(value) => format!("T{}", length_prefix(value)),
        })
        .collect::<Vec<_>>()
        .join("|")
}

fn length_prefix(value: &str) -> String {
    format!("{}:{value}", value.len())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use serde_json::json;

    use super::*;
    use crate::definition::Associativity;

    fn attributes(entries: &[(&str, &str)]) -> Attributes {
        Attributes::new(
            entries
                .iter()
                .map(|(key, value)| ((*key).to_owned(), json!(*value)))
                .collect::<BTreeMap<_, _>>(),
        )
    }

    fn nonterminal(sort: &str) -> ProductionItem {
        ProductionItem::NonTerminal {
            sort: Sort::new(sort),
            name: None,
        }
    }

    fn production(
        result: &str,
        items: Vec<ProductionItem>,
        label: Option<&str>,
        attrs: &[(&str, &str)],
    ) -> Sentence {
        Sentence::Production {
            label: label.map(Label::new),
            parameters: Vec::new(),
            sort: Sort::new(result),
            items,
            attributes: attributes(attrs),
        }
    }

    fn syntax_sort(name: &str, attrs: &[(&str, &str)]) -> Sentence {
        Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new(name),
            attributes: attributes(attrs),
        }
    }

    fn rendered(sentences: &[Sentence], start: &str, mode: Mode) -> Result<String, Error> {
        let prepared = prepare(sentences)?;
        let scanner = Scanner::new(&prepared.scanner_sentences())?;
        render(&prepared, &scanner, &Sort::new(start), mode, 321)
    }

    #[test]
    fn renders_tokens_labels_brackets_locations_and_kore_names() {
        let integer_regex = ProductionItem::regex("[0-9]+");
        let label = Label::new("_+_#quoted");
        let sentences = vec![
            syntax_sort("Int", &[("hook", "INT.Int")]),
            syntax_sort("Exp", &[("locations", "")]),
            production("Int", vec![integer_regex], None, &[("token", "")]),
            production(
                "Exp",
                vec![
                    nonterminal("Int"),
                    ProductionItem::Terminal("+".into()),
                    nonterminal("Int"),
                ],
                Some(&label.name),
                &[],
            ),
            production(
                "Exp",
                vec![
                    ProductionItem::Terminal("(".into()),
                    nonterminal("Exp"),
                    ProductionItem::Terminal(")".into()),
                ],
                None,
                &[("bracket", "")],
            ),
            production(
                "Unused",
                vec![ProductionItem::Terminal("quote\"\n".into())],
                Some("unused"),
                &[],
            ),
        ];

        let output = rendered(&sentences, "Exp", Mode::Lr).unwrap();
        let declarations = output
            .lines()
            .filter(|line| line.starts_with("%token"))
            .collect::<Vec<_>>();
        let kinds = declarations
            .iter()
            .map(|line| {
                line.split_whitespace()
                    .nth(1)
                    .unwrap()
                    .trim_start_matches("TOK_")
                    .parse::<usize>()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert!(kinds.windows(2).all(|pair| pair[0] < pair[1]));
        assert!(output.contains(r#""quote\"\n""#));
        assert!(output.contains(&format!("n->symbol = \"{}\"", encode_kore_label(&label))));
        assert!(output.contains(&format!(
            "n->sort = \"{}\"",
            encode_kore_sort(&Sort::new("Exp"))
        )));
        assert!(output.contains("n->hasLocation = 1"));
        assert!(output.contains("$$ = $2;"));
        assert!(output.contains("n2->symbol = \"\\\\dv{SortInt{}}\""));
    }

    #[test]
    fn glr_emits_merge_and_prefer_avoid_precedence() {
        let sentences = vec![
            production(
                "Exp",
                vec![ProductionItem::Terminal("preferred".into())],
                Some("preferred"),
                &[("prefer", "")],
            ),
            production(
                "Exp",
                vec![ProductionItem::Terminal("ordinary".into())],
                Some("ordinary"),
                &[],
            ),
            production(
                "Exp",
                vec![ProductionItem::Terminal("avoided".into())],
                Some("avoided"),
                &[("avoid", "")],
            ),
        ];
        let output = rendered(&sentences, "Exp", Mode::Glr).unwrap();

        assert!(output.contains("# define YYMAXDEPTH 321"));
        assert!(output.contains("# define YYLLOC_DEFAULT"));
        assert!(output.contains("%glr-parser"));
        assert!(output.contains("%merge <mergeAmb> %dprec 3"));
        assert!(output.contains("%merge <mergeAmb> %dprec 2"));
        assert!(output.contains("%merge <mergeAmb> %dprec 1"));
    }

    #[test]
    fn priority_and_associativity_use_stable_structural_order() {
        let add = production(
            "Exp",
            vec![
                nonterminal("Exp"),
                ProductionItem::Terminal("+".into()),
                nonterminal("Exp"),
            ],
            Some("add"),
            &[],
        );
        let multiply = production(
            "Exp",
            vec![
                nonterminal("Exp"),
                ProductionItem::Terminal("*".into()),
                nonterminal("Exp"),
            ],
            Some("multiply"),
            &[],
        );
        let atom = production(
            "Exp",
            vec![ProductionItem::Terminal("x".into())],
            Some("atom"),
            &[],
        );
        let priority = Sentence::SyntaxPriority {
            priorities: vec![vec!["multiply".into()], vec!["add".into()]],
            attributes: Attributes::default(),
        };
        let associativity = Sentence::SyntaxAssociativity {
            associativity: Associativity::Left,
            tags: vec!["add".into()],
            attributes: Attributes::default(),
        };
        let first = vec![
            add.clone(),
            multiply.clone(),
            atom.clone(),
            priority.clone(),
            associativity.clone(),
        ];
        let second = vec![associativity, atom, priority, multiply, add];

        let first_output = rendered(&first, "Exp", Mode::Lr).unwrap();
        let second_output = rendered(&second, "Exp", Mode::Lr).unwrap();

        assert_eq!(first_output, second_output);
        assert!(first_output.contains("_u23_"));
        assert!(first_output.contains("n->symbol = \"Lbladd{}\""));
        assert!(first_output.contains("n->symbol = \"Lblmultiply{}\""));
    }

    #[test]
    fn subsorts_and_user_list_bridges_build_injections_and_cons_cells() {
        let sentences = vec![
            production(
                "List",
                vec![nonterminal("Elem")],
                None,
                &[("userList", "cons"), ("userListTerminator", "nil")],
            ),
            production(
                "Elem",
                vec![ProductionItem::Terminal("x".into())],
                Some("x"),
                &[],
            ),
        ];
        let output = rendered(&sentences, "List", Mode::Lr).unwrap();

        assert!(output.contains("inj{SortElem{}, SortList{}}"));
        assert!(output.contains("n2->symbol = \"Lblnil{}\""));
        assert!(output.contains("n3->symbol = \"Lblcons{}\""));
        assert!(output.contains("n3->children[1] = $1.nterm"));
    }

    #[test]
    fn lowers_a_nonempty_program_list_to_a_hidden_terminator() {
        let sentences = vec![
            production(
                "Exps",
                vec![
                    nonterminal("Exp"),
                    ProductionItem::Terminal(",".into()),
                    nonterminal("Exps"),
                ],
                Some("cons"),
                &[("userList", "+")],
            ),
            production(
                "Exps",
                vec![ProductionItem::Terminal(".Exps".into())],
                Some("nil"),
                &[("userList", "+")],
            ),
            production(
                "Exp",
                vec![ProductionItem::Terminal("x".into())],
                Some("x"),
                &[],
            ),
        ];

        let output = rendered(&sentences, "Exps", Mode::Lr).unwrap();

        assert!(output.contains("SortNe_u23_Exps__"));
        assert!(output.contains("SortExps_u23_Terminator__"));
        assert!(output.contains("n->symbol = \"Lblcons{}\""));
        assert!(output.contains("n->symbol = \"Lblnil{}\""));
    }

    #[test]
    fn bison_lists_make_nonempty_lists_left_associative() {
        let sentences = vec![
            production(
                "Exps",
                vec![
                    nonterminal("Exps"),
                    ProductionItem::Terminal(",".into()),
                    nonterminal("Exp"),
                ],
                Some("cons"),
                &[("userList", "+")],
            ),
            production(
                "Exps",
                vec![ProductionItem::Terminal(".Exps".into())],
                Some("nil"),
                &[("userList", "+")],
            ),
            production(
                "Exp",
                vec![ProductionItem::Terminal("x".into())],
                Some("x"),
                &[],
            ),
        ];
        let prepared = prepare(&sentences).unwrap();
        let scanner = Scanner::new(&prepared.scanner_sentences()).unwrap();

        let output = render(&prepared, &scanner, &Sort::new("Exps"), Mode::Lr, 321).unwrap();

        assert!(!output.contains("SortNe_u23_Exps__"));
        assert!(output.contains("SortExps__ TOK_"));
        assert!(output.contains("n3->children[0] = n2;"));
        assert!(output.contains("n3->children[1] = $1.nterm;"));
    }

    #[test]
    fn labeled_unary_productions_remain_constructors() {
        let sentences = vec![
            production("Parent", vec![nonterminal("Child")], Some("wrap"), &[]),
            production(
                "Child",
                vec![ProductionItem::Terminal("x".into())],
                Some("x"),
                &[],
            ),
        ];

        let output = rendered(&sentences, "Parent", Mode::Lr).unwrap();

        assert!(output.contains("n->symbol = \"Lblwrap{}\""));
        assert!(output.contains("n->children[0] = $1.nterm"));
        assert!(!output.contains("inj{SortChild{}, SortParent{}}"));
    }

    #[test]
    fn overloads_emit_runtime_downcast_checks() {
        let sentences = vec![
            production("Big", vec![nonterminal("Small")], None, &[]),
            production("BigArg", vec![nonterminal("SmallArg")], None, &[]),
            production(
                "Small",
                vec![
                    ProductionItem::Terminal("f".into()),
                    nonterminal("SmallArg"),
                ],
                Some("fSmall"),
                &[("klabel", "f")],
            ),
            production(
                "Big",
                vec![ProductionItem::Terminal("f".into()), nonterminal("BigArg")],
                Some("fBig"),
                &[("klabel", "f")],
            ),
        ];
        let output = rendered(&sentences, "Big", Mode::Lr).unwrap();

        assert!(output.contains("strncmp($2.nterm->symbol, \"inj{\", 4) == 0"));
        assert!(output.contains("n->symbol = \"LblfSmall{}\""));
        assert!(output.contains("n2->symbol = injSymbol(n->sort, n2->sort)"));
    }

    #[test]
    fn ignores_formal_parametric_productions() {
        let parameter = Sort::new("S");
        let sentence = Sentence::Production {
            label: Some(Label::with_parameters("box", vec![parameter.clone()])),
            parameters: vec![parameter.clone()],
            sort: Sort::with_parameters("Box", vec![parameter]),
            items: vec![nonterminal("S")],
            attributes: Attributes::default(),
        };
        let concrete = production(
            "Value",
            vec![ProductionItem::Terminal("value".into())],
            Some("value"),
            &[],
        );
        let sentences = [sentence, concrete];
        let output = rendered(&sentences, "Value", Mode::Lr).unwrap();

        assert!(!output.contains("SortBox"));
        assert!(output.contains("n->symbol = \"Lblvalue{}\""));
    }

    #[test]
    fn rejects_a_start_sort_without_a_production() {
        let sentences = vec![production(
            "Other",
            vec![ProductionItem::Terminal("x".into())],
            Some("x"),
            &[],
        )];

        let error = rendered(&sentences, "Missing", Mode::Lr).unwrap_err();

        assert!(
            error
                .to_string()
                .contains("program start sort Missing has no Bison production")
        );
    }
}
