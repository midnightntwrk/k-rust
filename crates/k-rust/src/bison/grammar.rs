//! ```toml algorithm
//! id = "parser.bison.priorities"
//! name = "restricted-sort expansion for Bison grammar export"
//! sites = ["transform_priority_and_associativity", "constrain_side", "restricted_sort", "derived_root_nodes", "remove_rules_restriction_made_useless", "prepare_user_lists"]
//! variable = "Q = restricted-sort and excluded-node-set pairs; J = judged operands of source productions; P = productions"
//! counters = []
//! no_counter = "Bison grammar export has no dedicated counter"
//!
//! [[cost]]
//! mode = "one exported grammar"
//! bound = "O((Q + J) x P)"
//! ```
//!
//! ```toml algorithm
//! id = "parser.bison.reachable_sorts"
//! name = "reachable-sort traversal for Bison grammar export"
//! sites = ["reachable_sorts"]
//! variable = "S = reachable sorts; P = productions"
//! counters = []
//! no_counter = "Bison grammar export has no dedicated counter"
//!
//! [[cost]]
//! mode = "one exported grammar"
//! bound = "O(S x P)"
//! ```
//!
//! Deterministic Bison grammar rendering for standalone program parsers.
//!
//! Restricted-sort expansion is a monotone worklist over `(sort, excluded nodes)` pairs,
//! O(pairs * productions). Which operand of a node excludes which child node is the in-process
//! parser's own judgement (`inner::Exclusions`, `inner::NodeShape`): the positions it judges,
//! the side, and the scope, cast, priority and associativity exclusions, asked once per judged
//! operand of each source production against every node, O(J * productions). A child
//! of a restricted sort that a production passes through is restricted too when it derives an
//! excluded node at its root, which one indexed DFS per child decides in O(productions);
//! the productions that restriction leaves deriving no finite tree are then removed by two
//! productivity worklists, linear in the exported items; a third, before rendering, decides which
//! productions are useful (rendered) and whether the start sort derives a program at all.
//! Reachability is a visited-set DFS, O(reachable sorts * productions), run twice: through every
//! production (the productions checked) and through the useful ones (the sorts rendered).
//! These exporter-only algorithms have no dedicated counter.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::{self, Write};

use super::placement::CPlacement;
use crate::definition::{
    AttributeKey, Attributes, ProductionId, ProductionItem, Sentence, SortCatalog, SortHead,
    compute_associativities, compute_overloads, compute_priorities, compute_subsorts,
    sentence_equivalent,
};
use crate::inner::{Exclusions, NodeShape};
use crate::kast::{Label, Sort};
use crate::kompile::{Placement, PlacementKind};
use crate::kompile::{encode_kore_label, encode_kore_sort};

use super::scanner::{Scanner, TokenKey};
use super::{Error, Mode, quote_c_string};

#[derive(Clone, Debug, Eq, PartialEq)]
enum GrammarError {
    CircularPriority(Vec<String>),
    CircularSubsort(Vec<Sort>),
    CircularOverload(Vec<ProductionId>),
    MissingStartProduction {
        sort: Sort,
    },
    /// The start sort has productions, but none derives a finite program: each needs an operand
    /// of a sort that derives none. Each entry is a production's rendered items with those
    /// operand sorts.
    UnproductiveStartSort {
        sort: Sort,
        productions: Vec<(String, Vec<Sort>)>,
    },
    MissingSemanticAction {
        sort: Sort,
    },
    InvalidBracket {
        sort: Sort,
    },
    InvalidSubsort {
        sort: Sort,
    },
    InvalidUserListMetadata {
        sort: Sort,
    },
    InvalidUserList {
        sort: Sort,
        message: String,
    },
    InvalidApplyPriority {
        label: String,
        message: String,
    },
    Scanner(String),
    UnlicensedPlacement {
        production: String,
        child: Sort,
        target: Sort,
    },
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
            Self::UnproductiveStartSort { sort, productions } => write!(
                formatter,
                "program start sort {sort} derives no program: each of its productions needs a sort that derives none ({})",
                productions
                    .iter()
                    .map(|(items, operands)| format!(
                        "{items} needs {}",
                        operands
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(", ")
                    ))
                    .collect::<Vec<_>>()
                    .join("; ")
            ),
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
            Self::UnlicensedPlacement {
                production,
                child,
                target,
            } => write!(
                formatter,
                "unlicensed parser placement {child} -> {target} in production {production}"
            ),
            Self::InvalidUserListMetadata { sort } => write!(
                formatter,
                "user-list terminator bridge for {sort} requires string userList and userListTerminator labels"
            ),
            Self::InvalidUserList { sort, message } => {
                write!(formatter, "invalid user list {sort}: {message}")
            }
            Self::InvalidApplyPriority { label, message } => {
                write!(formatter, "production {label}: {message}")
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
    action: Action,
}

/// What a grammar production's semantic action builds from its items.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Action {
    /// The source production's term; its operands are the items at the source's positions.
    Source,
    /// One part of a user list, recognized by left recursion; its
    /// source is the list's constructor production `L ::= E sep L`. The parts read a list's
    /// elements into a prefix, a chain from the last element read back to the first, and build
    /// the list's term from the prefix when the list ends, applying the constructor to each element and the list after it, so
    /// the term is the one the constructor's own production writes.
    List(ListPart),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ListPart {
    /// `Ne#L ::= E`: the prefix of the first element.
    First,
    /// `Ne#L ::= Ne#L sep E`: a prefix followed by one more element.
    Next,
    /// `L ::= Ne#L L#Terminator`: the list of a prefix.
    End,
}

/// The source positions of a list constructor's element and tail, `E sep L`.
const LIST_ELEMENT: usize = 0;
const LIST_TAIL: usize = 2;

impl Action {
    /// The item that stands for the source item at `source_index`, which priority and
    /// associativity restrict. In a list part, the element item is the element; the prefix of
    /// `Next` is the tail of the element before the new one, and the terminator of `End` the
    /// tail of the last element. The prefix of `End` is the whole list, no operand.
    fn item_of_source(self, source_index: usize) -> Option<usize> {
        match (self, source_index) {
            (Self::Source, index) => Some(index),
            (Self::List(ListPart::First), LIST_ELEMENT) => Some(0),
            (Self::List(ListPart::Next), LIST_ELEMENT) => Some(2),
            (Self::List(ListPart::Next), LIST_TAIL) => Some(0),
            (Self::List(ListPart::End), LIST_TAIL) => Some(1),
            (Self::List(_), _) => None,
        }
    }
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
    // Only the useful grammar is rendered: the productions whose operands all derive a finite
    // tree, over the sorts the start sort reaches through such productions. Every other rule can
    // take part in no parse, so the program language and the parser are those of the useful
    // grammar alone; Bison drops such rules too (as useless) before building its tables, keeping
    // the order of the rest, so it builds the same parser from either rendering. Rendering them
    // anyway only leaves Bison that removal, which its IELR pass does not survive on some
    // grammars: `AnnotationList__compute_from_inadequacies` aborts on a grammar it accepts once
    // the useless rules are gone. The productions the start sort reaches through any production
    // are still checked as they are rendered, so a definition's own error in a production that
    // derives nothing is still reported.
    let productive = productive_sorts(&productions, Sort::clone);
    let useful = |production: &GrammarProduction| {
        nonterminal_sorts(&production.items)
            .iter()
            .all(|operand| productive.contains(*operand))
    };
    let reachable = reachable_sorts(&productions, start, |_| true);
    let rendered_sorts = reachable_sorts(&productions, start, useful);
    let sort_catalog = SortCatalog::from_visible(sentences.iter());
    let semantic_sentences = || {
        sentences.iter().filter(|sentence| {
            !matches!(sentence, Sentence::Production { attributes, .. }
                if attributes.has(AttributeKey::BisonParsingOnlySubsort))
        })
    };
    let subsorts = compute_subsorts(semantic_sentences(), false)
        .map_err(|cycle| GrammarError::CircularSubsort(cycle.path))?;
    let overloads = compute_overloads(semantic_sentences(), &subsorts)
        .map_err(|cycle| GrammarError::CircularOverload(cycle.path))?;

    let sorts = module_sorts(sentences);
    let placements = CPlacement {
        subsorts: &subsorts,
        sorts: &sorts,
        location: "@$",
        has_location: "0",
        prefix: "placed",
    };
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
    for sort in &rendered_sorts {
        writeln!(output, "%nterm {}", encode_bison_sort(sort))
            .expect("writing to a string cannot fail");
    }
    write_list_closers(
        &mut output,
        &productions,
        &rendered_sorts,
        &sort_catalog,
        &placements,
        &overloads,
    )?;
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
        let mut rule = String::new();
        for production in alternatives {
            let mut alternative = String::new();
            write_production(
                &mut alternative,
                production,
                scanner,
                &sort_catalog,
                &placements,
                &overloads,
                mode == Mode::Glr,
            )?;
            if rendered_sorts.contains(sort) && useful(production) {
                rule.push_str(if rule.is_empty() { "  " } else { "  |" });
                rule.push_str(&alternative);
            }
        }
        // A rendered sort is productive, so it has a useful alternative.
        if !rule.is_empty() {
            writeln!(output, "{}:", encode_bison_sort(sort))
                .expect("writing to a string cannot fail");
            output.push_str(&rule);
            output.push_str(";\n");
        }
    }
    // Bison requires the start symbol to derive a sentence. A start sort whose productions all
    // need a sort without finite programs has no programs at all, the same empty program
    // language as a start sort without productions, so it is reported the same way, by sort.
    // The check follows rendering so that a production's own error, which names the
    // production and its location, is reported first.
    if !productive.contains(start) {
        return Err(GrammarError::UnproductiveStartSort {
            sort: start.clone(),
            productions: productions
                .iter()
                .filter(|production| &production.result == start)
                .map(|production| {
                    // Report the source production: the exported items differ from it only in
                    // operand sorts that restriction renamed, position by position.
                    let source = if let Sentence::Production { items, .. } = &production.source
                        && items.len() == production.items.len()
                    {
                        items
                    } else {
                        &production.items
                    };
                    let mut missing = Vec::new();
                    for (exported, written) in production.items.iter().zip(source) {
                        if let (
                            ProductionItem::NonTerminal { sort, .. },
                            ProductionItem::NonTerminal { sort: written, .. },
                        ) = (exported, written)
                            && !productive.contains(sort)
                            && !missing.contains(written)
                        {
                            missing.push(written.clone());
                        }
                    }
                    (render_items(source), missing)
                })
                .collect(),
        });
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
    let exclusions = Exclusions::new(priorities, &compute_associativities(sentences.iter()));
    // The combined program grammar retains formal productions alongside the concrete instances
    // produced by lowering. Bison can consume only the latter.
    sources.retain(|source| {
        matches!(&source.source, Sentence::Production { parameters, .. } if parameters.is_empty())
    });
    sources.sort_by_key(structural_key);

    // One node per source production: the parts of a user list build their constructor's.
    let mut node_ids = BTreeMap::<String, usize>::new();
    let mut nodes = Vec::<SourceNode>::new();
    let mut node_of = Vec::with_capacity(sources.len());
    for source in &sources {
        let id = match node_ids.entry(source_structural_key(&source.source)) {
            std::collections::btree_map::Entry::Occupied(entry) => *entry.get(),
            std::collections::btree_map::Entry::Vacant(entry) => {
                nodes.push(SourceNode::of(&source.source)?);
                *entry.insert(nodes.len() - 1)
            }
        };
        node_of.push(id);
    }
    let shapes = nodes.iter().map(SourceNode::shape).collect::<Vec<_>>();
    let children = (0..shapes.len())
        .filter(|node| shapes[*node].judged_as_child())
        .collect::<Vec<_>>();

    let mut excluded_at = BTreeMap::<(usize, usize), BTreeSet<usize>>::new();
    let mut ordinals = BTreeMap::<BTreeSet<usize>, usize>::new();
    let mut pending = BTreeSet::<(Sort, BTreeSet<usize>)>::new();
    let mut productions = Vec::new();
    for (source, &node) in sources.into_iter().zip(&node_of) {
        let parent = &shapes[node];
        let mut transformed = source.items.clone();
        let operands = source_operands(&source.source);
        for (offset, &source_index) in operands.iter().enumerate() {
            let position = offset + 1;
            let Some(side) = parent.judged_side(position, operands.len()) else {
                continue;
            };
            let Some(index) = source.action.item_of_source(source_index) else {
                continue;
            };
            let excluded = excluded_at.entry((node, position)).or_insert_with(|| {
                children
                    .iter()
                    .copied()
                    .filter(|child| {
                        exclusions
                            .violation(parent, &shapes[*child], side)
                            .is_some()
                    })
                    .collect()
            });
            if !excluded.is_empty() {
                constrain_side(
                    index,
                    excluded,
                    &mut transformed,
                    &mut ordinals,
                    &mut pending,
                );
            }
        }
        productions.push(GrammarProduction {
            result: source.result,
            items: transformed,
            source: source.source,
            action: source.action,
        });
    }

    let base = productions.clone();
    let mut by_result = BTreeMap::<&Sort, Vec<(&GrammarProduction, usize)>>::new();
    for (production, &node) in base.iter().zip(&node_of) {
        by_result
            .entry(&production.result)
            .or_default()
            .push((production, node));
    }
    let mut root_nodes = BTreeMap::<Sort, BTreeSet<usize>>::new();
    let mut queue = pending.iter().cloned().collect::<VecDeque<_>>();
    // Invariant: a state is queued exactly when it enters `pending` (the queue starts as its
    // elements, and the only push follows a successful insertion), so each state is expanded
    // once and `pending` holds every expanded or queued state.
    while let Some((sort, excluded)) = queue.pop_front() {
        let ordinal = ordinals[&excluded];
        let restricted = restricted_sort(&sort, ordinal);
        for &(production, node) in by_result.get(&sort).into_iter().flatten() {
            if shapes[node].passes_child_through() {
                // A production that passes its child through builds no node, so a node of the
                // child sort stands at the restricted position itself: the child is restricted
                // by the same exclusion, unless it derives no excluded node at its root.
                let mut items = production.items.clone();
                let child = pass_through_child(&mut items);
                let child_nodes = root_nodes
                    .entry(child.clone())
                    .or_insert_with(|| derived_root_nodes(&by_result, &shapes, child));
                if !child_nodes.is_disjoint(&excluded) {
                    if pending.insert((child.clone(), excluded.clone())) {
                        queue.push_back((child.clone(), excluded.clone()));
                    }
                    *child = restricted_sort(child, ordinal);
                }
                productions.push(GrammarProduction {
                    result: restricted.clone(),
                    items,
                    source: production.source.clone(),
                    action: production.action,
                });
            } else if !excluded.contains(&node) {
                productions.push(GrammarProduction {
                    result: restricted.clone(),
                    items: production.items.clone(),
                    source: production.source.clone(),
                    action: production.action,
                });
            }
        }
    }
    productions.sort_by_key(structural_key);
    productions.dedup_by_key(|production| structural_key(production));
    let origins = pending
        .iter()
        .map(|(sort, excluded)| (restricted_sort(sort, ordinals[excluded]), sort.clone()))
        .collect::<BTreeMap<_, _>>();
    remove_rules_restriction_made_useless(&mut productions, &origins);
    Ok(productions)
}

/// What the relation filter reads of a source production ([`NodeShape`]), owned so that every
/// exported production can borrow its node's shape.
struct SourceNode {
    parse_label: Option<String>,
    labelled: bool,
    token: bool,
    bracket: bool,
    items: usize,
    nonterminals: usize,
    first_nonterminal: bool,
    last_nonterminal: bool,
    apply_priority: Option<BTreeSet<usize>>,
}

impl SourceNode {
    fn of(source: &Sentence) -> Result<Self, GrammarError> {
        let Sentence::Production {
            label,
            items,
            attributes,
            ..
        } = source
        else {
            unreachable!("grammar productions come from production sentences")
        };
        let bracket = attributes.has(AttributeKey::Bracket);
        let apply_priority = attributes
            .string(AttributeKey::ApplyPriority)
            .map(|value| {
                crate::inner::parse_apply_priority(value).map_err(|error| {
                    GrammarError::InvalidApplyPriority {
                        label: label
                            .as_ref()
                            .map_or_else(String::new, |label| label.name.clone()),
                        message: error.to_string(),
                    }
                })
            })
            .transpose()?;
        Ok(Self {
            parse_label: label.as_ref().map(|label| label.name.clone()).or_else(|| {
                attributes
                    .label(AttributeKey::BracketLabel)
                    .filter(|_| bracket)
                    .map(|label| label.name)
            }),
            labelled: label.is_some(),
            token: attributes.has(AttributeKey::Token),
            bracket,
            items: items.len(),
            nonterminals: source_operands(source).len(),
            first_nonterminal: matches!(items.first(), Some(ProductionItem::NonTerminal { .. })),
            last_nonterminal: matches!(items.last(), Some(ProductionItem::NonTerminal { .. })),
            apply_priority,
        })
    }

    /// The node's shape. A bracket is transparent, as the in-process grammar declares it, and
    /// an exported grammar has no record syntax.
    fn shape(&self) -> NodeShape<'_> {
        NodeShape {
            parse_label: self.parse_label.as_ref(),
            labelled: self.labelled,
            token: self.token,
            bracket: self.bracket,
            transparent: self.bracket,
            record: false,
            items: self.items,
            nonterminals: self.nonterminals,
            first_nonterminal: self.first_nonterminal,
            last_nonterminal: self.last_nonterminal,
            apply_priority: self.apply_priority.as_ref(),
        }
    }
}

/// The item indices of a source production's nonterminals, in order: its node's children.
fn source_operands(source: &Sentence) -> Vec<usize> {
    let Sentence::Production { items, .. } = source else {
        unreachable!("grammar productions come from production sentences")
    };
    items
        .iter()
        .enumerate()
        .filter(|(_, item)| matches!(item, ProductionItem::NonTerminal { .. }))
        .map(|(index, _)| index)
        .collect()
}

/// The sort of the one nonterminal of an exported production whose source passes its child
/// through, to be restricted in place.
fn pass_through_child(items: &mut [ProductionItem]) -> &mut Sort {
    items
        .iter_mut()
        .find_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => Some(sort),
            ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
        })
        .expect("a production that passes its child through has one nonterminal")
}

/// The nodes `sort` derives at its root: the source nodes of its productions that build one,
/// and those of the sorts it derives through productions that pass their child through.
/// `by_result` indexes the productions by result sort, so one call reads each production at
/// most once.
fn derived_root_nodes(
    by_result: &BTreeMap<&Sort, Vec<(&GrammarProduction, usize)>>,
    shapes: &[NodeShape<'_>],
    sort: &Sort,
) -> BTreeSet<usize> {
    let mut nodes = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut pending = vec![sort.clone()];
    // Invariant: `nodes` holds the nodes built by the productions of every sort in `visited`,
    // and `pending` holds the children of those sorts' pass-through productions not yet
    // visited; each sort is visited once.
    while let Some(sort) = pending.pop() {
        if !visited.insert(sort.clone()) {
            continue;
        }
        for &(production, node) in by_result.get(&sort).into_iter().flatten() {
            if shapes[node].passes_child_through() {
                pending.extend(nonterminal_sorts(&production.items).into_iter().cloned());
            } else {
                nodes.insert(node);
            }
        }
    }
    nodes
}

/// The items of a production as K syntax: terminals quoted, nonterminals by sort.
fn render_items(items: &[ProductionItem]) -> String {
    items
        .iter()
        .map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => sort.to_string(),
            ProductionItem::Terminal(text) => quote_c_string(text),
            ProductionItem::RegexTerminal { regex, .. } => format!("r{}", quote_c_string(regex)),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// Remove every production that derives no finite tree only because of restriction.
///
/// A sort derives a tree only through a production whose operands all derive one, so a
/// production with an operand that derives nothing derives nothing either, and removing it
/// leaves the trees the grammar derives unchanged. Restriction can leave a sort without
/// productions (a restricted sort whose only production is excluded), and then every production
/// using it, and the sorts left without productions in turn. Bison reports such a rule as
/// useless, and the merge code of a GLR parser then depends on where that rule is rendered, so
/// the export removes them. A production that already derives nothing in the source grammar
/// (where each restricted sort `origins` maps is its unrestricted sort) is the definition's own
/// and is kept, so the checks of rendering still report its errors. This holds also when
/// restriction has emptied another of its operands (`A ::= C#0 "*" B` with `B` unproductive): `B`
/// already makes the production derive nothing, so it stays, checked by rendering and left out of
/// the rendered grammar with the definition's other useless rules (`render_inner`).
fn remove_rules_restriction_made_useless(
    productions: &mut Vec<GrammarProduction>,
    origins: &BTreeMap<Sort, Sort>,
) {
    let unrestricted = |sort: &Sort| origins.get(sort).cloned().unwrap_or_else(|| sort.clone());
    let source = productive_sorts(productions, unrestricted);
    let exported = productive_sorts(productions, Sort::clone);
    productions.retain(|production| {
        let operands = nonterminal_sorts(&production.items);
        operands.iter().all(|operand| exported.contains(*operand))
            || !operands
                .iter()
                .all(|operand| source.contains(&unrestricted(operand)))
    });
}

/// The sorts that derive a finite tree in the grammar of `productions` with each sort replaced
/// by its image under `sort`.
///
/// This is the productivity fixpoint, with one counter per production of its operand occurrences
/// not yet known to be productive, so it is linear in the items of `productions`.
fn productive_sorts(
    productions: &[GrammarProduction],
    sort: impl Fn(&Sort) -> Sort,
) -> BTreeSet<Sort> {
    let mut unproven = Vec::with_capacity(productions.len());
    let mut users = BTreeMap::<Sort, Vec<usize>>::new();
    let mut proven = Vec::new();
    for (index, production) in productions.iter().enumerate() {
        let operands = nonterminal_sorts(&production.items);
        unproven.push(operands.len());
        if operands.is_empty() {
            proven.push(index);
        }
        for operand in operands {
            users.entry(sort(operand)).or_default().push(index);
        }
    }
    let mut productive = BTreeSet::new();
    // Invariant: `productive` holds the result sorts of the popped productions, every one of
    // which has all its operands productive; `unproven[index]` counts the operand occurrences of
    // production `index` whose sort is not yet in `productive`, and a production enters `proven`
    // once, when its count is or reaches zero.
    while let Some(index) = proven.pop() {
        let result = sort(&productions[index].result);
        if productive.contains(&result) {
            continue;
        }
        for &user in users.get(&result).into_iter().flatten() {
            unproven[user] -= 1;
            if unproven[user] == 0 {
                proven.push(user);
            }
        }
        productive.insert(result);
    }
    productive
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
        if attributes.string(AttributeKey::UserList).is_some()
            && !attributes.has(AttributeKey::UserListTerminator)
        {
            lists.entry(sort.clone()).or_default().push(sentence);
        } else {
            productions.push(GrammarProduction {
                result: sort.clone(),
                items: items.clone(),
                source: sentence.clone(),
                action: Action::Source,
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
                    action: Action::Source,
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
        let list_kind = recursive_attributes.string(AttributeKey::UserList);
        if !matches!(list_kind, Some("+") | Some("*"))
            || terminator_attributes.string(AttributeKey::UserList) != list_kind
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
            action: Action::Source,
        });

        if left_associative {
            productions.push(GrammarProduction {
                result: sort.clone(),
                items: recursive_items.clone(),
                source: recursive.clone(),
                action: Action::Source,
            });
            let mut attributes = recursive_attributes.clone();
            attributes.unset(AttributeKey::UserList);
            attributes.set(
                AttributeKey::UserList,
                serde_json::Value::String(cons.name.clone()),
            );
            attributes.set(
                AttributeKey::UserListTerminator,
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
                action: Action::Source,
            });
            continue;
        }

        let nonempty_sort =
            Sort::with_parameters(format!("Ne#{}", sort.name), sort.parameters.clone());
        let [
            ProductionItem::NonTerminal { .. },
            separator @ ProductionItem::Terminal(_),
            ProductionItem::NonTerminal { .. },
        ] = recursive_items.as_slice()
        else {
            return Err(GrammarError::InvalidUserList {
                sort,
                message: "a user list's constructor production must be an element, a separator and the list".into(),
            });
        };
        let nonterminal = |sort: &Sort| ProductionItem::NonTerminal {
            sort: sort.clone(),
            name: None,
        };
        for (part, result, items) in [
            (ListPart::First, &nonempty_sort, vec![nonterminal(&child)]),
            (
                ListPart::Next,
                &nonempty_sort,
                vec![
                    nonterminal(&nonempty_sort),
                    separator.clone(),
                    nonterminal(&child),
                ],
            ),
            (
                ListPart::End,
                &sort,
                vec![nonterminal(&nonempty_sort), nonterminal(&terminator_sort)],
            ),
        ] {
            productions.push(GrammarProduction {
                result: result.clone(),
                items,
                source: recursive.clone(),
                action: Action::List(part),
            });
        }
        if !non_empty {
            productions.push(transparent_production(sort, terminator_sort));
        }
    }
    Ok(productions)
}

fn transparent_production(result: Sort, child: Sort) -> GrammarProduction {
    let mut attributes = Attributes::default();
    attributes.mark(AttributeKey::NotInjection);
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
        action: Action::Source,
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

/// Restrict the operand at item `index` to its sort without the nodes `excluded` names,
/// queueing that restricted sort for expansion.
fn constrain_side(
    index: usize,
    excluded: &BTreeSet<usize>,
    items: &mut [ProductionItem],
    ordinals: &mut BTreeMap<BTreeSet<usize>, usize>,
    pending: &mut BTreeSet<(Sort, BTreeSet<usize>)>,
) {
    let next = ordinals.len();
    let ordinal = *ordinals.entry(excluded.clone()).or_insert(next);
    let ProductionItem::NonTerminal { sort, .. } = &mut items[index] else {
        unreachable!("caller checked the production item")
    };
    let original = sort.clone();
    *sort = restricted_sort(&original, ordinal);
    pending.insert((original, excluded.clone()));
}

fn restricted_sort(sort: &Sort, ordinal: usize) -> Sort {
    Sort::with_parameters(format!("{}#{ordinal}", sort.name), sort.parameters.clone())
}

/// The sorts `start` reaches through the productions `usable` accepts.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "ProductionItem is not a sentence kind; only the listed variants are special here"
)]
fn reachable_sorts(
    productions: &[GrammarProduction],
    start: &Sort,
    usable: impl Fn(&GrammarProduction) -> bool,
) -> BTreeSet<Sort> {
    let mut reachable = BTreeSet::new();
    let mut pending = vec![start.clone()];
    // Invariant: `reachable` contains exactly the visited sort closure and `pending` contains
    // discovered sorts whose production children have not yet been scanned.
    while let Some(sort) = pending.pop() {
        if !reachable.insert(sort.clone()) {
            continue;
        }
        for production in productions
            .iter()
            .filter(|production| production.result == sort && usable(production))
        {
            pending.extend(production.items.iter().filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                _ => None,
            }));
        }
    }
    reachable
}

fn write_production(
    output: &mut String,
    production: &GrammarProduction,
    scanner: &Scanner,
    sort_catalog: &SortCatalog<'_>,
    placements: &CPlacement<'_>,
    overloads: &crate::definition::OverloadOrder<'_>,
    glr: bool,
) -> Result<(), GrammarError> {
    let mut nonterminals = Vec::new();
    let mut rhs_position = 0usize;
    for item in &production.items {
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "ProductionItem is not a sentence kind; only the listed variants are special here"
        )]
        let () = match item {
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
        };
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
        .value(AttributeKey::Locations)
        .is_some();
    // K's Production.isSubsort requires both a unary nonterminal shape and no
    // klabel. A labeled unary production is an ordinary constructor.
    let is_subsort = label.is_none() && subsort_child(items).is_some();
    let placements = CPlacement {
        has_location: if has_location { "1" } else { "0" },
        ..*placements
    };

    if let Action::List(part) = production.action {
        write_list_action(output, part, sort, &nonterminals);
    } else if attributes.has(AttributeKey::Token) && !is_subsort {
        write_token_action(output, sort, sort_catalog, has_location);
    } else if !attributes.has(AttributeKey::Token)
        && is_subsort
        && !attributes.has(AttributeKey::NotInjection)
        && !attributes.has(AttributeKey::BisonParsingOnlySubsort)
    {
        write_subsort_action(output, sort, items, attributes, &placements)?;
    } else if attributes.has(AttributeKey::Token) && is_subsort {
        write_token_action(output, sort, sort_catalog, has_location);
    } else if is_subsort
        && (attributes.has(AttributeKey::NotInjection)
            || attributes.has(AttributeKey::BisonParsingOnlySubsort))
    {
        // A recognition bridge only lets a declared instance be recognized at its
        // placeholder slot. It states no subsort, so return the value unchanged.
        let [child] = nonterminals.as_slice() else {
            return Err(GrammarError::InvalidSubsort { sort: sort.clone() });
        };
        writeln!(output, "{{\n  $$ = ${child};\n}}").expect("writing to a string cannot fail");
    } else if let Some(label) = label {
        let operands = nonterminals
            .iter()
            .map(|rhs| format!("${rhs}.nterm"))
            .collect::<Vec<_>>();
        write_labeled_action(
            output,
            label,
            sort,
            items,
            attributes,
            &operands,
            "$$ = value;",
            sort_catalog,
            &placements,
            overloads,
            has_location,
        )?;
    } else if attributes.has(AttributeKey::Bracket) {
        let [child] = nonterminals.as_slice() else {
            return Err(GrammarError::InvalidBracket { sort: sort.clone() });
        };
        writeln!(output, "{{\n  $$ = ${child};\n}}").expect("writing to a string cannot fail");
    } else {
        return Err(GrammarError::MissingSemanticAction { sort: sort.clone() });
    }

    if glr {
        let precedence = if attributes.has(AttributeKey::Prefer) {
            3
        } else if attributes.has(AttributeKey::Avoid) {
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

/// The C symbol of a list prefix node, the value of `ListPart::First` and `ListPart::Next`: it
/// holds an element and, after the first, the prefix before it. A prefix is no term; the list's
/// end consumes it. A node with another symbol in a prefix's place is the merge of two prefixes
/// a GLR parser read over the same text (`mergeAmb`). A prefix node is never changed once built,
/// since a GLR parser can continue one prefix in several readings.
const LIST_PREFIX_SYMBOL: &str = "krust_list_prefix";

/// The C function that builds the term of a list of `sort` from its prefix and terminator.
fn list_closer(sort: &Sort) -> String {
    format!("krust_list_{}", encode_bison_sort(sort))
}

fn write_list_action(output: &mut String, part: ListPart, sort: &Sort, nonterminals: &[usize]) {
    // The positions are those of the part's nonterminals: a separator written as `""` is no
    // symbol of the rendered production.
    let (children, element, location, before) = match (part, nonterminals) {
        (ListPart::First, &[element]) => (1, element, "@$".to_owned(), String::new()),
        (ListPart::Next, &[prefix, element]) => (
            2,
            element,
            format!("@{element}"),
            format!("\n  n->children[1] = ${prefix}.nterm;"),
        ),
        (ListPart::End, &[prefix, terminator]) => {
            writeln!(
                output,
                "{{\n  value_type value = {{.nterm = {}(${prefix}.nterm, ${terminator}.nterm, @$)}};\n  $$ = value;\n}}",
                list_closer(sort)
            )
            .expect("writing to a string cannot fail");
            return;
        }
        _ => unreachable!("a list part has the nonterminals `prepare_user_lists` gives it"),
    };
    // A prefix node is located at its element: the constructor applied to that element starts
    // there (`write_list_closers`).
    writeln!(
        output,
        "{{\n  node *n = malloc(sizeof(node) + sizeof(node *)*{children});\n  n->symbol = {LIST_PREFIX_SYMBOL};\n  n->sort = \"{}\";\n  n->str = false;\n  n->location = {location};\n  n->hasLocation = 0;\n  n->nchildren = {children};\n  n->children[0] = ${element}.nterm;{before}\n  value_type value = {{.nterm = n}};\n  $$ = value;\n}}",
        c_kore_sort(sort)
    )
    .expect("writing to a string cannot fail");
}

/// Writes, for each list recognized by left recursion that the start sort reaches, the
/// function its `ListPart::End` calls. It walks the prefix from the last element and applies
/// the list's constructor to each element and the list after it, starting from the
/// terminator: the constructor's node is written by the action of the constructor's own
/// production, with that production's location, from the element's start to the list's end.
/// A merged prefix is two readings of the same elements: each is closed over the same rest, and
/// the two lists are merged as the parser merges any two readings.
fn write_list_closers(
    output: &mut String,
    productions: &[GrammarProduction],
    reachable: &BTreeSet<Sort>,
    sort_catalog: &SortCatalog<'_>,
    placements: &CPlacement<'_>,
    overloads: &crate::definition::OverloadOrder<'_>,
) -> Result<(), GrammarError> {
    let mut constructors = BTreeMap::<&Sort, &Sentence>::new();
    for production in productions {
        if production.action == Action::List(ListPart::End)
            && reachable.contains(&production.result)
            && let Sentence::Production { sort, .. } = &production.source
        {
            constructors.insert(sort, &production.source);
        }
    }
    if constructors.is_empty() {
        return Ok(());
    }
    writeln!(
        output,
        "%{{\n#include <stdlib.h>\nstatic char {LIST_PREFIX_SYMBOL}[] = \"krust#ListPrefix\";"
    )
    .expect("writing to a string cannot fail");
    for (sort, constructor) in constructors {
        let Sentence::Production {
            label: Some(label),
            items,
            attributes,
            ..
        } = constructor
        else {
            unreachable!("a list part's source is the list's constructor")
        };
        let closer = list_closer(sort);
        writeln!(
            output,
            "static node *{closer}(node *prefix, node *rest, YYLTYPE end) {{\n  while (prefix) {{\n    if (prefix->symbol != {LIST_PREFIX_SYMBOL}) {{\n      YYSTYPE first = {{.nterm = {closer}(prefix->children[0], rest, end)}};\n      YYSTYPE second = {{.nterm = {closer}(prefix->children[1], rest, end)}};\n      return mergeAmb(first, second).nterm;\n    }}\n    YYLTYPE location = prefix->location;\n    location.last_line = end.last_line;\n    location.last_column = end.last_column;\n    location.last_offset = end.last_offset;"
        )
        .expect("writing to a string cannot fail");
        let has_location = sort_attributes(sort_catalog, sort)
            .value(AttributeKey::Locations)
            .is_some();
        let placements = CPlacement {
            location: "location",
            has_location: if has_location { "1" } else { "0" },
            ..*placements
        };
        write_labeled_action(
            output,
            label,
            sort,
            items,
            attributes,
            &["prefix->children[0]".to_owned(), "rest".to_owned()],
            "rest = value.nterm;",
            sort_catalog,
            &placements,
            overloads,
            has_location,
        )?;
        output.push_str(
            "    prefix = prefix->nchildren == 2 ? prefix->children[1] : NULL;\n  }\n  return rest;\n}\n",
        );
    }
    output.push_str("%}\n");
    Ok(())
}

/// A token reads the input text its first item spans (`@1`, which `krust_read` records for every
/// token the scanner returns) as a literal of its sort's hook: a token production's own token, or,
/// for a token subsort (`syntax MyStr ::= String [token]`), its child's phrase, so a token
/// subsort's literal is that text decoded by its own sort's hook, not the child's literal, and a
/// phrase that no token production read (`syntax MyTok ::= Pair [token]`) is a token of the sort
/// all the same. A phrase's text runs from the first character of its first token to the last of
/// its last, with the layout between them. The text is every byte of the span, so a token holding
/// U+0000 keeps it.
fn write_token_action(
    output: &mut String,
    sort: &Sort,
    sort_catalog: &SortCatalog<'_>,
    has_location: bool,
) {
    let kind = token_literal_kind(sort, sort_catalog);
    let sort_name = escape_c_string(&sort.to_string());
    let sort = c_kore_sort(sort);
    writeln!(
        output,
        "{{\n  char *error = NULL;\n  char *literal = krust_kore_literal_at(&@1, {kind}, \"{sort_name}\", &error);\n  if (!literal) {{\n    yyerror(&@$, scanner, error);\n    YYABORT;\n  }}\n  node *n = malloc(sizeof(node));\n  n->symbol = literal;\n  n->str = true;\n  n->location = @$;\n  n->hasLocation = 0;\n  n->nchildren = 0;\n  node *n2 = malloc(sizeof(node) + sizeof(node *));\n  n2->symbol = \"\\\\dv{{{sort}}}\";\n  n2->sort = \"{sort}\";\n  n2->str = false;\n  n2->location = @$;\n  n2->hasLocation = {};\n  n2->nchildren = 1;\n  n2->children[0] = n;\n  value_type value = {{.nterm = n2}};\n  $$ = value;\n}}",
        u8::from(has_location)
    )
    .expect("writing to a string cannot fail");
}

/// How the generated parser reads the code points of a token of `sort` from its text: those the
/// in-process frontend reads from it by the sort's hook (`kompile::term_to_kore`);
/// `krust_kore_literal` reads and writes them by the escape tables of `literals`.
fn token_literal_kind(sort: &Sort, sort_catalog: &SortCatalog<'_>) -> &'static str {
    match sort_attributes(sort_catalog, sort).string(AttributeKey::Hook) {
        Some("STRING.String") => "KRUST_TOKEN_STRING",
        Some("BYTES.Bytes") => "KRUST_TOKEN_BYTES",
        _ => "KRUST_TOKEN_TEXT",
    }
}

/// Describes a production from its own sort, items, source and location attributes,
/// so a placement diagnostic cannot hold a non-production sentence.
struct ProductionDescription<'a> {
    sort: &'a Sort,
    items: &'a [ProductionItem],
    attributes: &'a Attributes,
}

impl fmt::Display for ProductionDescription<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            sort,
            items,
            attributes,
        } = self;
        write!(formatter, "syntax {sort} ::=")?;
        for item in *items {
            match item {
                ProductionItem::NonTerminal { sort, name } => {
                    if let Some(name) = name {
                        write!(formatter, " {name}:{sort}")?;
                    } else {
                        write!(formatter, " {sort}")?;
                    }
                }
                ProductionItem::Terminal(value) => write!(formatter, " {value:?}")?,
                ProductionItem::RegexTerminal { regex, .. } => {
                    write!(formatter, " r{regex:?}")?;
                }
            }
        }
        if let Some(source) = attributes.source() {
            write!(formatter, " at {source}")?;
        }
        if let Some(location) = attributes.location() {
            write!(
                formatter,
                " ({},{},{},{})",
                location.start_line, location.start_column, location.end_line, location.end_column
            )?;
        } else if let Some(location) = attributes.string(AttributeKey::Location) {
            write!(formatter, " {location}")?;
        }
        Ok(())
    }
}

fn require_placement(
    sort: &Sort,
    items: &[ProductionItem],
    attributes: &Attributes,
    child: &Sort,
    target: &Sort,
    placements: &CPlacement<'_>,
) -> Result<Placement, GrammarError> {
    Placement::between(child, target, placements.subsorts).ok_or_else(|| {
        GrammarError::UnlicensedPlacement {
            production: ProductionDescription {
                sort,
                items,
                attributes,
            }
            .to_string(),
            child: child.clone(),
            target: target.clone(),
        }
    })
}

fn write_subsort_action(
    output: &mut String,
    result: &Sort,
    items: &[ProductionItem],
    attributes: &Attributes,
    placements: &CPlacement<'_>,
) -> Result<(), GrammarError> {
    let child = subsort_child(items).ok_or_else(|| GrammarError::InvalidSubsort {
        sort: result.clone(),
    })?;
    let result_kore = c_kore_sort(result);
    output.push_str("{\n");
    if attributes.has(AttributeKey::UserListTerminator) {
        let nil = attributes
            .label(AttributeKey::UserListTerminator)
            .ok_or_else(|| GrammarError::InvalidUserListMetadata {
                sort: result.clone(),
            })?;
        let cons = attributes.label(AttributeKey::UserList).ok_or_else(|| {
            GrammarError::InvalidUserListMetadata {
                sort: result.clone(),
            }
        })?;
        let nil = c_kore_label(&nil);
        let cons = c_kore_label(&cons);
        writeln!(
            output,
            "  node *n2 = malloc(sizeof(node));\n  n2->symbol = \"{nil}\";\n  n2->str = false;\n  n2->location = @$;\n  n2->hasLocation = 0;\n  n2->nchildren = 0;\n  n2->sort = \"{result_kore}\";\n  node *n3 = malloc(sizeof(node) + 2*sizeof(node *));\n  n3->symbol = \"{cons}\";\n  n3->str = false;\n  n3->location = @$;\n  n3->hasLocation = {};\n  n3->nchildren = 2;\n  n3->children[0] = n2;\n  n3->children[1] = $1.nterm;\n  n3->sort = \"{result_kore}\";\n  value_type value = {{.nterm = n3}};\n  $$ = value;\n}}",
            placements.has_location
        )
        .expect("writing to a string cannot fail");
    } else {
        let plan = require_placement(result, items, attributes, child, result, placements)?;
        let value = placements.write(output, &plan, "$1.nterm");
        writeln!(
            output,
            "  value_type value = {{.nterm = {value}}};\n  $$ = value;\n}}"
        )
        .expect("writing to a string cannot fail");
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn write_labeled_action(
    output: &mut String,
    label: &Label,
    result: &Sort,
    items: &[ProductionItem],
    attributes: &Attributes,
    operands: &[String],
    sink: &str,
    sort_catalog: &SortCatalog<'_>,
    placements: &CPlacement<'_>,
    overloads: &crate::definition::OverloadOrder<'_>,
    has_location: bool,
) -> Result<(), GrammarError> {
    writeln!(
        output,
        "{{\n  node *n = malloc(sizeof(node) + sizeof(node *)*{});\n  n->str = false;\n  n->location = {};\n  n->nchildren = {};",
        operands.len(),
        placements.location,
        operands.len()
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
    let mut overload_count = 0;
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
            attributes: lesser_attributes,
            ..
        } = overloads.production(*lesser)
        else {
            continue;
        };
        let result_plan = require_placement(
            lesser_result,
            lesser_items,
            lesser_attributes,
            lesser_result,
            result,
            placements,
        )?;
        let greater_arguments = nonterminal_sorts(items);
        let lesser_arguments = nonterminal_sorts(lesser_items);
        let mut recoveries = Vec::new();
        for ((greater, lesser), operand) in greater_arguments
            .iter()
            .zip(&lesser_arguments)
            .zip(operands)
        {
            require_placement(
                lesser_result,
                lesser_items,
                lesser_attributes,
                lesser,
                greater,
                placements,
            )?;
            let cases = if greater == lesser {
                Vec::new()
            } else {
                recovery_cases(placements, greater, lesser, operand)
            };
            recoveries.push(cases);
        }
        // Each candidate has its own scope, so later candidates are tested only after a miss.
        output.push_str("  {\n");
        overload_count += 1;
        let mut previous_recovery = None;
        for (index, (greater_lesser, cases)) in greater_arguments
            .iter()
            .zip(&lesser_arguments)
            .zip(&recoveries)
            .enumerate()
        {
            if greater_lesser.0 == greater_lesser.1 {
                continue;
            }
            writeln!(output, "  int matched_case_{index} = -1;")
                .expect("writing to a string cannot fail");
            if let Some(previous) = previous_recovery {
                writeln!(output, "  if (matched_case_{previous} >= 0) {{")
                    .expect("writing to a string cannot fail");
            }
            for (ordinal, case) in cases.iter().enumerate() {
                writeln!(
                    output,
                    "  {}if ({}) {{ matched_case_{index} = {ordinal}; }}",
                    if ordinal == 0 { "" } else { "else " },
                    case.condition
                )
                .expect("writing to a string cannot fail");
            }
            if previous_recovery.is_some() {
                output.push_str("  }\n");
            }
            previous_recovery = Some(index);
        }
        output.push_str("  if (true");
        for (index, (greater, lesser)) in
            greater_arguments.iter().zip(&lesser_arguments).enumerate()
        {
            if greater != lesser {
                write!(output, " && matched_case_{index} >= 0")
                    .expect("writing to a string cannot fail");
            }
        }
        output.push_str(") {\n");
        writeln!(
            output,
            "    n->symbol = \"{}\";\n    n->sort = \"{}\";\n    n->hasLocation = {};",
            c_kore_label(lesser_label),
            c_kore_sort(lesser_result),
            u8::from(
                sort_attributes(sort_catalog, lesser_result)
                    .value(AttributeKey::Locations)
                    .is_some()
            )
        )
        .expect("writing to a string cannot fail");
        for (index, (((greater, lesser), operand), cases)) in greater_arguments
            .iter()
            .zip(&lesser_arguments)
            .zip(operands)
            .zip(&recoveries)
            .enumerate()
        {
            if greater == lesser {
                writeln!(output, "    n->children[{index}] = {operand};")
                    .expect("writing to a string cannot fail");
            } else {
                for (ordinal, case) in cases.iter().enumerate() {
                    writeln!(
                        output,
                        "    {}if (matched_case_{index} == {ordinal}) {{",
                        if ordinal == 0 { "" } else { "else " },
                    )
                    .expect("writing to a string cannot fail");
                    let location = format!("{operand}->location");
                    let has_location = format!("{operand}->hasLocation");
                    let prefix = format!("recovered_{index}");
                    let emitter = CPlacement {
                        location: &location,
                        has_location: &has_location,
                        prefix: &prefix,
                        ..*placements
                    };
                    let child = emitter.write(output, &case.placement, &case.child);
                    writeln!(output, "      n->children[{index}] = {child};\n    }}")
                        .expect("writing to a string cannot fail");
                }
            }
        }
        let returned = placements.write(output, &result_plan, "n");
        writeln!(
            output,
            "    value_type value = {{.nterm = {returned}}};\n    {sink}\n  }} else"
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
    for (index, operand) in operands.iter().enumerate() {
        writeln!(output, "    n->children[{index}] = {operand};")
            .expect("writing to a string cannot fail");
    }
    writeln!(
        output,
        "    value_type value = {{.nterm = n}};\n    {sink}\n  }}"
    )
    .expect("writing to a string cannot fail");
    for _ in 0..overload_count {
        output.push_str("  }\n");
    }
    output.push_str("}\n");
    Ok(())
}

struct RecoveryCase {
    condition: String,
    child: String,
    placement: Placement,
}

fn recovery_cases(
    placements: &CPlacement<'_>,
    greater: &Sort,
    lesser: &Sort,
    node: &str,
) -> Vec<RecoveryCase> {
    placements
        .sorts
        .iter()
        .filter_map(|source| {
            let placement = Placement::between(source, lesser, placements.subsorts)?;
            let outer = Placement::between(lesser, greater, placements.subsorts)?;
            let shape = RecoveryShape::from_plan(source, &placement, placements.subsorts)
                .wrap(&outer, placements.subsorts);
            let (condition, child) = shape.c_match(node);
            Some(RecoveryCase {
                condition,
                child,
                placement,
            })
        })
        .collect()
}

/// The inverse of an outer placement. Each traversal is guarded before its child is read.
/// Only a canonical singleton has an inverse from K to an item.
#[derive(Debug)]
enum RecoveryShape {
    Value(Sort),
    Injection {
        witness: crate::kompile::Injectable,
        inner: Box<Self>,
    },
    Singleton(Box<Self>),
}

impl RecoveryShape {
    fn from_plan(
        source: &Sort,
        plan: &Placement,
        subsorts: &crate::definition::PartialOrder<Sort>,
    ) -> Self {
        Self::Value(source.clone()).wrap(plan, subsorts)
    }

    fn wrap(self, plan: &Placement, subsorts: &crate::definition::PartialOrder<Sort>) -> Self {
        let inject = |inner: Self, witness: &crate::kompile::Injectable| match inner {
            Self::Injection {
                witness: nested,
                inner,
            } if nested.target() == witness.source() => {
                match crate::kompile::Injectable::between(
                    nested.source(),
                    witness.target(),
                    subsorts,
                ) {
                    Some(composed) => Self::Injection {
                        witness: composed,
                        inner,
                    },
                    None => Self::Injection {
                        witness: witness.clone(),
                        inner: Box::new(Self::Injection {
                            witness: nested,
                            inner,
                        }),
                    },
                }
            }
            inner @ (Self::Value(_) | Self::Injection { .. } | Self::Singleton(_)) => {
                Self::Injection {
                    witness: witness.clone(),
                    inner: Box::new(inner),
                }
            }
        };
        match plan.kind() {
            PlacementKind::Identity => self,
            PlacementKind::Injection(witness) => inject(self, witness),
            PlacementKind::SingletonK { item } => Self::Singleton(Box::new(match item {
                None => self,
                Some(witness) => inject(self, witness),
            })),
            PlacementKind::SingletonKInjection { item, sequence } => inject(
                Self::Singleton(Box::new(match item {
                    None => self,
                    Some(witness) => inject(self, witness),
                })),
                sequence,
            ),
        }
    }

    fn c_match(&self, node: &str) -> (String, String) {
        match self {
            Self::Value(sort) => (
                format!("strcmp(({node})->sort, \"{}\") == 0", c_kore_sort(sort)),
                node.into(),
            ),
            Self::Injection { witness, inner } => {
                let child = format!("({node})->children[0]");
                let (condition, recovered) = inner.c_match(&child);
                (
                    format!(
                        "!({node})->str && ({node})->nchildren == 1 && strcmp(({node})->symbol, {}) == 0 && strcmp(({node})->sort, \"{}\") == 0 && ({condition})",
                        quote_c_string(&super::placement::injection_symbol(witness)),
                        c_kore_sort(witness.target())
                    ),
                    recovered,
                )
            }
            Self::Singleton(inner) => {
                let head = format!("({node})->children[0]");
                let tail = format!("({node})->children[1]");
                let (condition, recovered) = inner.c_match(&head);
                (
                    format!(
                        "!({node})->str && ({node})->nchildren == 2 && strcmp(({node})->symbol, \"kseq{{}}\") == 0 && strcmp(({node})->sort, \"SortK{{}}\") == 0 && !({tail})->str && ({tail})->nchildren == 0 && strcmp(({tail})->symbol, \"dotk{{}}\") == 0 && strcmp(({tail})->sort, \"SortK{{}}\") == 0 && strcmp(({head})->sort, \"SortKItem{{}}\") == 0 && ({condition})"
                    ),
                    recovered,
                )
            }
        }
    }

    #[cfg(test)]
    fn recover<'a>(
        &self,
        pattern: &'a crate::kore::ast::Pattern,
    ) -> Option<&'a crate::kore::ast::Pattern> {
        use crate::kore::ast::Pattern;
        match self {
            Self::Value(_) => Some(pattern),
            Self::Injection { witness, inner } => {
                let Pattern::Application { symbol, arguments } = pattern else {
                    return None;
                };
                (symbol.name == "inj"
                    && symbol.sort_parameters
                        == [
                            encode_kore_sort(witness.source()),
                            encode_kore_sort(witness.target()),
                        ]
                    && arguments.len() == 1)
                    .then(|| inner.recover(&arguments[0]))
                    .flatten()
            }
            Self::Singleton(inner) => {
                let Pattern::Application { symbol, arguments } = pattern else {
                    return None;
                };
                let [
                    head,
                    Pattern::Application {
                        symbol: tail,
                        arguments: empty,
                    },
                ] = arguments.as_slice()
                else {
                    return None;
                };
                (symbol.name == "kseq"
                    && symbol.sort_parameters.is_empty()
                    && tail.name == "dotk"
                    && tail.sort_parameters.is_empty()
                    && empty.is_empty())
                .then(|| inner.recover(head))
                .flatten()
            }
        }
    }
}

fn module_sorts(sentences: &[Sentence]) -> BTreeSet<Sort> {
    let mut sorts = BTreeSet::from([Sort::new("K"), Sort::new("KItem")]);
    for sentence in sentences {
        match sentence {
            Sentence::Production {
                parameters,
                sort,
                items,
                ..
            } => {
                if parameters.is_empty() {
                    sorts.insert(sort.clone());
                    sorts.extend(nonterminal_sorts(items).into_iter().cloned());
                }
            }
            Sentence::SyntaxSort {
                parameters, sort, ..
            } => {
                if parameters.is_empty() {
                    sorts.insert(sort.clone());
                }
            }
            Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => {}
        }
    }
    sorts
}

fn write_prologue(output: &mut String, mode: Mode, stack_depth: u64) {
    write!(
        output,
        "%{{\n#include <stdio.h>\n#include <string.h>\n#include \"node.h\"\n#include \"parser.tab.h\"\nint yylex(YYSTYPE *, YYLTYPE *, void *);\nvoid yyerror(YYLTYPE *, void *, const char *);\nYYSTYPE mergeAmb(YYSTYPE x0, YYSTYPE x1);\nnode *result;\nextern char *filename;\n# define YYMAXDEPTH {}\n",
        stack_depth
    )
    .expect("writing to a string cannot fail");
    output.push_str(
        r#"# define YYLLOC_DEFAULT(Cur, Rhs, N)                      \
do                                                        \
  if (N)                                                  \
    {                                                     \
      int krust_first = 1;                                \
      while (krust_first < (N) &&                         \
             YYRHSLOC(Rhs, krust_first).first_offset ==   \
               YYRHSLOC(Rhs, krust_first).last_offset)    \
        ++krust_first;                                    \
      (Cur).filename     = YYRHSLOC(Rhs, 1).filename;     \
      (Cur).first_line   =                                \
        YYRHSLOC(Rhs, krust_first).first_line;            \
      (Cur).first_column =                                \
        YYRHSLOC(Rhs, krust_first).first_column;          \
      (Cur).first_offset =                                \
        YYRHSLOC(Rhs, krust_first).first_offset;          \
      (Cur).last_line    = YYRHSLOC(Rhs, N).last_line;    \
      (Cur).last_column  = YYRHSLOC(Rhs, N).last_column;  \
      (Cur).last_offset  = YYRHSLOC(Rhs, N).last_offset;  \
    }                                                     \
  else                                                    \
    {                                                     \
      (Cur).filename     = YYRHSLOC(Rhs, 0).filename;     \
      (Cur).first_line   = (Cur).last_line =             \
        YYRHSLOC(Rhs, 0).last_line;                       \
      (Cur).first_column = (Cur).last_column =           \
        YYRHSLOC(Rhs, 0).last_column;                     \
      (Cur).first_offset = (Cur).last_offset =           \
        YYRHSLOC(Rhs, 0).last_offset;                     \
    }                                                     \
while (0)
"#,
    );
    output.push_str(
        "%}\n\n%define api.value.type {union value_type}\n%define api.pure\n%define lr.type ielr\n%lex-param {void *scanner} \n%parse-param {void *scanner} \n%locations\n%initial-action {\n  @$.filename = filename;\n  @$.first_line = @$.first_column = @$.last_line = @$.last_column = 1;\n  @$.first_offset = @$.last_offset = 0;\n}\n",
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

#[cfg(test)]
fn production_label(sentence: &Sentence) -> Option<&Label> {
    match sentence {
        Sentence::Production { label, .. } => label.as_ref(),
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Rule { .. }
        | Sentence::Claim { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => None,
    }
}

#[cfg(test)]
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

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "ProductionItem is not a sentence kind; only the listed variants are special here"
)]
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
            ProductionItem::RegexTerminal { regex } => format!("R{}", length_prefix(regex)),
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
    fn kitem_subsort_returns_a_singleton_k() {
        use crate::kompile::{Placement, PlacementKind};
        let sentences = vec![
            syntax_sort("K", &[("locations", "")]),
            production("K", vec![nonterminal("KItem")], None, &[]),
            production(
                "KItem",
                vec![ProductionItem::Terminal("a".into())],
                Some("a"),
                &[],
            ),
        ];
        let subsorts = compute_subsorts(sentences.iter(), false).unwrap();
        let plan = Placement::between(&Sort::new("KItem"), &Sort::new("K"), &subsorts).unwrap();
        assert!(matches!(
            plan.kind(),
            PlacementKind::SingletonK { item: None }
        ));
        use crate::kore::ast::{Pattern, Symbol};
        let app = |name: &str, arguments| Pattern::Application {
            symbol: Symbol {
                name: name.into(),
                sort_parameters: vec![],
            },
            arguments,
        };
        let item = app("Lbla", vec![]);
        let expected = app("kseq", vec![item.clone(), app("dotk", vec![])]);
        assert_eq!(plan.apply_kore(item, &[]), expected);
        let output = rendered(&sentences, "K", Mode::Lr).unwrap();
        assert!(
            output.contains("->symbol = \"kseq{}\""),
            "SingletonK action required; generated parser:\n{output}"
        );
        assert!(output.contains("->symbol = \"dotk{}\""));
        assert!(output.contains("value_type value = {.nterm = placed_kseq}"));
        assert!(output.contains("placed_kseq->children[0] = $1.nterm"));
        assert!(output.contains("placed_kseq->children[1] = placed_dotk"));
        assert!(output.contains("placed_kseq->sort = \"SortK{}\""));
        assert!(output.contains("placed_dotk->sort = \"SortK{}\""));
        assert!(output.contains("n->sort = \"SortKItem{}\""));
        assert!(output.contains("placed_kseq->location = @$"));
        assert!(output.contains("placed_kseq->hasLocation = 1"));
        assert!(output.contains("placed_dotk->hasLocation = 0"));
        assert!(!output.contains("inj{SortKItem{}, SortK{}}"));
        println!("SingletonK: returned kseq(a,dotk()); head sort KItem, sequence/tail sort K");
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

    /// Labels of the productions `sort` derives at its root in `productions`: its labeled
    /// productions and those of the sorts it derives through unlabeled subsort productions.
    /// Written apart from `derived_root_labels`, which the transformation itself uses.
    fn root_labels(productions: &[GrammarProduction], sort: &Sort) -> BTreeSet<String> {
        let mut labels = BTreeSet::new();
        let mut visited = BTreeSet::new();
        let mut pending = vec![sort.clone()];
        while let Some(sort) = pending.pop() {
            if !visited.insert(sort.clone()) {
                continue;
            }
            for production in productions.iter().filter(|p| p.result == sort) {
                match (&production.source, production.items.as_slice()) {
                    (
                        Sentence::Production { label: None, .. },
                        [ProductionItem::NonTerminal { sort, .. }],
                    ) => pending.push(sort.clone()),
                    (
                        Sentence::Production {
                            label: Some(label), ..
                        },
                        _,
                    ) => {
                        labels.insert(label.name.clone());
                    }
                    _ => {}
                }
            }
        }
        labels
    }

    /// The exported production of the source production labeled `label`.
    fn exported<'a>(productions: &'a [GrammarProduction], label: &str) -> &'a GrammarProduction {
        productions
            .iter()
            .find(|production| {
                let Sentence::Production {
                    sort,
                    label: Some(source),
                    ..
                } = &production.source
                else {
                    return false;
                };
                source.name == label && &production.result == sort
            })
            .unwrap_or_else(|| panic!("no exported production labeled {label}"))
    }

    fn operand(production: &GrammarProduction, index: usize) -> &Sort {
        let ProductionItem::NonTerminal { sort, .. } = &production.items[index] else {
            panic!("item {index} of {production:?} is not a nonterminal")
        };
        sort
    }

    /// `parser.bison.priorities`: the first and last operand of a labeled production derive, at
    /// their root, exactly the operand sort's productions minus the labels of lesser priority and
    /// those the associativity of that side excludes, also when an excluded production is
    /// reached through a subsort; an inner operand and a subsort the exclusion cannot reach stay
    /// unrestricted.
    #[test]
    fn restricted_operands_exclude_lesser_priority_and_associativity_through_subsorts() {
        let binary = |sort: &str, operator: &str, label: &str| {
            production(
                sort,
                vec![
                    nonterminal("Exp"),
                    ProductionItem::Terminal(operator.into()),
                    nonterminal("Exp"),
                ],
                Some(label),
                &[],
            )
        };
        let associativity = |associativity, tag: &str| Sentence::SyntaxAssociativity {
            associativity,
            tags: vec![tag.into()],
            attributes: Attributes::default(),
        };
        let sentences = vec![
            // `plus` reaches `Exp` through two subsort paths, `Mid` and `Mid` via `Wrap`.
            production("Exp", vec![nonterminal("Mid")], None, &[]),
            production("Mid", vec![nonterminal("Add")], None, &[]),
            production("Mid", vec![nonterminal("Wrap")], None, &[]),
            production("Wrap", vec![nonterminal("Add")], None, &[]),
            binary("Add", "+", "plus"),
            binary("Exp", "*", "mul"),
            binary("Exp", "^", "pow"),
            production(
                "Exp",
                vec![
                    ProductionItem::Terminal("(".into()),
                    nonterminal("Exp"),
                    ProductionItem::Terminal(")".into()),
                ],
                Some("paren"),
                &[],
            ),
            production("Exp", vec![nonterminal("Int")], None, &[]),
            production(
                "Int",
                vec![ProductionItem::Terminal("1".into())],
                Some("one"),
                &[],
            ),
            Sentence::SyntaxPriority {
                priorities: vec![vec!["pow".into()], vec!["mul".into()], vec!["plus".into()]],
                attributes: Attributes::default(),
            },
            associativity(Associativity::Left, "plus"),
            associativity(Associativity::NonAssoc, "mul"),
            associativity(Associativity::Right, "pow"),
        ];
        let productions = transform_priority_and_associativity(
            &sentences,
            prepare(&sentences).unwrap().productions,
        )
        .unwrap();

        let all = ["plus", "mul", "pow", "paren", "one"];
        let without = |excluded: &[&str]| {
            all.iter()
                .filter(|label| !excluded.contains(label))
                .map(|label| (*label).to_owned())
                .collect::<BTreeSet<_>>()
        };
        for (label, left, right) in [
            ("plus", &[][..], &["plus"][..]),
            ("mul", &["plus", "mul"][..], &["plus", "mul"][..]),
            ("pow", &["plus", "mul", "pow"][..], &["plus", "mul"][..]),
        ] {
            let production = exported(&productions, label);
            for (index, excluded) in [(0, left), (2, right)] {
                assert_eq!(
                    root_labels(&productions, operand(production, index)),
                    without(excluded),
                    "operand {index} of {label}"
                );
            }
        }
        assert_eq!(
            operand(exported(&productions, "paren"), 1),
            &Sort::new("Exp")
        );
        // Every sort a production uses has a production: a sort without one derives nothing.
        let defined = productions
            .iter()
            .map(|production| &production.result)
            .collect::<BTreeSet<_>>();
        for production in &productions {
            for sort in nonterminal_sorts(&production.items) {
                assert!(defined.contains(sort), "{sort} is used by {production:?}");
            }
        }
        // `Int` derives no excluded label, so every restricted sort keeps it as is.
        let int_parents = productions
            .iter()
            .filter(|production| grammar_subsort_child(production) == Some(&Sort::new("Int")))
            .count();
        let restricted_exp = productions
            .iter()
            .map(|production| &production.result)
            .filter(|sort| sort.name.starts_with("Exp#"))
            .collect::<BTreeSet<_>>();
        assert_eq!(int_parents, 1 + restricted_exp.len());
    }

    /// `parser.bison.priorities`: `applyPriority` names the operands priority restricts, in place
    /// of the first and last item. A named first or last item is also restricted by the
    /// associativity of its side; a named inner operand by priority alone; an unnamed first item
    /// is not restricted.
    #[test]
    fn apply_priority_names_the_operands_priority_restricts() {
        let exp = || nonterminal("Exp");
        let terminal = |text: &str| ProductionItem::Terminal(text.into());
        let sentences = vec![
            production(
                "Exp",
                vec![terminal("f("), exp(), terminal(","), exp(), terminal(")")],
                Some("f"),
                &[("applyPriority", "1")],
            ),
            production(
                "Exp",
                vec![exp(), terminal("?"), exp()],
                Some("q"),
                &[("applyPriority", "2")],
            ),
            production("Exp", vec![exp(), terminal("+"), exp()], Some("add"), &[]),
            production("Exp", vec![terminal("1")], Some("one"), &[]),
            Sentence::SyntaxPriority {
                priorities: vec![vec!["f".into(), "q".into()], vec!["add".into()]],
                attributes: Attributes::default(),
            },
            Sentence::SyntaxAssociativity {
                associativity: Associativity::Left,
                tags: vec!["f".into(), "q".into()],
                attributes: Attributes::default(),
            },
        ];
        let productions = transform_priority_and_associativity(
            &sentences,
            prepare(&sentences).unwrap().productions,
        )
        .unwrap();
        let labels = |names: &[&str]| {
            names
                .iter()
                .map(|name| (*name).to_owned())
                .collect::<BTreeSet<_>>()
        };
        let f = exported(&productions, "f");
        assert_eq!(
            root_labels(&productions, operand(f, 1)),
            labels(&["f", "q", "one"])
        );
        assert_eq!(operand(f, 3), &Sort::new("Exp"));
        let q = exported(&productions, "q");
        assert_eq!(operand(q, 0), &Sort::new("Exp"));
        assert_eq!(root_labels(&productions, operand(q, 2)), labels(&["one"]));
        let add = exported(&productions, "add");
        assert_eq!(operand(add, 0), &Sort::new("Exp"));
        assert_eq!(operand(add, 2), &Sort::new("Exp"));

        let invalid = [production(
            "Exp",
            vec![exp(), terminal("!")],
            Some("bang"),
            &[("applyPriority", "first")],
        )];
        let error =
            transform_priority_and_associativity(&invalid, prepare(&invalid).unwrap().productions)
                .unwrap_err();
        assert_eq!(
            error.to_string(),
            "production bang: invalid applyPriority value \"first\" in \"first\""
        );
    }

    /// `parser.bison.priorities` reads the in-process filter's exclusions
    /// (`inner::Exclusions`): a labelled production with one nonterminal and no terminal
    /// (`wrap`) writes nothing around its child, so it judges no edge and its operand stays
    /// unrestricted although `wrap` has greater priority than `add`; a prefix operator over the
    /// same sort is restricted. A sequence below a labelled constructor's end is outside its
    /// scope and is excluded there as a priority is, and a constructor its scope admits (here a
    /// sequence's own operand) keeps it.
    #[test]
    fn exported_operands_are_restricted_by_the_in_process_exclusions() {
        let exp = || nonterminal("Exp");
        let terminal = |text: &str| ProductionItem::Terminal(text.into());
        let sentences = vec![
            production("Top", vec![exp()], Some("wrap"), &[]),
            production("Exp", vec![terminal("-"), exp()], Some("neg"), &[]),
            production("Exp", vec![exp(), terminal("+"), exp()], Some("add"), &[]),
            production(
                "Exp",
                vec![exp(), terminal("~>"), exp()],
                Some("#KSequence"),
                &[],
            ),
            production("Exp", vec![terminal("1")], Some("one"), &[]),
            Sentence::SyntaxPriority {
                priorities: vec![vec!["wrap".into(), "neg".into()], vec!["add".into()]],
                attributes: Attributes::default(),
            },
        ];
        let productions = transform_priority_and_associativity(
            &sentences,
            prepare(&sentences).unwrap().productions,
        )
        .unwrap();
        let labels = |names: &[&str]| {
            names
                .iter()
                .map(|name| (*name).to_owned())
                .collect::<BTreeSet<_>>()
        };
        assert_eq!(
            operand(exported(&productions, "wrap"), 0),
            &Sort::new("Exp")
        );
        assert_eq!(
            root_labels(&productions, operand(exported(&productions, "neg"), 1)),
            labels(&["neg", "one"])
        );
        let add = exported(&productions, "add");
        assert_eq!(
            root_labels(&productions, operand(add, 0)),
            labels(&["add", "neg", "one"])
        );
        let sequence = exported(&productions, "#KSequence");
        assert_eq!(operand(sequence, 0), &Sort::new("Exp"));
        assert_eq!(operand(sequence, 2), &Sort::new("Exp"));
    }

    /// `parser.bison.priorities`: a production that restriction leaves deriving nothing is not
    /// exported, also when it is a source production over a sort that restriction left without
    /// productions: here `q`'s last operand may not derive `add`, so it derives nothing, so `q`
    /// and then `Zoo` derive nothing. A production that derives nothing in the source grammar
    /// (`ghost`) is the definition's own and is kept.
    #[test]
    fn productions_restriction_leaves_deriving_nothing_are_not_exported() {
        let terminal = |text: &str| ProductionItem::Terminal(text.into());
        let sentences = vec![
            production("Num", vec![terminal("1")], Some("one"), &[]),
            production("Zpgm", vec![nonterminal("Num")], None, &[]),
            production("Zpgm", vec![nonterminal("Zoo")], None, &[]),
            production("Zpgm", vec![nonterminal("S")], None, &[]),
            production(
                "Zpgm",
                vec![nonterminal("Ghost"), terminal("!")],
                Some("ghost"),
                &[],
            ),
            production("S", vec![nonterminal("Add")], None, &[]),
            production(
                "Add",
                vec![nonterminal("Zpgm"), terminal("+"), nonterminal("Zpgm")],
                Some("add"),
                &[],
            ),
            production(
                "Zoo",
                vec![nonterminal("Zpgm"), terminal("?"), nonterminal("S")],
                Some("q"),
                &[],
            ),
            Sentence::SyntaxPriority {
                priorities: vec![vec!["q".into()], vec!["add".into()]],
                attributes: Attributes::default(),
            },
        ];
        let productions = transform_priority_and_associativity(
            &sentences,
            prepare(&sentences).unwrap().productions,
        )
        .unwrap();
        let defined = productions
            .iter()
            .map(|production| &production.result)
            .collect::<BTreeSet<_>>();
        for production in &productions {
            for sort in nonterminal_sorts(&production.items) {
                assert!(
                    defined.contains(sort) || sort == &Sort::new("Ghost"),
                    "{sort} is used by {production:?}"
                );
            }
        }
        let exported_labels = productions
            .iter()
            .filter_map(|production| production_label(&production.source))
            .map(|label| label.name.as_str())
            .collect::<BTreeSet<_>>();
        assert!(!exported_labels.contains("q"), "{productions:#?}");
        assert!(exported_labels.contains("ghost"), "{productions:#?}");
        assert!(defined.contains(&Sort::new("Add")));
        assert!(!defined.contains(&Sort::new("Zoo")));
    }

    /// Only the useful grammar is rendered: a production with an operand of a sort that derives
    /// no program (`Cfg`, which has no productions) is left out, and so are the sorts only such
    /// productions reach (`Hidden`) and the declaration of each; the start sort keeps its other
    /// productions. Such a production is still checked: one without a semantic action is an
    /// error although it could take part in no parse.
    #[test]
    fn only_the_useful_grammar_is_rendered_and_each_reachable_production_is_checked() {
        let terminal = |text: &str| ProductionItem::Terminal(text.into());
        let mut sentences = vec![
            syntax_sort("Cfg", &[]),
            production("Pgm", vec![nonterminal("Exp")], None, &[]),
            production("Pgm", vec![nonterminal("Cfg")], None, &[]),
            production(
                "Pgm",
                vec![nonterminal("Cfg"), terminal("!"), nonterminal("Hidden")],
                Some("bang"),
                &[],
            ),
            production("Exp", vec![terminal("1")], Some("one"), &[]),
            production("Hidden", vec![terminal("h")], Some("hidden"), &[]),
        ];
        for mode in [Mode::Lr, Mode::Glr] {
            let output = rendered(&sentences, "Pgm", mode).unwrap();
            let rules = output.split("\n%%\n").nth(1).unwrap();
            let rule_heads = rules
                .lines()
                .filter(|line| line.ends_with(':'))
                .collect::<Vec<_>>();
            assert_eq!(rule_heads, ["SortExp__:", "SortPgm__:"], "{rules}");
            assert!(
                !rules.contains("SortCfg__") && !rules.contains("SortHidden__"),
                "{rules}"
            );
            assert!(!rules.contains("Lblbang") && !rules.contains("Lblhidden"));
            assert!(
                !output.contains("%nterm SortCfg__") && !output.contains("%nterm SortHidden__")
            );
            assert!(output.contains("%nterm SortPgm__") && output.contains("%nterm SortExp__"));
        }
        sentences.push(production(
            "Pgm",
            vec![nonterminal("Cfg"), terminal("?"), nonterminal("Cfg")],
            None,
            &[],
        ));
        assert_eq!(
            rendered(&sentences, "Pgm", Mode::Lr)
                .unwrap_err()
                .to_string(),
            "production for Pgm has no Bison semantic action"
        );
    }

    /// `parser.bison.priorities`, `prepare_user_lists`: a user list that is not one recursive and
    /// one terminator production of the same `+` or `*` kind, with the list on one side, is
    /// rejected; a formal parametric list is kept unlowered.
    #[test]
    fn user_lists_are_validated_and_formal_lists_are_kept() {
        let recursive = |items: Vec<ProductionItem>, label: Option<&str>, kind: &str| {
            production("Es", items, label, &[("userList", kind)])
        };
        let right = || {
            vec![
                nonterminal("E"),
                ProductionItem::Terminal(",".into()),
                nonterminal("Es"),
            ]
        };
        let left = || {
            vec![
                nonterminal("Es"),
                ProductionItem::Terminal(",".into()),
                nonterminal("E"),
            ]
        };
        let terminator = |label: Option<&str>, kind: &str| {
            production(
                "Es",
                vec![ProductionItem::Terminal(".Es".into())],
                label,
                &[("userList", kind)],
            )
        };
        for (members, message) in [
            (
                vec![
                    recursive(right(), Some("cons"), "*"),
                    recursive(right(), Some("cons2"), "*"),
                    terminator(Some("nil"), "*"),
                ],
                "expected one recursive and one terminator production",
            ),
            (
                vec![recursive(right(), Some("cons"), "*")],
                "expected one recursive and one terminator production",
            ),
            (
                vec![recursive(right(), None, "*"), terminator(Some("nil"), "*")],
                "recursive production has no constructor label",
            ),
            (
                vec![recursive(right(), Some("cons"), "*"), terminator(None, "*")],
                "terminator production has no constructor label",
            ),
            (
                vec![
                    recursive(right(), Some("cons"), "+"),
                    terminator(Some("nil"), "*"),
                ],
                "recursive and terminator productions must have the same `+` or `*` userList attribute",
            ),
            (
                vec![
                    recursive(right(), Some("cons"), "?"),
                    terminator(Some("nil"), "?"),
                ],
                "recursive and terminator productions must have the same `+` or `*` userList attribute",
            ),
            (
                vec![
                    recursive(
                        vec![
                            nonterminal("E"),
                            ProductionItem::Terminal(",".into()),
                            nonterminal("E"),
                        ],
                        Some("cons"),
                        "*",
                    ),
                    terminator(Some("nil"), "*"),
                ],
                "recursive production must contain the list sort on exactly one side",
            ),
            (
                vec![
                    recursive(left(), Some("cons"), "*"),
                    terminator(Some("nil"), "*"),
                ],
                "left-associative `List` is not supported by K's Bison transform",
            ),
        ] {
            let error = prepare(&members).map(|_| ()).unwrap_err().to_string();
            assert_eq!(error, format!("invalid user list Es: {message}"));
        }
        for members in [
            vec![
                recursive(right(), Some("cons"), "*"),
                terminator(Some("nil"), "*"),
            ],
            vec![
                recursive(left(), Some("cons"), "+"),
                terminator(Some("nil"), "+"),
            ],
        ] {
            assert!(prepare(&members).is_ok(), "{members:?}");
        }

        let parameter = Sort::new("T");
        let formal = |items: Vec<ProductionItem>, label: &str| Sentence::Production {
            label: Some(Label::with_parameters(label, vec![parameter.clone()])),
            parameters: vec![parameter.clone()],
            sort: Sort::with_parameters("Ps", vec![parameter.clone()]),
            items,
            attributes: attributes(&[("userList", "*")]),
        };
        let parametric_list = Sort::with_parameters("Ps", vec![parameter.clone()]);
        let members = vec![
            formal(
                vec![
                    ProductionItem::NonTerminal {
                        sort: parameter.clone(),
                        name: None,
                    },
                    ProductionItem::Terminal(",".into()),
                    ProductionItem::NonTerminal {
                        sort: parametric_list.clone(),
                        name: None,
                    },
                ],
                "pcons",
            ),
            formal(vec![ProductionItem::Terminal(".Ps".into())], "pnil"),
        ];
        let prepared = prepare(&members).unwrap();
        assert_eq!(
            prepared
                .productions
                .iter()
                .map(|production| (production.result.clone(), production.source.clone()))
                .collect::<Vec<_>>(),
            members
                .iter()
                .map(|member| (parametric_list.clone(), member.clone()))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn user_list_bridge_returns_cons_without_an_unused_injection() {
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

        assert!(!output.contains("inj{SortElem{}, SortList{}}"));
        assert_eq!(output.matches("malloc(").count(), 3); // Elem, nil and cons.
        assert!(output.contains("value_type value = {.nterm = n3}"));
        assert!(output.contains("n3->sort = \"SortList{}\""));
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
    fn a_list_whose_constructor_takes_the_list_first_is_read_by_that_production() {
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
    fn left_recursion_reads_a_possibly_empty_list_and_builds_it_with_its_constructor() {
        let sentences = vec![
            production(
                "Exps",
                vec![
                    nonterminal("Exp"),
                    ProductionItem::Terminal(",".into()),
                    nonterminal("Exps"),
                ],
                Some("cons"),
                &[("userList", "*")],
            ),
            production(
                "Exps",
                vec![ProductionItem::Terminal(".Exps".into())],
                Some("nil"),
                &[("userList", "*")],
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

        let list = encode_bison_sort(&Sort::new("Exps"));
        let prefix = encode_bison_sort(&Sort::new("Ne#Exps"));
        let terminator = encode_bison_sort(&Sort::new("Exps#Terminator"));
        let exp = encode_bison_sort(&Sort::new("Exp"));
        assert!(output.contains(&format!("{prefix}:\n  {exp} {{")));
        assert!(output.contains(&format!("  |{prefix} TOK_")));
        assert!(output.contains(&format!(
            "{list}:\n  {terminator} {{\n  $$ = $1;\n}}\n\n  |{prefix} {terminator} {{"
        )));
        assert!(output.contains(&format!(
            "static node *krust_list_{list}(node *prefix, node *rest, YYLTYPE end)"
        )));
        assert!(output.contains("    n->symbol = \"Lblcons{}\";"));
        assert!(output.contains("    n->children[0] = prefix->children[0];"));
        assert!(output.contains("    n->children[1] = rest;"));
        assert!(output.contains(&format!("krust_list_{list}($1.nterm, $2.nterm, @$)")));
    }

    #[test]
    fn a_list_separated_by_nothing_reads_each_element_after_its_prefix() {
        let sentences = vec![
            production(
                "Exps",
                vec![
                    nonterminal("Exp"),
                    ProductionItem::Terminal(String::new()),
                    nonterminal("Exps"),
                ],
                Some("cons"),
                &[("userList", "+")],
            ),
            production(
                "Exps",
                vec![ProductionItem::Terminal(String::new())],
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

        let output = render(&prepared, &scanner, &Sort::new("Exps"), Mode::Glr, 321).unwrap();

        let prefix = encode_bison_sort(&Sort::new("Ne#Exps"));
        let exp = encode_bison_sort(&Sort::new("Exp"));
        assert!(
            output.contains(&format!("  |{prefix} {exp} {{")),
            "{output}"
        );
        assert!(output.contains("  n->location = @2;"));
        assert!(output.contains("  n->children[0] = $2.nterm;\n  n->children[1] = $1.nterm;"));
        assert!(!output.contains("$3"));
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
    fn overload_guard_and_dispatch_share_each_recovery_case() {
        let sentences = vec![
            production(
                "S",
                vec![ProductionItem::Terminal("s".into())],
                Some("s"),
                &[],
            ),
            production(
                "Same",
                vec![ProductionItem::Terminal("z".into())],
                Some("z"),
                &[],
            ),
            production("Mid", vec![nonterminal("S")], None, &[]),
            production("KItem", vec![nonterminal("Mid")], None, &[]),
            production("K", vec![nonterminal("KItem")], None, &[]),
            production("KList", vec![nonterminal("K")], None, &[]),
            production(
                "R",
                vec![
                    ProductionItem::Terminal("f".into()),
                    nonterminal("Mid"),
                    nonterminal("K"),
                    nonterminal("Same"),
                    nonterminal("Mid"),
                ],
                Some("fSmall"),
                &[("klabel", "f")],
            ),
            production(
                "R",
                vec![
                    ProductionItem::Terminal("f".into()),
                    nonterminal("K"),
                    nonterminal("KList"),
                    nonterminal("Same"),
                    nonterminal("K"),
                ],
                Some("fBig"),
                &[("klabel", "f")],
            ),
        ];
        let output = rendered(&sentences, "R", Mode::Lr).unwrap();
        let subsorts = compute_subsorts(sentences.iter(), false).unwrap();
        let sorts = module_sorts(&sentences);
        let placements = CPlacement {
            subsorts: &subsorts,
            sorts: &sorts,
            location: "@$",
            has_location: "0",
            prefix: "placed",
        };
        let mut total = 0;
        let mut previous_recovery = None;
        for (index, greater, lesser) in [(0, "K", "Mid"), (1, "KList", "K"), (3, "K", "Mid")] {
            let cases = recovery_cases(
                &placements,
                &Sort::new(greater),
                &Sort::new(lesser),
                &format!("${}.nterm", index + 2),
            );
            assert!(cases.len() > 1);
            let mut chain = format!("  int matched_case_{index} = -1;\n");
            if let Some(previous) = previous_recovery {
                writeln!(chain, "  if (matched_case_{previous} >= 0) {{").unwrap();
            }
            for (ordinal, case) in cases.iter().enumerate() {
                let count = output.matches(&case.condition).count();
                assert_eq!(
                    count, 1,
                    "recovery condition emitted {count} times; expected once"
                );
                assert!(output.contains(&format!("matched_case_{index} = {ordinal};")));
                assert!(output.contains(&format!("if (matched_case_{index} == {ordinal})")));
                writeln!(
                    chain,
                    "  {}if ({}) {{ matched_case_{index} = {ordinal}; }}",
                    if ordinal == 0 { "" } else { "else " },
                    case.condition
                )
                .unwrap();
                total += 1;
            }
            if previous_recovery.is_some() {
                chain.push_str("  }\n");
            }
            assert!(
                output.contains(&chain),
                "argument {index} recovery must short-circuit after the previous missed argument"
            );
            previous_recovery = Some(index);
            assert!(output.contains(&format!("int matched_case_{index} = -1;")));
            assert!(output.contains(&format!(" && matched_case_{index} >= 0")));
        }
        assert!(output.contains("n->children[2] = $4.nterm;"));
        assert!(!output.contains("matched_case_2"));
        println!(
            "{total} recovery conditions emitted once; later arguments short-circuit; guard and dispatch read the same matched cases"
        );
    }

    #[test]
    fn overloads_emit_runtime_downcast_checks() {
        let sentences = vec![
            production("Big", vec![nonterminal("Small")], None, &[]),
            production("BigArg", vec![nonterminal("SmallArg")], None, &[]),
            // A program of the argument sort, so the start sort has programs.
            production(
                "SmallArg",
                vec![ProductionItem::Terminal("s".into())],
                Some("s"),
                &[],
            ),
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

        assert!(
            output
                .contains("strcmp(($2.nterm)->symbol, \"inj{SortSmallArg{}, SortBigArg{}}\") == 0")
        );
        assert!(output.contains("n->symbol = \"LblfSmall{}\""));
        assert!(output.contains("placed_injection->symbol = \"inj{SortSmall{}, SortBig{}}\""));
        assert!(output.contains("value_type value = {.nterm = placed_injection}"));
        assert!(!output.contains("injSymbol("));
    }

    fn kore_app(
        name: &str,
        arguments: Vec<crate::kore::ast::Pattern>,
    ) -> crate::kore::ast::Pattern {
        crate::kore::ast::Pattern::Application {
            symbol: crate::kore::ast::Symbol {
                name: name.into(),
                sort_parameters: vec![],
            },
            arguments,
        }
    }

    #[test]
    fn nested_item_and_above_k_placements_preserve_sequence_structure() {
        let sentences = vec![
            production("KList", vec![nonterminal("K")], None, &[]),
            production("K", vec![nonterminal("KItem")], None, &[]),
            production("KItem", vec![nonterminal("S")], None, &[]),
            production(
                "S",
                vec![ProductionItem::Terminal("a".into())],
                Some("a"),
                &[],
            ),
        ];
        let order = compute_subsorts(sentences.iter(), false).unwrap();
        let item = kore_app("Lbla", vec![]);
        let item_plan = Placement::between(&Sort::new("S"), &Sort::new("KItem"), &order).unwrap();
        assert!(matches!(item_plan.kind(), PlacementKind::Injection(_)));
        let item = item_plan.apply_kore(item, &[]);
        let singleton = Placement::between(&Sort::new("KItem"), &Sort::new("K"), &order)
            .unwrap()
            .apply_kore(item.clone(), &[]);
        assert_eq!(
            singleton,
            kore_app("kseq", vec![item, kore_app("dotk", vec![])])
        );
        let plan = Placement::between(&Sort::new("K"), &Sort::new("KList"), &order).unwrap();
        assert!(
            matches!(plan.kind(), PlacementKind::Injection(w) if w.source() == &Sort::new("K"))
        );
        let placed = plan.apply_kore(singleton.clone(), &[]);
        let crate::kore::ast::Pattern::Application { arguments, .. } = &placed else {
            panic!("expected injection")
        };
        assert_eq!(arguments, &[singleton]);
        let output = rendered(&sentences, "KList", Mode::Lr).unwrap();
        assert!(output.contains("value_type value = {.nterm = placed_kseq}"));
        assert!(output.contains("placed_kseq->children[0] = $1.nterm"));
        assert!(output.contains("inj{SortS{}, SortKItem{}}"));
        assert!(output.contains("inj{SortK{}, SortKList{}}"));
        assert!(!output.contains("inj{SortS{}, SortKList{}}"));
        assert!(!output.contains("inj{SortKItem{}, SortK{}}"));
        assert!(!output.contains("injSymbol("));
    }

    #[test]
    fn equal_result_overload_returns_the_lesser_application_directly() {
        let sentences = vec![
            production("BigArg", vec![nonterminal("SmallArg")], None, &[]),
            // A program of the argument sort, so the start sort has programs.
            production(
                "SmallArg",
                vec![ProductionItem::Terminal("s".into())],
                Some("s"),
                &[],
            ),
            production(
                "R",
                vec![
                    ProductionItem::Terminal("f".into()),
                    nonterminal("SmallArg"),
                ],
                Some("fSmall"),
                &[("klabel", "f")],
            ),
            production(
                "R",
                vec![ProductionItem::Terminal("f".into()), nonterminal("BigArg")],
                Some("fBig"),
                &[("klabel", "f")],
            ),
        ];
        let order = compute_subsorts(sentences.iter(), false).unwrap();
        let plan = Placement::between(&Sort::new("R"), &Sort::new("R"), &order).unwrap();
        assert_eq!(plan.kind(), &PlacementKind::Identity);
        let app = kore_app("LblfSmall", vec![kore_app("LbLa", vec![])]);
        assert_eq!(plan.apply_kore(app.clone(), &[]), app);
        let output = rendered(&sentences, "R", Mode::Lr).unwrap();
        let branch = output.split("n->symbol = \"LblfSmall{}\"").last().unwrap();
        assert!(branch.contains("value_type value = {.nterm = n}"));
        assert!(!output.contains("inj{SortR{}, SortR{}}"));
        assert!(!output.contains("injSymbol("));
    }

    #[test]
    fn overload_k_argument_recovers_only_a_canonical_singleton() {
        let sentences = vec![
            production("K", vec![nonterminal("KItem")], None, &[]),
            // A program of the argument sort, so the start sort has programs.
            production(
                "KItem",
                vec![ProductionItem::Terminal("a".into())],
                Some("a"),
                &[],
            ),
            production(
                "R",
                vec![ProductionItem::Terminal("f".into()), nonterminal("KItem")],
                Some("fItem"),
                &[("klabel", "f")],
            ),
            production(
                "R",
                vec![ProductionItem::Terminal("f".into()), nonterminal("K")],
                Some("fK"),
                &[("klabel", "f")],
            ),
        ];
        let order = compute_subsorts(sentences.iter(), false).unwrap();
        let plan = Placement::between(&Sort::new("KItem"), &Sort::new("K"), &order).unwrap();
        let shape = RecoveryShape::from_plan(&Sort::new("KItem"), &plan, &order);
        let item = kore_app("Lbla", vec![]);
        let singleton = plan.apply_kore(item.clone(), &[]);
        assert_eq!(shape.recover(&singleton), Some(&item));
        let empty = kore_app("dotk", vec![]);
        assert_eq!(shape.recover(&empty), None);
        let multi = kore_app("kseq", vec![item.clone(), singleton]);
        assert_eq!(shape.recover(&multi), None);
        let arbitrary_k = kore_app("LblkFunction", vec![]);
        assert_eq!(shape.recover(&arbitrary_k), None);
        let output = rendered(&sentences, "R", Mode::Lr).unwrap();
        assert!(output.contains("n->symbol = \"LblfItem{}\""));
        assert!(output.contains("strcmp((($2.nterm)->children[1])->symbol, \"dotk{}\") == 0"));
        assert!(output.contains("n->children[0] = ($2.nterm)->children[0]"));
        assert!(!output.contains("inj{SortKItem{}, SortK{}}"));
    }

    #[test]
    fn overload_recovery_reinjects_only_witnessed_sources_and_preserves_whole_k() {
        let order = crate::definition::PartialOrder::new([
            (Sort::new("S"), Sort::new("Mid")),
            (Sort::new("Mid"), Sort::new("Upper")),
            (Sort::new("KItem"), Sort::new("K")),
            (Sort::new("K"), Sort::new("KList")),
        ])
        .unwrap();
        let sorts = BTreeSet::from([
            Sort::new("S"),
            Sort::new("Mid"),
            Sort::new("Upper"),
            Sort::new("K"),
            Sort::new("KItem"),
            Sort::new("KList"),
        ]);
        let emitter = CPlacement {
            location: "location",
            has_location: "1",
            prefix: "recovered",
            subsorts: &order,
            sorts: &sorts,
        };
        let cases = recovery_cases(&emitter, &Sort::new("Upper"), &Sort::new("Mid"), "arg");
        assert_eq!(cases.len(), 2);
        let source_case = cases.iter().find(|case| matches!(case.placement.kind(), PlacementKind::Injection(w) if w.source() == &Sort::new("S"))).unwrap();
        let mut output = String::new();
        let returned = emitter.write(&mut output, &source_case.placement, &source_case.child);
        assert_eq!(returned, "recovered_injection");
        assert!(output.contains("inj{SortS{}, SortMid{}}"));
        assert!(source_case.condition.contains("inj{SortS{}, SortUpper{}}"));
        let plan = Placement::between(&Sort::new("K"), &Sort::new("KList"), &order).unwrap();
        let shape = RecoveryShape::from_plan(&Sort::new("K"), &plan, &order);
        let whole = kore_app(
            "kseq",
            vec![
                kore_app("a", vec![]),
                kore_app(
                    "kseq",
                    vec![kore_app("b", vec![]), kore_app("dotk", vec![])],
                ),
            ],
        );
        let embedded = plan.apply_kore(whole.clone(), &[]);
        assert_eq!(shape.recover(&embedded), Some(&whole));
        let output_cases = recovery_cases(&emitter, &Sort::new("KList"), &Sort::new("K"), "arg");
        assert!(
            output_cases
                .iter()
                .any(|case| case.child == "(arg)->children[0]"
                    && case.placement.kind() == &PlacementKind::Identity)
        );
    }

    #[test]
    fn singleton_overload_recovery_reinjects_a_narrower_item_with_a_witness() {
        let order = crate::definition::PartialOrder::new([
            (Sort::new("S"), Sort::new("Mid")),
            (Sort::new("KItem"), Sort::new("K")),
        ])
        .unwrap();
        let source = Sort::new("S");
        let placement = Placement::between(&source, &Sort::new("Mid"), &order).unwrap();
        let outer = Placement::between(&Sort::new("Mid"), &Sort::new("K"), &order).unwrap();
        let shape = RecoveryShape::from_plan(&source, &placement, &order).wrap(&outer, &order);
        let item = kore_app("Lbla", vec![]);
        // Consecutive witnessed item injections compact to S -> KItem.
        let direct = Placement::between(&source, &Sort::new("K"), &order)
            .unwrap()
            .apply_kore(item.clone(), &[]);
        assert_eq!(shape.recover(&direct), Some(&item));
        let recovered = shape.recover(&direct).unwrap().clone();
        let placed = placement.clone().apply_kore(recovered, &[]);
        let crate::kore::ast::Pattern::Application { symbol, arguments } = &placed else {
            panic!("expected witnessed injection")
        };
        assert_eq!(
            symbol.sort_parameters,
            [
                encode_kore_sort(&source),
                encode_kore_sort(&Sort::new("Mid"))
            ]
        );
        assert_eq!(arguments, &[item]);
        let sorts = BTreeSet::from([source, Sort::new("Mid"), Sort::new("KItem"), Sort::new("K")]);
        let emitter = CPlacement {
            location: "location",
            has_location: "1",
            prefix: "r",
            subsorts: &order,
            sorts: &sorts,
        };
        let cases = recovery_cases(&emitter, &Sort::new("K"), &Sort::new("Mid"), "arg");
        let case = cases.iter().find(|case| matches!(case.placement.kind(), PlacementKind::Injection(w) if w.source() == &Sort::new("S"))).unwrap();
        assert!(case.condition.contains("dotk{}"));
        assert!(case.condition.contains("inj{SortS{}, SortKItem{}}"));
        let mut code = String::new();
        let returned = emitter.write(&mut code, &case.placement, &case.child);
        assert_eq!(returned, "r_injection");
        assert!(code.contains("inj{SortS{}, SortMid{}}"));
        assert!(!code.contains("injSymbol("));
    }

    #[test]
    fn recovery_follows_composed_placements_without_crossing_k_as_an_injection() {
        let order = crate::definition::PartialOrder::new([
            (Sort::new("S"), Sort::new("G")),
            (Sort::new("KItem"), Sort::new("K")),
            (Sort::new("K"), Sort::new("G")),
        ])
        .unwrap();
        let source = Sort::new("S");
        let lesser = Placement::between(&source, &Sort::new("K"), &order).unwrap();
        let outer = Placement::between(&Sort::new("K"), &Sort::new("G"), &order).unwrap();
        let shape = RecoveryShape::from_plan(&source, &lesser, &order).wrap(&outer, &order);
        let value = kore_app("Lbla", vec![]);
        let wrong_route = Placement::between(&source, &Sort::new("G"), &order)
            .unwrap()
            .apply_kore(value.clone(), &[]);
        assert_eq!(shape.recover(&wrong_route), None);
        let right_route = outer.apply_kore(lesser.apply_kore(value.clone(), &[]), &[]);
        assert_eq!(shape.recover(&right_route), Some(&value));
        let sorts = BTreeSet::from([source, Sort::new("K"), Sort::new("KItem"), Sort::new("G")]);
        let emitter = CPlacement {
            location: "location",
            has_location: "1",
            prefix: "p",
            subsorts: &order,
            sorts: &sorts,
        };
        let cases = recovery_cases(&emitter, &Sort::new("G"), &Sort::new("K"), "arg");
        assert!(
            cases
                .iter()
                .all(|case| !case.condition.contains("inj{SortS{}, SortG{}}"))
        );
        assert!(cases.iter().any(|case| case.condition.contains("kseq{}")));
    }

    #[test]
    fn parsing_only_bridge_returns_the_recognized_value_unchanged() {
        let sentences = vec![
            production(
                "Target",
                vec![nonterminal("Source")],
                None,
                &[("#bisonParsingOnlySubsort", "")],
            ),
            production(
                "Source",
                vec![ProductionItem::Terminal("x".into())],
                Some("x"),
                &[],
            ),
        ];
        let output = rendered(&sentences, "Target", Mode::Lr).unwrap();
        let target = output.split("SortTarget__:\n").nth(1).unwrap();
        let alternative = target.split("\n;\n").next().unwrap();
        assert!(alternative.contains("SortSource__ {\n  $$ = $1;\n}"));
        assert!(!output.contains("inj{SortSource{}, SortTarget{}}"));
    }

    #[test]
    fn unlicensed_subsort_reports_the_production_and_location() {
        let mut sentence = production(
            "K",
            vec![nonterminal("KLabel")],
            None,
            &[(AttributeKey::Source.as_str(), "bad.k")],
        );
        sentence
            .attributes_mut()
            .insert(AttributeKey::Location.as_str(), json!([2, 1, 2, 10]));
        let error = rendered(&[sentence], "K", Mode::Lr)
            .unwrap_err()
            .to_string();
        assert_eq!(
            error,
            "unlicensed parser placement KLabel -> K in production syntax K ::= KLabel at bad.k (2,1,2,10)"
        );
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

    /// A start sort whose every production needs a program of a sort that has none (here only
    /// itself, as a sort declared bare whose only production in the syntax module is a
    /// conditional over it) has no programs; the export reports the sort and the productions
    /// instead of handing Bison a start symbol that derives no sentence.
    #[test]
    fn rejects_a_start_sort_that_derives_no_program() {
        let terminal = |text: &str| ProductionItem::Terminal(text.into());
        let sentences = vec![
            production("Bool", vec![terminal("true")], Some("true"), &[]),
            production(
                "Sim",
                vec![
                    terminal("#if"),
                    nonterminal("Bool"),
                    terminal("#then"),
                    nonterminal("Sim"),
                    terminal("#else"),
                    nonterminal("Sim"),
                    terminal("#fi"),
                ],
                Some("ite"),
                &[],
            ),
            production("Pgm", vec![nonterminal("Sim")], None, &[]),
            production("Pgm", vec![terminal("skip")], Some("skip"), &[]),
        ];

        for mode in [Mode::Lr, Mode::Glr] {
            let error = rendered(&sentences, "Sim", mode).unwrap_err();
            assert_eq!(
                error.to_string(),
                "program start sort Sim derives no program: each of its productions needs a sort that derives none (\"#if\" Bool \"#then\" Sim \"#else\" Sim \"#fi\" needs Sim)"
            );
        }
        // A sort with programs beside the empty one still exports, without the empty sort.
        let output = rendered(&sentences, "Pgm", Mode::Lr).unwrap();
        assert!(output.contains("top: SortPgm__"), "{output}");
    }

    /// `parser.bison.priorities` against the priority filter K's documentation defines ("Symbol
    /// priority and associativity" in the K user manual), over random small grammars.
    ///
    /// The filter judges a tree: at each checked operand of a labelled production that is not a
    /// syntactic subsort (the positions `applyPriority` lists, else the first and the last item
    /// when it is a nonterminal), the
    /// child's root label, read through the subsort productions that the program text does not
    /// show, must not be of lesser priority than the parent, and associativity excludes a child
    /// of the same group at the last item (left) or the first item (right). The exported grammar
    /// must derive exactly the source grammar's trees that the filter allows, and hold no rule
    /// that derives nothing unless the source grammar's rule already does.
    mod priority_properties {
        use proptest::prelude::*;

        use super::*;

        #[derive(Clone, Debug)]
        enum Shape {
            Infix(usize, usize),
            Prefix(usize),
            Postfix(usize),
            Closed(usize),
            Pair(usize, usize),
            /// A labelled production with one nonterminal and no terminal.
            Wrap(usize),
        }

        #[derive(Clone, Debug)]
        struct Operator {
            result: usize,
            shape: Shape,
            apply_priority: Option<BTreeSet<usize>>,
        }

        #[derive(Clone, Debug)]
        struct RandomGrammar {
            sorts: usize,
            subsorts: BTreeSet<(usize, usize)>,
            atoms: BTreeSet<usize>,
            operators: Vec<Operator>,
            priorities: Vec<(usize, usize)>,
            associativities: Vec<(Associativity, BTreeSet<usize>)>,
        }

        fn sort(index: usize) -> String {
            format!("S{index}")
        }

        fn label(index: usize) -> String {
            format!("l{index}")
        }

        fn random_grammar() -> impl Strategy<Value = RandomGrammar> {
            (2usize..=4).prop_flat_map(|sorts| {
                // A wrap whose child's sort index is not above its result's becomes a prefix
                // (below), so wraps are drawn more often than the other shapes.
                let shape = prop_oneof![
                    1 => (0..sorts, 0..sorts).prop_map(|(left, right)| Shape::Infix(left, right)),
                    1 => (0..sorts).prop_map(Shape::Prefix),
                    1 => (0..sorts).prop_map(Shape::Postfix),
                    1 => (0..sorts).prop_map(Shape::Closed),
                    1 => (0..sorts, 0..sorts).prop_map(|(left, right)| Shape::Pair(left, right)),
                    3 => (0..sorts).prop_map(Shape::Wrap),
                ];
                let operator = (
                    0..sorts,
                    shape,
                    proptest::option::weighted(
                        0.3,
                        proptest::collection::btree_set(1usize..=2, 1..=2),
                    ),
                )
                    .prop_map(|(result, shape, apply_priority)| Operator {
                        result,
                        // Only a wrap from a lower to a higher index, as subsorts, so unary
                        // chains are acyclic.
                        shape: match shape {
                            Shape::Wrap(child) if child <= result => Shape::Prefix(child),
                            shape @ (Shape::Infix(..)
                            | Shape::Prefix(_)
                            | Shape::Postfix(_)
                            | Shape::Closed(_)
                            | Shape::Pair(..)
                            | Shape::Wrap(_)) => shape,
                        },
                        apply_priority,
                    });
                (
                    proptest::collection::btree_set((0..sorts, 0..sorts), 0..=3),
                    proptest::collection::btree_set(0..sorts, 1..=sorts),
                    proptest::collection::vec(operator, 1..=5),
                    proptest::collection::vec((0usize..5, 0usize..5), 0..=4),
                    proptest::collection::vec(
                        (
                            prop_oneof![
                                Just(Associativity::Left),
                                Just(Associativity::Right),
                                Just(Associativity::NonAssoc),
                            ],
                            proptest::collection::btree_set(0usize..5, 1..=3),
                        ),
                        0..=2,
                    ),
                )
                    .prop_map(
                        move |(subsorts, atoms, operators, priorities, associativities)| {
                            let count = operators.len();
                            RandomGrammar {
                                sorts,
                                // Only edges from a lower to a higher index, so subsorts are
                                // acyclic.
                                subsorts: subsorts
                                    .into_iter()
                                    .filter(|(parent, child)| parent < child)
                                    .collect(),
                                atoms,
                                // Only edges from a lower to a higher label, so priorities are
                                // acyclic.
                                priorities: priorities
                                    .into_iter()
                                    .map(|(higher, lower)| (higher % count, lower % count))
                                    .filter(|(higher, lower)| higher < lower)
                                    .collect(),
                                associativities: associativities
                                    .into_iter()
                                    .map(|(associativity, members)| {
                                        (
                                            associativity,
                                            members
                                                .into_iter()
                                                .map(|index| index % count)
                                                .collect(),
                                        )
                                    })
                                    .collect(),
                                operators,
                            }
                        },
                    )
            })
        }

        impl Operator {
            fn items(&self, index: usize) -> Vec<ProductionItem> {
                let terminal = |text: String| ProductionItem::Terminal(text);
                let operand = |sort_index: usize| nonterminal(&sort(sort_index));
                match self.shape {
                    Shape::Infix(left, right) => {
                        vec![operand(left), terminal(format!("o{index}")), operand(right)]
                    }
                    Shape::Prefix(child) => vec![terminal(format!("o{index}")), operand(child)],
                    Shape::Postfix(child) => vec![operand(child), terminal(format!("o{index}"))],
                    Shape::Closed(child) => vec![
                        terminal(format!("o{index}(")),
                        operand(child),
                        terminal(")".into()),
                    ],
                    Shape::Wrap(child) => vec![operand(child)],
                    Shape::Pair(left, right) => vec![
                        terminal(format!("o{index}(")),
                        operand(left),
                        terminal(",".into()),
                        operand(right),
                        terminal(")".into()),
                    ],
                }
            }
        }

        impl RandomGrammar {
            fn sentences(&self) -> Vec<Sentence> {
                let mut sentences = vec![
                    syntax_sort("T", &[]),
                    production(
                        "T",
                        vec![ProductionItem::Terminal("t".into())],
                        Some("atom"),
                        &[],
                    ),
                ];
                sentences.extend((0..self.sorts).map(|index| syntax_sort(&sort(index), &[])));
                sentences.extend(
                    self.atoms
                        .iter()
                        .map(|index| production(&sort(*index), vec![nonterminal("T")], None, &[])),
                );
                sentences.extend(self.subsorts.iter().map(|(parent, child)| {
                    production(&sort(*parent), vec![nonterminal(&sort(*child))], None, &[])
                }));
                for (index, operator) in self.operators.iter().enumerate() {
                    let positions = operator.apply_priority.as_ref().map(|positions| {
                        positions
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(",")
                    });
                    let attributes = positions
                        .as_deref()
                        .map(|positions| vec![("applyPriority", positions)])
                        .unwrap_or_default();
                    sentences.push(production(
                        &sort(operator.result),
                        operator.items(index),
                        Some(&label(index)),
                        &attributes,
                    ));
                }
                sentences.extend(self.priorities.iter().map(|(higher, lower)| {
                    Sentence::SyntaxPriority {
                        priorities: vec![vec![label(*higher)], vec![label(*lower)]],
                        attributes: Attributes::default(),
                    }
                }));
                sentences.extend(self.associativities.iter().map(|(associativity, members)| {
                    Sentence::SyntaxAssociativity {
                        associativity: *associativity,
                        tags: members.iter().map(|index| label(*index)).collect(),
                        attributes: Attributes::default(),
                    }
                }));
                sentences
            }
        }

        /// A derivation tree of the source grammar: the index of a production among the
        /// source productions, and one subtree per nonterminal item.
        #[derive(Clone, Debug)]
        struct Tree {
            production: usize,
            children: Vec<Tree>,
        }

        fn operand_sorts(items: &[ProductionItem]) -> Vec<&Sort> {
            items
                .iter()
                .filter_map(|item| match item {
                    ProductionItem::NonTerminal { sort, .. } => Some(sort),
                    ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
                })
                .collect()
        }

        /// At most `limit` trees of `sort` with at most `depth` nested labelled productions.
        fn trees(sources: &[&Sentence], sort: &Sort, depth: usize, limit: usize) -> Vec<Tree> {
            let mut result = Vec::new();
            for (index, source) in sources.iter().enumerate() {
                let Sentence::Production {
                    sort: result_sort,
                    items,
                    label,
                    ..
                } = source
                else {
                    unreachable!()
                };
                if result_sort != sort {
                    continue;
                }
                let operands = operand_sorts(items);
                let child_depth = match (label, operands.is_empty()) {
                    (_, true) => {
                        result.push(Tree {
                            production: index,
                            children: Vec::new(),
                        });
                        continue;
                    }
                    // A subsort production is not a level of the program text.
                    (None, false) => depth,
                    (Some(_), false) if depth == 0 => continue,
                    (Some(_), false) => depth - 1,
                };
                let mut combinations = vec![Vec::new()];
                for operand in operands {
                    let subtrees = trees(sources, operand, child_depth, limit);
                    combinations = combinations
                        .iter()
                        .flat_map(|prefix| {
                            subtrees.iter().map(move |subtree| {
                                let mut combination = prefix.clone();
                                combination.push(subtree.clone());
                                combination
                            })
                        })
                        .take(limit)
                        .collect();
                }
                result.extend(combinations.into_iter().map(|children| Tree {
                    production: index,
                    children,
                }));
            }
            result.truncate(limit);
            result
        }

        fn source_label(source: &Sentence) -> Option<&str> {
            let Sentence::Production { label, .. } = source else {
                unreachable!()
            };
            label.as_ref().map(|label| label.name.as_str())
        }

        /// The documented filter, written from the declarations alone.
        struct Filter {
            /// `(parent, child)`: `child` has lesser priority than `parent` (transitively).
            lesser: BTreeSet<(String, String)>,
            /// `(parent, child)` pairs of a left (or non-assoc) group.
            left: BTreeSet<(String, String)>,
            /// `(parent, child)` pairs of a right (or non-assoc) group.
            right: BTreeSet<(String, String)>,
        }

        impl Filter {
            fn new(grammar: &RandomGrammar) -> Self {
                let mut lesser = grammar
                    .priorities
                    .iter()
                    .map(|(higher, lower)| (label(*higher), label(*lower)))
                    .collect::<BTreeSet<_>>();
                loop {
                    let implied = lesser
                        .iter()
                        .flat_map(|(a, b)| {
                            lesser
                                .iter()
                                .filter(move |(c, _)| c == b)
                                .map(move |(_, d)| (a.clone(), d.clone()))
                        })
                        .collect::<Vec<_>>();
                    let before = lesser.len();
                    lesser.extend(implied);
                    if lesser.len() == before {
                        break;
                    }
                }
                let mut left = BTreeSet::new();
                let mut right = BTreeSet::new();
                for (associativity, members) in &grammar.associativities {
                    for parent in members {
                        for child in members {
                            let pair = (label(*parent), label(*child));
                            if matches!(
                                associativity,
                                Associativity::Left | Associativity::NonAssoc
                            ) {
                                left.insert(pair.clone());
                            }
                            if matches!(
                                associativity,
                                Associativity::Right | Associativity::NonAssoc
                            ) {
                                right.insert(pair);
                            }
                        }
                    }
                }
                Self {
                    lesser,
                    left,
                    right,
                }
            }

            fn allows(&self, sources: &[&Sentence], tree: &Tree) -> bool {
                let source = sources[tree.production];
                let Sentence::Production {
                    items, attributes, ..
                } = source
                else {
                    unreachable!()
                };
                // A syntactic subsort (one nonterminal and no terminal) writes nothing around its
                // child, so it judges no child.
                if let Some(parent) = source_label(source)
                    && items.len() > 1
                {
                    let count = tree.children.len();
                    let first = matches!(items.first(), Some(ProductionItem::NonTerminal { .. }));
                    let last = matches!(items.last(), Some(ProductionItem::NonTerminal { .. }));
                    let checked = attributes.string(AttributeKey::ApplyPriority).map_or_else(
                        || {
                            let mut positions = BTreeSet::new();
                            if first {
                                positions.insert(1);
                            }
                            if last {
                                positions.insert(count);
                            }
                            positions
                        },
                        |positions| {
                            positions
                                .split(',')
                                .map(|position| position.parse::<usize>().unwrap())
                                .collect()
                        },
                    );
                    for (index, child) in tree.children.iter().enumerate() {
                        let position = index + 1;
                        if !checked.contains(&position) {
                            continue;
                        }
                        let mut root = child;
                        while source_label(sources[root.production]).is_none()
                            && root.children.len() == 1
                        {
                            root = &root.children[0];
                        }
                        let Some(child_label) = source_label(sources[root.production]) else {
                            continue;
                        };
                        let pair = (parent.to_owned(), child_label.to_owned());
                        if self.lesser.contains(&pair)
                            || (position == 1 && first && self.right.contains(&pair))
                            || (position == count && last && self.left.contains(&pair))
                        {
                            return false;
                        }
                    }
                }
                tree.children
                    .iter()
                    .all(|child| self.allows(sources, child))
            }
        }

        /// Whether `productions` derive `tree` from `sort` with productions whose source is the
        /// tree's production at each node.
        fn derives(
            productions: &[GrammarProduction],
            sources: &[&Sentence],
            sort: &Sort,
            tree: &Tree,
        ) -> bool {
            productions.iter().any(|production| {
                &production.result == sort
                    && &production.source == sources[tree.production]
                    && operand_sorts(&production.items)
                        .into_iter()
                        .zip(&tree.children)
                        .all(|(operand, child)| derives(productions, sources, operand, child))
            })
        }

        /// The sorts of `productions` that derive a finite tree.
        fn productive(productions: &[GrammarProduction]) -> BTreeSet<Sort> {
            let mut productive = BTreeSet::new();
            loop {
                let before = productive.len();
                for production in productions {
                    if operand_sorts(&production.items)
                        .iter()
                        .all(|operand| productive.contains(*operand))
                    {
                        productive.insert(production.result.clone());
                    }
                }
                if productive.len() == before {
                    return productive;
                }
            }
        }

        proptest! {
            #![proptest_config(ProptestConfig {
                cases: 256,
                failure_persistence: None,
                ..ProptestConfig::default()
            })]

            #[test]
            fn the_export_derives_exactly_the_trees_priority_and_associativity_allow(
                grammar in random_grammar()
            ) {
                let sentences = grammar.sentences();
                let sources = sentences
                    .iter()
                    .filter(|sentence| matches!(sentence, Sentence::Production { .. }))
                    .collect::<Vec<_>>();
                let exported = transform_priority_and_associativity(
                    &sentences,
                    prepare(&sentences).unwrap().productions,
                )
                .unwrap();
                // Restriction leaves no rule that derives nothing, except the source grammar's
                // own.
                let exported_productive = productive(&exported);
                let source_productive = productive(&prepare(&sentences).unwrap().productions);
                for production in &exported {
                    let Sentence::Production { items, .. } = &production.source else {
                        unreachable!()
                    };
                    prop_assert!(
                        operand_sorts(&production.items)
                            .iter()
                            .all(|operand| exported_productive.contains(*operand))
                            || !operand_sorts(items)
                                .iter()
                                .all(|operand| source_productive.contains(*operand)),
                        "{:?} derives nothing",
                        production
                    );
                }
                let filter = Filter::new(&grammar);
                let start = Sort::new(sort(0));
                for tree in trees(&sources, &start, 3, 2000) {
                    prop_assert_eq!(
                        derives(&exported, &sources, &start, &tree),
                        filter.allows(&sources, &tree),
                        "tree {:?}",
                        tree
                    );
                }
            }
        }
    }
}
