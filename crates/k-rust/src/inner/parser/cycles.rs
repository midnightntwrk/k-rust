//! ```toml algorithm
//! id = "parser.grammar.same_span_cycles"
//! name = "detection of productions on same-span derivation cycles"
//! sites = ["SameSpanCycles::new", "strongly_connected_components"]
//! variable = "P = recognizable productions; I = their items; V = sorts"
//! counters = []
//! no_counter = "same-span cycle detection has no dedicated counter"
//!
//! [[cost]]
//! mode = "one grammar version"
//! bound = "O(P + I + V)"
//! ```
//!
//! ```toml algorithm
//! id = "parser.forest.cycle_check"
//! name = "same-span repetition check of packed nodes built by cyclic productions"
//! sites = ["check_same_span_repetition"]
//! variable = "N = packed nodes reachable from the new node through children of its own span"
//! counters = []
//! no_counter = "the repetition check has no dedicated counter; it runs only for productions SameSpanCycles flags, which none of the measured workloads' grammars have"
//!
//! [[cost]]
//! mode = "one node built by a flagged production"
//! bound = "O(N) expected (hashed visited set and build table)"
//! ```
//!
//! Termination of recognition on grammars whose derivations can repeat over the same text.
//!
//! A sort derives itself over one span when a production has one nonterminal whose siblings can
//! all match the empty string and that nonterminal derives the production's result again, as in
//! `Exp ::= Opt Exp Opt` with a nullable `Opt`. Every node of that sort over the span then has a
//! wrapped copy over the same span, so the parse forest has infinitely many trees, and the chart
//! loop, which builds each new tree as a new packed node, never reaches a fixed point.
//!
//! [`SameSpanCycles`] over-approximates, from the grammar alone, the productions that can take part
//! in such a repetition and build a node. [`check_same_span_repetition`] decides, for each node one
//! of them builds, whether the node already contains a node of the same production over the same
//! span; that is exactly when the forest is infinite (see its documentation), and the parse fails
//! with [`ParseError::CyclicDerivation`]. Grammars without a flagged production pay one
//! vector lookup per completed node.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::kast::TermSpan;

use super::chart::Chart;
use super::forest::{PackedNode, PackedTerm};
use super::grammar::render_added_production;
use super::{CyclicDerivation, Grammar, Item, ParseError};

/// Productions that may build a node on a derivation cycle that consumes no input.
#[derive(Clone, Debug, Default)]
pub(super) struct SameSpanCycles {
    flagged: Vec<bool>,
}

impl SameSpanCycles {
    /// Flag every recognizable production that has a nonterminal item `S` such that all its other
    /// items may match the empty string, `S` derives the production's result through productions
    /// of the same shape, and the production builds a node rather than returning its only child.
    ///
    /// "May match the empty string" over-approximates where it must: a regex item counts as
    /// possibly empty when its shortest match is empty, whatever its anchors and restrictions
    /// require of the surroundings. Over-approximation only adds checks; the check is exact.
    pub(super) fn new(grammar: &Grammar) -> Self {
        let sorts = grammar.sorts.len();
        let active = grammar
            .by_result
            .iter()
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        // The number of items of each production that are not nonterminals and cannot match the
        // empty string. Empty terminals are dropped when a production is added; any other literal
        // consumes its bytes.
        // Many productions share a regex (a token sort's regex, `#KVariable`), so each distinct
        // compiled body is analysed once.
        let mut regexes = HashMap::new();
        let mut lexical_blocking = vec![0usize; grammar.productions.len()];
        for &index in &active {
            lexical_blocking[index] = grammar.productions[index]
                .items
                .iter()
                .filter(|item| match item {
                    Item::Terminal(value) => !value.is_empty(),
                    Item::Regex { regex, .. } => !*regexes
                        .entry(regex.rust_body())
                        .or_insert_with(|| regex.may_match_empty()),
                    Item::NonTerminal(_) => false,
                })
                .count();
        }

        // Nullable sorts, by the counting worklist: a production becomes nullable when its last
        // nonterminal occurrence is proved nullable.
        let mut nullable = vec![false; sorts];
        let mut remaining = vec![0usize; grammar.productions.len()];
        let mut callers = vec![Vec::new(); sorts];
        let mut pending = Vec::new();
        for &index in &active {
            if lexical_blocking[index] != 0 {
                continue;
            }
            let production = &grammar.productions[index];
            for sort_id in production.item_sort_ids.iter().flatten() {
                remaining[index] += 1;
                callers[*sort_id].push(index);
            }
            if remaining[index] == 0 && !nullable[production.result_id] {
                nullable[production.result_id] = true;
                pending.push(production.result_id);
            }
        }
        // Invariant: every queued sort has just become nullable; each caller's count is the
        // number of its nonterminal occurrences not yet proved nullable.
        while let Some(sort) = pending.pop() {
            for &caller in &callers[sort] {
                remaining[caller] -= 1;
                let result = grammar.productions[caller].result_id;
                if remaining[caller] == 0 && !nullable[result] {
                    nullable[result] = true;
                    pending.push(result);
                }
            }
        }

        // Same-span edges `result -> S`, one per nonterminal item whose siblings may be empty.
        let mut edges = Vec::new();
        for &index in &active {
            let production = &grammar.productions[index];
            let blocking = lexical_blocking[index]
                + production
                    .item_sort_ids
                    .iter()
                    .flatten()
                    .filter(|sort_id| !nullable[**sort_id])
                    .count();
            for sort_id in production.item_sort_ids.iter().flatten() {
                if blocking - usize::from(!nullable[*sort_id]) == 0 {
                    edges.push((index, production.result_id, *sort_id));
                }
            }
        }
        let component = strongly_connected_components(sorts, &edges);
        let mut flagged = vec![false; grammar.productions.len()];
        for (index, result, child) in edges {
            let production = &grammar.productions[index];
            let children = production.item_sort_ids.iter().flatten().count();
            // `build_packed_term` returns the only child of such a production itself, so a cycle
            // through it alone repeats a node the chart already holds.
            let returns_child = production.record.is_none()
                && !production.bracket
                && (production.transparent || production.label.is_none())
                && children == 1;
            if component[result] == component[child] && !production.token && !returns_child {
                flagged[index] = true;
            }
        }
        Self { flagged }
    }

    pub(super) fn contains(&self, production: usize) -> bool {
        self.flagged.get(production).copied().unwrap_or(false)
    }
}

/// Component ids of the directed graph on `0..vertices` with the given `(_, from, to)` edges;
/// two vertices share an id exactly when each reaches the other.
fn strongly_connected_components(vertices: usize, edges: &[(usize, usize, usize)]) -> Vec<usize> {
    let mut successors = vec![Vec::new(); vertices];
    let mut predecessors = vec![Vec::new(); vertices];
    for &(_, from, to) in edges {
        successors[from].push(to);
        predecessors[to].push(from);
    }
    // Kosaraju: finish order on the graph, then components on the reverse graph in reverse
    // finish order. Both walks are iterative so deep grammars cannot exhaust the stack.
    let mut finished = Vec::with_capacity(vertices);
    let mut visited = vec![false; vertices];
    for root in 0..vertices {
        if visited[root] {
            continue;
        }
        visited[root] = true;
        let mut stack = vec![(root, 0usize)];
        // Invariant: `stack` is a path of visited vertices, each paired with the index of its
        // next unexplored successor; a vertex is finished when all its successors are explored.
        while let Some((vertex, next)) = stack.last_mut() {
            if let Some(&successor) = successors[*vertex].get(*next) {
                *next += 1;
                if !visited[successor] {
                    visited[successor] = true;
                    stack.push((successor, 0));
                }
            } else {
                finished.push(*vertex);
                stack.pop();
            }
        }
    }
    let mut component = vec![usize::MAX; vertices];
    for (id, &root) in finished.iter().rev().enumerate() {
        if component[root] != usize::MAX {
            continue;
        }
        component[root] = id;
        let mut stack = vec![root];
        while let Some(vertex) = stack.pop() {
            for &predecessor in &predecessors[vertex] {
                if component[predecessor] == usize::MAX {
                    component[predecessor] = id;
                    stack.push(predecessor);
                }
            }
        }
    }
    component
}

/// Fail when `term`, just built by the flagged `production` over `origin..end` of `input` and
/// accepted by the priority filter, contains a node of the same production over the same span
/// that `chart` recorded, with the same top parse label; otherwise record `term`.
///
/// Such a pair is a context `C` with `term = C[inner]`, both over one span and both completions of
/// the same production, so the chart offers `term` wherever it offered `inner`: the callers that
/// took `inner` take `term` and build `C[term]`, then `C[C[term]]`, and so on. Every edge of
/// `C[term]` is an edge of `term` or the edge that joined `inner` to its parent, now joining a
/// node with the same production and top parse label; the priority, associativity and cast
/// filters decide an edge from exactly those, so they accept every `C^n[inner]` and the forest is
/// infinite. Conversely, an infinite forest over a finite input has unboundedly deep paths of
/// nodes over one span, so the chart keeps building a node of some flagged production around an
/// earlier one of the same production; from the second repetition on the two have the same top
/// parse label, so the check fails the parse after finitely many completions.
pub(super) fn check_same_span_repetition(
    grammar: &Grammar,
    chart: &Chart,
    production: usize,
    term: &Rc<PackedTerm>,
    input: &str,
    origin: usize,
    end: usize,
) -> Result<(), ParseError> {
    let PackedNode::Production {
        children, metadata, ..
    } = &term.node
    else {
        return Ok(());
    };
    let span = metadata.span;
    let top_label = grammar.packed_top_parse_label(term);
    let built = chart.cycle_nodes.borrow();
    // `path[i]` is a visited node and the index of the node it was reached from (`0` is `term`).
    let mut path: Vec<(&PackedTerm, usize)> = vec![(term, 0)];
    let mut visited = HashSet::new();
    let mut pending = children
        .iter()
        .map(|child| (&**child, 0))
        .collect::<Vec<_>>();
    // Invariant: `pending` holds children, or ambiguity alternatives, of visited nodes over
    // `span`; every node over `span` reachable that way is visited once.
    while let Some((node, parent)) = pending.pop() {
        if !visited.insert(std::ptr::from_ref(node)) {
            continue;
        }
        let index = path.len();
        path.push((node, parent));
        match &node.node {
            PackedNode::Ambiguity(alternatives) => {
                pending.extend(
                    alternatives
                        .iter()
                        .map(|alternative| (&**alternative, index)),
                );
            }
            PackedNode::Production {
                children, metadata, ..
            } if metadata.span == span => {
                if built
                    .get(&std::ptr::from_ref(node))
                    .is_some_and(|(_, built_by)| *built_by == production)
                    && grammar.packed_top_parse_label(node) == top_label
                {
                    let mut chain = Vec::new();
                    let mut at = parent;
                    loop {
                        chain.push(path[at].0);
                        if at == 0 {
                            break;
                        }
                        at = path[at].1;
                    }
                    chain.reverse();
                    return Err(cyclic_derivation(
                        grammar, production, &chain, input, origin, end, span,
                    ));
                }
                pending.extend(children.iter().map(|child| (&**child, index)));
            }
            PackedNode::Production { .. }
            | PackedNode::InstantiatedProduction { .. }
            | PackedNode::Term(_) => {}
        }
    }
    drop(built);
    chart
        .cycle_nodes
        .borrow_mut()
        .insert(Rc::as_ptr(term), (Rc::clone(term), production));
    Ok(())
}

/// The error for a repetition found along `chain`, the nodes from the outer completion down to
/// the parent of the repeated node.
fn cyclic_derivation(
    grammar: &Grammar,
    production: usize,
    chain: &[&PackedTerm],
    input: &str,
    origin: usize,
    end: usize,
    span: Option<TermSpan>,
) -> ParseError {
    let mut productions = Vec::new();
    let mut empty = Vec::new();
    for node in chain {
        let PackedNode::Production {
            production: label,
            children,
            ..
        } = &node.node
        else {
            continue;
        };
        let descriptor = &grammar.productions[*label];
        let text = descriptor.source_production_text.as_ref().map_or_else(
            || {
                render_added_production(
                    &descriptor.result,
                    &descriptor.declared_items,
                    descriptor.token,
                    None,
                )
            },
            |text| text.as_str().to_owned(),
        );
        if !productions.contains(&text) {
            productions.push(text);
        }
        // Children follow the nonterminal items; a child that spans no input is an item the
        // repetition matched with the empty string. The node spans exactly its child on the
        // chain, so each of its regex items matched the empty string too.
        let nonterminals = descriptor
            .items
            .iter()
            .filter(|item| matches!(item, Item::NonTerminal(_)))
            .count();
        if nonterminals != children.len() {
            continue;
        }
        let mut children = children.iter();
        for item in &descriptor.items {
            let matched_empty = match item {
                Item::NonTerminal(_) => children
                    .next()
                    .is_some_and(|child| packed_span_is_empty(child)),
                Item::Regex { .. } => true,
                Item::Terminal(_) => false,
            };
            let description = item.description();
            if matched_empty && !empty.contains(&description) {
                empty.push(description);
            }
        }
    }
    ParseError::CyclicDerivation(Box::new(CyclicDerivation {
        sort: grammar.productions[production].result.clone(),
        text: input[origin..end].to_owned(),
        productions,
        empty,
        span,
    }))
}

fn packed_span_is_empty(term: &PackedTerm) -> bool {
    match &term.node {
        PackedNode::Production { metadata, .. }
        | PackedNode::InstantiatedProduction { metadata, .. } => {
            metadata.span.is_some_and(|span| span.start == span.end)
        }
        PackedNode::Term(term) => term
            .metadata()
            .and_then(|metadata| metadata.span)
            .is_some_and(|span| span.start == span.end),
        PackedNode::Ambiguity(alternatives) => alternatives
            .first()
            .is_some_and(|alternative| packed_span_is_empty(alternative)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::definition::{Attributes, ProductionItem, Sentence};
    use crate::kast::{Label, Sort, Term};

    fn nt(sort: &str) -> ProductionItem {
        ProductionItem::NonTerminal {
            sort: Sort::new(sort),
            name: None,
        }
    }

    fn terminal(text: &str) -> ProductionItem {
        ProductionItem::Terminal(text.into())
    }

    fn production(sort: &str, items: Vec<ProductionItem>, label: Option<&str>) -> Sentence {
        Sentence::Production {
            label: label.map(Label::new),
            parameters: vec![],
            sort: Sort::new(sort),
            items,
            attributes: Attributes::default(),
        }
    }

    /// `Opt ::= "" | "q"` and `Exp ::= "1" | "2" | Exp "+" Exp`, plus `extra`.
    fn grammar(extra: Vec<Sentence>) -> Grammar {
        let mut sentences = vec![
            production("Opt", vec![], Some("none")),
            production("Opt", vec![terminal("q")], Some("someq")),
            production("Exp", vec![terminal("1")], Some("one")),
            production("Exp", vec![terminal("2")], Some("two")),
            production(
                "Exp",
                vec![nt("Exp"), terminal("+"), nt("Exp")],
                Some("plus"),
            ),
        ];
        sentences.extend(extra);
        Grammar::from_sentences(&sentences).unwrap()
    }

    fn flagged(grammar: &Grammar) -> Vec<String> {
        let cycles = SameSpanCycles::new(grammar);
        grammar
            .productions
            .iter()
            .enumerate()
            .filter(|(index, _)| cycles.contains(*index))
            .map(|(_, production)| {
                production
                    .label
                    .as_ref()
                    .map_or("", |label| &label.name)
                    .to_owned()
            })
            .collect()
    }

    fn parse(grammar: &Grammar, sort: &str, input: &str) -> Result<Term, ParseError> {
        grammar.parse(&Sort::new(sort), input)
    }

    fn cycle(result: Result<Term, ParseError>) -> CyclicDerivation {
        match result {
            Err(ParseError::CyclicDerivation(cycle)) => *cycle,
            other => panic!("expected a cyclic derivation, got {other:?}"),
        }
    }

    #[test]
    fn flags_exactly_the_productions_that_derive_their_sort_over_one_span() {
        let wrap = production("Exp", vec![nt("Opt"), nt("Exp"), nt("Opt")], Some("wrap"));
        assert_eq!(flagged(&grammar(vec![wrap])), ["wrap"]);

        // Through two sorts: `A ::= B Opt`, `B ::= Opt A`.
        let indirect = grammar(vec![
            production("A", vec![nt("B"), nt("Opt")], Some("ab")),
            production("A", vec![terminal("1")], Some("a1")),
            production("B", vec![nt("Opt"), nt("A")], Some("ba")),
        ]);
        assert_eq!(flagged(&indirect), ["ab", "ba"]);

        // Only nullable siblings: a nullable sort that consumes input elsewhere does not repeat.
        let not_cyclic = grammar(vec![
            production(
                "Exp",
                vec![nt("Opt"), terminal("!"), nt("Exp")],
                Some("bang"),
            ),
            production("Pre", vec![nt("Opt"), nt("Exp")], Some("pre")),
        ]);
        assert!(flagged(&not_cyclic).is_empty());

        // A regex sibling counts exactly when it can match the empty string.
        let starred = grammar(vec![production(
            "Exp",
            vec![ProductionItem::regex("x*"), nt("Exp")],
            Some("stars"),
        )]);
        assert_eq!(flagged(&starred), ["stars"]);
        let plussed = grammar(vec![production(
            "Exp",
            vec![ProductionItem::regex("x+"), nt("Exp")],
            Some("pluses"),
        )]);
        assert!(flagged(&plussed).is_empty());

        // An unlabeled unary production on the cycle returns its child; it builds no node to
        // repeat, so only the wrapper is checked.
        let chain = grammar(vec![
            production("Exp", vec![nt("Other")], None),
            production("Other", vec![nt("Opt"), nt("Exp")], Some("other")),
        ]);
        assert_eq!(flagged(&chain), ["other"]);
    }

    #[test]
    fn a_nullable_wrapper_makes_every_parse_of_its_sort_a_cyclic_derivation() {
        let grammar = grammar(vec![production(
            "Exp",
            vec![nt("Opt"), nt("Exp"), nt("Opt")],
            Some("wrap"),
        )]);
        for input in ["1", "q 1", "1 + 2", "q 1 + 2 q"] {
            let cycle = cycle(parse(&grammar, "Exp", input));
            assert_eq!(cycle.sort, Sort::new("Exp"), "{input}");
            assert_eq!(cycle.productions, ["syntax Exp ::= Opt Exp Opt"], "{input}");
            assert_eq!(cycle.empty, ["Opt"], "{input}");
        }
        assert_eq!(
            parse(&grammar, "Exp", "1").unwrap_err().to_string(),
            "Parsing ambiguity: `1` has infinitely many parses, because Exp derives itself \
             without consuming input:\n    syntax Exp ::= Opt Exp Opt\n\
             where Opt matches the empty string."
        );
        // Opt itself is not cyclic.
        assert!(parse(&grammar, "Opt", "q").is_ok());
    }

    #[test]
    fn reports_every_production_of_an_indirect_cycle() {
        let grammar = grammar(vec![
            production("A", vec![nt("B"), nt("Opt")], Some("ab")),
            production("A", vec![terminal("1")], Some("a1")),
            production("B", vec![nt("Opt"), nt("A")], Some("ba")),
        ]);
        let cycle = cycle(parse(&grammar, "A", "q 1"));
        assert_eq!(cycle.text, "q 1");
        assert_eq!(cycle.productions.len(), 2);
        assert!(cycle.productions.contains(&"syntax A ::= B Opt".to_owned()));
        assert!(cycle.productions.contains(&"syntax B ::= Opt A".to_owned()));
    }

    #[test]
    fn a_flagged_production_whose_repetition_the_scanner_never_offers_parses_normally() {
        // `r"x*"` may match the empty string, so `stars` is flagged, but the scanner offers no
        // empty `x*` token before `1`: the check runs and finds no repetition.
        let grammar = grammar(vec![production(
            "Exp",
            vec![ProductionItem::regex("x*"), nt("Exp")],
            Some("stars"),
        )]);
        assert_eq!(flagged(&grammar), ["stars"]);
        assert_eq!(
            parse(&grammar, "Exp", "1").unwrap().to_string(),
            "one(.KList)"
        );
        assert_eq!(
            parse(&grammar, "Exp", "x 1").unwrap().to_string(),
            "stars(one(.KList))"
        );
    }

    #[test]
    fn a_cycle_over_the_empty_text_is_reported() {
        let grammar = grammar(vec![
            production("Opt", vec![nt("Opt"), nt("Opt")], Some("pair")),
            production("Start", vec![nt("Opt"), terminal("!")], Some("start")),
        ]);
        let error = parse(&grammar, "Start", "!").unwrap_err();
        let cycle = cycle(Err(error.clone()));
        assert!(cycle.text.is_empty());
        assert_eq!(cycle.sort, Sort::new("Opt"));
        assert!(error.to_string().starts_with(
            "Parsing ambiguity: the empty text has infinitely many parses, because Opt derives"
        ));
    }

    #[test]
    fn an_associativity_that_forbids_the_repetition_keeps_the_forest_finite() {
        // `post` may not be its own left child, so `post(post(X, none), none)` is filtered and
        // `1` has exactly the parses `1` and `post(1, none)`.
        let mut grammar = grammar(vec![production(
            "Exp",
            vec![nt("Exp"), nt("Opt")],
            Some("post"),
        )]);
        assert_eq!(flagged(&grammar), ["post"]);
        grammar.add_right_associative("post");
        let error = parse(&grammar, "Exp", "1").unwrap_err();
        assert!(
            matches!(&error, ParseError::Ambiguous { parses: 2, .. }),
            "{error:?}"
        );
        // Without the declaration the same input repeats without end.
        let grammar = self::grammar(vec![production(
            "Exp",
            vec![nt("Exp"), nt("Opt")],
            Some("post"),
        )]);
        cycle(parse(&grammar, "Exp", "1"));
    }

    #[test]
    fn grammars_without_a_flagged_production_parse_as_before() {
        // Nullable items that cannot repeat a sort over one span: the parses are the ordinary
        // finite ones.
        let grammar = grammar(vec![
            production("Pre", vec![nt("Opt"), nt("Exp")], Some("pre")),
            production(
                "Exp",
                vec![nt("Opt"), terminal("!"), nt("Exp")],
                Some("bang"),
            ),
        ]);
        assert!(flagged(&grammar).is_empty());
        assert_eq!(
            parse(&grammar, "Pre", "q 1").unwrap().to_string(),
            "pre(someq(.KList),one(.KList))"
        );
        assert_eq!(
            parse(&grammar, "Pre", "! 2").unwrap().to_string(),
            "pre(none(.KList),bang(none(.KList),two(.KList)))"
        );
    }
}
