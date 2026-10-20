//! ```toml algorithm
//! id = "kompile.labels.backward_closure"
//! name = "backward closure over the label-dependency graph"
//! sites = ["LabelDependencyGraph::build", "LabelDependencyGraph::backward_closure"]
//! variable = "V = function, anywhere and (under READS) macro labels; E = rule dependency edges; R = rules; N_f = term nodes of the rules that give edges"
//! counters = []
//! no_counter = "label-dependency closure has no dedicated counter"
//!
//! [[cost]]
//! mode = "graph construction"
//! bound = "O((R + N_f) log V + E)"
//!
//! [[cost]]
//! mode = "one closure"
//! bound = "O((V + E) log V)"
//! ```
//!
//! Backward dependency closure over the call graph of rules. The sources of edges are function
//! labels, and under [`Edges::READS`] macro labels too; an edge goes from a source to each
//! function, non-macro anywhere or (under [`Edges::READS`]) macro label its rules apply, so anywhere
//! labels are edge targets only.
//!
//! [`Edges`] selects the rule parts that give edges. With [`Edges::FUNCTION_RULES`] they are the
//! body and `requires` of function rules. With [`Edges::READS`], used for the functions that read
//! the configuration, they are every part a rule's evaluation reads: the body, `requires` and
//! `ensures` of a function rule, and a macro is a node too, with an edge from each rule part that
//! uses it to the macro and from the macro to what its right side applies, since expansion puts
//! that right side where the macro is used. A rule is credited to the label its head has once
//! macros are expanded ([`LabelDependencyGraph::rule_heads`]): a simplification rule written with
//! a macro or alias head is a rule of the function that head expands to. A macro label can enter
//! a closure; a caller that needs function labels only keeps those.
//!
//! Graph construction visits the rule catalog once; closure is O(V + E). No dedicated counter.

use std::collections::{BTreeMap, BTreeSet};

use petgraph::Direction::Incoming;
use petgraph::graph::{DiGraph, NodeIndex};

use crate::definition::{
    AttributeKey, LabelHead, ProductionCatalog, RuleCatalog, RuleHead, Sentence, match_rule_label,
};
use crate::kast::Term;
use crate::names::WellKnownSymbol;

/// The rule parts that give a [`LabelDependencyGraph`] its edges, besides the body and `requires`
/// of every function rule.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Edges {
    /// The `ensures` of a function rule.
    pub(crate) ensures: bool,
    /// Macro labels as nodes: an application of one is an edge target, and its rules give edges.
    pub(crate) macros: bool,
}

impl Edges {
    /// The body and `requires` of function rules only.
    pub(crate) const FUNCTION_RULES: Self = Self {
        ensures: false,
        macros: false,
    };
    /// Every part of a function rule, and macros, through which evaluating a function reaches
    /// another label.
    pub(crate) const READS: Self = Self {
        ensures: true,
        macros: true,
    };
}

pub(crate) struct LabelDependencyGraph {
    graph: DiGraph<LabelHead, ()>,
    nodes: BTreeMap<LabelHead, NodeIndex>,
    /// The macro labels, under [`Edges::READS`]; empty otherwise.
    macro_labels: BTreeSet<LabelHead>,
    /// For each macro label, the root labels of the right sides of its rules.
    expansions: BTreeMap<LabelHead, BTreeSet<LabelHead>>,
}

impl LabelDependencyGraph {
    pub(crate) fn build(
        productions: &ProductionCatalog<'_>,
        rules: &RuleCatalog<'_>,
        is_macro: impl Fn(&Sentence) -> bool,
        edges: Edges,
    ) -> Self {
        let function_labels = productions.function_labels();
        let macro_labels = if edges.macros {
            rules.all_macro_labels(productions)
        } else {
            BTreeSet::new()
        };
        let anywhere_labels = rules
            .rules()
            .filter(|(_, rule)| !is_macro(rule))
            .filter(|(_, rule)| rule.attributes().has(AttributeKey::Anywhere))
            .filter_map(|(_, rule)| anywhere_lhs_label(rule))
            .collect::<BTreeSet<_>>();
        let mut expansions = BTreeMap::<LabelHead, BTreeSet<LabelHead>>::new();
        // Invariant: `expansions` maps each macro label to the right-side root labels of the
        // macro's defining rules visited so far.
        for (_, rule) in rules.rules() {
            let head = LabelHead::from(&match_rule_label(rule));
            if macro_labels.contains(&head)
                && defines_macro(rule)
                && let Sentence::Rule { body, .. } = rule
                && let Some(root) = right_side_root_label(body)
            {
                expansions.entry(head).or_default().insert(root);
            }
        }
        let mut result = Self {
            graph: DiGraph::new(),
            nodes: BTreeMap::new(),
            macro_labels,
            expansions,
        };
        for function in function_labels {
            result.node(function.clone());
        }
        // Invariant: `nodes` names every label already observed and `graph` contains every
        // dependency edge found in the rule-catalog prefix already visited.
        for (_, rule) in rules.rules() {
            let Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            } = rule
            else {
                unreachable!("rule catalogs contain rules")
            };
            // Invariant: `result.graph` has every edge of the rule's heads before `current`.
            for current in result.rule_heads(rule) {
                if !function_labels.contains(&current) && !result.macro_labels.contains(&current) {
                    continue;
                }
                let current_node = result.node(current);
                let roots = [Some(body), Some(requires), edges.ensures.then_some(ensures)];
                result.add_edges(
                    current_node,
                    roots.into_iter().flatten(),
                    function_labels,
                    &anywhere_labels,
                );
            }
        }
        result
    }

    /// The labels `rule` is a rule of once macros are expanded: its head, or, for a rule that is
    /// not a macro's own rule but whose head is a macro label (a simplification rule written with
    /// a macro or alias head), the non-macro labels that head expands to, through macro chains.
    pub(crate) fn rule_heads(&self, rule: &Sentence) -> BTreeSet<LabelHead> {
        let head = LabelHead::from(&match_rule_label(rule));
        if !self.macro_labels.contains(&head) || defines_macro(rule) {
            return BTreeSet::from([head]);
        }
        let mut heads = BTreeSet::new();
        let mut seen = BTreeSet::from([head.clone()]);
        let mut pending = vec![head];
        // Invariant: `heads` holds the non-macro labels reached from the expanded macro labels;
        // `seen` grows by one macro label per iteration and bounds the loop.
        while let Some(label) = pending.pop() {
            for target in self.expansions.get(&label).into_iter().flatten() {
                if !self.macro_labels.contains(target) {
                    heads.insert(target.clone());
                } else if seen.insert(target.clone()) {
                    pending.push(target.clone());
                }
            }
        }
        heads
    }

    /// Add an edge from `current_node` for every non-injection application, in `roots`, of a
    /// function, anywhere or macro label.
    fn add_edges<'t>(
        &mut self,
        current_node: NodeIndex,
        roots: impl Iterator<Item = &'t Term>,
        function_labels: &BTreeSet<LabelHead>,
        anywhere_labels: &BTreeSet<LabelHead>,
    ) {
        // Invariant: `self.graph` has an edge from `current_node` to every function, anywhere or macro label applied in the roots before `root` (`body`, `requires`, then `ensures` when `edges.ensures`).
        for root in roots {
            // Invariant: the preorder traversal visits each node of `root` once and adds one edge from `current_node` for every non-injection application whose label is in `function_labels`, `anywhere_labels` or `macro_labels`.
            root.visit_preorder(&mut |term| {
                let Term::Apply { label, .. } = term.unannotated() else {
                    return;
                };
                if label.is(WellKnownSymbol::Inj) {
                    return;
                }
                let dependency = LabelHead::from(label);
                if function_labels.contains(&dependency)
                    || anywhere_labels.contains(&dependency)
                    || self.macro_labels.contains(&dependency)
                {
                    let dependency_node = self.node(dependency);
                    self.graph.add_edge(current_node, dependency_node, ());
                }
            });
        }
    }

    pub(crate) fn backward_closure(&self, mut seeds: BTreeSet<LabelHead>) -> BTreeSet<LabelHead> {
        let mut pending = seeds.iter().cloned().collect::<Vec<_>>();
        // Invariant: `seeds` contains the original labels and all discovered callers; `pending`
        // contains discovered labels whose incoming edges have not yet been expanded.
        while let Some(label) = pending.pop() {
            let Some(&label_node) = self.nodes.get(&label) else {
                continue;
            };
            // Invariant: predecessors already visited from this node are in `seeds`; the finite
            // incoming-edge iterator shrinks by one each iteration.
            for predecessor in self.graph.neighbors_directed(label_node, Incoming) {
                let predecessor = self.graph[predecessor].clone();
                if seeds.insert(predecessor.clone()) {
                    pending.push(predecessor);
                }
            }
        }
        seeds
    }

    fn node(&mut self, label: LabelHead) -> NodeIndex {
        *self
            .nodes
            .entry(label.clone())
            .or_insert_with(|| self.graph.add_node(label))
    }
}

/// Whether `rule`, whose head is a macro label, is one of the macro's own rules: a simplification
/// rule is not, it states an equation of what the macro expands to.
fn defines_macro(rule: &Sentence) -> bool {
    !rule.attributes().has(AttributeKey::Simplification)
}

/// The root label of the right side of `body`'s top rewrite, through annotations, aliases and an
/// injection.
fn right_side_root_label(body: &Term) -> Option<LabelHead> {
    let Term::Rewrite { right, .. } = body.unannotated() else {
        return None;
    };
    let mut root = right.unannotated();
    while let Term::As { pattern, .. } = root {
        root = pattern.unannotated();
    }
    let Term::Apply { label, arguments } = root else {
        return None;
    };
    if !label.is(WellKnownSymbol::Inj) {
        return Some(LabelHead::from(label));
    }
    let Term::Apply { label, .. } = arguments.first()?.unannotated() else {
        return None;
    };
    Some(LabelHead::from(label))
}

/// The label an `anywhere` rule rewrites: its head ([`RuleHead::of`], root aliases looked
/// through), or the injected argument's label when the head is an injection.
fn anywhere_lhs_label(rule: &Sentence) -> Option<LabelHead> {
    let Sentence::Rule { body, .. } = rule else {
        return None;
    };
    let head = RuleHead::of(body);
    head.injected()
        .or_else(|| head.label().filter(|label| !label.is(WellKnownSymbol::Inj)))
        .map(LabelHead::from)
}
