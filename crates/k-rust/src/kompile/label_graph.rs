//! ```toml algorithm
//! id = "kompile.labels.backward_closure"
//! name = "backward closure over the label-dependency graph"
//! sites = ["LabelDependencyGraph::build", "LabelDependencyGraph::backward_closure"]
//! variable = "V = function and macro labels; E = rule dependency edges; R = rules; N_f = term nodes of the rules that give edges"
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
//! Backward dependency closure over the call graph of function rules: an edge goes from a function
//! label to each function or non-macro anywhere label its rules apply, so anywhere labels are edge
//! targets only, and only function labels propagate a property to their callers.
//!
//! [`Edges`] selects the rule parts that give edges. With [`Edges::READS`], used for the
//! functions that read the configuration, they are every part a rule's evaluation reads: the body,
//! `requires` and `ensures` of a function rule, and a macro is a node too, with an edge from each
//! rule part that uses it to the macro and from the macro to what its right side applies, since
//! expansion puts that right side where the macro is used. A macro label can enter a closure; a
//! caller that needs function labels only keeps those.
//!
//! Graph construction visits the rule catalog once; closure is O(V + E). No dedicated counter.

use std::collections::{BTreeMap, BTreeSet};

use petgraph::Direction::Incoming;
use petgraph::graph::{DiGraph, NodeIndex};

use crate::definition::{
    AttributeKey, LabelHead, ProductionCatalog, RuleCatalog, Sentence, match_rule_label,
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
        let mut result = Self {
            graph: DiGraph::new(),
            nodes: BTreeMap::new(),
        };
        for function in function_labels {
            result.node(function.clone());
        }
        // Invariant: `nodes` names every label already observed and `graph` contains every
        // dependency edge found in the rule-catalog prefix already visited.
        for (_, rule) in rules.rules() {
            let current = LabelHead::from(&match_rule_label(rule));
            if !function_labels.contains(&current) && !macro_labels.contains(&current) {
                continue;
            }
            let current_node = result.node(current);
            let Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            } = rule
            else {
                unreachable!("rule catalogs contain rules")
            };
            let roots = [Some(body), Some(requires), edges.ensures.then_some(ensures)];
            // Invariant: `result.graph` has an edge from `current_node` to every function, anywhere or macro label applied in the roots before `root` (`body`, `requires`, then `ensures` when `edges.ensures`).
            for root in roots.into_iter().flatten() {
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
                        || macro_labels.contains(&dependency)
                    {
                        let dependency_node = result.node(dependency);
                        result.graph.add_edge(current_node, dependency_node, ());
                    }
                });
            }
        }
        result
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

fn anywhere_lhs_label(rule: &Sentence) -> Option<LabelHead> {
    let Sentence::Rule { body, .. } = rule else {
        return None;
    };
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is not a sentence kind; only the listed variants are special here"
    )]
    let left = match body.unannotated() {
        Term::Rewrite { left, .. } => left.as_ref(),
        _ => body,
    };
    let Term::Apply { label, arguments } = left.unannotated() else {
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
