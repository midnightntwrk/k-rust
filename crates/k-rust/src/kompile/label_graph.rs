//! ```toml algorithm
//! id = "kompile.labels.backward_closure"
//! name = "backward closure over the label-dependency graph"
//! sites = ["LabelDependencyGraph::build", "LabelDependencyGraph::backward_closure"]
//! variable = "V = function labels; E = rule dependency edges"
//! counters = []
//! no_counter = "label-dependency closure has no dedicated counter"
//!
//! [[cost]]
//! mode = "graph construction and one closure"
//! bound = "O(V + E)"
//! ```
//!
//! Backward dependency closure over function and non-macro anywhere labels.
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

pub(crate) struct LabelDependencyGraph {
    graph: DiGraph<LabelHead, ()>,
    nodes: BTreeMap<LabelHead, NodeIndex>,
}

impl LabelDependencyGraph {
    pub(crate) fn build(
        productions: &ProductionCatalog<'_>,
        rules: &RuleCatalog<'_>,
        is_macro: impl Fn(&Sentence) -> bool,
    ) -> Self {
        let function_labels = productions.function_labels();
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
            if !function_labels.contains(&current) {
                continue;
            }
            let current_node = result.node(current);
            let Sentence::Rule { body, requires, .. } = rule else {
                unreachable!("rule catalogs contain rules")
            };
            // Invariant: processed entries have reached their recorded state, the pending collection is the discovered frontier, and each pop consumes one entry before unseen successors are added.
            for root in [body, requires] {
                // Invariant: processed entries have reached their recorded state, the pending collection is the discovered frontier, and each pop consumes one entry before unseen successors are added.
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
