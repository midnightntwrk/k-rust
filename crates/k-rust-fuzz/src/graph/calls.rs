//! Function-call edges between the symbols that have equations (ARCHITECTURE 6.3, 8.3).
//!
//! A function application in a rule's `requires` or right-hand side is evaluated by the
//! function's equations, whose own conditions and right-hand sides apply further functions. The
//! dictionary proposer harvests the conditions of the equations reachable this way
//! (ARCHITECTURE 8.3), so the graph records, for every symbol with equations in
//! `BackendDefinition::function_theory()`, the symbols with equations that its equations apply.
//!
//! The edges are derived from the backend's function theory rather than taken from the
//! frontend's label dependency graph: the theory holds the equations evaluation uses, it names
//! symbols as the backend's terms do, and reading it needs no change to the facade.
//!
//! A node is a symbol with an equation stored in the function theory under that symbol. Symbols
//! without one (constructors, hooked builtins evaluated by their hook) are no nodes. The
//! simplification and definedness equations are in other theories and are not read, so a
//! `simplification` lemma does not make its head a node. An equation stored under a bucket that
//! is not a symbol (`Variable`, `Injection`, `And`) is skipped: no call names it.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use k_rust::k_rust_backend::{
    definition::BackendDefinition,
    rule::{RewriteRule, RuleRhs, TermIndex},
    term::Term,
};

/// The symbols with equations and the call edges between them, by KORE symbol name.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct FunctionCalls {
    /// Every symbol with an equation in the function theory, and its equations in the theory's
    /// order (priority, then the theory's order within a priority).
    equations: BTreeMap<String, Vec<Arc<RewriteRule>>>,
    /// The symbols with equations that some equation of the key applies, in its right-hand side,
    /// `requires` or `ensures`.
    callees: BTreeMap<String, BTreeSet<String>>,
}

impl FunctionCalls {
    pub(crate) fn new(definition: &BackendDefinition) -> Self {
        let mut equations: BTreeMap<String, Vec<Arc<RewriteRule>>> = BTreeMap::new();
        for (index, groups) in definition.function_theory() {
            // An equation is stored under its left-hand side's root; only an application has a
            // symbol a call can name.
            let TermIndex::Symbol(name) = index else {
                continue;
            };
            let entry = equations.entry(name.to_string()).or_default();
            for rules in groups.values() {
                entry.extend(rules.iter().cloned());
            }
        }
        let mut calls = Self {
            equations,
            callees: BTreeMap::new(),
        };
        calls.callees = calls
            .equations
            .iter()
            .map(|(name, rules)| {
                let mut called = BTreeSet::new();
                for rule in rules {
                    calls.collect_rule(rule, Part::All, &mut called);
                }
                (name.clone(), called)
            })
            .collect();
        calls
    }

    /// The equations of `function`, empty when it has none.
    pub(crate) fn equations(&self, function: &str) -> &[Arc<RewriteRule>] {
        self.equations.get(function).map_or(&[], Vec::as_slice)
    }

    /// Every equation of the function theory, by symbol name, each symbol's in the theory's
    /// order.
    pub(crate) fn all_equations(&self) -> impl Iterator<Item = &Arc<RewriteRule>> {
        self.equations.values().flatten()
    }

    /// `roots` and every symbol with equations reachable from them through call edges.
    pub(crate) fn closure(&self, roots: BTreeSet<String>) -> BTreeSet<String> {
        let mut reached = BTreeSet::new();
        let mut pending: Vec<String> = roots.into_iter().collect();
        while let Some(function) = pending.pop() {
            if reached.contains(&function) {
                continue;
            }
            if let Some(callees) = self.callees.get(&function) {
                pending.extend(
                    callees
                        .iter()
                        .filter(|callee| !reached.contains(*callee))
                        .cloned(),
                );
            }
            reached.insert(function);
        }
        reached
    }

    /// Add to `called` the symbols with equations that `part` of `rule` applies.
    pub(super) fn collect_rule(
        &self,
        rule: &RewriteRule,
        part: Part,
        called: &mut BTreeSet<String>,
    ) {
        let mut visit = |term: &Term| self.collect_term(term, called);
        for predicate in rule.requires.iter() {
            predicate.visit_terms(&mut visit);
        }
        if part == Part::Requires {
            return;
        }
        match &rule.rhs {
            RuleRhs::Term(rhs) => visit(rhs),
            RuleRhs::Disjunction(alternatives) => {
                for alternative in alternatives {
                    visit(&alternative.term);
                    for predicate in alternative.ensures.iter() {
                        predicate.visit_terms(&mut visit);
                    }
                }
            }
            RuleRhs::Predicates(predicates) => {
                for predicate in predicates {
                    predicate.visit_terms(&mut visit);
                }
            }
            RuleRhs::Top | RuleRhs::Bottom => {}
        }
        for predicate in rule.ensures.iter() {
            predicate.visit_terms(&mut visit);
        }
    }

    fn collect_term(&self, term: &Term, called: &mut BTreeSet<String>) {
        term.visit_symbols(&mut |symbol| {
            if self.equations.contains_key(symbol.name.as_ref()) {
                called.insert(symbol.name.to_string());
            }
        });
    }
}

/// Which parts of a rule [`FunctionCalls::collect_rule`] reads.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Part {
    /// The `requires` only.
    Requires,
    /// The `requires`, the right-hand side and the `ensures`.
    All,
}
