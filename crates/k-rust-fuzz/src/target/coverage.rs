//! Coverage targets: a run that records one of a set of coverage facts (CS-8).
//!
//! A coverage obligation of a corpus (an operand of a guard reached with a truth, a guard held
//! or refuted, a production a fired instance touched, a template field's value, a heating rule
//! fired) is decided from what the backend records of a run: the guard outcomes of the rules
//! and equations it names (`collectGuards`), the bindings of fired instances (`collectBindings`)
//! and the committed transitions (`collectCommitted`). A client that states an obligation as the
//! facts that cover it ([`CoverageFact`]) has a target whose hit is a run that records one of
//! them, read from the same records the client reads, so a hit is a run the obligation's reader
//! counts, up to what it adds of its own (kink counts comparable programs only, which the
//! target's `comparable` option requires of a hit).
//!
//! Each fact is a fact of the whole run, the union over every path it explored, as coverage is
//! (ARCHITECTURE 5.3, D13): a hit names no leaf.
//!
//! - [`CoverageFact::GuardNode`]: the guard of a rule or equation has a node, by its path in the
//!   written `requires` (the conjunct's index, then the operand's index at each level down),
//!   that some entry reached with the truth, where "reached" is the backend's written-order
//!   reading (`k_rust::backend::AxiomGuardOutput`).
//! - [`CoverageFact::GuardOutcome`]: some entry's guard outcome is `held`, or one of the
//!   refutations (`refuted-false`, `refuted-undefined`, `refuted-decided`).
//! - [`CoverageFact::Fired`]: the rule fired, a rewrite rule where some explored path took its
//!   step (coverage `committed`), an equation where an instance gave a result (coverage
//!   `applied`); of an axiom with several alternatives, where a fired instance took the named
//!   one (bindings `alternatives`).
//! - [`CoverageFact::Operand`]: a fired instance of the axiom bound a value whose head, through
//!   injections, is the symbol (bindings `operands`).
//! - [`CoverageFact::Binder`]: a fired instance of the axiom bound the variable to one of the
//!   values (bindings `binders`).
//!
//! Every rule a fact names resolves to one catalog entry ([`resolve_axiom`]). Unlike a rule
//! target, an equation is accepted: the facts are read from records the backend keeps of
//! equations as of rules, and the reader of the obligation reads the same records, so an
//! equation's fact means for the target what it means for the obligation.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::{
    backend::{
        BinderSelection, BindingCollection, CompiledRuleKind, CompiledRuleOutput, GuardCollection,
        GuardOutcomeOutput, NodeOutcomeOutput, RunCoverageOutput,
    },
    kore::ast::Pattern as KorePattern,
};
use serde::{Deserialize, Serialize};

use super::{RuleRef, rule};
use crate::error::TargetProblem;

/// A coverage target: a run that records one of `facts` (module documentation).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct CoverageTarget {
    /// The facts, any one of which makes a hit; at least one.
    pub facts: Vec<CoverageFact>,
}

/// One fact a run's records can show (module documentation).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "fact", rename_all = "kebab-case", deny_unknown_fields)]
pub enum CoverageFact {
    /// A node of the rule's guard reached with `truth`.
    GuardNode {
        /// The rule or equation.
        rule: RuleRef,
        /// The node's path in the written `requires`: the conjunct's index, then the operand's
        /// index at each level down.
        node: Vec<u32>,
        /// The truth.
        truth: bool,
    },
    /// An entry of the rule's guard with the outcome `held` (`held` true) or a refutation.
    GuardOutcome {
        /// The rule or equation.
        rule: RuleRef,
        /// `held`, else refuted.
        held: bool,
    },
    /// The rule fired: a rewrite rule's step on some explored path, an equation's instance with
    /// a result; with `lhs` or `rhs`, an instance that took that alternative.
    Fired {
        /// The rule or equation.
        rule: RuleRef,
        /// The left-hand side alternative, by its position; absent when there is one.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        lhs: Option<usize>,
        /// The right-hand side alternative of a rewrite rule; absent when there is one.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        rhs: Option<usize>,
    },
    /// A fired instance of the rule bound a value whose head is `symbol` (a KORE symbol name).
    Operand {
        /// The rule or equation.
        rule: RuleRef,
        /// The symbol, by its KORE name.
        symbol: String,
    },
    /// A fired instance of the rule bound `variable` to one of `values`.
    Binder {
        /// The rule or equation.
        rule: RuleRef,
        /// The variable, by its name in the definition (`VarOp`).
        variable: String,
        /// The `Int` values, in decimal.
        values: Vec<String>,
        /// The most values the run keeps of the variable, the least ones in integer order: at
        /// least the number of values the variable can take, so that no value is left out.
        cap: usize,
    },
}

impl CoverageFact {
    /// The rule the fact names.
    pub(crate) fn rule(&self) -> &RuleRef {
        match self {
            Self::GuardNode { rule, .. }
            | Self::GuardOutcome { rule, .. }
            | Self::Fired { rule, .. }
            | Self::Operand { rule, .. }
            | Self::Binder { rule, .. } => rule,
        }
    }
}

/// A fact with its rule resolved to a catalog id.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ResolvedFact {
    /// The catalog id of the fact's rule.
    pub(crate) id: String,
    /// Whether the rule is a rewrite rule (else an equation).
    pub(crate) rewrite: bool,
    /// The fact.
    pub(crate) fact: CoverageFact,
}

/// Resolve a coverage target's facts against `catalog` (relative, files recorded at
/// `recorded`): each fact's rule to the id of one entry ([`resolve_axiom`]). A target with no
/// fact is refused.
pub(crate) fn resolve(
    target: &CoverageTarget,
    catalog: &[CompiledRuleOutput],
    recorded: &rule::RecordedPaths,
) -> Result<Vec<ResolvedFact>, TargetProblem> {
    if target.facts.is_empty() {
        return Err(TargetProblem::Unsupported(
            "a coverage target needs at least one fact".into(),
        ));
    }
    target
        .facts
        .iter()
        .map(|fact| {
            let (id, kind) = resolve_axiom(catalog, fact.rule(), recorded)?;
            Ok(ResolvedFact {
                id,
                rewrite: kind == CompiledRuleKind::Rewrite,
                fact: fact.clone(),
            })
        })
        .collect()
}

/// Resolve `rule` to the id of one catalog entry for a coverage fact: as a rule target's
/// reference resolves ([`rule::resolve_rule_recorded`]), except that an equation is accepted,
/// and so is an id several equal written axioms share (the records name the id, and so does
/// every reader of them). An entry whose id is `UNKNOWN` or that is not executable is refused:
/// the backend records nothing a reader can attribute to it.
pub(crate) fn resolve_axiom(
    catalog: &[CompiledRuleOutput],
    reference: &RuleRef,
    recorded: &rule::RecordedPaths,
) -> Result<(String, CompiledRuleKind), TargetProblem> {
    let entry = rule::matching_entry(catalog, reference, recorded)?;
    if entry.id == "UNKNOWN" {
        return Err(TargetProblem::UnknownId);
    }
    if !entry.executable {
        return Err(TargetProblem::NotExecutable);
    }
    Ok((entry.id.clone(), entry.kind))
}

/// What a run of a coverage target must record: the guard outcomes of the rules its guard
/// facts name, and the bindings its operand, binder and alternative facts read.
pub(crate) fn collections(
    facts: &[ResolvedFact],
) -> (Option<GuardCollection>, Option<BindingCollection>) {
    let mut guards = BTreeSet::new();
    let mut symbols = BTreeSet::new();
    let mut binders = BTreeMap::<(String, String), usize>::new();
    let mut bindings = false;
    for fact in facts {
        match &fact.fact {
            CoverageFact::GuardNode { .. } | CoverageFact::GuardOutcome { .. } => {
                guards.insert(fact.id.clone());
            }
            CoverageFact::Fired { lhs, rhs, .. } => bindings |= lhs.is_some() || rhs.is_some(),
            CoverageFact::Operand { symbol, .. } => {
                bindings = true;
                symbols.insert(symbol.clone());
            }
            CoverageFact::Binder { variable, cap, .. } => {
                bindings = true;
                let slot = binders
                    .entry((fact.id.clone(), variable.clone()))
                    .or_default();
                *slot = (*slot).max(*cap);
            }
        }
    }
    let guards = (!guards.is_empty()).then(|| GuardCollection::new(guards));
    let bindings = bindings.then(|| BindingCollection {
        symbols: symbols.into_iter().collect(),
        binders: binders
            .into_iter()
            .map(|((axiom, variable), cap)| BinderSelection {
                axiom,
                variable,
                cap,
            })
            .collect(),
    });
    (guards, bindings)
}

/// Whether `coverage`, a run's, records `fact` (module documentation). `false` without
/// coverage, and for a record the run did not keep.
pub(crate) fn holds(
    fact: &ResolvedFact,
    coverage: Option<&RunCoverageOutput<KorePattern>>,
) -> bool {
    let Some(coverage) = coverage else {
        return false;
    };
    let id = fact.id.as_str();
    let guard = || {
        coverage
            .guards
            .iter()
            .flatten()
            .filter(move |guard| guard.axiom == id)
    };
    let bindings = coverage.bindings.as_ref();
    match &fact.fact {
        CoverageFact::GuardNode { node, truth, .. } => {
            let wanted = if *truth {
                NodeOutcomeOutput::True
            } else {
                NodeOutcomeOutput::False
            };
            guard().any(|guard| {
                guard
                    .nodes
                    .iter()
                    .any(|at| at.path == *node && at.reached.contains(&wanted))
            })
        }
        CoverageFact::GuardOutcome { held, .. } => guard().any(|guard| {
            guard.outcomes.iter().any(|outcome| match outcome {
                GuardOutcomeOutput::Held => *held,
                GuardOutcomeOutput::RefutedFalse
                | GuardOutcomeOutput::RefutedUndefined
                | GuardOutcomeOutput::RefutedDecided => !*held,
                _ => false,
            })
        }),
        CoverageFact::Fired {
            lhs: None,
            rhs: None,
            ..
        } => {
            if fact.rewrite {
                rule::committed(id, Some(coverage)) == Some(true)
            } else {
                rule::applied(id, Some(coverage))
            }
        }
        CoverageFact::Fired { lhs, rhs, .. } => bindings.is_some_and(|bindings| {
            bindings
                .alternatives
                .iter()
                .any(|taken| taken.axiom == id && taken.lhs == *lhs && taken.rhs == *rhs)
        }),
        CoverageFact::Operand { symbol, .. } => bindings.is_some_and(|bindings| {
            bindings
                .operands
                .iter()
                .any(|operands| operands.axiom == id && operands.symbols.contains(symbol))
        }),
        CoverageFact::Binder {
            variable, values, ..
        } => bound_values(fact, coverage, variable)
            .is_some_and(|bound| bound.iter().any(|value| values.contains(value))),
    }
}

/// The values the run's fired instances of `fact`'s rule bound to `variable`, as the bindings
/// record them; `None` when none were recorded.
pub(crate) fn bound_values<'c>(
    fact: &ResolvedFact,
    coverage: &'c RunCoverageOutput<KorePattern>,
    variable: &str,
) -> Option<&'c [String]> {
    coverage
        .bindings
        .as_ref()?
        .binders
        .iter()
        .find(|binder| binder.axiom == fact.id && binder.variable == variable)
        .map(|binder| binder.values.as_slice())
}
