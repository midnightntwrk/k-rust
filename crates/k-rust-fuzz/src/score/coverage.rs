//! The score of a coverage target (CS-8; `crate::target::coverage`).
//!
//! A coverage target is reached when the run records one of its facts, so a case is as near as
//! its nearest fact: the score is the least, over the facts, of each fact's score, compared as
//! every score is (rule-graph level, then guard distance; `super::Score`).
//!
//! - A guard fact (a node reached with a truth, the guard held or refuted) of a rule whose
//!   condition the case entered (the rule is in coverage `matched`) is at level 0, and its guard
//!   distance is the least, over the rule's recorded entries, of how far the entry is from the
//!   valuation that reaches the node with the truth, or from the outcome
//!   (`super::records::goal_entries`): the guard's recorded truths are the distance. A rule
//!   whose condition the case did not enter is scored as a rule target's case is
//!   ([`super::RuleScorer`]): the rule's step needs its condition entered first.
//! - A firing is scored as a rule target's case is.
//! - An operand or binder fact of a rule the case fired is at level 0; a binder's guard distance
//!   is the least normalized distance on the number line between a value the run bound and a
//!   value the fact asks for, and an operand's head has no order, so it has none. A rule the
//!   case did not fire is scored as a rule target's case is.
//!
//! An equation is in no rule graph and records no condition entries (`collectConditions` names
//! rewrite rules only), so an equation's fact scores level 0 with no guard distance where the
//! case entered the equation's condition (a guard fact) or applied it (any other fact), and no
//! level otherwise. As every score, this ranks cases for the climb and is never evidence.

use k_rust::backend::RunCoverageOutput;
use k_rust::kore::ast::Pattern as KorePattern;
use num_bigint::BigInt;

use super::{
    Distance, Guard, Level, Operand, RuleScorer, Score, Scored, Signals,
    records::{GuardGoal, goal_entries},
};
use crate::graph::RuleGraph;
use crate::target::{CoverageFact, coverage::ResolvedFact};

/// The scorer of a coverage target: each fact with the rule scorer of its rule, where the rule
/// is a rewrite rule.
#[derive(Clone, Debug)]
pub(crate) struct CoverageScorer {
    goals: Vec<(ResolvedFact, Option<RuleScorer>)>,
}

impl CoverageScorer {
    /// The scorer of a coverage target with `facts` over `graph`.
    pub(crate) fn new(graph: &RuleGraph, facts: &[ResolvedFact]) -> Self {
        Self {
            goals: facts
                .iter()
                .map(|fact| {
                    let rule = fact.rewrite.then(|| RuleScorer::new(graph, &fact.id));
                    (fact.clone(), rule)
                })
                .collect(),
        }
    }

    /// The rules whose condition entries the score reads: each rewrite fact's rule and its
    /// direct predecessors, sorted.
    pub(crate) fn condition_rules(&self) -> Vec<String> {
        let mut rules = std::collections::BTreeSet::new();
        for (_, rule) in &self.goals {
            if let Some(rule) = rule {
                rules.extend(rule.condition_rules());
            }
        }
        rules.into_iter().collect()
    }

    /// The score of a `miss` case with `signals`: the least of its facts' scores, the first of
    /// equal ones.
    pub(crate) fn score(&self, signals: Signals<'_>) -> Scored {
        let mut best: Option<Scored> = None;
        for (fact, rule) in &self.goals {
            let scored = fact_score(fact, rule.as_ref(), signals);
            if best.as_ref().is_none_or(|best| scored.score < best.score) {
                best = Some(scored);
            }
        }
        best.unwrap_or(Scored {
            score: Score {
                level: Level::Unreached,
                guard: Guard::Unknown,
            },
            reads: Vec::new(),
        })
    }
}

/// The score of one fact (module documentation).
fn fact_score(fact: &ResolvedFact, rule: Option<&RuleScorer>, signals: Signals<'_>) -> Scored {
    let id = fact.id.as_str();
    let at = |guard: Guard, reads: Vec<Operand>| Scored {
        score: Score {
            level: Level::At(0),
            guard,
        },
        reads,
    };
    let elsewhere = || match rule {
        Some(rule) => rule.score(signals),
        None => Scored {
            score: Score {
                level: Level::Unreached,
                guard: Guard::Unknown,
            },
            reads: Vec::new(),
        },
    };
    let entered = signals.matched.iter().any(|rule| rule == id);
    let applied = signals.applied.iter().any(|rule| rule == id);
    match &fact.fact {
        CoverageFact::GuardNode { node, truth, .. } => {
            if !entered {
                return elsewhere();
            }
            least_entry(goal_entries(
                conditions(signals),
                id,
                GuardGoal::Node(node, *truth),
            ))
            .map_or_else(
                || at(Guard::Unknown, Vec::new()),
                |(distance, reads)| at(Guard::Defined(distance), reads),
            )
        }
        CoverageFact::GuardOutcome { held, .. } => {
            if !entered {
                return elsewhere();
            }
            least_entry(goal_entries(
                conditions(signals),
                id,
                GuardGoal::Outcome(*held),
            ))
            .map_or_else(
                || at(Guard::Unknown, Vec::new()),
                |(distance, reads)| at(Guard::Defined(distance), reads),
            )
        }
        CoverageFact::Fired { .. } => match rule {
            Some(rule) => rule.score(signals),
            None if entered => at(Guard::Unknown, Vec::new()),
            None => elsewhere(),
        },
        CoverageFact::Operand { .. } => {
            if applied {
                at(Guard::Unknown, Vec::new())
            } else {
                elsewhere()
            }
        }
        CoverageFact::Binder {
            variable, values, ..
        } => {
            let bound = signals.coverage.and_then(|coverage| {
                crate::target::coverage::bound_values(fact, coverage, variable)
            });
            match bound {
                Some(bound) => at(
                    nearest_value(bound, values).map_or(Guard::Unknown, Guard::Defined),
                    Vec::new(),
                ),
                None if applied => at(Guard::Unknown, Vec::new()),
                None => elsewhere(),
            }
        }
    }
}

/// The entry of least distance (the first of equal ones), with its reads.
fn least_entry(entries: Vec<(Option<Distance>, Vec<Operand>)>) -> Option<(Distance, Vec<Operand>)> {
    let mut best: Option<(Distance, Vec<Operand>)> = None;
    for (distance, reads) in entries {
        if let Some(distance) = distance
            && best.as_ref().is_none_or(|(least, _)| distance < *least)
        {
            best = Some((distance, reads));
        }
    }
    best
}

/// The least normalized distance `|b - v| / (|b - v| + 1)` between a value `b` of `bound` and
/// a value `v` of `wanted`, both decimal `Int` literals; `None` when either side has no integer.
fn nearest_value(bound: &[String], wanted: &[String]) -> Option<Distance> {
    let parse = |values: &[String]| {
        values
            .iter()
            .filter_map(|value| value.parse::<BigInt>().ok())
            .collect::<Vec<_>>()
    };
    let (bound, wanted) = (parse(bound), parse(wanted));
    bound
        .iter()
        .flat_map(|b| wanted.iter().map(move |v| (b - v).magnitude().clone()))
        .min()
        .map(Distance::normalized)
}

/// The condition records of the case's run, if it kept them.
fn conditions<'a>(
    signals: Signals<'a>,
) -> &'a [k_rust::backend::RuleConditionsOutput<KorePattern>] {
    signals
        .coverage
        .and_then(|coverage: &'a RunCoverageOutput<KorePattern>| coverage.conditions.as_deref())
        .unwrap_or(&[])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_binder_is_as_near_as_its_nearest_bound_value() {
        let strings = |values: &[&str]| values.iter().map(|v| (*v).to_owned()).collect::<Vec<_>>();
        let near = nearest_value(&strings(&["3", "100"]), &strings(&["7", "112"]));
        let far = nearest_value(&strings(&["3"]), &strings(&["9"]));
        assert_eq!(near, Some(Distance::normalized(4u32.into())));
        assert!(near < far);
        assert_eq!(nearest_value(&strings(&["x"]), &strings(&["1"])), None);
    }
}
