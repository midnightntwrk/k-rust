//! Pattern targets `at: any-state` (ARCHITECTURE 4.1): the target is reached on a path when one
//! of its normalized configurations matches the pattern. Owner: FZ-ANYSTATE.
//!
//! A case runs once, through `Backend::execute_observed` with every observation event
//! ([`Executor::run_any_state`]), under the same cancellation scope, per-case safety limit and
//! work budget as every case. The leaves' paths are merged into the observer target's path tree
//! (`super::observer`), and the configurations shown are the ones an observer is shown, plus the
//! initial one:
//! - at the root, the initial configuration after normalization (the `before` of the first
//!   transition, or the state of a leaf that took no step);
//! - at every other node, the configuration its transition reached, after normalization (the
//!   `before` of the next transition, or the state of a leaf that ends there);
//! - never the state of a `work-bound`, `timeout` or `cancelled` leaf, which is the stopped,
//!   unnormalised state the worklist held, not a reached configuration (`classify`'s cut-leaf
//!   contract).
//!
//! Where a leaf ends at a node that another path leaves (an undefined step's leaf, under its
//! own path condition `#Not(#Ceil(...))`, beside the defined step), the configuration judged
//! there is the `before` of the transition that leaves it, the one the run went on from.
//!
//! Each shown configuration is judged as an end leaf's state is (ARCHITECTURE 5.2): it *reaches*
//! when it is decided (no constraint, no variable), ceil-free and matches with empty constraints
//! ([`ConfigurationVerdict`]). A leaf *reaches* the target when a configuration on its path
//! reaches; its hit step is the depth of the first such configuration, the number of committed
//! steps from the initial configuration, 0 for the initial configuration itself, which the
//! witness records ([`crate::report::Reaching::step`]). Nothing below a reaching configuration
//! is matched.
//!
//! The case is then classed by [`crate::exec::classify_ends_explained`], as every leaf-judged
//! target's is: a hit needs a reaching leaf that is clean (ARCHITECTURE 5.2) and, under
//! `run-to-completion`, a natural end (and a data end with `data-end`). The leaf's diagnostics
//! hold the facts of its whole path, so of the path up to the reaching configuration too, and the
//! run's facts are on every leaf. A reaching path later cut by a bound is therefore `unsupported`
//! (`reached-cut-path`), or `reached-unfinished` under `run-to-completion`, never a hit, as an
//! observer's accepted path is (P7-ADDENDUM open question 4, taken as recommended until KINK-27
//! tells a leaf's own facts from budget copies).
//!
//! A configuration that cannot be decided (it matches but is not ceil-free, its match is
//! undecided, it is not a decided state, or it does not decode or internalize), or a node the
//! tree shows no configuration at (a path without complete observation events, whose subtree
//! is then not walked), may hide a reaching configuration: the case is then `unsupported` unless
//! some leaf is a hit, with the first reason in [`UnjudgedReason`]'s order.
//!
//! Cost: observed execution carries two configurations per step and an event per equation
//! evaluated, and each configuration shown before the first reach on its path is decoded,
//! internalized and matched once (twice when the target evaluates something, in both evaluation
//! modes). Observed execution dominates: on IMP's `loop.imp` (306 steps) a case takes about 4 ms
//! through `execute`, 140 ms through observed execution with the observer's rewrite-rule filter,
//! 176 ms with every event, and 237 ms with the configurations matched (FZ-ANYSTATE report). A
//! syntactic prefilter could save at most the matching's quarter, and only by deciding which
//! configurations the matcher refutes, so there is none.

use k_rust::backend::{CancellationToken, ExecutionLeaf};

use super::{
    HitSite, Judgement, ResolvedTarget,
    observer::{defect, explained, path_tree, unobserved},
};
use crate::{
    exec::{
        self, CaseResult, ConfigurationVerdict, DeterminismBreak, OutcomeClass,
        PlannedConfiguration, UnjudgedReason,
    },
    report::EngineDefect,
};

#[cfg(test)]
#[path = "any_state_tests.rs"]
mod tests;

/// The configurations an any-state target judges on the path tree of `leaves`, by node index
/// (`crate::exec::run::ConfigurationPlan`): the node's parent, and the configuration shown there,
/// none at a node where a stopped leaf ends without successors.
pub(super) fn plan(leaves: &[ExecutionLeaf]) -> Vec<PlannedConfiguration<'_>> {
    let nodes = path_tree(leaves);
    let mut planned: Vec<PlannedConfiguration<'_>> = nodes
        .iter()
        .map(|node| PlannedConfiguration {
            parent: None,
            configuration: if node.stopped && node.edges.is_empty() {
                None
            } else {
                node.before.or(node.configuration)
            },
        })
        .collect();
    for (index, node) in nodes.iter().enumerate() {
        for edge in &node.edges {
            planned[edge.child].parent = Some(index);
        }
    }
    planned
}

/// What the walk over the verdicts found, per leaf of the observed result.
#[derive(Debug, Default, Eq, PartialEq)]
struct Reached {
    /// When a configuration on the leaf's path reaches the target, the depth of the first one.
    hit_steps: Vec<Option<u64>>,
    /// Whether that first reaching configuration's term holds a term-level `\and`
    /// ([`ConfigurationVerdict::Reaches`]); `false` for a leaf that reaches nothing.
    hit_conjunctions: Vec<bool>,
    /// The reasons of the configurations that could not be decided before any reach on their
    /// path, and [`UnjudgedReason::Unobservable`] for a node that shows no configuration.
    unresolved: Vec<UnjudgedReason>,
}

/// Walk the path tree of `leaves` with the configuration `verdicts` by node index
/// ([`ConfigurationVerdict`]).
///
/// # Errors
///
/// [`EngineDefect`] when a configuration the walk reaches carries no verdict.
fn walk(
    leaves: &[ExecutionLeaf],
    verdicts: &[ConfigurationVerdict],
) -> Result<Reached, EngineDefect> {
    let nodes = path_tree(leaves);
    if verdicts.len() != nodes.len() {
        return Err(defect(&format!(
            "{} configuration verdicts for a path tree of {} nodes",
            verdicts.len(),
            nodes.len()
        )));
    }
    let mut reached = Reached {
        hit_steps: vec![None; leaves.len()],
        hit_conjunctions: vec![false; leaves.len()],
        unresolved: Vec::new(),
    };
    // (node, depth, the depth of the first reaching configuration above it, whether that one
    // holds a term-level `\and`).
    let mut work: Vec<(usize, u64, Option<u64>, bool)> = vec![(0, 0, None, false)];
    while let Some((index, depth, mut hit, mut conjunction)) = work.pop() {
        let node = &nodes[index];
        if hit.is_none() {
            if node.stopped && node.edges.is_empty() {
                // The stopped state is no reached configuration: its leaves keep the reach of
                // the configurations above it (none here).
                continue;
            }
            if node.configuration.is_none() {
                // No complete observation of a path through it: the subtree is not shown.
                reached.unresolved.push(UnjudgedReason::Unobservable);
                continue;
            }
            match &verdicts[index] {
                ConfigurationVerdict::Reaches { term_conjunction } => {
                    hit = Some(depth);
                    conjunction = *term_conjunction;
                }
                ConfigurationVerdict::Refuted => {}
                ConfigurationVerdict::Unresolved(reason) => reached.unresolved.push(*reason),
                ConfigurationVerdict::NotJudged => {
                    return Err(defect(&format!(
                        "the configuration at depth {depth} of the path tree was not judged"
                    )));
                }
            }
        }
        for &leaf in &node.leaves {
            reached.hit_steps[leaf] = hit;
            reached.hit_conjunctions[leaf] = conjunction;
        }
        // The first successor is walked first.
        work.extend(
            node.edges
                .iter()
                .rev()
                .map(|edge| (edge.child, depth + 1, hit, conjunction)),
        );
    }
    Ok(reached)
}

impl ResolvedTarget {
    /// Judge an any-state case from its judged `result`, the raw observed `leaves` of the same
    /// run and the configuration `verdicts` ([`Executor::run_any_state`]), with the hit leaf's
    /// hit step for a hit (module documentation).
    ///
    /// A failed run is classed by its failure alone. A case outside the determinism contract,
    /// or whose `cancel` is cancelled by the time it is judged, is classed with no leaf reaching
    /// the target and lifted to `timeout` or `unsupported`, as an observer case is: such a stop
    /// may have hidden a reaching configuration, or decided one by the clock.
    ///
    /// # Errors
    ///
    /// [`EngineDefect`] from classification, when the observed leaves are not the judged
    /// result's, when a reached configuration carries no verdict, and for a `hit` class with
    /// no clean reaching leaf.
    ///
    /// [`Executor::run_any_state`]: crate::exec::Executor::run_any_state
    pub(super) fn judge_any_state(
        &self,
        result: &CaseResult,
        leaves: &[ExecutionLeaf],
        verdicts: &[ConfigurationVerdict],
        cancel: Option<&CancellationToken>,
    ) -> Result<(Judgement, Option<u64>), EngineDefect> {
        let run_to_completion = self.target.run_to_completion;
        let data_end = self.target.requires_data_end();
        if result.failure.is_some() {
            return exec::classify_explained(result, &[], run_to_completion)
                .map(|(class, reason)| (explained(class, reason), None));
        }
        let cancelled = cancel.is_some_and(CancellationToken::is_cancelled);
        let breaks = result.determinism_breaks();
        if result.safety_limit_hit || !breaks.is_empty() || cancelled {
            let clock =
                result.safety_limit_hit || breaks.contains(&DeterminismBreak::Clock) || cancelled;
            return unobserved(result, run_to_completion, clock).map(|judgement| (judgement, None));
        }
        if leaves.len() != result.leaves.len() {
            return Err(defect(&format!(
                "the observed run returned {} leaves where its judged result has {}",
                leaves.len(),
                result.leaves.len()
            )));
        }
        let walked = walk(leaves, verdicts)?;
        let reached: Vec<bool> = walked.hit_steps.iter().map(Option::is_some).collect();
        let (class, reason) =
            exec::classify_ends_explained(result, &reached, run_to_completion, data_end)?;
        if class != OutcomeClass::Hit
            && let Some(unresolved) = walked.unresolved.iter().copied().min()
        {
            // A configuration that could not be decided may reach the target: never a `miss`.
            let reason = reason.map_or(unresolved, |reason| reason.min(unresolved));
            return Ok((explained(OutcomeClass::Unsupported, Some(reason)), None));
        }
        if class != OutcomeClass::Hit {
            return Ok((explained(class, reason), None));
        }
        let leaf = result
            .leaves
            .iter()
            .zip(&reached)
            .position(|(leaf, reached)| {
                *reached
                    && leaf.is_clean()
                    && (!run_to_completion || leaf.natural_end)
                    && (!data_end || leaf.data_end == Some(true))
            });
        let Some(leaf) = leaf else {
            return Err(defect(
                "a case classed `hit` has no clean leaf that reaches the target",
            ));
        };
        let judgement = self.confirmable(
            Judgement {
                class,
                hit_site: Some(HitSite::Leaf(leaf)),
                blocked: false,
                reason,
                demoted_from: None,
            },
            result,
            walked.hit_conjunctions[leaf],
        );
        let hit_step = walked.hit_steps[leaf].filter(|_| judgement.class == OutcomeClass::Hit);
        Ok((judgement, hit_step))
    }
}
