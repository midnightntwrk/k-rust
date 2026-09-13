//! Named work counters for the compiler and the backend.
//!
//! Every crate of the workspace can count algorithmic work through this module because
//! `k-rust-kore` is the one crate all of them depend on. The module has no dependency on the KORE
//! types and adds none to the crate.
//!
//! The counters exist in every build so that call sites need no `cfg`. Without the `measure`
//! Cargo feature, [`add`] and [`bump`] are empty inline functions and [`snapshot`] returns zeros;
//! nothing is read from the environment and no output changes. With the feature, the counters are
//! thread-local: `cargo test` runs tests on several threads and a test must not see another test's
//! increments. The `krust` binary does its work on the main thread, so the main thread's counters
//! are the whole process for the one-shot subcommands.
//!
//! Tests take a [`snapshot`] before and after the code under test and assert on
//! [`Snapshot::delta`], so no test depends on the counters being zero when it starts. [`reset`]
//! serves the process-exit dump and the parser's existing test helpers.
//!
//! The counter names are a schema for the dump written by `krust` under `KRUST_COUNTERS`; a
//! rename is a contract change and bumps the dump's `version`.

/// One counted quantity. The discriminant indexes the counter array.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
#[repr(u16)]
pub enum Counter {
    // kompile (frontend)
    /// Full module-catalog rebuilds (`ResolvedDefinition::resolve`).
    KompileResolveCalls,
    /// Production-index rebases after a production-changing pass.
    KompileRebaseCalls,
    /// Rule bubbles parsed (one Earley parse plus sort inference each).
    KompileRuleBubblesParsed,
    /// Sentence count of the transformed definition, written once per compile.
    KompileSentencesTransformed,
    // parser (frontend)
    /// Earley parse entries; the filtered/unfiltered prediction retry doubles it.
    ParserParseAttempts,
    /// FIRST/nullable analysis builds, cached per grammar.
    ParserPredictionAnalysisBuilds,
    /// Predicted productions added to a chart.
    ParserChartPredictionAttempts,
    /// Predictions skipped by the FIRST-set filter, terminal-first productions.
    ParserTerminalPredictionsSkipped,
    /// Predictions skipped by the FIRST-set filter, nonterminal-first productions.
    ParserNonterminalPredictionsSkipped,
    /// Packed-term candidates built for completed states.
    ParserChartCompletionCandidates,
    /// Full structural comparisons after a packed fingerprint tie.
    ParserPackedStructuralComparisons,
    /// Packed nodes materialised into unpacked terms.
    ParserUnpackedNodes,
    /// Application resolutions during disambiguation of the packed forest.
    ParserPackedApplicationResolutions,
    /// Priority computations during disambiguation of the packed forest.
    ParserPackedPriorityComputations,
    /// Chart insertion attempts.
    ParserChartAddCalls,
    /// Chart insertions that changed a state and re-enqueued it.
    ParserChartStateChanges,
    /// Agenda pops of the Earley dispatch loop.
    ParserChartAgendaPops,
    /// Agenda pops of a state popped before (incremental ambiguity revisits).
    ParserChartRevisitPops,
    /// Derivations iterated per dispatched state.
    ParserChartDerivationsRead,
    /// Completed-nodes cache lookups that hit.
    ParserCompletedNodesHits,
    /// Completed-nodes cache lookups that rebuilt.
    ParserCompletedNodesMisses,
    /// Z3 check-sat calls issued by sort inference.
    ParserZ3Checks,
    // backend
    /// States popped by the execution loop, one per rewrite step attempted.
    RewriteSteps,
    /// Rule applications attempted, including pre-matched entries.
    RewriteRuleAttempts,
    /// Rule applications whose left-hand side failed to match.
    RewriteMatchFailures,
    /// Rules that unified and produced successors.
    RewriteRulesApplied,
    /// Indeterminate-match recoveries.
    RewriteIndeterminateRecoveries,
    /// One-way matching problems started.
    MatchingProblems,
    /// Pattern/subject pairs processed by the matcher.
    MatchingPairs,
    /// AC matching sub-problems over map and set collections.
    MatchingCollectionProblems,
    /// Unification problems started.
    UnificationProblems,
    /// Iterations of the bounded fixed-point simplification loop.
    SimplifyRounds,
    /// Function-equation trials.
    SimplifyEquationAttempts,
    /// Hooked builtin evaluations that produced a result.
    SimplifyBuiltinEvaluations,
    /// SMT queries issued, including result-cache hits.
    SmtQueries,
    /// SMT queries that ran a solver instance.
    SmtSolverRuns,
    /// Search states dropped by the per-depth visited set.
    SearchStatesDeduplicated,
    /// Proof states explored.
    ProofStatesExplored,
    /// Per-state implication checks against the claim right-hand side.
    ProofImplicationChecks,
    /// Terms constructed.
    TermConstructed,
}

impl Counter {
    /// Number of counters.
    pub const COUNT: usize = 40;

    /// Every counter in declaration order, which is also the dump's key order.
    pub const ALL: [Counter; Self::COUNT] = [
        Counter::KompileResolveCalls,
        Counter::KompileRebaseCalls,
        Counter::KompileRuleBubblesParsed,
        Counter::KompileSentencesTransformed,
        Counter::ParserParseAttempts,
        Counter::ParserPredictionAnalysisBuilds,
        Counter::ParserChartPredictionAttempts,
        Counter::ParserTerminalPredictionsSkipped,
        Counter::ParserNonterminalPredictionsSkipped,
        Counter::ParserChartCompletionCandidates,
        Counter::ParserPackedStructuralComparisons,
        Counter::ParserUnpackedNodes,
        Counter::ParserPackedApplicationResolutions,
        Counter::ParserPackedPriorityComputations,
        Counter::ParserChartAddCalls,
        Counter::ParserChartStateChanges,
        Counter::ParserChartAgendaPops,
        Counter::ParserChartRevisitPops,
        Counter::ParserChartDerivationsRead,
        Counter::ParserCompletedNodesHits,
        Counter::ParserCompletedNodesMisses,
        Counter::ParserZ3Checks,
        Counter::RewriteSteps,
        Counter::RewriteRuleAttempts,
        Counter::RewriteMatchFailures,
        Counter::RewriteRulesApplied,
        Counter::RewriteIndeterminateRecoveries,
        Counter::MatchingProblems,
        Counter::MatchingPairs,
        Counter::MatchingCollectionProblems,
        Counter::UnificationProblems,
        Counter::SimplifyRounds,
        Counter::SimplifyEquationAttempts,
        Counter::SimplifyBuiltinEvaluations,
        Counter::SmtQueries,
        Counter::SmtSolverRuns,
        Counter::SearchStatesDeduplicated,
        Counter::ProofStatesExplored,
        Counter::ProofImplicationChecks,
        Counter::TermConstructed,
    ];

    /// The dump key of the counter, `family.quantity`.
    pub const fn name(self) -> &'static str {
        match self {
            Counter::KompileResolveCalls => "kompile.resolve_calls",
            Counter::KompileRebaseCalls => "kompile.rebase_calls",
            Counter::KompileRuleBubblesParsed => "kompile.rule_bubbles_parsed",
            Counter::KompileSentencesTransformed => "kompile.sentences_transformed",
            Counter::ParserParseAttempts => "parser.parse_attempts",
            Counter::ParserPredictionAnalysisBuilds => "parser.prediction_analysis_builds",
            Counter::ParserChartPredictionAttempts => "parser.chart_prediction_attempts",
            Counter::ParserTerminalPredictionsSkipped => "parser.terminal_predictions_skipped",
            Counter::ParserNonterminalPredictionsSkipped => {
                "parser.nonterminal_predictions_skipped"
            }
            Counter::ParserChartCompletionCandidates => "parser.chart_completion_candidates",
            Counter::ParserPackedStructuralComparisons => "parser.packed_structural_comparisons",
            Counter::ParserUnpackedNodes => "parser.unpacked_nodes",
            Counter::ParserPackedApplicationResolutions => "parser.packed_application_resolutions",
            Counter::ParserPackedPriorityComputations => "parser.packed_priority_computations",
            Counter::ParserChartAddCalls => "parser.chart_add_calls",
            Counter::ParserChartStateChanges => "parser.chart_state_changes",
            Counter::ParserChartAgendaPops => "parser.chart_agenda_pops",
            Counter::ParserChartRevisitPops => "parser.chart_revisit_pops",
            Counter::ParserChartDerivationsRead => "parser.chart_derivations_read",
            Counter::ParserCompletedNodesHits => "parser.completed_nodes_hits",
            Counter::ParserCompletedNodesMisses => "parser.completed_nodes_misses",
            Counter::ParserZ3Checks => "parser.z3_checks",
            Counter::RewriteSteps => "rewrite.steps",
            Counter::RewriteRuleAttempts => "rewrite.rule_attempts",
            Counter::RewriteMatchFailures => "rewrite.match_failures",
            Counter::RewriteRulesApplied => "rewrite.rules_applied",
            Counter::RewriteIndeterminateRecoveries => "rewrite.indeterminate_recoveries",
            Counter::MatchingProblems => "matching.problems",
            Counter::MatchingPairs => "matching.pairs",
            Counter::MatchingCollectionProblems => "matching.collection_problems",
            Counter::UnificationProblems => "unification.problems",
            Counter::SimplifyRounds => "simplify.rounds",
            Counter::SimplifyEquationAttempts => "simplify.equation_attempts",
            Counter::SimplifyBuiltinEvaluations => "simplify.builtin_evaluations",
            Counter::SmtQueries => "smt.queries",
            Counter::SmtSolverRuns => "smt.solver_runs",
            Counter::SearchStatesDeduplicated => "search.states_deduplicated",
            Counter::ProofStatesExplored => "proof.states_explored",
            Counter::ProofImplicationChecks => "proof.implication_checks",
            Counter::TermConstructed => "term.constructed",
        }
    }
}

/// The values of every counter at one moment, indexed by [`Counter`] discriminant.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Snapshot(pub [u64; Counter::COUNT]);

impl Default for Snapshot {
    fn default() -> Self {
        Snapshot([0; Counter::COUNT])
    }
}

impl Snapshot {
    /// The value of one counter.
    pub fn get(&self, counter: Counter) -> u64 {
        self.0[counter as usize]
    }

    /// The counter-wise difference `self - before`, saturating at zero.
    pub fn delta(&self, before: &Snapshot) -> Snapshot {
        let mut delta = [0; Counter::COUNT];
        for (index, value) in delta.iter_mut().enumerate() {
            *value = self.0[index].saturating_sub(before.0[index]);
        }
        Snapshot(delta)
    }

    /// Every `(name, value)` pair in [`Counter::ALL`] order.
    pub fn iter(&self) -> impl Iterator<Item = (&'static str, u64)> + '_ {
        Counter::ALL
            .iter()
            .map(move |counter| (counter.name(), self.get(*counter)))
    }
}

/// Add one to a counter.
#[inline(always)]
pub fn bump(counter: Counter) {
    add(counter, 1);
}

pub use imp::{add, reset, snapshot};

#[cfg(feature = "measure")]
mod imp {
    use std::cell::Cell;

    use super::{Counter, Snapshot};

    thread_local! {
        static COUNTERS: [Cell<u64>; Counter::COUNT] =
            const { [const { Cell::new(0) }; Counter::COUNT] };
    }

    /// Add `n` to a counter of the current thread, wrapping on overflow.
    #[inline]
    pub fn add(counter: Counter, n: u64) {
        COUNTERS.with(|counters| {
            let cell = &counters[counter as usize];
            cell.set(cell.get().wrapping_add(n));
        });
    }

    /// Zero every counter of the current thread.
    pub fn reset() {
        COUNTERS.with(|counters| {
            for cell in counters {
                cell.set(0);
            }
        });
    }

    /// Copy every counter of the current thread.
    pub fn snapshot() -> Snapshot {
        COUNTERS.with(|counters| {
            let mut values = [0; Counter::COUNT];
            for (value, cell) in values.iter_mut().zip(counters) {
                *value = cell.get();
            }
            Snapshot(values)
        })
    }
}

#[cfg(not(feature = "measure"))]
mod imp {
    use super::{Counter, Snapshot};

    /// Counting is compiled out without the `measure` feature.
    #[inline(always)]
    pub fn add(_counter: Counter, _n: u64) {}

    /// Counting is compiled out without the `measure` feature.
    #[inline(always)]
    pub fn reset() {}

    /// Counting is compiled out without the `measure` feature; every counter reads as zero.
    #[inline(always)]
    pub fn snapshot() -> Snapshot {
        Snapshot::default()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    #[test]
    fn all_lists_forty_distinct_counters_with_distinct_names_in_index_order() {
        assert_eq!(Counter::ALL.len(), Counter::COUNT);
        let names = Counter::ALL
            .iter()
            .map(|counter| counter.name())
            .collect::<BTreeSet<_>>();
        assert_eq!(names.len(), Counter::COUNT);
        for (index, counter) in Counter::ALL.iter().enumerate() {
            assert_eq!(*counter as usize, index);
            let (family, quantity) = counter.name().split_once('.').unwrap();
            assert!(!family.is_empty() && !quantity.is_empty());
        }
        assert_eq!(Counter::ALL.first(), Some(&Counter::KompileResolveCalls));
        assert_eq!(Counter::ALL.last(), Some(&Counter::TermConstructed));
    }

    #[test]
    fn snapshot_iterates_in_all_order_and_reads_by_counter() {
        let mut values = [0; Counter::COUNT];
        for (index, value) in values.iter_mut().enumerate() {
            *value = index as u64 * 3;
        }
        let snapshot = Snapshot(values);
        assert_eq!(snapshot.get(Counter::TermConstructed), 39 * 3);
        let names = snapshot.iter().map(|(name, _)| name).collect::<Vec<_>>();
        let expected = Counter::ALL.map(Counter::name);
        assert_eq!(names, expected);
        assert!(snapshot.iter().all(|(_, value)| value % 3 == 0));
    }

    #[test]
    fn delta_subtracts_counter_wise_and_saturates() {
        let mut before = Snapshot::default();
        before.0[Counter::MatchingPairs as usize] = 7;
        let mut after = Snapshot::default();
        after.0[Counter::MatchingPairs as usize] = 10;
        after.0[Counter::RewriteSteps as usize] = 2;
        let delta = after.delta(&before);
        assert_eq!(delta.get(Counter::MatchingPairs), 3);
        assert_eq!(delta.get(Counter::RewriteSteps), 2);
        assert_eq!(before.delta(&after).get(Counter::MatchingPairs), 0);
    }

    #[cfg(feature = "measure")]
    #[test]
    fn add_bump_snapshot_and_reset_round_trip_on_the_current_thread() {
        let before = snapshot();
        add(Counter::RewriteSteps, 5);
        bump(Counter::RewriteSteps);
        bump(Counter::TermConstructed);
        let delta = snapshot().delta(&before);
        assert_eq!(delta.get(Counter::RewriteSteps), 6);
        assert_eq!(delta.get(Counter::TermConstructed), 1);
        assert_eq!(delta.get(Counter::SmtQueries), 0);

        let other_thread = std::thread::spawn(|| snapshot().get(Counter::RewriteSteps));
        assert_eq!(other_thread.join().unwrap(), 0);

        reset();
        assert_eq!(snapshot(), Snapshot::default());
    }

    #[cfg(not(feature = "measure"))]
    #[test]
    fn add_bump_snapshot_and_reset_round_trip_on_the_current_thread() {
        add(Counter::RewriteSteps, 5);
        bump(Counter::TermConstructed);
        assert_eq!(snapshot(), Snapshot::default());
        reset();
        assert_eq!(snapshot(), Snapshot::default());
    }
}
