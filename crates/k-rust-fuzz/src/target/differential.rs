//! The differential target: does the mutant reach a clean end that the baseline cannot reach on
//! the same input, or, on all paths, lose one the baseline reaches (ARCHITECTURE 4.3)?
//! Owner: FZ-08.
//!
//! A case runs the baseline on all paths and the mutant on the campaign's path mode, each on its
//! own backend, with hole values generated from the baseline's signature and internalized per
//! side. [`judge_pair`] then decides the case from the two [`CaseResult`]s alone.
//!
//! # Why the hit rule is sound
//!
//! An *added end* claims that the mutant reaches, on this input, a final configuration that the
//! baseline does not reach on any path. The baseline's set of final configurations is known only
//! when its all-paths run is complete: every leaf is a decided, clean end (`stuck`, or an
//! undefined step, whose configuration is the one before the step). A bound, a stop, an
//! undecided or unsupported leaf leaves paths unexplored, and an end outside a partial set proves
//! nothing; such a case is `baseline-incomplete`, never a miss. The mutant's configuration must
//! be a clean natural end (the program finished on the mutant) whose internalized term is built
//! from free constructors, injections, domain values and well-formed collections only, so that
//! it denotes itself and syntactic inequality is inequality of values. An implementation-chosen
//! value on either side would make the comparison depend on a choice k-rust made, not on the
//! definitions.
//!
//! A *removed end* is the same claim with the roles exchanged, so it needs the same facts the
//! other way round: the mutant's all-paths run is complete, and a baseline leaf that is a clean,
//! constructor-only natural end is not in the mutant's set. Only the all-paths mode can find it,
//! because one mutant path says nothing about the ends the mutant's other paths reach.
//!
//! # Comparison
//!
//! Each side's ends are held as a set of KORE patterns ordered by [`KorePattern`]'s `Ord`, whose
//! equality is structural, so two patterns are equal exactly when their printed KORE is equal.
//! Leaves are compared after k-rust's normalization, under which map and set entries are already
//! ordered.
//!
//! The whole configuration is compared, the `<generatedCounter>` cell included: an end that
//! differs from every end of the other side only in that cell is a kill. The compiled
//! definition's `<generatedCounter>` cell and its `freshGenerator` rules are part of each
//! definition's rewrite theory and fix the fresh constants a run mints, so the counter is a
//! component of the final configuration like any other cell. kink's whole-term oracle compares
//! the same complete terms, so the two agree on this point.

use std::collections::BTreeSet;

use k_rust::{backend::HaltReasonOutput, kore::ast::Pattern as KorePattern};

use crate::{
    error::CampaignError,
    exec::{self, CaseResult, LeafReport, OutcomeClass, TargetNeeds, UncleanReason},
    report::EngineDefect,
    spec::{BackendRoute, CaseOptions, CompiledDefinition, PathMode},
};

/// The request needs of the two sides of a differential case (ARCHITECTURE 4.3, 5.1).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DifferentialPlan {
    /// The baseline runs all paths, so that its set of ends can be complete; in the all-paths
    /// mode it also reports [`crate::exec::LeafReport::constructor_only`], for removed ends.
    pub(crate) baseline: TargetNeeds,
    /// The mutant runs on the campaign's path mode and reports
    /// [`crate::exec::LeafReport::constructor_only`].
    pub(crate) mutant: TargetNeeds,
}

/// The judgement of one baseline/mutant pair.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DifferentialJudgement {
    /// The case's class: `baseline-incomplete` when the baseline's ends are incomplete;
    /// otherwise `hit` for an added or a removed end, else the mutant's class.
    pub(crate) class: OutcomeClass,
    /// For a hit by an added end, the index of the mutant leaf whose configuration the baseline
    /// cannot reach.
    pub(crate) killing_leaf: Option<usize>,
    /// For a hit by a removed end (all-paths mode only), the index of the baseline leaf whose
    /// configuration the mutant cannot reach. A hit has at least one of the two indices.
    pub(crate) removed_end: Option<usize>,
}

impl DifferentialJudgement {
    const fn class(class: OutcomeClass) -> Self {
        Self {
            class,
            killing_leaf: None,
            removed_end: None,
        }
    }
}

/// The needs of each side for `options`: the baseline on all paths, whatever the campaign's
/// path mode; the mutant on the campaign's path mode, with the constructor-only judgement of
/// condition 4. In the all-paths mode the baseline's leaves carry that judgement too, since a
/// baseline end can then be the witness of a removed end. Neither side needs traces or terminal
/// rules: the differential target names no rule.
pub(crate) fn plan(options: &CaseOptions) -> DifferentialPlan {
    DifferentialPlan {
        baseline: TargetNeeds {
            paths: Some(PathMode::AllPaths),
            constructor_only: options.paths == PathMode::AllPaths,
            ..TargetNeeds::default()
        },
        mutant: TargetNeeds {
            constructor_only: true,
            paths: Some(options.paths),
            ..TargetNeeds::default()
        },
    }
}

/// Whether the campaign ends before any case with the result `equivalent`
/// (ARCHITECTURE 4.3, T-16): equal execution digests of baseline and mutant, and on the
/// rewrite-order route equal rewrite orders too.
///
/// Equal digests promise equal results for an equal module, options and initial state through
/// the routes that take no rewrite order (`docs/compatibility.md`, "Execution digest"). On
/// [`BackendRoute::SourceExecution`] the rewrite order reorders the rules of each priority, which
/// selects the one path `strategy: any` follows and, under `max_work`, what a bounded run
/// reaches, so the orders must be equal as well. The two sides must therefore also use one route,
/// one main module (the module the backend executes) and one syntax module (the grammar the
/// program and the hole values are parsed with, which decides each side's initial state).
/// Anything else is not `equivalent`, and the campaign runs its cases.
///
/// # Errors
///
/// [`CampaignError::Definition`] when a definition has no digest.
pub(crate) fn equivalent(
    baseline: &CompiledDefinition,
    mutant: &CompiledDefinition,
) -> Result<bool, CampaignError> {
    let digests_equal = baseline.execution_digest()? == mutant.execution_digest()?;
    let routes_equal = match (&baseline.route, &mutant.route) {
        (BackendRoute::FromDefinition, BackendRoute::FromDefinition) => true,
        (
            BackendRoute::SourceExecution {
                execution_rewrite_order: baseline_order,
            },
            BackendRoute::SourceExecution {
                execution_rewrite_order: mutant_order,
            },
        ) => baseline_order == mutant_order,
        (BackendRoute::FromDefinition, BackendRoute::SourceExecution { .. })
        | (BackendRoute::SourceExecution { .. }, BackendRoute::FromDefinition) => false,
    };
    Ok(digests_equal
        && routes_equal
        && baseline.main_module == mutant.main_module
        && baseline.syntax_module == mutant.syntax_module)
}

/// Judge one pair (ARCHITECTURE 4.3); `paths` is the campaign's path mode, which the mutant ran
/// on. A case is a hit by an *added end* if and only if:
/// 1. the baseline run with all paths is complete: every leaf is a clean `stuck` or `undefined`
///    end, with no bound, stop, timeout, unknown or unsupported leaf;
/// 2. the mutant leaf is a clean natural end;
/// 3. neither side carries an implementation-chosen value mark;
/// 4. the mutant leaf's internalized configuration is constructor-only (internal term kinds,
///    not KORE symbols);
/// 5. that configuration is not in the baseline's set of final configurations, compared as
///    printed KORE after k-rust's normalization.
///
/// In the all-paths mode a case is also a hit by a *removed end* if conditions 1 and 3 hold, the
/// mutant's run is complete in the sense of condition 1 with every end constructor-only, and
/// some baseline leaf is a clean natural end with a constructor-only configuration that is not
/// in the mutant's set of final configurations. The mutant's ends must be data too: a mutant end
/// such as an unevaluated application of a total function may denote the baseline's end, so its
/// syntactic difference proves nothing.
///
/// An incomplete baseline makes the case `baseline-incomplete`, whatever the mutant did.
/// Otherwise the mutant's leaves are classed by [`exec::classify`], a leaf "reaching the target"
/// when it is an added end. Two outcomes are neither a hit nor a pass, and are `unsupported`,
/// as a target-reaching leaf that is not clean is (ARCHITECTURE 5.3):
/// - an added or removed end exists, but some mutant leaf carries an implementation-chosen value
///   mark (condition 3 is a fact of the whole result);
/// - no kill exists, but some end outside the other side's set could not be judged: a clean
///   natural end that is not constructor-only, or a mutant `stuck` leaf that is not clean.
///
/// # Errors
///
/// [`EngineDefect`] from classification, or when a clean natural end outside the other side's
/// set carries no constructor-only judgement although [`plan`] asked for it.
pub(crate) fn judge_pair(
    baseline: &CaseResult,
    mutant: &CaseResult,
    paths: PathMode,
    run_to_completion: bool,
) -> Result<DifferentialJudgement, EngineDefect> {
    let Some(baseline_set) = complete_ends(baseline) else {
        return Ok(DifferentialJudgement::class(
            OutcomeClass::BaselineIncomplete,
        ));
    };
    let added = Verdicts::added(&baseline_set, mutant)?;
    let removed = match (paths, complete_ends(mutant)) {
        (PathMode::AllPaths, Some(mutant_set)) => Verdicts::removed(baseline, mutant, &mutant_set)?,
        (PathMode::OnePath, _) | (PathMode::AllPaths, None) => Verdicts::none(baseline),
    };
    let killing_leaf = added.kills.iter().position(|&kills| kills);
    let removed_end = removed.kills.iter().position(|&kills| kills);
    let class = exec::classify(mutant, &added.kills, run_to_completion)?;
    let chosen_value = mutant.leaves.iter().any(|leaf| {
        leaf.unclean
            .contains(&UncleanReason::ImplementationChosenValue)
    });
    if (killing_leaf.is_some() || removed_end.is_some()) && chosen_value {
        return Ok(DifferentialJudgement::class(OutcomeClass::Unsupported));
    }
    if class == OutcomeClass::Hit && killing_leaf.is_none() {
        return Err(EngineDefect {
            case: None,
            description: "classification reported a differential hit without a killing leaf"
                .to_owned(),
        });
    }
    if class == OutcomeClass::Hit || removed_end.is_some() {
        return Ok(DifferentialJudgement {
            class: OutcomeClass::Hit,
            killing_leaf: killing_leaf.filter(|_| class == OutcomeClass::Hit),
            removed_end,
        });
    }
    if added.undecided || removed.undecided {
        return Ok(DifferentialJudgement::class(OutcomeClass::Unsupported));
    }
    Ok(DifferentialJudgement::class(class))
}

/// A side's set of final configurations when its all-paths run is complete (condition 1, with
/// condition 3 for that side: a marked leaf is not clean), or `None`.
///
/// A complete run returned leaves, was not stopped by the safety limit, counted no stack stop,
/// SMT unknown or run allowance refusal, is inside the determinism contract (no stack stop in
/// its definition's load either, [`CaseResult::determinism_breaks`]), and every leaf is a clean `stuck` leaf or an undefined
/// step (`trivial`) whose only unclean reason is its halt: a decided, ceil-free configuration
/// with no diagnostic, the configuration before the undefined step. Load records are facts about
/// the definition and do not make a run incomplete (T-5).
fn complete_ends(result: &CaseResult) -> Option<BTreeSet<&KorePattern>> {
    let run_clean = result.failure.is_none()
        && !result.safety_limit_hit
        && result.stack_stops == 0
        && result.smt_unknowns == 0
        && result.run_allowance_refusals == 0
        && result.determinism_breaks().is_empty()
        && !result.leaves.is_empty();
    if !run_clean || !result.leaves.iter().all(complete_end) {
        return None;
    }
    Some(result.leaves.iter().map(|leaf| &leaf.state).collect())
}

/// Whether a leaf is an end a complete set may hold (condition 1).
fn complete_end(leaf: &LeafReport) -> bool {
    match leaf.halt {
        HaltReasonOutput::Stuck => leaf.is_clean(),
        HaltReasonOutput::Trivial => leaf
            .unclean
            .iter()
            .all(|reason| *reason == UncleanReason::Halt),
        _ => false,
    }
}

/// What one side's leaves show against the other side's complete set of ends.
#[derive(Debug, Eq, PartialEq)]
struct Verdicts {
    /// `kills[i]`: leaf `i` is a clean natural end (condition 2) whose configuration is
    /// constructor-only (condition 4) and not in the other side's set (condition 5).
    kills: Vec<bool>,
    /// Some end outside the other side's set could not be judged: a clean natural end that is
    /// not constructor-only, or (on the mutant side) a `stuck` leaf that is not clean.
    undecided: bool,
}

impl Verdicts {
    /// No judgement of `side`'s leaves.
    fn none(side: &CaseResult) -> Self {
        Self {
            kills: vec![false; side.leaves.len()],
            undecided: false,
        }
    }

    /// The mutant's added ends against the baseline's complete set.
    fn added(baseline: &BTreeSet<&KorePattern>, mutant: &CaseResult) -> Result<Self, EngineDefect> {
        Self::outside(mutant, baseline, "mutant")
    }

    /// The baseline's ends that the mutant's complete set of ends, `mutant_set`, lacks. Every
    /// baseline leaf is a clean end here (the baseline is complete), so no unclean leaf is met.
    /// When some mutant end is not constructor-only, an end the mutant lacks syntactically may
    /// still be one it reaches, so every such end is undecided rather than a kill.
    fn removed(
        baseline: &CaseResult,
        mutant: &CaseResult,
        mutant_set: &BTreeSet<&KorePattern>,
    ) -> Result<Self, EngineDefect> {
        let mut verdicts = Self::outside(baseline, mutant_set, "baseline")?;
        let mutant_is_data = mutant
            .leaves
            .iter()
            .all(|leaf| leaf.constructor_only == Some(true));
        if !mutant_is_data && verdicts.kills.contains(&true) {
            verdicts.kills.fill(false);
            verdicts.undecided = true;
        }
        Ok(verdicts)
    }

    /// The leaves of `side` whose configuration `others` lacks.
    fn outside(
        side: &CaseResult,
        others: &BTreeSet<&KorePattern>,
        role: &str,
    ) -> Result<Self, EngineDefect> {
        let mut verdicts = Self::none(side);
        for (index, leaf) in side.leaves.iter().enumerate() {
            // Only a stuck leaf is an end that may be a kill; an undefined step, a bound or a
            // stop is classed by `exec::classify`.
            if leaf.halt != HaltReasonOutput::Stuck || others.contains(&leaf.state) {
                continue;
            }
            if !leaf.is_clean() {
                verdicts.undecided = true;
            } else if leaf.natural_end {
                match leaf.constructor_only {
                    Some(true) => verdicts.kills[index] = true,
                    Some(false) => verdicts.undecided = true,
                    None => {
                        return Err(EngineDefect {
                            case: None,
                            description: format!(
                                "{role} leaf {index} is a natural end without the \
                                 constructor-only judgement the differential plan requests"
                            ),
                        });
                    }
                }
            }
            // A clean stuck leaf that is not a natural end is an abnormal stop: the program did
            // not finish on that path, so its configuration is no kill (condition 2).
        }
        Ok(verdicts)
    }
}

#[cfg(test)]
mod tests {
    use k_rust::kore::parser::parse_pattern;

    use super::*;
    use crate::{exec::CaseFailure, report::LoadRecord};

    /// A final configuration `<generatedTop>(<k>(.K), <out>(N), <generatedCounter>(C))`.
    fn config(out: i64, counter: i64) -> KorePattern {
        parse_pattern(&format!(
            "Lbl'-LT-'generatedTop'-GT-'{{}}(\
               Lbl'-LT-'k'-GT-'{{}}(dotk{{}}()), \
               Lbl'-LT-'out'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"{out}\")), \
               Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"{counter}\")))"
        ))
        .expect("the test configuration parses")
    }

    /// A clean natural end with the given constructor-only judgement.
    fn natural(state: KorePattern, constructor_only: Option<bool>) -> LeafReport {
        LeafReport {
            halt: HaltReasonOutput::Stuck,
            depth: 3,
            state,
            unclean: Vec::new(),
            natural_end: true,
            matches: Vec::new(),
            rewrites: Vec::new(),
            constructor_only,
        }
    }

    /// A leaf with `halt` and `unclean` that is not a natural end.
    fn leaf(halt: HaltReasonOutput, state: KorePattern, unclean: Vec<UncleanReason>) -> LeafReport {
        LeafReport {
            halt,
            depth: 3,
            state,
            unclean,
            natural_end: false,
            matches: Vec::new(),
            rewrites: Vec::new(),
            constructor_only: None,
        }
    }

    fn result(leaves: Vec<LeafReport>) -> CaseResult {
        CaseResult {
            leaves,
            work: 10,
            coverage: None,
            stack_stops: 0,
            smt_unknowns: 0,
            run_allowance_refusals: 0,
            load_records: Vec::new(),
            safety_limit_hit: false,
            failure: None,
        }
    }

    /// A complete baseline with the two ends 3 and 4 (the COIN baseline on `flip(3)`), judged
    /// constructor-only as in the all-paths mode.
    fn coin_baseline() -> CaseResult {
        result(vec![
            natural(config(3, 0), Some(true)),
            natural(config(4, 0), Some(true)),
        ])
    }

    fn judge(baseline: &CaseResult, mutant: &CaseResult, paths: PathMode) -> DifferentialJudgement {
        judge_pair(baseline, mutant, paths, false).expect("no engine defect")
    }

    fn added(baseline: &CaseResult, mutant: &CaseResult) -> Verdicts {
        let ends = complete_ends(baseline).expect("the baseline is complete");
        Verdicts::added(&ends, mutant).expect("no engine defect")
    }

    fn hit(killing_leaf: Option<usize>, removed_end: Option<usize>) -> DifferentialJudgement {
        DifferentialJudgement {
            class: OutcomeClass::Hit,
            killing_leaf,
            removed_end,
        }
    }

    const BOTH_MODES: [PathMode; 2] = [PathMode::OnePath, PathMode::AllPaths];

    // ---- plan

    #[test]
    fn baseline_runs_all_paths_and_mutant_the_campaign_mode() {
        for paths in BOTH_MODES {
            let plan = plan(&CaseOptions {
                paths,
                ..CaseOptions::default()
            });
            assert_eq!(plan.baseline.paths, Some(PathMode::AllPaths));
            assert_eq!(
                plan.baseline.constructor_only,
                paths == PathMode::AllPaths,
                "the baseline's ends are witnesses only in the all-paths mode"
            );
            assert_eq!(plan.mutant.paths, Some(paths));
            assert!(plan.mutant.constructor_only);
            for needs in [&plan.baseline, &plan.mutant] {
                assert!(!needs.trace);
                assert!(needs.terminal_rules.is_empty());
            }
        }
    }

    // ---- condition 1: completeness

    #[test]
    fn complete_baseline_holds_its_stuck_and_undefined_ends() {
        let undefined = config(7, 0);
        let baseline = result(vec![
            natural(config(3, 0), None),
            leaf(
                HaltReasonOutput::Trivial,
                undefined.clone(),
                vec![UncleanReason::Halt],
            ),
            // A clean abnormal stop is a final configuration too.
            leaf(HaltReasonOutput::Stuck, config(9, 0), Vec::new()),
        ]);
        let ends = complete_ends(&baseline).expect("complete");
        assert_eq!(ends.len(), 3);
        assert!(ends.contains(&undefined));
    }

    #[test]
    fn every_unclean_or_unfinished_leaf_makes_a_side_incomplete() {
        use HaltReasonOutput as H;
        let unfinished = [
            H::DepthBound,
            H::BreadthBound,
            H::WorkBound,
            H::Timeout,
            H::Cancelled,
            H::Vacuous,
            H::Terminal,
            H::Branch,
            H::CutPoint,
        ];
        for halt in unfinished {
            let baseline = result(vec![
                natural(config(3, 0), None),
                leaf(halt, config(4, 0), vec![UncleanReason::Halt]),
            ]);
            assert!(complete_ends(&baseline).is_none(), "{halt:?}");
        }
        let unclean = [
            UncleanReason::Undecided,
            UncleanReason::NotCeilFree,
            UncleanReason::ImplementationChosenValue,
            UncleanReason::ContradictedClaim,
            UncleanReason::IterationExhaustion,
            UncleanReason::Internalization("no".to_owned()),
        ];
        for reason in unclean {
            for (halt, mut reasons) in [(H::Stuck, vec![]), (H::Trivial, vec![UncleanReason::Halt])]
            {
                reasons.push(reason.clone());
                let baseline = result(vec![
                    natural(config(3, 0), None),
                    leaf(halt, config(4, 0), reasons),
                ]);
                assert!(complete_ends(&baseline).is_none(), "{halt:?} {reason:?}");
            }
        }
    }

    #[test]
    fn run_level_facts_make_a_side_incomplete() {
        let cases: [fn(&mut CaseResult); 7] = [
            |r| r.stack_stops = 1,
            |r| r.smt_unknowns = 1,
            |r| r.run_allowance_refusals = 1,
            |r| r.safety_limit_hit = true,
            |r| {
                r.failure = Some(CaseFailure::other("err"));
                r.leaves.clear();
            },
            |r| r.leaves.clear(),
            // A stack stop in the definition's load puts the case outside the determinism
            // contract.
            |r| {
                r.load_records.push(LoadRecord {
                    kind: crate::exec::LOAD_STACK_STOP.to_owned(),
                    detail: "load".to_owned(),
                });
            },
        ];
        for (index, edit) in cases.into_iter().enumerate() {
            let mut baseline = coin_baseline();
            edit(&mut baseline);
            assert!(complete_ends(&baseline).is_none(), "case {index}");
        }
    }

    #[test]
    fn a_contradicted_claim_of_the_load_does_not_make_a_side_incomplete() {
        let mut baseline = coin_baseline();
        baseline.load_records.push(LoadRecord {
            kind: "contradicted-claim".to_owned(),
            detail: "td(0)".to_owned(),
        });
        assert!(complete_ends(&baseline).is_some());
    }

    #[test]
    fn incomplete_baseline_is_baseline_incomplete_whatever_the_mutant() {
        let baseline = result(vec![
            natural(config(3, 0), None),
            leaf(
                HaltReasonOutput::DepthBound,
                config(4, 0),
                vec![UncleanReason::Halt],
            ),
        ]);
        // The mutant's end 5 would kill against a complete set {3, 4}.
        let mutant = result(vec![natural(config(5, 0), Some(true))]);
        for paths in BOTH_MODES {
            assert_eq!(
                judge(&baseline, &mutant, paths),
                DifferentialJudgement::class(OutcomeClass::BaselineIncomplete)
            );
        }
    }

    // ---- conditions 2, 4, 5 per mutant leaf

    #[test]
    fn a_mutant_end_outside_the_set_kills() {
        let mutant = result(vec![natural(config(5, 0), Some(true))]);
        assert_eq!(
            added(&coin_baseline(), &mutant),
            Verdicts {
                kills: vec![true],
                undecided: false,
            }
        );
    }

    #[test]
    fn a_mutant_end_inside_the_set_does_not_kill() {
        // A mutant whose single path differs from the baseline's but stays in its set.
        for out in [3, 4] {
            let mutant = result(vec![natural(config(out, 0), Some(true))]);
            assert_eq!(
                added(&coin_baseline(), &mutant),
                Verdicts {
                    kills: vec![false],
                    undecided: false,
                }
            );
        }
    }

    #[test]
    fn a_difference_only_in_the_generated_counter_kills() {
        let mutant = result(vec![natural(config(3, 1), Some(true))]);
        assert_eq!(added(&coin_baseline(), &mutant).kills, vec![true]);
    }

    #[test]
    fn an_abnormal_stop_or_undefined_step_outside_the_set_does_not_kill() {
        let mutant = result(vec![
            leaf(HaltReasonOutput::Stuck, config(5, 0), Vec::new()),
            leaf(
                HaltReasonOutput::Trivial,
                config(6, 0),
                vec![UncleanReason::Halt],
            ),
            leaf(
                HaltReasonOutput::DepthBound,
                config(7, 0),
                vec![UncleanReason::Halt],
            ),
        ]);
        assert_eq!(
            added(&coin_baseline(), &mutant),
            Verdicts {
                kills: vec![false, false, false],
                undecided: false,
            }
        );
    }

    #[test]
    fn a_natural_end_that_is_not_constructor_only_is_undecided() {
        let mutant = result(vec![natural(config(5, 0), Some(false))]);
        assert_eq!(
            added(&coin_baseline(), &mutant),
            Verdicts {
                kills: vec![false],
                undecided: true,
            }
        );
    }

    #[test]
    fn an_unclean_stuck_leaf_outside_the_set_is_undecided() {
        let mutant = result(vec![leaf(
            HaltReasonOutput::Stuck,
            config(5, 0),
            vec![UncleanReason::SmtUnknowns],
        )]);
        assert_eq!(
            added(&coin_baseline(), &mutant),
            Verdicts {
                kills: vec![false],
                undecided: true,
            }
        );
    }

    #[test]
    fn a_missing_constructor_only_judgement_is_an_engine_defect() {
        let mutant = result(vec![natural(config(5, 0), None)]);
        let baseline = coin_baseline();
        let ends = complete_ends(&baseline).expect("complete");
        assert!(Verdicts::added(&ends, &mutant).is_err());
        // Inside the set the judgement is not read.
        let agreeing = result(vec![natural(config(3, 0), None)]);
        assert!(Verdicts::added(&ends, &agreeing).is_ok());
    }

    // ---- classes

    #[test]
    fn a_kill_is_a_hit_on_its_leaf() {
        let mutant = result(vec![
            natural(config(3, 0), Some(true)),
            natural(config(5, 0), Some(true)),
        ]);
        // In the all-paths mode the mutant also lacks the baseline's end 4.
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::OnePath),
            hit(Some(1), None)
        );
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::AllPaths),
            hit(Some(1), Some(1))
        );
    }

    #[test]
    fn agreeing_natural_ends_are_a_miss() {
        let mutant = result(vec![
            natural(config(3, 0), Some(true)),
            natural(config(4, 0), Some(true)),
        ]);
        for paths in BOTH_MODES {
            assert_eq!(
                judge(&coin_baseline(), &mutant, paths),
                DifferentialJudgement::class(OutcomeClass::Miss)
            );
        }
    }

    #[test]
    fn a_kill_beside_a_chosen_value_mark_is_unsupported() {
        let mutant = result(vec![
            natural(config(5, 0), Some(true)),
            leaf(
                HaltReasonOutput::Stuck,
                config(3, 0),
                vec![UncleanReason::ImplementationChosenValue],
            ),
        ]);
        for paths in BOTH_MODES {
            assert_eq!(
                judge(&coin_baseline(), &mutant, paths),
                DifferentialJudgement::class(OutcomeClass::Unsupported)
            );
        }
    }

    #[test]
    fn an_undecided_end_without_a_kill_is_unsupported() {
        let mutant = result(vec![natural(config(5, 0), Some(false))]);
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::OnePath),
            DifferentialJudgement::class(OutcomeClass::Unsupported)
        );
    }

    #[test]
    fn a_kill_beside_an_undecided_end_is_still_a_hit() {
        let mutant = result(vec![
            natural(config(6, 0), Some(false)),
            natural(config(5, 0), Some(true)),
        ]);
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::OnePath),
            hit(Some(1), None)
        );
    }

    #[test]
    fn a_bounded_mutant_without_a_kill_keeps_its_class() {
        let mutant = result(vec![leaf(
            HaltReasonOutput::DepthBound,
            config(5, 0),
            vec![UncleanReason::Halt],
        )]);
        for paths in BOTH_MODES {
            assert_eq!(
                judge(&coin_baseline(), &mutant, paths).class,
                OutcomeClass::DepthBound
            );
        }
    }

    // ---- removed ends (all-paths mode)

    #[test]
    fn a_removed_end_is_a_hit_on_all_paths_only() {
        // The mutant reaches 4 only: it adds nothing and removes 3.
        let mutant = result(vec![natural(config(4, 0), Some(true))]);
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::AllPaths),
            hit(None, Some(0))
        );
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::OnePath),
            DifferentialJudgement::class(OutcomeClass::Miss)
        );
    }

    #[test]
    fn an_incomplete_mutant_removes_no_end() {
        let mutant = result(vec![
            natural(config(4, 0), Some(true)),
            leaf(
                HaltReasonOutput::DepthBound,
                config(4, 0),
                vec![UncleanReason::Halt],
            ),
        ]);
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::AllPaths).class,
            OutcomeClass::DepthBound
        );
    }

    #[test]
    fn a_removed_end_that_is_not_constructor_only_is_unsupported() {
        let baseline = result(vec![
            natural(config(3, 0), Some(false)),
            natural(config(4, 0), Some(true)),
        ]);
        let mutant = result(vec![natural(config(4, 0), Some(true))]);
        assert_eq!(
            judge(&baseline, &mutant, PathMode::AllPaths),
            DifferentialJudgement::class(OutcomeClass::Unsupported)
        );
    }

    #[test]
    fn a_removed_end_beside_a_mutant_end_that_is_not_data_is_unsupported() {
        // The mutant's end 4 is not constructor-only (say an unevaluated total function that
        // happens to print apart from 3 and 4): it may denote 3, so 3 is not shown removed.
        let mutant = result(vec![
            natural(config(4, 0), Some(true)),
            natural(config(6, 0), Some(false)),
        ]);
        assert_eq!(
            judge(&coin_baseline(), &mutant, PathMode::AllPaths),
            DifferentialJudgement::class(OutcomeClass::Unsupported)
        );
    }

    #[test]
    fn a_removed_abnormal_stop_or_undefined_step_is_no_hit() {
        let baseline = result(vec![
            leaf(HaltReasonOutput::Stuck, config(3, 0), Vec::new()),
            leaf(
                HaltReasonOutput::Trivial,
                config(5, 0),
                vec![UncleanReason::Halt],
            ),
            natural(config(4, 0), Some(true)),
        ]);
        let mutant = result(vec![natural(config(4, 0), Some(true))]);
        assert_eq!(
            judge(&baseline, &mutant, PathMode::AllPaths),
            DifferentialJudgement::class(OutcomeClass::Miss)
        );
    }

    #[test]
    fn a_removed_end_without_a_constructor_only_judgement_is_an_engine_defect() {
        let baseline = result(vec![
            natural(config(3, 0), None),
            natural(config(4, 0), None),
        ]);
        let mutant = result(vec![natural(config(4, 0), Some(true))]);
        assert!(judge_pair(&baseline, &mutant, PathMode::AllPaths, false).is_err());
        // The one-path mode never reads it.
        assert!(judge_pair(&baseline, &mutant, PathMode::OnePath, false).is_ok());
    }
}

/// FZ-FIX's fixture module (`tests/support`), included in the unit tests because the judge is
/// crate-private.
#[cfg(test)]
#[path = "../../tests/support/mod.rs"]
mod support;

/// The differential judge on FZ-FIX's baselines and mutants (`tests/data/README.md`), each side
/// run through its own executor as a campaign case runs it.
#[cfg(test)]
mod fixture_tests {
    use super::{
        support::{self, Compiled, Fixture},
        *,
    };
    use crate::{
        assemble::ProgramAssembly,
        exec::{CaseRequestShape, Executor},
    };

    /// One side of a differential case: its definition's executor and request shape.
    struct Side {
        compiled: &'static Compiled,
        executor: Executor,
        shape: CaseRequestShape,
    }

    impl Side {
        fn new(fixture: &'static Fixture, needs: &TargetNeeds, options: &CaseOptions) -> Self {
            let compiled = fixture.compiled();
            let definition = compiled.definition();
            let assembly = ProgramAssembly::new(&definition).expect("the fixture assembles");
            let executor =
                Executor::new(&definition, &assembly, options).expect("the executor builds");
            Self {
                compiled,
                executor,
                shape: CaseRequestShape::new(options, needs),
            }
        }

        /// Run the program `text`, named `file`, on this side.
        fn run(&mut self, file: &str, text: &str) -> CaseResult {
            let initial = self
                .compiled
                .assemble(file, text, &[])
                .expect("the program assembles");
            self.executor
                .run(&initial, &self.shape, &[], None)
                .expect("no solver prelude failure")
        }
    }

    /// Judge `text` on `baseline` and `mutant` under `options`, each side planned by [`plan`].
    fn judge_on(
        baseline: &'static Fixture,
        mutant: &'static Fixture,
        file: &str,
        text: &str,
        options: &CaseOptions,
    ) -> DifferentialJudgement {
        let plan = plan(options);
        let baseline = Side::new(baseline, &plan.baseline, options).run(file, text);
        let mutant = Side::new(mutant, &plan.mutant, options).run(file, text);
        judge_pair(&baseline, &mutant, options.paths, false).expect("no engine defect")
    }

    fn options(paths: PathMode) -> CaseOptions {
        CaseOptions {
            paths,
            ..CaseOptions::default()
        }
    }

    /// `flip(n)` on the COIN baseline and `mutant`.
    fn flip(mutant: &'static Fixture, n: i64, paths: PathMode) -> DifferentialJudgement {
        judge_on(
            &support::COIN,
            mutant,
            "coin/flip.pgm",
            &format!("flip({n})"),
            &options(paths),
        )
    }

    const BOTH_MODES: [PathMode; 2] = [PathMode::OnePath, PathMode::AllPaths];
    const MISS: DifferentialJudgement = DifferentialJudgement::class(OutcomeClass::Miss);

    #[test]
    fn single_paths_that_differ_inside_the_baseline_set_are_no_hit() {
        // The swapped mutant's one path ends elsewhere than the baseline's one path, ...
        let options = options(PathMode::OnePath);
        let one_path = TargetNeeds {
            paths: Some(PathMode::OnePath),
            ..TargetNeeds::default()
        };
        let baseline =
            Side::new(&support::COIN, &one_path, &options).run("coin/flip.pgm", "flip(3)");
        let mutant =
            Side::new(&support::COIN_SWAPPED, &one_path, &options).run("coin/flip.pgm", "flip(3)");
        assert_eq!(baseline.leaves.len(), 1);
        assert_eq!(mutant.leaves.len(), 1);
        assert_ne!(baseline.leaves[0].state, mutant.leaves[0].state);
        // ... but inside the baseline's set of ends {3, 4}: no hit in either mode.
        for paths in BOTH_MODES {
            assert_eq!(flip(&support::COIN_SWAPPED, 3, paths), MISS, "{paths:?}");
        }
    }

    #[test]
    fn a_mutant_that_adds_an_end_is_a_hit() {
        for paths in BOTH_MODES {
            let judgement = flip(&support::COIN_KILL, 11, paths);
            assert_eq!(judgement.class, OutcomeClass::Hit, "{paths:?}");
            assert_eq!(judgement.killing_leaf, Some(0), "{paths:?}");
            // On the anchor the mutant is the baseline.
            assert_eq!(flip(&support::COIN_KILL, 3, paths), MISS, "{paths:?}");
        }
        // On all paths the mutant's single end 13 also lacks both baseline ends 11 and 12.
        assert!(
            flip(&support::COIN_KILL, 11, PathMode::AllPaths)
                .removed_end
                .is_some()
        );
    }

    #[test]
    fn a_mutant_that_removes_an_end_is_a_hit_on_all_paths_only() {
        assert_eq!(flip(&support::COIN_PRIO, 3, PathMode::OnePath), MISS);
        let judgement = flip(&support::COIN_PRIO, 3, PathMode::AllPaths);
        assert_eq!(judgement.class, OutcomeClass::Hit);
        assert_eq!(judgement.killing_leaf, None);
        assert!(judgement.removed_end.is_some());
    }

    #[test]
    fn an_added_end_holding_a_function_application_is_no_hit() {
        // flip(11) ends with opaque(11) on the mutant: clean, ceil-free, not data.
        for paths in BOTH_MODES {
            assert_eq!(
                flip(&support::COIN_FUNC, 11, paths),
                DifferentialJudgement::class(OutcomeClass::Unsupported),
                "{paths:?}"
            );
            assert_eq!(flip(&support::COIN_FUNC, 3, paths), MISS, "{paths:?}");
        }
    }

    #[test]
    fn a_depth_bound_below_the_run_makes_the_baseline_incomplete() {
        // count(3) ends only under max_depth 5; the mutant does the same as the baseline.
        let count = |max_depth| {
            judge_on(
                &support::COIN,
                &support::COIN_KILL,
                "coin/count.pgm",
                "count(3)",
                &CaseOptions {
                    max_depth: Some(max_depth),
                    ..CaseOptions::default()
                },
            )
        };
        for max_depth in [3, 4] {
            assert_eq!(
                count(max_depth),
                DifferentialJudgement::class(OutcomeClass::BaselineIncomplete),
                "max_depth {max_depth}"
            );
        }
        assert_eq!(count(5), MISS);
    }

    #[test]
    fn a_chosen_value_mark_refuses_the_kill_and_its_absence_allows_it() {
        // listKeys(1, 2): both sides read keys_list of a two-key map and carry the mark, and the
        // ends differ; the marked baseline end makes its set incomplete.
        for paths in BOTH_MODES {
            let program = support::CHOSEN.program("chosen/keys.pgm");
            assert_eq!(
                judge_on(
                    &support::CHOSEN,
                    &support::CHOSEN_KILL,
                    program.file,
                    program.text,
                    &options(paths)
                ),
                DifferentialJudgement::class(OutcomeClass::BaselineIncomplete),
                "{paths:?}"
            );
            // listKeys(1, 1): one key, no mark; the mutant ends with [1, 1], the baseline [1].
            let judgement = judge_on(
                &support::CHOSEN,
                &support::CHOSEN_KILL,
                program.file,
                "listKeys(1, 1)",
                &options(paths),
            );
            assert_eq!(judgement.class, OutcomeClass::Hit, "{paths:?}");
            assert_eq!(judgement.killing_leaf, Some(0), "{paths:?}");
        }
    }

    #[test]
    fn equal_digests_and_orders_are_equivalent() {
        let coin = support::COIN.compiled();
        let layout = support::COIN_LAYOUT.compiled();
        assert_eq!(coin.digest(), layout.digest());
        assert!(equivalent(&coin.definition(), &layout.definition()).expect("digests"));
        assert!(
            equivalent(
                &coin.definition_on(BackendRoute::FromDefinition),
                &layout.definition_on(BackendRoute::FromDefinition),
            )
            .expect("digests")
        );
    }

    #[test]
    fn unequal_digests_are_not_equivalent() {
        let coin = support::COIN.compiled().definition();
        for mutant in [
            &support::COIN_SWAPPED,
            &support::COIN_PRIO,
            &support::COIN_KILL,
            &support::COIN_FUNC,
        ] {
            assert!(
                !equivalent(&coin, &mutant.compiled().definition()).expect("digests"),
                "{}",
                mutant.file
            );
        }
    }

    #[test]
    fn equal_digests_with_another_rewrite_order_route_or_module_are_not_equivalent() {
        // FZ-FIX has no source pair with one digest and two orders (compiled KORE keeps the
        // sentence order), so the pair is the baseline and itself with a permuted order.
        let coin = support::COIN.compiled();
        let mut order = coin.artifacts.execution_rewrite_order.clone();
        assert!(order.len() >= 2, "COIN orders several rules: {order:?}");
        order.reverse();
        let permuted = coin.definition_on(BackendRoute::SourceExecution {
            execution_rewrite_order: order,
        });
        assert!(!equivalent(&coin.definition(), &permuted).expect("digests"));
        let kore_route = coin.definition_on(BackendRoute::FromDefinition);
        assert!(!equivalent(&coin.definition(), &kore_route).expect("digests"));
        assert!(!equivalent(&kore_route, &coin.definition()).expect("digests"));
        let mut other_main = coin.definition();
        other_main.main_module = "COIN-SYNTAX".to_owned();
        assert!(!equivalent(&coin.definition(), &other_main).expect("digests"));
    }
}
