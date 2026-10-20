//! The differential target: does the mutant reach a clean end that the baseline cannot reach on
//! the same input (ARCHITECTURE 4.3)? Owner: FZ-08.
//!
//! A case runs the baseline on all paths and the mutant on the campaign's path mode, each on its
//! own backend, with hole values generated from the baseline's signature and internalized per
//! side. [`judge_pair`] then decides the case from the two [`CaseResult`]s alone.
//!
//! # Why the hit rule is sound
//!
//! A hit claims that the mutant reaches, on this input, a final configuration that the baseline
//! does not reach on any path. The baseline's set of final configurations is known only when its
//! all-paths run is complete: every leaf is a decided, clean end (`stuck`, or an undefined step,
//! whose configuration is the one before the step). A bound, a stop, an undecided or unsupported
//! leaf leaves paths unexplored, and an end outside a partial set proves nothing; such a case is
//! `baseline-incomplete`, never a miss. The mutant's configuration must be a clean natural end
//! (the program finished on the mutant) whose internalized term is built from free constructors,
//! injections, domain values and well-formed collections only, so that it denotes itself and
//! syntactic inequality is inequality of values. An implementation-chosen value on either side
//! would make the comparison depend on a choice k-rust made, not on the definitions.
//!
//! # Comparison
//!
//! The baseline's ends are held as a set of KORE patterns ordered by [`KorePattern`]'s `Ord`,
//! whose equality is structural, so two patterns are equal exactly when their printed KORE is
//! equal. Leaves are compared after k-rust's normalization, under which map and set entries are
//! already ordered.
//!
//! The whole configuration is compared, the `<generatedCounter>` cell included: a mutant end that
//! differs from every baseline end only in that cell is a kill. The compiled definition's
//! `<generatedCounter>` cell and its `freshGenerator` rules are part of each definition's
//! rewrite theory and fix the fresh constants a run mints, so the counter is a component of the
//! final configuration like any other cell. kink's whole-term oracle compares the same complete
//! terms, so the two agree on this point.
//!
//! The default mode runs the mutant on one path and finds ends the mutant adds; it never finds
//! ends the mutant removes.

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
    /// The baseline runs all paths, so that its set of ends can be complete.
    pub(crate) baseline: TargetNeeds,
    /// The mutant runs on the campaign's path mode and reports
    /// [`crate::exec::LeafReport::constructor_only`].
    pub(crate) mutant: TargetNeeds,
}

/// The judgement of one baseline/mutant pair.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DifferentialJudgement {
    /// The case's class: `baseline-incomplete` when the baseline's ends are incomplete,
    /// otherwise the mutant's class with "reaches the target" meaning "kills".
    pub(crate) class: OutcomeClass,
    /// For a hit, the index of the mutant leaf whose configuration the baseline cannot reach.
    pub(crate) killing_leaf: Option<usize>,
}

/// The needs of each side for `options`: the baseline on all paths, whatever the campaign's
/// path mode; the mutant on the campaign's path mode, with the constructor-only judgement of
/// condition 4. Neither side needs traces or terminal rules: the differential target names no
/// rule.
pub(crate) fn plan(options: &CaseOptions) -> DifferentialPlan {
    DifferentialPlan {
        baseline: TargetNeeds {
            paths: Some(PathMode::AllPaths),
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

/// Judge one pair (ARCHITECTURE 4.3). A case is a hit if and only if:
/// 1. the baseline run with all paths is complete: every leaf is a clean `stuck` or `undefined`
///    end, with no bound, stop, timeout, unknown or unsupported leaf;
/// 2. the mutant leaf is a clean natural end;
/// 3. neither side carries an implementation-chosen value mark;
/// 4. the mutant leaf's internalized configuration is constructor-only (internal term kinds,
///    not KORE symbols);
/// 5. that configuration is not in the baseline's set of final configurations, compared as
///    printed KORE after k-rust's normalization.
///
/// An incomplete baseline makes the case `baseline-incomplete`, whatever the mutant did.
/// Otherwise the mutant's leaves are classed by [`exec::classify`], a leaf "reaching the target"
/// when conditions 2, 4 and 5 hold for it. Two outcomes are neither a hit nor a pass, and are
/// `unsupported`, as a target-reaching leaf that is not clean is (ARCHITECTURE 5.3):
/// - a kill exists, but some mutant leaf carries an implementation-chosen value mark
///   (condition 3 is a fact of the whole result);
/// - no kill exists, but some mutant end outside the baseline's set could not be judged: a clean
///   natural end that is not constructor-only, or a `stuck` leaf that is not clean.
///
/// # Errors
///
/// [`EngineDefect`] from classification, or when a clean natural end of the mutant outside the
/// baseline's set carries no constructor-only judgement although [`plan`] asked for it.
pub(crate) fn judge_pair(
    baseline: &CaseResult,
    mutant: &CaseResult,
    run_to_completion: bool,
) -> Result<DifferentialJudgement, EngineDefect> {
    let Some(ends) = baseline_ends(baseline) else {
        return Ok(DifferentialJudgement {
            class: OutcomeClass::BaselineIncomplete,
            killing_leaf: None,
        });
    };
    let verdicts = Verdicts::of(&ends, mutant)?;
    let killing_leaf = verdicts.kills.iter().position(|&kills| kills);
    let class = exec::classify(mutant, &verdicts.kills, run_to_completion)?;
    let unsupported = DifferentialJudgement {
        class: OutcomeClass::Unsupported,
        killing_leaf: None,
    };
    if killing_leaf.is_some() && verdicts.chosen_value {
        return Ok(unsupported);
    }
    match class {
        OutcomeClass::Hit => match killing_leaf {
            Some(index) => Ok(DifferentialJudgement {
                class,
                killing_leaf: Some(index),
            }),
            None => Err(EngineDefect {
                case: None,
                description: "classification reported a differential hit without a killing leaf"
                    .to_owned(),
            }),
        },
        _ if verdicts.undecided => Ok(unsupported),
        _ => Ok(DifferentialJudgement {
            class,
            killing_leaf: None,
        }),
    }
}

/// The baseline's set of final configurations when its all-paths run is complete (condition 1,
/// with condition 3 for the baseline: a marked leaf is not clean), or `None`.
///
/// A complete run returned leaves, was not stopped by the safety limit, counted no stack stop,
/// SMT unknown or run allowance refusal, and every leaf is a clean `stuck` leaf or an undefined
/// step (`trivial`) whose only unclean reason is its halt: a decided, ceil-free configuration
/// with no diagnostic, the configuration before the undefined step. Load records are facts about
/// the definition and do not make a run incomplete (T-5).
fn baseline_ends(result: &CaseResult) -> Option<BTreeSet<&KorePattern>> {
    let run_clean = result.failure.is_none()
        && !result.safety_limit_hit
        && result.stack_stops == 0
        && result.smt_unknowns == 0
        && result.run_allowance_refusals == 0
        && !result.leaves.is_empty();
    if !run_clean || !result.leaves.iter().all(complete_end) {
        return None;
    }
    Some(result.leaves.iter().map(|leaf| &leaf.state).collect())
}

/// Whether a baseline leaf is an end its set may hold (condition 1).
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

/// What the mutant's leaves show against a complete baseline's set of ends.
#[derive(Debug, Eq, PartialEq)]
struct Verdicts {
    /// `kills[i]`: leaf `i` is a clean natural end (condition 2) whose configuration is
    /// constructor-only (condition 4) and not in the baseline's set (condition 5).
    kills: Vec<bool>,
    /// Some `stuck` leaf outside the baseline's set could not be judged: it is not clean, or it
    /// is a clean natural end that is not constructor-only.
    undecided: bool,
    /// Some mutant leaf carries an implementation-chosen value mark (condition 3).
    chosen_value: bool,
}

impl Verdicts {
    fn of(ends: &BTreeSet<&KorePattern>, mutant: &CaseResult) -> Result<Self, EngineDefect> {
        let mut kills = vec![false; mutant.leaves.len()];
        let mut undecided = false;
        for (index, leaf) in mutant.leaves.iter().enumerate() {
            // Only a stuck leaf is a final configuration of the mutant; an undefined step, a
            // bound or a stop is classed by `exec::classify`.
            if leaf.halt != HaltReasonOutput::Stuck || ends.contains(&leaf.state) {
                continue;
            }
            if !leaf.is_clean() {
                undecided = true;
            } else if leaf.natural_end {
                match leaf.constructor_only {
                    Some(true) => kills[index] = true,
                    Some(false) => undecided = true,
                    None => {
                        return Err(EngineDefect {
                            case: None,
                            description: format!(
                                "mutant leaf {index} is a natural end without the \
                                 constructor-only judgement the differential plan requests"
                            ),
                        });
                    }
                }
            }
            // A clean stuck leaf that is not a natural end is an abnormal stop: the program did
            // not finish on the mutant, so its configuration is no kill (condition 2).
        }
        let chosen_value = mutant.leaves.iter().any(|leaf| {
            leaf.unclean
                .contains(&UncleanReason::ImplementationChosenValue)
        });
        Ok(Self {
            kills,
            undecided,
            chosen_value,
        })
    }
}

#[cfg(test)]
mod tests {
    use k_rust::kore::parser::parse_pattern;

    use super::*;

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

    /// A complete baseline with the two ends 3 and 4 (the COIN baseline on `flip(3)`).
    fn coin_baseline() -> CaseResult {
        result(vec![
            natural(config(3, 0), None),
            natural(config(4, 0), None),
        ])
    }

    fn judge(baseline: &CaseResult, mutant: &CaseResult) -> DifferentialJudgement {
        judge_pair(baseline, mutant, false).expect("no engine defect")
    }

    fn verdicts(baseline: &CaseResult, mutant: &CaseResult) -> Verdicts {
        let ends = baseline_ends(baseline).expect("the baseline is complete");
        Verdicts::of(&ends, mutant).expect("no engine defect")
    }

    // ---- plan

    #[test]
    fn baseline_runs_all_paths_and_mutant_the_campaign_mode() {
        for paths in [PathMode::OnePath, PathMode::AllPaths] {
            let plan = plan(&CaseOptions {
                paths,
                ..CaseOptions::default()
            });
            assert_eq!(plan.baseline.paths, Some(PathMode::AllPaths));
            assert!(!plan.baseline.constructor_only);
            assert_eq!(plan.mutant.paths, Some(paths));
            assert!(plan.mutant.constructor_only);
            for needs in [&plan.baseline, &plan.mutant] {
                assert!(!needs.trace);
                assert!(needs.terminal_rules.is_empty());
            }
        }
    }

    // ---- condition 1: baseline completeness

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
        let ends = baseline_ends(&baseline).expect("complete");
        assert_eq!(ends.len(), 3);
        assert!(ends.contains(&undefined));
    }

    #[test]
    fn every_unclean_or_unfinished_baseline_leaf_makes_it_incomplete() {
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
            assert!(baseline_ends(&baseline).is_none(), "{halt:?}");
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
                assert!(baseline_ends(&baseline).is_none(), "{halt:?} {reason:?}");
            }
        }
    }

    #[test]
    fn run_level_facts_make_the_baseline_incomplete() {
        let cases: [fn(&mut CaseResult); 6] = [
            |r| r.stack_stops = 1,
            |r| r.smt_unknowns = 1,
            |r| r.run_allowance_refusals = 1,
            |r| r.safety_limit_hit = true,
            |r| {
                r.failure = Some("err".to_owned());
                r.leaves.clear();
            },
            |r| r.leaves.clear(),
        ];
        for (index, edit) in cases.into_iter().enumerate() {
            let mut baseline = coin_baseline();
            edit(&mut baseline);
            assert!(baseline_ends(&baseline).is_none(), "case {index}");
        }
    }

    #[test]
    fn load_records_do_not_make_the_baseline_incomplete() {
        let mut baseline = coin_baseline();
        baseline.load_records.push(crate::report::LoadRecord {
            kind: "contradicted-claim".to_owned(),
            detail: "td(0)".to_owned(),
        });
        assert!(baseline_ends(&baseline).is_some());
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
        assert_eq!(
            judge(&baseline, &mutant),
            DifferentialJudgement {
                class: OutcomeClass::BaselineIncomplete,
                killing_leaf: None,
            }
        );
    }

    // ---- conditions 2, 4, 5 per mutant leaf

    #[test]
    fn a_mutant_end_outside_the_set_kills() {
        let mutant = result(vec![natural(config(5, 0), Some(true))]);
        assert_eq!(
            verdicts(&coin_baseline(), &mutant),
            Verdicts {
                kills: vec![true],
                undecided: false,
                chosen_value: false,
            }
        );
    }

    #[test]
    fn a_mutant_end_inside_the_set_does_not_kill() {
        // A mutant whose single path differs from the baseline's but stays in its set.
        for out in [3, 4] {
            let mutant = result(vec![natural(config(out, 0), Some(true))]);
            assert_eq!(
                verdicts(&coin_baseline(), &mutant),
                Verdicts {
                    kills: vec![false],
                    undecided: false,
                    chosen_value: false,
                }
            );
        }
    }

    #[test]
    fn a_difference_only_in_the_generated_counter_kills() {
        let mutant = result(vec![natural(config(3, 1), Some(true))]);
        assert_eq!(verdicts(&coin_baseline(), &mutant).kills, vec![true]);
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
            verdicts(&coin_baseline(), &mutant),
            Verdicts {
                kills: vec![false, false, false],
                undecided: false,
                chosen_value: false,
            }
        );
    }

    #[test]
    fn a_natural_end_that_is_not_constructor_only_is_undecided() {
        let mutant = result(vec![natural(config(5, 0), Some(false))]);
        assert_eq!(
            verdicts(&coin_baseline(), &mutant),
            Verdicts {
                kills: vec![false],
                undecided: true,
                chosen_value: false,
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
            verdicts(&coin_baseline(), &mutant),
            Verdicts {
                kills: vec![false],
                undecided: true,
                chosen_value: false,
            }
        );
    }

    #[test]
    fn a_missing_constructor_only_judgement_is_an_engine_defect() {
        let mutant = result(vec![natural(config(5, 0), None)]);
        let baseline = coin_baseline();
        let ends = baseline_ends(&baseline).expect("complete");
        assert!(Verdicts::of(&ends, &mutant).is_err());
        // Inside the set the judgement is not read.
        let agreeing = result(vec![natural(config(3, 0), None)]);
        assert!(Verdicts::of(&ends, &agreeing).is_ok());
    }

    // ---- condition 3

    #[test]
    fn a_chosen_value_mark_on_any_mutant_leaf_is_recorded() {
        let mutant = result(vec![
            natural(config(5, 0), Some(true)),
            leaf(
                HaltReasonOutput::Stuck,
                config(3, 0),
                vec![UncleanReason::ImplementationChosenValue],
            ),
        ]);
        assert_eq!(
            verdicts(&coin_baseline(), &mutant),
            Verdicts {
                kills: vec![true, false],
                undecided: false,
                chosen_value: true,
            }
        );
    }

    // ---- classes (through `exec::classify`)

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
        assert_eq!(
            judge(&coin_baseline(), &mutant),
            DifferentialJudgement {
                class: OutcomeClass::Unsupported,
                killing_leaf: None,
            }
        );
    }

    #[test]
    fn a_kill_is_a_hit_on_its_leaf() {
        let mutant = result(vec![
            natural(config(3, 0), Some(true)),
            natural(config(5, 0), Some(true)),
        ]);
        assert_eq!(
            judge(&coin_baseline(), &mutant),
            DifferentialJudgement {
                class: OutcomeClass::Hit,
                killing_leaf: Some(1),
            }
        );
    }

    #[test]
    fn agreeing_natural_ends_are_a_miss() {
        let mutant = result(vec![natural(config(4, 0), Some(true))]);
        assert_eq!(
            judge(&coin_baseline(), &mutant),
            DifferentialJudgement {
                class: OutcomeClass::Miss,
                killing_leaf: None,
            }
        );
    }

    #[test]
    fn an_undecided_end_without_a_kill_is_unsupported() {
        let mutant = result(vec![natural(config(5, 0), Some(false))]);
        assert_eq!(
            judge(&coin_baseline(), &mutant),
            DifferentialJudgement {
                class: OutcomeClass::Unsupported,
                killing_leaf: None,
            }
        );
    }

    #[test]
    fn a_kill_beside_an_undecided_end_is_still_a_hit() {
        let mutant = result(vec![
            natural(config(6, 0), Some(false)),
            natural(config(5, 0), Some(true)),
        ]);
        assert_eq!(
            judge(&coin_baseline(), &mutant),
            DifferentialJudgement {
                class: OutcomeClass::Hit,
                killing_leaf: Some(1),
            }
        );
    }

    #[test]
    fn a_bounded_mutant_without_a_kill_keeps_its_class() {
        let mutant = result(vec![leaf(
            HaltReasonOutput::DepthBound,
            config(5, 0),
            vec![UncleanReason::Halt],
        )]);
        assert_eq!(
            judge(&coin_baseline(), &mutant).class,
            OutcomeClass::DepthBound
        );
    }
}
