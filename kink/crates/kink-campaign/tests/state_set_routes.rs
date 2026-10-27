//! Re-pin L1-1-fix-1 (L1-1 review 1, minors 1-3): the three routes by which a state-set result run
//! kills a mutant where the path set of the same request refuses the baseline. Each test pins
//! today's verdict under both `RunOptions::result_modality` values.
//!
//! Every route is a real difference between the two runs' sets of final configurations. Each
//! rests on re-pin decision 3 only (ANALYSIS.md section 4; the orchestrator's judgement in the
//! decisions log, 2026-10-17, "L1-1 StateSet moves on IMP"; Sebastien can override): k-rust's
//! state-set merge is correct, so a complete state set is the set of reachable final
//! configurations of the definition. None of them is a guess about values the definition leaves
//! open.
//!
//! - Crash multiplicity: the campaign runner's single-crash rule (`state_side`) makes a crash side
//!   only from exactly one terminal leaf. Two paths to one crash configuration are one leaf in a
//!   state set and two in a path set, so the state set gives a crash side where the path set gives
//!   `Unknown`.
//! - An undefined step on a merged state (before fz26 KINK-PATHSET-FALLBACK, mixed modality: kink
//!   replaced a state set with an undefined step by its path set, per side). Two paths to one
//!   undefined step are one `Trivial` leaf in a state set, so with the single-crash rule a crash
//!   side is compared with a single undefined-step side, where both path sets refuse.
//! - Absorbed depth bound: in a state set an earlier stuck leaf stands for a later depth-bound
//!   leaf of the same configuration (k-rust `docs/backend-port.md`, "Final search depth cuts"),
//!   which then leaves no leaf, so kink reads the state set as complete where the path set of the
//!   same bounds is incomplete.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::path::Path;
use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kore::{ast::Pattern, walk};
use kink_campaign::{
    Campaign, CampaignFailureKind, CampaignOptions, CampaignRun, CrashPolicy, FinalResult,
    MutantStatus, OracleDeclaration, OracleOutcome, OracleSide, OracleValue, Projection,
    RunOptions, ScheduleMode, SelectionPolicy as Sel, SideRun, StateProjection, TestCase, TestRun,
    run_campaign_with,
};
use kink_native::NativeValidator;
use kink_native::execution::{
    ExecutionAdapter, ExecutionBudget, HaltClass, ResultModality, ResultRun, SolverProfile,
};
use kink_patch::{
    Baseline, CandidateGeneration, Edit, Patch, SelectionPolicy, SiteSelector, TermRef,
    derive_sites, select,
};
use kink_pattern::ExecutionTerminalKind;

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(20),
    max_simplification_iterations: 10_000,
    max_depth: None,
    max_breadth: None,
};

const MODALITIES: [ResultModality; 2] = [ResultModality::PathSet, ResultModality::StateSet];

/// The argument of the first application of `symbol` in `term`, as its domain-value text.
fn argument_of(term: &Pattern, symbol: &str) -> Option<String> {
    if let Pattern::Application {
        symbol: head,
        arguments,
    } = term
        && head.name == symbol
    {
        return match arguments.as_slice() {
            [Pattern::DomainValue { value, .. }] => value.as_utf8().ok().map(str::to_owned),
            _ => None,
        };
    }
    walk::children(term)
        .into_iter()
        .find_map(|child| argument_of(child, symbol))
}

/// conv.k's classifier: a configuration holding `crash(_)` is a semantic crash.
fn crash_is_a_crash(term: &Pattern) -> ExecutionTerminalKind {
    if argument_of(term, "Lblcrash").is_some() {
        ExecutionTerminalKind::SemanticCrash
    } else {
        ExecutionTerminalKind::Normal
    }
}

fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}

fn validator(name: &str, module: &str) -> NativeValidator {
    NativeValidator::bind(
        support::load_path(
            &Path::new(support::DIR).join(format!("l1/{name}.k")),
            module,
        ),
        CompileOptions::default(),
    )
}

fn test(id: &str, symbol: &str, argument: i64, policy: CrashPolicy) -> Vec<TestCase> {
    vec![TestCase {
        id: id.into(),
        initial_state: support::initial_state(
            support::app(symbol, vec![support::int(argument)]),
            "SortProg",
        ),
        oracles: vec![
            OracleDeclaration::new(policy, Projection::State(StateProjection::WholeTerm)).unwrap(),
        ],
    }]
}

/// The one-candidate generation whose patch replaces the only Int token `from` of `rule` by `to`.
fn replace<'b>(
    baseline: &'b Baseline,
    rule: &str,
    from: &str,
    to: &str,
) -> CandidateGeneration<'b> {
    fn tokens(
        baseline: &Baseline,
        at: &kink_patch::SentenceRef,
        path: &mut Vec<u32>,
        token: &str,
    ) -> Vec<TermRef> {
        let here = TermRef::new(at.clone(), path.as_slice());
        let Some(term) = baseline.term(&here) else {
            return Vec::new();
        };
        let mut found = Vec::new();
        if matches!(term.unannotated(), Term::Token { token: t, .. } if t == token) {
            found.push(here);
        }
        for index in 0.. {
            path.push(index);
            if baseline
                .term(&TermRef::new(at.clone(), path.as_slice()))
                .is_none()
            {
                path.pop();
                break;
            }
            found.extend(tokens(baseline, at, path, token));
            path.pop();
        }
        found
    }
    let sentence = support::rule(baseline, rule);
    let [at] = (0..3)
        .flat_map(|part| tokens(baseline, &sentence, &mut vec![part], from))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap_or_else(|found: Vec<_>| panic!("{rule}: {} tokens {from}", found.len()));
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).unwrap().clone(),
        at,
        replacement: Term::Token {
            token: to.into(),
            sort: Sort::new("Int"),
        },
    }])
    .unwrap();
    let discovery = derive_sites(
        baseline,
        rule,
        &[
            SiteSelector::RuleLabel(rule.into()),
            SiteSelector::Path(vec![0]),
        ],
    )
    .unwrap();
    select(&discovery, SelectionPolicy::Each, 1)
        .unwrap()
        .fold(rule, |_| patch.clone())
        .unwrap()
}

fn run(
    campaign: &Campaign<'_>,
    generation: &CandidateGeneration<'_>,
    result_modality: ResultModality,
) -> Result<CampaignRun, CampaignFailureKind> {
    run_campaign_with(
        campaign,
        generation,
        &CampaignOptions {
            schedule: ScheduleMode::Full,
            selection: Sel::None,
            share_evidence: true,
            run: RunOptions {
                result_modality,
                ..RunOptions::default()
            },
            compile_workers: 1,
        },
    )
    .map_err(|failure| failure.kind())
}

/// The path set refuses the baseline: its declaration-scoped oracle gate sees `Unknown`.
fn assert_refused(run: &Result<CampaignRun, CampaignFailureKind>, what: &str) {
    assert_eq!(
        run.as_ref().err(),
        Some(&CampaignFailureKind::BaselineOracleFailed),
        "{what}: path set"
    );
}

/// The state set kills the one mutant through its one test's one slot.
fn assert_killed(run: &CampaignRun, test: &str, what: &str) {
    let [mutant] = run.mutants.as_slice() else {
        panic!("{what}: one mutant");
    };
    assert_eq!(mutant.report.status, MutantStatus::Killed, "{what}");
    assert_eq!(
        mutant.report.killing_test_ids,
        vec![test.to_owned()],
        "{what}"
    );
    assert_eq!(
        mutant.plan.tests[0].run,
        TestRun::Compared(vec![OracleOutcome::Distinguish]),
        "{what}"
    );
}

/// The baseline's one side.
fn baseline_side(run: &CampaignRun) -> &OracleSide {
    let SideRun::Sides { sides } = &run.baseline[0].run else {
        panic!("baseline sides: {:?}", run.baseline[0].run);
    };
    let [side] = sides.as_slice() else {
        panic!("one side: {sides:?}");
    };
    side
}

/// (Halt, depth) of every leaf of one adapter result run of `state` on `side`.
fn leaves(
    side: &kink_native::ValidatedDefinition,
    module: &str,
    state: &Pattern,
    budget: ExecutionBudget,
    run: Option<ResultRun>,
) -> (ResultModality, Vec<(HaltClass, u64)>) {
    let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .unwrap();
    let execution = match run {
        Some(run) => adapter.execute_result(&mut backend, state, budget, run),
        None => adapter.execute(&mut backend, state, budget),
    }
    .unwrap();
    (
        execution.modality(),
        execution
            .leaves()
            .iter()
            .map(|leaf| (leaf.halt, leaf.branch.depth))
            .collect(),
    )
}

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

mod kink_tier {
    use super::*;

    /// Route 1, crash multiplicity (L1-1 review 1 minor 1). conv.k's `a(3)` reaches `crash(3)` by
    /// two paths. As a path set that is two crash terminals, which `state_side` reads as `Unknown`
    /// (a crash among several terminals), so the baseline gate refuses the campaign. As a state set it
    /// is one crash terminal, a `SemanticCrash` side, and the mutant `mc: 1 -> 2` (`crash(1)`, again
    /// by two merged paths) is killed under `CompareIdentity`. Premise: decision 3 (the merged leaf is
    /// the set of the path set's final configurations, `{crash(3)}` against `{crash(1)}`).
    #[test]
    #[ignore = "kink"]
    fn route_1_the_single_crash_rule_reads_leaf_multiplicity() {
        on_a_big_stack(|| {
            let validator = validator("conv", "CONV");
            let tests = test("a3", "Lbla", 3, CrashPolicy::CompareIdentity);
            let generation = replace(validator.baseline(), "CONV.mc", "1", "2");
            let campaign = Campaign {
                validator: &validator,
                module: "CONV",
                observation: &[],
                classify: &crash_is_a_crash,
                tests: &tests,
                budget: BUDGET,
            };
            let state = &tests[0].initial_state;
            let side = validator.compile_baseline().unwrap();
            assert_eq!(
                leaves(
                    &side,
                    "CONV",
                    state,
                    BUDGET,
                    Some(ResultRun {
                        modality: ResultModality::PathSet,
                        max_work: None
                    })
                ),
                (
                    ResultModality::PathSet,
                    vec![(HaltClass::Stuck, 3), (HaltClass::Stuck, 3)]
                )
            );
            assert_eq!(
                leaves(&side, "CONV", state, BUDGET, None),
                (ResultModality::StateSet, vec![(HaltClass::Stuck, 3)])
            );
            let [path_set, state_set] =
                MODALITIES.map(|modality| run(&campaign, &generation, modality));
            assert_refused(&path_set, "crash multiplicity");
            let state_set = state_set.expect("the state set admits the baseline");
            let OracleSide::SemanticCrash(term) = baseline_side(&state_set) else {
                panic!("a crash side: {:?}", baseline_side(&state_set));
            };
            assert_eq!(argument_of(term, "Lblcrash").as_deref(), Some("3"));
            assert_killed(&state_set, "a3", "crash multiplicity");
        });
    }

    /// Route 2 (L1-1 review 1 minor 2; re-pinned by fz26 KINK-PATHSET-FALLBACK), an undefined step
    /// on a merged state. conv.k's state set is one crash terminal; convz.k (what conv.k's mutant
    /// `mc: 1 -> 0` compiles to) ends both converging paths in one undefined step at depth 2, one
    /// `Trivial` leaf of its state set (two in its path set). Within the one test of the campaign
    /// the baseline is a `SemanticCrash` side and the mutant a single undefined-step `Normal` side,
    /// and `CrashPolicy::Distinguish` kills. Both sides as path sets refuse the baseline (route 1).
    /// Before the ticket the mutant's state set was replaced by its path set, so the test compared
    /// a state set with a path set. Premise: decision 3 (the two sides' leaf sets are their sets of
    /// final configurations).
    #[test]
    #[ignore = "kink"]
    fn route_2_an_undefined_step_on_a_merged_state_is_one_leaf() {
        on_a_big_stack(|| {
            let tests = test("a3", "Lbla", 3, CrashPolicy::Distinguish);
            let state = &tests[0].initial_state;
            for (name, module, expected) in [
                (
                    "conv",
                    "CONV",
                    (ResultModality::StateSet, vec![(HaltClass::Stuck, 3)]),
                ),
                (
                    "convz",
                    "CONVZ",
                    (ResultModality::StateSet, vec![(HaltClass::Trivial, 2)]),
                ),
            ] {
                let side = validator(name, module).compile_baseline().unwrap();
                assert_eq!(
                    leaves(&side, module, state, BUDGET, None),
                    expected,
                    "{name}"
                );
            }
            let validator = validator("conv", "CONV");
            let generation = replace(validator.baseline(), "CONV.mc", "1", "0");
            let campaign = Campaign {
                validator: &validator,
                module: "CONV",
                observation: &[],
                classify: &crash_is_a_crash,
                tests: &tests,
                budget: BUDGET,
            };
            let [path_set, state_set] =
                MODALITIES.map(|modality| run(&campaign, &generation, modality));
            assert_refused(&path_set, "undefined step on a merged state");
            let state_set = state_set.expect("the state set admits the baseline");
            assert!(
                matches!(baseline_side(&state_set), OracleSide::SemanticCrash(_)),
                "{:?}",
                baseline_side(&state_set)
            );
            assert_killed(&state_set, "a3", "undefined step on a merged state");
        });
    }

    /// Route 3, absorbed depth bound (L1-1 review 1 minor 3; L1-1 listed it as "theoretically possible,
    /// not observed"). absorb.k's `s(3)` reaches `d(4)` at depth 3 and again at depth 4, where
    /// `max_depth = 4` stops the second path. The path set is `[Stuck 3, DepthBound 4]`, incomplete,
    /// so the baseline gate refuses the campaign; the state set is `[Stuck 3]`, the depth-bound leaf
    /// absorbed, so kink reads it as complete, and the mutant `start: 1 -> 2` (`d(5)`) is killed.
    /// Premise: decision 3, through k-rust's "a stuck leaf stands for any later leaf of its
    /// configuration" (the absorbed path's configuration is decided stuck by the earlier leaf), not
    /// through k-rust's coverage statement, which requires a run without depth stops.
    #[test]
    #[ignore = "kink"]
    fn route_3_a_stuck_leaf_absorbs_a_later_depth_bound_leaf() {
        on_a_big_stack(|| {
            let budget = ExecutionBudget {
                max_depth: Some(4),
                ..BUDGET
            };
            let validator = validator("absorb", "ABSORB");
            let tests = test("s3", "Lbls", 3, CrashPolicy::Reject);
            let state = &tests[0].initial_state;
            let side = validator.compile_baseline().unwrap();
            assert_eq!(
                leaves(
                    &side,
                    "ABSORB",
                    state,
                    budget,
                    Some(ResultRun {
                        modality: ResultModality::PathSet,
                        max_work: None
                    })
                ),
                (
                    ResultModality::PathSet,
                    vec![(HaltClass::Stuck, 3), (HaltClass::DepthBound, 4)]
                )
            );
            assert_eq!(
                leaves(&side, "ABSORB", state, budget, None),
                (ResultModality::StateSet, vec![(HaltClass::Stuck, 3)])
            );
            // Without the depth bound both modalities are complete and agree.
            assert_eq!(
                leaves(
                    &side,
                    "ABSORB",
                    state,
                    BUDGET,
                    Some(ResultRun {
                        modality: ResultModality::PathSet,
                        max_work: None
                    })
                ),
                (
                    ResultModality::PathSet,
                    vec![(HaltClass::Stuck, 3), (HaltClass::Stuck, 4)]
                )
            );
            let generation = replace(validator.baseline(), "ABSORB.start", "1", "2");
            let campaign = Campaign {
                validator: &validator,
                module: "ABSORB",
                observation: &[],
                classify: &normal,
                tests: &tests,
                budget,
            };
            let [path_set, state_set] =
                MODALITIES.map(|modality| run(&campaign, &generation, modality));
            assert_refused(&path_set, "absorbed depth bound");
            let state_set = state_set.expect("the state set admits the baseline");
            let OracleSide::Normal(OracleValue::FinalResult(FinalResult::WholeTerm(terms))) =
                baseline_side(&state_set)
            else {
                panic!("a whole-term side: {:?}", baseline_side(&state_set));
            };
            assert_eq!(
                terms
                    .iter()
                    .map(|term| argument_of(term, "Lbld"))
                    .collect::<Vec<_>>(),
                vec![Some("4".to_owned())]
            );
            assert_killed(&state_set, "s3", "absorbed depth bound");
        });
    }

    /// fz26 KINK-PATHSET-FALLBACK (D39), the remainder counterexample at admission
    /// (`testdata/k/stateset/remainder.k`, module REMAINDER-RECORD; kink-native
    /// `tests/exclusion.rs` pins the exclusions). The baseline run's remainder below the merged
    /// `p(X)` names the rule that produced `p(X)`: `g1` in the state set, `g1` and the
    /// `preserves-definedness` rule `g2` in the path set, and a covered candidate puts a record
    /// on the run's list. The path set's leaf rule reads a contradiction on `g2`, whose result is
    /// defined, so it keeps the baseline and fails only the test; the state set is excluded by
    /// the list alone and refuses the baseline. The move is fail-closed: the per-test granularity
    /// the path set kept rests on a contradiction nothing shows. Z3-only: without a solver there
    /// is no remainder.
    #[cfg(feature = "z3")]
    #[test]
    #[ignore = "kink"]
    fn a_refuted_remainder_below_a_merged_state_refuses_a_state_set_baseline() {
        on_a_big_stack(|| {
            use kink_campaign::ExecutionFailureKind;
            let validator = NativeValidator::bind(
                support::load_path(
                    &Path::new(support::DIR).join("stateset/remainder.k"),
                    "REMAINDER-RECORD",
                ),
                CompileOptions::default(),
            );
            let condition = k_rust::kore::parser::parse_pattern(
                r#"\equals{SortBool{}, SortGeneratedTopCell{}}(\dv{SortBool{}}("true"), Lbl'UndsEqlsSlshEqls'Int'Unds'{}(Lblh{}(VarX:SortInt{}), \dv{SortInt{}}("3")))"#,
            )
            .unwrap();
            let tests = vec![TestCase {
                id: "x".into(),
                initial_state: Pattern::And {
                    sort: k_rust::kore::ast::Sort::Application {
                        name: "SortGeneratedTopCell".into(),
                        arguments: Vec::new(),
                    },
                    arguments: vec![
                        support::initial_state(
                            support::app("Lblx", vec![support::var("VarX", "SortInt")]),
                            "SortProg",
                        ),
                        condition,
                    ],
                },
                oracles: vec![
                    OracleDeclaration::new(
                        CrashPolicy::Reject,
                        Projection::State(StateProjection::WholeTerm),
                    )
                    .unwrap(),
                ],
            }];
            let generation = replace(validator.baseline(), "REMAINDER.pr", "0", "1");
            let campaign = Campaign {
                validator: &validator,
                module: "REMAINDER-RECORD",
                observation: &[],
                classify: &normal,
                tests: &tests,
                budget: BUDGET,
            };
            let [path_set, state_set] =
                MODALITIES.map(|modality| run(&campaign, &generation, modality));
            let path_set = path_set.expect("the path set keeps the baseline per test");
            assert_eq!(
                path_set.baseline[0].run,
                SideRun::Failed(ExecutionFailureKind::ContradictedClaim)
            );
            assert!(path_set.baseline[0].notes.leaf_contradiction);
            assert_eq!(
                state_set.err(),
                Some(CampaignFailureKind::BaselineOracleFailed),
                "the state set refuses the baseline"
            );
        });
    }

    /// fz26 KINK-PATHSET-FALLBACK, the soundness guards at admission
    /// (`testdata/k/stateset/guards.k`; kink-native `tests/exclusion.rs` pins the exclusions): on
    /// each leaf kind kink reads, reached by two converging paths, a state-set campaign admits the
    /// baseline exactly as the path-set campaign does.
    /// - `two(0)` (a `preserves-definedness` undefined step) and `tc(0)` (a contradicted `total`):
    ///   a leaf contradiction, so the baseline is kept and only the test fails.
    /// - `ab(0)` (the record on an absorbed arrival's prefix only): excluded by the list alone, so
    ///   the baseline is refused.
    /// - `cr(0)` (a crash beside a feasible undefined step, under `CompareIdentity`): two
    ///   terminals in both modalities, so the side is `Unknown` and the baseline is refused.
    #[test]
    #[ignore = "kink"]
    fn the_soundness_guards_admit_a_baseline_alike_in_both_modalities() {
        on_a_big_stack(|| {
            use kink_campaign::ExecutionFailureKind;
            let validator = NativeValidator::bind(
                support::load_path(&Path::new(support::DIR).join("stateset/guards.k"), "GUARDS"),
                CompileOptions::default(),
            );
            let generation = replace(validator.baseline(), "GUARDS.join", "0", "1");
            let side = validator.compile_baseline().unwrap();
            for (symbol, policy, kept) in [
                ("Lbltwo", CrashPolicy::Reject, true),
                ("Lbltc", CrashPolicy::Reject, true),
                ("Lblab", CrashPolicy::Reject, false),
                ("Lblcr", CrashPolicy::CompareIdentity, false),
            ] {
                let tests = test("g", symbol, 0, policy);
                let campaign = Campaign {
                    validator: &validator,
                    module: "GUARDS",
                    observation: &[],
                    classify: &crash_is_a_crash,
                    tests: &tests,
                    budget: BUDGET,
                };
                for modality in MODALITIES {
                    let outcome = run(&campaign, &generation, modality);
                    if kept {
                        let run =
                            outcome.unwrap_or_else(|e| panic!("{symbol} {modality:?}: {e:?}"));
                        assert_eq!(
                            run.baseline[0].run,
                            SideRun::Failed(ExecutionFailureKind::ContradictedClaim),
                            "{symbol} {modality:?}"
                        );
                        assert!(run.baseline[0].notes.leaf_contradiction, "{symbol}");
                    } else {
                        assert_eq!(
                            outcome.err(),
                            Some(CampaignFailureKind::BaselineOracleFailed),
                            "{symbol} {modality:?}"
                        );
                    }
                }
                if symbol == "Lblcr" {
                    assert_eq!(
                        leaves(&side, "GUARDS", &tests[0].initial_state, BUDGET, None),
                        (
                            ResultModality::StateSet,
                            vec![(HaltClass::Trivial, 1), (HaltClass::Stuck, 1)]
                        )
                    );
                }
            }
        });
    }
}
