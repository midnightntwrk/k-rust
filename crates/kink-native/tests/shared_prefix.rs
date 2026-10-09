//! CS-06: identity-built native trees preserve the reference bridge's canonical paths and
//! whole evaluations over every step-event fixture, including sibling predicates and gaps.

#[path = "../../../testdata/k/step_support.rs"]
mod step_support;
#[path = "../../../testdata/k/support.rs"]
mod support;

use std::collections::BTreeMap;
use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::definition::AttributeKey;
use k_rust::kast::{Sort as KastSort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::kore_sort;
use k_rust::kore::{ast::Pattern, parser::parse_definition};
use kink_native::bridge::{BridgeContext, paths_from_steps, tree_from_steps};
use kink_native::execution::{ExecutionAdapter, ExecutionBudget, SolverProfile, SteppedExecution};
use kink_native::feasibility::{BackendRelations, TestInitialState};
use kink_native::step_events::{ObservationDecider, StepEventSpec, StepObservation};
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_patch::{Edit, InsertPosition, Patch, TermRef};
use kink_pattern::{
    Atom, EvaluationContext, EvaluationOptions, EventVocabulary, ExecutionTerminalKind, MatchMode,
    MonitorOptions, PathInput, PatternArm, PatternPlan, PayloadClause, Relation, RelationDecider,
    SearchPolicy, StructuralDecider, SymbolSorts, TermRelation, TreeOptions,
    evaluate_tree_with_stats, evaluate_with,
};

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(60),
    max_simplification_iterations: 1000,
    max_depth: Some(64),
    max_breadth: None,
};

fn app(symbol: &str, arguments: Vec<Pattern>) -> Pattern {
    support::app(&format!("Lbl{symbol}"), arguments)
}

fn var(name: &str, sort: &str) -> Pattern {
    support::var(name, sort)
}

fn seq(operation: Pattern, rest: Pattern) -> Pattern {
    app("seq", vec![operation, rest])
}

fn boolean(value: bool) -> Pattern {
    Pattern::DomainValue {
        sort: kore_sort("SortBool"),
        value: value.to_string().into(),
    }
}

fn nat(value: usize) -> Pattern {
    (0..value).fold(app("z", vec![]), |inner, _| app("s", vec![inner]))
}

fn address(value: i64) -> Pattern {
    app("addr", vec![support::int(value)])
}

/// A pre-state declaration over `<k> program ~> R </k>`, or a whole transition.
fn spec(
    constructor: &str,
    sort: &str,
    pre: Pattern,
    post: Option<Pattern>,
    payload: &[&str],
) -> StepEventSpec {
    StepEventSpec {
        constructor: constructor.into(),
        pre: support::k_config(pre, sort, "R", "C"),
        post: post.map(|post| support::k_config(post, sort, "R", "C2")),
        payload: payload.iter().map(|name| (*name).into()).collect(),
    }
}

/// One fixture input: the definition, its main module, the program and its sort, and the
/// declarations.
struct Case {
    label: &'static str,
    fixture: &'static str,
    module: &'static str,
    program: Pattern,
    sort: &'static str,
    specs: Vec<StepEventSpec>,
}

/// Counts of what was compared, so a case cannot pass vacuously.
#[derive(Debug, Default)]
struct Tally {
    runs: usize,
    refused_runs: usize,
    path_sets: usize,
    paths: usize,
    compared: usize,
    phase1_classifications: usize,
    phase1_cache_hits: usize,
    outcomes: BTreeMap<String, usize>,
}

/// Every plan over the declared constructors: each constructor alone with its payload bound;
/// every ordered pair under `NextEvent` and `EventuallyAfter`, without payload and, when the
/// first payload positions have one sort, binding it on the first and using it on the second;
/// chains of three under `NextEvent` and under `EventuallyAfter`; and two-arm alternatives.
fn plans(vocabulary: &EventVocabulary, constructors: &[String]) -> Vec<(String, PatternPlan)> {
    let declared = |name: &str| vocabulary.constructor(name).expect("declared constructor");
    let bare = |name: &str| Atom {
        constructor: name.into(),
        payload: Vec::new(),
    };
    let clause = |mode, variable: &str| PayloadClause {
        position: 0,
        mode,
        variable: variable.into(),
    };
    let mut plans = Vec::new();
    let mut push = |label: String, variables: Vec<(String, k_rust::kore::ast::Sort)>, arms| {
        let plan = PatternPlan::new(vocabulary, variables, arms, None)
            .unwrap_or_else(|failure| panic!("{label}: {failure}"));
        plans.push((label, plan));
    };
    for name in constructors {
        let sorts = &declared(name).payload_sorts;
        let variables = sorts
            .iter()
            .enumerate()
            .map(|(position, sort)| (format!("V{position}"), sort.clone()))
            .collect::<Vec<_>>();
        let atom = Atom {
            constructor: name.clone(),
            payload: variables
                .iter()
                .enumerate()
                .map(|(position, (variable, _))| PayloadClause {
                    position,
                    mode: MatchMode::Bind,
                    variable: variable.clone(),
                })
                .collect(),
        };
        push(
            format!("{name}(..)"),
            variables,
            vec![PatternArm {
                atoms: vec![atom],
                relations: Vec::new(),
            }],
        );
    }
    for first in constructors {
        for second in constructors {
            for relation in [Relation::NextEvent, Relation::EventuallyAfter] {
                push(
                    format!("{first} {relation:?} {second}"),
                    Vec::new(),
                    vec![PatternArm {
                        atoms: vec![bare(first), bare(second)],
                        relations: vec![relation],
                    }],
                );
                let (Some(left), Some(right)) = (
                    declared(first).payload_sorts.first(),
                    declared(second).payload_sorts.first(),
                ) else {
                    continue;
                };
                if left != right {
                    continue;
                }
                push(
                    format!("{first}(X) {relation:?} {second}(X)"),
                    vec![("X".into(), left.clone())],
                    vec![PatternArm {
                        atoms: vec![
                            Atom {
                                constructor: first.clone(),
                                payload: vec![clause(MatchMode::Bind, "X")],
                            },
                            Atom {
                                constructor: second.clone(),
                                payload: vec![clause(MatchMode::Use, "X")],
                            },
                        ],
                        relations: vec![relation],
                    }],
                );
            }
            push(
                format!("{first} Next {second} | {second} Eventually {first}"),
                Vec::new(),
                vec![
                    PatternArm {
                        atoms: vec![bare(first), bare(second)],
                        relations: vec![Relation::NextEvent],
                    },
                    PatternArm {
                        atoms: vec![bare(second), bare(first)],
                        relations: vec![Relation::EventuallyAfter],
                    },
                ],
            );
        }
    }
    for first in constructors {
        for second in constructors {
            for third in constructors {
                for relation in [Relation::NextEvent, Relation::EventuallyAfter] {
                    push(
                        format!("{first} {relation:?} {second} {relation:?} {third}"),
                        Vec::new(),
                        vec![PatternArm {
                            atoms: vec![bare(first), bare(second), bare(third)],
                            relations: vec![relation, relation],
                        }],
                    );
                }
            }
        }
    }
    plans
}

/// Runs every case to completion and cut at depths 1, 2 and 3, and compares the evaluators on
/// every bridged path set.
fn differential(cases: Vec<Case>) -> Tally {
    let mut tally = Tally::default();
    for case in cases {
        let validator =
            NativeValidator::bind(support::load(case.fixture), CompileOptions::default());
        let side = validator.compile_baseline().expect("fixture compiles");
        let state = support::initial_state(case.program.clone(), case.sort);
        let mut backend = Backend::new(
            &side.artifacts().definition_kore,
            case.module,
            BackendOptions::default(),
        )
        .expect("backend");
        let observation =
            StepObservation::new(&mut backend, case.specs.clone()).expect("declarations validate");
        let vocabulary = observation.vocabulary().clone();
        let mut constructors = case
            .specs
            .iter()
            .map(|spec| spec.constructor.clone())
            .collect::<Vec<_>>();
        constructors.dedup();
        let plans = plans(&vocabulary, &constructors);
        let sorts = SymbolSorts::from_definition(
            &parse_definition(&side.artifacts().definition_kore).expect("compiled KORE parses"),
        );
        for max_depth in [BUDGET.max_depth, Some(1), Some(2), Some(3)] {
            let budget = ExecutionBudget {
                max_depth,
                ..BUDGET
            };
            tally.runs += 1;
            let mut run_backend = Backend::new(
                &side.artifacts().definition_kore,
                case.module,
                BackendOptions::default(),
            )
            .expect("run backend");
            let Ok(Ok(execution)) = ExecutionAdapter::with_profile(SolverProfile::BUILD)
                .execute_steps(&mut run_backend, &state, budget)
            else {
                tally.refused_runs += 1;
                continue;
            };
            let context = EvaluationContext {
                test_id: "differential".into(),
                bounds: budget.bounds(),
                vocabulary: vocabulary.clone(),
                symbol_sorts: sorts.clone(),
            };
            let normal = |_: &Pattern| ExecutionTerminalKind::Normal;
            let counted = backend
                .with_solver(None, |definition, solver| {
                    let decider =
                        ObservationDecider::new(definition, solver, TestInitialState::of_test(&state));
                    let relations =
                        BackendRelations::shared(definition, solver, TestInitialState::of_test(&state));
                    let Ok(bridged) = paths_from_steps(
                        &BridgeContext {
                            test_id: "differential",
                            classify: &normal,
                            sorts: &sorts,
                        },
                        &execution,
                        &observation,
                        &decider,
                    ) else {
                        return Ok::<_, k_rust::backend::BackendError>(None);
                    };
                    let shared = tree_from_steps(
                        &BridgeContext {
                            test_id: "differential",
                            classify: &normal,
                            sorts: &sorts,
                        },
                        &execution,
                        &observation,
                        &decider,
                    ).expect("identity tree bridges a reference-compatible run");
                    assert_eq!(shared.tree.paths(), bridged.paths, "{} canonical PathInputs depth {max_depth:?}", case.label);
                    assert_eq!(shared.collection, bridged.collection, "{} collection", case.label);
                    let mut outcomes = Vec::new();
                    let mut unkeyed = bridged.paths.clone();
                    for path in &mut unkeyed {
                        path.path_key = None;
                    }
                    for (keyed, paths) in [(true, bridged.paths.clone()), (false, unkeyed)] {
                        let mut tree = shared.tree.clone();
                        if !keyed {
                            // Unkeyed coverage is already pinned by CS-04's tree tests; the
                            // native builder always returns canonical stable keys.
                            tree = kink_pattern::PathTree::from_paths(paths);
                        }
                        let evaluation = EvaluationOptions {
                            stable_path_keys: keyed,
                            search_policy: SearchPolicy::Exhaustive,
                            input_error: false,
                        };
                        let deciders: [(&str, &dyn RelationDecider); 2] =
                            [("shared", &relations), ("structural", &StructuralDecider)];
                        for (plan_label, plan) in &plans {
                            for (decider_label, decider) in deciders {
                                let reference = evaluate_with(
                                    &context,
                                    plan,
                                    tree.paths(),
                                    &bridged.collection,
                                    None,
                                    evaluation,
                                    decider,
                                );
                                let monitored = evaluate_tree_with_stats(
                                    &context,
                                    plan,
                                    &tree,
                                    &bridged.collection,
                                    None,
                                    TreeOptions {
                                        evaluation,
                                        monitor: MonitorOptions { cap: usize::MAX },
                                    },
                                    decider,
                                );
                                // Exhaustive, no side table: the monitor computes every result itself.
                                assert!(
                                    !monitored.as_ref().is_ok_and(|(_, stats)| stats.deferred),
                                    "{} deferred",
                                    case.label
                                );
                                let monitored = monitored.map(|(evaluation, _)| evaluation);
                                assert_eq!(
                                    monitored, reference,
                                    "{} depth {max_depth:?} keyed {keyed} {plan_label} {decider_label}",
                                    case.label
                                );
                                outcomes.push(match &reference {
                                    Ok(evaluation) => format!("{:?}", evaluation.outcome),
                                    Err(failure) => format!("{:?}", failure.kind()),
                                });
                            }
                        }
                    }
                    Ok(Some((bridged.paths.len(), outcomes, shared.stats)))
                })
                .expect("baseline solver");
            match counted {
                Some((paths, outcomes, stats)) => {
                    tally.phase1_classifications += stats.phase1_classifications;
                    tally.phase1_cache_hits += stats.phase1_cache_hits;
                    tally.path_sets += 1;
                    tally.paths += paths;
                    tally.compared += outcomes.len();
                    for outcome in outcomes {
                        *tally.outcomes.entry(outcome).or_default() += 1;
                    }
                }
                None => tally.refused_runs += 1,
            }
        }
    }
    tally
}

fn report(name: &str, tally: &Tally) {
    eprintln!(
        "CS06 differential {name} ({}): {tally:?}",
        if cfg!(feature = "z3") { "z3" } else { "no-z3" }
    );
    assert!(tally.path_sets > 0, "{name}: no path set was compared");
    assert!(tally.compared > 0, "{name}: nothing was compared");
}

#[test]
fn symmem_paths_agree() {
    let x = || var("X", "SortNat");
    let y = || var("Y", "SortNat");
    let mut cases = Vec::new();
    for whole in [false, true] {
        cases.push(Case {
            label: "symmem ground",
            fixture: "symmem.k",
            module: "SYMMEM",
            program: seq(
                app("write", vec![app("addr", vec![nat(0)]), nat(1)]),
                seq(
                    app("load", vec![app("addr", vec![nat(0)]), nat(1)]),
                    app("halt", vec![]),
                ),
            ),
            sort: "SortProg",
            specs: step_support::symmem(whole),
        });
        cases.push(Case {
            label: "symmem symbolic",
            fixture: "symmem.k",
            module: "SYMMEM",
            program: seq(
                app("write", vec![app("addr", vec![x()]), nat(1)]),
                seq(
                    app("load", vec![app("addr", vec![y()]), var("V", "SortNat")]),
                    seq(
                        app("free", vec![app("addr", vec![x()])]),
                        app("halt", vec![]),
                    ),
                ),
            ),
            sort: "SortProg",
            specs: step_support::symmem(whole),
        });
        cases.push(Case {
            label: "symmem fork",
            fixture: "symmem.k",
            module: "SYMMEM",
            program: seq(
                app("write", vec![app("addr", vec![x()]), nat(1)]),
                app(
                    "fork",
                    vec![
                        seq(
                            app("load", vec![app("addr", vec![x()]), nat(1)]),
                            app("halt", vec![]),
                        ),
                        seq(
                            app("free", vec![app("addr", vec![y()])]),
                            seq(
                                app("load", vec![app("addr", vec![y()]), nat(0)]),
                                app("halt", vec![]),
                            ),
                        ),
                    ],
                ),
            ),
            sort: "SortProg",
            specs: step_support::symmem(whole),
        });
    }
    report("symmem", &differential(cases));
}

#[test]
fn guardedmem_and_guardedeq_paths_agree() {
    let a = || var("A", "SortInt");
    let b = || var("B", "SortInt");
    let mut cases = Vec::new();
    for whole in [false, true] {
        cases.push(Case {
            label: "guardedmem symbolic",
            fixture: "guardedmem.k",
            module: "GUARDEDMEM",
            program: seq(
                app("write", vec![app("addr", vec![a()]), support::int(7)]),
                seq(
                    app("load", vec![app("addr", vec![b()]), var("V", "SortInt")]),
                    app("halt", vec![]),
                ),
            ),
            sort: "SortProg",
            specs: step_support::guardedmem(whole),
        });
        cases.push(Case {
            label: "guardedmem ground fault",
            fixture: "guardedmem.k",
            module: "GUARDEDMEM",
            program: seq(
                app("write", vec![address(1), support::int(7)]),
                seq(
                    app("load", vec![address(-1), support::int(7)]),
                    app("halt", vec![]),
                ),
            ),
            sort: "SortProg",
            specs: step_support::guardedmem(whole),
        });
        cases.push(Case {
            label: "guardedeq symbolic load",
            fixture: "guardedeq.k",
            module: "GUARDEDEQ",
            program: seq(
                app("write", vec![address(1), support::int(5)]),
                seq(
                    app("load", vec![app("addr", vec![a()]), var("V", "SortInt")]),
                    app("halt", vec![]),
                ),
            ),
            sort: "SortProg",
            specs: step_support::int_memory(whole),
        });
        cases.push(Case {
            label: "guardedeq symbolic write",
            fixture: "guardedeq.k",
            module: "GUARDEDEQ",
            program: seq(
                app("write", vec![app("addr", vec![a()]), support::int(5)]),
                seq(
                    app("load", vec![address(0), var("V", "SortInt")]),
                    app("halt", vec![]),
                ),
            ),
            sort: "SortProg",
            specs: step_support::int_memory(whole),
        });
    }
    report("guardedmem/guardedeq", &differential(cases));
}

#[test]
fn counter_paths_agree() {
    let mut cases = Vec::new();
    for whole in [false, true] {
        cases.push(Case {
            label: "counter ground",
            fixture: "counter.k",
            module: "COUNTER",
            program: app("counter", vec![nat(0), nat(3)]),
            sort: "SortCounter",
            specs: step_support::counter(whole),
        });
        for choice in [boolean(true), boolean(false), var("B", "SortBool")] {
            cases.push(Case {
                label: "counter choose",
                fixture: "counter.k",
                module: "COUNTER",
                program: app("choose", vec![choice]),
                sort: "SortControl",
                specs: step_support::counter(whole),
            });
        }
    }
    report("counter", &differential(cases));
}

#[test]
fn nextgap_and_nd_paths_agree() {
    let b = || var("B", "SortBool");
    let nextgap = || {
        vec![
            spec(
                "goMid",
                "SortProg",
                app("go", vec![b()]),
                Some(app("mid", vec![b()])),
                &[],
            ),
            spec(
                "midFin",
                "SortProg",
                app("mid", vec![boolean(true)]),
                Some(app("fin", vec![])),
                &[],
            ),
            spec(
                "finHalt",
                "SortProg",
                app("fin", vec![]),
                Some(app("halt", vec![])),
                &[],
            ),
        ]
    };
    let nd = || {
        let start = || app("start", vec![]);
        vec![
            spec("toMid1", "SortS", start(), Some(app("mid1", vec![])), &[]),
            spec("toMid2", "SortS", start(), Some(app("mid2", vec![])), &[]),
            spec("atMid1", "SortS", app("mid1", vec![]), None, &[]),
            spec("spinning", "SortS", app("spin", vec![]), None, &[]),
        ]
    };
    let mut cases = Vec::new();
    for program in [
        app("go", vec![var("X", "SortBool")]),
        app("go", vec![boolean(true)]),
        app("go", vec![boolean(false)]),
    ] {
        cases.push(Case {
            label: "nextgap",
            fixture: "nextgap.k",
            module: "NEXTGAP",
            program,
            sort: "SortProg",
            specs: nextgap(),
        });
    }
    for program in [app("start", vec![]), app("spin", vec![])] {
        cases.push(Case {
            label: "nd",
            fixture: "nd.k",
            module: "ND",
            program,
            sort: "SortS",
            specs: nd(),
        });
    }
    let tally = differential(cases);
    assert!(
        tally.phase1_classifications > 0,
        "structural classifications ran"
    );
    assert!(
        tally.phase1_cache_hits > 0,
        "actual repeated spin states reuse phase 1"
    );
    report("nextgap/nd", &tally);
}

#[test]
fn conflate_paths_agree() {
    let int = |name: &str| var(name, "SortInt");
    let check_specs = || {
        vec![
            spec(
                "check",
                "SortProg",
                seq(app("check", vec![int("J")]), var("P", "SortProg")),
                None,
                &["J"],
            ),
            spec(
                "check2",
                "SortProg",
                seq(app("check2", vec![int("J")]), var("P", "SortProg")),
                None,
                &["J"],
            ),
            spec(
                "go",
                "SortProg",
                seq(app("go", vec![var("X", "SortBox")]), var("P", "SortProg")),
                None,
                &["X"],
            ),
        ]
    };
    let symbolic = || {
        seq(
            app("check", vec![int("A")]),
            seq(
                app("check2", vec![int("B")]),
                seq(app("go", vec![var("Bx", "SortBox")]), app("done", vec![])),
            ),
        )
    };
    let ground = || {
        seq(
            app("check", vec![support::int(0)]),
            seq(
                app("check2", vec![support::int(1)]),
                seq(
                    app("go", vec![app("c", vec![support::int(5)])]),
                    app("done", vec![]),
                ),
            ),
        )
    };
    let mut cases = Vec::new();
    for (fixture, module) in [("conflate.k", "CONFLATE"), ("conflatem.k", "CONFLATEM")] {
        for program in [symbolic(), ground()] {
            cases.push(Case {
                label: "conflate",
                fixture,
                module,
                program,
                sort: "SortProg",
                specs: check_specs(),
            });
        }
    }
    let t_spec = |constructor: &str, symbol: &str| {
        spec(
            constructor,
            "SortProg",
            seq(app(symbol, vec![int("J")]), var("P", "SortProg")),
            None,
            &["J"],
        )
    };
    let bare_spec = |constructor: &str, symbol: &str| {
        spec(
            constructor,
            "SortProg",
            seq(app(symbol, vec![]), var("P", "SortProg")),
            None,
            &[],
        )
    };
    cases.push(Case {
        label: "conflate2",
        fixture: "conflate2.k",
        module: "CONFLATE2",
        program: seq(
            app("check", vec![int("A")]),
            seq(app("mk", vec![]), app("done", vec![])),
        ),
        sort: "SortProg",
        specs: vec![
            t_spec("check", "check"),
            bare_spec("mk", "mk"),
            t_spec("t", "t"),
        ],
    });
    cases.push(Case {
        label: "conflate3",
        fixture: "conflate3.k",
        module: "CONFLATE3",
        program: seq(
            app("new1", vec![]),
            seq(
                app("burnNew", vec![]),
                seq(app("new2", vec![]), app("done", vec![])),
            ),
        ),
        sort: "SortProg",
        specs: vec![
            bare_spec("new1", "new1"),
            bare_spec("burnNew", "burnNew"),
            t_spec("t1", "t1"),
            t_spec("t", "t"),
        ],
    });
    report("conflate*", &differential(cases));
}

fn symmem_program() -> Pattern {
    let z = || support::app("Lblz", vec![]);
    let address = || support::app("Lbladdr", vec![z()]);
    let value = || support::app("Lbls", vec![z()]);
    support::app(
        "Lblseq",
        vec![
            support::app("Lblwrite", vec![address(), value()]),
            support::app(
                "Lblseq",
                vec![
                    support::app("Lblload", vec![address(), value()]),
                    support::app("Lblhalt", vec![]),
                ],
            ),
        ],
    )
}

fn run_steps(side: &ValidatedDefinition, module: &str, state: &Pattern) -> SteppedExecution {
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .expect("backend");
    ExecutionAdapter::with_profile(SolverProfile::BUILD)
        .execute_steps(&mut backend, state, BUDGET)
        .expect("execution")
        .expect("step run")
}

fn identity_paths_for(
    baseline: &ValidatedDefinition,
    side: &ValidatedDefinition,
    module: &str,
    state: &Pattern,
    specs: Vec<StepEventSpec>,
) -> Vec<PathInput> {
    let execution = run_steps(side, module, state);
    let mut baseline_backend = Backend::new(
        &baseline.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .expect("baseline backend");
    let observation =
        StepObservation::new(&mut baseline_backend, specs).expect("declarations validate");
    let sorts = SymbolSorts::from_definition(
        &parse_definition(&baseline.artifacts().definition_kore).expect("compiled KORE parses"),
    );
    let normal = |_: &Pattern| ExecutionTerminalKind::Normal;
    baseline_backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(state));
            let bridged = paths_from_steps(
                &BridgeContext {
                    test_id: "identity",
                    classify: &normal,
                    sorts: &sorts,
                },
                &execution,
                &observation,
                &decider,
            )
            .expect("steps bridge");
            let shared = tree_from_steps(
                &BridgeContext {
                    test_id: "identity",
                    classify: &normal,
                    sorts: &sorts,
                },
                &execution,
                &observation,
                &decider,
            )
            .expect("identity tree bridges");
            assert_eq!(
                shared.tree.paths(),
                bridged.paths,
                "SO-AT1 canonical paths equal reference"
            );
            assert_eq!(shared.collection, bridged.collection);
            Ok::<_, k_rust::backend::BackendError>(shared.tree.paths().to_vec())
        })
        .expect("baseline decider")
}

/// A mutant with a dead existential rule (never fires) has the baseline's canonical PathInputs
/// and relation answers. Before variable identity both sides were decided under the pair
/// existentials flag; now both link the test's initial variables.
#[test]
fn so_at1_dead_existential_rule_preserves_canonical_tree_paths() {
    let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
    let baseline = validator.baseline();
    let free = support::rule(baseline, "SYMMEM.free");
    let mut dead = baseline.sentence(&free).expect("free rule").clone();
    for key in [
        AttributeKey::Label,
        AttributeKey::UniqueId,
        AttributeKey::Origin,
        AttributeKey::Location,
        AttributeKey::Source,
        AttributeKey::SourceId,
        AttributeKey::SentenceStartOffset,
        AttributeKey::SentenceEndOffset,
        AttributeKey::ContentStartLine,
        AttributeKey::ContentStartColumn,
        AttributeKey::ContentStartOffset,
    ] {
        dead.attributes_mut().remove(key.as_str());
    }
    let field = |path: &[u32]| {
        baseline
            .term(&TermRef::new(free.clone(), path))
            .expect("free term")
            .clone()
    };
    if let k_rust::definition::Sentence::Rule { body, .. } = &mut dead {
        *body = Term::Rewrite {
            left: Box::new(field(&[0, 0])),
            right: Box::new(Term::apply(
                "seq",
                vec![
                    Term::apply(
                        "write",
                        vec![
                            field(&[0, 0, 0, 0]),
                            Term::Variable {
                                name: "?E".into(),
                                sort: Some(KastSort::new("Nat")),
                            },
                        ],
                    ),
                    field(&[0, 1]),
                ],
            )),
        };
    } else {
        panic!("free is a rule");
    }
    dead.attributes_mut().set(
        AttributeKey::Priority,
        serde_json::Value::String("40".into()),
    );
    let patch = Patch::new(vec![Edit::InsertSentence {
        position: InsertPosition::After(free),
        ordinal: 0,
        sentence: dead,
    }])
    .expect("dead-rule patch");
    let original = validator.compile_baseline().expect("baseline");
    let mutant = validator.validate(&patch).expect("dead rule compiles");
    let symbolic = support::initial_state(
        support::app(
            "Lblseq",
            vec![
                support::app(
                    "Lblwrite",
                    vec![
                        support::app("Lbladdr", vec![support::var("X", "SortNat")]),
                        support::var("V", "SortNat"),
                    ],
                ),
                support::app(
                    "Lblseq",
                    vec![
                        support::app(
                            "Lblload",
                            vec![
                                support::app("Lbladdr", vec![support::var("X", "SortNat")]),
                                support::var("V", "SortNat"),
                            ],
                        ),
                        support::app("Lblhalt", vec![]),
                    ],
                ),
            ],
        ),
        "SortProg",
    );
    for state in [
        support::initial_state(symmem_program(), "SortProg"),
        symbolic,
    ] {
        let specs = step_support::symmem(true);
        let before = identity_paths_for(&original, &original, "SYMMEM", &state, specs.clone());
        let after = identity_paths_for(&original, &mutant, "SYMMEM", &state, specs);
        assert_eq!(before, after, "canonical PathInputs");

        let mut backend = Backend::new(
            &original.artifacts().definition_kore,
            "SYMMEM",
            BackendOptions::default(),
        )
        .expect("baseline backend");
        backend
            .with_solver(None, |definition, solver| {
                let decider =
                    BackendRelations::shared(definition, solver, TestInitialState::of_test(&state));
                let x = support::var("X", "SortNat");
                let z = support::app("Lblz", vec![]);
                let assumption = TermRelation {
                    left: x.clone(),
                    right: z.clone(),
                };
                let answers = |paths: &[PathInput]| {
                    paths
                        .iter()
                        .map(|path| {
                            (
                                decider.relate(path, &[], &x, &z),
                                decider.feasible(path, std::slice::from_ref(&assumption)),
                            )
                        })
                        .collect::<Vec<_>>()
                };
                assert_eq!(answers(&before), answers(&after), "shared relation answers");
                Ok::<_, k_rust::backend::BackendError>(())
            })
            .expect("baseline decider");
    }
}
