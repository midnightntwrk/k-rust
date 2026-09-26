//! Live symbolic memory observations and path-level acceptance checks.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::{collections::BTreeMap, num::NonZeroUsize, time::Duration};

use k_rust::backend::{Backend, BackendOptions};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::kore_sort;
use k_rust::kore::{ast::Pattern, codec, parser::parse_definition};
use kink_native::bridge::{BridgeContext, BridgedPaths, paths_from_execution};
use kink_native::execution::{
    AdaptedExecution, BaselineLeaf, ExecutionAdapter, ExecutionBudget, HaltClass, SolverProfile,
};
use kink_native::feasibility::{LeafFeasibility, with_backend_relations};
use kink_native::observation::{DomainEventSpec, DomainPayload, NativeEvent, PayloadSource};
use kink_native::report::{ReportInput, ReportResult, step3_report};
use kink_native::{
    NativeValidator, ObservedRule, RewriteRules, RuleSelection, RuleSelector, SelectionFailure,
    ValidatedDefinition, select_rules,
};
use kink_pattern::{
    Atom, CollectionStop, Constructor, Evaluation, EvaluationContext, EvaluationOptions,
    EventVocabulary, ExecutionTerminalKind, MatchMode, PathInput, PathStop, PatternArm,
    PatternOutcome, PatternPlan, PayloadClause, Relation, SearchPolicy, SymbolSorts, TermRelation,
    evaluate, evaluate_with,
};

/// The profile of this build (README section 9): the `z3` feature of kink-native.
const PROFILE: SolverProfile = SolverProfile::BUILD;

/// Selects the expected value of a profile table: `(no_z3, z3)` columns (README R8).
fn by_profile<T>(no_z3: T, z3: T) -> T {
    if cfg!(feature = "z3") { z3 } else { no_z3 }
}

/// SMT options for every backend in this file. k-rust's default 125 ms timeout makes a Z3
/// `unknown` depend on load (README R4); 4 s doubled twice (up to 28 s per query) keeps the
/// small fixture queries decided. A no-Z3 backend ignores them.
const BACKEND_OPTIONS: BackendOptions = BackendOptions {
    smt_timeout_ms: 4000,
    smt_retry_limit: 2,
};

fn backend(kore: &str, module: &str) -> Backend {
    Backend::new(kore, module, BACKEND_OPTIONS).expect("backend")
}

fn adapter(manifest: kink_native::observation::InstalledObservationManifest) -> ExecutionAdapter {
    ExecutionAdapter::with_profile(manifest, PROFILE)
}

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: None,
    max_breadth: None,
};

// These positions were resolved by executing all six rules with BindingVariable payloads
// (asserted below), including the generated-cell bindings. They are not rule-text positions.
const SYM_WRITE_A: usize = 0;
const SYM_WRITE_V: usize = 3;
const SYM_LOAD_A: usize = 0;
const SYM_LOAD_V: usize = 3;
const SYM_FREE_A: usize = 0;
const GUARD_WRITE_A: usize = 1;
const GUARD_WRITE_V: usize = 2;
const GUARD_LOAD_A: usize = 1;
const GUARD_LOAD_V: usize = 2;
const GUARD_LOAD_NEG_A: usize = 1;
const GUARD_LOAD_NEG_V: usize = 2;

fn nat(name: &str) -> Pattern {
    support::var(name, "SortNat")
}
fn integer(name: &str) -> Pattern {
    support::var(name, "SortInt")
}
fn z() -> Pattern {
    support::app("Lblz", vec![])
}
fn s(value: Pattern) -> Pattern {
    support::app("Lbls", vec![value])
}
fn addr(value: Pattern) -> Pattern {
    support::app("Lbladdr", vec![value])
}
fn write(address: Pattern, value: Pattern) -> Pattern {
    support::app("Lblwrite", vec![address, value])
}
fn load(address: Pattern, value: Pattern) -> Pattern {
    support::app("Lblload", vec![address, value])
}
fn load_neg(address: Pattern, value: Pattern) -> Pattern {
    support::app("LblloadNeg", vec![address, value])
}
fn free(address: Pattern) -> Pattern {
    support::app("Lblfree", vec![address])
}
fn halt() -> Pattern {
    support::app("Lblhalt", vec![])
}
fn seq(operation: Pattern, rest: Pattern) -> Pattern {
    support::app("Lblseq", vec![operation, rest])
}
fn fork(left: Pattern, right: Pattern) -> Pattern {
    support::app("Lblfork", vec![left, right])
}

fn p1() -> Pattern {
    seq(
        write(addr(nat("X")), nat("V")),
        seq(load(addr(nat("X")), nat("W")), halt()),
    )
}
fn p2() -> Pattern {
    seq(
        write(addr(nat("X")), nat("V")),
        seq(free(addr(z())), seq(load(addr(nat("X")), nat("W")), halt())),
    )
}
fn p3() -> Pattern {
    seq(
        load(addr(nat("X")), nat("W")),
        seq(write(addr(nat("X")), nat("V")), halt()),
    )
}
fn p4() -> Pattern {
    fork(
        seq(write(addr(nat("X")), nat("V")), halt()),
        seq(load(addr(nat("X")), nat("W")), halt()),
    )
}
fn p5() -> Pattern {
    fork(p1(), seq(load(addr(nat("X")), nat("W")), halt()))
}
fn p6() -> Pattern {
    seq(
        write(addr(nat("X")), nat("V")),
        seq(load(addr(nat("Y")), nat("W")), halt()),
    )
}
fn p7() -> Pattern {
    seq(
        write(addr(z()), nat("V")),
        seq(load(addr(s(nat("Y"))), nat("W")), halt()),
    )
}
fn p8() -> Pattern {
    p1()
}
fn p9() -> Pattern {
    fork(
        p1(),
        seq(
            write(addr(nat("Y")), nat("V")),
            seq(load(addr(nat("Y")), nat("W")), halt()),
        ),
    )
}

fn g1() -> Pattern {
    seq(
        write(addr(integer("X")), integer("V")),
        seq(load(addr(integer("Y")), integer("W")), halt()),
    )
}
fn g2() -> Pattern {
    seq(
        write(addr(integer("X")), integer("V")),
        seq(load_neg(addr(integer("Y")), integer("W")), halt()),
    )
}
fn g3() -> Pattern {
    seq(
        write(addr(support::int(1)), integer("V")),
        seq(load(addr(support::int(1)), integer("W")), halt()),
    )
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Fixture {
    Sym,
    Guard,
    /// `symwrap.k`: symmem's write/load over an `anywhere`-collapsed address constructor.
    Wrap,
    /// `symowise.k`: an `owise` rule that no value of its symbolic subject reaches.
    Owise,
    /// `symensures.k`: an `ensures` that constrains payload variables after their events.
    Ensures,
}

impl Fixture {
    fn name(self) -> &'static str {
        match self {
            Self::Sym => "symmem.k",
            Self::Guard => "guardedmem.k",
            Self::Wrap => "symwrap.k",
            Self::Owise => "symowise.k",
            Self::Ensures => "symensures.k",
        }
    }
    fn module(self) -> &'static str {
        match self {
            Self::Sym => "SYMMEM",
            Self::Guard => "GUARDEDMEM",
            Self::Wrap => "SYMWRAP",
            Self::Owise => "SYMOWISE",
            Self::Ensures => "SYMENSURES",
        }
    }
    fn address_sort(self) -> &'static str {
        match self {
            Self::Sym | Self::Wrap | Self::Owise | Self::Ensures => "SortAddress",
            Self::Guard => "SortInt",
        }
    }
    fn value_sort(self) -> &'static str {
        match self {
            Self::Sym | Self::Wrap | Self::Owise | Self::Ensures => "SortNat",
            Self::Guard => "SortInt",
        }
    }
    fn labels(self) -> &'static [&'static str; 3] {
        match self {
            Self::Sym => &["SYMMEM.write", "SYMMEM.load", "SYMMEM.free"],
            Self::Guard => &["GUARDEDMEM.write", "GUARDEDMEM.load", "GUARDEDMEM.loadNeg"],
            Self::Wrap => &["SYMWRAP.write", "SYMWRAP.load", "SYMWRAP.collapse"],
            Self::Owise => &["SYMOWISE.write", "SYMOWISE.load", "SYMOWISE.other"],
            Self::Ensures => &["SYMENSURES.write", "SYMENSURES.load", "SYMENSURES.pin"],
        }
    }
}

struct Run {
    execution: AdaptedExecution,
    bridged: BridgedPaths,
    context: EvaluationContext,
    backend: Backend,
    state: Pattern,
}

fn vocabulary(fixture: Fixture) -> EventVocabulary {
    let address = kore_sort(fixture.address_sort());
    let value = kore_sort(fixture.value_sort());
    let mut constructors = vec![
        Constructor {
            name: "memoryWrite".into(),
            payload_sorts: vec![address.clone(), value.clone()],
        },
        Constructor {
            name: "memoryLoad".into(),
            payload_sorts: vec![address.clone(), value],
        },
    ];
    if matches!(fixture, Fixture::Sym) {
        constructors.push(Constructor {
            name: "memoryFree".into(),
            payload_sorts: vec![address],
        });
    }
    EventVocabulary::new(constructors).expect("vocabulary")
}

fn observed(
    validator: &NativeValidator,
    label: &str,
    constructor: &str,
    indices: &[usize],
) -> ObservedRule {
    ObservedRule {
        rule: support::rule(validator.baseline(), label),
        emit_rule_applied: false,
        domain_events: vec![DomainEventSpec {
            constructor: constructor.into(),
            payload: indices
                .iter()
                .copied()
                .map(PayloadSource::BindingValue)
                .collect(),
        }],
    }
}

fn observations(fixture: Fixture, validator: &NativeValidator) -> Vec<ObservedRule> {
    match fixture {
        Fixture::Sym => vec![
            observed(
                validator,
                "SYMMEM.write",
                "memoryWrite",
                &[SYM_WRITE_A, SYM_WRITE_V],
            ),
            observed(
                validator,
                "SYMMEM.load",
                "memoryLoad",
                &[SYM_LOAD_A, SYM_LOAD_V],
            ),
            observed(validator, "SYMMEM.free", "memoryFree", &[SYM_FREE_A]),
        ],
        Fixture::Wrap | Fixture::Owise | Fixture::Ensures => vec![
            observed(
                validator,
                fixture.labels()[0],
                "memoryWrite",
                &[SYM_WRITE_A, SYM_WRITE_V],
            ),
            observed(
                validator,
                fixture.labels()[1],
                "memoryLoad",
                &[SYM_LOAD_A, SYM_LOAD_V],
            ),
        ],
        Fixture::Guard => vec![
            observed(
                validator,
                "GUARDEDMEM.write",
                "memoryWrite",
                &[GUARD_WRITE_A, GUARD_WRITE_V],
            ),
            observed(
                validator,
                "GUARDEDMEM.load",
                "memoryLoad",
                &[GUARD_LOAD_A, GUARD_LOAD_V],
            ),
            observed(
                validator,
                "GUARDEDMEM.loadNeg",
                "memoryLoad",
                &[GUARD_LOAD_NEG_A, GUARD_LOAD_NEG_V],
            ),
        ],
    }
}

fn run_side(
    validator: &NativeValidator,
    side: &ValidatedDefinition,
    fixture: Fixture,
    rules: &[ObservedRule],
    vocabulary: &EventVocabulary,
    program: Pattern,
    budget: ExecutionBudget,
) -> Run {
    let manifest = validator
        .observation_manifest(side, rules)
        .expect("manifest installs");
    let selected_rules = manifest.rules().cloned().collect();
    let mut backend = backend(&side.artifacts().definition_kore, fixture.module());
    let state = support::initial_state(program, "SortProg");
    let execution = adapter(manifest)
        .execute(&mut backend, &state, budget)
        .expect("execution adapts");
    let sorts = SymbolSorts::from_definition(
        &parse_definition(&side.artifacts().definition_kore).expect("compiled KORE parses"),
    );
    let normal = |_: &Pattern| ExecutionTerminalKind::Normal;
    let bridged = paths_from_execution(
        &execution,
        &BridgeContext {
            test_id: "symbolic",
            classify: &normal,
            sorts: &sorts,
        },
    )
    .expect("execution bridges");
    Run {
        execution,
        bridged,
        context: EvaluationContext {
            test_id: "symbolic".into(),
            bounds: budget.bounds(),
            vocabulary: vocabulary.clone(),
            selected_rules,
            symbol_sorts: sorts,
        },
        backend,
        state,
    }
}

fn run(fixture: Fixture, program: Pattern, budget: ExecutionBudget) -> (Run, EventVocabulary) {
    let validator = NativeValidator::bind(support::load(fixture.name()), CompileOptions::default());
    let side = validator.compile_baseline().expect("fixture compiles");
    let vocabulary = vocabulary(fixture);
    let rules = observations(fixture, &validator);
    (
        run_side(
            &validator,
            &side,
            fixture,
            &rules,
            &vocabulary,
            program,
            budget,
        ),
        vocabulary,
    )
}

fn leaf_multiset(leaves: Vec<BaselineLeaf>) -> BTreeMap<(String, HaltClass, u64), usize> {
    let mut counts = BTreeMap::new();
    for leaf in leaves {
        let state = serde_json::to_string(&leaf.state).expect("state JSON");
        *counts.entry((state, leaf.halt, leaf.depth)).or_insert(0) += 1;
    }
    counts
}

#[test]
fn observation_erasure_preserves_live_leaves() {
    let depth = ExecutionBudget {
        max_depth: Some(1),
        ..BUDGET
    };
    let breadth = ExecutionBudget {
        max_breadth: Some(NonZeroUsize::new(1).expect("nonzero")),
        ..BUDGET
    };
    let rows = [
        (
            "nd.k",
            "ND",
            "SortS",
            vec![
                ("start", support::app("Lblstart", vec![]), BUDGET),
                ("start-depth", support::app("Lblstart", vec![]), depth),
                ("start-breadth", support::app("Lblstart", vec![]), breadth),
            ],
        ),
        (
            "symmem.k",
            "SYMMEM",
            "SortProg",
            vec![
                ("P1", p1(), BUDGET),
                ("P2", p2(), BUDGET),
                ("P3", p3(), BUDGET),
                ("P4", p4(), BUDGET),
                ("P5", p5(), BUDGET),
                ("P6", p6(), BUDGET),
                ("P7", p7(), BUDGET),
                ("P8", p8(), depth),
                ("P9", p9(), breadth),
            ],
        ),
        (
            "guardedmem.k",
            "GUARDEDMEM",
            "SortProg",
            vec![
                ("G1", g1(), BUDGET),
                ("G2", g2(), BUDGET),
                ("G3", g3(), BUDGET),
            ],
        ),
    ];
    for (fixture, module, sort, programs) in rows {
        let validator = NativeValidator::bind(support::load(fixture), CompileOptions::default());
        let side = validator.compile_baseline().expect("fixture compiles");
        let rules = if fixture == "nd.k" {
            ["ND.left", "ND.right", "ND.l2", "ND.r2"]
                .into_iter()
                .map(|label| ObservedRule {
                    rule: support::rule(validator.baseline(), label),
                    emit_rule_applied: true,
                    domain_events: Vec::new(),
                })
                .collect()
        } else {
            observations(
                if fixture == "symmem.k" {
                    Fixture::Sym
                } else {
                    Fixture::Guard
                },
                &validator,
            )
        };
        let manifest = validator
            .observation_manifest(&side, &rules)
            .expect("manifest");
        let adapter = adapter(manifest);
        let mut backend = backend(&side.artifacts().definition_kore, module);
        for (row, program, budget) in programs {
            let state = support::initial_state(program, sort);
            let observed = adapter
                .execute(&mut backend, &state, budget)
                .expect("observed execution");
            assert!(!observed.timed_out(), "{fixture} {row}: observed timeout");
            let unobserved = adapter
                .execute_unobserved(&mut backend, &state, budget)
                .expect("unobserved execution");
            let observed = leaf_multiset(observed.erased());
            let unobserved = leaf_multiset(unobserved);
            assert!(!observed.is_empty(), "{fixture} {row}: no leaves");
            assert_eq!(observed, unobserved, "{fixture} {row}: observation erasure");
        }
    }
}

fn wl(vocabulary: &EventVocabulary, sort: &str, relation: Relation) -> PatternPlan {
    PatternPlan::new(
        vocabulary,
        vec![("A".into(), kore_sort(sort))],
        vec![PatternArm {
            atoms: vec![
                Atom {
                    constructor: "memoryWrite".into(),
                    payload: vec![PayloadClause {
                        position: 0,
                        mode: MatchMode::Bind,
                        variable: "A".into(),
                    }],
                },
                Atom {
                    constructor: "memoryLoad".into(),
                    payload: vec![PayloadClause {
                        position: 0,
                        mode: MatchMode::Use,
                        variable: "A".into(),
                    }],
                },
            ],
            relations: vec![relation],
        }],
        None,
    )
    .expect("plan")
}

fn wl_next(vocabulary: &EventVocabulary) -> PatternPlan {
    wl(vocabulary, "SortAddress", Relation::NextEvent)
}
fn wl_after(vocabulary: &EventVocabulary) -> PatternPlan {
    wl(vocabulary, "SortAddress", Relation::EventuallyAfter)
}
fn gwl_after(vocabulary: &EventVocabulary) -> PatternPlan {
    wl(vocabulary, "SortInt", Relation::EventuallyAfter)
}
fn w_only(vocabulary: &EventVocabulary) -> PatternPlan {
    PatternPlan::new(
        vocabulary,
        vec![("A".into(), kore_sort("SortAddress"))],
        vec![PatternArm {
            atoms: vec![Atom {
                constructor: "memoryWrite".into(),
                payload: vec![PayloadClause {
                    position: 0,
                    mode: MatchMode::Bind,
                    variable: "A".into(),
                }],
            }],
            relations: vec![],
        }],
        None,
    )
    .expect("plan")
}

fn outcome(run: &Run, plan: &PatternPlan) -> Evaluation {
    evaluate(
        &run.context,
        plan,
        &run.bridged.paths,
        &run.bridged.collection,
        None,
        EvaluationOptions {
            stable_path_keys: true,
            search_policy: SearchPolicy::Exhaustive,
            input_error: false,
        },
    )
    .expect("evaluation")
}

/// `outcome` with the backend's relation decider instead of the structural one.
fn decided(run: &mut Run, plan: &PatternPlan) -> Evaluation {
    with_backend_relations(&mut run.backend, &run.state, |relations| {
        evaluate_with(
            &run.context,
            plan,
            &run.bridged.paths,
            &run.bridged.collection,
            None,
            EvaluationOptions {
                stable_path_keys: true,
                search_policy: SearchPolicy::Exhaustive,
                input_error: false,
            },
            relations,
        )
    })
    .expect("backend definition")
    .expect("evaluation")
}

fn binding_names(fixture: Fixture, program: Pattern) -> Vec<(&'static str, Vec<String>)> {
    let validator = NativeValidator::bind(support::load(fixture.name()), CompileOptions::default());
    let side = validator.compile_baseline().expect("fixture compiles");
    let mut rules = observations(fixture, &validator);
    for rule in &mut rules {
        let count = if matches!(fixture, Fixture::Sym)
            && rule.domain_events[0].constructor == "memoryFree"
        {
            4
        } else {
            5
        };
        rule.domain_events[0].payload = (0..count).map(PayloadSource::BindingVariable).collect();
    }
    let manifest = validator
        .observation_manifest(&side, &rules)
        .expect("probe manifest");
    let mut backend = backend(&side.artifacts().definition_kore, fixture.module());
    let state = support::initial_state(program, "SortProg");
    let execution = adapter(manifest)
        .execute(&mut backend, &state, BUDGET)
        .expect("probe execution");
    execution
        .leaves()
        .iter()
        .flat_map(|leaf| leaf.branch.events.iter())
        .filter_map(|event| {
            let NativeEvent::Domain(domain) = event else {
                return None;
            };
            let ordinal = rules
                .iter()
                .position(|rule| rule.rule == domain.rule)
                .expect("observed rule");
            let names = domain
                .payload
                .iter()
                .map(|payload| {
                    let DomainPayload::Term(value) = payload else {
                        panic!("variable term payload")
                    };
                    let pattern = codec::from_value(value).expect("variable KORE");
                    let Pattern::Variable(variable) = &pattern else {
                        panic!("binding key is not a variable: {pattern:?}")
                    };
                    variable.name.clone()
                })
                .collect();
            Some((fixture.labels()[ordinal], names))
        })
        .collect()
}

#[test]
fn observed_binding_indices_follow_variable_names() {
    let sym = binding_names(Fixture::Sym, p2());
    assert_eq!(sym.len(), 3);
    let name_rows: Vec<_> = sym
        .iter()
        .map(|(label, names)| (*label, names.iter().map(String::as_str).collect::<Vec<_>>()))
        .collect();
    assert_eq!(
        name_rows,
        vec![
            (
                "SYMMEM.write",
                vec![
                    "RuleVarA",
                    "RuleVar'Unds'DotVar0",
                    "RuleVar'Unds'DotVar1",
                    "RuleVarV",
                    "RuleVarP"
                ]
            ),
            (
                "SYMMEM.free",
                vec![
                    "RuleVarA",
                    "RuleVar'Unds'DotVar0",
                    "RuleVar'Unds'DotVar1",
                    "RuleVarP"
                ]
            ),
            (
                "SYMMEM.load",
                vec![
                    "RuleVarA",
                    "RuleVar'Unds'DotVar0",
                    "RuleVar'Unds'DotVar1",
                    "RuleVarV",
                    "RuleVarP"
                ]
            ),
        ]
    );
    let guard = binding_names(Fixture::Guard, g3());
    let neg = binding_names(
        Fixture::Guard,
        seq(load_neg(addr(support::int(-1)), integer("W")), halt()),
    );
    assert_eq!(guard.len(), 2);
    assert_eq!(neg.len(), 1);
    let labels: Vec<_> = guard.iter().chain(&neg).map(|(label, _)| *label).collect();
    assert_eq!(
        labels,
        ["GUARDEDMEM.write", "GUARDEDMEM.load", "GUARDEDMEM.loadNeg"]
    );
    for (_, names) in guard.iter().chain(&neg) {
        assert_eq!(
            names.iter().map(String::as_str).collect::<Vec<_>>(),
            vec![
                "RuleVar'Unds'DotVar0",
                "RuleVarA",
                "RuleVarV",
                "RuleVar'Unds'DotVar1",
                "RuleVarP"
            ]
        );
    }
}

#[test]
fn symmem_binding_payloads_are_subject_terms() {
    let (run, _) = run(Fixture::Sym, p1(), BUDGET);
    assert_eq!(run.bridged.collection.stop, CollectionStop::SearchExhausted);
    let [path] = run.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert!(path.complete);
    assert_eq!(
        path.execution_terminal.as_ref().expect("terminal").state,
        support::initial_state(halt(), "SortProg")
    );
    assert_eq!(path.events.len(), 2);
    assert_eq!(path.events[0].constructor, "memoryWrite");
    assert_eq!(path.events[1].constructor, "memoryLoad");
    assert_eq!(path.events[0].payload, [addr(nat("X")), nat("V")]);
    assert_eq!(path.events[1].payload, [addr(nat("X")), nat("W")]);
}

#[test]
fn symmem_fork_keeps_siblings_apart() {
    let (run, _) = run(Fixture::Sym, p4(), BUDGET);
    assert_eq!(run.bridged.collection.stop, CollectionStop::SearchExhausted);
    let [left, right] = run.bridged.paths.as_slice() else {
        panic!("two paths")
    };
    assert!(left.complete && right.complete);
    assert_ne!(left.path_key, right.path_key);
    let constructors: Vec<_> = run
        .bridged
        .paths
        .iter()
        .map(|path| {
            path.events
                .iter()
                .map(|event| event.constructor.as_str())
                .collect::<Vec<_>>()
        })
        .collect();
    assert!(constructors.contains(&vec!["memoryWrite"]));
    assert!(constructors.contains(&vec!["memoryLoad"]));
}

/// No-Z3 only: the Z3 build's G1/G2 values are rows of `profile_table_rows`.
#[cfg(not(feature = "z3"))]
#[test]
fn solver_dependent_guard_is_unknown_without_z3() {
    let validator = NativeValidator::bind(support::load("guardedmem.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("fixture compiles");
    let backend = backend(&side.artifacts().definition_kore, "GUARDEDMEM");
    assert!(!backend.capabilities().smt);
    for program in [g1(), g2()] {
        let (run, vocabulary) = run(Fixture::Guard, program, BUDGET);
        assert_eq!(
            run.execution
                .leaves()
                .iter()
                .map(|leaf| leaf.halt)
                .collect::<Vec<_>>(),
            [HaltClass::Indeterminate]
        );
        assert!(
            run.bridged
                .paths
                .iter()
                .any(|path| path.stop == PathStop::BackendLimit)
        );
        let evaluation = outcome(&run, &gwl_after(&vocabulary));
        assert_eq!(evaluation.outcome, PatternOutcome::Unknown);
        assert_eq!(evaluation.failure, Some(PathStop::BackendLimit));
    }
}

#[test]
fn ground_guard_is_decided_without_z3() {
    let (run, vocabulary) = run(Fixture::Guard, g3(), BUDGET);
    assert_eq!(
        run.execution
            .leaves()
            .iter()
            .map(|leaf| leaf.halt)
            .collect::<Vec<_>>(),
        [HaltClass::Stuck]
    );
    assert_eq!(run.bridged.collection.stop, CollectionStop::SearchExhausted);
    let [path] = run.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert!(path.complete);
    assert_eq!(
        outcome(&run, &gwl_after(&vocabulary)).outcome,
        PatternOutcome::Match
    );
}

fn assert_both(
    run: &mut Run,
    plan: &PatternPlan,
    expected: PatternOutcome,
    failure: Option<PathStop>,
) -> Evaluation {
    let plain = outcome(run, plan);
    assert_eq!((plain.outcome, plain.failure), (expected, failure));
    let evaluation = decided(run, plan);
    assert_eq!(
        (evaluation.outcome, evaluation.failure),
        (expected, failure)
    );
    assert_witness_paths(run, &evaluation);
    for witness in &evaluation.witnesses {
        assert_eq!(witness.bindings.len(), 1);
        assert_eq!(witness.bindings[0].name, "A");
        assert_eq!(witness.bindings[0].term, addr(nat("X")));
        assert!(witness.assumptions.is_empty());
        assert_eq!(
            witness.path_predicate,
            Pattern::Top {
                sort: kore_sort("SortGeneratedTopCell")
            }
        );
    }
    evaluation
}

fn assert_witness_paths(run: &Run, evaluation: &Evaluation) {
    for witness in &evaluation.witnesses {
        let path = run
            .bridged
            .paths
            .iter()
            .find(|path| path.path_ordinal == witness.path_ordinal)
            .expect("witness path ordinal");
        assert!(path.path_key.is_some());
        assert_eq!(witness.path_key, path.path_key);
        assert!(path.stop.has_real_prefix());
        assert_eq!(witness.stop_reason, path.stop);
        assert_eq!(witness.path_predicate, path.path_predicate);
        assert_eq!(
            witness.events,
            witness
                .event_indices
                .iter()
                .map(|&index| path.events[index].clone())
                .collect::<Vec<_>>()
        );
    }
}

fn only_witness_path<'a>(run: &'a Run, evaluation: &Evaluation) -> &'a PathInput {
    let [witness] = evaluation.witnesses.as_slice() else {
        panic!("exactly one witness: {evaluation:?}")
    };
    run.bridged
        .paths
        .iter()
        .find(|path| path.path_ordinal == witness.path_ordinal)
        .expect("witness path")
}

#[test]
fn symbolic_write_then_load_matches_consecutive_and_separated() {
    let (mut first, vocabulary) = run(Fixture::Sym, p1(), BUDGET);
    for plan in [wl_next(&vocabulary), wl_after(&vocabulary)] {
        let evaluation = assert_both(&mut first, &plan, PatternOutcome::Match, None);
        assert_eq!(evaluation.witnesses.len(), 1);
        assert_eq!(evaluation.witnesses[0].event_indices, [0, 1]);
        assert_eq!(evaluation.witnesses[0].stop_reason, PathStop::Terminal);
    }

    let (mut separated, vocabulary) = run(Fixture::Sym, p2(), BUDGET);
    let evaluation = assert_both(
        &mut separated,
        &wl_next(&vocabulary),
        PatternOutcome::NoMatch,
        None,
    );
    assert!(evaluation.complete_coverage);
    assert!(evaluation.witnesses.is_empty());
    let evaluation = assert_both(
        &mut separated,
        &wl_after(&vocabulary),
        PatternOutcome::Match,
        None,
    );
    let path = only_witness_path(&separated, &evaluation);
    assert_eq!(evaluation.witnesses[0].event_indices, [0, 2]);
    assert_eq!(evaluation.witnesses[0].stop_reason, PathStop::Terminal);
    assert_eq!(path.events[1].constructor, "memoryFree");
}

#[test]
fn symbolic_reversed_order_does_not_match() {
    let (mut run, vocabulary) = run(Fixture::Sym, p3(), BUDGET);
    let evaluation = assert_both(
        &mut run,
        &wl_after(&vocabulary),
        PatternOutcome::NoMatch,
        None,
    );
    assert!(evaluation.complete_coverage);
    assert!(evaluation.witnesses.is_empty());
    let [path] = run.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert_eq!(path.stop, PathStop::Terminal);
    assert_eq!(path.events[0].constructor, "memoryLoad");
    assert_eq!(path.events[1].constructor, "memoryWrite");
}

#[test]
fn sibling_write_and_load_never_form_a_witness() {
    let (mut run, vocabulary) = run(Fixture::Sym, p4(), BUDGET);
    let evaluation = assert_both(
        &mut run,
        &wl_after(&vocabulary),
        PatternOutcome::NoMatch,
        None,
    );
    assert!(evaluation.complete_coverage);
    assert!(evaluation.witnesses.is_empty());
    assert_eq!(run.bridged.paths.len(), 2);
    assert!(
        run.bridged
            .paths
            .iter()
            .all(|path| path.complete && path.stop == PathStop::Terminal && path.events.len() == 1)
    );
    assert_ne!(run.bridged.paths[0].path_key, run.bridged.paths[1].path_key);
}

#[test]
fn witness_stays_on_its_own_sibling() {
    let (mut run, vocabulary) = run(Fixture::Sym, p5(), BUDGET);
    let evaluation = assert_both(
        &mut run,
        &wl_after(&vocabulary),
        PatternOutcome::Match,
        None,
    );
    let path = only_witness_path(&run, &evaluation);
    assert_eq!(evaluation.witnesses[0].event_indices, [0, 1]);
    assert_eq!(
        path.events
            .iter()
            .map(|event| event.constructor.as_str())
            .collect::<Vec<_>>(),
        ["memoryWrite", "memoryLoad"]
    );
    assert_eq!(path.stop, PathStop::Terminal);
    assert_eq!(run.bridged.paths.len(), 2);
    let other = run
        .bridged
        .paths
        .iter()
        .find(|other| other.path_key != path.path_key)
        .expect("other sibling");
    assert_eq!(other.stop, PathStop::Terminal);
    assert_eq!(other.events.len(), 1);
    assert_eq!(other.events[0].constructor, "memoryLoad");
}

#[test]
fn shared_symbolic_address_binds_one_term() {
    let (mut run, vocabulary) = run(Fixture::Sym, p1(), BUDGET);
    let evaluation = assert_both(
        &mut run,
        &wl_after(&vocabulary),
        PatternOutcome::Match,
        None,
    );
    let path = only_witness_path(&run, &evaluation);
    let witness = &evaluation.witnesses[0];
    assert_eq!(witness.bindings.len(), 1);
    assert_eq!(witness.bindings[0].name, "A");
    assert_eq!(witness.bindings[0].term, addr(nat("X")));
    assert!(witness.assumptions.is_empty());
    assert_eq!(
        witness.path_predicate,
        Pattern::Top {
            sort: kore_sort("SortGeneratedTopCell")
        }
    );
    assert_eq!(path.stop, PathStop::Terminal);
}

#[test]
fn distinct_symbolic_addresses_match_under_unifier_assumption() {
    let (mut run, vocabulary) = run(Fixture::Sym, p6(), BUDGET);
    let plan = wl_after(&vocabulary);
    let plain = outcome(&run, &plan);
    assert_eq!(
        (plain.outcome, plain.failure),
        (PatternOutcome::Unknown, Some(PathStop::SolverUnknown))
    );
    let evaluation = decided(&mut run, &plan);
    // Z3 column provisional (SYM-3B-03): with a solver present `BackendRelations` withholds
    // the solver-free `Sat` for `X = Y` and does not yet trust a solver `Sat` (README 4.2, R9).
    let expected = by_profile(
        (PatternOutcome::Match, None),
        (PatternOutcome::Unknown, Some(PathStop::SolverUnknown)),
    );
    assert_eq!((evaluation.outcome, evaluation.failure), expected);
    assert_witness_paths(&run, &evaluation);
    if PROFILE == SolverProfile::Z3 {
        assert!(evaluation.witnesses.is_empty());
        return;
    }
    let path = only_witness_path(&run, &evaluation);
    let witness = &evaluation.witnesses[0];
    assert_eq!(witness.event_indices, [0, 1]);
    assert_eq!(witness.bindings.len(), 1);
    assert_eq!(witness.bindings[0].name, "A");
    assert_eq!(witness.bindings[0].term, addr(nat("X")));
    assert_eq!(
        witness.assumptions,
        [TermRelation {
            left: nat("X"),
            right: nat("Y")
        }]
    );
    assert_eq!(
        witness.path_predicate,
        Pattern::Top {
            sort: kore_sort("SortGeneratedTopCell")
        }
    );
    assert_eq!(path.stop, PathStop::Terminal);
}

#[test]
fn clashing_symbolic_addresses_do_not_match() {
    let (mut run, vocabulary) = run(Fixture::Sym, p7(), BUDGET);
    let plan = wl_after(&vocabulary);
    let plain = outcome(&run, &plan);
    assert_eq!(
        (plain.outcome, plain.failure),
        (PatternOutcome::Unknown, Some(PathStop::SolverUnknown))
    );
    let evaluation = decided(&mut run, &plan);
    assert_eq!(
        (evaluation.outcome, evaluation.failure),
        (PatternOutcome::NoMatch, None)
    );
    assert!(evaluation.complete_coverage);
    assert!(evaluation.witnesses.is_empty());
    let [path] = run.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert_eq!(path.stop, PathStop::Terminal);
}

#[test]
fn symbolic_depth_bound_absence_is_unknown_depth_limit() {
    let (mut run, vocabulary) = run(
        Fixture::Sym,
        p8(),
        ExecutionBudget {
            max_depth: Some(1),
            ..BUDGET
        },
    );
    let [leaf] = run.execution.leaves() else {
        panic!("one leaf")
    };
    assert_eq!(
        (leaf.halt, leaf.feasibility),
        (HaltClass::DepthBound, LeafFeasibility::Syntactic)
    );
    let evaluation = assert_both(
        &mut run,
        &wl_after(&vocabulary),
        PatternOutcome::Unknown,
        Some(PathStop::DepthLimit),
    );
    assert!(evaluation.witnesses.is_empty());
    assert_eq!(run.bridged.paths[0].stop, PathStop::DepthLimit);
}

#[test]
fn depth_cut_prefix_still_witnesses() {
    let (mut run, vocabulary) = run(
        Fixture::Sym,
        p8(),
        ExecutionBudget {
            max_depth: Some(1),
            ..BUDGET
        },
    );
    let evaluation = assert_both(&mut run, &w_only(&vocabulary), PatternOutcome::Match, None);
    let path = only_witness_path(&run, &evaluation);
    assert_eq!(evaluation.witnesses[0].event_indices, [0]);
    assert_eq!(evaluation.witnesses[0].stop_reason, PathStop::DepthLimit);
    assert_eq!(path.stop, PathStop::DepthLimit);
    assert!(!path.complete);
}

#[test]
fn breadth_bound_absence_is_unknown_branch_limit() {
    let (mut run, vocabulary) = run(
        Fixture::Sym,
        p9(),
        ExecutionBudget {
            max_breadth: Some(NonZeroUsize::new(1).expect("nonzero")),
            ..BUDGET
        },
    );
    assert_eq!(run.execution.leaves().len(), 2);
    assert!(
        run.execution
            .leaves()
            .iter()
            .all(|leaf| (leaf.halt, leaf.feasibility)
                == (HaltClass::BreadthBound, LeafFeasibility::Syntactic)
                && leaf.branch.events.is_empty())
    );
    let evaluation = assert_both(
        &mut run,
        &wl_after(&vocabulary),
        PatternOutcome::Unknown,
        Some(PathStop::BranchLimit),
    );
    assert!(evaluation.witnesses.is_empty());
    assert_eq!(run.bridged.paths.len(), 2);
    assert!(
        run.bridged
            .paths
            .iter()
            .all(|path| path.stop == PathStop::BranchLimit
                && !path.complete
                && path.events.is_empty())
    );
}

// Report runs use the same program/plan rows as README section 6.1 and 6.2.
// Leave ample watchdog time so a collection stop is determined by the fixture.
const REPORT_BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(120),
    ..BUDGET
};

#[derive(Clone, Copy)]
struct ReportRow {
    id: &'static str,
    fixture: Fixture,
    program: fn() -> Pattern,
    plan: fn(&EventVocabulary) -> PatternPlan,
    budget: ExecutionBudget,
}

fn report_rows() -> [ReportRow; 15] {
    let depth = ExecutionBudget {
        max_depth: Some(1),
        ..REPORT_BUDGET
    };
    let breadth = ExecutionBudget {
        max_breadth: Some(NonZeroUsize::new(1).expect("nonzero")),
        ..REPORT_BUDGET
    };
    let row = |id, fixture, program, plan, budget| ReportRow {
        id,
        fixture,
        program,
        plan,
        budget,
    };
    [
        row("P1-WL-next", Fixture::Sym, p1, wl_next, REPORT_BUDGET),
        row("P1-WL-after", Fixture::Sym, p1, wl_after, REPORT_BUDGET),
        row("P2-WL-next", Fixture::Sym, p2, wl_next, REPORT_BUDGET),
        row("P2-WL-after", Fixture::Sym, p2, wl_after, REPORT_BUDGET),
        row("P3-WL-after", Fixture::Sym, p3, wl_after, REPORT_BUDGET),
        row("P4-WL-after", Fixture::Sym, p4, wl_after, REPORT_BUDGET),
        row("P5-WL-after", Fixture::Sym, p5, wl_after, REPORT_BUDGET),
        row("P6-WL-after", Fixture::Sym, p6, wl_after, REPORT_BUDGET),
        row("P7-WL-after", Fixture::Sym, p7, wl_after, REPORT_BUDGET),
        row("P8-WL-after", Fixture::Sym, p8, wl_after, depth),
        row("P8-W-only", Fixture::Sym, p8, w_only, depth),
        row("P9-WL-after", Fixture::Sym, p9, wl_after, breadth),
        row("G1-GWL-after", Fixture::Guard, g1, gwl_after, REPORT_BUDGET),
        row("G2-GWL-after", Fixture::Guard, g2, gwl_after, REPORT_BUDGET),
        row("G3-GWL-after", Fixture::Guard, g3, gwl_after, REPORT_BUDGET),
    ]
}

fn report_on_backend(
    row: ReportRow,
    validator: &NativeValidator,
    side: &ValidatedDefinition,
    backend: &mut Backend,
) -> String {
    // Rebuild the manifest even when the Backend is reused.
    let rules = observations(row.fixture, validator);
    let manifest = validator
        .observation_manifest(side, &rules)
        .expect("fresh manifest");
    let selected_rules = manifest.rules().cloned().collect();
    let vocabulary = vocabulary(row.fixture);
    let plan = (row.plan)(&vocabulary);
    let state = support::initial_state((row.program)(), "SortProg");
    let execution = adapter(manifest)
        .execute(backend, &state, row.budget)
        .expect("execution adapts");
    assert!(!execution.timed_out(), "{}: watchdog timed out", row.id);
    let sorts = SymbolSorts::from_definition(
        &parse_definition(&side.artifacts().definition_kore).expect("compiled KORE parses"),
    );
    let normal = |_: &Pattern| ExecutionTerminalKind::Normal;
    let bridged = paths_from_execution(
        &execution,
        &BridgeContext {
            test_id: row.id,
            classify: &normal,
            sorts: &sorts,
        },
    )
    .expect("execution bridges");
    assert_ne!(
        bridged.collection.stop,
        CollectionStop::TimeLimit,
        "{}: collection reached time limit",
        row.id
    );
    let context = EvaluationContext {
        test_id: row.id.into(),
        bounds: row.budget.bounds(),
        vocabulary,
        selected_rules,
        symbol_sorts: sorts,
    };
    let evaluation = with_backend_relations(backend, &state, |relations| {
        evaluate_with(
            &context,
            &plan,
            &bridged.paths,
            &bridged.collection,
            None,
            EvaluationOptions {
                stable_path_keys: true,
                search_policy: SearchPolicy::Exhaustive,
                input_error: false,
            },
            relations,
        )
    })
    .expect("backend definition")
    .expect("evaluation");
    let report = step3_report(ReportInput {
        profile: PROFILE,
        test_id: row.id,
        budget: &row.budget,
        backend_options: BACKEND_OPTIONS,
        result: ReportResult::Ok {
            execution: &execution,
            bridged: &bridged,
            evaluation: &evaluation,
        },
    });
    serde_json::to_string(&report).expect("report JSON")
}

fn fresh_report(row: ReportRow, validator: &NativeValidator, side: &ValidatedDefinition) -> String {
    let mut backend = backend(&side.artifacts().definition_kore, row.fixture.module());
    report_on_backend(row, validator, side, &mut backend)
}

fn assert_identical_reports(row: ReportRow, baseline: &str, candidate: &str) {
    if baseline == candidate {
        return;
    }
    let baseline: serde_json::Value = serde_json::from_str(baseline).expect("baseline JSON");
    let candidate: serde_json::Value = serde_json::from_str(candidate).expect("candidate JSON");
    fn differences(
        path: &str,
        left: &serde_json::Value,
        right: &serde_json::Value,
        output: &mut Vec<String>,
    ) {
        match (left, right) {
            (serde_json::Value::Object(left), serde_json::Value::Object(right)) => {
                for key in left.keys().chain(right.keys()) {
                    let child = format!("{path}/{key}");
                    match (left.get(key), right.get(key)) {
                        (Some(a), Some(b)) => differences(&child, a, b, output),
                        (a, b) => output.push(format!("{child}: {a:?} != {b:?}")),
                    }
                }
            }
            (serde_json::Value::Array(left), serde_json::Value::Array(right)) => {
                for index in 0..left.len().max(right.len()) {
                    let child = format!("{path}/{index}");
                    match (left.get(index), right.get(index)) {
                        (Some(a), Some(b)) => differences(&child, a, b, output),
                        (a, b) => output.push(format!("{child}: {a:?} != {b:?}")),
                    }
                }
            }
            (a, b) if a != b => output.push(format!("{path}: {a} != {b}")),
            _ => {}
        }
    }
    let mut paths = Vec::new();
    differences("$", &baseline, &candidate, &mut paths);
    panic!(
        "{}: report bytes differ; JSON differences: {paths:?}",
        row.id
    );
}

#[test]
fn repeated_symbolic_runs_emit_identical_reports() {
    for fixture in [Fixture::Sym, Fixture::Guard] {
        let validator =
            NativeValidator::bind(support::load(fixture.name()), CompileOptions::default());
        let side = validator.compile_baseline().expect("fixture compiles");
        for row in report_rows()
            .into_iter()
            .filter(|row| row.fixture == fixture)
        {
            let baseline = fresh_report(row, &validator, &side);
            for _ in 1..3 {
                let candidate = fresh_report(row, &validator, &side);
                assert_identical_reports(row, &baseline, &candidate);
            }
        }
    }
}

#[test]
fn report_is_stable_across_backend_reuse() {
    let row = report_rows()
        .into_iter()
        .find(|row| row.id == "P5-WL-after")
        .expect("branching report row");
    let validator =
        NativeValidator::bind(support::load(row.fixture.name()), CompileOptions::default());
    let side = validator.compile_baseline().expect("fixture compiles");
    let fresh = fresh_report(row, &validator, &side);
    let mut backend = backend(&side.artifacts().definition_kore, row.fixture.module());
    let first = report_on_backend(row, &validator, &side, &mut backend);
    let second = report_on_backend(row, &validator, &side, &mut backend);
    assert_identical_reports(row, &fresh, &first);
    assert_identical_reports(row, &first, &second);
}

fn wrap(value: Pattern) -> Pattern {
    support::app("Lblwrap", vec![value])
}

/// Audit (SYM-3A-09): an `anywhere` equation makes `wrap` non-injective, although k-rust's
/// kompile still marks it `injective` and the unifier decomposes it. `wrap(s(X))` against
/// `wrap(z)` is equal for `X = z`, so the backend decider must not call them unequal, and the
/// write/load pair must not be `no-match`.
#[test]
fn non_free_injective_symbol_does_not_prove_a_clash() {
    let program = |address: Pattern| {
        seq(
            write(wrap(address), nat("V")),
            seq(load(wrap(z()), nat("W")), halt()),
        )
    };
    // The ground instance X = z is a match: the backend collapses the written address.
    let (mut ground, vocabulary) = run(Fixture::Wrap, program(s(z())), BUDGET);
    let plan = wl_after(&vocabulary);
    assert_eq!(decided(&mut ground, &plan).outcome, PatternOutcome::Match);
    let (mut symbolic, vocabulary) = run(Fixture::Wrap, program(s(nat("X"))), BUDGET);
    let plan = wl_after(&vocabulary);
    let [path] = symbolic.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert!(path.complete, "{path:?}");
    assert_eq!(
        symbolic.bridged.collection.stop,
        CollectionStop::SearchExhausted
    );
    assert_eq!(path.events[0].payload[0], wrap(s(nat("X"))));
    assert_eq!(path.events[1].payload[0], wrap(z()));
    // A clash below the free `addr` constructor (P7) is still proved.
    let (mut free, free_vocabulary) = run(Fixture::Sym, p7(), BUDGET);
    assert_eq!(
        decided(&mut free, &wl_after(&free_vocabulary)).outcome,
        PatternOutcome::NoMatch
    );
    let evaluation = decided(&mut symbolic, &plan);
    assert_eq!(
        evaluation.outcome,
        PatternOutcome::Unknown,
        "{evaluation:?}"
    );
    assert!(evaluation.witnesses.is_empty());
    assert_eq!(outcome(&symbolic, &plan).outcome, PatternOutcome::Unknown);
}

/// Audit (SYM-3A-09): leaf feasibility and the solver-free `Sat` assume every valuation of the
/// initial variables follows a clean no-Z3 path. `other` is `owise` below rules that cover
/// every `Nat`, so no value reaches the write/load events behind it; a symbolic subject must
/// not take `other` as if the higher-priority rules were refuted.
#[test]
fn owise_rule_is_not_taken_for_a_symbolic_subject() {
    let program = |selector: Pattern| {
        support::app(
            "Lblpick",
            vec![
                selector,
                seq(
                    write(addr(z()), nat("V")),
                    seq(load(addr(z()), nat("W")), halt()),
                ),
            ],
        )
    };
    for ground in [z(), s(z())] {
        let (mut run, vocabulary) = run(Fixture::Owise, program(ground), BUDGET);
        assert_eq!(
            decided(&mut run, &wl_after(&vocabulary)).outcome,
            PatternOutcome::NoMatch
        );
    }
    let (mut symbolic, vocabulary) = run(Fixture::Owise, program(nat("X")), BUDGET);
    // No-Z3: matching `z` or `s(_)` against `X` needs a narrowing condition, which `NoSolver`
    // cannot accept, so the priority group is undecided and the one leaf is `Indeterminate`.
    // Z3: narrowing is accepted; `zero` and `succ` each give a `Stuck` leaf whose predicate
    // keeps its narrowing condition (`X = z`, `X = s(_)`), and `other` is still not taken. The
    // Z3 column (constrained symbolic `Stuck` is `SolverUnknown`) is provisional: SYM-3B-02.
    let stops: Vec<_> = symbolic
        .bridged
        .paths
        .iter()
        .map(|path| path.stop)
        .collect();
    assert_eq!(
        stops,
        by_profile(
            vec![PathStop::BackendLimit],
            vec![PathStop::SolverUnknown, PathStop::SolverUnknown]
        )
    );
    for path in &symbolic.bridged.paths {
        assert!(path.events.is_empty(), "{path:?}");
        if PROFILE == SolverProfile::Z3 {
            assert!(!matches!(path.path_predicate, Pattern::Top { .. }));
        }
    }
    let failure = by_profile(PathStop::BackendLimit, PathStop::SolverUnknown);
    let plan = wl_after(&vocabulary);
    for evaluation in [decided(&mut symbolic, &plan), outcome(&symbolic, &plan)] {
        assert_eq!(
            evaluation.outcome,
            PatternOutcome::Unknown,
            "{evaluation:?}"
        );
        assert_eq!(evaluation.failure, Some(failure));
    }
}

/// Section 9 "an observer whose selector cardinality changes fails before execution", on the
/// symmem observer: the label selections install a manifest; a selection whose expected
/// cardinality no longer matches the definition publishes no rule, so no execution can start.
#[test]
fn symmem_manifest_rejects_wrong_cardinality() {
    let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("fixture compiles");
    let module = support::rule(validator.baseline(), "SYMMEM.write").module;
    let classification =
        RewriteRules::classify(&validator, &side, &module).expect("rewrite classification");
    let selection = |selector: RuleSelector, expected_cardinality: usize| RuleSelection {
        selector,
        expected_cardinality,
        emit_rule_applied: true,
        domain_events: Vec::new(),
    };
    let label = |name: &str| RuleSelector::Label(name.to_owned());
    let select = |selections: &[RuleSelection]| {
        select_rules(validator.baseline(), Some(&classification), selections)
    };
    let observer = [
        selection(label("SYMMEM.write"), 1),
        selection(label("SYMMEM.load"), 1),
        selection(label("SYMMEM.free"), 1),
    ];
    let rules = select(&observer).expect("the symmem observer selects its rules");
    assert_eq!(rules.len(), 3);
    validator
        .observation_manifest(&side, &rules)
        .expect("manifest installs");
    // write, load, free, left and right are the five transitions.
    assert_eq!(
        select(&[selection(RuleSelector::AllTransitions, 5)]).map(|rules| rules.len()),
        Ok(5)
    );
    let mismatch = |selection, expected, actual| SelectionFailure::CardinalityMismatch {
        selection,
        expected,
        actual,
    };
    let rows = [
        (
            "all-transitions-expected-four",
            vec![selection(RuleSelector::AllTransitions, 4)],
            mismatch(0, 4, 5),
        ),
        (
            "missing-label",
            vec![
                selection(label("SYMMEM.write"), 1),
                selection(label("SYMMEM.store"), 1),
            ],
            mismatch(1, 1, 0),
        ),
        (
            "label-expected-twice",
            vec![selection(label("SYMMEM.load"), 2)],
            mismatch(0, 2, 1),
        ),
    ];
    for (id, selections, failure) in rows {
        assert_eq!(select(&selections), Err(failure), "{id}");
    }
}

/// Audit (SYM-3A-09): the solver-free `Sat` for witness assumptions needs the path predicate
/// to be exactly `\top`. `pin` pins `X = z` and `Y = s(z)` after the write/load events, so
/// `X = Y` is infeasible on the path; k-rust keeps both equations in the leaf predicate rather
/// than substituting them away, so the leaf is `SolverUnknown` and the result stays `unknown`.
#[test]
fn ensures_constraint_keeps_a_later_witness_unknown() {
    let program = seq(
        write(addr(nat("X")), nat("V")),
        seq(
            load(addr(nat("Y")), nat("W")),
            support::app("Lblpin", vec![nat("X"), nat("Y"), halt()]),
        ),
    );
    let (mut run, vocabulary) = run(Fixture::Ensures, program, BUDGET);
    let [path] = run.bridged.paths.as_slice() else {
        panic!("one path")
    };
    assert_eq!(path.stop, PathStop::SolverUnknown);
    assert!(!matches!(path.path_predicate, Pattern::Top { .. }));
    let evaluation = decided(&mut run, &wl_after(&vocabulary));
    assert_eq!(
        (evaluation.outcome, evaluation.failure),
        (PatternOutcome::Unknown, Some(PathStop::SolverUnknown))
    );
}

/// `symwrap.k`: write to `wrap(s(X))`, load from `wrap(z)`.
fn wrap_program() -> Pattern {
    seq(
        write(wrap(s(nat("X"))), nat("V")),
        seq(load(wrap(z()), nat("W")), halt()),
    )
}
/// `symowise.k`: a symbolic selector in front of a ground write/load pair.
fn owise_program() -> Pattern {
    support::app(
        "Lblpick",
        vec![
            nat("X"),
            seq(
                write(addr(z()), nat("V")),
                seq(load(addr(z()), nat("W")), halt()),
            ),
        ],
    )
}
/// `symensures.k`: `pin` constrains `X` and `Y` after the write/load pair.
fn ensures_program() -> Pattern {
    seq(
        write(addr(nat("X")), nat("V")),
        seq(
            load(addr(nat("Y")), nat("W")),
            support::app("Lblpin", vec![nat("X"), nat("Y"), halt()]),
        ),
    )
}

/// An expected status: outcome and, for `unknown`, its failure.
type Status = (PatternOutcome, Option<PathStop>);

/// One profile-table row: README 6.1, 6.2 and 6.3 programs with `(no_z3, z3)` columns for the
/// bridged path stops (in path order), plain `evaluate`, and `evaluate_with(BackendRelations)`.
struct ProfileRow {
    id: &'static str,
    fixture: Fixture,
    program: fn() -> Pattern,
    plan: fn(&EventVocabulary) -> PatternPlan,
    budget: ExecutionBudget,
    stops: (&'static [PathStop], &'static [PathStop]),
    structural: (Status, Status),
    decided: (Status, Status),
}

/// Every symbolic row in both profiles. A Z3 cell that differs from its no-Z3 cell is what the
/// SYM-3B-01 code produces and is provisional: SYM-3B-02 decides Z3 stop semantics
/// (constrained or symbolic `Stuck`, `Vacuous`, `Trivial`), SYM-3B-03 when a solver `Sat`
/// counts, and SYM-3B-04 fills G1/G2 from README 6.2 (target: G1 match, G2 no-match).
#[test]
fn profile_table_rows() {
    use PathStop::{BackendLimit, BranchLimit, DepthLimit, SolverUnknown, Terminal};
    use PatternOutcome::{Match, NoMatch, Unknown};
    let depth = ExecutionBudget {
        max_depth: Some(1),
        ..BUDGET
    };
    let breadth = ExecutionBudget {
        max_breadth: Some(NonZeroUsize::new(1).expect("nonzero")),
        ..BUDGET
    };
    let same = |status: Status| (status, status);
    let matched = same((Match, None));
    let absent = same((NoMatch, None));
    let rows = [
        ProfileRow {
            id: "P1-WL-next",
            fixture: Fixture::Sym,
            program: p1,
            plan: wl_next,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: matched,
            decided: matched,
        },
        ProfileRow {
            id: "P1-WL-after",
            fixture: Fixture::Sym,
            program: p1,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: matched,
            decided: matched,
        },
        ProfileRow {
            id: "P2-WL-next",
            fixture: Fixture::Sym,
            program: p2,
            plan: wl_next,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: absent,
            decided: absent,
        },
        ProfileRow {
            id: "P2-WL-after",
            fixture: Fixture::Sym,
            program: p2,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: matched,
            decided: matched,
        },
        ProfileRow {
            id: "P3-WL-after",
            fixture: Fixture::Sym,
            program: p3,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: absent,
            decided: absent,
        },
        ProfileRow {
            id: "P4-WL-after",
            fixture: Fixture::Sym,
            program: p4,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal, Terminal], &[Terminal, Terminal]),
            structural: absent,
            decided: absent,
        },
        ProfileRow {
            id: "P5-WL-after",
            fixture: Fixture::Sym,
            program: p5,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal, Terminal], &[Terminal, Terminal]),
            structural: matched,
            decided: matched,
        },
        ProfileRow {
            id: "P6-WL-after",
            fixture: Fixture::Sym,
            program: p6,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: same((Unknown, Some(SolverUnknown))),
            // Z3 provisional (SYM-3B-03): no `Sat` for `X = Y` while a solver is present.
            decided: ((Match, None), (Unknown, Some(SolverUnknown))),
        },
        ProfileRow {
            id: "P7-WL-after",
            fixture: Fixture::Sym,
            program: p7,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: same((Unknown, Some(SolverUnknown))),
            decided: absent,
        },
        ProfileRow {
            id: "P8-WL-after",
            fixture: Fixture::Sym,
            program: p8,
            plan: wl_after,
            budget: depth,
            stops: (&[DepthLimit], &[DepthLimit]),
            structural: same((Unknown, Some(DepthLimit))),
            decided: same((Unknown, Some(DepthLimit))),
        },
        ProfileRow {
            id: "P8-W-only",
            fixture: Fixture::Sym,
            program: p8,
            plan: w_only,
            budget: depth,
            stops: (&[DepthLimit], &[DepthLimit]),
            structural: matched,
            decided: matched,
        },
        ProfileRow {
            id: "P9-WL-after",
            fixture: Fixture::Sym,
            program: p9,
            plan: wl_after,
            budget: breadth,
            stops: (&[BranchLimit, BranchLimit], &[BranchLimit, BranchLimit]),
            structural: same((Unknown, Some(BranchLimit))),
            decided: same((Unknown, Some(BranchLimit))),
        },
        // G1/G2 Z3 provisional (SYM-3B-02): Z3 decides the `requires`, giving three
        // constrained ground `Stuck` leaves (halt, fault after the write, fault), all
        // `SolverUnknown` until constrained `Stuck` leaves are decided.
        ProfileRow {
            id: "G1-GWL-after",
            fixture: Fixture::Guard,
            program: g1,
            plan: gwl_after,
            budget: BUDGET,
            stops: (
                &[BackendLimit],
                &[SolverUnknown, SolverUnknown, SolverUnknown],
            ),
            structural: (
                (Unknown, Some(BackendLimit)),
                (Unknown, Some(SolverUnknown)),
            ),
            decided: (
                (Unknown, Some(BackendLimit)),
                (Unknown, Some(SolverUnknown)),
            ),
        },
        ProfileRow {
            id: "G2-GWL-after",
            fixture: Fixture::Guard,
            program: g2,
            plan: gwl_after,
            budget: BUDGET,
            stops: (
                &[BackendLimit],
                &[SolverUnknown, SolverUnknown, SolverUnknown],
            ),
            structural: (
                (Unknown, Some(BackendLimit)),
                (Unknown, Some(SolverUnknown)),
            ),
            decided: (
                (Unknown, Some(BackendLimit)),
                (Unknown, Some(SolverUnknown)),
            ),
        },
        ProfileRow {
            id: "G3-GWL-after",
            fixture: Fixture::Guard,
            program: g3,
            plan: gwl_after,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: matched,
            decided: matched,
        },
        ProfileRow {
            id: "symwrap-WL-after",
            fixture: Fixture::Wrap,
            program: wrap_program,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[Terminal], &[Terminal]),
            structural: same((Unknown, Some(SolverUnknown))),
            decided: same((Unknown, Some(SolverUnknown))),
        },
        // Z3 provisional (SYM-3B-02): narrowing gives two constrained symbolic `Stuck` leaves.
        ProfileRow {
            id: "symowise-WL-after",
            fixture: Fixture::Owise,
            program: owise_program,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[BackendLimit], &[SolverUnknown, SolverUnknown]),
            structural: (
                (Unknown, Some(BackendLimit)),
                (Unknown, Some(SolverUnknown)),
            ),
            decided: (
                (Unknown, Some(BackendLimit)),
                (Unknown, Some(SolverUnknown)),
            ),
        },
        ProfileRow {
            id: "symensures-WL-after",
            fixture: Fixture::Ensures,
            program: ensures_program,
            plan: wl_after,
            budget: BUDGET,
            stops: (&[SolverUnknown], &[SolverUnknown]),
            structural: same((Unknown, Some(SolverUnknown))),
            decided: same((Unknown, Some(SolverUnknown))),
        },
    ];
    let mut failures = Vec::new();
    for row in rows {
        let (mut run, vocabulary) = run(row.fixture, (row.program)(), row.budget);
        let plan = (row.plan)(&vocabulary);
        let stops: Vec<_> = run.bridged.paths.iter().map(|path| path.stop).collect();
        let plain = outcome(&run, &plan);
        let decided = decided(&mut run, &plan);
        assert_witness_paths(&run, &plain);
        assert_witness_paths(&run, &decided);
        let actual = (
            stops.as_slice(),
            (plain.outcome, plain.failure),
            (decided.outcome, decided.failure),
        );
        let expected = (
            by_profile(row.stops.0, row.stops.1),
            by_profile(row.structural.0, row.structural.1),
            by_profile(row.decided.0, row.decided.1),
        );
        if actual != expected {
            failures.push(format!(
                "{} ({}): expected {expected:?}, got {actual:?}",
                row.id,
                PROFILE.name()
            ));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}
