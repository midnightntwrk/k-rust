//! Live symbolic memory observations and path-level smoke checks.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::kore_sort;
use k_rust::kore::{ast::Pattern, codec, parser::parse_definition};
use kink_native::bridge::{BridgeContext, BridgedPaths, paths_from_execution};
use kink_native::execution::{AdaptedExecution, ExecutionAdapter, ExecutionBudget, HaltClass};
use kink_native::observation::{DomainEventSpec, DomainPayload, NativeEvent, PayloadSource};
use kink_native::{NativeValidator, ObservedRule, ValidatedDefinition};
use kink_pattern::{
    Atom, CollectionStop, Constructor, Evaluation, EvaluationContext, EvaluationOptions,
    EventVocabulary, ExecutionTerminalKind, MatchMode, PathStop, PatternArm, PatternOutcome,
    PatternPlan, PayloadClause, Relation, SearchPolicy, SymbolSorts, evaluate,
};

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
#[allow(dead_code)] // P7 is exercised by SYM-3A-05.
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
#[allow(dead_code)] // P3 is exercised by SYM-3A-05.
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
#[allow(dead_code)] // P5-P9 are exercised by SYM-3A-05 and SYM-3A-06.
fn p5() -> Pattern {
    fork(p1(), seq(load(addr(nat("X")), nat("W")), halt()))
}
#[allow(dead_code)]
fn p6() -> Pattern {
    seq(
        write(addr(nat("X")), nat("V")),
        seq(load(addr(nat("Y")), nat("W")), halt()),
    )
}
#[allow(dead_code)]
fn p7() -> Pattern {
    seq(
        write(addr(z()), nat("V")),
        seq(load(addr(s(nat("Y"))), nat("W")), halt()),
    )
}
#[allow(dead_code)]
fn p8() -> Pattern {
    p1()
}
#[allow(dead_code)]
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

#[derive(Clone, Copy)]
enum Fixture {
    Sym,
    Guard,
}

impl Fixture {
    fn name(self) -> &'static str {
        match self {
            Self::Sym => "symmem.k",
            Self::Guard => "guardedmem.k",
        }
    }
    fn module(self) -> &'static str {
        match self {
            Self::Sym => "SYMMEM",
            Self::Guard => "GUARDEDMEM",
        }
    }
    fn address_sort(self) -> &'static str {
        match self {
            Self::Sym => "SortAddress",
            Self::Guard => "SortInt",
        }
    }
    fn value_sort(self) -> &'static str {
        match self {
            Self::Sym => "SortNat",
            Self::Guard => "SortInt",
        }
    }
    fn labels(self) -> &'static [&'static str; 3] {
        match self {
            Self::Sym => &["SYMMEM.write", "SYMMEM.load", "SYMMEM.free"],
            Self::Guard => &["GUARDEDMEM.write", "GUARDEDMEM.load", "GUARDEDMEM.loadNeg"],
        }
    }
}

struct Run {
    execution: AdaptedExecution,
    bridged: BridgedPaths,
    context: EvaluationContext,
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
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        fixture.module(),
        BackendOptions::default(),
    )
    .expect("backend");
    let state = support::initial_state(program, "SortProg");
    let execution = ExecutionAdapter::new(manifest)
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

#[allow(dead_code)] // Symmem plans are used by SYM-3A-05.
fn wl_next(vocabulary: &EventVocabulary) -> PatternPlan {
    wl(vocabulary, "SortAddress", Relation::NextEvent)
}
#[allow(dead_code)]
fn wl_after(vocabulary: &EventVocabulary) -> PatternPlan {
    wl(vocabulary, "SortAddress", Relation::EventuallyAfter)
}
fn gwl_after(vocabulary: &EventVocabulary) -> PatternPlan {
    wl(vocabulary, "SortInt", Relation::EventuallyAfter)
}
#[allow(dead_code)]
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
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        fixture.module(),
        BackendOptions::default(),
    )
    .expect("backend");
    let state = support::initial_state(program, "SortProg");
    let execution = ExecutionAdapter::new(manifest)
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

#[test]
fn solver_dependent_guard_is_unknown_without_z3() {
    let validator = NativeValidator::bind(support::load("guardedmem.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("fixture compiles");
    let backend = Backend::new(
        &side.artifacts().definition_kore,
        "GUARDEDMEM",
        BackendOptions::default(),
    )
    .expect("backend");
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
