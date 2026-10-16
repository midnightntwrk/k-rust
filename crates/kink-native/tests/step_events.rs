//! State-defined events over complete generated configurations.

#[path = "../../../testdata/k/step_support.rs"]
mod step_support;
#[path = "../../../testdata/k/support.rs"]
mod support;

use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::definition::AttributeKey;
use k_rust::kast::{Sort as KastSort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::kore_sort;
use k_rust::kore::{ast::Pattern, parser::parse_definition};
use kink_native::bridge::{BridgeContext, BridgeFailure, paths_from_steps};
use kink_native::execution::{ExecutionAdapter, ExecutionBudget, SolverProfile, SteppedExecution};
use kink_native::feasibility::{BackendRelations, TestInitialState};
use kink_native::step_events::{
    ObservationDecider, StepEventSpec, StepObservation, StepObservationError, StepPresence,
};
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_patch::{Edit, InsertPosition, Patch, TermRef};
use kink_pattern::{
    EventPresence, ExecutionTerminalKind, Feasibility, PathInput, RelationDecider,
    RelationDecision, SymbolSorts, TermRelation,
};

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: None,
    max_breadth: None,
};

fn app(symbol: &str, args: Vec<Pattern>) -> Pattern {
    support::app(symbol, args)
}

fn contains_symbol(pattern: &Pattern, name: &str) -> bool {
    match pattern {
        Pattern::Application { symbol, arguments } => {
            symbol.name == name || arguments.iter().any(|arg| contains_symbol(arg, name))
        }
        Pattern::And { arguments, .. } => arguments.iter().any(|arg| contains_symbol(arg, name)),
        _ => false,
    }
}

fn contains_domain_value(pattern: &Pattern, sort_name: &str, bytes: &[u8]) -> bool {
    match pattern {
        Pattern::DomainValue { sort, value } => {
            *sort == kore_sort(sort_name) && value.as_bytes() == bytes
        }
        Pattern::Application { arguments, .. } | Pattern::And { arguments, .. } => arguments
            .iter()
            .any(|argument| contains_domain_value(argument, sort_name, bytes)),
        _ => false,
    }
}

fn symmem_program() -> Pattern {
    let z = || app("Lblz", vec![]);
    let address = || app("Lbladdr", vec![z()]);
    let value = || app("Lbls", vec![z()]);
    app(
        "Lblseq",
        vec![
            app("Lblwrite", vec![address(), value()]),
            app(
                "Lblseq",
                vec![
                    app("Lblload", vec![address(), value()]),
                    app("Lblhalt", vec![]),
                ],
            ),
        ],
    )
}

fn event_presences(
    fixture: &str,
    module: &str,
    state: &Pattern,
    specs: Vec<StepEventSpec>,
) -> Vec<Vec<(String, EventPresence)>> {
    let validator = NativeValidator::bind(support::load(fixture), CompileOptions::default());
    let side = validator.compile_baseline().expect("fixture compiles");
    paths_for(&side, &side, module, state, specs)
        .iter()
        .map(|path| {
            path.events
                .iter()
                .map(|event| (event.constructor.clone(), event.presence.clone()))
                .collect()
        })
        .collect()
}

fn certain(names: &[&str]) -> Vec<(String, EventPresence)> {
    names
        .iter()
        .map(|name| ((*name).into(), EventPresence::Certain))
        .collect()
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

fn paths_for(
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
            Ok::<_, k_rust::backend::BackendError>(bridged.paths)
        })
        .expect("baseline decider")
}

#[test]
fn symmem_ground_whole_and_pre_state_events() {
    let state = support::initial_state(symmem_program(), "SortProg");
    for whole in [true, false] {
        assert_eq!(
            event_presences("symmem.k", "SYMMEM", &state, step_support::symmem(whole)),
            [certain(&["memoryWrite", "memoryLoad"])],
            "whole={whole}"
        );
    }
    let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("symmem compiles");
    let paths = paths_for(&side, &side, "SYMMEM", &state, step_support::symmem(true));
    assert_eq!(paths.len(), 1);
    let expected = vec![
        app("Lbladdr", vec![app("Lblz", vec![])]),
        app("Lbls", vec![app("Lblz", vec![])]),
    ];
    assert_eq!(paths[0].events[0].payload, expected);
    assert_eq!(paths[0].events[1].payload, expected);
}

#[test]
fn release_after_load_separates_whole_and_pre_state_events() {
    let state = support::initial_state(symmem_program(), "SortProg");
    assert_eq!(
        event_presences(
            "symmem_release.k",
            "SYMMEM'Unds'RELEASE",
            &state,
            step_support::symmem(true),
        ),
        [certain(&["memoryFree", "memoryFree"])],
    );
    assert_eq!(
        event_presences(
            "symmem_release.k",
            "SYMMEM'Unds'RELEASE",
            &state,
            step_support::symmem(false),
        ),
        [certain(&[
            "memoryWrite",
            "memoryFree",
            "memoryLoad",
            "memoryFree"
        ])],
    );
}

#[test]
fn counter_by_two_is_one_pre_state_increment_and_no_whole_increment() {
    let z = || app("Lblz", vec![]);
    let s = |arg| app("Lbls", vec![arg]);
    let state = support::initial_state(app("Lblcounter", vec![z(), s(s(z()))]), "SortCounter");
    assert_eq!(
        event_presences(
            "counter_bytwo.k",
            "COUNTER'Unds'BYTWO",
            &state,
            step_support::counter(true)
        ),
        [Vec::new()],
    );
    assert_eq!(
        event_presences(
            "counter_bytwo.k",
            "COUNTER'Unds'BYTWO",
            &state,
            step_support::counter(false)
        ),
        [certain(&["increment"])],
    );
}

#[test]
fn counter_whole_transition_counts_two_increments() {
    let z = || app("Lblz", vec![]);
    let s = |arg| app("Lbls", vec![arg]);
    let state = support::initial_state(app("Lblcounter", vec![z(), s(s(z()))]), "SortCounter");
    assert_eq!(
        event_presences("counter.k", "COUNTER", &state, step_support::counter(true)),
        [certain(&["increment", "increment"])],
    );
}

#[test]
fn guardedmem_fault_step_emits_no_whole_transition_load() {
    let operation = app(
        "Lblload",
        vec![app("Lbladdr", vec![support::int(-1)]), support::int(7)],
    );
    let state = support::initial_state(
        app("Lblseq", vec![operation, app("Lblhalt", vec![])]),
        "SortProg",
    );
    assert_eq!(
        event_presences(
            "guardedmem.k",
            "GUARDEDMEM",
            &state,
            step_support::guardedmem(true)
        ),
        [Vec::new()],
    );
}

fn bare_spec(pre: Pattern, payload: &[&str]) -> StepEventSpec {
    StepEventSpec {
        constructor: "tick".into(),
        pre,
        post: None,
        payload: payload.iter().map(|name| (*name).into()).collect(),
    }
}

fn string_value(bytes: &[u8]) -> Pattern {
    Pattern::DomainValue {
        sort: kore_sort("SortString"),
        value: bytes.to_vec().into(),
    }
}

fn custom_value(sort: &str, bytes: &[u8]) -> Pattern {
    Pattern::DomainValue {
        sort: kore_sort(sort),
        value: bytes.to_vec().into(),
    }
}

#[test]
fn hooked_string_sort_identity_is_undecided() {
    let directory = std::env::temp_dir().join(format!(
        "so03-mystr-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock")
            .as_nanos()
    ));
    std::fs::create_dir(&directory).expect("temporary definition directory");
    let source = "module MYSTR-SYNTAX\n  imports INT-SYNTAX\n  imports STRING-SYNTAX\n  syntax MyStr [hook(STRING.String)]\n  syntax MyStr ::= r\"#mystr[0-9]+\" [token]\n  syntax MyStr ::= chrM(Int) [function, total, hook(STRING.chr), symbol(chrM)]\n                 | MyStr \"+M\" MyStr [function, total, hook(STRING.concat), symbol(concatM)]\n  syntax Bool ::= MyStr \"==M\" MyStr [function, total, hook(STRING.eq), symbol(eqM)]\n  syntax Prog ::= step(Int) [symbol(step)]\n                | done(MyStr, MyStr) [symbol(done)]\n                | verdict(Bool) [symbol(verdict)]\nendmodule\nmodule MYSTR\n  imports MYSTR-SYNTAX\n  imports INT\n  imports STRING\n  imports BOOL\n  configuration <k> .K </k>\n  rule [step]: step(0) => done(chrM(937), chrM(206) +M chrM(169))\n  rule [eqc]: step(1) => verdict(chrM(937) ==M (chrM(206) +M chrM(169)))\nendmodule\n";
    let source_path = directory.join("mystr.k");
    std::fs::write(&source_path, source).expect("definition source");
    let side = NativeValidator::bind(
        support::load_path(&source_path, "MYSTR"),
        CompileOptions::default(),
    )
    .compile_baseline()
    .expect("MyStr definition compiles");
    let state = support::initial_state(app("Lblstep", vec![support::int(0)]), "SortProg");
    let steps = run_steps(&side, "MYSTR", &state);
    let equality_state = support::initial_state(app("Lblstep", vec![support::int(1)]), "SortProg");
    let equality_steps = run_steps(&side, "MYSTR", &equality_state);
    // Re-pin R0a (finding E-13): at 927b9ce6 the run evaluated the ill-sorted MyStr hooks and
    // reached `verdict(false)` beside `done` payloads that were byte-equal for the two different
    // strings (the old two-reading bug). At 501f18b9 k-rust leaves `chrM` unevaluated
    // (UnsupportedHook, `the evaluator did not reduce constructor-like arguments`), so no Bool
    // verdict is formed and the `eqM` application stays in the state.
    let mut equality_symbols = std::collections::BTreeSet::new();
    for state in &equality_steps.states[0] {
        k_rust::kore::walk::for_each_post_order(state, |node| {
            if let Pattern::Application { symbol, .. } = node {
                equality_symbols.insert(symbol.name.clone());
            }
        });
    }
    assert!(equality_symbols.contains("LbleqM"), "{equality_symbols:?}");
    assert!(equality_steps.states[0].iter().all(|state| {
        !contains_domain_value(state, "SortBool", b"false")
            && !contains_domain_value(state, "SortBool", b"true")
    }));
    let path = paths_for(&side, &side, "MYSTR", &state, vec![]).remove(0);
    let spec = StepEventSpec {
        constructor: "probe".into(),
        pre: support::k_config(
            app("Lblstep", vec![support::var("N", "SortInt")]),
            "SortProg",
            "R",
            "C",
        ),
        post: Some(support::k_config(
            app(
                "Lbldone",
                vec![
                    support::var("X", "SortMyStr"),
                    support::var("X", "SortMyStr"),
                ],
            ),
            "SortProg",
            "R2",
            "C2",
        )),
        payload: vec![],
    };
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        "MYSTR",
        BackendOptions::default(),
    )
    .expect("backend");
    StepObservation::new(&mut backend, vec![spec.clone()]).expect("declaration validates");
    backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(&state));
            assert!(matches!(
                decider.classify_step(&spec, &steps.states[0][0], Some(&steps.states[0][1]), &path),
                StepPresence::Undecided
            ));
            let relations =
                BackendRelations::shared(definition, solver, TestInitialState::of_test(&state));
            let value = custom_value("SortMyStr", &[206, 169]);
            assert_eq!(
                relations.relate(&path, &[], &value, &value),
                RelationDecision::Indeterminate
            );
            assert!(matches!(
                decider.classify_step(&bare_spec(value.clone(), &[]), &value, None, &path),
                StepPresence::Undecided
            ));
            assert_eq!(
                relations.feasible(
                    &path,
                    &[TermRelation {
                        left: value.clone(),
                        right: value.clone()
                    }]
                ),
                Feasibility::Unknown
            );
            let other = custom_value("SortMyStr", &[195, 142, 194, 169]);
            assert_eq!(
                relations.relate(&path, &[], &value, &other),
                RelationDecision::Indeterminate
            );
            assert_eq!(
                relations.feasible(
                    &path,
                    &[TermRelation {
                        left: value.clone(),
                        right: other,
                    }]
                ),
                Feasibility::Unknown
            );
            assert!(!decider.definition_independent(&value));
            Ok::<_, k_rust::backend::BackendError>(())
        })
        .expect("decider");
    std::fs::remove_dir_all(directory).expect("remove temporary definition");
}

#[test]
fn unknown_domain_codec_blocks_identity() {
    let (side, directory) = string_definition("\"a\"");
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        "STRINGS",
        BackendOptions::default(),
    )
    .expect("backend");
    let state = support::initial_state(app("Lblstep", vec![support::int(0)]), "SortProg");
    let path = paths_for(&side, &side, "STRINGS", &state, vec![]).remove(0);
    backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(&state));
            let spec = StepEventSpec {
                constructor: "probe".into(),
                pre: support::var("X", "SortGeneratedTopCell"),
                post: Some(support::var("X", "SortGeneratedTopCell")),
                payload: vec![],
            };
            assert_eq!(
                definition
                    .sorts()
                    .get("SortFloat")
                    .and_then(|info| info.hook.as_deref()),
                Some("FLOAT.Float")
            );
            for value in [
                custom_value("SortFloat", b"1.0"),
                custom_value("SortInt", b"01"),
                custom_value("SortInt", b"+1"),
                custom_value("SortInt", b"-0"),
            ] {
                assert!(matches!(
                    decider.classify_step(&spec, &value, Some(&value), &path),
                    StepPresence::Undecided
                ));
                assert_eq!(
                    BackendRelations::shared(definition, solver, TestInitialState::of_test(&state))
                        .relate(&path, &[], &value, &value),
                    RelationDecision::Indeterminate
                );
            }
            Ok::<_, k_rust::backend::BackendError>(())
        })
        .expect("decider");
    std::fs::remove_dir_all(directory).expect("remove temporary definition");
}

fn string_definition(result: &str) -> (ValidatedDefinition, std::path::PathBuf) {
    let directory = std::env::temp_dir().join(format!(
        "so03-string-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock")
            .as_nanos()
    ));
    std::fs::create_dir(&directory).expect("temporary definition directory");
    let source = format!(
        "module STRINGS-SYNTAX\n  imports INT-SYNTAX\n  imports STRING-SYNTAX\n  imports FLOAT-SYNTAX\n  syntax Prog ::= step(Int) [symbol(step)]\n                | done(String) [symbol(done)]\nendmodule\nmodule STRINGS\n  imports STRINGS-SYNTAX\n  imports INT\n  imports STRING\n  imports FLOAT\n  configuration <k> .K </k>\n  rule [step]: step(_N) => done({result})\nendmodule\n"
    );
    let path = directory.join("strings.k");
    std::fs::write(&path, source).expect("definition source");
    let side = NativeValidator::bind(
        support::load_path(&path, "STRINGS"),
        CompileOptions::default(),
    )
    .compile_baseline()
    .expect("string definition compiles");
    (side, directory)
}

#[test]
fn non_ascii_string_encodings_do_not_distinguish_equal_executions() {
    let (baseline, baseline_directory) = string_definition("chrChar(195) +String chrChar(169)");
    let (mutant, mutant_directory) = string_definition("\"Ã©\"");
    let state = support::initial_state(app("Lblstep", vec![support::int(0)]), "SortProg");
    let spec = StepEventSpec {
        constructor: "probe".into(),
        pre: support::k_config(
            app("Lblstep", vec![support::var("N", "SortInt")]),
            "SortProg",
            "R",
            "C",
        ),
        post: Some(support::k_config(
            app("Lbldone", vec![string_value("Ã©".as_bytes())]),
            "SortProg",
            "R2",
            "C2",
        )),
        payload: vec![],
    };
    let mut backend = Backend::new(
        &baseline.artifacts().definition_kore,
        "STRINGS",
        BackendOptions::default(),
    )
    .expect("backend");
    assert!(matches!(
        StepObservation::new(&mut backend, vec![spec.clone()]),
        Err(StepObservationError::NonCanonicalValue(_))
    ));
    let baseline_steps = run_steps(&baseline, "STRINGS", &state);
    let mutant_steps = run_steps(&mutant, "STRINGS", &state);
    let path = paths_for(&baseline, &baseline, "STRINGS", &state, vec![]).remove(0);
    backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(&state));
            assert!(!decider.definition_independent(&string_value(&[195, 169])));
            assert!(!decider.definition_independent(&string_value("é".as_bytes())));
            assert!(decider.definition_independent(&string_value(b"abc")));
            assert!(matches!(
                decider.classify_step(
                    &spec,
                    &baseline_steps.states[0][0],
                    Some(&baseline_steps.states[0][1]),
                    &path,
                ),
                StepPresence::Undecided
            ));
            assert!(matches!(
                decider.classify_step(
                    &bare_spec(string_value(&[195, 169]), &[]),
                    &string_value(&[195, 169]),
                    None,
                    &path,
                ),
                StepPresence::Undecided
            ));
            assert!(matches!(
                decider.classify_step(
                    &spec,
                    &mutant_steps.states[0][0],
                    Some(&mutant_steps.states[0][1]),
                    &path,
                ),
                StepPresence::Undecided
            ));
            assert!(matches!(
                decider.classify_step(
                    &bare_spec(string_value(b"a"), &[]),
                    &string_value(b"b"),
                    None,
                    &path,
                ),
                StepPresence::Absent
            ));
            Ok::<_, k_rust::backend::BackendError>(())
        })
        .expect("decider");
    std::fs::remove_dir_all(baseline_directory).expect("remove baseline definition");
    std::fs::remove_dir_all(mutant_directory).expect("remove mutant definition");
}

#[test]
fn shared_string_relations_refuse_non_ascii_clashes() {
    let (side, directory) = string_definition("\"a\"");
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        "STRINGS",
        BackendOptions::default(),
    )
    .expect("backend");
    let state = support::initial_state(app("Lblstep", vec![support::int(0)]), "SortProg");
    let path = paths_for(&side, &side, "STRINGS", &state, vec![]).remove(0);
    backend
        .with_solver(None, |definition, solver| {
            let relations =
                BackendRelations::shared(definition, solver, TestInitialState::of_test(&state));
            for (left, right) in [
                (string_value(&[195, 169]), string_value("Ã©".as_bytes())),
                (string_value("é".as_bytes()), string_value("Ã©".as_bytes())),
                (string_value(&[195, 169]), string_value(&[195, 169])),
                (string_value(b"a"), string_value("é".as_bytes())),
            ] {
                assert_eq!(
                    relations.relate(&path, &[], &left, &right),
                    RelationDecision::Indeterminate
                );
                assert_ne!(
                    relations.feasible(&path, &[TermRelation { left, right }]),
                    Feasibility::Unsat
                );
            }
            assert_eq!(
                relations.relate(&path, &[], &string_value(b"a"), &string_value(b"b")),
                RelationDecision::Unequal
            );
            Ok::<_, k_rust::backend::BackendError>(())
        })
        .expect("relations");
    std::fs::remove_dir_all(directory).expect("remove temporary definition");
}

fn validation_backend() -> Backend {
    let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("symmem compiles");
    Backend::new(
        &side.artifacts().definition_kore,
        "SYMMEM",
        BackendOptions::default(),
    )
    .expect("backend")
}

#[test]
fn declaration_validation_has_one_refusal_for_each_rule() {
    let top = || support::var("X", "SortGeneratedTopCell");
    let pure = |specs: Vec<StepEventSpec>| StepObservation::vocabulary_of(&specs);
    assert!(matches!(
        pure(vec![bare_spec(top(), &["Missing"])]),
        Err(StepObservationError::MissingPayload(_))
    ));
    assert!(matches!(
        pure(vec![bare_spec(
            support::var("X!1", "SortGeneratedTopCell"),
            &[]
        )]),
        Err(StepObservationError::ReservedVariable(_))
    ));
    assert!(matches!(
        pure(vec![
            bare_spec(top(), &["X"]),
            bare_spec(support::var("X", "SortInt"), &["X"])
        ]),
        Err(StepObservationError::ConstructorSorts(_))
    ));

    let mut backend = validation_backend();
    let mut validate = |pre| StepObservation::new(&mut backend, vec![bare_spec(pre, &[])]);
    assert!(matches!(
        validate(app("Lblmissing", vec![])),
        Err(StepObservationError::Internalization(_))
    ));
    assert!(matches!(
        validate(support::k_config(
            support::var("P", "SortInt"),
            "SortProg",
            "R",
            "C"
        )),
        Err(StepObservationError::VariableSort(_))
    ));
    assert!(matches!(
        validate(Pattern::DomainValue {
            sort: kore_sort("SortInt"),
            value: "00".into()
        }),
        Err(StepObservationError::NonCanonicalValue(_))
    ));
    assert!(matches!(
        validate(Pattern::And {
            sort: kore_sort("SortGeneratedTopCell"),
            arguments: vec![top(), top()],
        }),
        Err(StepObservationError::UnsupportedPattern(_))
    ));

    let validator = NativeValidator::bind(support::load("residue.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("residue compiles");
    let mut residue = Backend::new(
        &side.artifacts().definition_kore,
        "RESIDUE",
        BackendOptions::default(),
    )
    .expect("residue backend");
    let function = app("Lblf", vec![support::int(1)]);
    let operation = app("Lblwrite", vec![function]);
    let pre = support::k_config(
        app("Lblseq", vec![operation, support::var("P", "SortProg")]),
        "SortProg",
        "R",
        "C",
    );
    assert!(matches!(
        StepObservation::new(&mut residue, vec![bare_spec(pre, &[])]),
        Err(StepObservationError::NonFreeSymbol(_))
    ));
}

#[test]
fn label_swapped_copy_gives_identical_paths() {
    let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
    let baseline = validator.baseline();
    let operation = |label| {
        let at = TermRef::new(support::rule(baseline, label), [0, 0, 0]);
        let term = baseline.term(&at).expect("operation").clone();
        (at, term)
    };
    let (write_at, write_op) = operation("SYMMEM.write");
    let (load_at, load_op) = operation("SYMMEM.load");
    let patch = Patch::new(vec![
        Edit::ReplaceTerm {
            at: write_at,
            expected: write_op.clone(),
            replacement: load_op.clone(),
        },
        Edit::ReplaceTerm {
            at: load_at,
            expected: load_op,
            replacement: write_op,
        },
    ])
    .expect("swap patch");
    let original = validator.compile_baseline().expect("baseline");
    let swapped = validator.validate(&patch).expect("swapped mutant");
    let state = support::initial_state(symmem_program(), "SortProg");
    let specs = step_support::symmem(true);
    assert_eq!(
        paths_for(&original, &original, "SYMMEM", &state, specs.clone()),
        paths_for(&original, &swapped, "SYMMEM", &state, specs),
    );
}

/// A mutant with a dead existential rule (never fires) has the baseline's canonical PathInputs
/// and relation answers. Before variable identity both sides were decided under the pair
/// existentials flag; now both link the test's initial variables.
#[test]
fn dead_existential_rule_does_not_change_paths() {
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
        app(
            "Lblseq",
            vec![
                app(
                    "Lblwrite",
                    vec![
                        app("Lbladdr", vec![support::var("X", "SortNat")]),
                        support::var("V", "SortNat"),
                    ],
                ),
                app(
                    "Lblseq",
                    vec![
                        app(
                            "Lblload",
                            vec![
                                app("Lbladdr", vec![support::var("X", "SortNat")]),
                                support::var("V", "SortNat"),
                            ],
                        ),
                        app("Lblhalt", vec![]),
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
        let before = paths_for(&original, &original, "SYMMEM", &state, specs.clone());
        let after = paths_for(&original, &mutant, "SYMMEM", &state, specs);
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
                let z = app("Lblz", vec![]);
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

#[test]
fn same_priority_twin_gives_identical_paths() {
    let validator = NativeValidator::bind(support::load("guardedmem.k"), CompileOptions::default());
    let baseline = validator.baseline();
    let write = support::rule(baseline, "GUARDEDMEM.write");
    let mut twin = baseline.sentence(&write).expect("write rule").clone();
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
        twin.attributes_mut().remove(key.as_str());
    }
    if let k_rust::definition::Sentence::Rule { requires, .. } = &mut twin {
        let address = baseline
            .term(&TermRef::new(write.clone(), [0, 0, 0, 0, 0]))
            .expect("address")
            .clone();
        *requires = Term::apply(
            "_<=Int_",
            vec![
                Term::Token {
                    token: "0".into(),
                    sort: KastSort::new("Int"),
                },
                address,
            ],
        );
    } else {
        panic!("write is a rule");
    }
    let patch = Patch::new(vec![Edit::InsertSentence {
        position: InsertPosition::After(write),
        ordinal: 0,
        sentence: twin,
    }])
    .expect("twin patch");
    let original = validator.compile_baseline().expect("baseline");
    let mutant = validator.validate(&patch).expect("twin compiles");
    for address in [0, 1] {
        let state = support::initial_state(
            app(
                "Lblseq",
                vec![
                    app(
                        "Lblwrite",
                        vec![app("Lbladdr", vec![support::int(address)]), support::int(5)],
                    ),
                    app("Lblhalt", vec![]),
                ],
            ),
            "SortProg",
        );
        let specs = step_support::guardedmem(true);
        assert_eq!(
            run_steps(&original, "GUARDEDMEM", &state)
                .adapted
                .leaves()
                .len(),
            1,
            "baseline raw leaf count at address={address}",
        );
        assert_eq!(
            run_steps(&mutant, "GUARDEDMEM", &state)
                .adapted
                .leaves()
                .len(),
            2,
            "twin raw leaf count at address={address}",
        );
        assert_eq!(
            paths_for(&original, &original, "GUARDEDMEM", &state, specs.clone()),
            paths_for(&original, &mutant, "GUARDEDMEM", &state, specs),
            "address={address}",
        );
        assert_eq!(
            paths_for(
                &original,
                &mutant,
                "GUARDEDMEM",
                &state,
                step_support::guardedmem(true)
            )
            .len(),
            1,
            "equal twin leaves merge",
        );
    }
}

#[test]
fn paths_are_ordered_canonically_and_duplicates_merged() {
    let validator = NativeValidator::bind(support::load("nd.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("nd compiles");
    let state = support::initial_state(app("Lblstart", vec![]), "SortS");
    let raw = run_steps(&side, "ND", &state);
    assert_eq!(raw.states.len(), 2);
    let raw_targets = raw
        .states
        .iter()
        .map(|states| {
            if states.iter().any(|state| contains_symbol(state, "Lblmid1")) {
                "Lblmid1"
            } else if states.iter().any(|state| contains_symbol(state, "Lblmid2")) {
                "Lblmid2"
            } else {
                panic!("raw branch lacks a mid state")
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(raw_targets, ["Lblmid1", "Lblmid2"], "raw leaf order");
    let specs = [("b", "Lblmid1"), ("a", "Lblmid2")]
        .into_iter()
        .map(|(constructor, target)| StepEventSpec {
            constructor: constructor.into(),
            pre: support::k_config(app("Lblstart", vec![]), "SortS", "R", "C"),
            post: Some(support::k_config(app(target, vec![]), "SortS", "R", "C2")),
            payload: vec![],
        })
        .collect();
    let paths = paths_for(&side, &side, "ND", &state, specs);
    assert_eq!(paths.len(), 2, "distinct event traces remain distinct");
    assert_eq!(paths[0].events[0].constructor, "a");
    assert_eq!(paths[1].events[0].constructor, "b");
    assert_eq!(paths[0].path_key.as_deref(), Some("leaf:0"));
    assert_eq!(paths[1].path_key.as_deref(), Some("leaf:1"));
    assert_eq!(paths[0].events[0].index, 0);
    assert_eq!(paths[1].events[0].index, 0);
    assert_ne!(paths[0], paths[1], "distinct PathInputs are retained");
}

#[test]
fn missing_stepped_states_refuse_the_whole_bridge() {
    let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("symmem compiles");
    let state = support::initial_state(symmem_program(), "SortProg");
    let mut execution = run_steps(&side, "SYMMEM", &state);
    assert_eq!(execution.states.len(), execution.adapted.leaves().len());
    execution.states.pop();
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        "SYMMEM",
        BackendOptions::default(),
    )
    .expect("backend");
    let observation =
        StepObservation::new(&mut backend, step_support::symmem(true)).expect("observation");
    let sorts = SymbolSorts::from_definition(
        &parse_definition(&side.artifacts().definition_kore).expect("compiled KORE parses"),
    );
    let normal = |_: &Pattern| ExecutionTerminalKind::Normal;
    backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(&state));
            let result = paths_from_steps(
                &BridgeContext {
                    test_id: "missing",
                    classify: &normal,
                    sorts: &sorts,
                },
                &execution,
                &observation,
                &decider,
            );
            assert!(matches!(result, Err(BridgeFailure::UndecodableState(_))));
            Ok::<_, k_rust::backend::BackendError>(())
        })
        .expect("baseline decider");
}

#[test]
fn symbolic_choose_has_one_conditional_branch_only_with_z3() {
    let validator = NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("counter compiles");
    let state = support::initial_state(
        app("Lblchoose", vec![support::var("B", "SortBool")]),
        "SortControl",
    );
    let paths = paths_for(&side, &side, "COUNTER", &state, step_support::counter(true));
    if cfg!(feature = "z3") {
        assert_eq!(paths.len(), 2, "branch and fallback leaves");
        let with_event: Vec<_> = paths
            .iter()
            .filter(|path| {
                path.events
                    .iter()
                    .any(|event| event.constructor == "branchTaken")
            })
            .collect();
        assert_eq!(with_event.len(), 1);
        match &with_event[0].events[0].presence {
            EventPresence::Certain => {}
            EventPresence::Conditional(relations) => assert_eq!(
                relations,
                &[TermRelation {
                    left: support::var("B", "SortBool"),
                    right: Pattern::DomainValue {
                        sort: kore_sort("SortBool"),
                        value: "true".into(),
                    },
                }],
            ),
            EventPresence::Undecided => panic!("branch event is undecided"),
        }
        assert_eq!(
            paths.iter().filter(|path| path.events.is_empty()).count(),
            1
        );
    } else {
        assert_eq!(paths.len(), 1, "one indeterminate leaf without a solver");
        assert!(paths[0].events.is_empty());
        let raw = run_steps(&side, "COUNTER", &state);
        assert_eq!(raw.adapted.leaves().len(), 1);
        assert_eq!(raw.states.len(), 1);
        assert_eq!(raw.states[0].len(), 1, "zero steps");
    }
}

#[test]
fn function_residue_does_not_make_a_constant_event_absent() {
    let validator = NativeValidator::bind(support::load("residue.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("residue compiles");
    let state = support::initial_state(
        app(
            "Lblseq",
            vec![
                app("Lblwrite", vec![app("Lblf", vec![support::int(1)])]),
                app("Lblhalt", vec![]),
            ],
        ),
        "SortProg",
    );
    let spec = bare_spec(
        support::k_config(
            app(
                "Lblseq",
                vec![
                    app("Lblwrite", vec![support::int(1)]),
                    support::var("P", "SortProg"),
                ],
            ),
            "SortProg",
            "R",
            "C",
        ),
        &[],
    );
    let paths = paths_for(&side, &side, "RESIDUE", &state, vec![spec]);
    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0].events.len(), 1);
    assert!(matches!(
        paths[0].events[0].presence,
        EventPresence::Undecided
    ));
}

#[test]
fn injections_match_modulo_subsorts() {
    let validator =
        NativeValidator::bind(support::load("subsort_steps.k"), CompileOptions::default());
    let side = validator
        .compile_baseline()
        .expect("subsort fixture compiles");
    let small = app("Lbla", vec![]);
    let injection = k_rust::kompile::initial_configuration::kore_application(
        "inj",
        vec![kore_sort("SortSmall"), kore_sort("SortLarge")],
        vec![small],
    );
    let state = support::initial_state(app("Lblstep", vec![injection]), "SortProg");
    let pre = support::k_config(
        app("Lblstep", vec![support::var("X", "SortLarge")]),
        "SortProg",
        "R",
        "C",
    );
    let post = support::k_config(
        app("Lbldone", vec![support::var("X", "SortLarge")]),
        "SortProg",
        "R",
        "C2",
    );
    let paths = paths_for(
        &side,
        &side,
        "SUBSORT'Unds'STEPS",
        &state,
        vec![StepEventSpec {
            constructor: "subsorted".into(),
            pre,
            post: Some(post),
            payload: vec!["X".into()],
        }],
    );
    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0].events.len(), 1);
    assert!(matches!(
        paths[0].events[0].presence,
        EventPresence::Certain
    ));
    assert_eq!(paths[0].events[0].payload.len(), 1);

    let inj = |source: &str, target: &str, value| {
        k_rust::kompile::initial_configuration::kore_application(
            "inj",
            vec![kore_sort(source), kore_sort(target)],
            vec![value],
        )
    };
    let spec = |pre| StepEventSpec {
        constructor: "probe".into(),
        pre,
        post: None,
        payload: vec![],
    };
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        "SUBSORT'Unds'STEPS",
        BackendOptions::default(),
    )
    .expect("backend");
    backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(&state));
            let nested = inj(
                "SortLarge",
                "SortKItem",
                inj("SortSmall", "SortLarge", app("Lbla", vec![])),
            );
            let collapsed = inj("SortSmall", "SortKItem", app("Lbla", vec![]));
            assert!(matches!(
                decider.classify_step(&spec(nested), &collapsed, None, &paths[0]),
                StepPresence::Certain(_)
            ));
            let other = inj("SortOther", "SortLarge", app("Lblb", vec![]));
            let small = inj("SortSmall", "SortLarge", app("Lbla", vec![]));
            assert!(matches!(
                decider.classify_step(&spec(small), &other, None, &paths[0]),
                StepPresence::Absent
            ));
            let unknown_small = inj("SortSmall", "SortLarge", support::var("X", "SortSmall"));
            let unknown_other = inj("SortOther", "SortLarge", support::var("Y", "SortOther"));
            assert!(matches!(
                decider.classify_step(&spec(unknown_small), &unknown_other, None, &paths[0]),
                StepPresence::Absent
            ));
            let left = inj("SortLeft", "SortWide", support::var("X", "SortLeft"));
            let right = inj("SortRight", "SortWide", support::var("Y", "SortRight"));
            assert!(matches!(
                decider.classify_step(&spec(left.clone()), &right, None, &paths[0]),
                StepPresence::Undecided
            ));
            let left_constructor = inj("SortLeft", "SortWide", app("Lbll", vec![]));
            let right = inj("SortRight", "SortWide", support::var("Y", "SortRight"));
            assert!(matches!(
                decider.classify_step(&spec(left_constructor), &right, None, &paths[0]),
                StepPresence::Absent
            ));
            let left = inj("SortLeft", "SortWide", support::var("X", "SortLeft"));
            let right_constructor = inj("SortRight", "SortWide", app("Lblr", vec![]));
            assert!(matches!(
                decider.classify_step(&spec(left), &right_constructor, None, &paths[0]),
                StepPresence::Absent
            ));
            let small = inj("SortSmall", "SortKItem", support::var("X", "SortSmall"));
            let larger_constructor = inj("SortLarge", "SortKItem", app("Lblc", vec![]));
            assert!(matches!(
                decider.classify_step(&spec(small.clone()), &larger_constructor, None, &paths[0]),
                StepPresence::Absent
            ));
            let larger_variable = inj("SortLarge", "SortKItem", support::var("Y", "SortLarge"));
            assert!(matches!(
                decider.classify_step(&spec(small.clone()), &larger_variable, None, &paths[0]),
                StepPresence::Conditional(_, _) | StepPresence::Undecided
            ));
            let larger_nested = inj(
                "SortLarge",
                "SortKItem",
                inj("SortOther", "SortLarge", app("Lblb", vec![])),
            );
            assert!(matches!(
                decider.classify_step(&spec(small), &larger_nested, None, &paths[0]),
                StepPresence::Undecided
            ));
            Ok::<_, k_rust::backend::BackendError>(())
        })
        .expect("decider");
}

#[test]
fn identity_injection_declaration_is_refused() {
    let validator =
        NativeValidator::bind(support::load("subsort_steps.k"), CompileOptions::default());
    let side = validator
        .compile_baseline()
        .expect("subsort fixture compiles");
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        "SUBSORT'Unds'STEPS",
        BackendOptions::default(),
    )
    .expect("backend");
    let identity = k_rust::kompile::initial_configuration::kore_application(
        "inj",
        vec![kore_sort("SortLarge"), kore_sort("SortLarge")],
        vec![support::var("X", "SortLarge")],
    );
    let spec = StepEventSpec {
        constructor: "probe".into(),
        pre: support::k_config(
            app("Lblstep", vec![support::var("X", "SortLarge")]),
            "SortProg",
            "R",
            "C",
        ),
        post: Some(support::k_config(
            app("Lbldone", vec![identity]),
            "SortProg",
            "R2",
            "C2",
        )),
        payload: vec![],
    };
    assert!(matches!(
        StepObservation::new(&mut backend, vec![spec]),
        Err(StepObservationError::VariableSort(_))
    ));
}

#[test]
fn unvalidated_identity_injections_are_undecided() {
    let validator =
        NativeValidator::bind(support::load("subsort_steps.k"), CompileOptions::default());
    let side = validator
        .compile_baseline()
        .expect("subsort fixture compiles");
    let inj = |source: &str, target: &str, value| {
        k_rust::kompile::initial_configuration::kore_application(
            "inj",
            vec![kore_sort(source), kore_sort(target)],
            vec![value],
        )
    };
    let spec = StepEventSpec {
        constructor: "probe".into(),
        pre: support::k_config(
            app("Lblstep", vec![support::var("X", "SortLarge")]),
            "SortProg",
            "R",
            "C",
        ),
        post: Some(support::k_config(
            app(
                "Lbldone",
                vec![inj(
                    "SortLarge",
                    "SortLarge",
                    support::var("X", "SortLarge"),
                )],
            ),
            "SortProg",
            "R2",
            "C2",
        )),
        payload: vec![],
    };
    for argument in [
        support::var("Y", "SortLarge"),
        inj("SortSmall", "SortLarge", app("Lbla", vec![])),
        inj("SortOther", "SortLarge", app("Lblb", vec![])),
    ] {
        let state = support::initial_state(app("Lblstep", vec![argument]), "SortProg");
        let stepped = run_steps(&side, "SUBSORT'Unds'STEPS", &state);
        let paths = paths_for(&side, &side, "SUBSORT'Unds'STEPS", &state, vec![]);
        let mut backend = Backend::new(
            &side.artifacts().definition_kore,
            "SUBSORT'Unds'STEPS",
            BackendOptions::default(),
        )
        .expect("backend");
        backend
            .with_solver(None, |definition, solver| {
                let decider =
                    ObservationDecider::new(definition, solver, TestInitialState::of_test(&state));
                assert!(matches!(
                    decider.classify_step(
                        &spec,
                        &stepped.states[0][0],
                        Some(&stepped.states[0][1]),
                        &paths[0],
                    ),
                    StepPresence::Undecided
                ));
                let identity = inj("SortLarge", "SortLarge", support::var("Y", "SortLarge"));
                assert!(matches!(
                    decider.classify_step(
                        &bare_spec(identity.clone(), &[]),
                        &identity,
                        None,
                        &paths[0]
                    ),
                    StepPresence::Undecided
                ));
                assert!(matches!(
                    decider.classify_step(
                        &bare_spec(inj("SortSmall", "SortLarge", app("Lbla", vec![])), &[]),
                        &identity,
                        None,
                        &paths[0],
                    ),
                    StepPresence::Undecided
                ));
                Ok::<_, k_rust::backend::BackendError>(())
            })
            .expect("decider");
    }
}

#[test]
fn ill_sorted_injection_constructor_heads_are_undecided() {
    let validator =
        NativeValidator::bind(support::load("subsort_steps.k"), CompileOptions::default());
    let side = validator
        .compile_baseline()
        .expect("subsort fixture compiles");
    let state = support::initial_state(app("Lblhalt", vec![]), "SortProg");
    let paths = paths_for(&side, &side, "SUBSORT'Unds'STEPS", &state, vec![]);
    let inj = |source: &str, target: &str, value| {
        k_rust::kompile::initial_configuration::kore_application(
            "inj",
            vec![kore_sort(source), kore_sort(target)],
            vec![value],
        )
    };
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        "SUBSORT'Unds'STEPS",
        BackendOptions::default(),
    )
    .expect("backend");
    backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(&state));
            for (pattern, subject) in [
                (
                    inj("SortSmall", "SortKItem", support::var("X", "SortSmall")),
                    inj("SortLarge", "SortKItem", app("Lbla", vec![])),
                ),
                (
                    inj("SortLeft", "SortWide", support::var("X", "SortLeft")),
                    inj("SortRight", "SortWide", app("Lblt", vec![])),
                ),
                (
                    inj("SortLeft", "SortWide", app("Lblt", vec![])),
                    inj("SortRight", "SortWide", support::var("Y", "SortRight")),
                ),
            ] {
                assert!(matches!(
                    decider.classify_step(&bare_spec(pattern, &[]), &subject, None, &paths[0]),
                    StepPresence::Undecided
                ));
            }
            Ok::<_, k_rust::backend::BackendError>(())
        })
        .expect("decider");
}

// The facade erasure contract is exercised on the original twelve symbolic programs.
mod position_rows {
    use super::*;
    use k_rust::kore::codec;
    use kink_native::execution::HaltClass;
    use kink_native::feasibility::LeafFeasibility;

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
    }

    fn app(name: &str, args: Vec<Pattern>) -> Pattern {
        support::app(name, args)
    }
    fn nat(name: &str) -> Pattern {
        support::var(name, "SortNat")
    }
    fn integer(name: &str) -> Pattern {
        support::var(name, "SortInt")
    }
    fn z() -> Pattern {
        app("Lblz", vec![])
    }
    fn s(value: Pattern) -> Pattern {
        app("Lbls", vec![value])
    }
    fn addr(value: Pattern) -> Pattern {
        app("Lbladdr", vec![value])
    }
    fn write(address: Pattern, value: Pattern) -> Pattern {
        app("Lblwrite", vec![address, value])
    }
    fn load(address: Pattern, value: Pattern) -> Pattern {
        app("Lblload", vec![address, value])
    }
    fn load_neg(address: Pattern, value: Pattern) -> Pattern {
        app("LblloadNeg", vec![address, value])
    }
    fn free(address: Pattern) -> Pattern {
        app("Lblfree", vec![address])
    }
    fn halt() -> Pattern {
        app("Lblhalt", vec![])
    }
    fn seq(operation: Pattern, rest: Pattern) -> Pattern {
        app("Lblseq", vec![operation, rest])
    }
    fn fork(left: Pattern, right: Pattern) -> Pattern {
        app("Lblfork", vec![left, right])
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

    type ProgramRow = (&'static str, Pattern);
    type FixtureRow = (Fixture, Vec<ProgramRow>);

    fn fixture_rows() -> Vec<FixtureRow> {
        vec![
            (
                Fixture::Sym,
                vec![
                    ("p1", p1()),
                    ("p2", p2()),
                    ("p3", p3()),
                    ("p4", p4()),
                    ("p5", p5()),
                    ("p6", p6()),
                    ("p7", p7()),
                    ("p8", p8()),
                    ("p9", p9()),
                ],
            ),
            (
                Fixture::Guard,
                vec![("g1", g1()), ("g2", g2()), ("g3", g3())],
            ),
        ]
    }

    fn expected_positions(fixture: Fixture, row: &str) -> Vec<(HaltClass, LeafFeasibility, usize)> {
        let (halt, feasibility, lengths) = match (fixture, row) {
            (Fixture::Guard, "g1") if cfg!(feature = "z3") => {
                (HaltClass::Stuck, LeafFeasibility::Solver, vec![3, 3, 2])
            }
            (Fixture::Guard, "g2") if cfg!(feature = "z3") => {
                (HaltClass::Stuck, LeafFeasibility::Solver, vec![3, 2, 2])
            }
            (Fixture::Guard, "g1" | "g2") => (
                HaltClass::Indeterminate,
                LeafFeasibility::Syntactic,
                vec![1],
            ),
            (Fixture::Sym, "p2") => (HaltClass::Stuck, LeafFeasibility::Syntactic, vec![4]),
            (Fixture::Sym, "p4") => (HaltClass::Stuck, LeafFeasibility::Syntactic, vec![3, 3]),
            (Fixture::Sym, "p5") => (HaltClass::Stuck, LeafFeasibility::Syntactic, vec![4, 3]),
            (Fixture::Sym, "p9") => (HaltClass::Stuck, LeafFeasibility::Syntactic, vec![4, 4]),
            _ => (HaltClass::Stuck, LeafFeasibility::Syntactic, vec![3]),
        };
        lengths
            .into_iter()
            .map(|length| (halt, feasibility, length))
            .collect()
    }

    #[test]
    fn stepped_positions_keep_unobserved_leaves_and_order() {
        let mut reached_three = false;
        let mut reached_remainder = false;
        for (fixture, programs) in fixture_rows() {
            let validator =
                NativeValidator::bind(support::load(fixture.name()), CompileOptions::default());
            let side = validator.compile_baseline().expect("fixture compiles");
            let mut backend = Backend::new(
                &side.artifacts().definition_kore,
                fixture.module(),
                BackendOptions {
                    smt_timeout_ms: 4000,
                    smt_retry_limit: 2,
                },
            )
            .expect("backend");
            let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
            for (row, program) in programs {
                let state = support::initial_state(program, "SortProg");
                let execution = adapter
                    .execute_steps(&mut backend, &state, BUDGET)
                    .expect("execution")
                    .expect("stepped run");
                assert_eq!(
                    execution
                        .adapted
                        .leaves()
                        .iter()
                        .zip(&execution.states)
                        .map(|(leaf, states)| (leaf.halt, leaf.feasibility, states.len()))
                        .collect::<Vec<_>>(),
                    expected_positions(fixture, row),
                    "{} {row}: pre-migration measurements",
                    fixture.name()
                );
                let unobserved = adapter
                    .execute_unobserved(&mut backend, &state, BUDGET)
                    .expect("unobserved run");
                assert!(
                    !unobserved.timed_out,
                    "{} {row}: unobserved timeout",
                    fixture.name()
                );
                let unobserved = unobserved.leaves;
                let mut erased = execution.adapted.erased();
                for leaf in &mut erased {
                    leaf.branch.clear();
                }
                assert_eq!(
                    erased,
                    unobserved,
                    "{} {row}: leaves and order",
                    fixture.name()
                );
                assert_eq!(
                    execution.states.len(),
                    execution.adapted.leaves().len(),
                    "{} {row}: sequences",
                    fixture.name()
                );
                for (index, (states, leaf)) in execution
                    .states
                    .iter()
                    .zip(execution.adapted.leaves())
                    .enumerate()
                {
                    let rewrites = leaf
                        .branch
                        .identity
                        .iter()
                        .filter(|id| !id.rule.starts_with("remainder:"))
                        .count();
                    let remainders = leaf.branch.identity.len() - rewrites;
                    assert_eq!(
                        states.len(),
                        rewrites + 1,
                        "{} {row} leaf {index}: Rewrite positions; Remainder adds none",
                        fixture.name()
                    );
                    assert_eq!(
                        states.last(),
                        Some(&codec::from_value(&leaf.branch.state).expect("decoded last state"))
                    );
                    reached_three |= states.len() >= 3;
                    reached_remainder |= remainders > 0;
                    if matches!(fixture, Fixture::Guard) && row != "g3" && !cfg!(feature = "z3") {
                        assert_eq!(
                            (leaf.halt, leaf.feasibility, states.len()),
                            (HaltClass::Indeterminate, LeafFeasibility::Syntactic, 1)
                        );
                    }
                }
            }
        }
        assert!(reached_three, "no program reached three states");
        assert_eq!(
            reached_remainder,
            cfg!(feature = "z3"),
            "Remainder entries arise only from solver-decided guarded rows"
        );
    }

    #[test]
    fn undefined_step_keeps_its_pre_step_state_as_last_position() {
        let validator =
            NativeValidator::bind(support::load("symbottom.k"), CompileOptions::default());
        let side = validator.compile_baseline().expect("fixture compiles");
        let stop = app("Lblstop", vec![support::int(1)]);
        let state = support::initial_state(
            seq(
                write(addr(support::int(1)), support::int(5)),
                seq(load(addr(support::int(1)), support::int(5)), stop.clone()),
            ),
            "SortProg",
        );
        let execution = run_steps(&side, "SYMBOTTOM", &state);
        let [leaf] = execution.adapted.leaves() else {
            panic!("one leaf")
        };
        assert_eq!(
            (leaf.halt, leaf.branch.depth, leaf.feasibility),
            (HaltClass::Trivial, 2, LeafFeasibility::Syntactic)
        );
        assert_eq!(execution.states[0].len(), 3);
        assert_eq!(
            execution.states[0].last(),
            Some(&support::initial_state(stop, "SortProg")),
            "undefined step adds no successor position"
        );
        assert_eq!(
            paths_for(
                &side,
                &side,
                "SYMBOTTOM",
                &state,
                step_support::int_memory(true)
            )[0]
            .events
            .len(),
            2,
            "undefined step emits no event"
        );
    }
}

// ---------------------------------------------------------------- SO-09 close-out audits

/// The bridged paths of `state` on `side`, with `specs` validated and decided by `side`'s own
/// decider (the baseline's, in these single-definition rows).
fn bridged_for(
    side: &ValidatedDefinition,
    module: &str,
    state: &Pattern,
    specs: Vec<StepEventSpec>,
) -> (kink_native::bridge::BridgedPaths, Backend) {
    let execution = run_steps(side, module, state);
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        module,
        BackendOptions::default(),
    )
    .expect("backend");
    let observation = StepObservation::new(&mut backend, specs).expect("declarations validate");
    let sorts = SymbolSorts::from_definition(
        &parse_definition(&side.artifacts().definition_kore).expect("compiled KORE parses"),
    );
    let normal = |_: &Pattern| ExecutionTerminalKind::Normal;
    let bridged = backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(state));
            Ok::<_, k_rust::backend::BackendError>(
                paths_from_steps(
                    &BridgeContext {
                        test_id: "audit",
                        classify: &normal,
                        sorts: &sorts,
                    },
                    &execution,
                    &observation,
                    &decider,
                )
                .expect("steps bridge"),
            )
        })
        .expect("decider");
    (bridged, backend)
}

/// A one-arm plan over `constructors` joined by `relation`, without payload clauses.
fn chain_plan(
    vocabulary: &kink_pattern::EventVocabulary,
    constructors: &[&str],
    relation: kink_pattern::Relation,
) -> kink_pattern::PatternPlan {
    kink_pattern::PatternPlan::new(
        vocabulary,
        Vec::new(),
        vec![kink_pattern::PatternArm {
            atoms: constructors
                .iter()
                .map(|constructor| kink_pattern::Atom {
                    constructor: (*constructor).into(),
                    payload: Vec::new(),
                })
                .collect(),
            relations: vec![relation; constructors.len() - 1],
        }],
        None,
    )
    .expect("plan")
}

fn whole_step(constructor: &str, pre: Pattern, post: Pattern, payload: &[&str]) -> StepEventSpec {
    StepEventSpec {
        constructor: constructor.into(),
        pre: support::k_config(pre, "SortProg", "R", "C"),
        post: Some(support::k_config(post, "SortProg", "R2", "C2")),
        payload: payload.iter().map(|name| (*name).into()).collect(),
    }
}

/// SO-AT3: a Conditional event at a NextEvent gap. `nextgap.k` runs `go(B)` to `mid(B)`, then
/// `mid(B) => fin requires B`, then `fin => halt`. Under Z3 the run splits into the path that
/// reaches `halt` (path condition B) and a stuck remainder at `mid(B)` (not B). On the first,
/// `goMid` (step 0) and `finHalt` (step 2) are Certain and `midFin` (step 1, declared on
/// `mid(true)`) is Conditional{B = true}. `goMid NextEvent finHalt` must skip the Conditional
/// event, so its only candidate is indeterminate and the plan is Unknown: never Match (the
/// skip needs the event's absence, which no instance of that path has) and never NoMatch. The
/// controls decide: `goMid EventuallyAfter finHalt` and `midFin NextEvent finHalt` (whose
/// Conditional relation is feasible on that path) are Match. Without Z3 the condition is
/// undecided: one Indeterminate leaf at `mid(B)` after `goMid`, so every plan is Unknown.
#[test]
fn audit_so_at3_conditional_event_at_a_next_event_gap_is_unknown() {
    use kink_pattern::{PatternOutcome, Relation};
    let validator = NativeValidator::bind(support::load("nextgap.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("nextgap compiles");
    let bool_var = || support::var("B", "SortBool");
    let truth = Pattern::DomainValue {
        sort: kore_sort("SortBool"),
        value: "true".into(),
    };
    let specs = vec![
        whole_step(
            "goMid",
            app("Lblgo", vec![bool_var()]),
            app("Lblmid", vec![bool_var()]),
            &[],
        ),
        whole_step(
            "midFin",
            app("Lblmid", vec![truth]),
            app("Lblfin", vec![]),
            &[],
        ),
        whole_step(
            "finHalt",
            app("Lblfin", vec![]),
            app("Lblhalt", vec![]),
            &[],
        ),
    ];
    let vocabulary = StepObservation::vocabulary_of(&specs).expect("vocabulary");
    let state = support::initial_state(
        app("Lblgo", vec![support::var("X", "SortBool")]),
        "SortProg",
    );
    let (bridged, mut backend) = bridged_for(&side, "NEXTGAP", &state, specs);
    let events = bridged
        .paths
        .iter()
        .map(|path| {
            path.events
                .iter()
                .map(|event| (event.constructor.clone(), event.presence.clone()))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    eprintln!(
        "SO-AT3 events: {events:?}; collection {:?}",
        bridged.collection
    );
    let context = kink_pattern::EvaluationContext {
        test_id: "audit".into(),
        bounds: BUDGET.bounds(),
        vocabulary: vocabulary.clone(),
        symbol_sorts: SymbolSorts::from_definition(
            &parse_definition(&side.artifacts().definition_kore).expect("compiled KORE parses"),
        ),
    };
    let outcomes = backend
        .with_solver(None, |definition, solver| {
            let relations =
                BackendRelations::shared(definition, solver, TestInitialState::of_test(&state));
            Ok::<_, k_rust::backend::BackendError>(
                [
                    (["goMid", "finHalt"], Relation::NextEvent),
                    (["goMid", "finHalt"], Relation::EventuallyAfter),
                    (["midFin", "finHalt"], Relation::NextEvent),
                ]
                .map(|(constructors, relation)| {
                    kink_pattern::evaluate_with(
                        &context,
                        &chain_plan(&vocabulary, &constructors, relation),
                        &bridged.paths,
                        &bridged.collection,
                        None,
                        kink_pattern::EvaluationOptions {
                            stable_path_keys: true,
                            search_policy: kink_pattern::SearchPolicy::Exhaustive,
                            input_error: false,
                        },
                        &relations,
                    )
                    .expect("evaluation")
                    .outcome
                }),
            )
        })
        .expect("relations");
    eprintln!("SO-AT3 outcomes: {outcomes:?}");
    let conditional = |relations: Vec<TermRelation>| EventPresence::Conditional(relations);
    if cfg!(feature = "z3") {
        assert!(events.contains(&vec![
            ("goMid".to_owned(), EventPresence::Certain),
            (
                "midFin".to_owned(),
                conditional(vec![TermRelation {
                    left: support::var("X", "SortBool"),
                    right: Pattern::DomainValue {
                        sort: kore_sort("SortBool"),
                        value: "true".into(),
                    },
                }])
            ),
            ("finHalt".to_owned(), EventPresence::Certain),
        ]));
        assert_eq!(
            outcomes,
            [
                PatternOutcome::Unknown,
                PatternOutcome::Match,
                PatternOutcome::Match
            ]
        );
    } else {
        assert_eq!(events, [vec![("goMid".to_owned(), EventPresence::Certain)]]);
        assert_eq!(outcomes, [PatternOutcome::Unknown; 3]);
    }
}

/// SO-AT7 (documented as intended, README 4.3 and SO-R2): a whole-transition `memoryLoad`
/// (`seq(load(addr(A), V), P) -> P`) fires on guardedmem's `loadFault` step when the
/// continuation P is itself `fault`, because that step has the same (pre, post) as a successful
/// load. W certifies "the step went to its continuation", not "the operation succeeded". The
/// same faulting load before `halt` emits nothing, and a successful load before `fault` emits
/// the same event. Ground, so identical in both profiles.
#[test]
fn audit_so_at7_whole_load_fires_on_a_fault_continuation() {
    let program = |address: i64, continuation: &str| {
        support::initial_state(
            app(
                "Lblseq",
                vec![
                    app(
                        "Lblload",
                        vec![app("Lbladdr", vec![support::int(address)]), support::int(7)],
                    ),
                    app(continuation, vec![]),
                ],
            ),
            "SortProg",
        )
    };
    let presences = |address, continuation| {
        event_presences(
            "guardedmem.k",
            "GUARDEDMEM",
            &program(address, continuation),
            step_support::guardedmem(true),
        )
    };
    assert_eq!(presences(-1, "Lblfault"), [certain(&["memoryLoad"])]);
    assert_eq!(presences(-1, "Lblhalt"), [Vec::new()]);
    assert_eq!(presences(1, "Lblfault"), [certain(&["memoryLoad"])]);
}

/// Attack (b) of the k-rust 927b9ce6 intake (decision D-B, T-UNSAT): steps from a state whose
/// path condition holds a partial `/Int` under a negation. `partialstep.k`'s `same(X, Y)` steps
/// to `halt` where `X /Int Y <=Int X /Int Y` holds and otherwise (owise) to `other(X, Y)`, then to
/// `done(Y)`; `pos(X, Y)` likewise under `X /Int Y >Int 0`. The owise path has the K instances
/// Y = 0 (the division is undefined there); for `same` it has no other. Read with `/Int` total
/// and without the definedness inside the negation, its condition would be refuted, and every
/// event on it Absent. Measured with Z3: on the owise path `otherZero` (`other(A, 0)`) and
/// `doneZero` (`other(A, B) -> done(0)`) are Conditional{Y = 0}, never Absent, the leaf is kept
/// (not discarded), and the relation query at the instance Y = 0 is not Unsat (it is Unknown:
/// `/Int` does not translate exactly). `same`'s applied path (condition Y =/=Int 0) refutes
/// Y = 0 and decides Y = 1. Without Z3 each run is one Indeterminate leaf at the initial state:
/// no step, no event, and no Unsat (the path is `SolverUnknown`, so no query is decided).
#[test]
fn audit_so_partial_condition_events_are_never_refuted() {
    use kink_pattern::Feasibility::{Sat, Unknown, Unsat};
    let validator =
        NativeValidator::bind(support::load("partialstep.k"), CompileOptions::default());
    let side = validator.compile_baseline().expect("partialstep compiles");
    let int = |name: &str| support::var(name, "SortInt");
    let specs = vec![
        whole_step(
            "toOther",
            app("Lblsame", vec![int("A"), int("B")]),
            app("Lblother", vec![int("A"), int("B")]),
            &["B"],
        ),
        whole_step(
            "toOther",
            app("Lblpos", vec![int("A"), int("B")]),
            app("Lblother", vec![int("A"), int("B")]),
            &["B"],
        ),
        bare_spec(
            support::k_config(
                app("Lblother", vec![int("A"), support::int(0)]),
                "SortProg",
                "R",
                "C",
            ),
            &["A"],
        ),
        whole_step(
            "doneZero",
            app("Lblother", vec![int("A"), int("B")]),
            app("Lbldone", vec![support::int(0)]),
            &["A"],
        ),
    ];
    let y_is = |value| {
        vec![TermRelation {
            left: int("Y"),
            right: support::int(value),
        }]
    };
    for head in ["Lblsame", "Lblpos"] {
        let state = support::initial_state(app(head, vec![int("X"), int("Y")]), "SortProg");
        let stepped = run_steps(&side, "PARTIALSTEP", &state);
        assert!(
            stepped.adapted.leaves().iter().all(|leaf| leaf.feasibility
                != kink_native::feasibility::LeafFeasibility::Unsat
                && kink_native::bridge::discarded(leaf).is_none()),
            "{head}: a leaf is refuted"
        );
        let (bridged, mut backend) = bridged_for(&side, "PARTIALSTEP", &state, specs.clone());
        let rows = backend
            .with_solver(None, |definition, solver| {
                let relations =
                    BackendRelations::shared(definition, solver, TestInitialState::of_test(&state));
                Ok::<_, k_rust::backend::BackendError>(
                    bridged
                        .paths
                        .iter()
                        .map(|path| {
                            (
                                path.events
                                    .iter()
                                    .map(|event| {
                                        (event.constructor.clone(), event.presence.clone())
                                    })
                                    .collect::<Vec<_>>(),
                                relations.feasible(path, &y_is(0)),
                                relations.feasible(path, &y_is(1)),
                            )
                        })
                        .collect::<Vec<_>>(),
                )
            })
            .expect("relations");
        eprintln!("SO-09 (b) {head}: {rows:?}");
        if cfg!(feature = "z3") {
            let zero = || EventPresence::Conditional(y_is(0));
            let owise = (
                vec![
                    ("toOther".to_owned(), EventPresence::Certain),
                    ("tick".to_owned(), zero()),
                    ("doneZero".to_owned(), zero()),
                ],
                Unknown,
                Unknown,
            );
            let expected = if head == "Lblsame" {
                vec![(Vec::new(), Unsat, Sat), owise]
            } else {
                vec![(Vec::new(), Unknown, Unknown), owise]
            };
            assert_eq!(rows, expected, "{head}");
        } else {
            assert_eq!(rows, [(Vec::new(), Unknown, Unknown)], "{head}");
        }
        assert!(
            rows.iter()
                .filter(|(events, ..)| events.len() > 1)
                .all(|(_, at_zero, _)| *at_zero != Unsat),
            "{head}: the owise path's K instance is refuted"
        );
    }
}

/// Hand-written KORE (the VI-06 AT13 definition, `feasibility.rs`): `tag` is an `anywhere`
/// head without a declared `function` (`HeadRole::EquationHead`), with equations collapsing
/// `tag(s(z))` to `tag(z)` and to `tag(s(s(z)))`; `f` is a partial function and `g` a total one
/// with `g(z) = z`; `pair` is a free constructor and plays the configuration here.
const EQUATION_HEADS: &str = r#"[]
    module MAIN
        sort SortNat{} []
        symbol Lblz{}() : SortNat{} [constructor{}(), functional{}()]
        symbol Lbls{}(SortNat{}) : SortNat{} [constructor{}(), functional{}()]
        symbol Lblpair{}(SortNat{}, SortNat{}) : SortNat{} [constructor{}(), functional{}()]
        symbol Lbltag{}(SortNat{}) : SortNat{} [functional{}(), injective{}(), anywhere{}()]
        symbol Lblf{}(SortNat{}) : SortNat{} [function{}()]
        symbol Lblg{}(SortNat{}) : SortNat{} [function{}(), functional{}()]
        axiom{R} \implies{R}(
            \and{R}(
                \top{R}(),
                \and{R}(\in{SortNat{}, R}(X0:SortNat{}, Lbls{}(Lblz{}())), \top{R}())
            ),
            \equals{SortNat{}, R}(
                Lbltag{}(X0:SortNat{}),
                \and{SortNat{}}(Lbltag{}(Lblz{}()), \top{SortNat{}}())
            )
        ) [label{}("t1"), anywhere{}()]
        axiom{R} \implies{R}(
            \and{R}(
                \top{R}(),
                \and{R}(\in{SortNat{}, R}(X0:SortNat{}, Lbls{}(Lblz{}())), \top{R}())
            ),
            \equals{SortNat{}, R}(
                Lbltag{}(X0:SortNat{}),
                \and{SortNat{}}(Lbltag{}(Lbls{}(Lbls{}(Lblz{}()))), \top{SortNat{}}())
            )
        ) [label{}("t2"), anywhere{}()]
        axiom{R} \implies{R}(
            \and{R}(
                \top{R}(),
                \and{R}(\in{SortNat{}, R}(X0:SortNat{}, Lblz{}()), \top{R}())
            ),
            \equals{SortNat{}, R}(
                Lblg{}(X0:SortNat{}),
                \and{SortNat{}}(Lblz{}(), \top{SortNat{}}())
            )
        ) [label{}("g-z")]
    endmodule []"#;

/// A real-prefix path with predicate `\top`, so relations and queries are asked at all.
fn top_path(sort: &str) -> PathInput {
    PathInput {
        test_id: "audit".into(),
        path_ordinal: 0,
        path_key: None,
        complete: true,
        stop: kink_pattern::PathStop::Terminal,
        execution_stop: kink_pattern::ExecutionStop::Terminal,
        execution_terminal: None,
        events: Vec::new(),
        path_predicate: Pattern::Top {
            sort: kore_sort(sort),
        },
        equivalences: Vec::new(),
        inequalities: Vec::new(),
    }
}

/// Attack (d) of the k-rust 927b9ce6 intake (AT13 at the step level): an `anywhere` head
/// (`HeadRole::EquationHead`) in a decoded state. The walk never decomposes or clashes a
/// non-free head, so a declaration whose pattern meets `tag(..)` with another `tag(..)` or with a
/// free constructor is Undecided, never Absent; a repeated variable bound to two different
/// `tag` applications goes to the shared relation, which is Indeterminate (Undecided) unless
/// k-rust decomposes both as normal on every instance (`tag(z)` against `tag(s(s(z)))` was both
/// normal, Unequal, Absent at 927b9ce6, and is Indeterminate at 501f18b9); identical applications are Equal by identity (Certain); and a
/// payload bound to a `tag` application is Certain but not definition independent, so a
/// `with_bindings` slot over it is Unknown (SO-D4). Same in both profiles (no solver query).
#[test]
fn audit_so_equation_heads_stay_undecided_in_steps() {
    let mut backend =
        Backend::new(EQUATION_HEADS, "MAIN", BackendOptions::default()).expect("backend");
    let nat = |name: &str| support::var(name, "SortNat");
    let z = || app("Lblz", vec![]);
    let s = |value| app("Lbls", vec![value]);
    let tag = |value| app("Lbltag", vec![value]);
    let pair = |left, right| app("Lblpair", vec![left, right]);
    let initial = pair(nat("X"), nat("Y"));
    let spec = |pre: Pattern, payload: &[&str]| StepEventSpec {
        constructor: "probe".into(),
        pre,
        post: None,
        payload: payload.iter().map(|name| (*name).into()).collect(),
    };
    let rows = [
        (spec(pair(tag(z()), nat("P")), &[]), pair(tag(s(z())), z())),
        (spec(pair(s(nat("N")), nat("P")), &[]), pair(tag(z()), z())),
        (spec(pair(tag(nat("N")), nat("P")), &[]), pair(z(), z())),
        (
            spec(pair(nat("V"), nat("V")), &[]),
            pair(tag(s(z())), tag(z())),
        ),
        (
            spec(pair(nat("V"), nat("V")), &[]),
            pair(tag(nat("X")), tag(z())),
        ),
        (
            spec(pair(nat("V"), nat("V")), &[]),
            pair(tag(z()), tag(s(s(z())))),
        ),
        (
            spec(pair(nat("V"), nat("V")), &[]),
            pair(tag(nat("X")), tag(nat("X"))),
        ),
        (spec(pair(nat("P"), nat("Q")), &["P"]), pair(tag(z()), z())),
    ];
    let (presences, independent) = backend
        .with_solver(None, |definition, solver| {
            let decider =
                ObservationDecider::new(definition, solver, TestInitialState::of_test(&initial));
            let path = top_path("SortNat");
            Ok::<_, k_rust::backend::BackendError>((
                rows.iter()
                    .map(|(spec, state)| decider.classify_step(spec, state, None, &path))
                    .collect::<Vec<_>>(),
                [tag(z()), tag(nat("X")), s(z())].map(|term| decider.definition_independent(&term)),
            ))
        })
        .expect("decider");
    eprintln!("SO-09 (d): {presences:?} {independent:?}");
    assert_eq!(
        presences,
        [
            StepPresence::Undecided,
            StepPresence::Undecided,
            StepPresence::Undecided,
            StepPresence::Undecided,
            StepPresence::Undecided,
            // Re-pin R0a (finding E-14; k-rust instance_normal.rs 216849c33, 22b9d5a07): at
            // 927b9ce6 k-rust decomposed `tag(z)` and `tag(s(s(z)))` as normal (Unequal, Absent);
            // at 501f18b9 the shared relation is Indeterminate, so the row is Undecided
            // (a lost decision, fail-closed).
            StepPresence::Undecided,
            StepPresence::Certain(Vec::new()),
            StepPresence::Certain(vec![tag(z())]),
        ]
    );
    assert_eq!(independent, [false, false, true]);
}

/// Attack (e) of the k-rust 927b9ce6 intake (T-CLASH, T-FREE): k-rust's unification evidence is
/// re-checked by kink's own criteria in the shared relations. Free constructors clash
/// (`s(X)` against `z`: Unequal) and a variable below free constructors is an occurs-check
/// clash (`X` against `s(X)`: Unequal). A k-rust `HeadClash` between an `EquationHead` normal
/// form and a constructor (`tag(z)` against `s(z)`, `tag(z)` against `z`) is not accepted: kink
/// requires both roots free (or free against an injection), so it is Indeterminate; nor is a
/// cycle through a non-free head (`X` against `tag(s(X))`, `X` against `g(s(X))`). Sort
/// injections with incomparable sources (`subsort_steps.k`: `inj{Small,Large}(a)` against
/// `inj{Other,Large}(b)`) give k-rust's sort evidence, which kink never counts as a clash
/// (Indeterminate; the step walk decides that pair itself, by `free_top`, in
/// `injections_match_modulo_subsorts`). `ArgumentLengthsDiffer` is not expressible: both sides
/// internalize against one symbol table, which checks arity first. Exactness (a solver Sat
/// counts only when `translation_exactness` is `Exact`) is pinned by `feasibility.rs`
/// `solver_sat_counts_only_for_the_exact_relation_query` and `symbolic.rs`
/// `z3_sat_on_abstracted_query_is_not_a_witness`. Same in both profiles.
#[test]
fn audit_so_unification_evidence_is_rechecked_by_kink() {
    use RelationDecision::{Indeterminate, Unequal};
    let mut backend =
        Backend::new(EQUATION_HEADS, "MAIN", BackendOptions::default()).expect("backend");
    let nat = |name: &str| support::var(name, "SortNat");
    let z = || app("Lblz", vec![]);
    let s = |value| app("Lbls", vec![value]);
    let tag = |value| app("Lbltag", vec![value]);
    let g = |value| app("Lblg", vec![value]);
    let initial = app("Lblpair", vec![nat("X"), nat("Y")]);
    let heads = backend
        .with_solver(None, |definition, solver| {
            let relations =
                BackendRelations::shared(definition, solver, TestInitialState::of_test(&initial));
            let path = top_path("SortNat");
            Ok::<_, k_rust::backend::BackendError>(
                [
                    (s(nat("X")), z()),
                    (nat("X"), s(nat("X"))),
                    (tag(z()), s(z())),
                    (tag(z()), z()),
                    (nat("X"), tag(s(nat("X")))),
                    (nat("X"), g(s(nat("X")))),
                ]
                .map(|(left, right)| relations.relate(&path, &[], &left, &right)),
            )
        })
        .expect("relations");
    eprintln!("SO-09 (e) heads: {heads:?}");
    assert_eq!(
        heads,
        [
            Unequal,
            Unequal,
            Indeterminate,
            Indeterminate,
            Indeterminate,
            Indeterminate
        ]
    );

    let validator =
        NativeValidator::bind(support::load("subsort_steps.k"), CompileOptions::default());
    let side = validator
        .compile_baseline()
        .expect("subsort fixture compiles");
    let inj = |source: &str, value| {
        k_rust::kompile::initial_configuration::kore_application(
            "inj",
            vec![kore_sort(source), kore_sort("SortLarge")],
            vec![value],
        )
    };
    let initial = support::initial_state(
        app("Lblstep", vec![support::var("L", "SortLarge")]),
        "SortProg",
    );
    let mut backend = Backend::new(
        &side.artifacts().definition_kore,
        "SUBSORT'Unds'STEPS",
        BackendOptions::default(),
    )
    .expect("backend");
    let sorts = backend
        .with_solver(None, |definition, solver| {
            let relations =
                BackendRelations::shared(definition, solver, TestInitialState::of_test(&initial));
            let path = top_path("SortGeneratedTopCell");
            Ok::<_, k_rust::backend::BackendError>(
                [
                    (
                        inj("SortSmall", app("Lbla", vec![])),
                        inj("SortOther", app("Lblb", vec![])),
                    ),
                    (inj("SortSmall", app("Lbla", vec![])), app("Lblc", vec![])),
                ]
                .map(|(left, right)| relations.relate(&path, &[], &left, &right)),
            )
        })
        .expect("relations");
    eprintln!("SO-09 (e) sorts: {sorts:?}");
    assert_eq!(sorts, [Indeterminate, Unequal]);
}
