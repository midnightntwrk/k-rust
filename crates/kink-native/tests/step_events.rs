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
use kink_native::feasibility::BackendRelations;
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
    ExecutionAdapter::without_manifest(SolverProfile::BUILD)
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
    paths_for_with_flag(baseline, side, module, state, specs, false)
}

fn paths_for_with_flag(
    baseline: &ValidatedDefinition,
    side: &ValidatedDefinition,
    module: &str,
    state: &Pattern,
    specs: Vec<StepEventSpec>,
    existentials: bool,
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
            let decider = ObservationDecider::new(definition, solver, state, existentials);
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
    assert!(
        equality_steps.states[0]
            .iter()
            .any(|state| contains_domain_value(state, "SortBool", b"false"))
    );
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
            let decider = ObservationDecider::new(definition, solver, &state, false);
            assert!(matches!(
                decider.classify_step(&spec, &steps.states[0][0], Some(&steps.states[0][1]), &path),
                StepPresence::Undecided
            ));
            let relations = BackendRelations::shared(definition, solver, &state, false);
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
            let decider = ObservationDecider::new(definition, solver, &state, false);
            let spec = StepEventSpec {
                constructor: "probe".into(),
                pre: support::var("X", "SortGeneratedTopCell"),
                post: Some(support::var("X", "SortGeneratedTopCell")),
                payload: vec![],
            };
            assert_eq!(
                definition
                    .sorts
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
                    BackendRelations::shared(definition, solver, &state, false).relate(
                        &path,
                        &[],
                        &value,
                        &value
                    ),
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
            let decider = ObservationDecider::new(definition, solver, &state, false);
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
            let relations = BackendRelations::shared(definition, solver, &state, false);
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
        let before =
            paths_for_with_flag(&original, &original, "SYMMEM", &state, specs.clone(), true);
        let after = paths_for_with_flag(&original, &mutant, "SYMMEM", &state, specs, true);
        assert_eq!(before, after, "canonical PathInputs with pair existentials");

        let mut backend = Backend::new(
            &original.artifacts().definition_kore,
            "SYMMEM",
            BackendOptions::default(),
        )
        .expect("baseline backend");
        backend
            .with_solver(None, |definition, solver| {
                let decider = BackendRelations::shared(definition, solver, &state, true);
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
            let decider = ObservationDecider::new(definition, solver, &state, false);
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
            let decider = ObservationDecider::new(definition, solver, &state, false);
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
                let decider = ObservationDecider::new(definition, solver, &state, false);
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
            let decider = ObservationDecider::new(definition, solver, &state, false);
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
