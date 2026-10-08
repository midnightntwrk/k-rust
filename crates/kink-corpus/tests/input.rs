use std::path::PathBuf;

use k_rust::{
    backend::{Backend, BackendOptions},
    kompile::CompileOptions,
    kore::{codec::to_value, parser::parse_definition},
};
use kink_corpus::{
    CorpusSource, InputError, LoadedSource, ProgramSource, TestInputSpec, assemble_input,
    load_source,
};
use kink_native::{NativeValidator, bridge::validate_test_initial_state};

fn load(entry: &str, main: &str) -> LoadedSource {
    load_source(&CorpusSource {
        root: PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/corpus"),
        entry: entry.into(),
        include_dirs: vec![],
        main_module: main.into(),
        syntax_module: Some(main.into()),
        md_selector: None,
    })
    .unwrap()
}

fn spec() -> TestInputSpec {
    TestInputSpec {
        program: ProgramSource::Text("true".into()),
        start_sort: None,
        variables: vec![],
    }
}

fn validate(loaded: &LoadedSource, state: &k_rust::kore::ast::Pattern) {
    let compiled = NativeValidator::bind(loaded.baseline.clone(), CompileOptions::default())
        .compile_baseline()
        .unwrap();
    let module = k_rust::kast::identifier::encode(&loaded.baseline.definition().main_module);
    let mut backend = Backend::from_definition(
        parse_definition(&compiled.artifacts().definition_kore).unwrap(),
        module,
        BackendOptions::default(),
    )
    .unwrap();
    validate_test_initial_state(&mut backend, state).unwrap();
}

#[test]
fn program_at_kitem() {
    let loaded = load("program.k", "PROGRAM");
    let mut input = spec();
    let state = assemble_input(&loaded, &input).unwrap();
    validate(&loaded, &state);
    input.start_sort = Some("K".into());
    assert!(matches!(
        assemble_input(&loaded, &input),
        Err(InputError::Parse(_))
    ));
}

#[test]
fn streams_are_refused() {
    let loaded = load("streams.k", "STREAMS");
    let state = assemble_input(&loaded, &spec())
        .expect("the pin binds String-sorted IO and STDIN defaults");
    validate(&loaded, &state);
    let json = to_value(&state).unwrap().to_string();
    assert!(json.contains("$IO"));
    assert!(json.contains("$STDIN"));
    assert!(json.contains("off"));
}

#[test]
fn assembled_inputs_are_deterministic() {
    let left = load("program.k", "PROGRAM");
    let right = load("program.k", "PROGRAM");
    assert_eq!(
        to_value(&assemble_input(&left, &spec()).unwrap()).unwrap(),
        to_value(&assemble_input(&right, &spec()).unwrap()).unwrap()
    );
    let mut file = spec();
    file.program = ProgramSource::File("true.test".into());
    assert_eq!(
        to_value(&assemble_input(&left, &file).unwrap()).unwrap(),
        to_value(&assemble_input(&left, &spec()).unwrap()).unwrap()
    );
}

#[test]
fn configuration_variables_are_required_and_parsed() {
    let loaded = load("variables.k", "VARIABLES");
    let mut input = spec();
    assert!(
        matches!(assemble_input(&loaded, &input), Err(InputError::MissingVariable(name)) if name.contains("$N"))
    );
    input.variables.push(("N".into(), "42".into()));
    validate(&loaded, &assemble_input(&loaded, &input).unwrap());
    input.variables[0].1 = "true".into();
    assert!(matches!(
        assemble_input(&loaded, &input),
        Err(InputError::Parse(_))
    ));
}

#[test]
fn program_file_escape_is_refused() {
    let loaded = load("program.k", "PROGRAM");
    let mut input = spec();
    input.program = ProgramSource::File("../program.k".into());
    assert!(matches!(
        assemble_input(&loaded, &input),
        Err(InputError::Parse(_))
    ));
}
