use std::path::PathBuf;

use k_rust::{
    backend::{Backend, BackendOptions},
    kompile::CompileOptions,
    kore::{codec::to_value, parser::parse_definition},
};
use kink_corpus::{
    CorpusSource, InputError, LoadedSource, ProgramSource, TestInputSpec, assemble_input,
    assemble_input_with, load_source,
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

mod kink_tier {
    use super::*;

    /// Re-pin L1-4: assembling with the caller's compile of the baseline gives what assembling with
    /// a compile of its own gives, inputs and refusals alike; a compile of another definition is not
    /// used (the input is assembled with a compile of its own, so its configuration is its own).
    #[test]
    #[ignore = "kink"]
    fn assembling_with_the_callers_compile_is_assembling_alone() {
        let compile = |loaded: &LoadedSource| {
            NativeValidator::bind(loaded.baseline.clone(), CompileOptions::default())
                .compile_baseline()
                .unwrap()
        };
        let variables = load("variables.k", "VARIABLES");
        let program = load("program.k", "PROGRAM");
        let streams = load("streams.k", "STREAMS");
        // One compile of each definition (packet test-gate TG-P: before, one per row).
        let variables_compile = compile(&variables);
        let program_compile = compile(&program);
        let streams_compile = compile(&streams);
        let mut bound = spec();
        bound.variables.push(("N".into(), "42".into()));
        let mut ill_sorted = bound.clone();
        ill_sorted.variables[0].1 = "true".into();
        let mut at_k = spec();
        at_k.start_sort = Some("K".into());
        let value = |state: Result<k_rust::kore::ast::Pattern, InputError>| {
            state.map(|state| to_value(&state).unwrap())
        };
        for (loaded, compiled, input) in [
            (&variables, &variables_compile, spec()),
            (&variables, &variables_compile, bound.clone()),
            (&variables, &variables_compile, ill_sorted),
            (&program, &program_compile, spec()),
            (&program, &program_compile, at_k),
            (&streams, &streams_compile, spec()),
        ] {
            let alone = value(assemble_input(loaded, &input));
            assert_eq!(
                value(assemble_input_with(loaded, Some(compiled), &input)),
                alone
            );
            assert_eq!(value(assemble_input_with(loaded, None, &input)), alone);
        }
        // A compile of another definition (program.k's) is not taken for variables.k: $N is still
        // required and bound as variables.k declares it.
        assert_eq!(
            value(assemble_input_with(
                &variables,
                Some(&program_compile),
                &bound
            )),
            value(assemble_input(&variables, &bound))
        );
        assert!(matches!(
            assemble_input_with(&variables, Some(&program_compile), &spec()),
            Err(InputError::MissingVariable(_))
        ));
    }
}
