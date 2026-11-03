use std::path::PathBuf;

use k_rust::{
    backend::{Backend, BackendOptions},
    kompile::CompileOptions,
    kore::{codec::to_value, parser::parse_definition},
};
use kink_corpus::{
    CorpusSource, InputAssembler, InputError, InputGrammar, LoadedSource, ProgramSource,
    TestInputSpec, VariableInput, assemble_input, assemble_input_with, load_source,
};
use kink_native::{NativeValidator, bridge::validate_test_initial_state};

fn load(entry: &str, main: &str) -> LoadedSource {
    load_with_syntax(entry, main, main)
}

fn load_with_syntax(entry: &str, main: &str, syntax: &str) -> LoadedSource {
    load_source(&CorpusSource {
        root: PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/corpus"),
        entry: entry.into(),
        include_dirs: vec![],
        main_module: main.into(),
        syntax_module: Some(syntax.into()),
        md_selector: None,
    })
    .unwrap()
}

fn spec() -> TestInputSpec {
    TestInputSpec {
        program: Some(ProgramSource::Text("true".into())),
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

/// KINK-CENSUS-RUNLIST (fz26): on a definition with stream cells a program may not bind `$IO`
/// (`stream-mode`), whatever the text, written with or without its `$`; it may bind `$STDIN`. A
/// definition without stream cells that declares its own `$IO` may bind it. At base every binding
/// here was accepted.
#[test]
fn an_io_binding_on_a_stream_definition_is_refused() {
    let streams = load("streams.k", "STREAMS");
    for (name, text) in [("IO", "\"on\""), ("$IO", "\"on\""), ("IO", "\"off\"")] {
        let mut input = spec();
        input.variables.push((name.into(), text.into()));
        let refused = assemble_input(&streams, &input);
        assert!(
            matches!(&refused, Err(InputError::StreamMode(message)) if message.contains("stream cells")),
            "{name} = {text}: {refused:?}"
        );
    }
    let mut stdin = spec();
    stdin.variables.push(("STDIN".into(), "\"5\\n\"".into()));
    validate(&streams, &assemble_input(&streams, &stdin).unwrap());
    let own = load("ioparam.k", "IOPARAM");
    let mut input = spec();
    input.variables.push(("IO".into(), "\"on\"".into()));
    let state = assemble_input(&own, &input).unwrap();
    validate(&own, &state);
    assert!(to_value(&state).unwrap().to_string().contains("on"));
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
    file.program = Some(ProgramSource::File("true.test".into()));
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
    input.program = Some(ProgramSource::File("../program.k".into()));
    assert!(matches!(
        assemble_input(&loaded, &input),
        Err(InputError::Parse(_))
    ));
}

/// One `InputAssembler` serves every program of its definition: each result, an initial state
/// or a refusal, is the one a fresh assembly gives, also right after a program whose
/// configuration was abandoned on an error after its program was bound (the `true` value of
/// `$N`, the `$IO` binding on a stream definition). The assembler is cleared before each program;
/// without that the program after an abandoned one would be refused as a second `$PGM`.
#[test]
fn one_assembler_assembles_what_assemble_input_does() {
    let with_variables = |variables: &[(&str, &str)]| TestInputSpec {
        variables: variables
            .iter()
            .map(|(name, text)| ((*name).into(), (*text).into()))
            .collect(),
        ..spec()
    };
    for (loaded, inputs) in [
        (
            load("variables.k", "VARIABLES"),
            vec![
                with_variables(&[]),
                with_variables(&[("N", "42")]),
                with_variables(&[("N", "true")]),
                with_variables(&[("N", "7")]),
            ],
        ),
        (
            load("streams.k", "STREAMS"),
            vec![
                with_variables(&[("IO", "\"on\"")]),
                with_variables(&[("STDIN", "\"5\\n\"")]),
            ],
        ),
    ] {
        let compiled = NativeValidator::bind(loaded.baseline.clone(), CompileOptions::default())
            .compile_baseline()
            .unwrap();
        let grammar = InputGrammar::prepare(&loaded, Some(&compiled)).unwrap();
        let mut assembler = InputAssembler::new(&grammar);
        let mut refusals = 0;
        for input in &inputs {
            let Some(ProgramSource::Text(text)) = &input.program else {
                unreachable!("every program here is a text")
            };
            let fresh = assemble_input_with(&loaded, Some(&compiled), input);
            refusals += usize::from(fresh.is_err());
            assert_eq!(
                assembler.assemble(Some((text, input.start_sort.as_deref())), &input.variables),
                fresh,
                "{:?}",
                input.variables
            );
        }
        assert!(refusals > 0 && refusals < inputs.len(), "{inputs:?}");
    }
}

/// A definition without `$PGM` takes no program: its test binds every configuration variable by
/// name. A program text given to it would bind nothing, so it is refused (`stray-program`),
/// naming `$PGM` and every declared variable with its sort; a program-less test of a definition
/// that declares `$PGM` is refused as missing it.
#[test]
fn a_definition_without_pgm_takes_no_program() {
    let loaded = load("nopgm.k", "NOPGM");
    let bare = TestInputSpec {
        program: None,
        start_sort: None,
        variables: vec![("ENTRY".into(), "true".into()), ("N".into(), "7".into())],
    };
    let state = assemble_input(&loaded, &bare).unwrap();
    validate(&loaded, &state);
    let json = to_value(&state).unwrap().to_string();
    assert!(json.contains("$ENTRY") && json.contains("$N"), "{json}");
    assert!(!json.contains("$PGM"), "{json}");
    let stray = TestInputSpec {
        program: Some(ProgramSource::Text("true".into())),
        ..bare.clone()
    };
    match assemble_input(&loaded, &stray) {
        Err(InputError::StrayProgram(message)) => assert_eq!(
            message,
            "the definition declares no $PGM, so a program text binds nothing; bind its \
             configuration variables by name: $ENTRY:K, $N:Int"
        ),
        other => panic!("{other:?}"),
    }
    assert_eq!(
        kink_corpus::admission::input_refusal(InputError::StrayProgram(String::new())).reason,
        "stray-program"
    );
    let with_pgm = load("program.k", "PROGRAM");
    assert!(matches!(
        assemble_input(
            &with_pgm,
            &TestInputSpec {
                program: None,
                start_sort: None,
                variables: vec![],
            }
        ),
        Err(InputError::MissingVariable(message)) if message.contains("$PGM")
    ));
}

/// A variable bound to a KAST term built without the parser gives the initial configuration the
/// same variable's text gives: the term is typed and macro-expanded as a parsed value is. A term
/// whose sort is not at most the variable's is refused, as ill-sorted text is.
#[test]
fn a_term_binding_is_the_text_binding() {
    let loaded = load("variables.k", "VARIABLES");
    let mut text = spec();
    text.variables.push(("N".into(), "42".into()));
    let mut term = spec();
    term.variables.push((
        "N".into(),
        VariableInput::Term(k_rust::kast::Term::Token {
            token: "42".into(),
            sort: k_rust::kast::Sort::new("Int"),
        }),
    ));
    let state = assemble_input(&loaded, &term).unwrap();
    validate(&loaded, &state);
    assert_eq!(
        to_value(&state).unwrap(),
        to_value(&assemble_input(&loaded, &text).unwrap()).unwrap()
    );
    let mut ill_sorted = spec();
    ill_sorted.variables.push((
        "N".into(),
        VariableInput::Term(k_rust::kast::Term::Token {
            token: "true".into(),
            sort: k_rust::kast::Sort::new("Bool"),
        }),
    ));
    assert!(
        matches!(
            assemble_input(&loaded, &ill_sorted),
            Err(InputError::Assemble(_))
        ),
        "{:?}",
        assemble_input(&loaded, &ill_sorted)
    );
}

/// kink reads a configuration variable's text as krs-exec does (k-rust
/// `variable_reading_modules`): with the syntax module's grammar first wherever it has the
/// variable's sort, so `word` given for a `Word` variable is that `Word`, although the main
/// module's grammar, whose token sort `Name` the scanner prefers, reads it as a `Name`; a sort
/// only the main module has (`Name`) is read with its grammar. Read with the main module alone,
/// `word` at `Word` would not parse.
#[test]
fn variables_read_as_krs_exec_reads_them() {
    let loaded = load_with_syntax("tokens.k", "TOKENS", "TOKENS-SYNTAX");
    let input = TestInputSpec {
        program: Some(ProgramSource::Text("run".into())),
        start_sort: None,
        variables: vec![("W".into(), "word".into()), ("N".into(), "word".into())],
    };
    let state = assemble_input(&loaded, &input).unwrap();
    validate(&loaded, &state);
    let kore = state.to_string();
    for value in [r#"\dv{SortWord{}}("word")"#, r#"\dv{SortName{}}("word")"#] {
        assert!(kore.contains(value), "{value}: {kore}");
    }
}

/// A term bound to `$PGM` is a program built without the parser: the test it gives is the one
/// the same program's text gives. With a program text as well, `$PGM` is bound twice, which is
/// refused.
#[test]
fn a_term_binds_pgm_as_its_program_text_does() {
    let loaded = load("program.k", "PROGRAM");
    let term = VariableInput::Term(k_rust::kast::Term::Token {
        token: "true".into(),
        sort: k_rust::kast::Sort::new("Bool"),
    });
    let typed = TestInputSpec {
        program: None,
        start_sort: None,
        variables: vec![("PGM".into(), term.clone())],
    };
    let state = assemble_input(&loaded, &typed).unwrap();
    validate(&loaded, &state);
    assert_eq!(
        to_value(&state).unwrap(),
        to_value(&assemble_input(&loaded, &spec()).unwrap()).unwrap()
    );
    let mut twice = spec();
    twice.variables.push(("$PGM".into(), term));
    assert!(
        matches!(assemble_input(&loaded, &twice), Err(InputError::Assemble(ref message)) if message.contains("PGM")),
        "{:?}",
        assemble_input(&loaded, &twice)
    );
}

/// The reading krun's `-c` gives (and a k-rust-fuzz campaign's assembly): every variable's text
/// read with the main module's grammar alone. On `tokens.k` only `$W` (a sort of the syntax
/// module) is read with the syntax module first, and with the main module alone `word` at `Word`
/// does not parse, since the main module's scanner reads it as a `Name`.
#[test]
fn the_main_module_reading_is_the_reading_krun_gives() {
    let loaded = load_with_syntax("tokens.k", "TOKENS", "TOKENS-SYNTAX");
    let grammar = InputGrammar::prepare(&loaded, None).unwrap();
    assert_eq!(grammar.syntax_read_variables().collect::<Vec<_>>(), ["W"]);
    let variables = |w: &str| -> Vec<(String, VariableInput)> {
        vec![("W".into(), w.into()), ("N".into(), "word".into())]
    };
    let mut krun = InputAssembler::reading_with_main_module(&grammar);
    assert!(matches!(
        krun.assemble(Some(("run", None)), &variables("word")),
        Err(InputError::Parse(_))
    ));
    // A text both grammars read as one term gives one configuration.
    let mut kink = InputAssembler::new(&grammar);
    assert_eq!(
        krun.assemble(Some(("run", None)), &variables("w")),
        kink.assemble(Some(("run", None)), &variables("w"))
    );
    assert!(
        kink.assemble(Some(("run", None)), &variables("word"))
            .is_ok()
    );
}

/// A program text on a definition that declares no configuration variable binds nothing, and so
/// does the case.
#[test]
fn a_program_on_a_definition_without_variables_is_stray() {
    let loaded = load("novars.k", "NOVARS");
    match assemble_input(&loaded, &spec()) {
        Err(InputError::StrayProgram(message)) => assert_eq!(
            message,
            "the definition declares no $PGM, so a program text binds nothing; it declares no \
             configuration variable either, so its case binds none"
        ),
        other => panic!("{other:?}"),
    }
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
