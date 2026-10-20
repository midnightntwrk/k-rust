//! The library contract of `k_rust::krun`, the portable front half of `krust krun`: a
//! configuration assembled through it is the one krun builds for the same definition and inputs,
//! and the backend it builds runs it as krun does.

use std::{collections::BTreeMap, sync::Arc};

use k_rust::{
    builtin::embedded,
    definition::Definition,
    kast::{Sort, parser::parse_sort},
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ConfigurationError,
        ProgramGrammar, compile_loaded_definition,
    },
    kore::{ast::Pattern, printer::Printer},
    krun::{KrunDefinition, KrunInputs, ProgramText, buffered_stdin_bytes},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

#[path = "support/shared.rs"]
mod shared;

/// IMP of the K tutorial (`tests/fixtures/kink/imp-lesson-4.k`).
const IMP: &str = include_str!("fixtures/kink/imp-lesson-4.k");

/// A definition that declares, besides `$PGM`, an ordinary configuration variable and both
/// stream variables, so that the binding order and the stream defaults show in its configuration.
const STREAMS: &str = r#"
module STREAMS-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "go" Int
endmodule

module STREAMS
  imports STREAMS-SYNTAX
  imports DOMAINS
  configuration <T>
                  <k> $PGM:Pgm </k>
                  <n> $N:Int </n>
                  <in> $STDIN:String </in>
                  <io> $IO:String </io>
                </T>
  rule <k> go I => I +Int N ...</k> <n> N </n>
endmodule
"#;

const IMP_SUM: &str =
    "int n, sum; n = 10; sum = 0; while (!(n <= 0)) { sum = sum + n; n = n + -1; }";
const IMP_SHORT: &str = "int x; x = 3 + 4;";

struct Compiled {
    main_module: String,
    frontend: Definition,
    variables: BTreeMap<String, Sort>,
    rewrite_order: Vec<String>,
    kore: String,
}

impl Compiled {
    fn new(source: &str, main_module: &str) -> Self {
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("test.k", source),
            main_module,
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                ..CompilationBackend::Rust.load_options()
            },
        )
        .expect("definition should load");
        let artifacts = compile_loaded_definition(
            &loaded,
            CompileOptions {
                backend: CompilationBackend::Rust,
                ..CompileOptions::default()
            },
        )
        .expect("definition should compile");
        Self {
            main_module: main_module.to_owned(),
            frontend: loaded.into_definition(),
            variables: artifacts.configuration_variables,
            rewrite_order: artifacts.execution_rewrite_order,
            kore: artifacts.definition_kore,
        }
    }

    fn definition(&self) -> KrunDefinition<'_> {
        KrunDefinition {
            main_module: &self.main_module,
            syntax_module: &self.main_module,
            frontend_definition: &self.frontend,
            configuration_variables: &self.variables,
            execution_rewrite_order: &self.rewrite_order,
            definition_kore: &self.kore,
        }
    }
}

fn imp() -> Arc<Compiled> {
    static COMPILED: shared::Shared<Compiled> = shared::Shared::new();
    COMPILED.get(|| Compiled::new(IMP, "IMP"))
}

fn streams() -> Arc<Compiled> {
    static COMPILED: shared::Shared<Compiled> = shared::Shared::new();
    COMPILED.get(|| Compiled::new(STREAMS, "STREAMS"))
}

fn print(pattern: &Pattern) -> String {
    Printer::compact().print_pattern(pattern)
}

fn pgm() -> Sort {
    parse_sort("Pgm").unwrap()
}

fn no_input() -> Result<Vec<u8>, ConfigurationError> {
    Ok(Vec::new())
}

/// The configuration krun's steps build, written out against `ConfigurationAssembler`: the
/// program, the `-c` values in order, the stream defaults with `$STDIN` buffered, the assembly.
fn assembled_by_steps(
    grammar: &ProgramGrammar,
    compiled: &Compiled,
    program: &str,
    variables: &[(&str, &str)],
    (io, program_uses_input): (bool, bool),
    input: &[u8],
) -> Pattern {
    let mut assembler = ConfigurationAssembler::new(
        grammar,
        &compiled.main_module,
        &compiled.main_module,
        &compiled.variables,
    );
    assembler.program(&pgm(), program).unwrap();
    for (name, text) in variables {
        assembler.bind(name, text).unwrap();
    }
    assembler
        .bind_stream_defaults(io, program_uses_input, || {
            Ok::<_, ConfigurationError>(buffered_stdin_bytes(input.to_vec()))
        })
        .unwrap();
    assembler.finish().unwrap()
}

#[test]
fn assemble_takes_krun_steps_in_order() {
    let compiled = streams();
    let definition = compiled.definition();
    let grammar = definition.program_grammar().unwrap();
    let mut assembler = definition.assembler(&grammar);
    let sort = pgm();
    for io in [false, true] {
        let assembled = assembler
            .assemble(
                &KrunInputs {
                    start_sort: &sort,
                    program: Some(ProgramText::unnamed("go 4")),
                    configuration_variables: &[("N".to_owned(), "3".to_owned())],
                    io,
                },
                || Ok::<_, ConfigurationError>(b"abc\n\n".to_vec()),
            )
            .unwrap();
        let expected = assembled_by_steps(
            &grammar,
            &compiled,
            "go 4",
            &[("N", "3")],
            (io, false),
            b"abc\n\n",
        );
        assert_eq!(print(&assembled), print(&expected), "io = {io}");
        let text = print(&assembled);
        if io {
            assert!(text.contains(r#""on""#) && !text.contains("abc"), "{text}");
        } else {
            assert!(
                text.contains(r#""off""#) && text.contains(r#""abc\n""#),
                "{text}"
            );
        }
    }
}

#[test]
fn a_program_read_from_standard_input_leaves_stdin_empty() {
    let compiled = streams();
    let definition = compiled.definition();
    let grammar = definition.program_grammar().unwrap();
    let mut assembler = definition.assembler(&grammar);
    let sort = pgm();
    let program = ProgramText {
        text: "go 4",
        file: k_rust::inner::UNNAMED_PROGRAM,
        from_standard_input: true,
    };
    let assembled = assembler
        .assemble(
            &KrunInputs {
                start_sort: &sort,
                program: Some(program),
                configuration_variables: &[("$N".to_owned(), "3".to_owned())],
                io: false,
            },
            || -> Result<Vec<u8>, ConfigurationError> {
                panic!("standard input is the program and holds nothing for $STDIN")
            },
        )
        .unwrap();
    assert_eq!(
        print(&assembled),
        print(&assembled_by_steps(
            &grammar,
            &compiled,
            "go 4",
            &[("N", "3")],
            (false, true),
            b"unread",
        ))
    );
    assert!(print(&assembled).contains(r#""off""#));
}

#[test]
fn one_assembler_serves_many_programs_and_recovers_from_errors() {
    let compiled = imp();
    let definition = compiled.definition();
    let grammar = definition.program_grammar().unwrap();
    let mut assembler = definition.assembler(&grammar);
    let sort = pgm();
    let mut assemble = |program: &str| {
        assembler
            .assemble(
                &KrunInputs {
                    start_sort: &sort,
                    program: Some(ProgramText::unnamed(program)),
                    configuration_variables: &[],
                    io: false,
                },
                no_input,
            )
            .map(|pattern| print(&pattern))
    };
    let sum = assemble(IMP_SUM).unwrap();
    let short = assemble(IMP_SHORT).unwrap();
    assert_ne!(sum, short);
    assert!(matches!(
        assemble("int x; x = ;"),
        Err(ConfigurationError::Program(_))
    ));
    assert_eq!(assemble(IMP_SUM).unwrap(), sum);
    assert_eq!(
        sum,
        print(&assembled_by_steps(
            &grammar,
            &compiled,
            IMP_SUM,
            &[],
            (false, false),
            b""
        ))
    );
    // A missing program is reported, and leaves the assembler empty.
    let missing = assembler.assemble(
        &KrunInputs {
            start_sort: &sort,
            program: None,
            configuration_variables: &[],
            io: false,
        },
        no_input,
    );
    assert!(matches!(missing, Err(ConfigurationError::Missing { .. })));
    assert!(assembler.binds_program(false), "IMP declares $PGM");
}

#[test]
fn the_backend_is_built_on_the_rewrite_order_route() {
    let compiled = imp();
    let definition = compiled.definition();
    let syntax = definition.parse_kore().unwrap();
    // The route that takes the rewrite order is the one krun takes.
    definition.internalize(&syntax).unwrap();
    definition
        .backend(k_rust::backend::BackendOptions::default())
        .unwrap();
}

/// krun's output, at depth 0 (the initial configuration) and after the run, for compiled
/// definitions and inputs, equals the output of the run of the library's configuration on the
/// library's backend with krun's run options.
#[cfg(feature = "cli")]
mod cli {
    use std::{
        fs,
        path::{Path, PathBuf},
        process::{Command, Stdio},
    };

    use k_rust::{
        backend::{BackendOptions, execution::BackendRunOptions},
        inner::{UNNAMED_PROGRAM, program_file_name},
        k_rust_backend::{rewrite::ExecutionMode, simplify::DEFAULT_MAX_SIMPLIFICATION_ITERATIONS},
        kore::printer::Printer,
        krun::{KrunDefinition, KrunInputs, ProgramText},
        native::load_runnable_artifact,
    };

    use super::{IMP, IMP_SHORT, IMP_SUM, STREAMS, pgm};

    struct Case {
        program: &'static str,
        /// Whether the program is passed on standard input instead of in a file.
        program_on_stdin: bool,
        variables: &'static [(&'static str, &'static str)],
        stdin: &'static [u8],
    }

    fn directory(name: &str) -> PathBuf {
        let directory = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("krun-front-{}-{name}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        directory
    }

    fn krun(compiled: &Path, root: &Path, case: &Case, depth: Option<u64>) -> Vec<u8> {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command
            .arg("krun")
            .arg("--definition")
            .arg(compiled)
            .args(["--sort", "Pgm", "--io", "off", "--output", "kore"]);
        if let Some(depth) = depth {
            command.args(["--depth", &depth.to_string()]);
        }
        for (name, value) in case.variables {
            command.arg(format!("-c{name}={value}"));
        }
        let input = root.join("stdin");
        if case.program_on_stdin {
            fs::write(&input, case.program).unwrap();
        } else {
            let program = root.join("program.pgm");
            fs::write(&program, case.program).unwrap();
            command.arg(&program);
            fs::write(&input, case.stdin).unwrap();
        }
        command.stdin(Stdio::from(fs::File::open(&input).unwrap()));
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        output.stdout
    }

    fn library(
        definition: KrunDefinition<'_>,
        root: &Path,
        case: &Case,
        depth: Option<u64>,
    ) -> Vec<u8> {
        let grammar = definition.program_grammar().unwrap();
        let mut assembler = definition.assembler(&grammar);
        let file = program_file_name(&root.join("program.pgm"));
        let program = if case.program_on_stdin {
            ProgramText {
                text: case.program,
                file: UNNAMED_PROGRAM,
                from_standard_input: true,
            }
        } else {
            ProgramText {
                text: case.program,
                file: &file,
                from_standard_input: false,
            }
        };
        let variables: Vec<(String, String)> = case
            .variables
            .iter()
            .map(|(name, value)| ((*name).to_owned(), (*value).to_owned()))
            .collect();
        let sort = pgm();
        let initial = assembler
            .assemble(
                &KrunInputs {
                    start_sort: &sort,
                    program: Some(program),
                    configuration_variables: &variables,
                    io: false,
                },
                || Ok::<_, k_rust::kompile::ConfigurationError>(case.stdin.to_vec()),
            )
            .unwrap();
        let mut backend = definition.backend(BackendOptions::default()).unwrap();
        let initial = backend.internalize_executable(None, &initial).unwrap();
        let function_symbols = backend
            .select_definition(None)
            .unwrap()
            .function_symbol_names();
        let output = backend
            .run_cli(
                None,
                initial,
                BackendRunOptions {
                    depth: depth.unwrap_or(u64::MAX),
                    max_simplification_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
                    breadth_limit: None,
                    execute_to_branch: false,
                    cut_point_rules: Default::default(),
                    terminal_rules: Default::default(),
                    strategy: ExecutionMode::Any,
                    search: None,
                    match_target: None,
                    function_symbols,
                    stop_leaves: None,
                    step_timeout: None,
                    moving_average_timeout: false,
                    capture_stdout: false,
                    execution_input: None,
                },
            )
            .unwrap();
        let mut printed = Vec::new();
        output
            .pattern
            .with_source(|source| Printer::pretty(100).write_source(source, &mut printed))
            .unwrap();
        printed.push(b'\n');
        printed
    }

    fn assert_library_equals_krun(source: &str, main_module: &str, cases: &[Case]) {
        let root = directory(main_module);
        let definition_file = root.join("definition.k");
        fs::write(&definition_file, source).unwrap();
        let compiled = root.join("compiled");
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .arg("kcompile")
            .arg(&definition_file)
            .args(["--main-module", main_module])
            .arg("--output-directory")
            .arg(&compiled)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let artifact = load_runnable_artifact(&compiled).unwrap();
        let definition = KrunDefinition {
            main_module: &artifact.main_module,
            syntax_module: &artifact.syntax_module,
            frontend_definition: &artifact.frontend_definition,
            configuration_variables: &artifact.configuration_variables,
            execution_rewrite_order: &artifact.execution_rewrite_order,
            definition_kore: &artifact.definition_kore,
        };
        for case in cases {
            for depth in [Some(0), None] {
                let krun = krun(&compiled, &root, case, depth);
                let library = library(definition, &root, case, depth);
                assert_eq!(
                    String::from_utf8_lossy(&library),
                    String::from_utf8_lossy(&krun),
                    "{main_module}: program {:?}, depth {depth:?}",
                    case.program
                );
            }
        }
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn library_configuration_and_backend_equal_krun_on_imp() {
        assert_library_equals_krun(
            IMP,
            "IMP",
            &[
                Case {
                    program: IMP_SUM,
                    program_on_stdin: false,
                    variables: &[],
                    stdin: b"",
                },
                Case {
                    program: IMP_SHORT,
                    program_on_stdin: true,
                    variables: &[],
                    stdin: b"",
                },
            ],
        );
    }

    #[test]
    fn library_configuration_and_backend_equal_krun_with_variables_and_streams() {
        assert_library_equals_krun(
            STREAMS,
            "STREAMS",
            &[
                Case {
                    program: "go 4",
                    program_on_stdin: false,
                    variables: &[("N", "3")],
                    stdin: b"abc\n\n",
                },
                Case {
                    program: "go 4",
                    program_on_stdin: true,
                    variables: &[("N", "-2")],
                    stdin: b"",
                },
            ],
        );
    }
}
