use std::{
    env,
    error::Error,
    fs,
    io::{self, Read},
    path::{Path, PathBuf},
};

use clap::{Args, Parser, Subcommand, ValueEnum};
use k_rust::{
    definition::checks::check_definition,
    diagnostic::{Diagnostic, Severity},
    inner::ProgramParser,
    kast::{json as kast_json, parser::parse_sort, printer::Printer as KastPrinter},
    kompile::{
        CompilationBackend, CompileOptions, SortInjector, compile_loaded_definition,
        encode_kore_sort, term_to_kore_from_resolved,
    },
    kore::{
        ast::{Pattern as KorePattern, Sort as KoreSort, Symbol as KoreSymbol},
        parser::parse_definition as parse_kore_definition,
        printer::Printer as KorePrinter,
    },
    native::FileResolver,
    outer::{LoadOptions, SourceResolver, load_with_options},
};
use k_rust_backend::{
    definition::BackendDefinition,
    externalize,
    rewrite::{ExecutionOptions, HaltReason, Pattern, execute_with_solver},
    smt::Z3Solver,
};

fn main() {
    let cli = Cli::parse();
    if let Err(error) = run(cli) {
        eprintln!("error: {error}");
        std::process::exit(1);
    }
}

fn run(cli: Cli) -> Result<(), Box<dyn Error>> {
    match cli.command {
        Command::Kcompile(options) => kcompile(options.into()),
        Command::Kast(options) => kast(options.into()),
        Command::Krun(options) => krun(options.into()),
    }
}

#[derive(Debug, Parser)]
#[command(
    name = "krust",
    version,
    about = "Rust frontend for the K Framework",
    arg_required_else_help = true
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Compile a K definition to backend-facing KORE files.
    Kcompile(KcompileArgs),
    /// Parse a program using a K definition and print its KAST.
    Kast(KastArgs),
    /// Compile and execute a program with the in-process Rust backend.
    Krun(KrunArgs),
}

#[derive(Clone, Debug, Args)]
struct SourceArgs {
    /// Add a directory to the definition source search path.
    #[arg(short = 'I', long = "include", value_name = "DIR")]
    includes: Vec<PathBuf>,

    /// Select Markdown code blocks using this expression.
    #[arg(long = "md-selector", default_value = "k", value_name = "EXPR")]
    markdown_selector: String,

    /// Resolve K builtin sources from this directory instead of the embedded copies.
    #[arg(long, value_name = "DIR")]
    builtin_directory: Option<PathBuf>,

    /// Do not load the standard K prelude implicitly.
    #[arg(long)]
    no_prelude: bool,
}

#[derive(Debug, Args)]
struct KcompileArgs {
    /// K definition file to compile.
    #[arg(value_name = "DEFINITION")]
    definition: PathBuf,

    /// Main module of the definition.
    #[arg(short = 'm', long = "main-module", value_name = "MODULE")]
    module: String,

    /// Backend for which KORE should be generated.
    #[arg(long, value_enum, default_value_t)]
    backend: CompilationBackendArg,

    /// Directory in which generated KORE files are written.
    #[arg(short = 'o', long, default_value = ".", value_name = "DIR")]
    output_directory: PathBuf,

    #[command(flatten)]
    source: SourceArgs,
}

#[derive(Debug, Args)]
struct KastArgs {
    /// K definition file whose grammar should parse the program.
    #[arg(value_name = "DEFINITION")]
    definition: PathBuf,

    /// Module whose grammar should parse the program.
    #[arg(short = 'm', long, value_name = "MODULE")]
    module: String,

    /// Start sort for the program parser.
    #[arg(short = 's', long, value_name = "SORT")]
    sort: String,

    /// Parse this program text instead of reading a file or standard input.
    #[arg(
        short = 'e',
        long,
        conflicts_with = "program_file",
        allow_hyphen_values = true,
        value_name = "PROGRAM"
    )]
    expression: Option<String>,

    /// Program file to parse, or `-` for standard input.
    #[arg(value_name = "PROGRAM_FILE")]
    program_file: Option<PathBuf>,

    /// KAST output format.
    #[arg(short = 'o', long, value_enum, default_value_t)]
    output: OutputFormat,

    #[command(flatten)]
    source: SourceArgs,
}

#[derive(Debug, Args)]
struct KrunArgs {
    /// K definition whose semantics should execute the program.
    #[arg(value_name = "DEFINITION")]
    definition: PathBuf,

    /// Main module of the definition.
    #[arg(short = 'm', long = "main-module", value_name = "MODULE")]
    module: String,

    /// Start sort for the program parser.
    #[arg(short = 's', long, value_name = "SORT")]
    sort: String,

    /// Execute this program text instead of reading a file or standard input.
    #[arg(
        short = 'e',
        long,
        conflicts_with = "program_file",
        allow_hyphen_values = true,
        value_name = "PROGRAM"
    )]
    expression: Option<String>,

    /// Program file to execute, or `-` for standard input.
    #[arg(value_name = "PROGRAM_FILE")]
    program_file: Option<PathBuf>,

    /// Maximum number of semantic rewrite steps per execution branch.
    #[arg(long, default_value_t = 1_000, value_name = "STEPS")]
    depth: u64,

    #[command(flatten)]
    source: SourceArgs,
}

#[derive(Debug)]
struct CommonOptions {
    definition: PathBuf,
    module: String,
    includes: Vec<PathBuf>,
    markdown_selector: String,
    builtin_directory: Option<PathBuf>,
    no_prelude: bool,
}

#[derive(Debug)]
struct KcompileOptions {
    common: CommonOptions,
    backend: CompilationBackend,
    output_directory: PathBuf,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
enum CompilationBackendArg {
    #[default]
    #[value(alias = "haskell")]
    Rust,
    Llvm,
}

impl From<CompilationBackendArg> for CompilationBackend {
    fn from(backend: CompilationBackendArg) -> Self {
        match backend {
            CompilationBackendArg::Rust => Self::Rust,
            CompilationBackendArg::Llvm => Self::Llvm,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
enum OutputFormat {
    #[default]
    Text,
    Json,
}

#[derive(Debug)]
struct KastOptions {
    common: CommonOptions,
    sort: String,
    expression: Option<String>,
    program_file: Option<PathBuf>,
    output: OutputFormat,
}

#[derive(Debug)]
struct KrunOptions {
    common: CommonOptions,
    sort: String,
    expression: Option<String>,
    program_file: Option<PathBuf>,
    depth: u64,
}

impl SourceArgs {
    fn common(self, definition: PathBuf, module: String) -> CommonOptions {
        CommonOptions {
            definition,
            module,
            includes: self.includes,
            markdown_selector: self.markdown_selector,
            builtin_directory: self.builtin_directory,
            no_prelude: self.no_prelude,
        }
    }
}

impl From<KcompileArgs> for KcompileOptions {
    fn from(arguments: KcompileArgs) -> Self {
        Self {
            common: arguments
                .source
                .common(arguments.definition, arguments.module),
            backend: arguments.backend.into(),
            output_directory: arguments.output_directory,
        }
    }
}

impl From<KastArgs> for KastOptions {
    fn from(arguments: KastArgs) -> Self {
        Self {
            common: arguments
                .source
                .common(arguments.definition, arguments.module),
            sort: arguments.sort,
            expression: arguments.expression,
            program_file: arguments.program_file,
            output: arguments.output,
        }
    }
}

impl From<KrunArgs> for KrunOptions {
    fn from(arguments: KrunArgs) -> Self {
        Self {
            common: arguments
                .source
                .common(arguments.definition, arguments.module),
            sort: arguments.sort,
            expression: arguments.expression,
            program_file: arguments.program_file,
            depth: arguments.depth,
        }
    }
}

fn load_definition(
    options: &CommonOptions,
    backend: Option<CompilationBackend>,
) -> Result<k_rust::outer::LoadedDefinition, Box<dyn Error>> {
    let builtin_directory = options
        .builtin_directory
        .clone()
        .or_else(|| env::var_os("KRUST_BUILTIN_DIRECTORY").map(PathBuf::from));
    let mut resolver = FileResolver::from_current_directory(options.includes.clone())?;
    if let Some(directory) = builtin_directory {
        resolver = resolver.with_builtin_directory(directory);
    }
    let entry = resolver.load_entry(&options.definition)?;
    let implicit_sources = if options.no_prelude {
        Vec::new()
    } else {
        vec![
            resolver
                .resolve(&entry.source, "prelude.md")
                .map_err(|message| io::Error::new(io::ErrorKind::NotFound, message))?,
        ]
    };
    let loaded = load_with_options(
        entry,
        &options.module,
        &mut resolver,
        &LoadOptions {
            markdown_selector: options.markdown_selector.clone(),
            implicit_sources,
            excluded_module_attributes: backend
                .map(|backend| vec![backend.excluded_module_attribute().into()])
                .unwrap_or_default(),
        },
    )?;
    Ok(loaded)
}

fn kcompile(options: KcompileOptions) -> Result<(), Box<dyn Error>> {
    let loaded = load_definition(&options.common, Some(options.backend))?;
    let artifacts = match compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend: options.backend,
            ..CompileOptions::default()
        },
    ) {
        Ok(artifacts) => artifacts,
        Err(error) => {
            emit_diagnostics(&error.diagnostics);
            return Err(error.into());
        }
    };
    emit_diagnostics(&artifacts.diagnostics);
    fs::create_dir_all(&options.output_directory)?;
    fs::write(
        options.output_directory.join("definition.kore"),
        artifacts.definition_kore,
    )?;
    fs::write(
        options.output_directory.join("syntaxDefinition.kore"),
        artifacts.syntax_definition_kore,
    )?;
    fs::write(
        options.output_directory.join("macros.kore"),
        artifacts.macros_kore,
    )?;
    Ok(())
}

fn kast(options: KastOptions) -> Result<(), Box<dyn Error>> {
    let loaded = load_definition(&options.common, None)?;
    let diagnostics = check_definition(&loaded.resolved)?;
    emit_diagnostics(&diagnostics);
    if diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        return Err("definition checks failed".into());
    }
    let source = read_program_source(options.expression, options.program_file)?;
    let sort = parse_sort(&options.sort)?;
    let parser = ProgramParser::from_resolved(&loaded.resolved, &options.common.module)?;
    let term = parser.parse(&sort, &source)?;
    match options.output {
        OutputFormat::Text => println!("{}", KastPrinter::new().print_term(&term)),
        OutputFormat::Json => println!("{}", kast_json::to_string_pretty(&term)?),
    }
    Ok(())
}

fn krun(options: KrunOptions) -> Result<(), Box<dyn Error>> {
    let loaded = load_definition(&options.common, Some(CompilationBackend::Rust))?;
    let compiled = match compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend: CompilationBackend::Rust,
            ..CompileOptions::default()
        },
    ) {
        Ok(compiled) => compiled,
        Err(error) => {
            emit_diagnostics(&error.diagnostics);
            return Err(error.into());
        }
    };
    emit_diagnostics(&compiled.diagnostics);

    let source = read_program_source(options.expression, options.program_file)?;
    let start_sort = parse_sort(&options.sort)?;
    let parser = ProgramParser::from_resolved(&loaded.resolved, &options.common.module)?;
    let program = parser.parse(&start_sort, &source)?;
    // Parser annotations refer to the source definition's production catalog. Perform
    // production-sensitive conversion there, before crossing into the transformed definition.
    let injector = SortInjector::new(&loaded.resolved, &options.common.module)?;
    let program_sort = injector.term_sort(&program, None)?;
    let program = injector.inject_at_top(&program)?;
    let program = term_to_kore_from_resolved(&loaded.resolved, &options.common.module, &program)?;
    let initial = top_cell_initializer(program, encode_kore_sort(&program_sort));

    let syntax = parse_kore_definition(&compiled.definition_kore)?;
    let backend = BackendDefinition::internalize(&syntax, &options.common.module)?;
    let initial = backend.internalize_term(&initial, &[])?;
    let solver = Z3Solver::new(&backend)
        .map_err(|error| io::Error::other(format!("could not initialize Z3: {error:?}")))?;
    let execution = execute_with_solver(
        &backend,
        Pattern {
            term: initial,
            constraints: Vec::new(),
        },
        ExecutionOptions {
            max_depth: options.depth,
            ..ExecutionOptions::default()
        },
        &solver,
    );
    if let Some(leaf) = execution.leaves.iter().find(|leaf| {
        matches!(
            leaf.halt_reason,
            HaltReason::Indeterminate(_) | HaltReason::Simplification(_)
        )
    }) {
        return Err(io::Error::other(format!(
            "in-process backend halted at depth {}: {:?}",
            leaf.depth, leaf.halt_reason
        ))
        .into());
    }
    let Some(first_leaf) = execution.leaves.first() else {
        return Err("in-process backend produced no execution states".into());
    };
    let final_sort = externalize::sort(&first_leaf.pattern.term.sort());
    let mut states = execution
        .leaves
        .iter()
        .map(|leaf| externalize::constrained_pattern(&leaf.pattern))
        .collect::<Vec<_>>();
    let output = match states.len() {
        0 => unreachable!("execution leaves were checked above"),
        1 => states.pop().unwrap(),
        _ => KorePattern::Or {
            sort: final_sort,
            arguments: states,
        },
    };
    println!("{}", KorePrinter::pretty(100).print_pattern(&output));
    Ok(())
}

fn read_program_source(
    expression: Option<String>,
    program_file: Option<PathBuf>,
) -> Result<String, Box<dyn Error>> {
    Ok(match (expression, program_file) {
        (Some(source), None) => source,
        (None, Some(path)) if path == Path::new("-") => read_stdin()?,
        (None, Some(path)) => fs::read_to_string(path)?,
        (None, None) => read_stdin()?,
        (Some(_), Some(_)) => unreachable!(),
    })
}

fn top_cell_initializer(program: KorePattern, program_sort: KoreSort) -> KorePattern {
    let config_var_sort = kore_sort("SortKConfigVar");
    let item_sort = kore_sort("SortKItem");
    let key = kore_application(
        "inj",
        vec![config_var_sort.clone(), item_sort.clone()],
        vec![KorePattern::DomainValue {
            sort: config_var_sort,
            value: "$PGM".into(),
        }],
    );
    let program = if program_sort == item_sort {
        program
    } else {
        kore_application("inj", vec![program_sort, item_sort], vec![program])
    };
    let config = kore_application("Lbl'UndsPipe'-'-GT-Unds'", Vec::new(), vec![key, program]);
    kore_application("LblinitGeneratedTopCell", Vec::new(), vec![config])
}

fn kore_application(
    name: &str,
    sort_parameters: Vec<KoreSort>,
    arguments: Vec<KorePattern>,
) -> KorePattern {
    KorePattern::Application {
        symbol: KoreSymbol {
            name: name.into(),
            sort_parameters,
        },
        arguments,
    }
}

fn kore_sort(name: &str) -> KoreSort {
    KoreSort::Application {
        name: name.into(),
        arguments: Vec::new(),
    }
}

fn read_stdin() -> io::Result<String> {
    let mut source = String::new();
    io::stdin().read_to_string(&mut source)?;
    Ok(source)
}

fn emit_diagnostics(diagnostics: &[Diagnostic]) {
    for diagnostic in diagnostics {
        let location = match (&diagnostic.source, diagnostic.location) {
            (Some(source), Some(location)) => format!(
                "{source}:{}:{}: ",
                location.start_line, location.start_column
            ),
            (Some(source), None) => format!("{source}: "),
            _ => String::new(),
        };
        eprintln!(
            "{location}{:?}[{:?}]: {}",
            diagnostic.severity, diagnostic.code, diagnostic.message
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_kast_options_in_any_order() {
        let cli = Cli::try_parse_from([
            "krust",
            "kast",
            "--sort",
            "Exp",
            "definition.k",
            "-I",
            "builtins",
            "--module",
            "MAIN",
            "-e",
            "1 + 2",
            "--output",
            "json",
        ])
        .unwrap();
        let Command::Kast(options) = cli.command else {
            panic!("expected kast command");
        };
        let options = KastOptions::from(options);
        assert_eq!(options.common.definition, Path::new("definition.k"));
        assert_eq!(options.common.module, "MAIN");
        assert_eq!(options.common.includes, [PathBuf::from("builtins")]);
        assert_eq!(options.sort, "Exp");
        assert_eq!(options.expression.as_deref(), Some("1 + 2"));
        assert_eq!(options.output, OutputFormat::Json);
    }

    #[test]
    fn accepts_haskell_as_a_legacy_name_for_the_rust_backend() {
        let cli = Cli::try_parse_from([
            "krust",
            "kcompile",
            "definition.k",
            "--main-module",
            "MAIN",
            "--backend",
            "haskell",
        ])
        .unwrap();
        let Command::Kcompile(options) = cli.command else {
            panic!("expected kcompile command");
        };
        let options = KcompileOptions::from(options);

        assert_eq!(options.backend, CompilationBackend::Rust);
    }

    #[test]
    fn parses_krun_options() {
        let cli = Cli::try_parse_from([
            "krust",
            "krun",
            "definition.k",
            "--main-module",
            "MAIN",
            "--sort",
            "Exp",
            "--expression",
            "1 + 2",
            "--depth",
            "42",
        ])
        .unwrap();
        let Command::Krun(options) = cli.command else {
            panic!("expected krun command");
        };
        let options = KrunOptions::from(options);

        assert_eq!(options.common.definition, Path::new("definition.k"));
        assert_eq!(options.common.module, "MAIN");
        assert_eq!(options.sort, "Exp");
        assert_eq!(options.expression.as_deref(), Some("1 + 2"));
        assert_eq!(options.depth, 42);
    }

    #[test]
    fn accepts_program_expressions_that_begin_with_a_hyphen() {
        let cli = Cli::try_parse_from([
            "krust",
            "kast",
            "definition.k",
            "--module",
            "MAIN",
            "--sort",
            "Int",
            "--expression",
            "-1",
        ])
        .unwrap();
        let Command::Kast(options) = cli.command else {
            panic!("expected kast command");
        };

        assert_eq!(options.expression.as_deref(), Some("-1"));
    }
}
