use std::{
    env,
    error::Error,
    fs,
    io::{self, Read},
    path::{Path, PathBuf},
};

use clap::{Args, Parser, Subcommand, ValueEnum};
use k_rust::{
    definition::{
        ResolvedDefinition, StructuralCheckBackend, StructuralCheckOptions,
        checks::check_definition_with_options,
    },
    diagnostic::{Diagnostic, Severity},
    inner::ProgramParser,
    kast::{json as kast_json, parser::parse_sort, printer::Printer as KastPrinter},
    kompile::{
        ModuleToKoreOptions, add_cool_like_attributes, add_implicit_computation_cell,
        add_semantics_module, add_sort_injections_to_definition, check_simplification_rules,
        concretize_cells, constant_fold, expand_macros, generate_sort_predicate_rules,
        generate_sort_predicate_syntax, generate_sort_projections, guard_or_patterns,
        minimize_term_construction, module_to_kore_from_resolved_with_options, number_sentences,
        propagate_macro_attributes, remove_unit, resolve_anon_vars, resolve_comm,
        resolve_config_var, resolve_contexts, resolve_fresh_config_constants,
        resolve_fresh_constants, resolve_fun, resolve_function_with_config,
        resolve_heat_cool_attributes, resolve_io, resolve_semantic_casts, resolve_strict,
        subsort_kitem,
    },
    kore::printer::Printer as KorePrinter,
    native::FileResolver,
    outer::{LoadOptions, SourceResolver, load_with_options},
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
    backend: CompilationBackend,

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
enum CompilationBackend {
    #[default]
    Llvm,
    Haskell,
}

impl CompilationBackend {
    fn excluded_module_attribute(self) -> &'static str {
        match self {
            Self::Llvm => "symbolic",
            Self::Haskell => "concrete",
        }
    }

    fn structural_check_options(self) -> StructuralCheckOptions {
        match self {
            Self::Llvm => StructuralCheckOptions::default(),
            Self::Haskell => StructuralCheckOptions {
                symbolic: true,
                backend: StructuralCheckBackend::Haskell,
            },
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
            backend: arguments.backend,
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
    let check_options = backend
        .map(CompilationBackend::structural_check_options)
        .unwrap_or_default();
    let diagnostics = check_definition_with_options(&loaded.resolved, check_options)?;
    emit_diagnostics(&diagnostics);
    if diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        return Err("definition checks failed".into());
    }
    Ok(loaded)
}

fn kcompile(options: KcompileOptions) -> Result<(), Box<dyn Error>> {
    let loaded = load_definition(&options.common, Some(options.backend))?;
    let definition = resolve_comm(&loaded.definition).inspect_err(|error| {
        emit_diagnostics(&error.diagnostics);
    })?;
    let definition = resolve_io(&definition).inspect_err(|error| {
        emit_diagnostics(&error.diagnostics);
    })?;
    let definition = resolve_fun(&definition).inspect_err(|error| {
        emit_diagnostics(&error.diagnostics);
    })?;
    let definition = resolve_function_with_config(&definition).inspect_err(|error| {
        emit_diagnostics(&error.diagnostics);
    })?;
    let definition = resolve_strict(&definition).inspect_err(|error| {
        emit_diagnostics(&error.diagnostics);
    })?;
    let definition = resolve_anon_vars(&definition);
    let definition = resolve_contexts(&definition).inspect_err(|error| {
        emit_diagnostics(&error.diagnostics);
    })?;
    let definition = number_sentences(&definition);
    let definition = resolve_heat_cool_attributes(&definition).inspect_err(|error| {
        emit_diagnostics(&error.diagnostics);
    })?;
    let definition = resolve_semantic_casts(&definition);
    let definition = subsort_kitem(&definition)?;
    let definition = constant_fold(&definition).inspect_err(|error| {
        emit_diagnostics(&error.diagnostics);
    })?;
    let definition = propagate_macro_attributes(&definition)?;
    let definition = guard_or_patterns(&definition)?;
    let (definition, fresh_config_count) = resolve_fresh_config_constants(&definition)
        .inspect_err(|error| {
            emit_diagnostics(&error.diagnostics);
        })?;
    let definition = generate_sort_predicate_syntax(&definition)?;
    let definition = generate_sort_projections(&definition)?;
    let definition = expand_macros(&definition).inspect_err(|error| {
        emit_diagnostics(&error.diagnostics);
    })?;
    let definition = add_implicit_computation_cell(&definition)?;
    let definition =
        resolve_fresh_constants(&definition, fresh_config_count).inspect_err(|error| {
            emit_diagnostics(&error.diagnostics);
        })?;
    let definition = generate_sort_predicate_syntax(&definition)?;
    let definition = generate_sort_projections(&definition)?;
    let definition = check_simplification_rules(&definition).inspect_err(|error| {
        emit_diagnostics(&error.diagnostics);
    })?;
    let definition = subsort_kitem(&definition)?;
    let definition = concretize_cells(&definition).inspect_err(|error| {
        emit_diagnostics(&error.diagnostics);
    })?;
    // `genCoverage` is an identity stage unless coverage instrumentation is requested. The CLI
    // does not expose that optional mode yet. `removeAnywhereRules` is likewise an identity stage
    // unless the Haskell-only unsafe removal option is selected.
    let definition = add_semantics_module(&definition);
    let definition = resolve_config_var(&definition);
    let definition = add_cool_like_attributes(&definition);
    let definition = generate_sort_predicate_rules(&definition);
    let definition = number_sentences(&definition);
    let definition = add_sort_injections_to_definition(&definition)?;
    let definition = remove_unit(&definition)?;
    let definition = minimize_term_construction(&definition)?;
    let resolved = ResolvedDefinition::resolve(&definition)?;
    let generated = module_to_kore_from_resolved_with_options(
        &resolved,
        &options.common.module,
        ModuleToKoreOptions {
            generate_map_ceil_axioms: options.backend == CompilationBackend::Haskell,
        },
    )?;
    fs::create_dir_all(&options.output_directory)?;
    let printer = KorePrinter::pretty(100);
    let semantics = generated.semantics_definition();
    let syntax = generated.syntax_definition();
    fs::write(
        options.output_directory.join("definition.kore"),
        with_newline(printer.print_definition(&semantics)),
    )?;
    fs::write(
        options.output_directory.join("syntaxDefinition.kore"),
        with_newline(printer.print_definition(&syntax)),
    )?;
    let macros = generated
        .macros
        .iter()
        .map(|sentence| printer.print_sentence(sentence))
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(
        options.output_directory.join("macros.kore"),
        with_newline(macros),
    )?;
    Ok(())
}

fn kast(options: KastOptions) -> Result<(), Box<dyn Error>> {
    let loaded = load_definition(&options.common, None)?;
    let source = match (options.expression, options.program_file) {
        (Some(source), None) => source,
        (None, Some(path)) if path == Path::new("-") => read_stdin()?,
        (None, Some(path)) => fs::read_to_string(path)?,
        (None, None) => read_stdin()?,
        (Some(_), Some(_)) => unreachable!(),
    };
    let sort = parse_sort(&options.sort)?;
    let parser = ProgramParser::from_resolved(&loaded.resolved, &options.common.module)?;
    let term = parser.parse(&sort, &source)?;
    match options.output {
        OutputFormat::Text => println!("{}", KastPrinter::new().print_term(&term)),
        OutputFormat::Json => println!("{}", kast_json::to_string_pretty(&term)?),
    }
    Ok(())
}

fn read_stdin() -> io::Result<String> {
    let mut source = String::new();
    io::stdin().read_to_string(&mut source)?;
    Ok(source)
}

fn with_newline(mut text: String) -> String {
    if !text.ends_with('\n') {
        text.push('\n');
    }
    text
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
    fn parses_haskell_kcompile_backend() {
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

        assert_eq!(options.backend, CompilationBackend::Haskell);
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
