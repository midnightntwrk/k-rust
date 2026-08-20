use std::{
    collections::BTreeSet,
    env,
    error::Error,
    fs,
    io::{self, Read},
    num::NonZeroUsize,
    path::{Path, PathBuf},
    time::Duration,
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
        ast::{
            Attributes as KoreAttributes, Definition as KoreDefinition, Module as KoreModule,
            Pattern as KorePattern, Sentence as KoreSentence, Sort as KoreSort,
            Symbol as KoreSymbol,
        },
        parser::parse_definition as parse_kore_definition,
        printer::Printer as KorePrinter,
    },
    native::FileResolver,
    outer::{LoadOptions, SourceResolver, load_with_options},
};
use k_rust_backend::{
    builtin::BuiltinEffect,
    definition::BackendDefinition,
    externalize,
    proof::{ProofLeafOutcome, ProofOptions, ProofSearchOrder, ProofStatus, prove_claim},
    rewrite::{ExecutionOptions, HaltReason, Pattern, execute_with_solver_and_observer},
    smt::{SmtError, Z3Solver},
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
        Command::Kprove(options) => kprove(options.into()),
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
    /// Compile and prove modal reachability claims with the in-process Rust backend.
    Kprove(KproveArgs),
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

#[derive(Debug, Args)]
struct KproveArgs {
    /// K definition or specification containing the claims to prove.
    #[arg(value_name = "DEFINITION")]
    definition: PathBuf,

    /// Main specification module.
    #[arg(short = 'm', long = "main-module", value_name = "MODULE")]
    module: String,

    /// Semantics module that owns the configuration; defaults to the specification module.
    #[arg(long, visible_alias = "def-module", value_name = "MODULE")]
    definition_module: Option<String>,

    /// Prove only claims with one of these labels. May be repeated.
    #[arg(long = "claim", value_name = "LABEL")]
    claims: Vec<String>,

    /// Maximum number of rewrite or circularity steps per proof branch.
    #[arg(long, default_value_t = 1_000, value_name = "STEPS")]
    depth: u64,

    /// Maximum number of live parallel proof branches.
    #[arg(long = "breadth", value_name = "BRANCHES")]
    breadth_limit: Option<usize>,

    /// Stop an all-path proof after finding this many counterexamples.
    #[arg(long, default_value = "1", value_name = "COUNT")]
    max_counterexamples: NonZeroUsize,

    /// Load and update a KORE checkpoint containing previously proven claims.
    #[arg(long, value_name = "FILE")]
    save_proofs: Option<PathBuf>,

    /// Load additional SMT-LIB declarations and assertions before proving.
    #[arg(long, value_name = "FILE")]
    smt_prelude: Option<PathBuf>,

    /// Do not attempt implication closure before this depth.
    #[arg(long, default_value_t = 0, value_name = "STEPS")]
    min_depth: u64,

    /// Accept branches whose left-hand side simplifies to bottom.
    #[arg(long)]
    allow_vacuous: bool,

    /// Select breadth-first or depth-first proof graph traversal.
    #[arg(long, value_enum, default_value_t = GraphSearchArg::BreadthFirst)]
    graph_search: GraphSearchArg,

    /// Continue rewriting when destination terms match but their side conditions do not.
    #[arg(long)]
    disable_stuck_check: bool,

    /// Cancel a proof step after this many seconds.
    #[arg(long = "set-step-timeout", value_name = "SECONDS")]
    step_timeout: Option<NonZeroUsize>,

    /// Dynamically limit each step to twice the moving average of prior steps.
    #[arg(long)]
    moving_average: bool,

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

#[derive(Debug)]
struct KproveOptions {
    common: CommonOptions,
    definition_module: String,
    claims: Vec<String>,
    depth: u64,
    breadth_limit: Option<usize>,
    max_counterexamples: usize,
    save_proofs: Option<PathBuf>,
    smt_prelude: Option<PathBuf>,
    min_depth: u64,
    allow_vacuous: bool,
    graph_search: ProofSearchOrder,
    stuck_check: bool,
    step_timeout: Option<Duration>,
    moving_average_timeout: bool,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
enum GraphSearchArg {
    #[default]
    BreadthFirst,
    DepthFirst,
}

impl From<GraphSearchArg> for ProofSearchOrder {
    fn from(order: GraphSearchArg) -> Self {
        match order {
            GraphSearchArg::BreadthFirst => Self::BreadthFirst,
            GraphSearchArg::DepthFirst => Self::DepthFirst,
        }
    }
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

impl From<KproveArgs> for KproveOptions {
    fn from(arguments: KproveArgs) -> Self {
        let definition_module = arguments
            .definition_module
            .clone()
            .unwrap_or_else(|| arguments.module.clone());
        Self {
            common: arguments
                .source
                .common(arguments.definition, arguments.module),
            definition_module,
            claims: arguments.claims,
            depth: arguments.depth,
            breadth_limit: arguments.breadth_limit,
            max_counterexamples: arguments.max_counterexamples.get(),
            save_proofs: arguments.save_proofs,
            smt_prelude: arguments.smt_prelude,
            min_depth: arguments.min_depth,
            allow_vacuous: arguments.allow_vacuous,
            graph_search: arguments.graph_search.into(),
            stuck_check: !arguments.disable_stuck_check,
            step_timeout: arguments
                .step_timeout
                .map(|seconds| Duration::from_secs(seconds.get() as u64)),
            moving_average_timeout: arguments.moving_average,
        }
    }
}

fn load_definition(
    options: &CommonOptions,
    backend: Option<CompilationBackend>,
    configuration_module: Option<&str>,
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
            configuration_module: configuration_module.map(str::to_owned),
        },
    )?;
    Ok(loaded)
}

fn kcompile(options: KcompileOptions) -> Result<(), Box<dyn Error>> {
    let loaded = load_definition(&options.common, Some(options.backend), None)?;
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
    let loaded = load_definition(&options.common, None, None)?;
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
    let loaded = load_definition(&options.common, Some(CompilationBackend::Rust), None)?;
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
    let execution = execute_with_solver_and_observer(
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
        |effect| match effect {
            BuiltinEffect::UserLog(message) => eprintln!("{message}"),
        },
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

fn kprove(options: KproveOptions) -> Result<(), Box<dyn Error>> {
    let loaded = load_definition(
        &options.common,
        Some(CompilationBackend::Rust),
        Some(&options.definition_module),
    )?;
    let compiled = match compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend: CompilationBackend::Rust,
            default_claims_to_all_path: true,
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

    let syntax = parse_kore_definition(&compiled.definition_kore)?;
    let saved_claims = options
        .save_proofs
        .as_deref()
        .map(load_saved_claims)
        .transpose()?
        .unwrap_or_default();
    let spec_module = syntax
        .modules
        .iter()
        .find(|module| module.name == options.common.module)
        .ok_or_else(|| format!("compiled KORE has no module `{}`", options.common.module))?;
    let mut proven_ids = saved_claims
        .iter()
        .filter_map(claim_unique_id)
        .filter(|id| {
            spec_module.sentences.iter().any(|sentence| {
                claim_unique_id(sentence) == Some(id.clone()) && saved_claims.contains(sentence)
            })
        })
        .collect::<BTreeSet<_>>();
    let backend = BackendDefinition::internalize(&syntax, &options.common.module)?;
    if backend.reachability_claims.is_empty() {
        return Err("the selected module contains no modal reachability claims".into());
    }
    let smt_prelude = options
        .smt_prelude
        .as_deref()
        .map(|path| {
            fs::read_to_string(path).map_err(|error| {
                io::Error::new(
                    error.kind(),
                    format!("could not read SMT prelude `{}`: {error}", path.display()),
                )
            })
        })
        .transpose()?;
    let solver = match smt_prelude.as_deref() {
        Some(prelude) => Z3Solver::with_prelude(&backend, prelude),
        None => Z3Solver::new(&backend),
    }
    .map_err(|error| {
        io::Error::other(match error {
            SmtError::InconsistentPrelude => {
                "the definitions sent to the solver are inconsistent".to_owned()
            }
            error => format!("could not initialize Z3: {error:?}"),
        })
    })?;
    let selected = backend
        .reachability_claims
        .iter()
        .filter(|claim| {
            options.claims.is_empty()
                || claim
                    .attributes
                    .label
                    .as_ref()
                    .is_some_and(|label| options.claims.contains(label))
        })
        .collect::<Vec<_>>();
    for requested in &options.claims {
        if !selected
            .iter()
            .any(|claim| claim.attributes.label.as_ref() == Some(requested))
        {
            return Err(format!("no modal reachability claim has label `{requested}`").into());
        }
    }

    let mut all_proven = true;
    for (index, claim) in selected.into_iter().enumerate() {
        let name = claim
            .attributes
            .label
            .as_deref()
            .map_or_else(|| format!("#{}", index + 1), str::to_owned);
        if proven_ids.contains(&claim.attributes.unique_id) {
            println!("claim {name}: proven (saved)");
            continue;
        }
        let result = prove_claim(
            &backend,
            claim,
            ProofOptions {
                max_depth: options.depth,
                min_depth: options.min_depth,
                breadth_limit: options.breadth_limit,
                max_counterexamples: options.max_counterexamples,
                allow_vacuous: options.allow_vacuous,
                search_order: options.graph_search,
                stuck_check: options.stuck_check,
                step_timeout: options.step_timeout,
                moving_average_timeout: options.moving_average_timeout,
                ..ProofOptions::default()
            },
            &solver,
        )?;
        println!(
            "claim {name}: {} ({} states, {} unexplored)",
            proof_status(result.status),
            result.explored_states,
            result.unexplored_states,
        );
        if result.status == ProofStatus::Proven {
            proven_ids.insert(claim.attributes.unique_id.clone());
        } else {
            all_proven = false;
            for leaf in result.leaves.iter().filter(|leaf| {
                !matches!(
                    leaf.outcome,
                    ProofLeafOutcome::Proven(_) | ProofLeafOutcome::Trusted
                )
            }) {
                println!("  {:?} at depth {}", leaf.outcome, leaf.depth);
                let pattern = externalize::constrained_pattern(&leaf.pattern);
                let rendered = KorePrinter::pretty(100).print_pattern(&pattern);
                for line in rendered.lines() {
                    println!("    {line}");
                }
            }
        }
    }
    if let Some(path) = &options.save_proofs {
        save_proven_claims(path, spec_module, &proven_ids)?;
    }
    if !all_proven {
        return Err("one or more reachability claims were not proven".into());
    }
    Ok(())
}

const SAVED_PROOFS_MODULE: &str =
    "haskell-backend-saved-claims-43943e50-f723-47cd-99fd-07104d664c6d";

fn load_saved_claims(path: &Path) -> Result<Vec<KoreSentence>, Box<dyn Error>> {
    if !path.exists() {
        return Ok(Vec::new());
    }
    let definition = parse_kore_definition(&fs::read_to_string(path)?)?;
    let module = definition
        .modules
        .iter()
        .find(|module| module.name == SAVED_PROOFS_MODULE)
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("saved proof file has no `{SAVED_PROOFS_MODULE}` module"),
            )
        })?;
    Ok(module
        .sentences
        .iter()
        .filter(|sentence| matches!(sentence, KoreSentence::Claim { .. }))
        .cloned()
        .collect())
}

fn save_proven_claims(
    path: &Path,
    spec_module: &KoreModule,
    proven_ids: &BTreeSet<String>,
) -> Result<(), Box<dyn Error>> {
    let definition = saved_proof_definition(spec_module, proven_ids);
    let rendered = KorePrinter::pretty(100).print_definition(&definition);
    fs::write(path, rendered)?;
    Ok(())
}

fn saved_proof_definition(
    spec_module: &KoreModule,
    proven_ids: &BTreeSet<String>,
) -> KoreDefinition {
    let declarations = spec_module
        .sentences
        .iter()
        .filter(|sentence| {
            !matches!(
                sentence,
                KoreSentence::Axiom { .. } | KoreSentence::Claim { .. }
            )
        })
        .cloned();
    let claims = spec_module
        .sentences
        .iter()
        .filter(|sentence| claim_unique_id(sentence).is_some_and(|id| proven_ids.contains(&id)))
        .cloned();
    KoreDefinition {
        attributes: KoreAttributes::default(),
        modules: vec![KoreModule {
            name: SAVED_PROOFS_MODULE.into(),
            sentences: declarations.chain(claims).collect(),
            attributes: KoreAttributes::default(),
        }],
    }
}

fn claim_unique_id(sentence: &KoreSentence) -> Option<String> {
    let KoreSentence::Claim { attributes, .. } = sentence else {
        return None;
    };
    attribute_string(attributes, "UNIQUE'Unds'ID").or_else(|| attribute_string(attributes, "label"))
}

fn attribute_string(attributes: &KoreAttributes, name: &str) -> Option<String> {
    attributes.0.iter().find_map(|attribute| {
        let KorePattern::Application { symbol, arguments } = attribute else {
            return None;
        };
        let [KorePattern::String(value)] = arguments.as_slice() else {
            return None;
        };
        (symbol.name == name).then(|| value.clone())
    })
}

fn proof_status(status: ProofStatus) -> &'static str {
    match status {
        ProofStatus::Proven => "proven",
        ProofStatus::Disproved => "disproved",
        ProofStatus::Indeterminate => "indeterminate",
        ProofStatus::DepthBound => "depth bound",
        ProofStatus::BreadthBound => "breadth bound",
    }
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
    fn parses_kprove_claim_selection_and_bounds() {
        let cli = Cli::try_parse_from([
            "krust",
            "kprove",
            "spec.k",
            "--main-module",
            "SPEC",
            "--definition-module",
            "SEMANTICS",
            "--claim",
            "first",
            "--claim",
            "second",
            "--depth",
            "42",
            "--breadth",
            "7",
            "--max-counterexamples",
            "3",
            "--save-proofs",
            "proofs.kore",
            "--smt-prelude",
            "prelude.smt2",
            "--min-depth",
            "2",
            "--allow-vacuous",
            "--graph-search",
            "depth-first",
            "--disable-stuck-check",
            "--set-step-timeout",
            "9",
            "--moving-average",
        ])
        .unwrap();
        let Command::Kprove(options) = cli.command else {
            panic!("expected kprove command");
        };
        let options = KproveOptions::from(options);

        assert_eq!(options.common.definition, Path::new("spec.k"));
        assert_eq!(options.common.module, "SPEC");
        assert_eq!(options.definition_module, "SEMANTICS");
        assert_eq!(options.claims, ["first", "second"]);
        assert_eq!(options.depth, 42);
        assert_eq!(options.breadth_limit, Some(7));
        assert_eq!(options.max_counterexamples, 3);
        assert_eq!(
            options.save_proofs.as_deref(),
            Some(Path::new("proofs.kore"))
        );
        assert_eq!(
            options.smt_prelude.as_deref(),
            Some(Path::new("prelude.smt2"))
        );
        assert_eq!(options.min_depth, 2);
        assert!(options.allow_vacuous);
        assert_eq!(options.graph_search, ProofSearchOrder::DepthFirst);
        assert!(!options.stuck_check);
        assert_eq!(options.step_timeout, Some(Duration::from_secs(9)));
        assert!(options.moving_average_timeout);
    }

    #[test]
    fn saved_proofs_keep_declarations_and_only_proven_claims() {
        let definition = parse_kore_definition(
            r#"[]
            module SPEC
              sort SortS{} []
              symbol a{}() : SortS{} []
              axiom{} \top{SortS{}}() [UNIQUE'Unds'ID{}("axiom")]
              claim{} \top{SortS{}}() [UNIQUE'Unds'ID{}("first")]
              claim{} \bottom{SortS{}}() [UNIQUE'Unds'ID{}("second")]
            endmodule []"#,
        )
        .unwrap();
        let saved =
            saved_proof_definition(&definition.modules[0], &BTreeSet::from(["second".into()]));
        let module = &saved.modules[0];

        assert_eq!(module.name, SAVED_PROOFS_MODULE);
        assert_eq!(module.sentences.len(), 3);
        assert!(matches!(
            module.sentences.as_slice(),
            [
                KoreSentence::SortDeclaration { .. },
                KoreSentence::SymbolDeclaration { .. },
                KoreSentence::Claim { .. }
            ]
        ));
        assert_eq!(
            claim_unique_id(&module.sentences[2]).as_deref(),
            Some("second")
        );

        let rendered = KorePrinter::compact().print_definition(&saved);
        let reparsed = parse_kore_definition(&rendered).unwrap();
        assert_eq!(reparsed, saved);
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
