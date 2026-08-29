use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    error::Error,
    fmt, fs,
    io::{self, Read},
    num::{NonZeroU32, NonZeroUsize},
    path::{Path, PathBuf},
    time::Duration,
};

use clap::{ArgGroup, Args, Parser, Subcommand, ValueEnum};
use k_rust::{
    definition::checks::check_definition,
    diagnostic::{Diagnostic, Severity},
    inner::ProgramParser,
    kast::{
        Sort as KastSort, json as kast_json, parser::parse_sort, printer::Printer as KastPrinter,
    },
    kompile::{
        CompilationBackend, CompileOptions, SortInjector, compile_loaded_definition,
        encode_kore_sort, term_to_kore_from_resolved,
    },
    kore::{
        ast::{
            Attributes as KoreAttributes, Definition as KoreDefinition, Module as KoreModule,
            Pattern as KorePattern, Sentence as KoreSentence, Sort as KoreSort,
            Symbol as KoreSymbol, Variable as KoreVariable,
        },
        binary as kore_binary, json as kore_json,
        parser::{
            parse_definition as parse_kore_definition, parse_module as parse_kore_module,
            parse_pattern as parse_kore_pattern,
        },
        printer::Printer as KorePrinter,
    },
    native::FileResolver,
    outer::{LoadOptions, SourceResolver, load_with_options},
};
use k_rust_backend::{
    binary as backend_binary,
    builtin::BuiltinEffect,
    definition::{BackendDefinition, DefinitionError},
    externalize,
    implication::{
        ImplicationCondition, ImplicationResult, ImplicationStatus,
        check_implication_with_existentials_complete,
    },
    proof::{ProofLeafOutcome, ProofOptions, ProofSearchOrder, ProofStatus, prove_claim},
    rewrite::{
        ExecutionBranchMode, ExecutionMode, ExecutionOptions, HaltReason, Pattern,
        execute_with_solver_and_observer,
    },
    rule::{Predicate, RulePatternError},
    search::{
        IncompleteSearch, PatternMatch, PatternMatchError, PatternSearchResult, SearchOptions,
        SearchType, match_disjunction, search_pattern_with_solver,
    },
    session::BackendSession,
    simplify::{
        SimplificationOptions, simplify_and_decide_predicate_with_solver,
        simplify_pattern_with_solver,
    },
    smt::{ModelResult, SmtError, SmtSolver, Z3Options, Z3Solver},
    substitution::Substitution,
    term::{Name as BackendName, Sort as BackendSort, Term, TermKind, Variable},
};

mod rpc;

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
        Command::KoreExec(options) => kore_exec(options),
        Command::KoreSimplify(options) => kore_simplify(options),
        Command::KoreGetModel(options) => kore_get_model(options),
        Command::KoreImplies(options) => kore_implies(options),
        Command::KoreRpc(options) => kore_rpc(options),
        Command::KoreMatchDisjunction(options) => kore_match_disjunction(options),
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
    /// Execute an already compiled KORE definition with the in-process Rust backend.
    KoreExec(KoreExecArgs),
    /// Simplify an arbitrary KORE pattern with the in-process Rust backend.
    KoreSimplify(KoreSimplifyArgs),
    /// Obtain a satisfying model for the predicate portion of a KORE pattern.
    KoreGetModel(KoreGetModelArgs),
    /// Check implication between two constrained KORE patterns.
    KoreImplies(KoreImpliesArgs),
    /// Serve the in-process backend over KORE's raw-socket JSON-RPC protocol.
    KoreRpc(KoreRpcArgs),
    /// Match a constrained KORE pattern against a disjunction of configurations.
    KoreMatchDisjunction(KoreMatchDisjunctionArgs),
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

    /// Backend whose module view should be used while parsing.
    #[arg(long, value_enum)]
    backend: Option<CompilationBackendArg>,

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
#[command(group(
    ArgGroup::new("search_mode")
        .args([
            "search_final",
            "search_all",
            "search_one_step",
            "search_one_or_more_steps",
        ])
        .multiple(false)
))]
struct SearchArgs {
    /// Return only irreducible reachable configurations.
    #[arg(long, group = "search_mode")]
    search_final: bool,

    /// Return every reachable configuration, including the initial one.
    #[arg(long, group = "search_mode")]
    search_all: bool,

    /// Return configurations reached in exactly one rewrite step.
    #[arg(long, group = "search_mode")]
    search_one_step: bool,

    /// Return configurations reached in one or more rewrite steps.
    #[arg(long, group = "search_mode")]
    search_one_or_more_steps: bool,

    /// Match search results against this text, JSON v1, or binary KORE pattern file.
    #[arg(long, requires = "search_mode", value_name = "KORE_FILE")]
    search_pattern: Option<PathBuf>,

    /// Stop after finding this many distinct search solutions.
    #[arg(long, requires = "search_mode", value_name = "COUNT")]
    search_bound: Option<usize>,
}

#[derive(Debug, Args)]
struct ExecutionTimeoutArgs {
    /// Cancel a semantic rewrite step after this many milliseconds.
    #[arg(long = "step-timeout", value_name = "MILLISECONDS")]
    step_timeout: Option<NonZeroUsize>,

    /// Dynamically limit each step to twice the moving average of prior steps.
    #[arg(long = "moving-average-step-timeout")]
    moving_average: bool,
}

impl ExecutionTimeoutArgs {
    fn timeout(&self) -> Option<Duration> {
        self.step_timeout
            .map(|milliseconds| Duration::from_millis(milliseconds.get() as u64))
    }
}

#[derive(Clone, Copy, Debug, Args)]
struct SmtArgs {
    /// Limit each Z3 query to this many milliseconds before retrying.
    #[arg(
        long = "smt-timeout",
        default_value = "125",
        value_name = "MILLISECONDS"
    )]
    timeout: NonZeroU32,

    /// Retry an unknown Z3 result this many times, doubling the timeout each time.
    #[arg(long = "smt-retry-limit", default_value_t = 3, value_name = "COUNT")]
    retry_limit: u32,
}

impl SmtArgs {
    fn options(self) -> Z3Options {
        Z3Options {
            timeout_ms: self.timeout.get(),
            retry_limit: self.retry_limit,
        }
    }
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

    /// Bind an additional configuration variable. May be repeated.
    #[arg(short = 'c', long = "config-var", value_name = "NAME=VALUE")]
    config_vars: Vec<String>,

    /// Maximum number of semantic rewrite steps per execution branch.
    #[arg(long, value_name = "STEPS")]
    depth: Option<u64>,

    /// Maximum number of live execution or search branches.
    #[arg(long = "breadth", value_name = "BRANCHES")]
    breadth_limit: Option<usize>,

    /// Stop and return the current configuration when execution first branches.
    #[arg(long)]
    execute_to_branch: bool,

    /// Stop before applying a rule with this label or unique ID. May be repeated.
    #[arg(long = "cut-point-rule", value_name = "LABEL_OR_ID")]
    cut_point_rules: Vec<String>,

    /// Stop after applying a rule with this label or unique ID. May be repeated.
    #[arg(long = "terminal-rule", value_name = "LABEL_OR_ID")]
    terminal_rules: Vec<String>,

    /// Choose all rewrites or ordered first-applicable rewriting.
    #[arg(long, value_enum, default_value_t = ExecutionStrategyArg::All)]
    strategy: ExecutionStrategyArg,

    #[command(flatten)]
    search: SearchArgs,

    #[command(flatten)]
    timeout: ExecutionTimeoutArgs,

    #[command(flatten)]
    smt: SmtArgs,

    #[command(flatten)]
    source: SourceArgs,
}

#[derive(Debug, Args)]
struct KoreExecArgs {
    /// Compiled textual KORE definition.
    #[arg(value_name = "DEFINITION_KORE")]
    definition: PathBuf,

    /// Module to verify and execute.
    #[arg(short = 'm', long, value_name = "MODULE")]
    module: String,

    /// Rule-only textual KORE module to add before execution. May be repeated.
    #[arg(long = "add-module", value_name = "MODULE_KORE")]
    added_modules: Vec<PathBuf>,

    /// Initial constrained text, JSON v1, or binary KORE pattern.
    #[arg(short = 'p', long, value_name = "PATTERN_KORE")]
    pattern: PathBuf,

    /// Maximum number of semantic rewrite steps per execution branch.
    #[arg(long, value_name = "STEPS")]
    depth: Option<u64>,

    /// Write the resulting KORE pattern to this file instead of standard output.
    #[arg(short, long, value_name = "OUTPUT_KORE")]
    output: Option<PathBuf>,

    /// Maximum number of live execution or search branches.
    #[arg(long = "breadth", value_name = "BRANCHES")]
    breadth_limit: Option<usize>,

    /// Stop and return the current configuration when execution first branches.
    #[arg(long)]
    execute_to_branch: bool,

    /// Stop before applying a rule with this label or unique ID. May be repeated.
    #[arg(long = "cut-point-rule", value_name = "LABEL_OR_ID")]
    cut_point_rules: Vec<String>,

    /// Stop after applying a rule with this label or unique ID. May be repeated.
    #[arg(long = "terminal-rule", value_name = "LABEL_OR_ID")]
    terminal_rules: Vec<String>,

    /// Choose all rewrites or ordered first-applicable rewriting.
    #[arg(long, value_enum, default_value_t = ExecutionStrategyArg::All)]
    strategy: ExecutionStrategyArg,

    #[command(flatten)]
    search: SearchArgs,

    #[command(flatten)]
    timeout: ExecutionTimeoutArgs,

    #[command(flatten)]
    smt: SmtArgs,
}

#[derive(Debug, Args)]
struct KoreSimplifyArgs {
    /// Compiled textual KORE definition.
    #[arg(value_name = "DEFINITION_KORE")]
    definition: PathBuf,

    /// Module to verify and use for simplification.
    #[arg(short = 'm', long, value_name = "MODULE")]
    module: String,

    /// Text, JSON v1, or binary KORE pattern to simplify.
    #[arg(short = 'p', long, value_name = "PATTERN_KORE")]
    pattern: PathBuf,

    /// Write the simplified KORE pattern to this file instead of standard output.
    #[arg(short, long, value_name = "OUTPUT_KORE")]
    output: Option<PathBuf>,

    #[command(flatten)]
    smt: SmtArgs,
}

#[derive(Debug, Args)]
struct KoreGetModelArgs {
    /// Compiled textual KORE definition.
    #[arg(value_name = "DEFINITION_KORE")]
    definition: PathBuf,

    /// Module to verify and use for model extraction.
    #[arg(short = 'm', long, value_name = "MODULE")]
    module: String,

    /// Text, JSON v1, or binary KORE pattern whose predicate should be solved.
    #[arg(short = 'p', long, value_name = "PATTERN_KORE")]
    pattern: PathBuf,

    /// Write the JSON result to this file instead of standard output.
    #[arg(short, long, value_name = "OUTPUT_JSON")]
    output: Option<PathBuf>,

    #[command(flatten)]
    smt: SmtArgs,
}

#[derive(Debug, Args)]
struct KoreImpliesArgs {
    /// Compiled textual KORE definition.
    #[arg(value_name = "DEFINITION_KORE")]
    definition: PathBuf,

    /// Module to verify and use for implication.
    #[arg(short = 'm', long, value_name = "MODULE")]
    module: String,

    /// Antecedent text, JSON v1, or binary KORE pattern.
    #[arg(long, value_name = "PATTERN_KORE")]
    antecedent: PathBuf,

    /// Consequent text, JSON v1, or binary KORE pattern.
    #[arg(long, value_name = "PATTERN_KORE")]
    consequent: PathBuf,

    /// Write the JSON result to this file instead of standard output.
    #[arg(short, long, value_name = "OUTPUT_JSON")]
    output: Option<PathBuf>,

    #[command(flatten)]
    smt: SmtArgs,
}

#[derive(Debug, Args)]
struct KoreRpcArgs {
    /// Compiled textual KORE definition.
    #[arg(value_name = "DEFINITION_KORE")]
    definition: PathBuf,

    /// Default module used by requests that do not select one.
    #[arg(short = 'm', long, value_name = "MODULE")]
    module: String,

    /// TCP port on which the raw JSON-RPC server listens. Use 0 for an ephemeral port.
    #[arg(long = "server-port", value_name = "PORT")]
    port: u16,

    /// Interface on which the server listens.
    #[arg(long, default_value = "127.0.0.1", value_name = "ADDRESS")]
    host: String,

    #[command(flatten)]
    smt: SmtArgs,
}

#[derive(Debug, Args)]
struct KoreMatchDisjunctionArgs {
    /// Compiled textual KORE definition.
    #[arg(value_name = "DEFINITION_KORE")]
    definition: PathBuf,

    /// Module to verify and use for matching.
    #[arg(short = 'm', long, value_name = "MODULE")]
    module: String,

    /// KORE file containing a disjunction of constrained configurations.
    #[arg(long, value_name = "DISJUNCTION_KORE")]
    disjunction: PathBuf,

    /// Constrained KORE pattern to match against each configuration.
    #[arg(long = "match", value_name = "PATTERN_KORE")]
    pattern: PathBuf,

    /// Write the resulting KORE predicate to this file instead of standard output.
    #[arg(short, long, value_name = "OUTPUT_KORE")]
    output: Option<PathBuf>,
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
    #[arg(long, value_name = "STEPS")]
    depth: Option<u64>,

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
    smt: SmtArgs,

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

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
enum ExecutionStrategyArg {
    #[default]
    All,
    Any,
}

impl From<ExecutionStrategyArg> for ExecutionMode {
    fn from(strategy: ExecutionStrategyArg) -> Self {
        match strategy {
            ExecutionStrategyArg::All => Self::All,
            ExecutionStrategyArg::Any => Self::Any,
        }
    }
}

#[derive(Debug)]
struct KastOptions {
    common: CommonOptions,
    backend: Option<CompilationBackend>,
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
    config_vars: Vec<String>,
    depth: u64,
    breadth_limit: Option<usize>,
    execute_to_branch: bool,
    cut_point_rules: BTreeSet<String>,
    terminal_rules: BTreeSet<String>,
    strategy: ExecutionMode,
    search: Option<KrunSearchOptions>,
    step_timeout: Option<Duration>,
    moving_average_timeout: bool,
    smt: Z3Options,
}

#[derive(Debug)]
struct KrunSearchOptions {
    search_type: SearchType,
    pattern: Option<PathBuf>,
    bound: Option<usize>,
}

#[derive(Debug)]
struct BackendRunOptions {
    depth: u64,
    breadth_limit: Option<usize>,
    execute_to_branch: bool,
    cut_point_rules: BTreeSet<String>,
    terminal_rules: BTreeSet<String>,
    strategy: ExecutionMode,
    search: Option<KrunSearchOptions>,
    step_timeout: Option<Duration>,
    moving_average_timeout: bool,
    smt: Z3Options,
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
    smt: Z3Options,
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

impl SearchArgs {
    fn into_options(self) -> Option<KrunSearchOptions> {
        let search_type = if self.search_final {
            Some(SearchType::Final)
        } else if self.search_all {
            Some(SearchType::Star)
        } else if self.search_one_step {
            Some(SearchType::One)
        } else if self.search_one_or_more_steps {
            Some(SearchType::Plus)
        } else {
            None
        };
        search_type.map(|search_type| KrunSearchOptions {
            search_type,
            pattern: self.search_pattern,
            bound: self.search_bound,
        })
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
            backend: arguments.backend.map(Into::into),
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
            config_vars: arguments.config_vars,
            depth: arguments.depth.unwrap_or(u64::MAX),
            breadth_limit: arguments.breadth_limit,
            execute_to_branch: arguments.execute_to_branch,
            cut_point_rules: arguments.cut_point_rules.into_iter().collect(),
            terminal_rules: arguments.terminal_rules.into_iter().collect(),
            strategy: arguments.strategy.into(),
            search: arguments.search.into_options(),
            step_timeout: arguments.timeout.timeout(),
            moving_average_timeout: arguments.timeout.moving_average,
            smt: arguments.smt.options(),
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
            depth: arguments.depth.unwrap_or(u64::MAX),
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
            smt: arguments.smt.options(),
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
    let loaded = load_definition(&options.common, options.backend, None)?;
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
    let syntax = parse_kore_definition(&compiled.definition_kore)?;
    let declared = declared_configuration_variables(&syntax)?;
    let assignments = validate_configuration_assignments(&options.config_vars, &declared)?;
    let mut config_bindings = Vec::new();
    for (name, source, sort) in assignments {
        let value = parser.parse(&sort, &source).map_err(|error| {
            format!("could not parse configuration variable {name} at sort {sort}: {error}")
        })?;
        let value = injector.inject_at_top(&value)?;
        let value = term_to_kore_from_resolved(&loaded.resolved, &options.common.module, &value)?;
        config_bindings.push(ConfigurationBinding {
            name,
            value,
            sort: encode_kore_sort(&sort),
        });
    }
    let initial = top_cell_initializer(program, encode_kore_sort(&program_sort), config_bindings);

    let backend = BackendDefinition::internalize(&syntax, &options.common.module)?;
    let initial = backend.internalize_frontend_term(&initial, &[])?;
    let output = run_backend(
        &backend,
        Pattern {
            term: initial,
            constraints: Vec::new(),
        },
        BackendRunOptions {
            depth: options.depth,
            breadth_limit: options.breadth_limit,
            execute_to_branch: options.execute_to_branch,
            cut_point_rules: options.cut_point_rules,
            terminal_rules: options.terminal_rules,
            strategy: options.strategy,
            search: options.search,
            step_timeout: options.step_timeout,
            moving_average_timeout: options.moving_average_timeout,
            smt: options.smt,
        },
    )?;
    println!("{}", KorePrinter::pretty(100).print_pattern(&output));
    Ok(())
}

fn kore_exec(options: KoreExecArgs) -> Result<(), Box<dyn Error>> {
    let definition_source = fs::read_to_string(&options.definition)?;
    let definition = parse_kore_definition(&definition_source).map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "could not parse KORE definition {}: {error}",
                options.definition.display()
            ),
        )
    })?;
    let mut session = BackendSession::new(definition, &options.module);
    for path in &options.added_modules {
        let source = fs::read_to_string(path)?;
        let module = parse_kore_module(&source).map_err(|error| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "could not parse added KORE module {}: {error}",
                    path.display()
                ),
            )
        })?;
        session.add_module(&source, module, true)?;
    }
    let backend = session.definition(None)?;
    let initial = load_backend_pattern(&backend, &options.pattern, "initial")?;
    let output = run_backend(
        &backend,
        initial,
        BackendRunOptions {
            depth: options.depth.unwrap_or(u64::MAX),
            breadth_limit: options.breadth_limit,
            execute_to_branch: options.execute_to_branch,
            cut_point_rules: options.cut_point_rules.into_iter().collect(),
            terminal_rules: options.terminal_rules.into_iter().collect(),
            strategy: options.strategy.into(),
            search: options.search.into_options(),
            step_timeout: options.timeout.timeout(),
            moving_average_timeout: options.timeout.moving_average,
            smt: options.smt.options(),
        },
    )?;
    let output = KorePrinter::pretty(100).print_pattern(&output);
    if let Some(path) = options.output {
        fs::write(path, output)?;
    } else {
        println!("{output}");
    }
    Ok(())
}

fn kore_rpc(options: KoreRpcArgs) -> Result<(), Box<dyn Error>> {
    let definition_source = fs::read_to_string(&options.definition)?;
    let definition = parse_kore_definition(&definition_source).map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "could not parse KORE definition {}: {error}",
                options.definition.display()
            ),
        )
    })?;
    rpc::serve(
        BackendSession::new(definition, options.module),
        (options.host.as_str(), options.port),
        options.smt.options(),
    )
}

fn kore_simplify(options: KoreSimplifyArgs) -> Result<(), Box<dyn Error>> {
    let definition_source = fs::read_to_string(&options.definition)?;
    let definition = parse_kore_definition(&definition_source).map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "could not parse KORE definition {}: {error}",
                options.definition.display()
            ),
        )
    })?;
    let backend = BackendDefinition::internalize(&definition, &options.module)?;
    let syntax = load_kore_syntax(&options.pattern, "simplification")?;
    let output = simplify_kore_pattern_with_options(&backend, &syntax, options.smt.options())?;
    let output = KorePrinter::pretty(100).print_pattern(&output);
    if let Some(path) = options.output {
        fs::write(path, output)?;
    } else {
        println!("{output}");
    }
    Ok(())
}

#[cfg(test)]
fn simplify_kore_pattern(
    definition: &BackendDefinition,
    syntax: &KorePattern,
) -> Result<KorePattern, Box<dyn Error>> {
    simplify_kore_pattern_with_options(definition, syntax, Z3Options::default())
}

fn simplify_kore_pattern_with_options(
    definition: &BackendDefinition,
    syntax: &KorePattern,
    options: Z3Options,
) -> Result<KorePattern, Box<dyn Error>> {
    let solver = Z3Solver::with_options(definition, options)
        .map_err(|error| io::Error::other(format!("could not initialize Z3: {error:?}")))?;
    match definition.internalize_pattern(syntax, &[]) {
        Ok(pattern) => {
            let simplified = simplify_pattern_with_solver(
                definition,
                &pattern,
                SimplificationOptions::unbounded(),
                &solver,
            )
            .map_err(|error| {
                io::Error::other(format!("could not simplify KORE pattern: {error:?}"))
            })?;
            return Ok(externalize::constrained_pattern(&simplified));
        }
        Err(DefinitionError::RulePattern(RulePatternError::MissingTerm)) => {}
        Err(error) => return Err(error.into()),
    }
    let (predicate, result_sort) = definition.internalize_predicate(syntax, &[])?;
    let simplified = simplify_and_decide_predicate_with_solver(
        definition,
        &predicate,
        &[],
        SimplificationOptions::unbounded(),
        &solver,
    )
    .map_err(|error| io::Error::other(format!("could not simplify KORE pattern: {error:?}")))?;
    Ok(externalize::ml_pattern(&simplified, &result_sort))
}

fn kore_get_model(options: KoreGetModelArgs) -> Result<(), Box<dyn Error>> {
    let definition_source = fs::read_to_string(&options.definition)?;
    let definition = parse_kore_definition(&definition_source).map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "could not parse KORE definition {}: {error}",
                options.definition.display()
            ),
        )
    })?;
    let backend = BackendDefinition::internalize(&definition, &options.module)?;
    let syntax = load_kore_syntax(&options.pattern, "model")?;
    let model = match backend.internalize_model_predicate(&syntax, &[])? {
        None => (ModelResult::Unknown("no predicate".into()), None),
        Some((predicate, result_sort)) => {
            let solver = Z3Solver::with_options(&backend, options.smt.options())
                .map_err(|error| io::Error::other(format!("could not initialize Z3: {error:?}")))?;
            let result = solver
                .get_model(&[predicate], &Substitution::new())
                .map_err(|error| io::Error::other(format!("could not obtain model: {error:?}")))?;
            (result, Some(result_sort))
        }
    };
    let output = model_output(model.0, model.1.as_ref())?;
    if let Some(path) = options.output {
        fs::write(path, output)?;
    } else {
        println!("{output}");
    }
    Ok(())
}

fn model_output(
    result: ModelResult,
    result_sort: Option<&BackendSort>,
) -> Result<String, Box<dyn Error>> {
    let (satisfiable, substitution) = match result {
        ModelResult::Sat(substitution) => {
            let pattern = result_sort.and_then(|sort| model_substitution(&substitution, sort));
            ("Sat", pattern)
        }
        ModelResult::Unsat => ("Unsat", None),
        ModelResult::Unknown(_) => ("Unknown", None),
    };
    let mut output = serde_json::json!({ "satisfiable": satisfiable });
    if let Some(substitution) = substitution {
        output["substitution"] = kore_json::to_value(&substitution)?;
    }
    Ok(serde_json::to_string_pretty(&output)?)
}

fn model_substitution(
    substitution: &Substitution,
    result_sort: &BackendSort,
) -> Option<KorePattern> {
    let mut bindings = substitution.iter().collect::<Vec<_>>();
    bindings.sort_by(|(left, _), (right, _)| {
        compare_natural_names(&left.name, &right.name).then_with(|| left.sort.cmp(&right.sort))
    });
    let bindings = bindings
        .into_iter()
        .map(|(variable, value)| {
            externalize::predicate_pattern(
                &Predicate::Equals(Term::variable(variable.clone()), value.clone()),
                result_sort,
            )
        })
        .collect::<Vec<_>>();
    match bindings.as_slice() {
        [] => None,
        [binding] => Some(binding.clone()),
        _ => Some(KorePattern::And {
            sort: externalize::sort(result_sort),
            arguments: bindings,
        }),
    }
}

fn compare_natural_names(left: &str, right: &str) -> std::cmp::Ordering {
    let (left_prefix, left_number) = trailing_number(left);
    let (right_prefix, right_number) = trailing_number(right);
    if left_prefix == right_prefix && !left_number.is_empty() && !right_number.is_empty() {
        let left_value = left_number.trim_start_matches('0');
        let right_value = right_number.trim_start_matches('0');
        let left_value = if left_value.is_empty() {
            "0"
        } else {
            left_value
        };
        let right_value = if right_value.is_empty() {
            "0"
        } else {
            right_value
        };
        return left_value
            .len()
            .cmp(&right_value.len())
            .then_with(|| left_value.cmp(right_value))
            .then_with(|| left_number.len().cmp(&right_number.len()))
            .then_with(|| left.cmp(right));
    }
    left.cmp(right)
}

fn trailing_number(name: &str) -> (&str, &str) {
    let prefix_length = name
        .trim_end_matches(|character: char| character.is_ascii_digit())
        .len();
    (&name[..prefix_length], &name[prefix_length..])
}

fn kore_implies(options: KoreImpliesArgs) -> Result<(), Box<dyn Error>> {
    // Real compiled configurations can contain patterns hundreds of nodes deep. Keep the entire
    // decode/verify/drop lifecycle on a suitably sized stack instead of overflowing the platform's
    // relatively small main-thread stack.
    let worker = std::thread::Builder::new()
        .name("krust-kore-implies".into())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || kore_implies_inner(options).map_err(|error| error.to_string()))?;
    match worker.join() {
        Ok(Ok(())) => Ok(()),
        Ok(Err(error)) => Err(io::Error::other(error).into()),
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

fn kore_implies_inner(options: KoreImpliesArgs) -> Result<(), Box<dyn Error>> {
    let definition_source = fs::read_to_string(&options.definition)?;
    let definition = parse_kore_definition(&definition_source).map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "could not parse KORE definition {}: {error}",
                options.definition.display()
            ),
        )
    })?;
    let backend = BackendDefinition::internalize(&definition, &options.module)?;
    let antecedent_syntax = load_kore_syntax(&options.antecedent, "antecedent")?;
    let consequent_syntax = load_kore_syntax(&options.consequent, "consequent")?;
    backend
        .validate_implication_pattern(&antecedent_syntax)
        .map_err(|error| io::Error::other(format!("invalid implication antecedent: {error}")))?;
    backend
        .validate_implication_pattern(&consequent_syntax)
        .map_err(|error| io::Error::other(format!("invalid implication consequent: {error}")))?;
    reject_non_singleton_implication_pattern(&antecedent_syntax, "antecedent")?;
    reject_non_singleton_implication_pattern(&consequent_syntax, "consequent")?;
    reject_implication_variable_capture(&antecedent_syntax, &consequent_syntax)?;

    let sort_variables = implication_sort_variables(&antecedent_syntax, &consequent_syntax);
    let (antecedent, antecedent_existentials) = backend
        .internalize_implication_pattern(&antecedent_syntax, &sort_variables)
        .map_err(|error| io::Error::other(format!("invalid implication antecedent: {error}")))?;
    let result_sort = antecedent.term.sort();
    let result = if matches!(strip_exists(&consequent_syntax), KorePattern::Not { .. }) {
        ImplicationResult {
            status: ImplicationStatus::Invalid,
            condition: None,
            failure: None,
        }
    } else {
        let (consequent, consequent_existentials) = backend
            .internalize_implication_pattern(&consequent_syntax, &sort_variables)
            .map_err(|error| {
                io::Error::other(format!("invalid implication consequent: {error}"))
            })?;
        if antecedent.term.sort() != consequent.term.sort() {
            return Err(io::Error::other(format!(
                "antecedent and consequent sorts differ: {:?} and {:?}",
                antecedent.term.sort(),
                consequent.term.sort()
            ))
            .into());
        }
        let solver = Z3Solver::with_options(&backend, options.smt.options())
            .map_err(|error| io::Error::other(format!("could not initialize Z3: {error:?}")))?;
        check_implication_with_existentials_complete(
            &backend,
            &antecedent,
            &antecedent_existentials,
            &consequent,
            &consequent_existentials,
            &solver,
        )?
    };
    let output = implication_output(&antecedent_syntax, &consequent_syntax, &result_sort, result)?;
    if let Some(path) = options.output {
        fs::write(path, output)?;
    } else {
        println!("{output}");
    }
    Ok(())
}

fn implication_output(
    antecedent: &KorePattern,
    consequent: &KorePattern,
    result_sort: &BackendSort,
    result: ImplicationResult,
) -> Result<String, Box<dyn Error>> {
    let status = match result.status {
        ImplicationStatus::Valid => "valid",
        ImplicationStatus::Invalid => "invalid",
        ImplicationStatus::Indeterminate => "unknown",
    };
    let implication = KorePattern::Implies {
        sort: externalize::sort(result_sort),
        left: Box::new(antecedent.clone()),
        right: Box::new(consequent.clone()),
    };
    let mut output = serde_json::json!({
        "status": status,
        "implication": kore_json_value(&implication)?,
    });
    if let Some(condition) = result.condition {
        let antecedent_variable = match strip_exists(antecedent) {
            KorePattern::Variable(variable) => Some(variable.name.as_str()),
            _ => None,
        };
        output["condition"] =
            implication_condition_output(&condition, result_sort, antecedent_variable)?;
    }
    Ok(serde_json::to_string_pretty(&output)?)
}

fn implication_condition_output(
    condition: &ImplicationCondition,
    result_sort: &BackendSort,
    antecedent_variable: Option<&str>,
) -> Result<serde_json::Value, Box<dyn Error>> {
    let substitution =
        implication_substitution(&condition.substitution, result_sort, antecedent_variable)
            .unwrap_or_else(|| KorePattern::Top {
                sort: externalize::sort(result_sort),
            });
    let predicate = match condition.predicates.as_slice() {
        [] => KorePattern::Top {
            sort: externalize::sort(result_sort),
        },
        [predicate] => externalize::predicate_pattern(predicate, result_sort),
        predicates => KorePattern::And {
            sort: externalize::sort(result_sort),
            arguments: predicates
                .iter()
                .map(|predicate| externalize::predicate_pattern(predicate, result_sort))
                .collect(),
        },
    };
    Ok(serde_json::json!({
        "substitution": kore_json_value(&substitution)?,
        "predicate": kore_json_value(&predicate)?,
    }))
}

fn implication_substitution(
    substitution: &Substitution,
    result_sort: &BackendSort,
    antecedent_variable: Option<&str>,
) -> Option<KorePattern> {
    let mut bindings = substitution.iter().collect::<Vec<_>>();
    bindings.sort_by_key(|(variable, _)| (variable.name.clone(), variable.sort.clone()));
    let mut bindings = bindings.into_iter().map(|(variable, value)| {
        let mut output_variable = variable.clone();
        let consequent_existential = variable
            .name
            .as_ref()
            .rsplit_once("!exists")
            .filter(|(_, suffix)| suffix.chars().all(|character| character.is_ascii_digit()));
        if let Some((name, _)) = consequent_existential {
            output_variable.name = BackendName::from(name);
        }
        let prefer_antecedent = consequent_existential.is_some()
            && matches!(
                value.kind(),
                TermKind::Variable(value) if antecedent_variable == Some(value.name.as_ref())
            );
        let (left, right) = if prefer_antecedent {
            (
                externalize::term(value),
                externalize::term(&Term::variable(output_variable)),
            )
        } else {
            (
                externalize::term(&Term::variable(output_variable)),
                externalize::term(value),
            )
        };
        KorePattern::Equals {
            operand_sort: externalize::sort(&variable.sort),
            result_sort: externalize::sort(result_sort),
            left: Box::new(left),
            right: Box::new(right),
        }
    });
    let mut result = bindings.next()?;
    for binding in bindings {
        result = KorePattern::And {
            sort: externalize::sort(result_sort),
            arguments: vec![result, binding],
        };
    }
    Some(result)
}

fn kore_json_value(pattern: &KorePattern) -> Result<serde_json::Value, Box<dyn Error>> {
    Ok(kore_json::to_value(pattern)?)
}

fn reject_non_singleton_implication_pattern(
    pattern: &KorePattern,
    side: &str,
) -> Result<(), Box<dyn Error>> {
    match strip_exists(pattern) {
        KorePattern::Or { arguments, .. } if arguments.len() != 1 => Err(io::Error::other(
            format!("implication {side} must contain exactly one pattern"),
        )
        .into()),
        KorePattern::Mu { .. } | KorePattern::Nu { .. } if side == "antecedent" => {
            Err(io::Error::other("implication antecedent must be function-like").into())
        }
        _ => Ok(()),
    }
}

fn strip_exists(mut pattern: &KorePattern) -> &KorePattern {
    while let KorePattern::Exists { body, .. } = pattern {
        pattern = body;
    }
    pattern
}

fn implication_sort_variables(
    antecedent: &KorePattern,
    consequent: &KorePattern,
) -> Vec<BackendName> {
    let mut variables = BTreeSet::new();
    collect_pattern_sort_variables(antecedent, &mut variables);
    collect_pattern_sort_variables(consequent, &mut variables);
    variables.into_iter().map(BackendName::from).collect()
}

fn collect_sort_variables(sort: &KoreSort, output: &mut BTreeSet<String>) {
    match sort {
        KoreSort::Variable(name) => {
            output.insert(name.clone());
        }
        KoreSort::Application { arguments, .. } => {
            for argument in arguments {
                collect_sort_variables(argument, output);
            }
        }
    }
}

fn collect_pattern_sort_variables(pattern: &KorePattern, output: &mut BTreeSet<String>) {
    let recurse =
        |pattern, output: &mut BTreeSet<String>| collect_pattern_sort_variables(pattern, output);
    match pattern {
        KorePattern::String(_) => {}
        KorePattern::Variable(variable) => collect_sort_variables(&variable.sort, output),
        KorePattern::Application { symbol, arguments }
        | KorePattern::AssociativeApplication {
            symbol, arguments, ..
        } => {
            for sort in &symbol.sort_parameters {
                collect_sort_variables(sort, output);
            }
            for argument in arguments {
                recurse(argument, output);
            }
        }
        KorePattern::Top { sort }
        | KorePattern::Bottom { sort }
        | KorePattern::Not { sort, .. }
        | KorePattern::Next { sort, .. }
        | KorePattern::And { sort, .. }
        | KorePattern::Or { sort, .. }
        | KorePattern::Rewrites { sort, .. }
        | KorePattern::Implies { sort, .. }
        | KorePattern::Iff { sort, .. }
        | KorePattern::Exists { sort, .. }
        | KorePattern::Forall { sort, .. } => collect_sort_variables(sort, output),
        KorePattern::Mu { variable, .. } | KorePattern::Nu { variable, .. } => {
            collect_sort_variables(&variable.sort, output);
        }
        KorePattern::Ceil {
            operand_sort,
            result_sort,
            ..
        }
        | KorePattern::Floor {
            operand_sort,
            result_sort,
            ..
        }
        | KorePattern::Equals {
            operand_sort,
            result_sort,
            ..
        }
        | KorePattern::In {
            operand_sort,
            result_sort,
            ..
        } => {
            collect_sort_variables(operand_sort, output);
            collect_sort_variables(result_sort, output);
        }
        KorePattern::DomainValue { sort, .. } => collect_sort_variables(sort, output),
    }
    match pattern {
        KorePattern::Not { argument, .. }
        | KorePattern::Next { argument, .. }
        | KorePattern::Ceil { argument, .. }
        | KorePattern::Floor { argument, .. } => recurse(argument, output),
        KorePattern::And { arguments, .. } | KorePattern::Or { arguments, .. } => {
            for argument in arguments {
                recurse(argument, output);
            }
        }
        KorePattern::Rewrites { left, right, .. }
        | KorePattern::Implies { left, right, .. }
        | KorePattern::Iff { left, right, .. }
        | KorePattern::Equals { left, right, .. }
        | KorePattern::In { left, right, .. } => {
            recurse(left, output);
            recurse(right, output);
        }
        KorePattern::Exists { variable, body, .. }
        | KorePattern::Forall { variable, body, .. }
        | KorePattern::Mu { variable, body }
        | KorePattern::Nu { variable, body } => {
            collect_sort_variables(&variable.sort, output);
            recurse(body, output);
        }
        _ => {}
    }
}

fn reject_implication_variable_capture(
    antecedent: &KorePattern,
    consequent: &KorePattern,
) -> Result<(), Box<dyn Error>> {
    let mut antecedent_free = BTreeSet::new();
    collect_free_kore_variables(antecedent, &mut BTreeSet::new(), &mut antecedent_free);
    let mut captured = Vec::new();
    let mut body = consequent;
    while let KorePattern::Exists {
        variable,
        body: next,
        ..
    } = body
    {
        if antecedent_free.contains(variable) {
            captured.push(variable.name.clone());
        }
        body = next;
    }
    if captured.is_empty() {
        Ok(())
    } else {
        Err(io::Error::other(format!(
            "consequent existentials capture antecedent variables: {}",
            captured.join(", ")
        ))
        .into())
    }
}

fn collect_free_kore_variables(
    pattern: &KorePattern,
    bound: &mut BTreeSet<KoreVariable>,
    output: &mut BTreeSet<KoreVariable>,
) {
    match pattern {
        KorePattern::Variable(variable) => {
            if !bound.contains(variable) {
                output.insert(variable.clone());
            }
        }
        KorePattern::Application { arguments, .. }
        | KorePattern::AssociativeApplication { arguments, .. }
        | KorePattern::And { arguments, .. }
        | KorePattern::Or { arguments, .. } => {
            for argument in arguments {
                collect_free_kore_variables(argument, bound, output);
            }
        }
        KorePattern::Not { argument, .. }
        | KorePattern::Next { argument, .. }
        | KorePattern::Ceil { argument, .. }
        | KorePattern::Floor { argument, .. } => {
            collect_free_kore_variables(argument, bound, output);
        }
        KorePattern::Rewrites { left, right, .. }
        | KorePattern::Implies { left, right, .. }
        | KorePattern::Iff { left, right, .. }
        | KorePattern::Equals { left, right, .. }
        | KorePattern::In { left, right, .. } => {
            collect_free_kore_variables(left, bound, output);
            collect_free_kore_variables(right, bound, output);
        }
        KorePattern::Exists { variable, body, .. }
        | KorePattern::Forall { variable, body, .. }
        | KorePattern::Mu { variable, body }
        | KorePattern::Nu { variable, body } => {
            let inserted = bound.insert(variable.clone());
            collect_free_kore_variables(body, bound, output);
            if inserted {
                bound.remove(variable);
            }
        }
        KorePattern::String(_)
        | KorePattern::Top { .. }
        | KorePattern::Bottom { .. }
        | KorePattern::DomainValue { .. } => {}
    }
}

fn kore_match_disjunction(options: KoreMatchDisjunctionArgs) -> Result<(), Box<dyn Error>> {
    let definition_source = fs::read_to_string(&options.definition)?;
    let definition = parse_kore_definition(&definition_source).map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "could not parse KORE definition {}: {error}",
                options.definition.display()
            ),
        )
    })?;
    let backend = BackendDefinition::internalize(&definition, &options.module)?;

    let target_source = fs::read_to_string(&options.pattern)?;
    let target = parse_kore_pattern(&target_source).map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "could not parse match pattern {}: {error}",
                options.pattern.display()
            ),
        )
    })?;
    let target = backend.internalize_pattern(&target, &[])?;

    let disjunction_source = fs::read_to_string(&options.disjunction)?;
    let disjunction = parse_kore_pattern(&disjunction_source).map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "could not parse configuration disjunction {}: {error}",
                options.disjunction.display()
            ),
        )
    })?;
    let alternatives = backend.internalize_disjunction(&disjunction, &[])?;
    let matches =
        match_disjunction(&backend, &target, &alternatives).map_err(pattern_match_error)?;
    let output_sort = externalize::sort(&target.term.sort());
    let output = pattern_matches_output(&matches, &output_sort, &target.term.sort());
    let output = KorePrinter::pretty(100).print_pattern(&output);
    if let Some(path) = options.output {
        fs::write(path, output)?;
    } else {
        println!("{output}");
    }
    Ok(())
}

fn pattern_match_error(error: PatternMatchError) -> io::Error {
    io::Error::other(format!("KORE pattern match was indeterminate: {error:?}"))
}

fn run_backend(
    backend: &BackendDefinition,
    initial: Pattern,
    options: BackendRunOptions,
) -> Result<KorePattern, Box<dyn Error>> {
    let output_sort = externalize::sort(&initial.term.sort());
    let solver = Z3Solver::with_options(backend, options.smt)
        .map_err(|error| io::Error::other(format!("could not initialize Z3: {error:?}")))?;
    if let Some(search) = options.search {
        let target = match search.pattern {
            Some(path) => load_backend_pattern(backend, &path, "search")?,
            None => Pattern {
                term: Term::variable(Variable::new("Result", initial.term.sort())),
                constraints: Vec::new(),
            },
        };
        let result = search_pattern_with_solver(
            backend,
            initial,
            &target,
            SearchOptions {
                search_type: search.search_type,
                max_depth: options.depth,
                max_breadth: options.breadth_limit,
                max_results: search.bound,
                ..SearchOptions::default()
            },
            &solver,
        );
        for effect in &result.effects {
            match effect {
                BuiltinEffect::UserLog(message) => eprintln!("{message}"),
            }
        }
        if let Some(incomplete) = result
            .incomplete
            .iter()
            .find(|incomplete| !matches!(incomplete, IncompleteSearch::DepthBound(_)))
        {
            return Err(io::Error::other(format!(
                "in-process backend search was incomplete: {incomplete:?}"
            ))
            .into());
        }
        return Ok(search_output(&result, &output_sort));
    }
    let execution = execute_with_solver_and_observer(
        backend,
        initial,
        ExecutionOptions {
            max_depth: options.depth,
            max_breadth: options.breadth_limit,
            mode: options.strategy,
            branch_mode: if options.execute_to_branch {
                ExecutionBranchMode::StopAtBranch
            } else {
                ExecutionBranchMode::ExploreAll
            },
            cut_point_rules: options.cut_point_rules,
            terminal_rules: options.terminal_rules,
            step_timeout: options.step_timeout,
            moving_average_timeout: options.moving_average_timeout,
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
            HaltReason::Cancelled | HaltReason::Indeterminate(_) | HaltReason::Simplification(_)
        )
    }) {
        return Err(io::Error::other(format!(
            "in-process backend halted at depth {}: {:?}",
            leaf.depth, leaf.halt_reason
        ))
        .into());
    }
    let final_sort = execution
        .leaves
        .first()
        .map(|leaf| externalize::sort(&leaf.pattern.term.sort()))
        .unwrap_or_else(|| output_sort.clone());
    let mut states = execution
        .leaves
        .iter()
        .filter(|leaf| !matches!(leaf.halt_reason, HaltReason::Trivial | HaltReason::Vacuous))
        .map(|leaf| externalize::constrained_pattern(&leaf.pattern))
        .collect::<Vec<_>>();
    Ok(match states.len() {
        0 => KorePattern::Bottom { sort: output_sort },
        1 => states.pop().unwrap(),
        _ => KorePattern::Or {
            sort: final_sort,
            arguments: states,
        },
    })
}

fn load_backend_pattern(
    definition: &BackendDefinition,
    path: &Path,
    purpose: &str,
) -> Result<Pattern, Box<dyn Error>> {
    let input = fs::read(path)?;
    decode_backend_pattern(definition, path, purpose, &input)
}

fn load_kore_syntax(path: &Path, purpose: &str) -> Result<KorePattern, Box<dyn Error>> {
    let input = fs::read(path)?;
    decode_kore_syntax(path, purpose, &input)
}

fn decode_kore_syntax(
    path: &Path,
    purpose: &str,
    input: &[u8],
) -> Result<KorePattern, Box<dyn Error>> {
    if input.starts_with(b"\x7fKORE") {
        return kore_binary::decode_term(input)
            .map_err(|error| invalid_kore_pattern(path, purpose, "binary", error));
    }
    let source = std::str::from_utf8(input)
        .map_err(|error| invalid_kore_pattern(path, purpose, "UTF-8", error))?;
    if source.trim_start().starts_with('{') {
        kore_json::from_str_unbounded(source)
            .map_err(|error| invalid_kore_pattern(path, purpose, "JSON", error))
    } else {
        parse_kore_pattern(source)
            .map_err(|error| invalid_kore_pattern(path, purpose, "text", error))
    }
}

fn decode_backend_pattern(
    definition: &BackendDefinition,
    path: &Path,
    purpose: &str,
    input: &[u8],
) -> Result<Pattern, Box<dyn Error>> {
    if input.starts_with(b"\x7fKORE") {
        return backend_binary::decode_pattern(definition, input)
            .map_err(|error| invalid_kore_pattern(path, purpose, "binary", error));
    }
    let source = std::str::from_utf8(input)
        .map_err(|error| invalid_kore_pattern(path, purpose, "UTF-8", error))?;
    let syntax = if source.trim_start().starts_with('{') {
        kore_json::from_str_unbounded(source)
            .map_err(|error| invalid_kore_pattern(path, purpose, "JSON", error))?
    } else {
        parse_kore_pattern(source)
            .map_err(|error| invalid_kore_pattern(path, purpose, "text", error))?
    };
    definition
        .internalize_pattern(&syntax, &[])
        .map_err(Into::into)
}

fn invalid_kore_pattern(
    path: &Path,
    purpose: &str,
    encoding: &str,
    error: impl fmt::Display,
) -> Box<dyn Error> {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!(
            "could not decode {purpose} {encoding} KORE pattern {}: {error}",
            path.display()
        ),
    )
    .into()
}

fn search_output(result: &PatternSearchResult, result_sort: &KoreSort) -> KorePattern {
    let solutions = result
        .matches
        .iter()
        .map(|found| {
            match_condition_output(
                &found.substitution,
                &found.constraints,
                result_sort,
                &found.state.pattern.term.sort(),
            )
        })
        .collect::<Vec<_>>();
    disjoin_outputs(solutions, result_sort)
}

fn pattern_matches_output(
    matches: &[PatternMatch],
    result_sort: &KoreSort,
    predicate_sort: &BackendSort,
) -> KorePattern {
    let solutions = matches
        .iter()
        .map(|found| {
            match_condition_output(
                &found.substitution,
                &found.constraints,
                result_sort,
                predicate_sort,
            )
        })
        .collect::<Vec<_>>();
    disjoin_outputs(solutions, result_sort)
}

fn match_condition_output(
    substitution: &Substitution,
    constraints: &[Predicate],
    result_sort: &KoreSort,
    predicate_sort: &BackendSort,
) -> KorePattern {
    let mut bindings = substitution.iter().collect::<Vec<_>>();
    bindings.sort_by(|(left, _), (right, _)| {
        left.name
            .cmp(&right.name)
            .then_with(|| left.sort.cmp(&right.sort))
    });
    let predicates = bindings
        .into_iter()
        .map(|(variable, value)| Predicate::Equals(Term::variable(variable.clone()), value.clone()))
        .chain(constraints.iter().cloned())
        .map(|predicate| externalize::predicate_pattern(&predicate, predicate_sort))
        .collect::<Vec<_>>();
    let mut predicates = predicates.into_iter();
    let Some(mut result) = predicates.next() else {
        return KorePattern::Top {
            sort: result_sort.clone(),
        };
    };
    for predicate in predicates {
        result = KorePattern::And {
            sort: result_sort.clone(),
            arguments: vec![result, predicate],
        };
    }
    result
}

fn disjoin_outputs(solutions: Vec<KorePattern>, result_sort: &KoreSort) -> KorePattern {
    let mut solutions = solutions.into_iter();
    let Some(mut result) = solutions.next() else {
        return KorePattern::Bottom {
            sort: result_sort.clone(),
        };
    };
    for solution in solutions {
        result = KorePattern::Or {
            sort: result_sort.clone(),
            arguments: vec![result, solution],
        };
    }
    result
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
    let mut proven_ids = spec_module
        .sentences
        .iter()
        .filter_map(|sentence| {
            let id = claim_unique_id(sentence)?;
            saved_claims
                .iter()
                .any(|saved| same_claim(sentence, saved))
                .then_some(id)
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
    let solver = Z3Solver::with_options_and_prelude(&backend, options.smt, smt_prelude.as_deref())
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

fn same_claim(left: &KoreSentence, right: &KoreSentence) -> bool {
    let (
        KoreSentence::Claim {
            parameters: left_parameters,
            pattern: left_pattern,
            ..
        },
        KoreSentence::Claim {
            parameters: right_parameters,
            pattern: right_pattern,
            ..
        },
    ) = (left, right)
    else {
        return false;
    };

    left_parameters == right_parameters && left_pattern == right_pattern
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

fn declared_configuration_variables(
    definition: &KoreDefinition,
) -> Result<BTreeMap<String, KastSort>, String> {
    let projection_sorts = definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            KoreSentence::SymbolDeclaration {
                symbol,
                result_sort,
                ..
            } if symbol.name.starts_with("Lblproject'Coln'") => {
                Some((symbol.name.clone(), result_sort.clone()))
            }
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let mut variables = BTreeMap::new();
    for sentence in definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
    {
        let pattern = match sentence {
            KoreSentence::Axiom { pattern, .. } | KoreSentence::Claim { pattern, .. } => pattern,
            _ => continue,
        };
        collect_projected_configuration_variables(pattern, &projection_sorts, &mut variables)?;
    }
    Ok(variables)
}

fn collect_projected_configuration_variables(
    pattern: &KorePattern,
    projection_sorts: &BTreeMap<String, KoreSort>,
    variables: &mut BTreeMap<String, KastSort>,
) -> Result<(), String> {
    if let KorePattern::Application { symbol, .. } = pattern
        && let Some(result_sort) = projection_sorts.get(&symbol.name)
    {
        let sort = k_rust::kast::convert::convert_sort(result_sort)
            .map_err(|error| format!("invalid configuration-variable sort: {error}"))?;
        let mut names = BTreeSet::new();
        collect_configuration_variable_tokens(pattern, &mut names);
        for name in names {
            let name = name.strip_prefix('$').unwrap_or(&name).to_owned();
            if let Some(previous) = variables.insert(name.clone(), sort.clone())
                && previous != sort
            {
                return Err(format!(
                    "configuration variable {name} is projected at both {previous} and {sort}"
                ));
            }
        }
    }
    visit_kore_children(pattern, &mut |child| {
        collect_projected_configuration_variables(child, projection_sorts, variables)
    })
}

fn collect_configuration_variable_tokens(pattern: &KorePattern, names: &mut BTreeSet<String>) {
    if let KorePattern::DomainValue { sort, value } = pattern
        && matches!(sort, KoreSort::Application { name, arguments }
            if name == "SortKConfigVar" && arguments.is_empty())
    {
        names.insert(value.clone());
    }
    let _: Result<(), ()> = visit_kore_children(pattern, &mut |child| {
        collect_configuration_variable_tokens(child, names);
        Ok(())
    });
}

fn visit_kore_children<E>(
    pattern: &KorePattern,
    visitor: &mut impl FnMut(&KorePattern) -> Result<(), E>,
) -> Result<(), E> {
    match pattern {
        KorePattern::Application { arguments, .. }
        | KorePattern::AssociativeApplication { arguments, .. }
        | KorePattern::And { arguments, .. }
        | KorePattern::Or { arguments, .. } => {
            for argument in arguments {
                visitor(argument)?;
            }
        }
        KorePattern::Not { argument, .. }
        | KorePattern::Next { argument, .. }
        | KorePattern::Ceil { argument, .. }
        | KorePattern::Floor { argument, .. } => visitor(argument)?,
        KorePattern::Exists { body, .. }
        | KorePattern::Forall { body, .. }
        | KorePattern::Mu { body, .. }
        | KorePattern::Nu { body, .. } => visitor(body)?,
        KorePattern::Implies { left, right, .. }
        | KorePattern::Iff { left, right, .. }
        | KorePattern::Rewrites { left, right, .. }
        | KorePattern::Equals { left, right, .. }
        | KorePattern::In { left, right, .. } => {
            visitor(left)?;
            visitor(right)?;
        }
        KorePattern::String(_)
        | KorePattern::Variable(_)
        | KorePattern::Top { .. }
        | KorePattern::Bottom { .. }
        | KorePattern::DomainValue { .. } => {}
    }
    Ok(())
}

fn validate_configuration_assignments(
    assignments: &[String],
    declared: &BTreeMap<String, KastSort>,
) -> Result<Vec<(String, String, KastSort)>, String> {
    let mut seen = BTreeSet::new();
    let mut validated = Vec::new();
    for assignment in assignments {
        let (name, value) = assignment.split_once('=').ok_or_else(|| {
            format!("invalid configuration assignment {assignment:?}; expected NAME=VALUE")
        })?;
        let name = name.strip_prefix('$').unwrap_or(name);
        if name.is_empty() {
            return Err(format!(
                "invalid configuration assignment {assignment:?}; variable name is empty"
            ));
        }
        if name == "PGM" {
            return Err("configuration variable PGM is supplied by the program argument".into());
        }
        if !seen.insert(name.to_owned()) {
            return Err(format!(
                "configuration variable {name} was supplied more than once"
            ));
        }
        let sort = declared
            .get(name)
            .cloned()
            .ok_or_else(|| format!("configuration variable {name} is not declared"))?;
        validated.push((name.to_owned(), value.to_owned(), sort));
    }
    Ok(validated)
}

struct ConfigurationBinding {
    name: String,
    value: KorePattern,
    sort: KoreSort,
}

fn top_cell_initializer(
    program: KorePattern,
    program_sort: KoreSort,
    additional: Vec<ConfigurationBinding>,
) -> KorePattern {
    let config_var_sort = kore_sort("SortKConfigVar");
    let item_sort = kore_sort("SortKItem");
    let mut entries = vec![ConfigurationBinding {
        name: "PGM".into(),
        value: program,
        sort: program_sort,
    }];
    entries.extend(additional);
    let mut entries = entries.into_iter().map(|binding| {
        let key = kore_application(
            "inj",
            vec![config_var_sort.clone(), item_sort.clone()],
            vec![KorePattern::DomainValue {
                sort: config_var_sort.clone(),
                value: format!("${}", binding.name),
            }],
        );
        let value = if binding.sort == item_sort {
            binding.value
        } else {
            kore_application(
                "inj",
                vec![binding.sort, item_sort.clone()],
                vec![binding.value],
            )
        };
        kore_application("Lbl'UndsPipe'-'-GT-Unds'", Vec::new(), vec![key, value])
    });
    let first = entries.next().expect("$PGM always provides one map entry");
    let config = entries.fold(first, |left, right| {
        kore_application("Lbl'Unds'Map'Unds'", Vec::new(), vec![left, right])
    });
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
    fn discovers_and_validates_declared_configuration_variables() {
        let projection = KoreSymbol {
            name: "Lblproject'Coln'Map".into(),
            sort_parameters: Vec::new(),
        };
        let config_token = KorePattern::DomainValue {
            sort: kore_sort("SortKConfigVar"),
            value: "$ENV".into(),
        };
        let pattern = KorePattern::Application {
            symbol: projection.clone(),
            arguments: vec![kore_application(
                "LblMap'Coln'lookup",
                Vec::new(),
                vec![
                    KorePattern::Variable(KoreVariable {
                        kind: k_rust::kore::ast::VariableKind::Element,
                        name: "VarInit".into(),
                        sort: kore_sort("SortMap"),
                    }),
                    config_token,
                ],
            )],
        };
        let definition = KoreDefinition {
            attributes: KoreAttributes::default(),
            modules: vec![KoreModule {
                name: "MAIN".into(),
                sentences: vec![
                    KoreSentence::SymbolDeclaration {
                        hooked: false,
                        symbol: projection,
                        argument_sorts: vec![kore_sort("SortKItem")],
                        result_sort: kore_sort("SortMap"),
                        attributes: KoreAttributes::default(),
                    },
                    KoreSentence::Axiom {
                        parameters: Vec::new(),
                        pattern: Box::new(pattern),
                        attributes: KoreAttributes::default(),
                    },
                ],
                attributes: KoreAttributes::default(),
            }],
        };
        let declared = declared_configuration_variables(&definition).unwrap();

        assert_eq!(
            declared,
            BTreeMap::from([("ENV".into(), KastSort::new("Map"))])
        );
        assert_eq!(
            validate_configuration_assignments(&["ENV=.Map".into()], &declared).unwrap(),
            [("ENV".into(), ".Map".into(), KastSort::new("Map"))]
        );
        for (assignment, expected) in [
            ("PGM=value", "supplied by the program argument"),
            ("NOSUCH=value", "is not declared"),
        ] {
            let error =
                validate_configuration_assignments(&[assignment.into()], &declared).unwrap_err();
            assert!(error.contains(expected), "{error}");
        }
        let error =
            validate_configuration_assignments(&["ENV=one".into(), "ENV=two".into()], &declared)
                .unwrap_err();
        assert!(error.contains("more than once"), "{error}");
    }

    #[test]
    fn top_initializer_combines_program_and_configuration_bindings() {
        let initial = top_cell_initializer(
            KorePattern::DomainValue {
                sort: kore_sort("SortExp"),
                value: "program".into(),
            },
            kore_sort("SortExp"),
            vec![ConfigurationBinding {
                name: "ENV".into(),
                value: kore_application("Lbl'Dot'Map", Vec::new(), Vec::new()),
                sort: kore_sort("SortMap"),
            }],
        );
        let rendered = KorePrinter::compact().print_pattern(&initial);

        assert!(rendered.contains("Lbl'Unds'Map'Unds'"), "{rendered}");
        assert!(rendered.contains("$PGM"), "{rendered}");
        assert!(rendered.contains("$ENV"), "{rendered}");
        assert!(
            rendered.contains("inj{SortMap{}, SortKItem{}}"),
            "{rendered}"
        );
    }

    fn deeply_nested_kore_pattern(depth: usize) -> KorePattern {
        let sort = KoreSort::Application {
            name: "SortK".into(),
            arguments: Vec::new(),
        };
        (0..depth).fold(KorePattern::Top { sort: sort.clone() }, |argument, _| {
            KorePattern::Not {
                sort: sort.clone(),
                argument: Box::new(argument),
            }
        })
    }

    #[test]
    fn converts_deep_kore_output_to_json_values() {
        assert!(kore_json_value(&deeply_nested_kore_pattern(160)).is_ok());
    }

    #[test]
    fn decodes_deep_backend_kore_json_input() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let syntax = parse_kore_definition(
                    r#"[]
                    module MAIN
                      sort SortK{} []
                      symbol value{}() : SortK{} [constructor{}()]
                      symbol wrap{}(SortK{}) : SortK{} [constructor{}()]
                    endmodule []"#,
                )
                .unwrap();
                let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
                let mut pattern = parse_kore_pattern("value{}()").unwrap();
                for _ in 0..160 {
                    pattern = KorePattern::Application {
                        symbol: KoreSymbol {
                            name: "wrap".into(),
                            sort_parameters: Vec::new(),
                        },
                        arguments: vec![pattern],
                    };
                }
                let source = kore_json::to_string(&pattern).unwrap();

                decode_backend_pattern(
                    &definition,
                    Path::new("state.json"),
                    "initial",
                    source.as_bytes(),
                )
                .unwrap();
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn decodes_text_json_and_binary_backend_patterns() {
        use k_rust::kore::binary::{ConstrainedPattern, encode_pattern};

        let syntax = parse_kore_definition(
            r#"[]
            module MAIN
              sort SortS{} []
              symbol state{}(SortS{}) : SortS{} [constructor{}()]
              symbol value{}() : SortS{} [constructor{}()]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let syntax = parse_kore_pattern("state{}(value{}())").unwrap();
        let expected = definition.internalize_pattern(&syntax, &[]).unwrap();
        let path = Path::new("state.kore");

        let text =
            decode_backend_pattern(&definition, path, "initial", b"state{}(value{}())").unwrap();
        let json = decode_backend_pattern(
            &definition,
            path,
            "initial",
            kore_json::to_string(&syntax).unwrap().as_bytes(),
        )
        .unwrap();
        let binary = decode_backend_pattern(
            &definition,
            path,
            "initial",
            &encode_pattern(&ConstrainedPattern::new(syntax, Vec::new())).unwrap(),
        )
        .unwrap();

        assert_eq!(text, expected);
        assert_eq!(json, expected);
        assert_eq!(binary, expected);
    }

    fn empty_predicate_definition() -> BackendDefinition {
        let syntax = parse_kore_definition(
            r#"[]
            module MAIN
              sort SortK{} []
            endmodule []"#,
        )
        .unwrap();
        BackendDefinition::internalize(&syntax, "MAIN").unwrap()
    }

    fn simplify_predicate(source: &str) -> KorePattern {
        let syntax = parse_kore_pattern(source).unwrap();
        simplify_kore_pattern(&empty_predicate_definition(), &syntax).unwrap()
    }

    #[test]
    fn standalone_simplification_deduplicates_conjunctions() {
        assert_eq!(
            simplify_predicate(
                r"\and{SortK{}}(\not{SortK{}}(X:SortK{}), \not{SortK{}}(X:SortK{}))"
            ),
            parse_kore_pattern(r"\not{SortK{}}(X:SortK{})").unwrap()
        );
    }

    #[test]
    fn standalone_simplification_detects_contradictions() {
        assert_eq!(
            simplify_predicate(r"\and{SortK{}}(\not{SortK{}}(X:SortK{}), X:SortK{})"),
            parse_kore_pattern(r"\bottom{SortK{}}()").unwrap()
        );
    }

    #[test]
    fn standalone_simplification_eliminates_double_negation() {
        assert_eq!(
            simplify_predicate(r"\not{SortK{}}(\not{SortK{}}(X:SortK{}))"),
            parse_kore_pattern("X:SortK{}").unwrap()
        );
    }

    #[test]
    fn decodes_text_json_and_binary_simplification_patterns() {
        let syntax = parse_kore_pattern(r"\not{SortK{}}(X:SortK{})").unwrap();
        let path = Path::new("predicate.kore");

        let text =
            decode_kore_syntax(path, "simplification", br"\not{SortK{}}(X:SortK{})").unwrap();
        let json = decode_kore_syntax(
            path,
            "simplification",
            kore_json::to_string(&syntax).unwrap().as_bytes(),
        )
        .unwrap();
        let binary = decode_kore_syntax(
            path,
            "simplification",
            &kore_binary::encode_term(&syntax).unwrap(),
        )
        .unwrap();

        assert_eq!(text, syntax);
        assert_eq!(json, syntax);
        assert_eq!(binary, syntax);
    }

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
    fn parses_an_optional_kast_backend() {
        let cli = Cli::try_parse_from([
            "krust",
            "kast",
            "definition.k",
            "--module",
            "MAIN",
            "--sort",
            "Exp",
            "--backend",
            "llvm",
            "--expression",
            "value",
        ])
        .unwrap();
        let Command::Kast(options) = cli.command else {
            panic!("expected kast command");
        };
        let options = KastOptions::from(options);

        assert_eq!(options.backend, Some(CompilationBackend::Llvm));
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
            "-cENV=.Map",
            "--config-var",
            "ARGS=.List",
            "--depth",
            "42",
            "--breadth",
            "7",
            "--execute-to-branch",
            "--cut-point-rule",
            "MAIN.loop",
            "--terminal-rule",
            "rule-id",
            "--strategy",
            "any",
            "--step-timeout",
            "250",
            "--moving-average-step-timeout",
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
        assert_eq!(options.config_vars, ["ENV=.Map", "ARGS=.List"]);
        assert_eq!(options.depth, 42);
        assert_eq!(options.breadth_limit, Some(7));
        assert!(options.execute_to_branch);
        assert_eq!(
            options.cut_point_rules,
            BTreeSet::from(["MAIN.loop".into()])
        );
        assert_eq!(options.terminal_rules, BTreeSet::from(["rule-id".into()]));
        assert_eq!(options.strategy, ExecutionMode::Any);
        assert!(options.search.is_none());
        assert_eq!(options.step_timeout, Some(Duration::from_millis(250)));
        assert!(options.moving_average_timeout);
        assert_eq!(options.smt, Z3Options::default());
    }

    #[test]
    fn parses_krun_search_options() {
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
            "--search-all",
            "--search-pattern",
            "target.kore",
            "--search-bound",
            "3",
        ])
        .unwrap();
        let Command::Krun(options) = cli.command else {
            panic!("expected krun command");
        };
        let options = KrunOptions::from(options);
        let search = options.search.expect("search options should be present");

        assert_eq!(search.search_type, SearchType::Star);
        assert_eq!(search.pattern.as_deref(), Some(Path::new("target.kore")));
        assert_eq!(search.bound, Some(3));
    }

    #[test]
    fn parses_kore_exec_options() {
        let cli = Cli::try_parse_from([
            "krust",
            "kore-exec",
            "definition.kore",
            "--module",
            "MAIN",
            "--add-module",
            "rules-one.kore",
            "--add-module",
            "rules-two.kore",
            "--pattern",
            "program.kore",
            "--depth",
            "42",
            "--output",
            "result.kore",
            "--cut-point-rule",
            "MAIN.loop",
            "--terminal-rule",
            "rule-id",
            "--search-final",
            "--search-pattern",
            "target.kore",
            "--step-timeout",
            "500",
            "--moving-average-step-timeout",
        ])
        .unwrap();
        let Command::KoreExec(options) = cli.command else {
            panic!("expected kore-exec command");
        };

        assert_eq!(options.definition, Path::new("definition.kore"));
        assert_eq!(options.module, "MAIN");
        assert_eq!(
            options.added_modules,
            [
                PathBuf::from("rules-one.kore"),
                PathBuf::from("rules-two.kore")
            ]
        );
        assert_eq!(options.pattern, Path::new("program.kore"));
        assert_eq!(options.depth, Some(42));
        assert_eq!(options.output.as_deref(), Some(Path::new("result.kore")));
        assert_eq!(options.cut_point_rules, ["MAIN.loop"]);
        assert_eq!(options.terminal_rules, ["rule-id"]);
        assert_eq!(options.timeout.timeout(), Some(Duration::from_millis(500)));
        assert!(options.timeout.moving_average);
        let search = options
            .search
            .into_options()
            .expect("search options should be present");
        assert_eq!(search.search_type, SearchType::Final);
        assert_eq!(search.pattern.as_deref(), Some(Path::new("target.kore")));
    }

    #[test]
    fn parses_kore_simplify_options() {
        let cli = Cli::try_parse_from([
            "krust",
            "kore-simplify",
            "definition.kore",
            "--module",
            "MAIN",
            "--pattern",
            "predicate.json",
            "--output",
            "result.kore",
        ])
        .unwrap();
        let Command::KoreSimplify(options) = cli.command else {
            panic!("expected kore-simplify command");
        };

        assert_eq!(options.definition, Path::new("definition.kore"));
        assert_eq!(options.module, "MAIN");
        assert_eq!(options.pattern, Path::new("predicate.json"));
        assert_eq!(options.output.as_deref(), Some(Path::new("result.kore")));
    }

    #[test]
    fn kore_simplify_preserves_boolean_terms() {
        let syntax = parse_kore_definition(
            r#"[]
            module MAIN
              hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let boolean = parse_kore_pattern(r#"\dv{SortBool{}}("true")"#).unwrap();

        assert_eq!(
            simplify_kore_pattern(&definition, &boolean).unwrap(),
            boolean
        );
    }

    #[test]
    fn parses_kore_get_model_options() {
        let cli = Cli::try_parse_from([
            "krust",
            "kore-get-model",
            "definition.kore",
            "--module",
            "MAIN",
            "--pattern",
            "state.json",
            "--output",
            "model.json",
        ])
        .unwrap();
        let Command::KoreGetModel(options) = cli.command else {
            panic!("expected kore-get-model command");
        };

        assert_eq!(options.definition, Path::new("definition.kore"));
        assert_eq!(options.module, "MAIN");
        assert_eq!(options.pattern, Path::new("state.json"));
        assert_eq!(options.output.as_deref(), Some(Path::new("model.json")));
    }

    #[test]
    fn parses_kore_implies_options() {
        let cli = Cli::try_parse_from([
            "krust",
            "kore-implies",
            "definition.kore",
            "--module",
            "MAIN",
            "--antecedent",
            "left.json",
            "--consequent",
            "right.json",
            "--output",
            "result.json",
        ])
        .unwrap();
        let Command::KoreImplies(options) = cli.command else {
            panic!("expected kore-implies command");
        };

        assert_eq!(options.definition, Path::new("definition.kore"));
        assert_eq!(options.module, "MAIN");
        assert_eq!(options.antecedent, Path::new("left.json"));
        assert_eq!(options.consequent, Path::new("right.json"));
        assert_eq!(options.output.as_deref(), Some(Path::new("result.json")));
    }

    #[test]
    fn parses_kore_rpc_options() {
        let cli = Cli::try_parse_from([
            "krust",
            "kore-rpc",
            "definition.kore",
            "--module",
            "MAIN",
            "--server-port",
            "31337",
            "--host",
            "0.0.0.0",
            "--smt-timeout",
            "1",
            "--smt-retry-limit",
            "5",
        ])
        .unwrap();
        let Command::KoreRpc(options) = cli.command else {
            panic!("expected kore-rpc command");
        };

        assert_eq!(options.definition, Path::new("definition.kore"));
        assert_eq!(options.module, "MAIN");
        assert_eq!(options.port, 31_337);
        assert_eq!(options.host, "0.0.0.0");
        assert_eq!(
            options.smt.options(),
            Z3Options {
                timeout_ms: 1,
                retry_limit: 5,
            }
        );
    }

    #[test]
    fn model_output_distinguishes_sat_unsat_and_unknown() {
        let variable = Variable::new("X", BackendSort::simple("SortInt"));
        let substitution = Substitution::from([(
            variable,
            Term::domain_value(BackendSort::simple("SortInt"), "42"),
        )]);

        let sat = model_output(
            ModelResult::Sat(substitution),
            Some(&BackendSort::simple("SortBool")),
        )
        .unwrap();
        let unsat = model_output(ModelResult::Unsat, None).unwrap();
        let unknown = model_output(ModelResult::Unknown("timeout".into()), None).unwrap();

        let sat: serde_json::Value = serde_json::from_str(&sat).unwrap();
        assert_eq!(sat["satisfiable"], "Sat");
        assert_eq!(sat["substitution"]["format"], "KORE");
        assert_eq!(
            serde_json::from_str::<serde_json::Value>(&unsat).unwrap()["satisfiable"],
            "Unsat"
        );
        assert_eq!(
            serde_json::from_str::<serde_json::Value>(&unknown).unwrap()["satisfiable"],
            "Unknown"
        );
    }

    #[test]
    fn model_substitution_flattens_multiple_bindings() {
        let value_sort = BackendSort::simple("SortInt");
        let result_sort = BackendSort::simple("SortBool");
        let substitution = Substitution::from([
            (
                Variable::new("X", value_sort.clone()),
                Term::domain_value(value_sort.clone(), "1"),
            ),
            (
                Variable::new("Y", value_sort.clone()),
                Term::domain_value(value_sort.clone(), "2"),
            ),
            (
                Variable::new("Z", value_sort.clone()),
                Term::domain_value(value_sort, "3"),
            ),
        ]);

        let KorePattern::And { arguments, .. } =
            model_substitution(&substitution, &result_sort).unwrap()
        else {
            panic!("multiple model bindings should form a conjunction");
        };
        assert_eq!(arguments.len(), 3);
        assert!(
            arguments
                .iter()
                .all(|argument| matches!(argument, KorePattern::Equals { .. }))
        );
    }

    #[test]
    fn generated_variable_names_use_natural_numeric_order() {
        assert_eq!(
            compare_natural_names("RuleVar_Gen2", "RuleVar_Gen10"),
            std::cmp::Ordering::Less
        );
        assert_eq!(
            compare_natural_names("RuleVar_Gen02", "RuleVar_Gen2"),
            std::cmp::Ordering::Greater
        );
        assert_eq!(
            compare_natural_names("RuleVar_A", "RuleVar_B"),
            std::cmp::Ordering::Less
        );
    }

    #[test]
    fn execution_depth_is_unlimited_by_default() {
        let krun = Cli::try_parse_from([
            "krust",
            "krun",
            "definition.k",
            "--main-module",
            "MAIN",
            "--sort",
            "Exp",
            "--expression",
            "0",
        ])
        .unwrap();
        let Command::Krun(krun) = krun.command else {
            panic!("expected krun command");
        };
        assert_eq!(KrunOptions::from(krun).depth, u64::MAX);

        let kore_exec = Cli::try_parse_from([
            "krust",
            "kore-exec",
            "definition.kore",
            "--module",
            "MAIN",
            "--pattern",
            "program.kore",
        ])
        .unwrap();
        let Command::KoreExec(kore_exec) = kore_exec.command else {
            panic!("expected kore-exec command");
        };
        assert_eq!(kore_exec.depth, None);
    }

    #[test]
    fn parses_kore_match_disjunction_options() {
        let cli = Cli::try_parse_from([
            "krust",
            "kore-match-disjunction",
            "definition.kore",
            "--module",
            "MAIN",
            "--disjunction",
            "states.kore",
            "--match",
            "target.kore",
            "--output",
            "result.kore",
        ])
        .unwrap();
        let Command::KoreMatchDisjunction(options) = cli.command else {
            panic!("expected kore-match-disjunction command");
        };

        assert_eq!(options.definition, Path::new("definition.kore"));
        assert_eq!(options.module, "MAIN");
        assert_eq!(options.disjunction, Path::new("states.kore"));
        assert_eq!(options.pattern, Path::new("target.kore"));
        assert_eq!(options.output.as_deref(), Some(Path::new("result.kore")));
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
        assert_eq!(options.smt, Z3Options::default());
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
