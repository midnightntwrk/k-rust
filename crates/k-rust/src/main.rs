//! The `krust` command line: option parsing, file and stream I/O, printing, timings, and process status. Every backend operation goes through `k_rust::backend::Backend`; the kompile pipeline belongs to `k_rust::kompile`.
//!
//! ```toml algorithm-site
//! id = "kompile.kore.declarations"
//! role = "part"
//! sites = ["kcompile"]
//! produces = [{ type = "k_rust::PreparedDefinitionManifest", role = "prepared definition manifest" }]
//! ```
//!
//! ```toml algorithm-site
//! id = "definition.outer.requires"
//! role = "variant"
//! sites = ["load_definition_against_prepared", "load_prepared_manifest"]
//! consumes = [{ type = "k_rust::PreparedDefinitionManifest", role = "prepared definition manifest" }]
//! constrains = [{ id = "kompile.kore.declarations", site = "load_definition_against_prepared", via = "the SyntaxModule attribute and PreparedDefinitionManifest module digests cross the process boundary in parsed.json and krust.json" }]
//! ```
//!
//! ```toml algorithm-contract
//! id = "contract.counters.krust_writer_order"
//! name = "stable KRUST_COUNTERS key order"
//! sites = ["write_counters_if_requested"]
//! constrains = [{ id = "Counter::ALL", site = "write_counters_if_requested", via = "Snapshot::iter preserves Counter::ALL declaration order for the hand-written JSON object" }]
//! ```

use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    error::Error,
    fmt, fs,
    io::{self, IsTerminal, Read, Write},
    num::{NonZeroU32, NonZeroUsize},
    path::{Path, PathBuf},
    process::ExitCode,
    time::{Duration, Instant},
};

use clap::{ArgGroup, Args, Parser, Subcommand, ValueEnum};
use k_rust::backend::search::*;
use k_rust::names::BuiltinSort;
use k_rust::{
    backend::{
        Backend, BackendError, BackendOptions,
        execution::{BackendRunOptions, SearchRunOptions},
        proving::{ClaimFilter, SavedProofs, filter_claims},
        simplification::model_substitution,
    },
    definition::{
        AttributeKey, Attributes, CheckMode, checks::check_definition, json as definition_json,
    },
    diagnostic::{Diagnostic, DiagnosticPolicy, Severity, WarningLevel},
    inner::{ProgramParser, definition_with_named_projections, parse_program_for_presentation},
    kast::{
        Sort as KastSort, WellKnownModule, json as kast_json, parser::parse_sort,
        printer::Printer as KastPrinter,
    },
    kompile::{
        CompilationBackend, CompileOptions, CompileSearchPatternError, CompiledSearchPattern,
        MacroExpansionDefinition, SortInjector, compile_loaded_definition,
        compile_loaded_definition_timed, compile_search_pattern, encode_kore_sort,
        initial_configuration::{
            missing_variables, parser_modules, stream_defaults, top_cell_initializer,
        },
        pipeline::{emission_phase, load_phase},
        term_to_kore_from_resolved_with_token_module,
    },
    kore::{
        ast::{Definition as KoreDefinition, Pattern as KorePattern},
        codec as kore_codec, json as kore_json,
        parser::{
            parse_definition as parse_kore_definition, parse_module as parse_kore_module,
            parse_pattern as parse_kore_pattern,
        },
        printer::Printer as KorePrinter,
    },
    native::{
        FileResolver, load_runnable_artifact, unpublish_runnable_artifact, write_runnable_artifact,
    },
    outer::{
        LoadOptions, PreparedModuleDeclaration, SourceResolver, SyntaxModule,
        load_for_compilation_timed, load_with_options_timed, load_with_prepared_base_timed,
        prepared_module_declarations, resolve_syntax_module,
    },
    timings::{PhaseTiming, PhaseTimings, TIMINGS_SCHEMA_VERSION},
};
use k_rust_backend::{
    externalize,
    proof::{ProofLeafOutcome, ProofOptions, ProofSearchOrder, ProofStatus},
    rewrite::{ExecutionMode, Pattern},
    search::SearchType,
    simplify::DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
    smt::{ModelResult, Z3Options},
    term::Sort as BackendSort,
    transition::DescriptorTranscriptEntry,
};
use serde::{Deserialize, Serialize};
use tracing_subscriber::prelude::*;

mod rpc;
mod trace_aggregate;

struct TraceRecorder {
    default: Option<tracing::dispatcher::DefaultGuard>,
    flush: Option<tracing_chrome::FlushGuard>,
    aggregate: Option<trace_aggregate::AggregateOutput>,
}

impl Drop for TraceRecorder {
    fn drop(&mut self) {
        // Stop routing new spans to the writer before asking it to finish the JSON document.
        drop(self.default.take());
        drop(self.flush.take());
        if let Some(aggregate) = self.aggregate.take()
            && let Err(error) = aggregate.write()
        {
            eprintln!("warning: trace aggregate not written: {error}");
        }
    }
}

/// How `--trace` spans are aggregated; `algo-graph join` applies this rule to either output.
const TRACE_AGGREGATION_RULE: &str = "per algorithm id: invocation count, total and self duration; counter deltas summed across invocations";

fn start_trace(
    path: Option<&Path>,
    aggregate: Option<&Path>,
) -> Result<Option<TraceRecorder>, Box<dyn Error>> {
    if path.is_none() && aggregate.is_none() {
        return Ok(None);
    }
    let (chrome, flush) = match path {
        Some(path) => {
            let writer = fs::File::create(path).map_err(|error| {
                io::Error::new(
                    error.kind(),
                    format!("could not create trace file `{}`: {error}", path.display()),
                )
            })?;
            let (layer, flush) = tracing_chrome::ChromeLayerBuilder::new()
                .writer(writer)
                .include_args(true)
                .build();
            (Some(layer), Some(flush))
        }
        None => (None, None),
    };
    let (aggregate_layer, aggregate) = match aggregate {
        Some(path) => {
            let (layer, output) = trace_aggregate::layer(path, TRACE_AGGREGATION_RULE)?;
            (Some(layer), Some(output))
        }
        None => (None, None),
    };
    let subscriber = tracing_subscriber::registry()
        .with(chrome)
        .with(aggregate_layer);
    let default = tracing::subscriber::set_default(subscriber);
    tracing::info!(
        target: "algo_graph",
        aggregation_rule = tracing::field::display(TRACE_AGGREGATION_RULE),
        "trace_metadata"
    );
    Ok(Some(TraceRecorder {
        default: Some(default),
        flush,
        aggregate,
    }))
}

fn main() -> ExitCode {
    let outcome = run(Cli::parse());
    #[cfg(feature = "measure")]
    write_counters_if_requested();
    match outcome {
        Ok(exit_code) => exit_code,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(1)
        }
    }
}

/// Write the main thread's `k_rust_kore::measure` counters to the file named by
/// `KRUST_COUNTERS`, on success and on failure alike. Only `measure` builds read the variable;
/// a write failure is reported on stderr and never changes the exit code. The document is
/// written by hand so the keys keep `Counter::ALL` order, which `serde_json` maps do not.
#[cfg(feature = "measure")]
fn write_counters_if_requested() {
    let Some(path) = env::var_os("KRUST_COUNTERS") else {
        return;
    };
    let mut text = format!(
        "{{\n  \"format\": \"krust-counters\",\n  \"version\": {},\n  \"counters\": {{\n",
        k_rust_kore::measure::COUNTER_SCHEMA_VERSION
    );
    let snapshot = k_rust_kore::measure::snapshot();
    let mut counters = snapshot.iter().peekable();
    while let Some((name, value)) = counters.next() {
        let separator = if counters.peek().is_some() { "," } else { "" };
        text.push_str(&format!("    \"{name}\": {value}{separator}\n"));
    }
    text.push_str("  }\n}\n");
    if let Err(error) = fs::write(&path, text) {
        eprintln!(
            "warning: could not write counters to {}: {error}",
            path.to_string_lossy()
        );
    }
}

fn run(cli: Cli) -> Result<ExitCode, Box<dyn Error>> {
    match cli.command {
        Command::Kcompile(options) => kcompile(options.into()).map(|()| ExitCode::SUCCESS),
        Command::Kast(options) => kast(options.into()).map(|()| ExitCode::SUCCESS),
        Command::Krun(options) => krun(options.into()),
        Command::KoreExec(options) => kore_exec(options),
        Command::KoreSimplify(options) => kore_simplify(options).map(|()| ExitCode::SUCCESS),
        Command::KoreGetModel(options) => kore_get_model(options).map(|()| ExitCode::SUCCESS),
        Command::KoreImplies(options) => kore_implies(options).map(|()| ExitCode::SUCCESS),
        Command::KoreRpc(options) => kore_rpc(options).map(|()| ExitCode::SUCCESS),
        Command::KoreMatchDisjunction(options) => {
            kore_match_disjunction_command(options).map(|()| ExitCode::SUCCESS)
        }
        Command::Kprove(options) => kprove(options.into()).map(|()| ExitCode::SUCCESS),
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

#[derive(Clone, Copy, Debug, Args)]
struct WarningArgs {
    /// Warning level: all, normal, or none.
    #[arg(
        short = 'w',
        long = "warnings",
        value_enum,
        default_value_t,
        value_name = "LEVEL"
    )]
    warnings: WarningLevelArg,

    /// Treat every reported warning as an error.
    #[arg(long = "warnings-to-errors")]
    warnings_to_errors: bool,
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

    /// Module whose grammar parses programs (defaults to MAIN-MODULE-SYNTAX when present).
    #[arg(long, value_name = "MODULE")]
    syntax_module: Option<String>,

    /// Generate an executable deterministic Bison parser for the $PGM configuration variable.
    #[arg(long)]
    gen_bison_parser: bool,

    /// Generate an executable GLR Bison parser for the $PGM configuration variable.
    #[arg(long)]
    gen_glr_bison_parser: bool,

    /// Maximum size of the generated Bison parser stack.
    #[arg(long, default_value_t = 10_000, value_name = "SIZE")]
    bison_stack_max_depth: u64,

    /// Make generated Bison list grammars left associative to bound parser stack use.
    #[arg(long)]
    bison_lists: bool,

    /// Generate the requested Bison parser as a shared library instead of an executable.
    #[arg(long)]
    bison_parser_library: bool,

    /// Plugin hook namespaces (for example `KRYPTO`) emitted as hooked symbols. K's form is one
    /// whitespace-separated list; commas and repeated flags are accepted too. Defaults to the
    /// namespaces the Rust backend implements, or to none for other backends.
    #[arg(
        long,
        value_name = "NAMESPACES",
        action = clap::ArgAction::Append
    )]
    hook_namespaces: Option<Vec<String>>,

    /// Directory in which generated KORE files are written.
    #[arg(short = 'o', long, default_value = ".", value_name = "DIR")]
    output_directory: PathBuf,

    /// Also write the parsed outer definition as KAST JSON v4.
    #[arg(long)]
    emit_json: bool,

    /// Emit bare claims as all-path reachability claims consumable by `kprove`.
    #[arg(long)]
    for_proving: bool,

    /// Semantics module whose configuration parses proof claims (defaults to MAIN-MODULE).
    #[arg(long, requires = "for_proving", value_name = "MODULE")]
    definition_module: Option<String>,

    /// Compile this specification against a prepared semantics directory.
    #[arg(long, requires = "for_proving", value_name = "PATH")]
    compiled_definition: Option<PathBuf>,

    /// Write phase timings in seconds as JSON (excludes process startup and teardown).
    #[arg(long, value_name = "FILE")]
    timings: Option<PathBuf>,

    /// Write algorithm and phase spans as Chrome trace-event JSON.
    #[arg(long, value_name = "FILE")]
    trace: Option<PathBuf>,

    /// Write only the per-algorithm and per-phase aggregate of the spans `--trace` would write,
    /// as JSON that `algo-graph join --trace` reads in place of the trace.
    #[arg(long, value_name = "FILE")]
    trace_aggregate: Option<PathBuf>,

    #[command(flatten)]
    warnings: WarningArgs,

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

    /// Backend whose module view parses the program (the same default as `kcompile`, so the
    /// grammar always matches the compiled artifact).
    #[arg(long, value_enum, default_value_t)]
    backend: CompilationBackendArg,

    /// Start sort for the program parser.
    #[arg(
        short = 's',
        long,
        value_name = "SORT",
        required_unless_present_any = ["batch_case", "batch_reject_case"],
        conflicts_with_all = ["batch_case", "batch_reject_case"]
    )]
    sort: Option<String>,

    /// Parse one named case in a shared frontend session; may be repeated.
    #[arg(
        long,
        num_args = 3,
        value_names = ["NAME", "SORT", "PROGRAM"],
        action = clap::ArgAction::Append,
        allow_hyphen_values = true,
        conflicts_with_all = ["expression", "program_file"]
    )]
    batch_case: Vec<String>,

    /// Require one named case to be rejected in the shared frontend session; may be repeated.
    #[arg(
        long,
        num_args = 3,
        value_names = ["NAME", "SORT", "PROGRAM"],
        action = clap::ArgAction::Append,
        allow_hyphen_values = true,
        conflicts_with_all = ["expression", "program_file"]
    )]
    batch_reject_case: Vec<String>,

    /// Parse this program text instead of reading a file or standard input.
    #[arg(
        short = 'e',
        long,
        conflicts_with = "program_file",
        allow_hyphen_values = true,
        value_name = "PROGRAM"
    )]
    expression: Option<String>,

    /// Generate a standalone deterministic Bison parser at PROGRAM_FILE.
    #[arg(
        long,
        conflicts_with_all = ["gen_glr_parser", "expression", "batch_case", "batch_reject_case", "output"]
    )]
    gen_parser: bool,

    /// Generate a standalone GLR Bison parser at PROGRAM_FILE.
    #[arg(
        long,
        conflicts_with_all = ["gen_parser", "expression", "batch_case", "batch_reject_case", "output"]
    )]
    gen_glr_parser: bool,

    /// Maximum size of the generated Bison parser stack.
    #[arg(long, default_value_t = 10_000, value_name = "SIZE")]
    bison_stack_max_depth: u64,

    /// Program file to parse, or `-` for standard input.
    #[arg(
        value_name = "PROGRAM_FILE",
        conflicts_with_all = ["batch_case", "batch_reject_case"]
    )]
    program_file: Option<PathBuf>,

    /// KAST output format.
    #[arg(short = 'o', long, value_enum, default_value_t)]
    output: OutputFormat,

    #[command(flatten)]
    warnings: WarningArgs,

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
    /// Runnable directory produced by `krust kcompile`.
    #[arg(long = "definition", value_name = "DIR")]
    compiled_definition: Option<PathBuf>,

    /// Main module of the definition.
    #[arg(short = 'm', long = "main-module", value_name = "MODULE")]
    module: Option<String>,

    /// Module whose grammar should parse the program (defaults to the main module).
    #[arg(long, value_name = "MODULE")]
    syntax_module: Option<String>,

    /// Start sort for the program parser.
    #[arg(short = 's', long, value_name = "SORT")]
    sort: String,

    /// Execute this program text instead of reading a file or standard input.
    #[arg(short = 'e', long, allow_hyphen_values = true, value_name = "PROGRAM")]
    expression: Option<String>,

    /// Source definition followed by an optional program file. With `--definition`, this is only
    /// the optional program file.
    #[arg(value_names = ["SOURCE_DEFINITION", "PROGRAM_FILE"], num_args = 0..=2)]
    inputs: Vec<PathBuf>,

    /// Set a configuration variable (for example `-c ENV=.Map`). May be repeated.
    #[arg(short = 'c', long = "config-var", value_name = "NAME=VALUE")]
    config_vars: Vec<String>,

    /// Match results against this K surface rule-content pattern.
    #[arg(
        long = "pattern",
        value_name = "K_TEXT",
        conflicts_with = "search_pattern",
        allow_hyphen_values = true
    )]
    surface_pattern: Option<String>,

    /// Enable real input/output for stream cells. `off` buffers standard input to end of file
    /// into `$STDIN`, with its trailing newlines replaced by exactly one, as K's krun does.
    /// Defaults to `on` for execution and `off` for search.
    #[arg(long, value_enum, value_name = "on|off")]
    io: Option<IoArg>,

    /// Select KORE result rendering (`kore`, the default), emit the one terminal buffered stdout
    /// stream (`captured`), or suppress result rendering (`none`). Captured output uses `--io off`
    /// semantics. Live `--io on` console output requires `none` when it writes stdout.
    #[arg(long, value_enum, default_value_t = KrunOutputArg::Kore)]
    output: KrunOutputArg,

    /// Maximum number of semantic rewrite steps per execution branch.
    #[arg(long, value_name = "STEPS")]
    depth: Option<u64>,

    /// Maximum simplifier iterations per rewrite step.
    #[arg(long, value_name = "ITERATIONS")]
    max_simplification_iterations: Option<usize>,

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

    /// Follow the first applicable rule by priority and order (`any`, the default: the single
    /// successor K's krun takes) or explore every applicable rule (`all`, kore-exec's default).
    #[arg(long, value_enum, default_value_t = ExecutionStrategyArg::Any)]
    strategy: ExecutionStrategyArg,

    #[command(flatten)]
    search: SearchArgs,

    #[command(flatten)]
    timeout: ExecutionTimeoutArgs,

    #[command(flatten)]
    smt: SmtArgs,

    /// Write phase timings in seconds as JSON (excludes process startup and teardown).
    #[arg(long, value_name = "FILE")]
    timings: Option<PathBuf>,

    /// Write algorithm and phase spans as Chrome trace-event JSON.
    #[arg(long, value_name = "FILE")]
    trace: Option<PathBuf>,

    /// Write only the per-algorithm and per-phase aggregate of the spans `--trace` would write,
    /// as JSON that `algo-graph join --trace` reads in place of the trace.
    #[arg(long, value_name = "FILE")]
    trace_aggregate: Option<PathBuf>,

    #[command(flatten)]
    warnings: WarningArgs,

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

    /// Maximum simplifier iterations per rewrite step.
    #[arg(long, value_name = "ITERATIONS")]
    max_simplification_iterations: Option<usize>,

    /// Write the resulting KORE pattern to this file instead of standard output.
    #[arg(short, long, value_name = "OUTPUT_KORE")]
    output: Option<PathBuf>,

    /// Write the depth-bounded execution leaves as a KORE disjunction for differential tests.
    #[arg(long, value_name = "OUTPUT_KORE")]
    stop_leaves: Option<PathBuf>,

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
#[command(group(
    ArgGroup::new("kprove_input")
        .args(["definition", "compiled_definition"])
        .required(true)
        .multiple(true)
))]
struct KproveArgs {
    /// K definition or specification containing the claims to prove.
    #[arg(value_name = "DEFINITION")]
    definition: Option<PathBuf>,

    /// Proof-ready KORE file or `kcompile --for-proving` output directory.
    #[arg(long, value_name = "PATH")]
    compiled_definition: Option<PathBuf>,

    /// Main specification module.
    #[arg(short = 'm', long = "main-module", value_name = "MODULE")]
    module: String,

    /// Semantics module that owns the configuration; defaults to the specification module.
    #[arg(long, visible_alias = "def-module", value_name = "MODULE")]
    definition_module: Option<String>,

    /// Load and validate the prepared definition without running any claims.
    #[arg(long, requires = "compiled_definition", conflicts_with = "definition")]
    load_only: bool,

    /// Write phase timings in seconds as JSON (excludes process startup and teardown).
    #[arg(long, value_name = "FILE")]
    timings: Option<PathBuf>,

    /// Write algorithm and phase spans as Chrome trace-event JSON.
    #[arg(long, value_name = "FILE")]
    trace: Option<PathBuf>,

    /// Write only the per-algorithm and per-phase aggregate of the spans `--trace` would write,
    /// as JSON that `algo-graph join --trace` reads in place of the trace.
    #[arg(long, value_name = "FILE")]
    trace_aggregate: Option<PathBuf>,

    /// Prove only claims with one of these labels. May be repeated.
    #[arg(long = "claim", value_name = "LABEL")]
    claims: Vec<String>,

    /// Exclude claims with these labels from obligations and circularities. May be repeated.
    #[arg(long = "exclude", value_name = "LABEL")]
    excluded_claims: Vec<String>,

    /// Keep claims with these labels only as trusted circularities. May be repeated.
    #[arg(long = "trusted", value_name = "LABEL")]
    trusted_claims: Vec<String>,

    /// Maximum number of rewrite or circularity steps per proof branch.
    #[arg(long, value_name = "STEPS")]
    depth: Option<u64>,

    /// Maximum simplifier iterations per proof step.
    #[arg(long, value_name = "ITERATIONS")]
    max_simplification_iterations: Option<usize>,

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
    warnings: WarningArgs,

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
    diagnostics: DiagnosticPolicy,
}

impl CommonOptions {
    fn configured_builtin_directory(&self) -> Option<PathBuf> {
        self.builtin_directory
            .clone()
            .or_else(|| env::var_os("KRUST_BUILTIN_DIRECTORY").map(PathBuf::from))
    }

    fn builtin_source_prefixes(&self) -> Vec<String> {
        let mut prefixes = vec!["krust-builtin://".into()];
        if let Some(directory) = self.configured_builtin_directory()
            && let Ok(canonical) = fs::canonicalize(directory)
        {
            let mut prefix = canonical.to_string_lossy().into_owned();
            if !prefix.ends_with(std::path::MAIN_SEPARATOR) {
                prefix.push(std::path::MAIN_SEPARATOR);
            }
            prefixes.push(prefix);
        }
        prefixes
    }
}

#[derive(Debug)]
struct KcompileOptions {
    common: CommonOptions,
    backend: CompilationBackend,
    hook_namespaces: Option<Vec<String>>,
    syntax_module: Option<String>,
    gen_bison_parser: bool,
    gen_glr_bison_parser: bool,
    bison_stack_max_depth: u64,
    bison_lists: bool,
    bison_parser_library: bool,
    output_directory: PathBuf,
    emit_json: bool,
    for_proving: bool,
    definition_module: Option<String>,
    compiled_definition: Option<PathBuf>,
    timings: Option<PathBuf>,
    trace: Option<PathBuf>,
    trace_aggregate: Option<PathBuf>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
enum CompilationBackendArg {
    #[default]
    #[value(alias = "haskell")]
    Rust,
    Llvm,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
enum WarningLevelArg {
    All,
    #[default]
    Normal,
    None,
}

impl From<WarningLevelArg> for WarningLevel {
    fn from(level: WarningLevelArg) -> Self {
        match level {
            WarningLevelArg::All => Self::All,
            WarningLevelArg::Normal => Self::Normal,
            WarningLevelArg::None => Self::None,
        }
    }
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

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
enum IoArg {
    On,
    Off,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
enum KrunOutputArg {
    #[default]
    Kore,
    Captured,
    None,
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
    backend: CompilationBackend,
    sort: Option<String>,
    batch_cases: Vec<KastBatchCase>,
    batch_reject_cases: Vec<KastBatchCase>,
    expression: Option<String>,
    program_file: Option<PathBuf>,
    output: OutputFormat,
    gen_parser: bool,
    gen_glr_parser: bool,
    bison_stack_max_depth: u64,
}

#[derive(Debug)]
struct KastBatchCase {
    name: String,
    sort: String,
    expression: String,
}

#[derive(Debug)]
struct KrunOptions {
    source: Option<CommonOptions>,
    compiled_definition: Option<PathBuf>,
    requested_main_module: Option<String>,
    syntax_module: Option<String>,
    sort: String,
    expression: Option<String>,
    program_file: Option<PathBuf>,
    extra_input: Option<PathBuf>,
    config_vars: Vec<String>,
    surface_pattern: Option<String>,
    io: Option<bool>,
    output: KrunOutputArg,
    depth: u64,
    max_simplification_iterations: usize,
    breadth_limit: Option<usize>,
    execute_to_branch: bool,
    cut_point_rules: BTreeSet<String>,
    terminal_rules: BTreeSet<String>,
    strategy: ExecutionMode,
    search: Option<SearchRunOptions>,
    step_timeout: Option<Duration>,
    moving_average_timeout: bool,
    smt: Z3Options,
    timings: Option<PathBuf>,
    trace: Option<PathBuf>,
    trace_aggregate: Option<PathBuf>,
}

struct KrunCompiledInput {
    main_module: String,
    syntax_module: String,
    frontend_definition: k_rust::definition::Definition,
    execution_definition: k_rust::definition::Definition,
    configuration_variables: BTreeMap<String, KastSort>,
    execution_rewrite_order: Vec<String>,
    definition_kore: String,
    timings: CompileTimings,
}

#[derive(Debug)]
enum MatchTargetSource {
    KoreFile(PathBuf),
    Surface(CompiledSearchPattern),
}

#[derive(Debug)]
struct KproveOptions {
    input: KproveInput,
    module: String,
    definition_module: String,
    claims: Vec<String>,
    excluded_claims: Vec<String>,
    trusted_claims: Vec<String>,
    depth: u64,
    max_simplification_iterations: usize,
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
    load_only: bool,
    timings: Option<PathBuf>,
    trace: Option<PathBuf>,
    trace_aggregate: Option<PathBuf>,
}

#[derive(Serialize)]
struct ProofTimings {
    version: u32,
    input_seconds: f64,
    internalize_seconds: f64,
    proof_setup_seconds: f64,
    proof_seconds: f64,
    claims: Vec<ClaimTiming>,
}

impl Default for ProofTimings {
    fn default() -> Self {
        Self {
            version: TIMINGS_SCHEMA_VERSION,
            input_seconds: 0.0,
            internalize_seconds: 0.0,
            proof_setup_seconds: 0.0,
            proof_seconds: 0.0,
            claims: Vec::new(),
        }
    }
}

#[derive(Serialize)]
struct ClaimTiming {
    label: String,
    seconds: f64,
    status: String,
}

impl ProofTimings {
    fn write(&self, path: Option<&Path>) -> Result<(), Box<dyn Error>> {
        if let Some(path) = path {
            fs::write(path, serde_json::to_string_pretty(self)?)?;
        }
        Ok(())
    }
}

/// `kcompile --timings` output: every load, compile, and artifact-write phase in execution order,
/// with the three group totals.
#[derive(Serialize)]
struct CompileTimings {
    version: u32,
    load_seconds: f64,
    compile_seconds: f64,
    write_seconds: f64,
    load_wall_seconds: f64,
    compile_wall_seconds: f64,
    write_wall_seconds: f64,
    load_unattributed_seconds: f64,
    compile_unattributed_seconds: f64,
    write_unattributed_seconds: f64,
    total_wall_seconds: f64,
    phases: Vec<PhaseTiming>,
}

impl CompileTimings {
    fn new(load: PhaseTimings, compile: PhaseTimings, write: PhaseTimings) -> Self {
        let load_seconds = load.total_seconds();
        let compile_seconds = compile.total_seconds();
        let write_seconds = write.total_seconds();
        let load_wall_seconds = load.measured_span_seconds();
        let compile_wall_seconds = compile.measured_span_seconds();
        let write_wall_seconds = write.measured_span_seconds();
        let load_unattributed_seconds = (load_wall_seconds - load_seconds).max(0.0);
        let compile_unattributed_seconds = (compile_wall_seconds - compile_seconds).max(0.0);
        let write_unattributed_seconds = (write_wall_seconds - write_seconds).max(0.0);
        let total_wall_seconds = load_wall_seconds + compile_wall_seconds + write_wall_seconds;
        let mut phases = load;
        phases.extend(compile);
        phases.extend(write);
        Self {
            version: TIMINGS_SCHEMA_VERSION,
            load_seconds,
            compile_seconds,
            write_seconds,
            load_wall_seconds,
            compile_wall_seconds,
            write_wall_seconds,
            load_unattributed_seconds,
            compile_unattributed_seconds,
            write_unattributed_seconds,
            total_wall_seconds,
            phases: phases.phases,
        }
    }

    fn write(&self, path: Option<&Path>) -> Result<(), Box<dyn Error>> {
        if let Some(path) = path {
            fs::write(path, serde_json::to_string_pretty(self)?)?;
        }
        Ok(())
    }
}

/// `krun --timings` output: the in-process compilation, then each execution phase.
#[derive(Serialize)]
struct KrunTimings {
    compile: CompileTimings,
    program_parse_seconds: f64,
    config_vars_parse_seconds: f64,
    internalize_seconds: f64,
    execute_seconds: f64,
    output_seconds: f64,
}

impl KrunTimings {
    fn write(&self, path: Option<&Path>) -> Result<(), Box<dyn Error>> {
        if let Some(path) = path {
            fs::write(path, serde_json::to_string_pretty(self)?)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
enum KproveInput {
    Source(CommonOptions),
    Compiled(PathBuf),
    SourceWithCompiled {
        source: CommonOptions,
        compiled: PathBuf,
    },
}

const PREPARED_MANIFEST: &str = "krust.json";
const PREPARED_FORMAT: &str = "krust-prepared-definition";

#[derive(Debug, Deserialize, Serialize)]
struct PreparedDefinitionManifest {
    format: String,
    version: u32,
    sources: Vec<String>,
    #[serde(default)]
    modules: Vec<PreparedModuleDeclaration>,
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
    fn common(
        self,
        definition: PathBuf,
        module: String,
        diagnostics: DiagnosticPolicy,
    ) -> CommonOptions {
        CommonOptions {
            definition,
            module,
            includes: self.includes,
            markdown_selector: self.markdown_selector,
            builtin_directory: self.builtin_directory,
            no_prelude: self.no_prelude,
            diagnostics,
        }
    }
}

impl WarningArgs {
    fn policy(self) -> DiagnosticPolicy {
        DiagnosticPolicy {
            level: self.warnings.into(),
            warnings_to_errors: self.warnings_to_errors,
        }
    }
}

impl SearchArgs {
    fn into_options(self) -> Option<SearchRunOptions> {
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
        search_type.map(|search_type| SearchRunOptions {
            search_type,
            pattern: self.search_pattern,
            bound: self.search_bound,
        })
    }
}

impl From<KcompileArgs> for KcompileOptions {
    fn from(arguments: KcompileArgs) -> Self {
        Self {
            common: arguments.source.common(
                arguments.definition,
                arguments.module,
                arguments.warnings.policy(),
            ),
            backend: arguments.backend.into(),
            hook_namespaces: arguments
                .hook_namespaces
                .map(|values| split_hook_namespaces(&values)),
            syntax_module: arguments.syntax_module,
            gen_bison_parser: arguments.gen_bison_parser,
            gen_glr_bison_parser: arguments.gen_glr_bison_parser,
            bison_stack_max_depth: arguments.bison_stack_max_depth,
            bison_lists: arguments.bison_lists,
            bison_parser_library: arguments.bison_parser_library,
            output_directory: arguments.output_directory,
            emit_json: arguments.emit_json,
            for_proving: arguments.for_proving,
            definition_module: arguments.definition_module,
            compiled_definition: arguments.compiled_definition,
            timings: arguments.timings,
            trace: arguments.trace,
            trace_aggregate: arguments.trace_aggregate,
        }
    }
}

/// K's `StringListConverter` semantics plus comma separators retained for krust compatibility.
fn split_hook_namespaces(values: &[String]) -> Vec<String> {
    let mut namespaces = Vec::new();
    for value in values {
        let mut namespace = String::new();
        let mut characters = value.chars().peekable();
        while let Some(character) = characters.next() {
            match character {
                '\\' if characters.peek().is_some_and(|next| next.is_whitespace()) => {
                    namespace.push(characters.next().expect("peeked character must exist"));
                }
                character if character.is_whitespace() || character == ',' => {
                    if !namespace.is_empty() {
                        namespaces.push(std::mem::take(&mut namespace));
                    }
                }
                character => namespace.push(character),
            }
        }
        if !namespace.is_empty() {
            namespaces.push(namespace);
        }
    }
    namespaces
}

impl From<KastArgs> for KastOptions {
    fn from(arguments: KastArgs) -> Self {
        let collect_cases = |values: Vec<String>| {
            values
                .as_chunks::<3>()
                .0
                .iter()
                .map(|case| KastBatchCase {
                    name: case[0].clone(),
                    sort: case[1].clone(),
                    expression: case[2].clone(),
                })
                .collect()
        };
        let batch_cases = collect_cases(arguments.batch_case);
        let batch_reject_cases = collect_cases(arguments.batch_reject_case);
        Self {
            common: arguments.source.common(
                arguments.definition,
                arguments.module,
                arguments.warnings.policy(),
            ),
            backend: arguments.backend.into(),
            sort: arguments.sort,
            batch_cases,
            batch_reject_cases,
            expression: arguments.expression,
            program_file: arguments.program_file,
            output: arguments.output,
            gen_parser: arguments.gen_parser,
            gen_glr_parser: arguments.gen_glr_parser,
            bison_stack_max_depth: arguments.bison_stack_max_depth,
        }
    }
}

impl From<KrunArgs> for KrunOptions {
    fn from(arguments: KrunArgs) -> Self {
        let mut inputs = arguments.inputs.into_iter();
        let definition = arguments
            .compiled_definition
            .is_none()
            .then(|| inputs.next())
            .flatten();
        let program_file = inputs.next();
        let extra_input = inputs.next();
        let source = definition.map(|definition| {
            arguments.source.common(
                definition,
                arguments.module.clone().unwrap_or_default(),
                arguments.warnings.policy(),
            )
        });
        Self {
            source,
            compiled_definition: arguments.compiled_definition,
            requested_main_module: arguments.module,
            syntax_module: arguments.syntax_module,
            sort: arguments.sort,
            expression: arguments.expression,
            program_file,
            extra_input,
            config_vars: arguments.config_vars,
            surface_pattern: arguments.surface_pattern,
            io: arguments.io.map(|io| io == IoArg::On),
            output: arguments.output,
            depth: arguments.depth.unwrap_or(u64::MAX),
            max_simplification_iterations: arguments
                .max_simplification_iterations
                .unwrap_or(DEFAULT_MAX_SIMPLIFICATION_ITERATIONS),
            breadth_limit: arguments.breadth_limit,
            execute_to_branch: arguments.execute_to_branch,
            cut_point_rules: arguments.cut_point_rules.into_iter().collect(),
            terminal_rules: arguments.terminal_rules.into_iter().collect(),
            strategy: arguments.strategy.into(),
            search: arguments.search.into_options(),
            step_timeout: arguments.timeout.timeout(),
            moving_average_timeout: arguments.timeout.moving_average,
            smt: arguments.smt.options(),
            timings: arguments.timings,
            trace: arguments.trace,
            trace_aggregate: arguments.trace_aggregate,
        }
    }
}

fn select_match_target_source(
    search: Option<&SearchRunOptions>,
    surface: Option<CompiledSearchPattern>,
) -> Option<MatchTargetSource> {
    if let Some(surface) = surface {
        return Some(MatchTargetSource::Surface(surface));
    }
    search.and_then(|search| {
        search
            .pattern
            .as_ref()
            .map(|path| MatchTargetSource::KoreFile(path.clone()))
    })
}

fn command_line_pattern_attributes(contents: &str) -> Attributes {
    let mut end_line = 1_u32;
    let mut end_column = 1_u32;
    for character in contents.chars() {
        if character == '\n' {
            end_line += 1;
            end_column = 1;
        } else {
            end_column += 1;
        }
    }
    let mut attributes = Attributes::default();
    attributes.set(AttributeKey::Source, serde_json::json!("<command line>"));
    attributes.set(AttributeKey::SourceId, serde_json::json!(0));
    attributes.set(
        AttributeKey::Location,
        serde_json::json!([1, 1, end_line, end_column]),
    );
    attributes.set(AttributeKey::ContentStartOffset, serde_json::json!(0));
    attributes.set(AttributeKey::ContentStartLine, serde_json::json!(1));
    attributes.set(AttributeKey::ContentStartColumn, serde_json::json!(1));
    attributes
}

impl From<KproveArgs> for KproveOptions {
    fn from(arguments: KproveArgs) -> Self {
        let module = arguments.module;
        let definition_module = arguments
            .definition_module
            .clone()
            .unwrap_or_else(|| module.clone());
        let input = match (arguments.definition, arguments.compiled_definition) {
            (Some(definition), Some(compiled)) => KproveInput::SourceWithCompiled {
                source: arguments.source.common(
                    definition,
                    module.clone(),
                    arguments.warnings.policy(),
                ),
                compiled,
            },
            (Some(definition), None) => KproveInput::Source(arguments.source.common(
                definition,
                module.clone(),
                arguments.warnings.policy(),
            )),
            (None, Some(compiled)) => KproveInput::Compiled(compiled),
            (None, None) => unreachable!("clap requires an input"),
        };
        Self {
            input,
            module,
            definition_module,
            claims: arguments.claims,
            excluded_claims: arguments.excluded_claims,
            trusted_claims: arguments.trusted_claims,
            depth: arguments.depth.unwrap_or(u64::MAX),
            max_simplification_iterations: arguments
                .max_simplification_iterations
                .unwrap_or(DEFAULT_MAX_SIMPLIFICATION_ITERATIONS),
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
            load_only: arguments.load_only,
            timings: arguments.timings,
            trace: arguments.trace,
            trace_aggregate: arguments.trace_aggregate,
        }
    }
}

fn load_definition(
    options: &CommonOptions,
    backend: Option<CompilationBackend>,
    configuration_module: Option<&str>,
) -> Result<k_rust::outer::LoadedDefinition, Box<dyn Error>> {
    load_definition_impl(options, backend, configuration_module, None, false)
        .map(|(loaded, _, _)| loaded)
}

/// Load a definition from the command line, recording entry-source resolution and every loader
/// phase in the returned timings.
fn load_definition_impl(
    options: &CommonOptions,
    backend: Option<CompilationBackend>,
    configuration_module: Option<&str>,
    compilation_syntax: Option<Option<&str>>,
    bison_lists: bool,
) -> Result<
    (
        k_rust::outer::LoadedDefinition,
        Option<String>,
        PhaseTimings,
    ),
    Box<dyn Error>,
> {
    let span_started = Instant::now();
    let mut timings = PhaseTimings::default();
    let (mut resolver, entry, load_options) =
        timings.time(load_phase::RESOLVE_ENTRY_SOURCE, || {
            let builtin_directory = options.configured_builtin_directory();
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
            let load_options = LoadOptions {
                markdown_selector: options.markdown_selector.clone(),
                implicit_sources,
                excluded_module_attributes: backend
                    .map(|backend| vec![backend.excluded_module_attribute().into()])
                    .unwrap_or_default(),
                configuration_module: configuration_module.map(str::to_owned),
                project_root: None,
                diagnostics: options.diagnostics,
                bison_lists,
            };
            Ok::<_, Box<dyn Error>>((resolver, entry, load_options))
        })?;
    if let Some(syntax) = compilation_syntax {
        let (loaded, syntax, loader_timings) = load_for_compilation_timed(
            entry,
            &options.module,
            syntax,
            &mut resolver,
            &load_options,
        )
        .inspect_err(|error| {
            if let k_rust::outer::LoadError::SourceDiagnostics(diagnostics) = error {
                emit_diagnostics(diagnostics);
            }
        })?;
        timings.extend(loader_timings);
        timings.set_span_seconds(span_started.elapsed().as_secs_f64());
        Ok((loaded, Some(syntax), timings))
    } else {
        let (loaded, loader_timings) =
            load_with_options_timed(entry, &options.module, &mut resolver, &load_options)?;
        timings.extend(loader_timings);
        timings.set_span_seconds(span_started.elapsed().as_secs_f64());
        Ok((loaded, None, timings))
    }
}

fn kcompile(options: KcompileOptions) -> Result<(), Box<dyn Error>> {
    let _trace = start_trace(options.trace.as_deref(), options.trace_aggregate.as_deref())?;
    if options.for_proving && options.backend != CompilationBackend::Rust {
        return Err("--for-proving requires --backend rust".into());
    }
    if options.bison_parser_library && !options.gen_bison_parser && !options.gen_glr_bison_parser {
        return Err(
            "--bison-parser-library requires --gen-bison-parser or --gen-glr-bison-parser".into(),
        );
    }
    let configuration_module = options.for_proving.then(|| {
        options
            .definition_module
            .as_deref()
            .unwrap_or(&options.common.module)
    });
    let (mut loaded, syntax_module, load_timings) =
        if let Some(prepared) = &options.compiled_definition {
            let (loaded, load_timings) = load_definition_against_prepared(
                &options.common,
                configuration_module.expect("--compiled-definition requires --for-proving"),
                prepared,
                options.bison_lists,
            )?;
            let syntax = resolve_syntax_module(&loaded.resolved, options.syntax_module.as_deref())?;
            (loaded, syntax, load_timings)
        } else {
            let (loaded, syntax, load_timings) = load_definition_impl(
                &options.common,
                Some(options.backend),
                configuration_module,
                Some(options.syntax_module.as_deref()),
                options.bison_lists,
            )?;
            (
                loaded,
                SyntaxModule {
                    name: syntax.expect("fresh compilation selects syntax"),
                    fallback_warning: None,
                },
                load_timings,
            )
        };
    let builtin_source_prefixes = options.common.builtin_source_prefixes();
    if let Some(warning) = syntax_module.fallback_warning {
        loaded
            .diagnostics
            .extend(options.common.diagnostics.apply(vec![warning]));
    }
    let (artifacts, compile_timings) = match compile_loaded_definition_timed(
        &loaded,
        CompileOptions {
            backend: options.backend,
            hook_namespaces: options.hook_namespaces,
            default_claims_to_all_path: options.for_proving,
            check_mode: configuration_module.map_or(CheckMode::Definition, |module| {
                CheckMode::Proof {
                    definition_module: module.to_owned(),
                }
            }),
            diagnostics: options.common.diagnostics,
            builtin_source_prefixes,
            ..CompileOptions::default()
        },
    ) {
        Ok(compiled) => compiled,
        Err(error) => {
            emit_diagnostics(&error.diagnostics);
            return Err(error.into());
        }
    };
    emit_diagnostics(&artifacts.diagnostics);
    fs::create_dir_all(&options.output_directory)?;
    // A directory is runnable only after its new Rust manifest is published. Removing an older
    // marker first prevents both interrupted recompilation and LLVM output written over a prior
    // Rust directory from appearing runnable.
    unpublish_runnable_artifact(&options.output_directory)?;
    let write_span_started = Instant::now();
    let mut write_timings = PhaseTimings::default();
    let bison_mode = if options.gen_glr_bison_parser {
        Some(k_rust::bison::Mode::Glr)
    } else if options.gen_bison_parser {
        Some(k_rust::bison::Mode::Lr)
    } else {
        None
    };
    if let Some(mode) = bison_mode
        && let Some(start_sort) = artifacts.configuration_variables.get("PGM")
    {
        write_timings.time(emission_phase::GENERATE_BISON_PARSER, || {
            k_rust::bison::generate_program_parser(
                &loaded.resolved,
                &syntax_module.name,
                start_sort,
                &options.output_directory,
                k_rust::bison::Options {
                    mode,
                    stack_max_depth: options.bison_stack_max_depth,
                    artifact: if options.bison_parser_library {
                        k_rust::bison::Artifact::SharedLibrary
                    } else {
                        k_rust::bison::Artifact::Executable
                    },
                },
            )
        })?;
    }
    write_timings.time(emission_phase::WRITE_ARTIFACTS, || {
        if options.emit_json || options.for_proving {
            let definition = if options.compiled_definition.is_some() {
                parsed_definition_for_json(&loaded, &syntax_module.name)?
            } else {
                // Fresh compilation already selected its modules before parsing. Keep that exact
                // graph, including any distinct configuration root, in the parsed artifact.
                let mut definition = loaded.definition.clone();
                definition.attributes.set(
                    AttributeKey::SyntaxModule,
                    serde_json::Value::String(syntax_module.name.clone()),
                );
                definition
            };
            fs::write(
                options.output_directory.join("parsed.json"),
                definition_json::to_string_pretty(&definition)?,
            )?;
        }
        if options.for_proving {
            let (mut sources, mut modules) = if let Some(prepared) = &options.compiled_definition {
                let manifest = load_prepared_manifest(prepared)?;
                (manifest.sources, manifest.modules)
            } else {
                (Vec::new(), Vec::new())
            };
            sources.extend(loaded.files.iter().map(|file| file.source.clone()));
            sources.sort();
            sources.dedup();
            modules.extend(prepared_module_declarations(
                &loaded.files,
                &loaded.definition,
            ));
            modules.sort();
            modules.dedup();
            let manifest = PreparedDefinitionManifest {
                format: PREPARED_FORMAT.into(),
                version: 1,
                sources,
                modules,
            };
            fs::write(
                options.output_directory.join(PREPARED_MANIFEST),
                serde_json::to_string_pretty(&manifest)?,
            )?;
        }
        fs::write(
            options.output_directory.join("definition.kore"),
            &artifacts.definition_kore,
        )?;
        fs::write(
            options.output_directory.join("syntaxDefinition.kore"),
            &artifacts.syntax_definition_kore,
        )?;
        fs::write(
            options.output_directory.join("macros.kore"),
            &artifacts.macros_kore,
        )?;
        // Proof preparation has its own parsed-definition contract and can combine source tables
        // from a prepared semantics and a new specification. It is not an executable definition
        // compilation, so publish the krun payload only for ordinary Rust definitions.
        if options.backend == CompilationBackend::Rust && !options.for_proving {
            write_runnable_artifact(
                &options.output_directory,
                &options.common.module,
                &syntax_module.name,
                &loaded.definition,
                &loaded.source_table,
                &artifacts.execution_definition,
                &artifacts.configuration_variables,
                &artifacts.execution_rewrite_order,
                &artifacts.definition_kore,
            )?;
        }
        Ok::<_, Box<dyn Error>>(())
    })?;
    write_timings.set_span_seconds(write_span_started.elapsed().as_secs_f64());
    CompileTimings::new(load_timings, compile_timings, write_timings)
        .write(options.timings.as_deref())?;
    Ok(())
}

fn parsed_definition_for_json(
    loaded: &k_rust::outer::LoadedDefinition,
    syntax_module: &str,
) -> Result<k_rust::definition::Definition, Box<dyn Error>> {
    // Match DefinitionParsing.parseDefinitionAndResolveBubbles: retain the semantic and syntax
    // import closures, the frontend's always-present utility modules, and entry modules whose
    // visible sentences contained no bubbles before backend-tag filtering.
    let main = loaded.resolved.main_module();

    let mut seeds = BTreeSet::from([
        main.name.clone(),
        syntax_module.to_owned(),
        WellKnownModule::KReflection.as_str().into(),
        WellKnownModule::StdinStream.as_str().into(),
        WellKnownModule::StdoutStream.as_str().into(),
        WellKnownModule::Map.as_str().into(),
    ]);
    let source_modules = loaded
        .files
        .iter()
        .flat_map(|file| &file.modules)
        .collect::<Vec<_>>();
    let mut modules_with_visible_bubbles = source_modules
        .iter()
        .filter(|module| {
            module
                .sentences
                .iter()
                .any(|sentence| matches!(sentence, k_rust::outer::Sentence::Bubble(_)))
        })
        .map(|module| module.name.as_str())
        .map(str::to_owned)
        .collect::<BTreeSet<_>>();
    loop {
        let before = modules_with_visible_bubbles.len();
        for module in &source_modules {
            if module
                .imports
                .iter()
                .any(|import| modules_with_visible_bubbles.contains(&import.module))
            {
                modules_with_visible_bubbles.insert(module.name.clone());
            }
        }
        if modules_with_visible_bubbles.len() == before {
            break;
        }
    }
    for module in source_modules {
        if !modules_with_visible_bubbles.contains(&module.name) {
            seeds.insert(module.name.clone());
        }
    }

    let mut retained = BTreeSet::new();
    for seed in seeds {
        let Some(module) = loaded.resolved.module_id(&seed) else {
            continue;
        };
        retained.insert(loaded.resolved.module(module).name.clone());
        retained.extend(
            loaded
                .resolved
                .transitive_imports(module)
                .into_iter()
                .map(|import| loaded.resolved.module(import).name.clone()),
        );
    }
    let mut definition = loaded.definition.clone();
    definition
        .modules
        .retain(|module| retained.contains(&module.name));
    definition.attributes.set(
        AttributeKey::SyntaxModule,
        serde_json::Value::String(syntax_module.into()),
    );
    Ok(definition)
}

fn kast(options: KastOptions) -> Result<(), Box<dyn Error>> {
    let loaded = load_definition(&options.common, Some(options.backend), None)?;
    let mut diagnostics = loaded.diagnostics.clone();
    diagnostics.extend(
        options
            .common
            .diagnostics
            .apply(check_definition(&loaded.resolved)?),
    );
    emit_diagnostics(&diagnostics);
    if diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        return Err("definition checks failed".into());
    }
    let bison_mode = if options.gen_glr_parser {
        Some(k_rust::bison::Mode::Glr)
    } else if options.gen_parser {
        Some(k_rust::bison::Mode::Lr)
    } else {
        None
    };
    if let Some(mode) = bison_mode {
        let output = options
            .program_file
            .as_deref()
            .ok_or("--gen-parser and --gen-glr-parser require an output path")?;
        let sort = parse_sort(options.sort.as_deref().expect("clap requires --sort"))?;
        return k_rust::bison::generate_parser(
            &loaded.resolved,
            &options.common.module,
            &sort,
            output,
            k_rust::bison::Options {
                mode,
                stack_max_depth: options.bison_stack_max_depth,
                artifact: k_rust::bison::Artifact::Executable,
            },
        )
        .map_err(Into::into);
    }
    let parser = ProgramParser::from_resolved(&loaded.resolved, &options.common.module)?;
    if !options.batch_cases.is_empty() || !options.batch_reject_cases.is_empty() {
        if options.output != OutputFormat::Json {
            return Err("KAST batch mode requires --output json".into());
        }
        let mut output = serde_json::Map::new();
        for case in options.batch_cases {
            let sort = parse_sort(&case.sort)
                .map_err(|error| format!("KAST batch case {:?}: {error}", case.name))?;
            let term = parse_program_for_presentation(
                &loaded.resolved,
                &options.common.module,
                &parser,
                &sort,
                &case.expression,
            )
            .map_err(|error| format!("KAST batch case {:?}: {error}", case.name))?;
            let encoded: serde_json::Value =
                serde_json::from_str(&kast_json::to_string_pretty(&term)?)?;
            if output.insert(case.name.clone(), encoded).is_some() {
                return Err(format!("duplicate KAST batch case name {:?}", case.name).into());
            }
        }
        for case in options.batch_reject_cases {
            let sort = parse_sort(&case.sort)
                .map_err(|error| format!("KAST rejection batch case {:?}: {error}", case.name))?;
            if parser.parse(&sort, &case.expression).is_ok() {
                return Err(format!(
                    "KAST rejection batch case {:?} was unexpectedly accepted",
                    case.name
                )
                .into());
            }
        }
        println!("{}", serde_json::to_string_pretty(&output)?);
        return Ok(());
    }
    let source = read_program_source(options.expression, options.program_file)?;
    let sort = parse_sort(options.sort.as_deref().expect("clap requires --sort"))?;
    let term = parse_program_for_presentation(
        &loaded.resolved,
        &options.common.module,
        &parser,
        &sort,
        &source,
    )?;
    match options.output {
        OutputFormat::Text => println!("{}", KastPrinter::new().print_term(&term)),
        OutputFormat::Json => println!("{}", kast_json::to_string_pretty(&term)?),
    }
    Ok(())
}

fn krun(options: KrunOptions) -> Result<ExitCode, Box<dyn Error>> {
    let _trace = start_trace(options.trace.as_deref(), options.trace_aggregate.as_deref())?;
    if options.source.is_none() && options.compiled_definition.is_none() {
        return Err("a source definition or --definition DIR is required".into());
    }
    if let Some(extra) = &options.extra_input {
        return Err(format!(
            "unexpected positional argument `{}` with --definition; pass only the program file",
            extra.display()
        )
        .into());
    }
    if options.expression.is_some() && options.program_file.is_some() {
        return Err("--expression cannot be used with a program file".into());
    }
    let io = match options.output {
        KrunOutputArg::Captured => false,
        KrunOutputArg::Kore | KrunOutputArg::None => options.io.unwrap_or(options.search.is_none()),
    };
    if options.search.is_some() && options.io == Some(true) {
        return Err("--io on is supported only for ordinary execution, not search".into());
    }
    if options.output == KrunOutputArg::Captured {
        if options.io == Some(true) {
            return Err(
                "--output captured uses buffered stream semantics and cannot be combined with --io on"
                    .into(),
            );
        }
        if options.search.is_some() {
            return Err(
                "--output captured is supported only for ordinary execution, not search".into(),
            );
        }
        if options.surface_pattern.is_some() {
            return Err("--output captured cannot be combined with --pattern".into());
        }
        if options.config_vars.iter().any(|assignment| {
            assignment
                .split_once('=')
                .is_some_and(|(name, _)| name.strip_prefix('$').unwrap_or(name) == "IO")
        }) {
            return Err(
                "--output captured owns the buffered $IO setting and cannot be combined with -c IO=VALUE"
                    .into(),
            );
        }
    }
    if io && options.strategy != ExecutionMode::Any {
        return Err(
            "--io on requires --strategy any; console output from alternatives is not combined"
                .into(),
        );
    }
    let compiled = if let Some(directory) = &options.compiled_definition {
        let started = Instant::now();
        let artifact = load_runnable_artifact(directory)?;
        if let Some(requested) = &options.requested_main_module
            && requested != &artifact.main_module
        {
            return Err(format!(
                "runnable artifact main module is `{}`, not requested `{requested}`",
                artifact.main_module
            )
            .into());
        }
        if let Some(requested) = &options.syntax_module
            && requested != &artifact.syntax_module
        {
            return Err(format!(
                "runnable artifact syntax module is `{}`, not requested `{requested}`",
                artifact.syntax_module
            )
            .into());
        }
        let mut load_timings = PhaseTimings::default();
        load_timings.phases.push(PhaseTiming {
            name: "read runnable artifact",
            seconds: started.elapsed().as_secs_f64(),
            depth: 0,
        });
        KrunCompiledInput {
            main_module: artifact.main_module,
            syntax_module: artifact.syntax_module,
            frontend_definition: artifact.frontend_definition,
            execution_definition: artifact.execution_definition,
            configuration_variables: artifact.configuration_variables,
            execution_rewrite_order: artifact.execution_rewrite_order,
            definition_kore: artifact.definition_kore,
            timings: CompileTimings::new(
                load_timings,
                PhaseTimings::default(),
                PhaseTimings::default(),
            ),
        }
    } else {
        let common = options
            .source
            .as_ref()
            .expect("clap requires a source or compiled definition");
        if common.module.is_empty() {
            return Err("--main-module is required with a source definition".into());
        }
        let (mut loaded, _, load_timings) =
            load_definition_impl(common, Some(CompilationBackend::Rust), None, None, false)?;
        let syntax_module =
            resolve_syntax_module(&loaded.resolved, options.syntax_module.as_deref())?;
        if let Some(warning) = syntax_module.fallback_warning {
            loaded
                .diagnostics
                .extend(common.diagnostics.apply(vec![warning]));
        }
        let builtin_source_prefixes = common.builtin_source_prefixes();
        let (artifacts, compile_timings) = match compile_loaded_definition_timed(
            &loaded,
            CompileOptions {
                backend: CompilationBackend::Rust,
                diagnostics: common.diagnostics,
                builtin_source_prefixes,
                ..CompileOptions::default()
            },
        ) {
            Ok(compiled) => compiled,
            Err(error) => {
                emit_diagnostics(&error.diagnostics);
                return Err(error.into());
            }
        };
        emit_diagnostics(&artifacts.diagnostics);
        KrunCompiledInput {
            main_module: common.module.clone(),
            syntax_module: syntax_module.name,
            frontend_definition: loaded.definition,
            execution_definition: artifacts.execution_definition,
            configuration_variables: artifacts.configuration_variables,
            execution_rewrite_order: artifacts.execution_rewrite_order,
            definition_kore: artifacts.definition_kore,
            timings: CompileTimings::new(load_timings, compile_timings, PhaseTimings::default()),
        }
    };

    let program_parse_phase =
        tracing::info_span!("phase", name = tracing::field::display("program_parse")).entered();
    let started = Instant::now();
    let available_config_vars = &compiled.configuration_variables;
    // K's krun (krun:484-489, :506-521) reads a program only when one is passed; a
    // definition without `$PGM` runs from the configuration variables alone and never
    // touches standard input.
    let program_supplied = options.expression.is_some() || options.program_file.is_some();
    let program_uses_stdin = options.expression.is_none()
        && options
            .program_file
            .as_deref()
            .is_none_or(|path| path == Path::new("-"));
    // Programs are parsed with the reference's program grammar, which declares the named-field
    // projections of every production (RuleGrammarGenerator.getCombinedGrammar); the source
    // definition gains the same productions so that a projection a program applies has a
    // production for sort injection and KORE conversion.
    let program_definition = definition_with_named_projections(&compiled.frontend_definition);
    let program_resolved = k_rust::definition::ResolvedDefinition::resolve(&program_definition)?;
    let compiled_surface_pattern = if let Some(contents) = options.surface_pattern.as_deref() {
        let execution_resolved =
            k_rust::definition::ResolvedDefinition::resolve(&compiled.execution_definition)?;
        let attributes = command_line_pattern_attributes(contents);
        match compile_search_pattern(
            &program_resolved,
            &execution_resolved,
            &compiled.main_module,
            contents,
            attributes,
        ) {
            Ok(pattern) => Some(pattern),
            Err(error) => {
                if let CompileSearchPatternError::CellConcretization(cell_error) = &error {
                    emit_diagnostics(&cell_error.diagnostics);
                }
                return Err(error.into());
            }
        }
    } else {
        None
    };
    let match_target_source =
        select_match_target_source(options.search.as_ref(), compiled_surface_pattern);
    // The macro expander's definition depends on the program definition alone: it is prepared
    // at the first expansion and reused for the program and every configuration value.
    let mut macro_definition = None;
    let program = if program_supplied || available_config_vars.contains_key("PGM") {
        let source = read_program_source(options.expression, options.program_file)?;
        let start_sort = parse_sort(&options.sort)?;
        let program_parser =
            ProgramParser::from_resolved(&program_resolved, &compiled.syntax_module)?;
        let program = program_parser.parse(&start_sort, &source)?;
        let program = prepared_macro_definition(&mut macro_definition, &program_definition)?
            .expand_term(&compiled.main_module, program)?;
        // Expansion rebases applications into the executable catalog. Tokens remain
        // self-describing, and conversion retains lexical hooks from the parser module.
        let program_injector = SortInjector::new(&program_resolved, &compiled.main_module)?;
        let program_sort = program_injector.term_sort(&program, None)?;
        let program = program_injector.inject_at_top(&program)?;
        let program = term_to_kore_from_resolved_with_token_module(
            &program_resolved,
            &compiled.main_module,
            &compiled.syntax_module,
            &program,
        )?;
        Some((program, encode_kore_sort(&program_sort)))
    } else {
        None
    };
    let program_parse_seconds = started.elapsed().as_secs_f64();
    drop(program_parse_phase);
    let config_vars_parse_phase =
        tracing::info_span!("phase", name = tracing::field::display("config_vars_parse")).entered();
    let started = Instant::now();
    let program_uses_stdin = program_uses_stdin && program.is_some();
    let config_parser_modules = parser_modules(&program_resolved, &compiled.main_module)?;
    let mut config_parsers = BTreeMap::new();
    let config_injector = (!options.config_vars.is_empty())
        .then(|| SortInjector::new(&program_resolved, &compiled.main_module))
        .transpose()?;
    let mut seen_config_vars = BTreeSet::new();
    let mut config_vars = Vec::new();
    // Invariant: seen names are exactly the bindings already assigned; parser and injector maps share their key set.
    for assignment in &options.config_vars {
        let (name, source) = assignment.split_once('=').ok_or_else(|| {
            format!("invalid configuration variable `{assignment}`; expected NAME=VALUE")
        })?;
        let name = name.strip_prefix('$').unwrap_or(name);
        if name.is_empty() {
            return Err("configuration variable name cannot be empty".into());
        }
        if name == "PGM" {
            return Err(
                "$PGM is supplied by the program argument and cannot be set with -c".into(),
            );
        }
        if !seen_config_vars.insert(name.to_owned()) {
            return Err(
                format!("configuration variable `${name}` was provided more than once").into(),
            );
        }
        let sort = available_config_vars.get(name).ok_or_else(|| {
            let available = available_config_vars
                .keys()
                .filter(|candidate| candidate.as_str() != "PGM")
                .map(|candidate| format!("${candidate}"))
                .collect::<Vec<_>>()
                .join(", ");
            if available.is_empty() {
                format!("definition has no configuration variable `${name}`")
            } else {
                format!(
                    "definition has no configuration variable `${name}`; available variables: {available}"
                )
            }
        })?;
        let parser_module = match config_parser_modules.get(name) {
            Some(parser_module) => parser_module.as_str(),
            None if matches!(name, "IO" | "STDIN") && sort.is_builtin(BuiltinSort::String) => {
                "STRING-SYNTAX"
            }
            None => &compiled.main_module,
        };
        if program_resolved.module_id(parser_module).is_none() {
            return Err(format!(
                "parser module `{parser_module}` for configuration variable `${name}` was not found"
            )
            .into());
        }
        if !config_parsers.contains_key(parser_module) {
            config_parsers.insert(
                parser_module.to_owned(),
                ProgramParser::from_resolved(&program_resolved, parser_module)?,
            );
        }
        let parser = config_parsers
            .get(parser_module)
            .expect("configuration parser was inserted above");
        let parse_sort = if sort.name == BuiltinSort::K.k_name() {
            KastSort::builtin(BuiltinSort::KItem)
        } else {
            sort.clone()
        };
        let value = parser.parse(&parse_sort, source).map_err(|error| {
            format!("could not parse configuration variable `${name}` at sort {sort}: {error}")
        })?;
        let value = prepared_macro_definition(&mut macro_definition, &program_definition)?
            .expand_term(&compiled.main_module, value)?;
        let injector = config_injector
            .as_ref()
            .expect("a configuration assignment creates the main-module injector");
        let value_sort = injector.term_sort(&value, None)?;
        let value = injector.inject_at_top(&value)?;
        let value = term_to_kore_from_resolved_with_token_module(
            &program_resolved,
            &compiled.main_module,
            parser_module,
            &value,
        )?;
        config_vars.push((format!("${name}"), value, encode_kore_sort(&value_sort)));
    }
    config_vars.extend(stream_defaults(
        available_config_vars,
        &mut seen_config_vars,
        io,
        program_uses_stdin,
        || {
            if std::io::stdin().is_terminal() {
                eprintln!(
                    "note: reading standard input into $STDIN until end of file (--io off); \
                     redirect from /dev/null or end the input with Ctrl-D"
                );
            }
            read_stdin_for_stream().map(buffered_stdin_bytes)
        },
    )?);
    let execution_input = if io {
        if std::io::stdin().is_terminal() {
            eprintln!(
                "note: pre-buffering standard input until end of file (--io on batch mode); \
                 end the input with Ctrl-D"
            );
        }
        Some(read_stdin_for_stream()?)
    } else {
        None
    };
    let missing_config_vars = missing_variables(available_config_vars, &seen_config_vars);
    if !missing_config_vars.is_empty() {
        return Err(format!(
            "missing required configuration variable{} {}; pass {}",
            if missing_config_vars.len() == 1 {
                ""
            } else {
                "s"
            },
            missing_config_vars.join(", "),
            missing_config_vars
                .iter()
                .map(|name| format!("`-c {}=VALUE`", name.trim_start_matches('$')))
                .collect::<Vec<_>>()
                .join(" and ")
        )
        .into());
    }
    let initial = top_cell_initializer(program, config_vars);
    let config_vars_parse_seconds = started.elapsed().as_secs_f64();
    drop(config_vars_parse_phase);

    let internalize_phase =
        tracing::info_span!("phase", name = tracing::field::display("internalize")).entered();
    let started = Instant::now();
    let syntax = parse_kore_definition(&compiled.definition_kore)?;

    let backend = Backend::internalize_source_definition(
        &syntax,
        &compiled.main_module,
        &compiled.execution_rewrite_order,
    )?;
    let function_symbols = backend.function_symbol_names();
    backend.validate_executable_pattern(&initial)?;
    let initial = backend.internalize_frontend_term(&initial, &[])?;
    let match_target = match match_target_source {
        Some(MatchTargetSource::Surface(compiled)) => {
            Some(prepare_backend_match_target(&backend, compiled)?)
        }
        Some(MatchTargetSource::KoreFile(path)) => {
            debug_assert_eq!(
                options
                    .search
                    .as_ref()
                    .and_then(|search| search.pattern.as_ref()),
                Some(&path)
            );
            None
        }
        None => None,
    };
    let internalize_seconds = started.elapsed().as_secs_f64();
    drop(internalize_phase);
    let execute_phase =
        tracing::info_span!("phase", name = tracing::field::display("execute")).entered();
    let started = Instant::now();
    let mut backend = Backend::from_internalized(
        backend,
        BackendOptions {
            smt_timeout_ms: options.smt.timeout_ms,
            smt_retry_limit: options.smt.retry_limit,
        },
    )?;
    let output = backend.run_cli(
        None,
        vec![Pattern {
            term: initial,
            constraints: Vec::new(),
        }],
        BackendRunOptions {
            depth: options.depth,
            max_simplification_iterations: options.max_simplification_iterations,
            breadth_limit: options.breadth_limit,
            execute_to_branch: options.execute_to_branch,
            cut_point_rules: options.cut_point_rules,
            terminal_rules: options.terminal_rules,
            strategy: options.strategy,
            search: options.search,
            match_target,
            function_symbols,
            stop_leaves: None,
            step_timeout: options.step_timeout,
            moving_average_timeout: options.moving_average_timeout,
            capture_stdout: options.output == KrunOutputArg::Captured,
            execution_input,
        },
    )?;
    let execute_seconds = started.elapsed().as_secs_f64();
    drop(execute_phase);
    let output_phase =
        tracing::info_span!("phase", name = tracing::field::display("output")).entered();
    let started = Instant::now();
    if options.output == KrunOutputArg::Kore
        && output.live_transcript.as_ref().is_some_and(|transcript| {
            transcript
                .iter()
                .any(|entry| entry.descriptor == 1 && !entry.bytes.is_empty())
        })
    {
        return Err(
            "--io on produced console stdout; use --output none so program output remains separate from KORE result rendering"
                .into(),
        );
    }
    if let Some(transcript) = &output.live_transcript {
        deliver_console_transcript(transcript)?;
    }
    match options.output {
        KrunOutputArg::Kore => write_kore_result(&output.pattern, None)?,
        KrunOutputArg::Captured => {
            io::stdout().lock().write_all(
                output
                    .captured_stdout
                    .as_deref()
                    .expect("captured output was requested and validated"),
            )?;
        }
        KrunOutputArg::None => {}
    }
    let output_seconds = started.elapsed().as_secs_f64();
    drop(output_phase);
    KrunTimings {
        compile: compiled.timings,
        program_parse_seconds,
        config_vars_parse_seconds,
        internalize_seconds,
        execute_seconds,
        output_seconds,
    }
    .write(options.timings.as_deref())?;
    let exit_code = ExitCode::from(output.exit_code);
    // The result and the timings are written, and the process exits once `main` returns.
    // `_trace` still drops normally: it finishes the trace and aggregate files.
    // Borrowers are released before what they borrow.
    release_at_exit(config_injector);
    release_at_exit(config_parsers);
    release_at_exit(macro_definition);
    release_at_exit(program_resolved);
    release_at_exit(program_definition);
    release_at_exit((
        compiled.frontend_definition,
        compiled.execution_definition,
        compiled.definition_kore,
    ));
    release_at_exit(syntax);
    release_at_exit(backend);
    release_at_exit(output);
    Ok(exit_code)
}

/// Leave a value allocated until the process exits instead of dropping it.
///
/// The operating system reclaims all of a process's memory when it exits, so walking and freeing
/// a definition-sized structure just before that has no observable effect and only takes time.
/// Callers pass only values whose drop does nothing but free memory: no file, buffered writer,
/// child process, temporary directory, lock, or trace guard is reachable from them. A command
/// calls this only after writing all of its output, right before returning to `main`.
fn release_at_exit<T>(value: T) {
    std::mem::forget(value);
}

/// Return the macro expander's definition for `definition`, preparing it on first use.
fn prepared_macro_definition<'slot>(
    slot: &'slot mut Option<MacroExpansionDefinition>,
    definition: &k_rust::definition::Definition,
) -> Result<&'slot MacroExpansionDefinition, String> {
    if slot.is_none() {
        *slot = Some(MacroExpansionDefinition::prepare(definition)?);
    }
    Ok(slot
        .as_ref()
        .expect("the macro definition was prepared above"))
}

fn kore_exec(options: KoreExecArgs) -> Result<ExitCode, Box<dyn Error>> {
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
    let construction_module = definition
        .modules
        .iter()
        .any(|module| module.name == options.module)
        .then(|| options.module.clone())
        .or_else(|| definition.modules.last().map(|module| module.name.clone()))
        .ok_or_else(|| io::Error::other("KORE definition has no modules"))?;
    let backend_options = BackendOptions {
        smt_timeout_ms: options.smt.options().timeout_ms,
        smt_retry_limit: options.smt.options().retry_limit,
    };
    let mut backend = Backend::from_definition(definition, construction_module, backend_options)?;
    for path in &options.added_modules {
        let source = fs::read_to_string(path)?;
        parse_kore_module(&source).map_err(|error| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "could not parse added KORE module {}: {error}",
                    path.display()
                ),
            )
        })?;
        backend.add_module(&source, true)?;
    }
    let function_symbols = backend
        .select_definition(Some(&options.module))?
        .function_symbol_names();
    let initial = backend.load_patterns(Some(&options.module), &options.pattern, "initial")?;
    let output = backend.run_cli(
        Some(&options.module),
        initial,
        BackendRunOptions {
            depth: options.depth.unwrap_or(u64::MAX),
            max_simplification_iterations: options
                .max_simplification_iterations
                .unwrap_or(DEFAULT_MAX_SIMPLIFICATION_ITERATIONS),
            breadth_limit: options.breadth_limit,
            execute_to_branch: options.execute_to_branch,
            cut_point_rules: options.cut_point_rules.into_iter().collect(),
            terminal_rules: options.terminal_rules.into_iter().collect(),
            strategy: options.strategy.into(),
            search: options.search.into_options(),
            match_target: None,
            function_symbols,
            stop_leaves: options.stop_leaves,
            step_timeout: options.timeout.timeout(),
            moving_average_timeout: options.timeout.moving_average,
            capture_stdout: false,
            execution_input: None,
        },
    )?;
    write_kore_result(&output.pattern, options.output.as_deref())?;
    Ok(ExitCode::from(output.exit_code))
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
    let backend = Backend::from_definition(
        definition,
        options.module,
        BackendOptions {
            smt_timeout_ms: options.smt.timeout.get(),
            smt_retry_limit: options.smt.retry_limit,
        },
    )?;
    rpc::serve(backend, (options.host.as_str(), options.port))
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
    let mut backend = Backend::from_definition(
        definition,
        &options.module,
        BackendOptions {
            smt_timeout_ms: options.smt.options().timeout_ms,
            smt_retry_limit: options.smt.options().retry_limit,
        },
    )?;
    let syntax = load_kore_syntax(&options.pattern, "simplification")?;
    let output = backend.simplify_kore(None, &syntax)?;
    write_kore_result(&output, options.output.as_deref())
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
    let mut backend = Backend::from_definition(
        definition,
        &options.module,
        BackendOptions {
            smt_timeout_ms: options.smt.options().timeout_ms,
            smt_retry_limit: options.smt.options().retry_limit,
        },
    )?;
    let syntax = load_kore_syntax(&options.pattern, "model")?;
    let model = backend.model_for(None, &syntax)?;
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
    let mut backend = Backend::from_definition(
        definition,
        &options.module,
        BackendOptions {
            smt_timeout_ms: options.smt.options().timeout_ms,
            smt_retry_limit: options.smt.options().retry_limit,
        },
    )?;
    let antecedent_syntax = load_kore_syntax(&options.antecedent, "antecedent")?;
    let consequent_syntax = load_kore_syntax(&options.consequent, "consequent")?;
    let (result, result_sort) =
        backend.implies_kore(None, &antecedent_syntax, &consequent_syntax)?;
    let output = k_rust::backend::implication::cli_output(
        &antecedent_syntax,
        &consequent_syntax,
        &result_sort,
        result,
    )?;
    if let Some(path) = options.output {
        fs::write(path, output)?;
    } else {
        println!("{output}");
    }
    Ok(())
}

fn kore_match_disjunction_command(options: KoreMatchDisjunctionArgs) -> Result<(), Box<dyn Error>> {
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
    let mut backend =
        Backend::from_definition(definition, &options.module, BackendOptions::default())?;
    let function_symbols = backend.select_definition(None)?.function_symbol_names();

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
    let target = backend.with_solver(None, |definition, _| {
        definition
            .verify_standalone_pattern(&target)
            .and_then(|()| definition.internalize_pattern(&target, &[]))
            .map_err(|error| BackendError(error.to_string()))
    })?;

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
    let alternatives = backend.with_solver(None, |definition, _| {
        definition
            .internalize_disjunction(&disjunction, &[])
            .map_err(|error| BackendError(error.to_string()))
    })?;
    let matches = backend.match_patterns(None, &target, &alternatives)?;
    let output_sort = externalize::sort(&target.term.sort());
    let output = pattern_matches_output(
        &matches,
        &output_sort,
        &target.term.sort(),
        &BTreeSet::new(),
        &function_symbols,
    );
    write_kore_result(&output, options.output.as_deref())
}

/// Write `pattern` as `KorePrinter::pretty(100).print_pattern` prints it, rendering as it goes
/// so that the text is never held whole: to the file `path` as the text alone, or to standard
/// output followed by a newline.
fn write_kore_result(pattern: &KorePattern, path: Option<&Path>) -> Result<(), Box<dyn Error>> {
    const BUFFER_BYTES: usize = 1 << 20;
    let printer = KorePrinter::pretty(100);
    match path {
        Some(path) => {
            let mut file = io::BufWriter::with_capacity(BUFFER_BYTES, fs::File::create(path)?);
            printer.write_pattern(pattern, &mut file)?;
            file.into_inner().map_err(io::IntoInnerError::into_error)?;
        }
        None => {
            let mut stdout = io::BufWriter::with_capacity(BUFFER_BYTES, io::stdout().lock());
            printer.write_pattern(pattern, &mut stdout)?;
            stdout.write_all(b"\n")?;
            stdout.flush()?;
        }
    }
    Ok(())
}

/// A writer that writes each line of the text written through it to `inner` preceded by
/// `prefix` and followed by a newline, as `for line in text.lines() { writeln!(inner,
/// "{prefix}{line}") }` does once the text is complete, without holding the text.
///
/// `str::lines` splits at `\n` and at `\r\n`, drops those terminators, and yields no empty line
/// after a final terminator. So a `\r` is held back until the next byte shows whether it ends
/// the line, a line's prefix is written with its first byte (an empty line's with its `\n`),
/// and `finish` terminates a last line that has no `\n`, keeping a `\r` that no `\n` followed.
struct PrefixedLines<W: Write> {
    inner: W,
    prefix: &'static str,
    line_open: bool,
    pending_carriage_return: bool,
}

impl<W: Write> PrefixedLines<W> {
    fn new(inner: W, prefix: &'static str) -> Self {
        Self {
            inner,
            prefix,
            line_open: false,
            pending_carriage_return: false,
        }
    }

    /// Write the prefix if the current line has not started, and a held `\r` that a byte other
    /// than `\n` follows.
    fn continue_line(&mut self) -> io::Result<()> {
        if !self.line_open {
            self.inner.write_all(self.prefix.as_bytes())?;
            self.line_open = true;
        }
        if self.pending_carriage_return {
            self.inner.write_all(b"\r")?;
            self.pending_carriage_return = false;
        }
        Ok(())
    }

    fn finish(mut self) -> io::Result<W> {
        if self.line_open {
            if self.pending_carriage_return {
                self.inner.write_all(b"\r")?;
            }
            self.inner.write_all(b"\n")?;
        }
        Ok(self.inner)
    }
}

impl<W: Write> Write for PrefixedLines<W> {
    fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
        let mut rest = buffer;
        // Invariant: the bytes of `buffer` before `rest` have been written, or held as the one
        // pending `\r`, as the line-by-line form writes them.
        while !rest.is_empty() {
            let end = rest
                .iter()
                .position(|byte| matches!(byte, b'\n' | b'\r'))
                .unwrap_or(rest.len());
            if end > 0 {
                self.continue_line()?;
                self.inner.write_all(&rest[..end])?;
            }
            match rest.get(end) {
                Some(b'\n') => {
                    if !self.line_open {
                        self.inner.write_all(self.prefix.as_bytes())?;
                    }
                    self.pending_carriage_return = false;
                    self.inner.write_all(b"\n")?;
                    self.line_open = false;
                }
                Some(_) => {
                    self.continue_line()?;
                    self.pending_carriage_return = true;
                }
                None => break,
            }
            rest = &rest[end + 1..];
        }
        Ok(buffer.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

#[cfg(test)]
mod prefixed_lines_tests {
    use std::io::Write;

    use proptest::prelude::*;

    use super::PrefixedLines;

    proptest! {
        /// Writing a text through `PrefixedLines` in arbitrary pieces gives the bytes that
        /// `writeln!` over `str::lines` gives on the whole text.
        #[test]
        fn prefixed_lines_match_str_lines(
            text in "[a\r\n ]{0,40}",
            cuts in prop::collection::vec(0usize..41, 0..6),
        ) {
            let mut expected = Vec::new();
            for line in text.lines() {
                writeln!(expected, "    {line}").unwrap();
            }
            let mut cuts = cuts
                .into_iter()
                .map(|cut| cut.min(text.len()))
                .collect::<Vec<_>>();
            cuts.push(0);
            cuts.push(text.len());
            cuts.sort_unstable();
            let mut lines = PrefixedLines::new(Vec::new(), "    ");
            for piece in cuts.windows(2) {
                lines.write_all(&text.as_bytes()[piece[0]..piece[1]]).unwrap();
            }
            prop_assert_eq!(lines.finish().unwrap(), expected);
        }
    }
}

fn deliver_console_transcript(transcript: &[DescriptorTranscriptEntry]) -> io::Result<()> {
    let stdout = io::stdout();
    let stderr = io::stderr();
    let mut stdout = stdout.lock();
    let mut stderr = stderr.lock();
    for entry in transcript {
        match entry.descriptor {
            1 => {
                stdout.write_all(&entry.bytes)?;
                stdout.flush()?;
            }
            2 => {
                stderr.write_all(&entry.bytes)?;
                stderr.flush()?;
            }
            descriptor => {
                return Err(io::Error::other(format!(
                    "execution produced output for unsupported console descriptor {descriptor}"
                )));
            }
        }
    }
    Ok(())
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
    kore_codec::decode_bytes(input)
        .map_err(|error| invalid_kore_pattern(path, purpose, error.encoding, error.cause))
}

fn invalid_kore_pattern(
    path: &Path,
    purpose: &str,
    encoding: impl fmt::Display,
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

fn compile_proof_source(
    common: &CommonOptions,
    definition_module: &str,
    prepared: Option<&Path>,
) -> Result<KoreDefinition, Box<dyn Error>> {
    let loaded = if let Some(prepared) = prepared {
        load_definition_against_prepared(common, definition_module, prepared, false)?.0
    } else {
        load_definition(
            common,
            Some(CompilationBackend::Rust),
            Some(definition_module),
        )?
    };
    let builtin_source_prefixes = common.builtin_source_prefixes();
    let compiled = match compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend: CompilationBackend::Rust,
            default_claims_to_all_path: true,
            diagnostics: common.diagnostics,
            check_mode: CheckMode::Proof {
                definition_module: definition_module.to_owned(),
            },
            builtin_source_prefixes,
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
    Ok(parse_kore_definition(&compiled.definition_kore)?)
}

/// Load a specification against a prepared semantics directory, recording the prepared-artifact
/// read and every loader phase in the returned timings.
fn load_definition_against_prepared(
    options: &CommonOptions,
    definition_module: &str,
    prepared: &Path,
    bison_lists: bool,
) -> Result<(k_rust::outer::LoadedDefinition, PhaseTimings), Box<dyn Error>> {
    let span_started = Instant::now();
    let mut timings = PhaseTimings::default();
    let (mut resolver, entry, manifest, base) =
        timings.time(load_phase::READ_PREPARED_DEFINITION, || {
            let directory = prepared_artifact_directory(prepared);
            let manifest = load_prepared_manifest(prepared)?;
            let base: k_rust::definition::Definition =
                definition_json::from_str(&fs::read_to_string(directory.join("parsed.json"))?)?;
            let builtin_directory = options
                .builtin_directory
                .clone()
                .or_else(|| env::var_os("KRUST_BUILTIN_DIRECTORY").map(PathBuf::from));
            let mut resolver = FileResolver::from_current_directory(options.includes.clone())?;
            if let Some(directory) = builtin_directory {
                resolver = resolver.with_builtin_directory(directory);
            }
            resolver = resolver.with_prepared_sources(manifest.sources.clone());
            let entry = resolver.load_entry(&options.definition)?;
            Ok::<_, Box<dyn Error>>((resolver, entry, manifest, base))
        })?;
    let (loaded, loader_timings) = load_with_prepared_base_timed(
        entry,
        &options.module,
        &mut resolver,
        &LoadOptions {
            markdown_selector: options.markdown_selector.clone(),
            implicit_sources: Vec::new(),
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            configuration_module: Some(definition_module.into()),
            project_root: None,
            diagnostics: options.diagnostics,
            bison_lists,
        },
        &base,
        &manifest.sources,
        &manifest.modules,
    )?;
    timings.extend(loader_timings);
    timings.set_span_seconds(span_started.elapsed().as_secs_f64());
    Ok((loaded, timings))
}

fn load_prepared_manifest(path: &Path) -> Result<PreparedDefinitionManifest, Box<dyn Error>> {
    let path = prepared_artifact_directory(path).join(PREPARED_MANIFEST);
    let manifest: PreparedDefinitionManifest = serde_json::from_str(&fs::read_to_string(&path)?)?;
    if manifest.format != PREPARED_FORMAT || manifest.version != 1 {
        return Err(format!(
            "unsupported prepared definition manifest format {:?} version {}",
            manifest.format, manifest.version
        )
        .into());
    }
    Ok(manifest)
}

fn prepared_artifact_directory(path: &Path) -> PathBuf {
    if path.is_dir() {
        path.to_owned()
    } else {
        path.parent().unwrap_or_else(|| Path::new(".")).to_owned()
    }
}

fn kprove(options: KproveOptions) -> Result<(), Box<dyn Error>> {
    let _trace = start_trace(options.trace.as_deref(), options.trace_aggregate.as_deref())?;
    let started = Instant::now();
    let syntax = {
        let _phase =
            tracing::info_span!("phase", name = tracing::field::display("input")).entered();
        match &options.input {
            KproveInput::Source(common) => {
                compile_proof_source(common, &options.definition_module, None)?
            }
            KproveInput::Compiled(path) => load_compiled_definition(path)?,
            KproveInput::SourceWithCompiled { source, compiled } => {
                compile_proof_source(source, &options.definition_module, Some(compiled))?
            }
        }
    };
    let mut timings = ProofTimings {
        input_seconds: started.elapsed().as_secs_f64(),
        ..ProofTimings::default()
    };
    let started = Instant::now();
    let definition = {
        let _phase =
            tracing::info_span!("phase", name = tracing::field::display("internalize")).entered();
        Backend::internalize_definition(&syntax, &options.module)?
    };
    timings.internalize_seconds = started.elapsed().as_secs_f64();
    if options.load_only {
        return timings.write(options.timings.as_deref());
    }
    let setup_phase =
        tracing::info_span!("phase", name = tracing::field::display("proof_setup")).entered();
    let setup_started = Instant::now();
    let saved_proofs = SavedProofs::load(options.save_proofs.as_deref())?;
    let spec_module = syntax
        .modules
        .iter()
        .find(|module| module.name == options.module)
        .ok_or_else(|| format!("compiled KORE has no module `{}`", options.module))?;
    let mut proven_ids = saved_proofs.proven_ids(spec_module);
    if definition.reachability_claims.is_empty() {
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
    let kept = filter_claims(
        &definition.reachability_claims,
        &ClaimFilter {
            selected: options.claims,
            excluded: options.excluded_claims,
            trusted: options.trusted_claims,
        },
    )?;
    // `Kore.Exec.assertSomeClaims`: the reference aborts on a filtered module with no claims.
    if kept.is_empty() {
        return Err("the selected module contains no modal reachability claims".into());
    }
    let circularities = kept.iter().collect::<Vec<_>>();
    let mut backend = Backend::from_internalized_with_prelude(
        definition,
        BackendOptions {
            smt_timeout_ms: options.smt.timeout_ms,
            smt_retry_limit: options.smt.retry_limit,
        },
        smt_prelude,
    )
    .map_err(|error| {
        io::Error::other(
            if error.0 == "could not initialize Z3: InconsistentPrelude" {
                "the definitions sent to the solver are inconsistent".to_owned()
            } else {
                error.to_string()
            },
        )
    })?;

    timings.proof_setup_seconds = setup_started.elapsed().as_secs_f64();
    drop(setup_phase);
    let mut output = io::stdout().lock();
    let mut all_proven = true;
    let proof_phase =
        tracing::info_span!("phase", name = tracing::field::display("proof")).entered();
    // Invariant: proven_ids contains every uniquely identified claim proven before this index.
    for (index, claim) in kept.iter().enumerate() {
        let name = claim
            .attributes
            .label
            .as_deref()
            .map_or_else(|| format!("#{}", index + 1), str::to_owned);
        if claim.attributes.trusted {
            writeln!(output, "claim {name}: proven (trusted)")?;
            timings.claims.push(ClaimTiming {
                label: name,
                seconds: 0.0,
                status: "trusted".into(),
            });
            continue;
        }
        if proven_ids.contains(&claim.attributes.unique_id) {
            writeln!(output, "claim {name}: proven (saved)")?;
            timings.claims.push(ClaimTiming {
                label: name,
                seconds: 0.0,
                status: "saved".into(),
            });
            continue;
        }
        let started = Instant::now();
        let proof_options = ProofOptions {
            max_depth: options.depth,
            min_depth: options.min_depth,
            breadth_limit: options.breadth_limit,
            max_counterexamples: options.max_counterexamples,
            max_simplification_iterations: options.max_simplification_iterations,
            allow_vacuous: options.allow_vacuous,
            search_order: options.graph_search,
            stuck_check: options.stuck_check,
            step_timeout: options.step_timeout,
            moving_average_timeout: options.moving_average_timeout,
        };
        let result = backend.with_solver(None, |definition, solver| {
            k_rust::backend::proving::run_claim(
                definition,
                claim,
                &circularities,
                proof_options,
                solver,
            )
            .map_err(|error| BackendError(format!("could not prove claim: {error:?}")))
        })?;
        let seconds = started.elapsed().as_secs_f64();
        timings.proof_seconds += seconds;
        timings.claims.push(ClaimTiming {
            label: name.clone(),
            seconds,
            status: proof_status(result.status).into(),
        });
        writeln!(
            output,
            "claim {name}: {} ({} states, {} unexplored)",
            proof_status(result.status),
            result.explored_states,
            result.unexplored_states,
        )?;
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
                writeln!(output, "  {:?} at depth {}", leaf.outcome, leaf.depth)?;
                if matches!(
                    leaf.outcome,
                    ProofLeafOutcome::Vacuous | ProofLeafOutcome::Trivial
                ) {
                    writeln!(
                        output,
                        "  the left-hand side of the claim has been simplified to bottom \
                         (--allow-vacuous accepts such branches)"
                    )?;
                }
                let pattern = externalize::constrained_pattern(&leaf.pattern);
                let mut lines = PrefixedLines::new(io::BufWriter::new(&mut output), "    ");
                KorePrinter::pretty(100).write_pattern(&pattern, &mut lines)?;
                lines
                    .finish()?
                    .into_inner()
                    .map_err(io::IntoInnerError::into_error)?;
            }
        }
    }
    drop(proof_phase);
    saved_proofs.save(spec_module, &proven_ids)?;
    timings.write(options.timings.as_deref())?;
    // The claim results and the timings are written; `output` and `_trace` still drop normally.
    release_at_exit(circularities);
    release_at_exit(kept);
    release_at_exit(backend);
    release_at_exit(syntax);
    if !all_proven {
        return Err("one or more reachability claims were not proven".into());
    }
    Ok(())
}

fn load_compiled_definition(path: &Path) -> Result<KoreDefinition, Box<dyn Error>> {
    let path = if path.is_dir() {
        path.join("definition.kore")
    } else {
        path.to_owned()
    };
    let source = fs::read_to_string(&path).map_err(|error| {
        io::Error::new(
            error.kind(),
            format!(
                "could not read compiled KORE definition `{}`: {error}",
                path.display()
            ),
        )
    })?;
    parse_kore_definition(&source).map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "could not parse compiled KORE definition `{}`: {error}",
                path.display()
            ),
        )
        .into()
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

fn read_stdin() -> io::Result<String> {
    let mut source = String::new();
    io::stdin().read_to_string(&mut source)?;
    Ok(source)
}

fn read_stdin_for_stream() -> io::Result<Vec<u8>> {
    let mut input = Vec::new();
    io::stdin().read_to_end(&mut input)?;
    Ok(input)
}

/// The text K's krun buffers into `$STDIN` under `--io off` (krun:557-558): standard input is
/// read by a command substitution, which drops every trailing newline, and fed through a bash
/// here-string, which appends one, to the escaping awk script, which emits every record with
/// `ORS`. The buffer therefore ends in exactly one newline, also when standard input is empty
/// (`#buffer("\n")`); interior newlines and every other byte are kept.
fn buffered_stdin_bytes(mut input: Vec<u8>) -> Vec<u8> {
    let trimmed = input
        .iter()
        .rposition(|byte| *byte != b'\n')
        .map_or(0, |index| index + 1);
    input.truncate(trimmed);
    input.push(b'\n');
    input
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
    use k_rust::{
        backend::{
            execution::{default_search_pattern, term_exit_code},
            proving::{
                SAVED_PROOFS_MODULE, claim_unique_id, resolve_claim_labels, saved_proof_definition,
            },
        },
        kompile::initial_configuration::{kore_application, kore_sort},
        kore::{
            ast::{Sentence as KoreSentence, Sort as KoreSort, Symbol as KoreSymbol},
            binary as kore_binary,
        },
    };
    use k_rust_backend::{
        definition::{BackendDefinition, PatternOrPredicate},
        implication::ImplicationCondition,
        rule::Predicate,
        search::PatternMatch,
        simplify::{
            SimplificationOptions, simplify_and_decide_predicate_with_solver,
            simplify_pattern_with_solver,
        },
        smt::Z3Solver,
        substitution::Substitution,
        term::{
            FunctionType, Symbol, SymbolAttributes, SymbolType, Term, TermKind, Variable,
            VariableKind as BackendVariableKind,
        },
    };

    #[cfg(test)]
    fn simplify_kore_pattern(
        definition: &BackendDefinition,
        syntax: &KorePattern,
    ) -> Result<KorePattern, Box<dyn Error>> {
        simplify_kore_pattern_with_options(definition, syntax, Z3Options::default())
    }

    #[cfg(test)]
    fn simplify_kore_pattern_with_options(
        definition: &BackendDefinition,
        syntax: &KorePattern,
        options: Z3Options,
    ) -> Result<KorePattern, Box<dyn Error>> {
        let solver = Z3Solver::with_options(definition, options)
            .map_err(|error| io::Error::other(format!("could not initialize Z3: {error:?}")))?;
        match definition.internalize_pattern_or_predicate(syntax, &[])? {
            PatternOrPredicate::Term(pattern) => {
                let simplified = simplify_pattern_with_solver(
                    definition,
                    &pattern,
                    SimplificationOptions::unbounded(),
                    &solver,
                )
                .map_err(|error| {
                    io::Error::other(format!("could not simplify KORE pattern: {error:?}"))
                })?;
                Ok(externalize::constrained_pattern(&simplified))
            }
            PatternOrPredicate::Predicate(predicate, result_sort) => {
                let simplified = simplify_and_decide_predicate_with_solver(
                    definition,
                    &predicate,
                    &[],
                    SimplificationOptions::unbounded(),
                    &solver,
                )
                .map_err(|error| {
                    io::Error::other(format!("could not simplify KORE pattern: {error:?}"))
                })?;
                Ok(externalize::ml_pattern(&simplified, &result_sort))
            }
        }
    }
    #[cfg(test)]
    fn implication_condition_output(
        condition: &ImplicationCondition,
        result_sort: &BackendSort,
        antecedent_variable: Option<&str>,
    ) -> Result<serde_json::Value, Box<dyn Error>> {
        k_rust::backend::implication::cli_condition_output(
            condition,
            result_sort,
            antecedent_variable,
        )
    }

    #[cfg(test)]
    fn kore_json_value(pattern: &KorePattern) -> Result<serde_json::Value, Box<dyn Error>> {
        Ok(kore_json::to_value(pattern)?)
    }
    #[cfg(test)]
    fn decode_backend_pattern(
        definition: &BackendDefinition,
        path: &Path,
        purpose: &str,
        input: &[u8],
    ) -> Result<Pattern, Box<dyn Error>> {
        let syntax = kore_codec::decode_bytes(input)
            .map_err(|error| invalid_kore_pattern(path, purpose, error.encoding, error.cause))?;
        definition.verify_standalone_pattern(&syntax)?;
        definition
            .internalize_pattern(&syntax, &[])
            .map_err(Into::into)
    }

    #[test]
    fn buffered_stdin_ends_in_exactly_one_newline() {
        assert_eq!(buffered_stdin_bytes(Vec::new()), b"\n");
        assert_eq!(buffered_stdin_bytes(b"ab".to_vec()), b"ab\n");
        assert_eq!(buffered_stdin_bytes(b"ab\n".to_vec()), b"ab\n");
        assert_eq!(buffered_stdin_bytes(b"ab\n\n\n".to_vec()), b"ab\n");
        assert_eq!(buffered_stdin_bytes(b"\n\n".to_vec()), b"\n");
        assert_eq!(
            buffered_stdin_bytes(b"a\r\n\nb\r\n".to_vec()),
            b"a\r\n\nb\r\n"
        );
        assert_eq!(buffered_stdin_bytes(vec![b'x', 0x80]), [b'x', 0x80, b'\n']);
    }

    #[test]
    fn exit_code_maps_reference_integer_values() {
        let value = |value: &str| Term::domain_value(BackendSort::simple("SortInt"), value);

        assert_eq!(term_exit_code(&value("0")), Some(0));
        assert_eq!(term_exit_code(&value("7")), Some(7));
        assert_eq!(term_exit_code(&value("-1")), Some(255));
        assert_eq!(term_exit_code(&value("256")), Some(0));
        assert_eq!(term_exit_code(&value("not-an-integer")), None);
        assert_eq!(
            term_exit_code(&Term::variable(Variable::new(
                "VarExit",
                BackendSort::simple("SortInt")
            ))),
            None
        );
    }

    #[test]
    fn disjuncts_are_printed_in_structural_order() {
        let sort = kore_sort("SortGeneratedTopCell");
        let application = |name: &str| kore_application(name, Vec::new(), Vec::new());
        let solution = |name: &str| KorePattern::Equals {
            operand_sort: sort.clone(),
            result_sort: sort.clone(),
            left: Box::new(KorePattern::Variable(k_rust::kore::ast::Variable {
                kind: k_rust::kore::ast::VariableKind::Element,
                name: "VarResult".into(),
                sort: sort.clone(),
            })),
            right: Box::new(application(name)),
        };

        assert_eq!(
            order_disjuncts(vec![solution("c"), solution("a"), solution("b")]),
            vec![solution("a"), solution("b"), solution("c")]
        );

        let application = application("a");
        let top = KorePattern::Top { sort: sort.clone() };
        let conjunction = KorePattern::And {
            sort,
            arguments: vec![top.clone(), top.clone()],
        };
        assert_eq!(
            order_disjuncts(vec![conjunction.clone(), top.clone(), application.clone()]),
            vec![application, top, conjunction]
        );
    }

    #[test]
    fn default_search_uses_the_reference_kore_variable_name() {
        let initial = Pattern {
            term: Term::variable(Variable::new(
                "Initial",
                BackendSort::simple("SortGeneratedTopCell"),
            )),
            constraints: Vec::new(),
        };
        let target = default_search_pattern(&initial);
        let TermKind::Variable(variable) = target.term.kind() else {
            panic!("default search target should be a variable");
        };

        assert_eq!(variable.name.as_ref(), "VarResult");
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
    fn implication_condition_output_keeps_witnesses_separate() {
        let result_sort = BackendSort::simple("SortS");
        let condition = ImplicationCondition {
            predicates: Vec::new(),
            substitution: Substitution::new(),
            witnesses: Substitution::from([(
                Variable::new("Y!exists0", result_sort.clone()),
                Term::variable(Variable::new("X", result_sort.clone())),
            )]),
        };

        let output = implication_condition_output(&condition, &result_sort, None).unwrap();
        assert_eq!(output["predicate"]["term"]["tag"], "Top", "{output:#}");
        assert_eq!(output["substitution"]["term"]["tag"], "Top", "{output:#}");
        assert_eq!(output["witnesses"]["term"]["tag"], "Equals", "{output:#}");
        assert_eq!(
            output["witnesses"]["term"]["first"]["name"], "Y",
            "{output:#}"
        );
        assert_eq!(
            output["witnesses"]["term"]["second"]["name"], "X",
            "{output:#}"
        );
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
        assert_eq!(options.sort.as_deref(), Some("Exp"));
        assert!(options.batch_cases.is_empty());
        assert!(options.batch_reject_cases.is_empty());
        assert_eq!(options.expression.as_deref(), Some("1 + 2"));
        assert_eq!(options.output, OutputFormat::Json);
    }

    #[test]
    fn parses_kast_batch_cases() {
        let cli = Cli::try_parse_from([
            "krust",
            "kast",
            "definition.k",
            "--module",
            "MAIN",
            "--batch-case",
            "one",
            "Exp",
            "1",
            "--batch-case",
            "sum",
            "Exp",
            "1 + 2",
            "--batch-reject-case",
            "bad",
            "Exp",
            "+",
            "--output",
            "json",
        ])
        .unwrap();
        let Command::Kast(options) = cli.command else {
            panic!("expected kast command");
        };
        let options = KastOptions::from(options);
        assert_eq!(options.sort, None);
        assert_eq!(options.batch_cases.len(), 2);
        assert_eq!(options.batch_cases[0].name, "one");
        assert_eq!(options.batch_cases[0].sort, "Exp");
        assert_eq!(options.batch_cases[0].expression, "1");
        assert_eq!(options.batch_cases[1].name, "sum");
        assert_eq!(options.batch_cases[1].expression, "1 + 2");
        assert_eq!(options.batch_reject_cases.len(), 1);
        assert_eq!(options.batch_reject_cases[0].name, "bad");
        assert_eq!(options.batch_reject_cases[0].expression, "+");
    }

    #[test]
    fn kast_defaults_to_the_kcompile_backend() {
        let parse = |extra: &[&str]| {
            let mut arguments = vec![
                "krust",
                "kast",
                "definition.k",
                "--module",
                "MAIN",
                "--sort",
                "Exp",
                "--expression",
                "value",
            ];
            arguments.extend_from_slice(extra);
            let cli = Cli::try_parse_from(arguments).unwrap();
            let Command::Kast(options) = cli.command else {
                panic!("expected kast command");
            };
            KastOptions::from(options).backend
        };

        assert_eq!(parse(&[]), CompilationBackend::Rust);
        assert_eq!(
            parse(&[]),
            CompilationBackend::from(CompilationBackendArg::default())
        );
        assert_eq!(parse(&["--backend", "llvm"]), CompilationBackend::Llvm);
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
            "--syntax-module",
            "GRAMMAR",
            "--sort",
            "Exp",
            "--expression",
            "1 + 2",
            "-c",
            "ENV=.Map",
            "--io",
            "off",
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

        let source = options.source.as_ref().unwrap();
        assert_eq!(source.definition, Path::new("definition.k"));
        assert_eq!(source.module, "MAIN");
        assert_eq!(options.syntax_module.as_deref(), Some("GRAMMAR"));
        assert_eq!(options.sort, "Exp");
        assert_eq!(options.expression.as_deref(), Some("1 + 2"));
        assert_eq!(options.config_vars, ["ENV=.Map"]);
        assert_eq!(options.io, Some(false));
        assert_eq!(options.depth, 42);
        assert_eq!(options.breadth_limit, Some(7));
        assert!(options.execute_to_branch);
        assert_eq!(
            options.cut_point_rules,
            BTreeSet::from(["MAIN.loop".into()])
        );
        assert_eq!(options.terminal_rules, BTreeSet::from(["rule-id".into()]));
        assert_eq!(options.strategy, ExecutionMode::Any);
        assert!(options.surface_pattern.is_none());
        assert!(options.search.is_none());
        assert_eq!(options.step_timeout, Some(Duration::from_millis(250)));
        assert!(options.moving_average_timeout);
        assert_eq!(options.smt, Z3Options::default());
    }

    fn parse_krun_pattern_options(extra: &[&str]) -> Result<KrunOptions, clap::Error> {
        let mut arguments = vec![
            "krust",
            "krun",
            "definition.k",
            "--main-module",
            "MAIN",
            "--sort",
            "Exp",
        ];
        arguments.extend_from_slice(extra);
        let cli = Cli::try_parse_from(arguments)?;
        let Command::Krun(options) = cli.command else {
            unreachable!("the command name is fixed above")
        };
        Ok(options.into())
    }

    #[test]
    fn krun_accepts_surface_pattern_without_search() {
        let options = parse_krun_pattern_options(&["--pattern", "<k> X => Y </k>"]).unwrap();

        assert_eq!(options.surface_pattern.as_deref(), Some("<k> X => Y </k>"));
        assert!(options.search.is_none());
    }

    #[test]
    fn krun_accepts_surface_pattern_with_each_search_mode() {
        for (flag, expected) in [
            ("--search-final", SearchType::Final),
            ("--search-all", SearchType::Star),
            ("--search-one-step", SearchType::One),
            ("--search-one-or-more-steps", SearchType::Plus),
        ] {
            let options = parse_krun_pattern_options(&["--pattern", "<k> X </k>", flag])
                .unwrap_or_else(|error| panic!("{flag}: {error}"));
            assert_eq!(options.surface_pattern.as_deref(), Some("<k> X </k>"));
            assert_eq!(options.search.unwrap().search_type, expected);
        }
    }

    #[test]
    fn krun_rejects_surface_and_kore_file_targets_together() {
        let error = parse_krun_pattern_options(&[
            "--search-final",
            "--pattern",
            "<k> X </k>",
            "--search-pattern",
            "target.kore",
        ])
        .unwrap_err();

        assert_eq!(error.kind(), clap::error::ErrorKind::ArgumentConflict);

        let reverse_error = parse_krun_pattern_options(&[
            "--search-final",
            "--search-pattern",
            "target.kore",
            "--pattern",
            "<k> X </k>",
        ])
        .unwrap_err();

        assert_eq!(
            reverse_error.kind(),
            clap::error::ErrorKind::ArgumentConflict
        );
    }

    #[test]
    fn krun_rejects_repeated_surface_pattern() {
        let error =
            parse_krun_pattern_options(&["--pattern", "<k> X </k>", "--pattern", "<k> Y </k>"])
                .unwrap_err();

        assert_eq!(error.kind(), clap::error::ErrorKind::ArgumentConflict);
    }

    #[test]
    fn krun_accepts_hyphen_leading_surface_text_as_one_value() {
        let options = parse_krun_pattern_options(&["--pattern", "-1 => X"]).unwrap();

        assert_eq!(options.surface_pattern.as_deref(), Some("-1 => X"));
    }

    fn compiled_pattern_for_selection() -> k_rust::kompile::CompiledSearchPattern {
        k_rust::kompile::CompiledSearchPattern {
            pattern: KorePattern::Top {
                sort: kore_sort("SortGeneratedTopCell"),
            },
            generated_anonymous_variables: BTreeSet::new(),
        }
    }

    #[test]
    fn match_target_selects_all_source_rows() {
        assert!(select_match_target_source(None, None).is_none());
        assert!(matches!(
            select_match_target_source(None, Some(compiled_pattern_for_selection())),
            Some(MatchTargetSource::Surface(_))
        ));

        let default_search = SearchRunOptions {
            search_type: SearchType::Final,
            pattern: None,
            bound: None,
        };
        assert!(select_match_target_source(Some(&default_search), None).is_none());

        let file_search = SearchRunOptions {
            search_type: SearchType::Final,
            pattern: Some("target.kore".into()),
            bound: None,
        };
        assert!(matches!(
            select_match_target_source(Some(&file_search), None),
            Some(MatchTargetSource::KoreFile(path)) if path == Path::new("target.kore")
        ));
        assert!(matches!(
            select_match_target_source(
                Some(&default_search),
                Some(compiled_pattern_for_selection())
            ),
            Some(MatchTargetSource::Surface(_))
        ));
    }

    fn backend_pattern_with_candidates(term: Variable, constraints: Vec<Predicate>) -> Pattern {
        Pattern {
            term: Term::variable(term),
            constraints,
        }
    }

    #[test]
    fn generated_identity_mapping_uses_the_actual_sorted_element_variable() {
        let variable = Variable::new("VarGenerated", BackendSort::simple("SortInt"));
        let target = backend_pattern_with_candidates(variable.clone(), Vec::new());
        let identities = BTreeSet::from([k_rust::kompile::KoreVariableIdentity::element(
            "VarGenerated",
        )]);

        assert_eq!(
            map_generated_anonymous_variables(&target, &identities).unwrap(),
            BTreeSet::from([variable])
        );
    }

    #[test]
    fn generated_identity_mapping_keeps_set_and_element_variables_distinct() {
        let element = Variable::new("@VarGenerated", BackendSort::simple("SortInt"));
        let set = Variable {
            kind: k_rust_backend::term::VariableKind::Set,
            sort: BackendSort::simple("SortInt"),
            name: "@VarGenerated".into(),
        };
        let target = backend_pattern_with_candidates(
            element,
            vec![Predicate::Term(Term::variable(set.clone()))],
        );
        let identities =
            BTreeSet::from([k_rust::kompile::KoreVariableIdentity::set("@VarGenerated")]);

        assert_eq!(
            map_generated_anonymous_variables(&target, &identities).unwrap(),
            BTreeSet::from([set])
        );
    }

    #[test]
    fn generated_identity_mapping_rejects_authored_gen_lookalikes() {
        let authored = Variable::new("Var'Unds'Gen0", BackendSort::simple("SortInt"));
        let generated = Variable::new("Var'Unds'Gen1", BackendSort::simple("SortInt"));
        let target = backend_pattern_with_candidates(
            authored,
            vec![Predicate::Term(Term::variable(generated.clone()))],
        );
        let identities = BTreeSet::from([k_rust::kompile::KoreVariableIdentity::element(
            "Var'Unds'Gen1",
        )]);

        assert_eq!(
            map_generated_anonymous_variables(&target, &identities).unwrap(),
            BTreeSet::from([generated])
        );
    }

    #[test]
    fn generated_identity_mapping_rejects_a_missing_identity() {
        let target = backend_pattern_with_candidates(
            Variable::new("VarPresent", BackendSort::simple("SortInt")),
            Vec::new(),
        );
        let missing = k_rust::kompile::KoreVariableIdentity::element("VarMissing");
        let error = map_generated_anonymous_variables(&target, &BTreeSet::from([missing.clone()]))
            .unwrap_err();

        assert_eq!(
            error,
            GeneratedIdentityMappingError::Missing { identity: missing }
        );
    }

    #[test]
    fn generated_identity_mapping_rejects_ambiguous_sorts() {
        let first = Variable::new("VarGenerated", BackendSort::simple("SortInt"));
        let second = Variable::new("VarGenerated", BackendSort::simple("SortBool"));
        let target = backend_pattern_with_candidates(
            first.clone(),
            vec![Predicate::Term(Term::variable(second.clone()))],
        );
        let identity = k_rust::kompile::KoreVariableIdentity::element("VarGenerated");
        let error = map_generated_anonymous_variables(&target, &BTreeSet::from([identity.clone()]))
            .unwrap_err();

        assert_eq!(
            error,
            GeneratedIdentityMappingError::Ambiguous {
                identity,
                candidates: BTreeSet::from([first, second]),
            }
        );
    }

    #[test]
    fn generated_identity_mapping_accepts_empty_and_bound_only_sets() {
        let binder = Variable::new("VarBound", BackendSort::simple("SortInt"));
        let target = backend_pattern_with_candidates(
            Variable::new("VarTerm", BackendSort::simple("SortInt")),
            vec![Predicate::Exists(binder.clone(), Box::new(Predicate::True))],
        );

        assert_eq!(
            map_generated_anonymous_variables(&target, &BTreeSet::new()).unwrap(),
            BTreeSet::new()
        );
        assert_eq!(
            map_generated_anonymous_variables(
                &target,
                &BTreeSet::from([k_rust::kompile::KoreVariableIdentity::element("VarBound")])
            )
            .unwrap(),
            BTreeSet::from([binder])
        );
    }

    #[test]
    fn command_line_match_metadata_covers_exact_multiline_contents() {
        let attributes = command_line_pattern_attributes("a\nbc");

        assert_eq!(attributes.source(), Some("<command line>"));
        assert_eq!(
            attributes.source_id(),
            Some(k_rust::provenance::SourceId(0))
        );
        assert_eq!(
            attributes.location(),
            Some(k_rust::definition::Location {
                start_line: 1,
                start_column: 1,
                end_line: 2,
                end_column: 3,
            })
        );
        assert_eq!(
            attributes.get("contentStartOffset"),
            Some(&serde_json::json!(0))
        );
        assert_eq!(
            attributes.get("contentStartLine"),
            Some(&serde_json::json!(1))
        );
        assert_eq!(
            attributes.get("contentStartColumn"),
            Some(&serde_json::json!(1))
        );
    }

    fn pattern01d_condition_output(
        substitution: Substitution,
        constraints: Vec<Predicate>,
        generated: BTreeSet<Variable>,
    ) -> KorePattern {
        pattern01d_condition_output_with_functions(
            substitution,
            constraints,
            generated,
            BTreeSet::from(["LbltestFunction".to_owned()]),
        )
    }

    fn pattern01d_condition_output_with_functions(
        substitution: Substitution,
        constraints: Vec<Predicate>,
        generated: BTreeSet<Variable>,
        function_symbols: BTreeSet<String>,
    ) -> KorePattern {
        let result_sort = kore_sort("SortGeneratedTopCell");
        let predicate_sort = BackendSort::simple("SortGeneratedTopCell");
        let condition =
            raw_match_condition_output(&substitution, &constraints, &result_sort, &predicate_sort);
        filter_match_condition(condition, &result_sort, &generated, &function_symbols)
    }

    fn test_function(arguments: Vec<Term>) -> Term {
        let sort = BackendSort::simple("SortGeneratedTopCell");
        let mut attributes = SymbolAttributes::constructor();
        attributes.symbol_type = SymbolType::Function(FunctionType::Total);
        Term::application(
            std::sync::Arc::new(Symbol {
                name: "LbltestFunction".into(),
                sort_variables: Vec::new(),
                argument_sorts: vec![sort.clone(); arguments.len()],
                result_sort: sort,
                attributes,
            }),
            Vec::new(),
            arguments,
        )
    }

    #[test]
    fn hidden_bindings_drop_a_one_use_generated_equality() {
        let variable = Variable::new("Var'Unds'Gen0", BackendSort::simple("SortInt"));
        let value = Term::domain_value(BackendSort::simple("SortInt"), "1");
        let output = pattern01d_condition_output(
            Substitution::from([(variable.clone(), value)]),
            Vec::new(),
            BTreeSet::from([variable]),
        );

        assert!(matches!(output, KorePattern::Top { .. }));
    }

    #[test]
    fn hidden_bindings_keep_named_and_authored_lookalikes() {
        for variable in [
            Variable::new("VarNamed", BackendSort::simple("SortInt")),
            Variable::new("Var'Unds'Gen0", BackendSort::simple("SortInt")),
        ] {
            let output = pattern01d_condition_output(
                Substitution::from([(
                    variable,
                    Term::domain_value(BackendSort::simple("SortInt"), "1"),
                )]),
                Vec::new(),
                BTreeSet::new(),
            );
            assert!(matches!(output, KorePattern::Equals { .. }), "{output:?}");
        }
    }

    #[test]
    fn hidden_bindings_count_the_whole_conjunction() {
        let variable = Variable::new("Var'Unds'Gen0", BackendSort::simple("SortGeneratedTopCell"));
        let output = pattern01d_condition_output(
            Substitution::from([(
                variable.clone(),
                Term::domain_value(BackendSort::simple("SortGeneratedTopCell"), "value"),
            )]),
            vec![Predicate::Term(Term::variable(variable.clone()))],
            BTreeSet::from([variable]),
        );

        assert!(matches!(output, KorePattern::And { .. }), "{output:?}");
    }

    #[test]
    fn hidden_bindings_drop_only_eligible_function_equalities() {
        let sort = BackendSort::simple("SortGeneratedTopCell");
        let variable = Variable::new("Var'Unds'Gen0", sort.clone());
        let value = Term::domain_value(sort.clone(), "value");
        let one_use = Predicate::Equals(
            test_function(vec![Term::variable(variable.clone())]),
            value.clone(),
        );
        assert!(matches!(
            pattern01d_condition_output(
                Substitution::new(),
                vec![one_use],
                BTreeSet::from([variable.clone()])
            ),
            KorePattern::Top { .. }
        ));

        let repeated = Predicate::Equals(
            test_function(vec![
                Term::variable(variable.clone()),
                Term::variable(variable.clone()),
            ]),
            value.clone(),
        );
        assert!(matches!(
            pattern01d_condition_output(
                Substitution::new(),
                vec![repeated],
                BTreeSet::from([variable])
            ),
            KorePattern::Equals { .. }
        ));

        let ground = Predicate::Equals(test_function(Vec::new()), value);
        assert!(matches!(
            pattern01d_condition_output(Substitution::new(), vec![ground], BTreeSet::new()),
            KorePattern::Top { .. }
        ));

        let functional_only = Predicate::Equals(
            test_function(Vec::new()),
            Term::domain_value(BackendSort::simple("SortGeneratedTopCell"), "value"),
        );
        assert!(matches!(
            pattern01d_condition_output_with_functions(
                Substitution::new(),
                vec![functional_only],
                BTreeSet::new(),
                BTreeSet::new(),
            ),
            KorePattern::Equals { .. }
        ));
    }

    #[test]
    fn hidden_bindings_flatten_only_selected_conjunctions() {
        let variable = Variable::new("Var'Unds'Gen0", BackendSort::simple("SortInt"));
        let equality = Predicate::Equals(
            Term::variable(variable.clone()),
            Term::domain_value(BackendSort::simple("SortInt"), "1"),
        );
        assert!(matches!(
            pattern01d_condition_output(
                Substitution::new(),
                vec![Predicate::And(vec![equality.clone()])],
                BTreeSet::from([variable.clone()]),
            ),
            KorePattern::Top { .. }
        ));
        assert!(matches!(
            pattern01d_condition_output(
                Substitution::new(),
                vec![Predicate::Not(Box::new(equality))],
                BTreeSet::from([variable]),
            ),
            KorePattern::Not { .. }
        ));
    }

    #[test]
    fn hidden_bindings_count_binders_and_bodies() {
        let variable = Variable::new("Var'Unds'Gen0", BackendSort::simple("SortInt"));
        let output = pattern01d_condition_output(
            Substitution::from([(
                variable.clone(),
                Term::domain_value(BackendSort::simple("SortInt"), "1"),
            )]),
            vec![Predicate::Exists(
                variable.clone(),
                Box::new(Predicate::Term(Term::variable(variable.clone()))),
            )],
            BTreeSet::from([variable]),
        );

        assert!(matches!(output, KorePattern::And { .. }), "{output:?}");
    }

    #[test]
    fn hidden_bindings_filter_after_boolean_orientation() {
        let sort = BackendSort::simple("SortBool");
        let variable = Variable::new("Var'Unds'Gen0", sort.clone());
        let mut attributes = SymbolAttributes::constructor();
        attributes.symbol_type = SymbolType::Function(FunctionType::Total);
        let function = Term::application(
            std::sync::Arc::new(Symbol {
                name: "LbltestFunction".into(),
                sort_variables: Vec::new(),
                argument_sorts: vec![sort.clone()],
                result_sort: sort.clone(),
                attributes,
            }),
            Vec::new(),
            vec![Term::variable(variable.clone())],
        );
        let output = pattern01d_condition_output(
            Substitution::new(),
            vec![Predicate::Equals(
                function,
                Term::domain_value(sort, "true"),
            )],
            BTreeSet::from([variable]),
        );

        let KorePattern::Equals { left, .. } = &output else {
            panic!("expected the externally oriented equality to remain")
        };
        assert!(matches!(left.as_ref(), KorePattern::DomainValue { .. }));
    }

    #[test]
    fn hidden_bindings_distinguish_element_and_set_variables() {
        let set = Variable {
            kind: BackendVariableKind::Set,
            sort: BackendSort::simple("SortInt"),
            name: "@Var'Unds'Gen0".into(),
        };
        let output = pattern01d_condition_output(
            Substitution::from([(
                set.clone(),
                Term::domain_value(BackendSort::simple("SortInt"), "1"),
            )]),
            Vec::new(),
            BTreeSet::from([set]),
        );

        assert!(matches!(output, KorePattern::Top { .. }));
    }

    #[test]
    fn hidden_bindings_use_exact_function_markers() {
        let definition = parse_kore_definition(
            r#"[]
            module M
              sort S{} []
              symbol exact{}() : S{} [function{}()]
              symbol functionalOnly{}() : S{} [functional{}()]
              symbol totalOnly{}() : S{} [total{}()]
              symbol constructor{}() : S{} [constructor{}()]
            endmodule []"#,
        )
        .unwrap();

        let backend = BackendDefinition::internalize(&definition, "M").unwrap();
        assert_eq!(
            backend.function_symbol_names(),
            BTreeSet::from(["exact".to_owned()])
        );
    }

    #[test]
    fn hidden_bindings_deduplicate_filtered_disjuncts() {
        let sort = kore_sort("SortGeneratedTopCell");
        let duplicate = KorePattern::Top { sort: sort.clone() };

        assert_eq!(
            order_distinct_match_outputs(vec![duplicate.clone(), duplicate.clone()]),
            vec![duplicate]
        );
    }

    #[test]
    fn hidden_bindings_deduplicate_after_filtering() {
        let sort = BackendSort::simple("SortGeneratedTopCell");
        let first = Variable::new("Var'Unds'Gen0", sort.clone());
        let second = Variable::new("Var'Unds'Gen1", sort.clone());
        let value = Term::domain_value(sort.clone(), "value");
        let matches = [
            PatternMatch {
                substitution: Substitution::from([(first.clone(), value.clone())]),
                constraints: Vec::new(),
            },
            PatternMatch {
                substitution: Substitution::from([(second.clone(), value)]),
                constraints: Vec::new(),
            },
        ];
        let output = pattern_matches_output(
            &matches,
            &kore_sort("SortGeneratedTopCell"),
            &sort,
            &BTreeSet::from([first, second]),
            &BTreeSet::new(),
        );

        assert!(matches!(output, KorePattern::Top { .. }), "{output:?}");
    }

    #[test]
    fn hidden_bindings_flatten_and_deduplicate_disjuncts_across_matches() {
        let sort = BackendSort::simple("SortGeneratedTopCell");
        let variable = Variable::new("VarX", sort.clone());
        let generated = Variable::new("Var'Unds'Gen0", sort.clone());
        let first_value = Term::domain_value(sort.clone(), "first");
        let second_value = Term::domain_value(sort.clone(), "second");
        let first = Predicate::Equals(Term::variable(variable.clone()), first_value);
        let second = Predicate::Equals(Term::variable(variable), second_value);
        let generated_binding = Predicate::Equals(
            Term::variable(generated.clone()),
            Term::domain_value(sort.clone(), "generated"),
        );
        let matches = [
            PatternMatch {
                substitution: Substitution::new(),
                constraints: vec![Predicate::Or(vec![
                    Predicate::And(vec![generated_binding, first.clone()]),
                    second,
                ])],
            },
            PatternMatch {
                substitution: Substitution::new(),
                constraints: vec![first],
            },
        ];
        let result_sort = kore_sort("SortGeneratedTopCell");
        let output = pattern_matches_output(
            &matches,
            &result_sort,
            &sort,
            &BTreeSet::from([generated]),
            &BTreeSet::new(),
        );

        let disjuncts = output.disjuncts_at(&result_sort);
        assert_eq!(disjuncts.len(), 2, "{disjuncts:?}");
        assert!(
            disjuncts
                .iter()
                .all(|disjunct| !matches!(disjunct, KorePattern::Or { .. })),
            "{disjuncts:?}"
        );
    }

    #[test]
    fn resolves_unambiguous_short_claim_labels() {
        let labels = vec![
            "FIRST.alpha".to_owned(),
            "SECOND.beta".to_owned(),
            "exact".to_owned(),
        ];
        assert_eq!(
            resolve_claim_labels(&labels, &["alpha".into(), "exact".into()]).unwrap(),
            BTreeSet::from(["FIRST.alpha".into(), "exact".into()])
        );
    }

    #[test]
    fn rejects_ambiguous_short_claim_labels() {
        let labels = vec!["FIRST.same".to_owned(), "SECOND.same".to_owned()];
        let error = resolve_claim_labels(&labels, &["same".into()]).unwrap_err();
        assert!(error.to_string().contains("is ambiguous"), "{error}");
    }

    #[test]
    fn filter_claims_follows_k_filter_semantics() {
        let syntax = parse_kore_definition(
            r#"[]
            module SPEC
                sort SortS{} []
                symbol a{}() : SortS{} [constructor{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                claim{} \implies{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()),
                    weakAlwaysFinally{SortS{}}(a{}())
                ) [label{}("SPEC.x")]
                claim{} \implies{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()),
                    weakAlwaysFinally{SortS{}}(a{}())
                ) [label{}("SPEC.y")]
                claim{} \implies{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()),
                    weakAlwaysFinally{SortS{}}(a{}())
                ) [label{}("SPEC.z")]
                claim{} \implies{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()),
                    weakAlwaysFinally{SortS{}}(a{}())
                ) [UNIQUE'Unds'ID{}("unlabelled")]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "SPEC").unwrap();

        let kept = filter_claims(
            &definition.reachability_claims,
            &ClaimFilter {
                selected: vec!["x".into()],
                excluded: vec!["y".into()],
                trusted: vec!["x".into(), "z".into()],
            },
        )
        .unwrap();
        assert_eq!(kept.len(), 2);
        assert_eq!(kept[0].attributes.label.as_deref(), Some("SPEC.x"));
        assert!(kept[0].attributes.trusted);
        assert_eq!(kept[1].attributes.label, None);
        assert!(!kept[1].attributes.trusted);

        for filter in [
            ClaimFilter {
                selected: vec!["missing".into()],
                ..ClaimFilter::default()
            },
            ClaimFilter {
                excluded: vec!["missing".into()],
                ..ClaimFilter::default()
            },
            ClaimFilter {
                trusted: vec!["missing".into()],
                ..ClaimFilter::default()
            },
        ] {
            let error = filter_claims(&definition.reachability_claims, &filter).unwrap_err();
            assert!(
                error
                    .to_string()
                    .contains("no modal reachability claim has label `missing`"),
                "{error}"
            );
        }

        let error = filter_claims(
            &definition.reachability_claims,
            &ClaimFilter {
                selected: vec!["x".into()],
                excluded: vec!["SPEC.x".into()],
                ..ClaimFilter::default()
            },
        )
        .unwrap_err();
        assert!(error.to_string().contains("used for both"), "{error}");
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
    fn kore_simplify_discharges_constraints_valid_under_smt_lemmas() {
        let syntax = parse_kore_definition(
            r#"[]
            module MAIN
              hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
              hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
              hooked-sort SortList{} [hook{}("LIST.List")]
              sort SortCell{} []
              symbol holder{}(SortList{}) : SortCell{}
                [constructor{}(), functional{}(), injective{}()]
              hooked-symbol size{}(SortList{}) : SortInt{}
                [function{}(), total{}(), hook{}("LIST.size"), smtlib{}("smt_seq_len")]
              hooked-symbol gte{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), hook{}("INT.ge"), smt-hook{}(">=")]
              axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortBool{}, R}(
                  gte{}(size{}(L:SortList{}), \dv{SortInt{}}("0")),
                  \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}())
                )
              ) [label{}("size-non-negative"), simplification{}(), smt-lemma{}()]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let constrained = |bound: &str| {
            parse_kore_pattern(&format!(
                r#"\and{{SortCell{{}}}}(
                    holder{{}}(Var'Ques'L:SortList{{}}),
                    \equals{{SortBool{{}}, SortCell{{}}}}(
                        \dv{{SortBool{{}}}}("true"),
                        gte{{}}(size{{}}(Var'Ques'L:SortList{{}}), \dv{{SortInt{{}}}}("{bound}"))
                    )
                )"#
            ))
            .unwrap()
        };

        // The lemma `size(L) >=Int 0` makes `size(?L) >=Int -1` valid: the constraint disappears.
        assert_eq!(
            simplify_kore_pattern(&definition, &constrained("-1")).unwrap(),
            parse_kore_pattern("holder{}(Var'Ques'L:SortList{})").unwrap()
        );
        // Negative control: `size(?L) >=Int 1` is open and stays.
        assert_eq!(
            simplify_kore_pattern(&definition, &constrained("1")).unwrap(),
            constrained("1")
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

        let pattern = model_substitution(&substitution, &result_sort).unwrap();
        let KorePattern::And { arguments, .. } = &pattern else {
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
            externalize::natural_name_order("RuleVar_Gen2", "RuleVar_Gen10"),
            std::cmp::Ordering::Less
        );
        assert_eq!(
            externalize::natural_name_order("RuleVar_Gen02", "RuleVar_Gen2"),
            std::cmp::Ordering::Greater
        );
        assert_eq!(
            externalize::natural_name_order("RuleVar_A", "RuleVar_B"),
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
            "--max-simplification-iterations",
            "17",
        ])
        .unwrap();
        let Command::Krun(krun) = krun.command else {
            panic!("expected krun command");
        };
        let krun = KrunOptions::from(krun);
        assert_eq!(krun.syntax_module, None);
        assert_eq!(krun.io, None);
        assert_eq!(krun.depth, u64::MAX);
        assert_eq!(krun.max_simplification_iterations, 17);

        let kore_exec = Cli::try_parse_from([
            "krust",
            "kore-exec",
            "definition.kore",
            "--module",
            "MAIN",
            "--pattern",
            "program.kore",
            "--max-simplification-iterations",
            "19",
        ])
        .unwrap();
        let Command::KoreExec(kore_exec) = kore_exec.command else {
            panic!("expected kore-exec command");
        };
        assert_eq!(kore_exec.depth, None);
        assert_eq!(kore_exec.max_simplification_iterations, Some(19));
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
            "--exclude",
            "excluded",
            "--trusted",
            "trusted",
            "--depth",
            "42",
            "--max-simplification-iterations",
            "23",
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

        let KproveInput::Source(common) = &options.input else {
            panic!("expected source input");
        };
        assert_eq!(common.definition, Path::new("spec.k"));
        assert_eq!(options.module, "SPEC");
        assert_eq!(options.definition_module, "SEMANTICS");
        assert_eq!(options.claims, ["first", "second"]);
        assert_eq!(options.excluded_claims, ["excluded"]);
        assert_eq!(options.trusted_claims, ["trusted"]);
        assert_eq!(options.depth, 42);
        assert_eq!(options.max_simplification_iterations, 23);
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
    fn parses_kprove_prepared_definition_and_specification_options() {
        let cli = Cli::try_parse_from([
            "krust",
            "kprove",
            "--compiled-definition",
            "spec-kompiled",
            "--main-module",
            "SPEC",
            "--load-only",
        ])
        .unwrap();
        let Command::Kprove(options) = cli.command else {
            panic!("expected kprove command");
        };
        let options = KproveOptions::from(options);
        let KproveInput::Compiled(path) = options.input else {
            panic!("expected compiled input");
        };
        assert_eq!(path, Path::new("spec-kompiled"));
        assert_eq!(options.module, "SPEC");
        assert!(options.load_only);

        let cli = Cli::try_parse_from([
            "krust",
            "kprove",
            "spec.k",
            "--compiled-definition",
            "semantics-kompiled",
            "--main-module",
            "SPEC",
        ])
        .unwrap();
        let Command::Kprove(options) = cli.command else {
            panic!("expected kprove command");
        };
        let options = KproveOptions::from(options);
        let KproveInput::SourceWithCompiled { source, compiled } = options.input else {
            panic!("expected source plus compiled input");
        };
        assert_eq!(source.definition, Path::new("spec.k"));
        assert_eq!(compiled, Path::new("semantics-kompiled"));
        assert!(
            Cli::try_parse_from([
                "krust",
                "kprove",
                "spec.k",
                "--main-module",
                "SPEC",
                "--load-only",
            ])
            .is_err()
        );
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
