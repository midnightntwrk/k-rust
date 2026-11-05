//! Cargo-style command-line frontend for the KRS definition compiler.

use krs_cli::{
    Backend, ColorChoice, Command, CommandKind, CommandRequest, DiagnosticSources, FacetSelector,
    KrsCfg, MessageFormat, PackageSelector, ParseRequest, ProgramSource, ProveRequest,
    RegistrationMode, RunRequest, SearchMode, SearchRequest, StopCriterion, StopRules, TermOutput,
    execute_command_reported, supervise_prove, valid_identifier_segment,
};
use krs_fmt::{Edition, FormatOptions, TrailingCommentStyle};
use krs_ir::measure::Measurement;
use lexopt::Arg::{Long, Short, Value};
use std::ffi::OsString;
use std::fmt;
use std::io::{self, IsTerminal, Read, Write};
use std::num::NonZeroU64;
use std::path::{Path, PathBuf};

const USAGE: &str = "\
KRS definition compiler

Usage:
  krs <check|expand|emit-k|build> --package PACKAGE --definition NAME [OPTIONS]
  krs parse  --package P --definition D [--sort SORT] [--output kast|program|json|kore] [FILE|-]
  krs run    --package P --definition D [FILE|-] [--case FILE] [--input NAME=JSON]...
             [-c NAME=TEXT]... [--depth N] [--stop-before NAME]... [--stop-after NAME]...
             [--stop-count N] [--trace] [--coverage]
             [--output pretty|kast|json|kore|none] [--color auto|always|never]
  krs search --package P --definition D [FILE|-] [--case FILE] [--input NAME=JSON]...
             [-c NAME=TEXT]... [--mode final|all|one-step|one-or-more-steps] [--depth N]
             [--max-solutions N] [--trace] [--output pretty|kast|json|kore]
             [--color auto|always|never]
  krs prove  --package P --definition D [--spec-module NAME] [--claim LABEL]... [--depth N]
             [--output pretty|kast|json|jsonl|kore] [--color auto|always|never]
  krs kink <emit|check|results|run|report|query|fuzz> --package P --definition D [OPTIONS]
             (krs kink --help lists the corpus loop's options)
  krs fmt [--check] [--manifest-path PATH] [PATH ...]
  krs fmt --stdin [--edition YEAR]

Commands:
  check                     Judge the definition as emit-k, build, and the run commands do;
                            write nothing
  expand                    Print the selected Rust reference surface: the one changed module
                            file on stdout, or with --output each changed file at its path
  emit-k                    Emit canonical K with its symbol and source maps (definition.k,
                            spec.k when there are claims, symbols.json, sources.json)
  build                     Compile native backend artifacts
  parse                     Parse a program with the definition's grammar (kast)
  run                       Run a program on one path (krun)
  search                    Return the set of reachable final states (krun --search)
  prove                     Prove the definition's claims (kprove)
  kink                      The corpus loop over the package's kink/ corpus: results and
                            coverage per case, mutations killed or survived, query and fuzz
  fmt                       Format Rust and KRS rules! bodies using the package's facade aliases

Options:
  --manifest-path PATH       Cargo manifest (default: Cargo.toml)
  --package PACKAGE          Root Cargo package name
  --package-id ID            Exact root Cargo package ID
  --definition NAME          Root package definition facet
  --dependency PACKAGE:NAME  Composed dependency facet; repeatable
  --cfg KEY[=VALUE]          KRS rustc cfg; repeatable
  --backend llvm|haskell     Native target dialect (default: llvm); with check, judge only
                             that backend's route (default: every route)
  --output DIRECTORY         Required for emit-k and build; with expand, an absent or empty
                             directory for the changed module files, whose paths stdout lists
  --output FORMAT            Result format: pretty (default of run, search, prove), program (parse), kast (default of parse), json, jsonl (prove), kore, none (run)
  FILE|-                     With run and search, bind the main parameter: the file's bytes
                             when its type is exactly Bytes, else its text, parsed at its sort
  --case FILE                Bind the inputs a case document (.toml or .json) gives by
                             parameter name; its file paths are relative to FILE's directory
  --input NAME=JSON          Bind input NAME to a JSON document of the typed encoding; file
                             paths are relative to the working directory; repeatable
  -c NAME=TEXT               Bind configuration variable NAME ($ENV, ENV, or init parameter env); repeatable
  --depth N                  At most N rewrite steps
  --stop-before NAME         With run, end before a step by a rule of NAME: a KRS item by
                             its Rust path (`crate::ppu::frame_end`, or `lang::tick` in the
                             dependency crate `lang`), whose every rewrite rule it names, or a
                             K label (exact or unique suffix); repeatable
  --stop-after NAME          With run, end after a step by a rule of NAME; repeatable
  --stop-count N             With run, end at the Nth stop, resuming past the earlier ones
                             (default: 1); needs --stop-before or --stop-after
  --trace                    Print each rewrite step with its rule and source
  --coverage                 With run, list the rules and equations the run matched, applied
                             and committed, with their sources (--output json: the report's
                             `coverage`)
  --mode MODE                Search mode (default: final)
  --max-solutions N          Stop search after N solutions
  --spec-module NAME         Prove the claims of this author spec module (default: the generated <MAIN>-SPEC)
  --claim LABEL              Prove only this claim (exact label or unique suffix); repeatable
  --sort SORT                Parse at SORT (default: the sort of the main parameter)
  --color WHEN               Colour pretty output (auto, always, never)
  --timings FILE             Write krs-timings/1 phase timings as JSON
  --counters FILE            Write krs-counters/1 work counters as JSON
  --message-format human|json Diagnostic output (default: human)
  --profile standard|strict  Raw K profile for every package (default: each package's `profile`)
  --no-reuse                 Run the collector and compiler even on an unchanged input
  --partition                With check, print each package's program-syntax partition
  --ir                       With emit-k, also write descriptor-bundle.json, semantic-ir.json,
                             and definition-ir.json
  --stdin                    Format stdin with facade alias k and write the result to stdout
  --edition YEAR             Rust edition for --stdin (default: 2024)
  --check                    Report files that are not canonically formatted
  --trailing-comments STYLE  aligned or gutter (default: aligned)
  -h, --help                 Show this help
";

/// `krs kink --help`.
#[cfg(feature = "kink")]
const KINK_USAGE: &str = "\
krs kink: the corpus loop over a KRS package, with kink as its engine

Usage:
  krs kink emit    --package P --definition D [--check]
  krs kink check   --package P --definition D [--mutations PATH] [--locked]
  krs kink results --package P --definition D [--verify] [--mutations PATH] [--cache DIR]
                   [--output json|verdicts] [--locked]
  krs kink run     --package P --definition D [--mutations PATH] [--only ID]... [--verify]
                   [--order cost|corpus] [--full] [--compile-workers N] [--no-memo]
                   [--cache DIR] [--output json|verdicts] [--locked]
  krs kink report  --package P --definition D [--cache DIR] [--output json|verdicts]
  krs kink query   --package P --definition D [--patterns PATH] [--only ID]... [--verify]
                   [--cache DIR] [--locked]
  krs kink fuzz    --package P --definition D [--templates PATH] --template ID
                   (--kill MUTATION | --matched RULE | --fired RULE | --pattern ID) [kink-flow's
                   fuzz options] [--locked]

The corpus is <package>/kink (or --corpus DIR):
  FLOW.toml         [spec] krs = { definition = \"D\" }, [budget], and the cases, as
                    kink-flow's manifest; a case's paths stay inside the corpus directory
  cases/            the cases' program files and typed-input documents; a program file
                    binds the main parameter, as krs run FILE does
  mutations/        <topic>.toml mutation lists, K patches anchored by `rule = <label or
                    suffix>` (else MUTATIONS.toml)
  PATTERNS.toml     patterns of interest, for query
  TEMPLATES.toml    case templates with holes, for fuzz
  definition.k      the package's emitted K, which kink judges; written by krs kink
  .kink-flow/       kink-flow's caches

Every verb but emit and report builds the package, writes kink/definition.k when it differs
from the emission (the document's `definition.status` says `written`), and runs kink-flow's
verb on it; every rule a document names gains `krs = {item, package, file, line, column,
kind, claim_helper}`. --locked refuses a stale definition.k instead of writing it, and
emit --check exits 1 when it is stale: the gate a CI runs. report builds nothing: it prints
the last run's stored document (or its verdicts) as that run printed it, and takes no
--locked.

Exit status: 0, 1 when anything is refused (the document says what and why), 2 on a usage
error. The selection options (--manifest-path, --package, --package-id, --definition,
--dependency, --cfg, --profile, --registration, --message-format, --timings, --counters)
are krs's, before or after the verb; every other option is the kink-flow verb's own. Every
command that builds the package builds it in process, so krs kink takes no --no-reuse.
";

fn main() {
    let arguments: Vec<OsString> = std::env::args_os().skip(1).collect();
    match parse(arguments.clone()) {
        Ok(ParseResult::Help) => print!("{USAGE}"),
        Ok(ParseResult::Format(request)) => match execute_format(&request) {
            Ok(true) => {}
            Ok(false) => std::process::exit(1),
            Err(error) => {
                eprintln!("krs fmt: {error}");
                std::process::exit(1);
            }
        },
        #[cfg(feature = "kink")]
        Ok(ParseResult::KinkHelp) => print!("{KINK_USAGE}"),
        #[cfg(feature = "kink")]
        Ok(ParseResult::Kink(request, measure)) => {
            let status = execute_kink(&request, &measure);
            if status != 0 {
                std::process::exit(status);
            }
        }
        // `krs prove` proves its claims in supervised worker processes, which do the measuring.
        Ok(ParseResult::Run(request, _)) if matches!(&request.command, Command::Prove(prove) if !prove.worker) =>
        {
            let Command::Prove(prove) = &request.command else {
                unreachable!("the guard matched a prove command")
            };
            let status = supervise_prove(&arguments, prove);
            if status != 0 {
                std::process::exit(status);
            }
        }
        Ok(ParseResult::Run(request, measure)) => {
            if matches!(&request.command, Command::Prove(prove) if prove.worker) {
                krs_cli::watch_supervisor();
            }
            let mut measurement =
                Measurement::new(measure.timings.is_some(), measure.counters.is_some());
            let (result, sources) = execute_command_reported(&request, &mut measurement);
            let measured = write_measurement(
                &measure,
                &measurement,
                request.command.kind().as_str(),
                result.is_ok(),
            );
            let status = report_outcome(result, request.message_format, &sources);
            if status != 0 {
                std::process::exit(status);
            }
            if !measured {
                std::process::exit(1);
            }
        }
        #[cfg(feature = "kink")]
        Err(UsageError::Kink(message)) => {
            eprintln!("krs kink: {message}\n\n{KINK_USAGE}");
            std::process::exit(2);
        }
        Err(error) => {
            eprintln!("krs: {error}\n\n{USAGE}");
            std::process::exit(2);
        }
    }
}

/// Run `krs kink`: krs's warnings and refusal on stderr, then the document on stdout, then the
/// command's notes on stderr; returns the exit status.
#[cfg(feature = "kink")]
fn execute_kink(request: &krs_cli::KinkRequest, measure: &MeasureOptions) -> i32 {
    let mut measurement = Measurement::new(measure.timings.is_some(), measure.counters.is_some());
    let outcome = krs_cli::execute_kink(request, &mut measurement);
    let measured = write_measurement(measure, &measurement, "kink", outcome.status == 0);
    report_diagnostics(
        &outcome.warnings.envelopes,
        request.message_format,
        &outcome.sources,
    );
    if let Some(error) = &outcome.error {
        report_error(error, request.message_format, &outcome.sources);
    }
    if let Err(error) = io::stdout().lock().write_all(&outcome.stdout) {
        eprintln!("krs: could not write stdout: {error}");
        return 1;
    }
    let _ = io::stdout().lock().flush();
    for note in &outcome.notes {
        eprintln!("{note}");
    }
    if outcome.status == krs_cli::kink::EXIT_USAGE {
        eprintln!("\n{KINK_USAGE}");
    }
    match outcome.status {
        0 if !measured => 1,
        status => i32::from(status),
    }
}

/// Measurement output paths requested on the command line.
#[derive(Default)]
struct MeasureOptions {
    timings: Option<PathBuf>,
    counters: Option<PathBuf>,
}

fn write_measurement(
    options: &MeasureOptions,
    measurement: &Measurement,
    command: &str,
    succeeded: bool,
) -> bool {
    let mut ok = true;
    let mut write = |path: &Path, bytes: serde_json::Result<Vec<u8>>| {
        let result = bytes
            .map_err(|error| error.to_string())
            .and_then(|mut bytes| {
                bytes.push(b'\n');
                std::fs::write(path, bytes).map_err(|error| error.to_string())
            });
        if let Err(error) = result {
            eprintln!("krs: could not write `{}`: {error}", path.display());
            ok = false;
        }
    };
    if let Some(path) = &options.timings {
        let document = measurement.timings.document(command, succeeded);
        write(path, serde_json::to_vec_pretty(&document));
    }
    if let Some(path) = &options.counters {
        let document = measurement.counters.document(command, succeeded);
        write(path, serde_json::to_vec_pretty(&document));
    }
    ok
}

/// Print a command outcome and return the process exit status.
///
/// A success exits with the outcome's status (0, or 1 for an inconclusive run, search, or proof);
/// a failure exits 2 for a usage error and 1 otherwise; a stdout failure exits 1.
fn report_outcome(
    result: Result<krs_cli::CommandOutcome, krs_cli::CommandError>,
    format: MessageFormat,
    sources: &DiagnosticSources,
) -> i32 {
    match result {
        Ok(outcome) => {
            report_diagnostics(&outcome.warnings().envelopes, format, sources);
            if let Err(error) = io::stdout().lock().write_all(outcome.stdout()) {
                eprintln!("krs: could not write stdout: {error}");
                return 1;
            }
            let _ = io::stdout().lock().flush();
            if let Err(error) = io::stderr().lock().write_all(outcome.stderr()) {
                eprintln!("krs: could not write stderr: {error}");
                return 1;
            }
            outcome.exit_code()
        }
        Err(error) => {
            report_error(&error, format, sources);
            error.exit_code()
        }
    }
}

/// Print a command's refusal: the warnings of the stages that completed first, as on success;
/// the error is the verdict and comes last.
fn report_error(error: &krs_cli::CommandError, format: MessageFormat, sources: &DiagnosticSources) {
    if let Some(warnings) = error.warnings() {
        report_diagnostics(&warnings.envelopes, format, sources);
    }
    if let Some(diagnostics) = error.diagnostics() {
        report_diagnostics(&diagnostics, format, sources);
    } else {
        eprintln!("krs: {error}");
    }
}

fn report_diagnostics(
    envelopes: &[krs_cli::DiagnosticEnvelope],
    format: MessageFormat,
    sources: &DiagnosticSources,
) {
    let color = io::stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none();
    if let Err(error) =
        write_diagnostics(&mut io::stderr().lock(), envelopes, format, sources, color)
    {
        eprintln!("krs: could not render diagnostic: {error}");
    }
}

/// Writes `envelopes`, the located ones first, each group in producer order.
fn write_diagnostics(
    writer: &mut impl Write,
    envelopes: &[krs_cli::DiagnosticEnvelope],
    format: MessageFormat,
    sources: &DiagnosticSources,
    color: bool,
) -> io::Result<()> {
    let (located, unlocated): (Vec<_>, Vec<_>) = envelopes
        .iter()
        .partition(|envelope| envelope.authored_range.is_some());
    for diagnostic in located.into_iter().chain(unlocated) {
        match format {
            MessageFormat::Json => writer.write_all(diagnostic.to_json_line()?.as_bytes())?,
            MessageFormat::Human => {
                writeln!(writer, "{}", sources.render_envelope(diagnostic, color))?;
            }
        }
    }
    Ok(())
}

enum ParseResult {
    Help,
    Format(FormatRequest),
    Run(Box<CommandRequest>, MeasureOptions),
    #[cfg(feature = "kink")]
    KinkHelp,
    #[cfg(feature = "kink")]
    Kink(Box<krs_cli::KinkRequest>, MeasureOptions),
}

struct FormatRequest {
    stdin: bool,
    edition: Edition,
    check: bool,
    manifest_path: Option<PathBuf>,
    paths: Vec<PathBuf>,
    trailing_comments: TrailingCommentStyle,
}

/// Options of the run-family commands (`parse`, `run`, `search`, `prove`), with the spelling of each given option.
#[derive(Default)]
struct ExecOptions {
    given: Vec<&'static str>,
    inputs: Vec<OsString>,
    case: Option<PathBuf>,
    typed: Vec<(String, String)>,
    variables: Vec<(String, String)>,
    depth: Option<u64>,
    stop: StopRules,
    stop_count: Option<NonZeroU64>,
    trace: bool,
    coverage: bool,
    mode: Option<SearchMode>,
    max_solutions: Option<usize>,
    claims: Vec<String>,
    /// `--worker-protocol` (hidden): prove for a supervising `krs prove`.
    worker: bool,
    /// `--worker-claim` (hidden): the claims a worker proves, exactly, instead of `--claim`'s.
    worker_claims: Vec<String>,
    /// `--worker-color` (hidden): whether a worker colours, as its supervisor resolved `--color`.
    worker_color: Option<ColorChoice>,
    spec_module: Option<String>,
    sort: Option<String>,
    color: Option<ColorChoice>,
}

impl ExecOptions {
    fn note(&mut self, option: &'static str) {
        if !self.given.contains(&option) {
            self.given.push(option);
        }
    }
}

#[derive(Default)]
struct RunOptions {
    exec: ExecOptions,
    manifest_path: Option<PathBuf>,
    package: Option<String>,
    package_id: Option<String>,
    definition: Option<String>,
    dependencies: Vec<FacetSelector>,
    cfg: Vec<KrsCfg>,
    backend: Option<Backend>,
    output: Option<PathBuf>,
    registration: Option<RegistrationMode>,
    no_reuse: bool,
    message_format: Option<MessageFormat>,
    measure: MeasureOptions,
    partition: bool,
    ir: bool,
    profile: Option<krs_ir::RawKProfile>,
}

#[derive(Debug)]
enum UsageError {
    Argument(lexopt::Error),
    Message(String),
    /// A usage error of `krs kink`, shown with its own usage.
    #[cfg(feature = "kink")]
    Kink(String),
}

impl fmt::Display for UsageError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Argument(error) => error.fmt(formatter),
            Self::Message(message) => message.fmt(formatter),
            #[cfg(feature = "kink")]
            Self::Kink(message) => message.fmt(formatter),
        }
    }
}

impl From<lexopt::Error> for UsageError {
    fn from(error: lexopt::Error) -> Self {
        Self::Argument(error)
    }
}

fn usage(message: impl Into<String>) -> UsageError {
    UsageError::Message(message.into())
}

fn set_once<T>(slot: &mut Option<T>, value: T, option: &str) -> Result<(), UsageError> {
    if slot.replace(value).is_some() {
        return Err(usage(format!("{option} specified more than once")));
    }
    Ok(())
}

fn option_value(parser: &mut lexopt::Parser, role: &str) -> Result<String, UsageError> {
    utf8(parser.value()?, role)
}

fn parse(arguments: Vec<OsString>) -> Result<ParseResult, UsageError> {
    let mut parser = lexopt::Parser::from_args(arguments);
    let command = match parser.next()? {
        Some(Short('h') | Long("help")) => return Ok(ParseResult::Help),
        Some(Value(value)) => utf8(value, "command")?,
        Some(argument) => return Err(argument.unexpected().into()),
        None => return Err(usage("missing command")),
    };
    if command == "fmt" {
        return parse_format(&mut parser);
    }
    if command == "kink" {
        #[cfg(feature = "kink")]
        return parse_kink(parser.raw_args()?.collect());
        #[cfg(not(feature = "kink"))]
        return Err(usage(
            "this krs was built without the `kink` feature, which `krs kink` needs",
        ));
    }
    let kind = match command.as_str() {
        "check" => CommandKind::Check,
        "expand" => CommandKind::Expand,
        "emit-k" => CommandKind::EmitK,
        "build" => CommandKind::Build,
        "parse" => CommandKind::Parse,
        "run" => CommandKind::Run,
        "search" => CommandKind::Search,
        "prove" => CommandKind::Prove,
        unknown => return Err(usage(format!("unknown command `{unknown}`"))),
    };
    parse_run(&mut parser, kind)
}

fn parse_run(parser: &mut lexopt::Parser, kind: CommandKind) -> Result<ParseResult, UsageError> {
    let mut options = RunOptions::default();
    while let Some(argument) = parser.next()? {
        match argument {
            Short('h') | Long("help") => return Ok(ParseResult::Help),
            Long("no-reuse") => options.no_reuse = true,
            Long("partition") if kind == CommandKind::Check => options.partition = true,
            Long("ir") if kind == CommandKind::EmitK => options.ir = true,
            Long("profile") => {
                let value = option_value(parser, "profile")?;
                let selected = krs_ir::RawKProfile::from_metadata(&value).ok_or_else(|| {
                    usage(format!(
                        "unknown profile `{value}`; expected standard or strict"
                    ))
                })?;
                set_once(&mut options.profile, selected, "--profile")?;
            }
            Long("message-format") => {
                let value = option_value(parser, "message format")?;
                let selected = match value.as_str() {
                    "human" => MessageFormat::Human,
                    "json" => MessageFormat::Json,
                    _ => return Err(usage(format!("unknown message format `{value}`"))),
                };
                set_once(&mut options.message_format, selected, "--message-format")?;
            }
            Long("manifest-path") => set_once(
                &mut options.manifest_path,
                PathBuf::from(option_value(parser, "manifest path")?),
                "--manifest-path",
            )?,
            Long("package") => set_once(
                &mut options.package,
                option_value(parser, "package")?,
                "--package",
            )?,
            Long("package-id") => set_once(
                &mut options.package_id,
                option_value(parser, "package ID")?,
                "--package-id",
            )?,
            Long("definition") => set_once(
                &mut options.definition,
                option_value(parser, "definition")?,
                "--definition",
            )?,
            Long("dependency") => options
                .dependencies
                .push(parse_dependency(parser.value()?)?),
            Long("cfg") => options.cfg.push(parse_cfg(parser.value()?)?),
            Long("backend") => {
                let value = option_value(parser, "backend")?;
                let selected = Backend::ALL
                    .into_iter()
                    .find(|backend| backend.as_str() == value)
                    .ok_or_else(|| usage(format!("unknown backend `{value}`")))?;
                set_once(&mut options.backend, selected, "--backend")?;
            }
            Long("output") => set_once(
                &mut options.output,
                PathBuf::from(option_value(parser, "output")?),
                "--output",
            )?,
            Long("timings") => set_once(
                &mut options.measure.timings,
                PathBuf::from(option_value(parser, "timings")?),
                "--timings",
            )?,
            Long("counters") => set_once(
                &mut options.measure.counters,
                PathBuf::from(option_value(parser, "counters")?),
                "--counters",
            )?,
            Long("registration") => {
                let value = option_value(parser, "registration")?;
                let selected = match value.as_str() {
                    "inventory" => RegistrationMode::Inventory,
                    "explicit" => RegistrationMode::Explicit,
                    _ => return Err(usage(format!("unknown registration mode `{value}`"))),
                };
                set_once(&mut options.registration, selected, "--registration")?;
            }
            Short('c') => exec_option(parser, &mut options.exec, "-c")?,
            Long(name) if EXEC_LONG_OPTIONS.contains(&name) => {
                let option = EXEC_LONG_OPTIONS
                    .iter()
                    .find(|option| **option == name)
                    .copied()
                    .expect("guard matched a run option");
                exec_option(parser, &mut options.exec, option)?;
            }
            Value(value) => {
                options.exec.note("FILE");
                options.exec.inputs.push(value);
            }
            _ => return Err(argument.unexpected().into()),
        }
    }
    finish_run(kind, options)
}

/// The options between a supervising `krs prove` and its workers, which the usage does not show.
#[cfg(test)]
const HIDDEN_OPTIONS: [&str; 3] = ["--worker-protocol", "--worker-claim", "--worker-color"];

/// Long options of the run-family commands, without their leading dashes.
const EXEC_LONG_OPTIONS: [&str; 17] = [
    "case",
    "input",
    "depth",
    "stop-before",
    "stop-after",
    "stop-count",
    "max-solutions",
    "mode",
    "trace",
    "coverage",
    "claim",
    "spec-module",
    "sort",
    "color",
    "worker-protocol",
    "worker-claim",
    "worker-color",
];

/// Parse one run-family option (`-c` or a member of [`EXEC_LONG_OPTIONS`]).
fn exec_option(
    parser: &mut lexopt::Parser,
    exec: &mut ExecOptions,
    option: &'static str,
) -> Result<(), UsageError> {
    match option {
        "-c" => {
            exec.note("-c");
            let value = option_value(parser, "configuration variable")?;
            let (name, text) = value
                .split_once('=')
                .ok_or_else(|| usage(format!("-c `{value}` must have the form NAME=TEXT")))?;
            if name.trim_start_matches('$').is_empty() {
                return Err(usage(format!("-c `{value}` has an empty variable name")));
            }
            exec.variables.push((name.to_owned(), text.to_owned()));
        }
        "case" => {
            exec.note("--case");
            let path = case_path(option_value(parser, "case file")?)?;
            set_once(&mut exec.case, path, "--case")?;
        }
        "input" => {
            exec.note("--input");
            exec.typed
                .push(typed_input(&option_value(parser, "input")?)?);
        }
        "depth" => {
            exec.note("--depth");
            let value = option_value(parser, "depth")?;
            let depth = value
                .parse::<u64>()
                .map_err(|_| usage(format!("--depth `{value}` is not a non-negative integer")))?;
            set_once(&mut exec.depth, depth, "--depth")?;
        }
        "stop-before" | "stop-after" | "stop-count" => stop_option(parser, exec, option)?,
        "max-solutions" => {
            exec.note("--max-solutions");
            let value = option_value(parser, "maximum solution count")?;
            let limit = value.parse::<usize>().map_err(|_| {
                usage(format!(
                    "--max-solutions `{value}` is not a non-negative integer"
                ))
            })?;
            set_once(&mut exec.max_solutions, limit, "--max-solutions")?;
        }
        "mode" => {
            exec.note("--mode");
            let value = option_value(parser, "search mode")?;
            let mode = SearchMode::ALL
                .into_iter()
                .find(|mode| mode.as_str() == value)
                .ok_or_else(|| usage(format!("unknown search mode `{value}`")))?;
            set_once(&mut exec.mode, mode, "--mode")?;
        }
        "trace" => {
            exec.note("--trace");
            exec.trace = true;
        }
        "coverage" => {
            exec.note("--coverage");
            exec.coverage = true;
        }
        "claim" => {
            exec.note("--claim");
            exec.claims.push(option_value(parser, "claim label")?);
        }
        "worker-protocol" | "worker-claim" | "worker-color" => {
            worker_option(parser, exec, option)?;
        }
        "spec-module" => {
            exec.note("--spec-module");
            let module = option_value(parser, "spec module")?;
            set_once(&mut exec.spec_module, module, "--spec-module")?;
        }
        "sort" => {
            exec.note("--sort");
            let sort = option_value(parser, "sort")?;
            set_once(&mut exec.sort, sort, "--sort")?;
        }
        "color" => {
            exec.note("--color");
            let value = option_value(parser, "color")?;
            let color = match value.as_str() {
                "auto" => ColorChoice::Auto,
                "always" => ColorChoice::Always,
                "never" => ColorChoice::Never,
                _ => return Err(usage(format!("unknown color choice `{value}`"))),
            };
            set_once(&mut exec.color, color, "--color")?;
        }
        _ => unreachable!("exec_option is called only for run options"),
    }
    Ok(())
}

/// Parse one of the stop options of `krs run`.
fn stop_option(
    parser: &mut lexopt::Parser,
    exec: &mut ExecOptions,
    option: &'static str,
) -> Result<(), UsageError> {
    match option {
        "stop-before" => {
            exec.note("--stop-before");
            exec.stop.before.push(stop_name(parser, "--stop-before")?);
        }
        "stop-after" => {
            exec.note("--stop-after");
            exec.stop.after.push(stop_name(parser, "--stop-after")?);
        }
        "stop-count" => {
            exec.note("--stop-count");
            let value = option_value(parser, "stop count")?;
            let count = value
                .parse::<NonZeroU64>()
                .map_err(|_| usage(format!("--stop-count `{value}` is not a positive integer")))?;
            set_once(&mut exec.stop_count, count, "--stop-count")?;
        }
        _ => unreachable!("stop_option is called only for the stop options"),
    }
    Ok(())
}

/// The KRS item or K label a stop option names, which must not be empty.
fn stop_name(parser: &mut lexopt::Parser, option: &str) -> Result<String, UsageError> {
    let name = option_value(parser, "stop rule")?;
    if name.is_empty() {
        return Err(usage(format!(
            "{option} needs a KRS item or a K label, not an empty name"
        )));
    }
    Ok(name)
}

/// The stop criterion of `--stop-before`, `--stop-after` and `--stop-count`: a count without a
/// rule has no stop to count.
fn stop_criterion(
    rules: StopRules,
    count: Option<NonZeroU64>,
) -> Result<StopCriterion, UsageError> {
    match count {
        Some(_) if rules.is_empty() => Err(usage(
            "--stop-count needs --stop-before or --stop-after: it counts arrivals at their rules",
        )),
        Some(count) => Ok(StopCriterion::Rules { rules, count }),
        None => Ok(rules.into()),
    }
}

/// Parse one of the hidden options between a supervising `krs prove` and its workers.
fn worker_option(
    parser: &mut lexopt::Parser,
    exec: &mut ExecOptions,
    option: &'static str,
) -> Result<(), UsageError> {
    match option {
        "worker-protocol" => {
            exec.note("--worker-protocol");
            exec.worker = true;
        }
        "worker-claim" => {
            exec.note("--worker-claim");
            exec.worker_claims
                .push(option_value(parser, "claim label")?);
        }
        "worker-color" => {
            exec.note("--worker-color");
            // The supervisor resolves `auto`: a worker's stdout is never the terminal.
            let value = option_value(parser, "color")?;
            let color = match value.as_str() {
                "always" => ColorChoice::Always,
                "never" => ColorChoice::Never,
                _ => return Err(usage(format!("unknown worker color `{value}`"))),
            };
            set_once(&mut exec.worker_color, color, "--worker-color")?;
        }
        _ => unreachable!("worker_option is called only for the worker options"),
    }
    Ok(())
}

/// The case file `--case` names, which must be `.toml` or `.json`: its extension selects how it
/// is read.
fn case_path(value: String) -> Result<PathBuf, UsageError> {
    let path = PathBuf::from(value);
    match path.extension().and_then(|extension| extension.to_str()) {
        Some("toml" | "json") => Ok(path),
        Some(extension) => Err(usage(format!(
            "--case `{}` has the extension `.{extension}`; a case file is `.toml` or `.json`",
            path.display()
        ))),
        None => Err(usage(format!(
            "--case `{}` has no extension; a case file is `.toml` or `.json`",
            path.display()
        ))),
    }
}

/// The input name and the JSON document of `--input NAME=JSON`.
fn typed_input(value: &str) -> Result<(String, String), UsageError> {
    let (name, document) = value
        .split_once('=')
        .ok_or_else(|| usage(format!("--input `{value}` must have the form NAME=JSON")))?;
    if name.trim_start_matches('$').is_empty() {
        return Err(usage(format!("--input `{value}` has an empty input name")));
    }
    Ok((name.to_owned(), document.to_owned()))
}

/// The options each run-family command accepts beyond the shared selection options.
fn exec_options(kind: CommandKind) -> &'static [&'static str] {
    match kind {
        CommandKind::Parse => &["FILE", "--sort"],
        CommandKind::Run => &[
            "FILE",
            "--case",
            "--input",
            "-c",
            "--depth",
            "--stop-before",
            "--stop-after",
            "--stop-count",
            "--trace",
            "--coverage",
            "--color",
        ],
        CommandKind::Search => &[
            "FILE",
            "--case",
            "--input",
            "-c",
            "--mode",
            "--depth",
            "--max-solutions",
            "--trace",
            "--color",
        ],
        CommandKind::Prove => &[
            "--spec-module",
            "--claim",
            "--depth",
            "--color",
            "--worker-protocol",
            "--worker-claim",
            "--worker-color",
        ],
        CommandKind::Check | CommandKind::Expand | CommandKind::EmitK | CommandKind::Build => &[],
    }
}

fn term_output(kind: CommandKind, output: Option<PathBuf>) -> Result<TermOutput, UsageError> {
    let Some(output) = output else {
        return Ok(if kind == CommandKind::Parse {
            TermOutput::Kast
        } else {
            TermOutput::Pretty
        });
    };
    let value = output.to_string_lossy();
    match (value.as_ref(), kind) {
        ("kast", _) => Ok(TermOutput::Kast),
        ("json", _) => Ok(TermOutput::Json),
        ("kore", _) => Ok(TermOutput::Kore),
        ("none", CommandKind::Run) => Ok(TermOutput::None),
        ("jsonl", CommandKind::Prove) => Ok(TermOutput::JsonLines),
        ("program", CommandKind::Parse) => Ok(TermOutput::Program),
        ("pretty", CommandKind::Run | CommandKind::Search | CommandKind::Prove) => {
            Ok(TermOutput::Pretty)
        }
        ("program", _) => Err(usage("--output program applies only to krs parse")),
        _ => Err(usage(format!(
            "unknown --output format `{value}` for krs {}",
            kind.as_str()
        ))),
    }
}

fn exec_command(
    kind: CommandKind,
    exec: ExecOptions,
    output: Option<PathBuf>,
) -> Result<Command, UsageError> {
    let accepted = exec_options(kind);
    if let Some(option) = exec.given.iter().find(|option| !accepted.contains(option)) {
        return Err(usage(if *option == "FILE" {
            format!("krs {} takes no FILE argument", kind.as_str())
        } else {
            format!("{option} does not apply to krs {}", kind.as_str())
        }));
    }
    if exec.inputs.len() > 1 {
        return Err(usage("more than one FILE given"));
    }
    let input = exec.inputs.into_iter().next().map(|input| {
        if input == "-" {
            ProgramSource::Stdin
        } else {
            ProgramSource::File(PathBuf::from(input))
        }
    });
    let output = term_output(kind, output)?;
    let color = exec.color.unwrap_or_default();
    Ok(match kind {
        CommandKind::Parse => Command::Parse(ParseRequest {
            sort: exec.sort,
            input: input.unwrap_or(ProgramSource::Stdin),
            output,
        }),
        CommandKind::Run => Command::Run(RunRequest {
            input,
            case: exec.case,
            inputs: exec.typed,
            variables: exec.variables,
            depth: exec.depth,
            stop: stop_criterion(exec.stop, exec.stop_count)?,
            trace: exec.trace,
            coverage: exec.coverage,
            output,
            color,
        }),
        CommandKind::Search => Command::Search(SearchRequest {
            input,
            case: exec.case,
            inputs: exec.typed,
            variables: exec.variables,
            mode: exec.mode.unwrap_or_default(),
            depth: exec.depth,
            max_solutions: exec.max_solutions,
            trace: exec.trace,
            output,
            color,
        }),
        CommandKind::Prove => {
            if !exec.worker && !exec.worker_claims.is_empty() {
                return Err(usage("--worker-claim applies only with --worker-protocol"));
            }
            if !exec.worker && exec.worker_color.is_some() {
                return Err(usage("--worker-color applies only with --worker-protocol"));
            }
            Command::Prove(ProveRequest {
                spec_module: exec.spec_module,
                claims: if exec.worker_claims.is_empty() {
                    exec.claims
                } else {
                    exec.worker_claims
                },
                depth: exec.depth,
                output,
                color: exec.worker_color.unwrap_or(color),
                worker: exec.worker,
            })
        }
        CommandKind::Check | CommandKind::Expand | CommandKind::EmitK | CommandKind::Build => {
            unreachable!("only run-family commands take run options")
        }
    })
}

fn finish_run(kind: CommandKind, options: RunOptions) -> Result<ParseResult, UsageError> {
    let RunOptions {
        exec,
        manifest_path,
        package,
        package_id,
        definition,
        dependencies,
        cfg,
        backend,
        output,
        registration,
        no_reuse,
        message_format,
        measure,
        partition,
        ir,
        profile,
    } = options;
    if package.is_some() && package_id.is_some() {
        return Err(usage("--package and --package-id cannot be combined"));
    }
    let root = FacetSelector {
        package: match (package, package_id) {
            (Some(name), None) => PackageSelector::Name(name),
            (None, Some(id)) => PackageSelector::Id(id),
            _ => return Err(usage("missing --package or --package-id")),
        },
        definition: definition.ok_or_else(|| usage("missing --definition"))?,
    };
    if let Some(option) = exec.given.first()
        && exec_options(kind).is_empty()
    {
        return Err(usage(if *option == "FILE" {
            format!("krs {} takes no FILE argument", kind.as_str())
        } else {
            format!("{option} does not apply to krs {}", kind.as_str())
        }));
    }
    let command = match kind {
        CommandKind::Parse | CommandKind::Run | CommandKind::Search | CommandKind::Prove => {
            if backend.is_some() {
                return Err(usage(format!(
                    "--backend does not apply to krs {}; it always uses the in-process k-rust backend",
                    kind.as_str()
                )));
            }
            exec_command(kind, exec, output)?
        }
        CommandKind::Check if output.is_some() => {
            return Err(usage("--output does not apply to check"));
        }
        CommandKind::Check => Command::Check { backend, partition },
        CommandKind::Expand => Command::Expand { output },
        CommandKind::EmitK => Command::EmitK {
            output: output.ok_or_else(|| usage("missing --output"))?,
            ir,
        },
        CommandKind::Build => Command::Build {
            backend: backend.unwrap_or(Backend::Llvm),
            output: output.ok_or_else(|| usage("missing --output"))?,
        },
    };
    Ok(ParseResult::Run(
        Box::new(CommandRequest {
            command,
            manifest_path: manifest_path.unwrap_or_else(|| PathBuf::from("Cargo.toml")),
            root,
            dependencies,
            cfg,
            registration: registration.unwrap_or(RegistrationMode::Inventory),
            no_reuse,
            message_format: message_format.unwrap_or_default(),
            profile,
        }),
        measure,
    ))
}

/// The options of `krs kink` that are krs's own and take a value, as `--name`.
#[cfg(feature = "kink")]
const KINK_VALUE_OPTIONS: [&str; 12] = [
    "--manifest-path",
    "--package",
    "--package-id",
    "--definition",
    "--dependency",
    "--cfg",
    "--profile",
    "--message-format",
    "--registration",
    "--corpus",
    "--timings",
    "--counters",
];

/// Parse `krs kink`'s arguments: krs's selection options and `--corpus`, `--locked`, before or
/// after the verb; the verb (`emit`, or one of kink-flow's); and, for a kink-flow verb, every
/// other argument in order, which kink-flow's parser reads. Before the verb only krs's options
/// may appear, so the verb is the first argument that is neither one of them nor a value of one.
#[cfg(feature = "kink")]
fn parse_kink(arguments: Vec<OsString>) -> Result<ParseResult, UsageError> {
    let kink = |message: String| UsageError::Kink(message);
    let arguments = arguments
        .into_iter()
        .map(|argument| {
            argument
                .into_string()
                .map_err(|_| kink("an argument is not valid UTF-8".into()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut options = RunOptions::default();
    let mut corpus = None;
    let mut locked = false;
    let mut check = false;
    let mut verb: Option<String> = None;
    let mut rest = Vec::new();
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if matches!(argument.as_str(), "-h" | "--help") {
            return Ok(ParseResult::KinkHelp);
        }
        let (name, inline) = match argument.split_once('=') {
            Some((name, value)) if name.starts_with("--") => {
                (name.to_owned(), Some(value.to_owned()))
            }
            _ => (argument.clone(), None),
        };
        if KINK_VALUE_OPTIONS.contains(&name.as_str()) {
            let value = match inline {
                Some(value) => value,
                None => arguments
                    .next()
                    .ok_or_else(|| kink(format!("{name} needs a value")))?,
            };
            kink_selection(&mut options, &mut corpus, &name, value)
                .map_err(|error| kink(error.to_string()))?;
            continue;
        }
        match name.as_str() {
            "--no-reuse" => {
                return Err(kink(
                    "--no-reuse does not apply to krs kink: every command that builds the \
                     package builds it in process, and reuses no earlier build"
                        .into(),
                ));
            }
            "--locked" if inline.is_none() => locked = true,
            "--check" if inline.is_none() && verb.as_deref() == Some("emit") => check = true,
            _ if verb.is_none() => {
                if argument.starts_with('-') {
                    return Err(kink(format!(
                        "{argument} before the verb: give the verb first (emit, {})",
                        kink_verbs()
                    )));
                }
                if argument != "emit" && kink_flow::Verb::parse(&argument).is_none() {
                    return Err(kink(format!(
                        "unknown verb `{argument}`; expected emit, {}",
                        kink_verbs()
                    )));
                }
                verb = Some(argument);
            }
            _ => rest.push(argument),
        }
    }
    let verb = verb.ok_or_else(|| kink(format!("missing verb: emit, {}", kink_verbs())))?;
    kink_request(options, corpus, locked, check, &verb, rest)
}

/// The request of `krs kink VERB` with the options `parse_kink` read, and `rest`, the
/// arguments that are not krs's.
#[cfg(feature = "kink")]
fn kink_request(
    options: RunOptions,
    corpus: Option<PathBuf>,
    locked: bool,
    check: bool,
    verb: &str,
    rest: Vec<String>,
) -> Result<ParseResult, UsageError> {
    let kink = |message: String| UsageError::Kink(message);
    let verb = if verb == "emit" {
        if let Some(argument) = rest.first() {
            return Err(kink(format!("krs kink emit takes no {argument}")));
        }
        if locked {
            return Err(kink(
                "--locked does not apply to emit; emit --check writes nothing and fails on a \
                 stale definition.k"
                    .into(),
            ));
        }
        krs_cli::KinkVerb::Emit { check }
    } else {
        let verb = kink_flow::Verb::parse(verb).expect("the verb was checked");
        if locked && verb == kink_flow::Verb::Report {
            return Err(kink(
                "--locked does not apply to report, which builds nothing and only prints the \
                 stored run; emit --check fails on a stale definition.k"
                    .into(),
            ));
        }
        krs_cli::KinkVerb::Flow {
            verb,
            options: rest,
        }
    };
    if options.package.is_some() && options.package_id.is_some() {
        return Err(kink("--package and --package-id cannot be combined".into()));
    }
    let root = FacetSelector {
        package: match (options.package, options.package_id) {
            (Some(name), None) => PackageSelector::Name(name),
            (None, Some(id)) => PackageSelector::Id(id),
            _ => return Err(kink("missing --package or --package-id".into())),
        },
        definition: options
            .definition
            .ok_or_else(|| kink("missing --definition".into()))?,
    };
    Ok(ParseResult::Kink(
        Box::new(krs_cli::KinkRequest {
            manifest_path: options
                .manifest_path
                .unwrap_or_else(|| PathBuf::from("Cargo.toml")),
            root,
            dependencies: options.dependencies,
            cfg: options.cfg,
            registration: options.registration.unwrap_or(RegistrationMode::Inventory),
            profile: options.profile,
            message_format: options.message_format.unwrap_or_default(),
            corpus,
            locked,
            verb,
        }),
        options.measure,
    ))
}

/// kink-flow's verbs, as a usage message lists them.
#[cfg(feature = "kink")]
fn kink_verbs() -> String {
    kink_flow::Verb::ALL
        .iter()
        .map(|verb| verb.as_str())
        .collect::<Vec<_>>()
        .join(", ")
}

/// One of `krs kink`'s value options ([`KINK_VALUE_OPTIONS`]), read as the other commands read
/// it.
#[cfg(feature = "kink")]
fn kink_selection(
    options: &mut RunOptions,
    corpus: &mut Option<PathBuf>,
    name: &str,
    value: String,
) -> Result<(), UsageError> {
    match name {
        "--manifest-path" => set_once(&mut options.manifest_path, PathBuf::from(value), name),
        "--package" => set_once(&mut options.package, value, name),
        "--package-id" => set_once(&mut options.package_id, value, name),
        "--definition" => set_once(&mut options.definition, value, name),
        "--dependency" => {
            options.dependencies.push(parse_dependency(value.into())?);
            Ok(())
        }
        "--cfg" => {
            options.cfg.push(parse_cfg(value.into())?);
            Ok(())
        }
        "--profile" => {
            let selected = krs_ir::RawKProfile::from_metadata(&value).ok_or_else(|| {
                usage(format!(
                    "unknown profile `{value}`; expected standard or strict"
                ))
            })?;
            set_once(&mut options.profile, selected, name)
        }
        "--message-format" => {
            let selected = match value.as_str() {
                "human" => MessageFormat::Human,
                "json" => MessageFormat::Json,
                _ => return Err(usage(format!("unknown message format `{value}`"))),
            };
            set_once(&mut options.message_format, selected, name)
        }
        "--registration" => {
            let selected = match value.as_str() {
                "inventory" => RegistrationMode::Inventory,
                "explicit" => RegistrationMode::Explicit,
                _ => return Err(usage(format!("unknown registration mode `{value}`"))),
            };
            set_once(&mut options.registration, selected, name)
        }
        "--corpus" => set_once(corpus, PathBuf::from(value), name),
        "--timings" => set_once(&mut options.measure.timings, PathBuf::from(value), name),
        "--counters" => set_once(&mut options.measure.counters, PathBuf::from(value), name),
        _ => unreachable!("kink_selection is called only for KINK_VALUE_OPTIONS"),
    }
}

fn parse_format(parser: &mut lexopt::Parser) -> Result<ParseResult, UsageError> {
    let mut stdin = false;
    let mut edition = None;
    let mut check = false;
    let mut manifest_path = None;
    let mut paths = Vec::new();
    let mut trailing_comments = None;
    while let Some(argument) = parser.next()? {
        match argument {
            Short('h') | Long("help") => return Ok(ParseResult::Help),
            Long("stdin") => stdin = true,
            Long("edition") => {
                let value = option_value(parser, "Rust edition")?;
                set_once(
                    &mut edition,
                    value.parse::<Edition>().map_err(usage)?,
                    "--edition",
                )?;
            }
            Long("check") => check = true,
            Long("manifest-path") => set_once(
                &mut manifest_path,
                PathBuf::from(option_value(parser, "manifest path")?),
                "--manifest-path",
            )?,
            Long("trailing-comments") => {
                let value = option_value(parser, "trailing comment style")?;
                let selected = match value.as_str() {
                    "aligned" => TrailingCommentStyle::AlignedColumn,
                    "gutter" => TrailingCommentStyle::FixedGutter,
                    _ => return Err(usage(format!("unknown trailing comment style `{value}`"))),
                };
                set_once(&mut trailing_comments, selected, "--trailing-comments")?;
            }
            Value(path) => paths.push(PathBuf::from(path)),
            _ => return Err(argument.unexpected().into()),
        }
    }
    if stdin && (!paths.is_empty() || manifest_path.is_some()) {
        return Err(usage(
            "--stdin cannot be combined with paths or --manifest-path",
        ));
    }
    if edition.is_some() && !stdin {
        return Err(usage("--edition requires --stdin"));
    }
    Ok(ParseResult::Format(FormatRequest {
        stdin,
        edition: edition.unwrap_or_default(),
        check,
        manifest_path,
        paths,
        trailing_comments: trailing_comments.unwrap_or(TrailingCommentStyle::AlignedColumn),
    }))
}

fn execute_format(request: &FormatRequest) -> Result<bool, String> {
    let options = FormatOptions {
        trailing_comments: request.trailing_comments,
        edition: request.edition,
        ..FormatOptions::default()
    };
    if request.stdin {
        let mut source = String::new();
        io::stdin()
            .read_to_string(&mut source)
            .map_err(|error| format!("cannot read stdin: {error}"))?;
        let output =
            krs_fmt::format_source(&source, &options).map_err(|error| error.to_string())?;
        if request.check {
            if output != source {
                eprint!(
                    "{}",
                    krs_fmt::unified_diff(Path::new("<stdin>"), &source, &output)
                );
                return Ok(false);
            }
        } else {
            io::stdout()
                .lock()
                .write_all(output.as_bytes())
                .map_err(|error| format!("cannot write stdout: {error}"))?;
        }
        return Ok(true);
    }

    let files = krs_cli::discover_format_inputs(request.manifest_path.as_deref(), &request.paths)?;
    let mut formatted = Vec::with_capacity(files.len());
    let mut failed = false;
    for input in &files {
        match krs_fmt::format_file(
            &input.path,
            &FormatOptions {
                edition: input.edition,
                facade_aliases: input.facade_aliases.clone(),
                ..options
            },
        ) {
            Ok(file) => formatted.push(file),
            Err(error) => {
                eprintln!("{}: {error}", input.path.display());
                failed = true;
            }
        }
    }
    if failed {
        return Ok(false);
    }
    if request.check {
        let mut changed = false;
        for file in formatted.iter().filter(|file| file.changed) {
            let before = std::fs::read_to_string(&file.path)
                .map_err(|error| format!("cannot reread `{}`: {error}", file.path.display()))?;
            eprint!(
                "{}",
                krs_fmt::unified_diff(&file.path, &before, &file.output)
            );
            changed = true;
        }
        return Ok(!changed);
    }
    for file in formatted.into_iter().filter(|file| file.changed) {
        std::fs::write(&file.path, file.output)
            .map_err(|error| format!("cannot write `{}`: {error}", file.path.display()))?;
    }
    Ok(true)
}

fn parse_dependency(value: OsString) -> Result<FacetSelector, UsageError> {
    let value = utf8(value, "dependency")?;
    let (package, definition) = value.rsplit_once(':').ok_or_else(|| {
        usage(format!(
            "dependency `{value}` must have the form CargoPackage:definition"
        ))
    })?;
    if package.is_empty() || definition.is_empty() {
        return Err(usage(format!(
            "dependency `{value}` must have non-empty package and definition names"
        )));
    }
    Ok(FacetSelector {
        package: PackageSelector::Name(package.to_owned()),
        definition: definition.to_owned(),
    })
}

fn parse_cfg(value: OsString) -> Result<KrsCfg, UsageError> {
    let value = utf8(value, "cfg")?;
    let (key, value) = value
        .split_once('=')
        .map_or((value.as_str(), None), |(key, value)| {
            (key, Some(value.to_owned()))
        });
    if !valid_identifier_segment(key) {
        return Err(usage(format!("invalid cfg key `{key}`")));
    }
    Ok(KrsCfg {
        key: key.to_owned(),
        value,
    })
}

fn utf8(value: OsString, role: &str) -> Result<String, UsageError> {
    value
        .into_string()
        .map_err(|_| usage(format!("{role} is not valid UTF-8")))
}

#[cfg(test)]
mod tests {
    use super::*;
    use krs_diagnostic::codes::CodeKind;

    #[test]
    fn reports_located_then_unlocated_errors_and_warnings_as_envelopes() {
        let package = krs_ir::PackageId::new("diag", "diag", "0.1.0", "workspace").unwrap();
        let file = krs_ir::SourceFileId::new(
            package,
            "src/lib.rs",
            krs_ir::Sha256Digest::new("11".repeat(32)).unwrap(),
        )
        .unwrap();
        let unused = krs_diagnostic::Code::foreign("UnusedVariable", CodeKind::Author);
        let mut envelope = krs_cli::DiagnosticEnvelope::error(
            krs_cli::DiagnosticStage::Native,
            unused.clone(),
            "unused variable",
            krs_ir::SourceRange::new(file, 7, 16).unwrap(),
        );
        envelope.severity = krs_cli::DiagnosticSeverity::Warning;
        // An undefined label in a `raw_k!` text: the author's.
        let error = krs_cli::DiagnosticEnvelope::unlocated(
            krs_cli::DiagnosticStage::Native,
            krs_diagnostic::Code::foreign("UndefinedKLabel", CodeKind::Author),
            "undefined label",
        );
        let mut warning = krs_cli::DiagnosticEnvelope::unlocated(
            krs_cli::DiagnosticStage::Native,
            unused,
            "unused variable",
        );
        warning.severity = krs_cli::DiagnosticSeverity::Warning;
        let mut output = Vec::new();
        write_diagnostics(
            &mut output,
            &[error.clone(), envelope.clone(), warning.clone()],
            MessageFormat::Json,
            &DiagnosticSources::default(),
            false,
        )
        .unwrap();
        let output = String::from_utf8(output).unwrap();
        assert_eq!(
            output,
            format!(
                "{}{}{}",
                envelope.to_json_line().unwrap(),
                error.to_json_line().unwrap(),
                warning.to_json_line().unwrap(),
            )
        );
        assert!(output.contains("\"authored_range\":null"));
        let mut human = Vec::new();
        write_diagnostics(
            &mut human,
            &[error],
            MessageFormat::Human,
            &DiagnosticSources::default(),
            false,
        )
        .unwrap();
        assert_eq!(
            String::from_utf8(human).unwrap(),
            "error[UndefinedKLabel]: undefined label\n"
        );
    }

    fn parse_args(args: &[&str]) -> Result<ParseResult, UsageError> {
        parse(args.iter().map(OsString::from).collect())
    }

    fn error(args: &[&str]) -> String {
        match parse_args(args) {
            Err(error) => error.to_string(),
            Ok(_) => panic!("expected error for {args:?}"),
        }
    }

    #[cfg(feature = "kink")]
    fn kink(args: &[&str]) -> krs_cli::KinkRequest {
        match parse_args(args).unwrap() {
            ParseResult::Kink(request, _) => *request,
            _ => panic!("expected a kink command for {args:?}"),
        }
    }

    /// `krs kink` takes krs's selection before or after the verb and hands every other option
    /// to kink-flow's parser in order; `emit` takes `--check` and nothing of kink-flow's.
    #[cfg(feature = "kink")]
    #[test]
    fn kink_separates_krs_options_from_the_verbs() {
        let request = kink(&[
            "kink",
            "--package",
            "p",
            "run",
            "--only",
            "a",
            "--definition=main",
            "--full",
            "--locked",
            "--corpus",
            "c",
            "--output",
            "verdicts",
        ]);
        assert_eq!(request.root.definition, "main");
        assert_eq!(request.corpus, Some(PathBuf::from("c")));
        assert!(request.locked);
        assert_eq!(
            request.verb,
            krs_cli::KinkVerb::Flow {
                verb: kink_flow::Verb::Run,
                options: ["--only", "a", "--full", "--output", "verdicts"]
                    .map(String::from)
                    .to_vec(),
            }
        );
        let emit = kink(&[
            "kink",
            "emit",
            "--check",
            "--package",
            "p",
            "--definition",
            "d",
        ]);
        assert_eq!(emit.verb, krs_cli::KinkVerb::Emit { check: true });
        for (args, message) in [
            (&["kink", "--full", "run"][..], "--full before the verb"),
            (
                &["kink", "walk", "--package", "p"][..],
                "unknown verb `walk`",
            ),
            (
                &[
                    "kink",
                    "emit",
                    "--full",
                    "--package",
                    "p",
                    "--definition",
                    "d",
                ][..],
                "takes no --full",
            ),
            (
                &[
                    "kink",
                    "emit",
                    "--locked",
                    "--package",
                    "p",
                    "--definition",
                    "d",
                ][..],
                "--locked does not apply",
            ),
            (
                &[
                    "kink",
                    "report",
                    "--locked",
                    "--package",
                    "p",
                    "--definition",
                    "d",
                ][..],
                "--locked does not apply to report",
            ),
            (
                &[
                    "kink",
                    "report",
                    "--no-reuse",
                    "--package",
                    "p",
                    "--definition",
                    "d",
                ][..],
                "every command that builds the package",
            ),
            (
                &["kink", "run", "--definition", "d"][..],
                "missing --package",
            ),
            (
                &["kink", "--package", "p", "--definition", "d"][..],
                "missing verb",
            ),
        ] {
            let error = error(args);
            assert!(error.contains(message), "{args:?}: {error}");
        }
        assert!(matches!(
            parse_args(&["kink", "--help"]),
            Ok(ParseResult::KinkHelp)
        ));
    }

    fn run(args: &[&str]) -> (CommandRequest, MeasureOptions) {
        match parse_args(args).unwrap() {
            ParseResult::Run(request, measure) => (*request, measure),
            _ => panic!("expected run command"),
        }
    }

    #[test]
    fn parses_message_format() {
        for command in ["check", "expand", "emit-k", "build"] {
            let mut args = vec![command, "--package", "imp", "--definition", "main"];
            if matches!(command, "emit-k" | "build") {
                args.extend(["--output", "out"]);
            }
            assert_eq!(run(&args).0.message_format, MessageFormat::Human);
            for spelling in [
                vec!["--message-format", "json"],
                vec!["--message-format=json"],
                vec!["--message-format=human"],
            ] {
                let mut selected = args.clone();
                selected.extend(&spelling);
                let expected = if spelling.last() == Some(&"--message-format=human") {
                    MessageFormat::Human
                } else {
                    MessageFormat::Json
                };
                assert_eq!(run(&selected).0.message_format, expected);
            }
        }
        assert_eq!(
            error(&["check", "--message-format=xml"]),
            "unknown message format `xml`"
        );
    }

    #[test]
    fn parses_value_options_with_equals() {
        let (request, measure) = run(&[
            "build",
            "--manifest-path=Cargo.toml",
            "--package=imp",
            "--definition=main",
            "--dependency=base:core",
            "--cfg=feature=enabled",
            "--backend=haskell",
            "--output=out",
            "--timings=timings.json",
            "--counters=counters.json",
            "--registration=explicit",
        ]);
        assert_eq!(
            request.command,
            Command::Build {
                backend: Backend::Haskell,
                output: PathBuf::from("out")
            }
        );
        assert_eq!(request.dependencies.len(), 1);
        assert_eq!(request.cfg[0].value.as_deref(), Some("enabled"));
        assert_eq!(request.registration, RegistrationMode::Explicit);
        assert_eq!(measure.timings, Some(PathBuf::from("timings.json")));
        assert_eq!(measure.counters, Some(PathBuf::from("counters.json")));
    }

    #[test]
    fn parses_command_variants_and_repeatable_values() {
        let (request, _) = run(&[
            "emit-k",
            "--package",
            "imp",
            "--definition",
            "main",
            "--backend",
            "haskell",
            "--output",
            "out",
            "--dependency",
            "a:b",
            "--dependency",
            "c:d",
            "--cfg",
            "flag",
            "--cfg",
            "mode=fast",
            "--no-reuse",
            "--no-reuse",
        ]);
        assert_eq!(
            request.command,
            Command::EmitK {
                output: "out".into(),
                ir: false,
            }
        );
        assert_eq!(request.dependencies.len(), 2);
        assert_eq!(request.cfg.len(), 2);
        assert_eq!(request.cfg[0].value, None);
        assert!(request.no_reuse);
        let (request, _) = run(&[
            "emit-k",
            "--package",
            "imp",
            "--definition",
            "main",
            "--output",
            "out",
            "--ir",
        ]);
        assert_eq!(
            request.command,
            Command::EmitK {
                output: "out".into(),
                ir: true,
            }
        );
        for command in ["check", "build"] {
            let mut args = vec![command, "--package", "imp", "--definition", "main", "--ir"];
            if command == "build" {
                args.extend(["--output", "out"]);
            }
            assert!(parse_args(&args).is_err(), "{command} accepted --ir");
        }

        let (request, _) = run(&[
            "check",
            "--package-id",
            "exact-id",
            "--definition",
            "main",
            "--backend",
            "haskell",
        ]);
        assert_eq!(
            request.command,
            Command::Check {
                backend: Some(Backend::Haskell),
                partition: false,
            }
        );
        assert_eq!(request.root.package, PackageSelector::Id("exact-id".into()));

        let (request, _) = run(&["expand", "--package", "imp", "--definition", "main"]);
        assert_eq!(request.command, Command::Expand { output: None });
        let (request, _) = run(&[
            "expand",
            "--package",
            "imp",
            "--definition",
            "main",
            "--output",
            "printed",
        ]);
        assert_eq!(
            request.command,
            Command::Expand {
                output: Some(PathBuf::from("printed"))
            }
        );
    }

    #[test]
    fn rejects_repeated_singular_options() {
        let required = [
            "build",
            "--package-id",
            "id",
            "--definition",
            "main",
            "--output",
            "out",
        ];
        for (option, value) in [
            ("--manifest-path", "Cargo.toml"),
            ("--package", "imp"),
            ("--package-id", "id"),
            ("--definition", "main"),
            ("--backend", "llvm"),
            ("--output", "out"),
            ("--timings", "timings.json"),
            ("--counters", "counters.json"),
            ("--registration", "inventory"),
            ("--message-format", "json"),
        ] {
            let mut args = required.to_vec();
            if !args.contains(&option) {
                args.extend([option, value]);
            }
            args.extend([option, value]);
            assert_eq!(
                error(&args),
                format!("{option} specified more than once"),
                "{args:?}"
            );
        }
        for (option, value) in [
            ("--manifest-path", "Cargo.toml"),
            ("--trailing-comments", "gutter"),
        ] {
            assert_eq!(
                error(&["fmt", option, value, option, value]),
                format!("{option} specified more than once")
            );
        }
    }

    #[test]
    fn rejects_invalid_combinations_and_spellings() {
        let base = ["--package", "imp", "--definition", "main"];
        assert!(
            error(&[
                "check",
                "--package",
                "imp",
                "--package-id",
                "id",
                "--definition",
                "main"
            ])
            .contains("--package and --package-id")
        );
        for key in ["1abc", "a-b", "fn", ""] {
            assert!(
                error(&[
                    "check",
                    "--package",
                    "imp",
                    "--definition",
                    "main",
                    "--cfg",
                    key
                ])
                .contains("invalid cfg key")
            );
        }
        assert!(
            error(&[
                "check", base[0], base[1], base[2], base[3], "--output", "out"
            ])
            .contains("--output does not apply to check")
        );
        for command in ["emit-k", "build"] {
            assert!(
                error(&[command, base[0], base[1], base[2], base[3]]).contains("missing --output")
            );
        }
        assert!(error(&["check", "--package", "imp"]).contains("missing --definition"));
        assert!(!error(&["check", "--wat"]).is_empty());
        assert!(error(&["wat"]).contains("unknown command"));
        assert!(error(&["check", "--backend", "unknown"]).contains("unknown backend"));
        for dependency in ["base", ":core", "base:"] {
            assert!(error(&["check", "--dependency", dependency]).contains("dependency"));
        }
    }

    #[test]
    fn parses_fmt_editor_mode() {
        let ParseResult::Format(request) = parse_args(&[
            "fmt",
            "--stdin",
            "--edition",
            "2021",
            "--trailing-comments",
            "gutter",
        ])
        .unwrap() else {
            panic!("expected fmt command")
        };
        assert!(request.stdin);
        assert_eq!(request.edition, Edition::E2021);
        assert_eq!(request.trailing_comments, TrailingCommentStyle::FixedGutter);
    }

    #[test]
    fn parses_fmt_modes() {
        let ParseResult::Format(request) = parse_args(&[
            "fmt",
            "--stdin",
            "--stdin",
            "--check",
            "--check",
            "--trailing-comments=gutter",
        ])
        .unwrap() else {
            panic!("expected fmt command")
        };
        assert!(request.stdin);
        assert!(request.check);
        assert_eq!(request.trailing_comments, TrailingCommentStyle::FixedGutter);
        let ParseResult::Format(request) =
            parse_args(&["fmt", "--", "--check", "--help", "src/lib.rs"]).unwrap()
        else {
            panic!("expected fmt command")
        };
        assert_eq!(
            request.paths,
            [
                PathBuf::from("--check"),
                PathBuf::from("--help"),
                PathBuf::from("src/lib.rs")
            ]
        );
        assert!(!request.check);
        let ParseResult::Format(request) =
            parse_args(&["fmt", "--manifest-path=Cargo.toml"]).unwrap()
        else {
            panic!("expected fmt command")
        };
        assert_eq!(request.manifest_path, Some(PathBuf::from("Cargo.toml")));
    }

    #[test]
    fn rejects_unknown_or_file_mode_edition() {
        assert!(error(&["fmt", "--stdin", "--edition", "2030"]).contains("unknown Rust edition"));
        assert!(error(&["fmt", "--edition", "2021", "src"]).contains("--edition requires --stdin"));
        assert!(
            error(&["fmt", "--stdin", "--edition", "2021", "--edition=2024"])
                .contains("--edition specified more than once")
        );
    }

    #[test]
    fn rejects_fmt_stdin_conflicts() {
        assert!(error(&["fmt", "--stdin", "src"]).contains("--stdin cannot"));
        assert!(
            error(&["fmt", "--stdin", "--manifest-path", "Cargo.toml"]).contains("--stdin cannot")
        );
    }

    #[test]
    fn help_and_missing_values() {
        for args in [vec!["--help"], vec!["check", "--help"], vec!["fmt", "-h"]] {
            assert!(matches!(parse_args(&args), Ok(ParseResult::Help)));
        }
        assert!(
            error(&["check", "--definition"])
                .contains("missing argument for option '--definition'")
        );
        assert!(
            error(&["fmt", "--trailing-comments"])
                .contains("missing argument for option '--trailing-comments'")
        );
    }

    #[test]
    #[expect(
        clippy::too_many_lines,
        reason = "One table of every run-family command keeps their parses side by side."
    )]
    fn parses_run_family_commands() {
        let base = ["--package", "imp", "--definition", "main"];
        let with = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb];
            args.extend(base);
            args.extend(extra);
            run(&args).0.command
        };
        assert_eq!(
            with(
                "run",
                &[
                    "prog.imp",
                    "--case",
                    "cases/sum.toml",
                    "--input",
                    "regs={\"A\": 1}",
                    "--input=$PC=0x100",
                    "-c",
                    "env=.Map",
                    "-c$STORE=1",
                    "--depth",
                    "3",
                    "--trace",
                    "--coverage",
                    "--output",
                    "json"
                ]
            ),
            Command::Run(RunRequest {
                input: Some(ProgramSource::File(PathBuf::from("prog.imp"))),
                case: Some(PathBuf::from("cases/sum.toml")),
                inputs: vec![
                    ("regs".to_owned(), "{\"A\": 1}".to_owned()),
                    ("$PC".to_owned(), "0x100".to_owned()),
                ],
                variables: vec![
                    ("env".to_owned(), ".Map".to_owned()),
                    ("$STORE".to_owned(), "1".to_owned()),
                ],
                depth: Some(3),
                stop: StopCriterion::None,
                trace: true,
                coverage: true,
                output: TermOutput::Json,
                color: ColorChoice::Auto,
            })
        );
        assert_eq!(
            with(
                "search",
                &[
                    "-",
                    "--case=case.json",
                    "--mode",
                    "one-step",
                    "--max-solutions",
                    "2",
                    "--color",
                    "never"
                ]
            ),
            Command::Search(SearchRequest {
                input: Some(ProgramSource::Stdin),
                case: Some(PathBuf::from("case.json")),
                inputs: Vec::new(),
                variables: Vec::new(),
                mode: SearchMode::OneStep,
                depth: None,
                max_solutions: Some(2),
                trace: false,
                output: TermOutput::Pretty,
                color: ColorChoice::Never,
            })
        );
        assert_eq!(
            with(
                "prove",
                &[
                    "--claim",
                    "branching",
                    "--claim",
                    "MAIN-SPEC.sum",
                    "--output=kore"
                ]
            ),
            Command::Prove(ProveRequest {
                spec_module: None,
                claims: vec!["branching".to_owned(), "MAIN-SPEC.sum".to_owned()],
                depth: None,
                output: TermOutput::Kore,
                color: ColorChoice::Auto,
                worker: false,
            })
        );
        assert_eq!(
            with("prove", &["--spec-module", "IMP-SUM-SPEC"]),
            Command::Prove(ProveRequest {
                spec_module: Some("IMP-SUM-SPEC".to_owned()),
                claims: Vec::new(),
                depth: None,
                output: TermOutput::Pretty,
                color: ColorChoice::Auto,
                worker: false,
            })
        );
        assert_eq!(
            with("parse", &["--sort", "Stmt"]),
            Command::Parse(ParseRequest {
                sort: Some("Stmt".to_owned()),
                input: ProgramSource::Stdin,
                output: TermOutput::Kast,
            })
        );
        assert_eq!(
            with("parse", &["--output", "program"]),
            Command::Parse(ParseRequest {
                sort: None,
                input: ProgramSource::Stdin,
                output: TermOutput::Program,
            })
        );
        let Command::Run(run) = with("run", &["prog.imp", "--output", "pretty"]) else {
            panic!("krs run parses as a run command");
        };
        assert_eq!(run.output, TermOutput::Pretty);
        let Command::Prove(prove) = with("prove", &[]) else {
            panic!("krs prove parses as a prove command");
        };
        assert_eq!(prove.output, TermOutput::Pretty);
        assert!(!prove.worker);
        // A worker proves exactly the claims its supervisor gives it, whatever `--claim` says.
        let Command::Prove(worker) = with(
            "prove",
            &[
                "--claim",
                "sum",
                "--output",
                "jsonl",
                "--worker-protocol",
                "--worker-claim",
                "MAIN-SPEC.branching",
                "--color",
                "auto",
                "--worker-color",
                "always",
            ],
        ) else {
            panic!("krs prove parses as a prove command");
        };
        assert!(worker.worker);
        assert_eq!(worker.claims, ["MAIN-SPEC.branching"]);
        assert_eq!(worker.output, TermOutput::JsonLines);
        // A worker colours as its supervisor resolved `--color` against the supervisor's stdout.
        assert_eq!(worker.color, ColorChoice::Always);
    }

    /// `--stop-before` and `--stop-after` name stop rules by KRS item or K label, each
    /// repeatable, and `--stop-count` counts arrivals at them; a count without a stop is refused.
    #[test]
    fn parses_stop_options_and_refuses_a_count_without_a_stop() {
        let base = ["--package", "imp", "--definition", "main"];
        let with = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb];
            args.extend(base);
            args.extend(extra);
            run(&args).0.command
        };
        let failure = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb];
            args.extend(base);
            args.extend(extra);
            error(&args)
        };
        let stop = |extra: &[&str]| match with("run", extra) {
            Command::Run(request) => request.stop,
            other => panic!("{other:?}"),
        };
        let rules = StopRules {
            before: vec!["ppu::frame_end".to_owned()],
            after: vec!["boundary-fetch".to_owned(), "crate::tick".to_owned()],
        };
        assert_eq!(
            stop(&[
                "--stop-before",
                "ppu::frame_end",
                "--stop-after=boundary-fetch",
                "--stop-after",
                "crate::tick",
                "--stop-count",
                "60"
            ]),
            StopCriterion::Rules {
                rules,
                count: NonZeroU64::new(60).unwrap(),
            }
        );
        // Without --stop-count the run ends at its first stop.
        assert_eq!(
            stop(&["--stop-after", "boundary-fetch"]),
            StopCriterion::Rules {
                rules: StopRules {
                    after: vec!["boundary-fetch".to_owned()],
                    ..StopRules::default()
                },
                count: NonZeroU64::MIN,
            }
        );
        assert_eq!(stop(&[]), StopCriterion::None);
        assert_eq!(
            failure("run", &["--stop-count", "2"]),
            "--stop-count needs --stop-before or --stop-after: it counts arrivals at their rules"
        );
        assert_eq!(
            failure("run", &["--stop-after", "tick", "--stop-count", "0"]),
            "--stop-count `0` is not a positive integer"
        );
        assert_eq!(
            failure(
                "run",
                &[
                    "--stop-after",
                    "tick",
                    "--stop-count",
                    "2",
                    "--stop-count",
                    "3"
                ]
            ),
            "--stop-count specified more than once"
        );
        assert_eq!(
            failure("run", &["--stop-before", ""]),
            "--stop-before needs a KRS item or a K label, not an empty name"
        );
        assert_eq!(
            failure("search", &["--stop-after", "tick"]),
            "--stop-after does not apply to krs search"
        );
    }

    #[test]
    fn worker_options_need_the_worker_protocol_and_jsonl_is_prove_only() {
        let failure = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb, "--package", "imp", "--definition", "main"];
            args.extend(extra);
            error(&args)
        };
        assert_eq!(
            failure("prove", &["--worker-claim", "sum"]),
            "--worker-claim applies only with --worker-protocol"
        );
        assert_eq!(
            failure("prove", &["--worker-color", "never"]),
            "--worker-color applies only with --worker-protocol"
        );
        assert_eq!(
            failure("run", &["--output", "jsonl"]),
            "unknown --output format `jsonl` for krs run"
        );
    }

    #[test]
    fn rejects_run_family_options_on_the_wrong_verb() {
        let base = ["--package", "imp", "--definition", "main"];
        let failure = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb];
            args.extend(base);
            args.extend(extra);
            error(&args)
        };
        assert_eq!(
            failure("run", &["--max-solutions", "1"]),
            "--max-solutions does not apply to krs run"
        );
        assert_eq!(
            failure("run", &["--mode", "all"]),
            "--mode does not apply to krs run"
        );
        assert_eq!(
            failure("parse", &["--trace"]),
            "--trace does not apply to krs parse"
        );
        assert_eq!(
            failure("prove", &["--trace"]),
            "--trace does not apply to krs prove"
        );
        assert_eq!(
            failure("run", &["--claim", "x"]),
            "--claim does not apply to krs run"
        );
        assert_eq!(
            failure("check", &["--claim", "x"]),
            "--claim does not apply to krs check"
        );
        assert_eq!(
            failure("run", &["--spec-module", "IMP-SUM-SPEC"]),
            "--spec-module does not apply to krs run"
        );
        assert_eq!(
            failure("prove", &["--spec-module", "A", "--spec-module", "B"]),
            "--spec-module specified more than once"
        );
        assert_eq!(
            failure("prove", &["prog.imp"]),
            "krs prove takes no FILE argument"
        );
        assert_eq!(
            failure("check", &["prog.imp"]),
            "krs check takes no FILE argument"
        );
        assert_eq!(failure("run", &["a", "b"]), "more than one FILE given");
        assert_eq!(
            failure("run", &["--output", "program"]),
            "--output program applies only to krs parse"
        );
        assert_eq!(
            failure("search", &["--output", "none"]),
            "unknown --output format `none` for krs search"
        );
        assert_eq!(
            failure("run", &["-c", "ENV"]),
            "-c `ENV` must have the form NAME=TEXT"
        );
        assert_eq!(
            failure("run", &["--input", "pc"]),
            "--input `pc` must have the form NAME=JSON"
        );
        assert_eq!(
            failure("run", &["--input", "$=1"]),
            "--input `$=1` has an empty input name"
        );
        assert_eq!(
            failure("run", &["--case", "case.yaml"]),
            "--case `case.yaml` has the extension `.yaml`; a case file is `.toml` or `.json`"
        );
        assert_eq!(
            failure("search", &["--case", "case"]),
            "--case `case` has no extension; a case file is `.toml` or `.json`"
        );
        assert_eq!(
            failure("run", &["--case", "a.toml", "--case", "b.toml"]),
            "--case specified more than once"
        );
        assert_eq!(
            failure("prove", &["--input", "pc=1"]),
            "--input does not apply to krs prove"
        );
        assert_eq!(
            failure("parse", &["--case", "a.toml"]),
            "--case does not apply to krs parse"
        );
        assert_eq!(
            failure("run", &["--depth", "-1"]),
            "--depth `-1` is not a non-negative integer"
        );
        assert_eq!(
            failure("search", &["--mode", "=>!"]),
            "unknown search mode `=>!`"
        );
        assert!(
            failure("run", &["--backend", "llvm"])
                .starts_with("--backend does not apply to krs run")
        );
    }

    #[cfg(unix)]
    #[test]
    fn rejects_non_utf8_option_values() {
        use std::os::unix::ffi::OsStringExt;
        let args = vec![
            OsString::from("check"),
            OsString::from("--definition"),
            OsString::from_vec(vec![0xff]),
        ];
        assert!(
            matches!(parse(args), Err(UsageError::Message(message)) if message.contains("UTF-8"))
        );
    }

    /// The synopsis of each run-family command lists exactly the `--output`
    /// formats the parser accepts for it and every option it accepts.
    #[test]
    fn usage_synopsis_matches_the_parser() {
        let lines: Vec<&str> = USAGE.lines().collect();
        for kind in [
            CommandKind::Parse,
            CommandKind::Run,
            CommandKind::Search,
            CommandKind::Prove,
        ] {
            let head = format!("  krs {:<6} ", kind.as_str());
            let start = lines
                .iter()
                .position(|line| line.starts_with(&head))
                .unwrap_or_else(|| panic!("no synopsis for krs {}", kind.as_str()));
            let synopsis = std::iter::once(lines[start])
                .chain(
                    lines[start + 1..]
                        .iter()
                        .copied()
                        .take_while(|line| line.starts_with("             ")),
                )
                .collect::<Vec<_>>()
                .join(" ");
            let listed: Vec<&str> = synopsis
                .split("[--output ")
                .nth(1)
                .and_then(|rest| rest.split(']').next())
                .unwrap_or_else(|| panic!("no --output in the krs {} synopsis", kind.as_str()))
                .split('|')
                .collect();
            for format in ["pretty", "program", "kast", "json", "jsonl", "kore", "none"] {
                assert_eq!(
                    term_output(kind, Some(PathBuf::from(format))).is_ok(),
                    listed.contains(&format),
                    "krs {} synopsis and parser disagree on --output {format}",
                    kind.as_str()
                );
            }
            for option in exec_options(kind) {
                if HIDDEN_OPTIONS.contains(option) {
                    assert!(
                        !USAGE.contains(option),
                        "the usage shows the hidden {option}"
                    );
                    continue;
                }
                let option = if *option == "FILE" { "FILE|-" } else { option };
                assert!(
                    synopsis.contains(option),
                    "krs {} synopsis omits {option}",
                    kind.as_str()
                );
            }
        }
    }
}
