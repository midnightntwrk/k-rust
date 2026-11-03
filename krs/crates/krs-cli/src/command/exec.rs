//! `krs parse`, `krs run`, `krs search`, and `krs prove` over the prepared Definition IR.
//!
//! Each command compiles the Definition IR in-process through `krs-exec` and the k-rust symbolic backend, on a 64 MiB-stack worker.
//! The compiled stage is kept in the per-user stage cache (`stage_cache`), keyed by the Definition IR digest, so an unchanged definition is compiled once; so is the proof definition `krs prove --spec-module NAME` compiles, keyed also by NAME.
//! Results are never cached: a run depends on its inputs, and the collector and lowering stages it shares with the other commands are already incremental.
//!
//! With `KRS_CHECK_PRINTS=1`, every state `run`, `search` and `prove` print through the definition's grammar is read back, cell by cell ([`Semantics::check_prints`]), and so is the program `parse --output program` prints ([`Semantics::read_back_program`]); a print that does not read back as the state or the program fails the command ([`CommandError::PrintCheck`]), and output that reads back is printed as without the variable.
//!
//! Each print is text of the grammar its output is for: a `run`, `search` or `prove` state is a configuration value's, which a program or a `-c` value reads (a child grouped in K's default bracket is a stated fallback there, a warning); a `parse --output program` print is a program's.

use std::fmt::Write as _;
use std::io::{IsTerminal as _, Read};
use std::path::PathBuf;

use krs_diagnostic::{Code, codes};
use krs_exec::{
    CompiledStage, ConfigInputs, Coverage, CoverageOptions, ExecError, Halt, PrintStyle, Printed,
    ProgramInput, ProveOptions, REPORT_SCHEMA, ReadBack, RunOptions, SearchMode, SearchOptions,
    Semantics, SourceText, SpecStage, Step, StepOrigin, Term, Verdict,
};
use krs_ir::measure::Measurement;
use serde_json::json;

use super::stage_cache::StageCache;
use super::{Command, CommandError, CommandOutcome, PreparedDefinition, native_command_error};
use crate::DiagnosticSources;

/// Where FILE comes from.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProgramSource {
    /// A file path.
    File(PathBuf),
    /// Standard input (`-`).
    Stdin,
}

/// How a result term is printed.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum TermOutput {
    /// Grammar-directed text, as `krun --output pretty` prints it (the default of `run`, `search` and `prove`).
    Pretty,
    /// The program grammar's text, as `kast --output program` prints it (`parse` only).
    Program,
    /// Textual KAST (the default of `parse`).
    #[default]
    Kast,
    /// The `krs-exec/1` JSON report (`parse` prints the KAST JSON envelope, as `kast --output json` does).
    Json,
    /// KORE text.
    Kore,
    /// Nothing on stdout (`run` only).
    None,
}

/// Colour selection for pretty output.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ColorChoice {
    /// Colour when stdout is a terminal.
    #[default]
    Auto,
    /// Always colour.
    Always,
    /// Never colour.
    Never,
}

/// `krs parse` inputs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseRequest {
    /// `--sort`; the default is the sort of `$PGM`.
    pub sort: Option<String>,
    /// FILE, or standard input.
    pub input: ProgramSource,
    /// `--output`.
    pub output: TermOutput,
}

/// `krs run` inputs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RunRequest {
    /// FILE, bound to `$PGM`.
    pub input: Option<ProgramSource>,
    /// `-c NAME=TEXT` bindings, in command-line order.
    pub variables: Vec<(String, String)>,
    /// `--depth`.
    pub depth: Option<u64>,
    /// `--trace`.
    pub trace: bool,
    /// `--coverage`.
    pub coverage: bool,
    /// `--output`.
    pub output: TermOutput,
    /// `--color`.
    pub color: ColorChoice,
}

/// `krs search` inputs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SearchRequest {
    /// FILE, bound to `$PGM`.
    pub input: Option<ProgramSource>,
    /// `-c NAME=TEXT` bindings, in command-line order.
    pub variables: Vec<(String, String)>,
    /// `--mode`.
    pub mode: SearchMode,
    /// `--depth`.
    pub depth: Option<u64>,
    /// `--max-solutions`.
    pub max_solutions: Option<usize>,
    /// `--trace`.
    pub trace: bool,
    /// `--output`.
    pub output: TermOutput,
    /// `--color`.
    pub color: ColorChoice,
}

/// `krs prove` inputs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProveRequest {
    /// `--spec-module`: an author spec module (KF-041); `None` proves the generated `<MAIN>-SPEC`.
    pub spec_module: Option<String>,
    /// `--claim` labels; empty proves every claim.
    pub claims: Vec<String>,
    /// `--depth`.
    pub depth: Option<u64>,
    /// `--output`.
    pub output: TermOutput,
    /// `--color`.
    pub color: ColorChoice,
}

impl ColorChoice {
    /// Whether to colour: `auto` colours exactly when standard output is a terminal and `NO_COLOR` is unset.
    fn enabled(self) -> bool {
        match self {
            Self::Always => true,
            Self::Never => false,
            Self::Auto => {
                std::io::stdout().is_terminal()
                    && std::env::var_os("NO_COLOR").is_none_or(|value| value.is_empty())
            }
        }
    }
}

pub(super) const WORKER_STACK: usize = 64 * 1024 * 1024;

/// How the compiled stage is looked up and kept.
#[derive(Clone, Copy)]
pub(super) struct StageReuse<'a> {
    /// The definition's entry in the stage cache, when there is a usable store.
    pub cache: Option<&'a StageCache>,
    /// Whether a stored stage may be restored (`--no-reuse` and `KRS_NO_REUSE=1` clear it); a compiled stage is stored either way.
    pub restore: bool,
}

/// Compile the prepared definition, or restore its compiled stage, and run one parse, run, search, or prove command.
pub(super) fn execute(
    prepared: &PreparedDefinition,
    command: &Command,
    sources: &DiagnosticSources,
    reuse: StageReuse<'_>,
    measurement: &mut Measurement,
) -> Result<CommandOutcome, CommandError> {
    let sources = sources.clone();
    let timings = &mut measurement.timings;
    let definition = prepared.lowered.definition();
    let mut reused = false;
    let reused_flag = &mut reused;
    let mut spec_reused = None;
    let spec_reused_flag = &mut spec_reused;
    let result = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("krs-exec".into())
            .stack_size(WORKER_STACK)
            .spawn_scoped(scope, move || {
                let provider: SourceText = Box::new(move |file| sources.source_text(file));
                let started = std::time::Instant::now();
                let restored = reuse
                    .cache
                    .filter(|_| reuse.restore)
                    .and_then(StageCache::load);
                let stage = if let Some(stage) = restored {
                    timings.record("stage.reuse", started.elapsed().as_secs_f64(), 0);
                    *reused_flag = true;
                    stage
                } else {
                    let stage =
                        CompiledStage::compile(definition, timings).map_err(Failure::Exec)?;
                    if let Some(cache) = reuse.cache {
                        timings.span("stage.store", |_| cache.store(&stage));
                    }
                    stage
                };
                let mut semantics =
                    Semantics::from_stage(definition, stage, Some(provider), timings)
                        .map_err(Failure::Exec)?;
                if let Command::Prove(ProveRequest {
                    spec_module: Some(module),
                    ..
                }) = command
                    && semantics.spec_modules().contains(module)
                {
                    let reused =
                        load_spec_stage(&mut semantics, definition, module, reuse, timings)?;
                    *spec_reused_flag = Some(reused);
                }
                dispatch(&mut semantics, command)
            })
            .map_err(|error| {
                CommandError::InvalidRequest(format!("could not start the run worker: {error}"))
            })?
            .join()
            .map_err(|_| CommandError::InvalidRequest("the run worker panicked".into()))
    })?;
    measurement.counters.set("stage.reused", u64::from(reused));
    if let Some(reused) = spec_reused {
        measurement
            .counters
            .set("spec_stage.reused", u64::from(reused));
    }
    result.map_err(|failure| failure.into_command_error(prepared))
}

/// The definition-level judgement of `krs parse`, `run`, `search`, and `prove`, for `krs check`:
/// the stage loaded into the backend, as every run command loads it before it reads a program,
/// and the proof definition of each author spec module compiled and loaded, as
/// `krs prove --spec-module NAME` does.
///
/// `artifacts` and `context` are the definition's symbolic (Haskell-dialect) compile, the one
/// [`CompiledStage::compile`] makes; this function runs on the same worker stack as the run commands.
/// Once the definition is loaded, `visit` is made on it there, before the spec modules are loaded,
/// as the run commands' semantics stand before their program is read.
pub(super) fn judge(
    prepared: &PreparedDefinition,
    artifacts: krs_k_rust::CompiledArtifacts,
    context: krs_k_rust::ConfigurationContext,
    visit: Option<super::LoadVisit<'_>>,
    timings: &mut krs_ir::measure::Timings,
) -> Result<(), CommandError> {
    let definition = prepared.lowered.definition();
    let result = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("krs-check".into())
            .stack_size(WORKER_STACK)
            .spawn_scoped(scope, move || {
                let stage = CompiledStage::from_compiled(artifacts, context);
                let mut semantics = Semantics::from_stage(definition, stage, None, timings)
                    .map_err(Failure::Exec)?;
                if let Some(visit) = visit {
                    visit(&mut semantics);
                }
                let fresh = StageReuse {
                    cache: None,
                    restore: false,
                };
                for module in semantics.spec_modules().to_vec() {
                    load_spec_stage(&mut semantics, definition, &module, fresh, timings)?;
                }
                Ok::<(), Failure>(())
            })
            .map_err(|error| {
                CommandError::InvalidRequest(format!("could not start the check worker: {error}"))
            })?
            .join()
            .map_err(|_| CommandError::InvalidRequest("the check worker panicked".into()))
    })?;
    result.map_err(|failure| failure.into_command_error(prepared))
}

/// Restore the proof definition of the author spec module `module` from the stage cache, or compile and store it, and load it into `semantics`; returns whether it was restored.
fn load_spec_stage(
    semantics: &mut Semantics,
    definition: &krs_ir_levels::DefinitionIr,
    module: &str,
    reuse: StageReuse<'_>,
    timings: &mut krs_ir::measure::Timings,
) -> Result<bool, Failure> {
    let cache = reuse.cache.and_then(|cache| cache.for_spec_module(module));
    let started = std::time::Instant::now();
    let restored = cache
        .as_ref()
        .filter(|_| reuse.restore)
        .and_then(StageCache::load_spec);
    let reused = restored.is_some();
    let stage = if let Some(stage) = restored {
        timings.record("spec_stage.reuse", started.elapsed().as_secs_f64(), 0);
        stage
    } else {
        let stage = timings.try_span("spec_stage.compile", |timings| {
            SpecStage::compile(definition, module, timings)
        })?;
        if let Some(cache) = &cache {
            timings.span("spec_stage.store", |_| cache.store_spec(&stage));
        }
        stage
    };
    timings.try_span("spec_stage.load", |_| semantics.load_spec_stage(stage))?;
    Ok(reused)
}

/// A worker failure, converted to a [`CommandError`] on the calling thread.
enum Failure {
    Exec(ExecError),
    Usage(String),
    Serialization(serde_json::Error),
    Read(String),
    PrintCheck(String),
}

impl Failure {
    fn into_command_error(self, prepared: &PreparedDefinition) -> CommandError {
        match self {
            Self::Exec(ExecError::Compile(error)) => {
                native_command_error(prepared.lowered.source_map(), error)
            }
            Self::Exec(error) => CommandError::Exec(error),
            Self::Usage(message) => CommandError::Usage(message),
            Self::Serialization(error) => CommandError::Serialization(error),
            Self::Read(message) => CommandError::InvalidRequest(message),
            Self::PrintCheck(message) => CommandError::PrintCheck(message),
        }
    }
}

impl From<ExecError> for Failure {
    fn from(error: ExecError) -> Self {
        Self::Exec(error)
    }
}

impl From<serde_json::Error> for Failure {
    fn from(error: serde_json::Error) -> Self {
        Self::Serialization(error)
    }
}

fn read_program(source: &ProgramSource) -> Result<ProgramInput, Failure> {
    match source {
        ProgramSource::Stdin => {
            let mut text = String::new();
            std::io::stdin()
                .read_to_string(&mut text)
                .map_err(|error| {
                    Failure::Read(format!("could not read standard input: {error}"))
                })?;
            Ok(ProgramInput {
                name: "<stdin>".to_owned(),
                text,
            })
        }
        ProgramSource::File(path) => Ok(ProgramInput {
            name: path.display().to_string(),
            text: std::fs::read_to_string(path).map_err(|error| {
                Failure::Read(format!("could not read `{}`: {error}", path.display()))
            })?,
        }),
    }
}

fn dispatch(semantics: &mut Semantics, command: &Command) -> Result<CommandOutcome, Failure> {
    match command {
        Command::Parse(request) => {
            let program = read_program(&request.input)?;
            if request.output == TermOutput::Program {
                let printed =
                    semantics.unparse_program(request.sort.as_deref(), &program, false)?;
                let mut prints = PrintCheck::new(request.output);
                prints.check_program(semantics, request.sort.as_deref(), &program, &printed)?;
                prints.verdict()?;
                let mut stderr = String::new();
                write_warnings(&mut stderr, &printed);
                return Ok(outcome(format!("{}\n", printed.text), stderr, 0));
            }
            let term = semantics.parse(request.sort.as_deref(), &program)?;
            let stdout = match request.output {
                TermOutput::Json => semantics.print(&term, PrintStyle::Json)?,
                TermOutput::Kore => semantics.print(&term, PrintStyle::Kore)?,
                TermOutput::Kast | TermOutput::None | TermOutput::Pretty | TermOutput::Program => {
                    semantics.print(&term, PrintStyle::Kast)?
                }
            }
            .text;
            Ok(outcome(format!("{stdout}\n"), String::new(), 0))
        }
        Command::Run(request) => run(semantics, request),
        Command::Search(request) => search(semantics, request),
        Command::Prove(request) => prove(semantics, request),
        _ => unreachable!("only run-family commands reach the run worker"),
    }
}

fn configure(
    semantics: &mut Semantics,
    input: Option<&ProgramSource>,
    variables: &[(String, String)],
    console_input: bool,
) -> Result<krs_exec::State, Failure> {
    // FILE is checked against `$PGM` before it is read, so a stray FILE is reported as such.
    let takes_program = semantics
        .variables()
        .iter()
        .any(|variable| variable.is_main);
    match (input, takes_program) {
        (Some(_), false) => return Err(ExecError::StrayProgram.into()),
        (None, true) => return Err(ExecError::MissingProgram.into()),
        _ => {}
    }
    if input == Some(&ProgramSource::Stdin)
        && semantics
            .variables()
            .iter()
            .any(|variable| variable.name == "STDIN")
    {
        return Err(Failure::Usage(
            "FILE `-` and the stdin stream cell both read standard input".into(),
        ));
    }
    let program = input.map(read_program).transpose()?;
    let stdin = if console_input
        && semantics
            .variables()
            .iter()
            .any(|variable| variable.name == "STDIN")
    {
        Some(read_console_input()?)
    } else {
        None
    };
    Ok(semantics.configure(&ConfigInputs {
        program,
        variables: variables
            .iter()
            .map(|(name, text)| (name.clone(), text.as_str().into()))
            .collect(),
        stdin,
    })?)
}

/// Standard input for the stdin stream cell, read to end of file before the first step, as krun does.
fn read_console_input() -> Result<Vec<u8>, Failure> {
    let mut stdin = std::io::stdin();
    if stdin.is_terminal() {
        eprintln!(
            "note: reading standard input into the stdin stream cell until end of file; redirect it or end the input with Ctrl-D"
        );
    }
    let mut input = Vec::new();
    stdin
        .read_to_end(&mut input)
        .map_err(|error| Failure::Read(format!("could not read standard input: {error}")))?;
    Ok(input)
}

fn run(semantics: &mut Semantics, request: &RunRequest) -> Result<CommandOutcome, Failure> {
    let smt = semantics.capabilities().smt;
    let state = configure(semantics, request.input.as_ref(), &request.variables, true)?;
    let report = semantics.run(
        &state,
        RunOptions {
            depth: request.depth,
            trace: request.trace,
            coverage: request.coverage.then(CoverageOptions::default),
            ..RunOptions::default()
        },
    )?;
    let mut stderr = log_text(&report.log);
    if request.output != TermOutput::Json {
        write_trace(&mut stderr, &report.trace);
        if let Some(coverage) = &report.coverage {
            write_coverage(&mut stderr, coverage);
        }
    }
    let color = request.color.enabled();
    let printed = match request.output {
        TermOutput::Json => json_line(&json!({"schema": REPORT_SCHEMA, "run": report}))?,
        TermOutput::None => String::new(),
        output => format!(
            "{}\n",
            print(semantics, &report.state, output, color, &mut stderr)?
        ),
    };
    let mut prints = PrintCheck::new(request.output);
    prints.check(semantics, &report.state)?;
    prints.verdict()?;
    let head = main_cell_head(semantics, &report.state, request.output, &mut stderr);
    let _ = write!(
        stderr,
        "krs run: {} after {} step{}{head}",
        status_word(report.halt.as_str(), smt),
        report.steps,
        if report.steps == 1 { "" } else { "s" }
    );
    stderr.push('\n');
    if request.output != TermOutput::Json {
        let notation = match request.output {
            TermOutput::None => TermOutput::Pretty,
            output => output,
        };
        for term in &report.valueless {
            let printed = print(semantics, term, notation, false, &mut stderr)?;
            let printed = printed.trim();
            let _ = if report.halt == Halt::Undefined {
                writeln!(
                    stderr,
                    "note: `{printed}` has no value: its function is partial and defined by its equations alone, and none applies there, so no state holds it"
                )
            } else {
                writeln!(
                    stderr,
                    "note: a rule's condition reads `{printed}`, which has no value (its function is partial and defined by its equations alone, and none applies there), so the rule does not apply"
                )
            };
        }
    }
    let exit_code = match report.exit_code {
        Some(code) if report.halt.is_complete() => i32::try_from(code & 0xff).unwrap_or(1),
        _ => i32::from(!report.halt.is_complete()),
    };
    // Console output comes first, as krun writes it during the run and prints the result after;
    // the JSON report carries it in `stdout` instead.
    let mut stdout = match (&report.stdout, request.output) {
        (Some(console), output) if output != TermOutput::Json => console.clone(),
        _ => Vec::new(),
    };
    stdout.extend_from_slice(printed.as_bytes());
    let mut outcome = outcome(String::new(), stderr, exit_code);
    outcome.stdout = stdout;
    Ok(outcome)
}

fn search(semantics: &mut Semantics, request: &SearchRequest) -> Result<CommandOutcome, Failure> {
    let state = configure(semantics, request.input.as_ref(), &request.variables, false)?;
    let report = semantics.search(
        &state,
        SearchOptions {
            mode: request.mode,
            depth: request.depth,
            max_solutions: request.max_solutions,
            trace: request.trace,
        },
    )?;
    let truncated = request
        .max_solutions
        .is_some_and(|limit| report.solutions.len() >= limit);
    let mut stderr = log_text(&report.log);
    let mut stdout = String::new();
    let color = request.color.enabled();
    let mut prints = PrintCheck::new(request.output);
    if request.output == TermOutput::Json {
        stdout = json_line(&json!({"schema": REPORT_SCHEMA, "search": report}))?;
    } else {
        for (index, solution) in report.solutions.iter().enumerate() {
            prints.check(semantics, &solution.state)?;
            let _ = writeln!(stderr, "solution {}: depth {}", index + 1, solution.depth);
            write_trace(&mut stderr, &solution.trace);
            let text = print(
                semantics,
                &solution.state,
                request.output,
                color,
                &mut stderr,
            )?;
            let _ = writeln!(stdout, "{text}");
        }
    }
    prints.verdict()?;
    let count = report.solutions.len();
    let _ = writeln!(
        stderr,
        "krs search: {count} solution{}{}",
        if count == 1 { "" } else { "s" },
        if report.complete {
            ""
        } else if truncated {
            " (stopped at --max-solutions)"
        } else {
            " (incomplete: some paths were not decided)"
        }
    );
    Ok(outcome(
        stdout,
        stderr,
        i32::from(!report.complete && !truncated),
    ))
}

fn prove(semantics: &mut Semantics, request: &ProveRequest) -> Result<CommandOutcome, Failure> {
    let smt = semantics.capabilities().smt;
    let reports = semantics.prove(&ProveOptions {
        module: request.spec_module.clone(),
        claims: request.claims.clone(),
        depth: request.depth,
    })?;
    let proven = reports
        .iter()
        .filter(|report| report.verdict == Verdict::Proven)
        .count();
    // A trusted claim is assumed, never proven (KF-042); it does not fail the run.
    let trusted = reports
        .iter()
        .filter(|report| report.verdict == Verdict::Trusted)
        .count();
    let mut stdout = String::new();
    let mut warnings = String::new();
    let color = request.color.enabled();
    // A leaf is a printed state, as a run's and a search's are.
    let mut prints = PrintCheck::new(request.output);
    if request.output == TermOutput::Json {
        stdout = json_line(&json!({"schema": REPORT_SCHEMA, "prove": reports}))?;
    } else {
        for report in &reports {
            let _ = writeln!(
                stdout,
                "{}: {}",
                report.claim,
                status_word(report.verdict.as_str(), smt)
            );
            for leaf in &report.leaves {
                if leaf.vacuous {
                    let _ = writeln!(
                        stdout,
                        "  vacuously proven leaf at proof depth {}",
                        leaf.depth
                    );
                }
                if let Some(record) = &leaf.contradicted_total {
                    let _ = writeln!(
                        stdout,
                        "  total declaration {} contradicted by equation {}",
                        record.k_label.as_deref().unwrap_or(&record.symbol),
                        record.rule_label.as_deref().unwrap_or(&record.rule_id)
                    );
                }
                for step in &leaf.claim_steps {
                    let _ = writeln!(
                        stdout,
                        "  applied claim {} at proof depth {}",
                        step.label.as_deref().unwrap_or(&step.unique_id),
                        step.depth
                    );
                }
            }
            if matches!(report.verdict, Verdict::Proven | Verdict::Trusted) {
                continue;
            }
            for (index, leaf) in report.leaves.iter().enumerate() {
                prints.check(semantics, &leaf.state)?;
                let text = print(semantics, &leaf.state, request.output, color, &mut warnings)?;
                let _ = writeln!(
                    stdout,
                    "  leaf {} ({}, depth {}):\n{text}",
                    index + 1,
                    leaf.outcome,
                    leaf.depth,
                );
            }
        }
    }
    prints.verdict()?;
    let stderr = format!(
        "{warnings}krs prove: {proven} of {} claim{} proven{}\n",
        reports.len(),
        if reports.len() == 1 { "" } else { "s" },
        if trusted == 0 {
            String::new()
        } else {
            format!(", {trusted} trusted")
        }
    );
    Ok(outcome(
        stdout,
        stderr,
        i32::from(proven + trusted != reports.len()),
    ))
}

/// The read-back of the states a command prints through the definition's grammar, which
/// `KRS_CHECK_PRINTS=1` asks for: the prints that do not read back as their states.
struct PrintCheck {
    /// Whether the prints are checked: the variable is set and the output is the grammar's.
    enabled: bool,
    failures: Vec<String>,
}

impl PrintCheck {
    fn new(output: TermOutput) -> Self {
        let requested =
            std::env::var_os("KRS_CHECK_PRINTS").as_deref() == Some(std::ffi::OsStr::new("1"));
        Self {
            enabled: requested
                && matches!(
                    output,
                    TermOutput::Pretty | TermOutput::Program | TermOutput::None
                ),
            failures: Vec::new(),
        }
    }

    /// Read every cell of `state`, a state the command prints, back ([`Semantics::check_prints`]).
    fn check(&mut self, semantics: &mut Semantics, state: &Term) -> Result<(), Failure> {
        if self.enabled {
            for (_, read) in semantics.check_prints(state)? {
                if let ReadBack::Fails(failure) = read {
                    self.failures.push(failure);
                }
            }
        }
        Ok(())
    }

    /// Read `printed`, the print of the program `input` at `sort`, back
    /// ([`Semantics::read_back_program`]).
    fn check_program(
        &mut self,
        semantics: &mut Semantics,
        sort: Option<&str>,
        input: &ProgramInput,
        printed: &Printed,
    ) -> Result<(), Failure> {
        if self.enabled
            && let ReadBack::Fails(failure) = semantics.read_back_program(sort, input, printed)?
        {
            self.failures.push(failure);
        }
        Ok(())
    }

    /// The command's failure where a print did not read back.
    fn verdict(&mut self) -> Result<(), Failure> {
        if self.failures.is_empty() {
            return Ok(());
        }
        let mut message =
            "KRS_CHECK_PRINTS: a printed term does not read back as the term:".to_owned();
        for failure in self.failures.drain(..) {
            message.push_str("\n  ");
            message.push_str(&failure);
        }
        Err(Failure::PrintCheck(message))
    }
}

/// A status word, marked when it is `indeterminate` in a build without an SMT solver.
/// The `io::log` lines, one per line, as krun writes them to standard error while it rewrites.
fn log_text(lines: &[String]) -> String {
    lines.iter().fold(String::new(), |mut text, line| {
        text.push_str(line);
        text.push('\n');
        text
    })
}

fn status_word(word: &str, smt: bool) -> String {
    if word == "indeterminate" && !smt {
        "indeterminate (no SMT solver)".to_owned()
    } else {
        word.to_owned()
    }
}

/// The status line's description of the result's main cell, the computation
/// ([`Semantics::main_cell`], `<k>` or another name): `; <prog> starts with ` and its first item
/// in backquotes, `; <prog> is empty`, or nothing without a main cell.
///
/// The item is printed in the notation the result itself is printed in, so the line names the same term
/// the reader sees above it: grammar-directed text for `pretty` and for `none` (which prints no
/// result, and whose reader gets the default notation), KAST for `kast` and `json`, KORE for
/// `kore`. The grammar-directed print's warnings go to `stderr`, each the print of the whole result
/// has not reported already: the item printed alone has no parent position, and can fall back
/// where the whole print did not.
fn main_cell_head(
    semantics: &Semantics,
    state: &Term,
    output: TermOutput,
    stderr: &mut String,
) -> String {
    let Some(cell) = semantics.main_cell() else {
        return String::new();
    };
    let head = match output {
        TermOutput::Pretty | TermOutput::Program | TermOutput::None => {
            semantics.unparse_computation_head(state).map(|head| {
                head.map(|printed| {
                    // The head printed alone can say what the whole print did not: its own
                    // warnings are written, each the whole print has not written already.
                    for warning in &printed.warnings {
                        let line = format!("warning: {warning}\n");
                        if !stderr.contains(&line) {
                            stderr.push_str(&line);
                        }
                    }
                    printed.text
                })
            })
        }
        TermOutput::Kast | TermOutput::Json => state.computation_head(cell),
        TermOutput::Kore => state
            .computation_head_kore(cell)
            .map(|head| head.map(ToString::to_string)),
    };
    match head {
        Some(Some(item)) => format!("; <{cell}> starts with `{item}`"),
        Some(None) => format!("; <{cell}> is empty"),
        None => String::new(),
    }
}

/// Print a result term; a pretty print's warnings go to `stderr`.
fn print(
    semantics: &Semantics,
    term: &Term,
    output: TermOutput,
    color: bool,
    stderr: &mut String,
) -> Result<String, Failure> {
    let style = match output {
        TermOutput::Pretty | TermOutput::Program => {
            let printed = semantics.unparse(term, color);
            write_warnings(stderr, &printed);
            return Ok(printed.text);
        }
        TermOutput::Kore => PrintStyle::Kore,
        TermOutput::Json => PrintStyle::Json,
        TermOutput::Kast | TermOutput::None => PrintStyle::Kast,
    };
    Ok(semantics.print(term, style)?.text)
}

/// One `warning:` line per problem that degraded a grammar-directed print.
fn write_warnings(stderr: &mut String, printed: &Printed) {
    for warning in &printed.warnings {
        let _ = writeln!(stderr, "warning: {warning}");
    }
}

fn json_line(value: &serde_json::Value) -> Result<String, Failure> {
    let mut line = serde_json::to_string(value)?;
    line.push('\n');
    Ok(line)
}

const fn outcome(stdout: String, stderr: String, exit_code: i32) -> CommandOutcome {
    CommandOutcome {
        stdout: stdout.into_bytes(),
        stderr: stderr.into_bytes(),
        exit_code,
        warnings: crate::DiagnosticReports {
            envelopes: Vec::new(),
        },
    }
}

/// One trace line per step: `step N  LABEL   FILE:LINE:COLUMN`, or `step N  (LABEL, generated by PASS)  from FILE:LINE:COLUMN`.
fn write_trace(output: &mut String, steps: &[Step]) {
    for step in steps {
        let name = step.label.as_deref().unwrap_or(&step.rule_id);
        let _ = match &step.origin {
            StepOrigin::Authored { file, line, column } => {
                let position = match (line, column) {
                    (Some(line), Some(column)) => format!(":{line}:{column}"),
                    _ => String::new(),
                };
                writeln!(output, "step {}  {name}   {file}{position}", step.index)
            }
            StepOrigin::Generated { pass, from } => {
                let name = step.label.as_deref().unwrap_or("rule");
                match from {
                    Some(span) => writeln!(
                        output,
                        "step {}  ({name}, generated by {pass})  from {span}",
                        step.index
                    ),
                    None => writeln!(output, "step {}  ({name}, generated by {pass})", step.index),
                }
            }
            StepOrigin::Builtin { module } => {
                writeln!(output, "step {}  {name}   (builtin {module})", step.index)
            }
        };
    }
}

/// One line per rule and equation of the definition a run covered, the strongest predicate that
/// holds of it first: `committed` (a path took its step), `applied` with the number of times, or
/// `matched` (its condition was begun for a matched instance). A rule is named by its KRS item
/// when it has one, else by its label; the sentences of K's builtin closure are counted on a last
/// line, and `--output json` lists them.
fn write_coverage(output: &mut String, coverage: &Coverage) {
    let mut builtin = 0_usize;
    let mut rows = Vec::new();
    for rule in &coverage.rules {
        if matches!(rule.origin, StepOrigin::Builtin { .. }) {
            builtin += 1;
            continue;
        }
        let predicate = if rule.committed {
            format!("committed ×{}", rule.applications)
        } else if rule.applied {
            format!("applied ×{}", rule.applications)
        } else if rule.matched {
            "matched".to_owned()
        } else {
            "offered".to_owned()
        };
        let name = rule
            .item
            .as_deref()
            .or(rule.label.as_deref())
            .unwrap_or(&rule.rule_id);
        let kind = rule.kind.map_or("rule", krs_exec::RuleKind::as_str);
        let origin = match &rule.origin {
            StepOrigin::Authored { file, line, column } => match (line, column) {
                (Some(line), Some(column)) => format!("{file}:{line}:{column}"),
                _ => file.clone(),
            },
            StepOrigin::Generated {
                pass,
                from: Some(span),
            } => format!("generated by {pass} from {span}"),
            StepOrigin::Generated { pass, from: None } => format!("generated by {pass}"),
            StepOrigin::Builtin { .. } => unreachable!("builtin sentences are counted"),
        };
        rows.push((name.to_owned(), predicate, kind, origin));
    }
    rows.sort();
    for (name, predicate, kind, origin) in rows {
        let _ = writeln!(output, "coverage  {predicate}  {name}  ({kind})  {origin}");
    }
    if builtin > 0 {
        let _ = writeln!(
            output,
            "coverage  and {builtin} more of K's builtin modules"
        );
    }
}

/// The registered code of an exec failure.
pub(super) const fn diagnostic_code(error: &ExecError) -> Code {
    match error {
        ExecError::Compile(_) | ExecError::Backend(_) => codes::exec::BACKEND,
        ExecError::StrayProgram | ExecError::MissingProgram => codes::exec::PROGRAM,
        ExecError::UnknownVariable { .. }
        | ExecError::DuplicateVariable(_)
        | ExecError::MissingVariables(_)
        | ExecError::Value { .. } => codes::exec::VARIABLE,
        ExecError::CollectionElementSort(_) => codes::exec::COLLECTION_ELEMENT_SORT,
        ExecError::Parse { .. } => codes::exec::PARSE,
        ExecError::UnknownSort { .. } | ExecError::NoProgramSort => codes::exec::SORT,
        ExecError::UnknownClaim { .. }
        | ExecError::AmbiguousClaim { .. }
        | ExecError::NoClaims
        | ExecError::NoSpecClaims(_)
        | ExecError::UnknownSpecModule { .. } => codes::exec::CLAIM,
        ExecError::UnknownRule { .. } | ExecError::AmbiguousRule { .. } => codes::exec::RULE,
        ExecError::SearchWithStreams => codes::exec::STREAMS,
        ExecError::Unavailable(_) => codes::exec::UNAVAILABLE,
        ExecError::Result(_) => codes::exec::RESULT,
        ExecError::Undecided(_) => codes::exec::UNDECIDED,
    }
}

impl From<ExecError> for CommandError {
    fn from(error: ExecError) -> Self {
        Self::Exec(error)
    }
}

#[cfg(test)]
mod tests {
    use super::{log_text, status_word, write_coverage, write_trace};
    use krs_exec::{Coverage, CoveredRule, RuleKind, SourceSpan, Step, StepOrigin};

    #[test]
    fn indeterminate_results_name_a_missing_solver() {
        assert_eq!(
            status_word("indeterminate", false),
            "indeterminate (no SMT solver)"
        );
        assert_eq!(status_word("indeterminate", true), "indeterminate");
        assert_eq!(status_word("stuck", false), "stuck");
    }

    #[test]
    fn log_lines_end_with_a_newline_each() {
        assert_eq!(log_text(&[]), "");
        assert_eq!(log_text(&["a".into(), "b c".into()]), "a\nb c\n");
    }

    #[test]
    fn trace_lines_name_the_label_and_origin() {
        let mut output = String::new();
        write_trace(
            &mut output,
            &[
                Step {
                    index: 1,
                    label: Some("KRS-TOUR-MINIMAL.foo-to-bar".to_owned()),
                    rule_id: "id1".to_owned(),
                    origin: StepOrigin::Authored {
                        file: "src/lib.rs".to_owned(),
                        line: Some(42),
                        column: Some(5),
                    },
                },
                Step {
                    index: 4,
                    label: Some("heat".to_owned()),
                    rule_id: "id4".to_owned(),
                    origin: StepOrigin::Generated {
                        pass: "strict".to_owned(),
                        from: Some(SourceSpan {
                            file: "src/imp.rs".to_owned(),
                            line: Some(57),
                            column: Some(5),
                        }),
                    },
                },
            ],
        );
        assert_eq!(
            output,
            "step 1  KRS-TOUR-MINIMAL.foo-to-bar   src/lib.rs:42:5\nstep 4  (heat, generated by strict)  from src/imp.rs:57:5\n"
        );
    }

    #[test]
    fn coverage_lines_name_the_item_the_strongest_predicate_and_the_origin() {
        let rule =
            |id: &str, item: Option<&str>, kind, origin, applications, committed| CoveredRule {
                rule_id: id.to_owned(),
                label: Some(format!("NAT.krsRule_{id}")),
                item: item.map(str::to_owned),
                kind: Some(kind),
                origin,
                matched: true,
                applied: applications > 0,
                applications,
                committed,
            };
        let authored = |line| StepOrigin::Authored {
            file: "src/lib.rs".to_owned(),
            line: Some(line),
            column: Some(1),
        };
        let mut output = String::new();
        write_coverage(
            &mut output,
            &Coverage {
                offered: false,
                rules: vec![
                    rule(
                        "e2",
                        Some("plus_zero"),
                        RuleKind::Equation,
                        authored(31),
                        1,
                        false,
                    ),
                    rule(
                        "e1",
                        Some("plus_succ"),
                        RuleKind::Equation,
                        authored(38),
                        2,
                        false,
                    ),
                    rule("r1", Some("step"), RuleKind::Rule, authored(50), 3, true),
                    rule("r2", None, RuleKind::Rule, authored(60), 0, false),
                    rule(
                        "b1",
                        None,
                        RuleKind::Simplification,
                        StepOrigin::Builtin {
                            module: "MAP".to_owned(),
                        },
                        1,
                        false,
                    ),
                ],
            },
        );
        assert_eq!(
            output,
            "coverage  matched  NAT.krsRule_r2  (rule)  src/lib.rs:60:1\n\
             coverage  applied ×2  plus_succ  (equation)  src/lib.rs:38:1\n\
             coverage  applied ×1  plus_zero  (equation)  src/lib.rs:31:1\n\
             coverage  committed ×3  step  (rule)  src/lib.rs:50:1\n\
             coverage  and 1 more of K's builtin modules\n"
        );
    }
}
