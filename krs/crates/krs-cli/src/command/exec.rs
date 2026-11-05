//! `krs parse`, `krs run`, `krs search`, and `krs prove` over the prepared Definition IR.
//!
//! Each command compiles the Definition IR in-process through `krs-exec` and the k-rust symbolic backend, on a 64 MiB-stack worker.
//! The compiled stage is kept in the per-user stage cache (`stage_cache`), keyed by the Definition IR digest, so an unchanged definition is compiled once; so is the proof definition `krs prove --spec-module NAME` compiles, keyed also by NAME.
//! Results are never cached: a run depends on its inputs, and the collector and lowering stages it shares with the other commands are already incremental.
//!
//! With `KRS_CHECK_PRINTS=1`, every state `run`, `search` and `prove` print through the definition's grammar is read back, cell by cell ([`Semantics::check_prints`]), and so is the program `parse --output program` prints ([`Semantics::read_back_program`]); a print that does not read back as the state or the program fails the command ([`CommandError::PrintCheck`]), and output that reads back is printed as without the variable.
//!
//! Each print is text of the grammar its output is for: a `run`, `search` or `prove` state is a configuration value's, which a program or a `-c` value reads (a child grouped in K's default bracket is a stated fallback there, a warning); a `parse --output program` print is a program's.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::io::{IsTerminal as _, Read};
use std::path::{Path, PathBuf};

use krs_diagnostic::{Code, codes};
use krs_exec::{
    BackendOptions, Case, CaseDocument, Compared, CompiledStage, ConfigInputs, ConfigValue,
    Coverage, CoverageOptions, Difference, DifferenceAt, EndError, Ends, ExecError, Expectation,
    Halt, InputError, InputFiles, PrintStyle, Printed, ProgramFile, ProgramInput, ProofReport,
    ProveOptions, RUN_REPORT_SCHEMA, ReadBack, Rendered, RunOptions, RunReport,
    SEARCH_REPORT_SCHEMA, SearchMode, SearchOptions, Semantics, Side, SolverReport, SourceText,
    SpecStage, Step, StepOrigin, StopAt, StopCriterion, Term, Verdict, canonical_text,
    json_document, open_values,
};
use krs_ir::measure::{Measurement, Timings};
use krs_ir_levels::DefinitionIr;
use serde_json::json;

use super::stage_cache::StageCache;
use super::supervisor::{self, ProveOutput};
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
    /// The `krs-exec` JSON report (`parse` prints the KAST JSON envelope, as `kast --output json` does).
    Json,
    /// One `krs-exec/2` JSON document per line: a proof report as each claim ends, then a summary
    /// (`prove` only).
    JsonLines,
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
    /// `--sort`; the default is the main parameter's sort.
    pub sort: Option<String>,
    /// FILE, or standard input.
    pub input: ProgramSource,
    /// `--output`.
    pub output: TermOutput,
}

/// `krs run` inputs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RunRequest {
    /// FILE, bound to the main parameter.
    pub input: Option<ProgramSource>,
    /// `--case FILE`: a case document, whose inputs are bound by name, whose `run` table gives
    /// the depth, the stop rules and the stop count, and whose expectation the run is checked
    /// against.
    pub case: Option<PathBuf>,
    /// `--case-name NAME`: the case of that name in a document of named cases.
    pub case_name: Option<String>,
    /// `--input NAME=JSON` bindings, each a document of the typed encoding, in command-line order.
    pub inputs: Vec<(String, String)>,
    /// `-c NAME=TEXT` bindings, in command-line order.
    pub variables: Vec<(String, String)>,
    /// `--depth`.
    pub depth: Option<u64>,
    /// `--stop-before`, `--stop-after` and `--stop-count`.
    pub stop: StopCriterion,
    /// `--trace`.
    pub trace: bool,
    /// `--coverage`.
    pub coverage: bool,
    /// `--output`.
    pub output: TermOutput,
    /// `--color`.
    pub color: ColorChoice,
    /// `--smt-resource-limit`, `--smt-clock-ms` and `--smt-retries`.
    pub solver: BackendOptions,
    /// `--view-budget`: the polls each evaluation of a view of the case's expectation may take
    /// ([`DEFAULT_VIEW_BUDGET`] by default).
    pub view_budget: u64,
}

/// The polls an evaluation of a view may take unless `--view-budget` says otherwise
/// ([`krs_exec::views`], "Evaluation"): a count of the evaluation's own work, so that whether it
/// stops does not depend on the host's speed or load. A view is a function of one cell's value,
/// and the views corpora apply end in a few polls a value (a view of a short log in fewer than
/// ten), while a simplification polls about a million times a second on a desktop core (measured
/// on a function that recurses for ever), so this bound, about half a minute of such
/// work, stops in practice only an evaluation that does not end; that one is then inconclusive,
/// never a verdict of its own.
pub const DEFAULT_VIEW_BUDGET: u64 = 30_000_000;

/// `krs search` inputs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SearchRequest {
    /// FILE, bound to the main parameter.
    pub input: Option<ProgramSource>,
    /// `--case FILE`: a case document, whose inputs are bound by name, whose `run` table gives
    /// the depth, and whose expectation every solution is checked against.
    pub case: Option<PathBuf>,
    /// `--case-name NAME`: the case of that name in a document of named cases.
    pub case_name: Option<String>,
    /// `--input NAME=JSON` bindings, each a document of the typed encoding, in command-line order.
    pub inputs: Vec<(String, String)>,
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
    /// `--smt-resource-limit`, `--smt-clock-ms` and `--smt-retries`.
    pub solver: BackendOptions,
    /// `--view-budget`: the polls each evaluation of a view of the case's expectation may take
    /// ([`DEFAULT_VIEW_BUDGET`] by default).
    pub view_budget: u64,
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
    /// `--worker-protocol` (hidden): this process proves the claims for a supervising `krs prove`,
    /// writing the events of [`supervisor`] on stdout instead of the output; the claims are
    /// proved in this process, without a supervisor, when this is false and the command is
    /// executed as a library call.
    pub worker: bool,
    /// `--smt-resource-limit`, `--smt-clock-ms` and `--smt-retries`.
    pub solver: BackendOptions,
    /// `--claim-timeout`: the wall-clock time each claim's proof may take
    /// ([`ProveOptions::claim_timeout`]).
    pub claim_timeout: Option<std::time::Duration>,
}

impl ColorChoice {
    /// Whether to colour: `auto` colours exactly when standard output is a terminal and `NO_COLOR` is unset.
    pub(super) fn enabled(self) -> bool {
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

/// The observer definition a case's views are resolved and evaluated in, when the case names
/// one other than the definition it runs on: its Definition IR and its entry in the stage cache.
pub(super) struct ObserverDefinition {
    /// Its Definition IR, composed with the definition the case runs on.
    pub definition: DefinitionIr,
    /// Its entry in the stage cache, when there is a usable store.
    pub cache: Option<StageCache>,
}

/// The compiled stage of `definition`: restored from its entry in the stage cache when `reuse`
/// allows, else compiled and stored; returns it with whether it was restored.
pub(super) fn compiled_stage(
    definition: &DefinitionIr,
    reuse: StageReuse<'_>,
    timings: &mut Timings,
) -> Result<(CompiledStage, bool), ExecError> {
    let started = std::time::Instant::now();
    let restored = reuse
        .cache
        .filter(|_| reuse.restore)
        .and_then(StageCache::load);
    if let Some(stage) = restored {
        timings.record("stage.reuse", started.elapsed().as_secs_f64(), 0);
        return Ok((stage, true));
    }
    let stage = CompiledStage::compile(definition, timings)?;
    if let Some(cache) = reuse.cache {
        timings.span("stage.store", |_| cache.store(&stage));
    }
    Ok((stage, false))
}

/// The semantics of the observer `observer`, its stage restored or compiled as `restore` allows.
fn load_observer(
    observer: &ObserverDefinition,
    restore: bool,
    solver: BackendOptions,
    timings: &mut Timings,
) -> Result<Semantics, ExecError> {
    let reuse = StageReuse {
        cache: observer.cache.as_ref(),
        restore,
    };
    let (stage, _) = compiled_stage(&observer.definition, reuse, timings)?;
    Semantics::from_stage_with_solver(&observer.definition, stage, None, solver, timings)
}

/// Compile the prepared definition, or restore its compiled stage, and run one parse, run, search, or prove command.
///
/// `read` is what was read of a `run`'s or `search`'s case before the definition was loaded: the
/// case, and the observer definition its views are evaluated in, when it names one.
pub(super) fn execute(
    prepared: &PreparedDefinition,
    command: &Command,
    sources: &DiagnosticSources,
    reuse: StageReuse<'_>,
    read: ReadCase,
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
                let (stage, reused) =
                    compiled_stage(definition, reuse, timings).map_err(Failure::Exec)?;
                *reused_flag = reused;
                let mut semantics = Semantics::from_stage_with_solver(
                    definition,
                    stage,
                    Some(provider),
                    command.solver(),
                    timings,
                )
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
                let ReadCase { case, observer } = read;
                let mut observer = observer
                    .map(|observer| {
                        load_observer(&observer, reuse.restore, command.solver(), timings)
                    })
                    .transpose()
                    .map_err(Failure::Exec)?;
                dispatch(&mut semantics, observer.as_mut(), command, case)
            })
            .map_err(|error| {
                CommandError::InvalidRequest(format!("could not start the run worker: {error}"))
            })?
            .join()
            .map_err(|_| {
                // A worker of a supervising `krs prove` that panics has crashed on the claim it
                // was proving: it ends with a status krs never returns otherwise, so the
                // supervisor records that claim `crashed` and proves the rest in a new worker.
                if matches!(command, Command::Prove(ProveRequest { worker: true, .. })) {
                    let _ = std::io::Write::flush(&mut std::io::stdout());
                    std::process::exit(krs_exec::PANIC_EXIT_STATUS);
                }
                CommandError::InvalidRequest("the run worker panicked".into())
            })
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
pub(super) enum Failure {
    Exec(ExecError),
    Usage(String),
    Serialization(serde_json::Error),
    Read(String),
    PrintCheck(String),
}

impl Failure {
    /// The failure as one line of text, for a report that goes on past it (`krs cases`).
    pub(super) fn reason(&self) -> String {
        match self {
            Self::Exec(error) => error.to_string(),
            Self::Usage(message) | Self::Read(message) | Self::PrintCheck(message) => {
                message.clone()
            }
            Self::Serialization(error) => error.to_string(),
        }
    }

    pub(super) fn into_command_error(self, prepared: &PreparedDefinition) -> CommandError {
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

/// FILE's name and text, for `parse`, which reads it as a program.
fn read_program(source: &ProgramSource) -> Result<ProgramInput, Failure> {
    let (name, bytes) = read_program_bytes(source)?;
    let text = String::from_utf8(bytes)
        .map_err(|error| Failure::Read(format!("could not read `{name}`: {error}")))?;
    Ok(ProgramInput { name, text })
}

/// FILE's name and bytes, read whole, for the main parameter to read as its type says
/// ([`Semantics::program_file`]).
fn read_program_bytes(source: &ProgramSource) -> Result<(String, Vec<u8>), Failure> {
    match source {
        ProgramSource::Stdin => {
            let mut bytes = Vec::new();
            std::io::stdin().read_to_end(&mut bytes).map_err(|error| {
                Failure::Read(format!("could not read standard input: {error}"))
            })?;
            Ok(("<stdin>".to_owned(), bytes))
        }
        ProgramSource::File(path) => Ok((
            path.display().to_string(),
            std::fs::read(path).map_err(|error| {
                Failure::Read(format!("could not read `{}`: {error}", path.display()))
            })?,
        )),
    }
}

fn dispatch(
    semantics: &mut Semantics,
    observer: Option<&mut Semantics>,
    command: &Command,
    case: Option<SelectedCase>,
) -> Result<CommandOutcome, Failure> {
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
                TermOutput::Kast
                | TermOutput::JsonLines
                | TermOutput::None
                | TermOutput::Pretty
                | TermOutput::Program => semantics.print(&term, PrintStyle::Kast)?,
            }
            .text;
            Ok(outcome(format!("{stdout}\n"), String::new(), 0))
        }
        Command::Run(request) => run(semantics, observer, request, case),
        Command::Search(request) => search(semantics, observer, request, case),
        Command::Prove(request) => prove(semantics, request),
        _ => unreachable!("only run-family commands reach the run worker"),
    }
}

/// The inputs of a run or search: FILE, `--case`, `--input` and `-c`, which [`configure`] binds
/// in that order.
#[derive(Clone, Copy)]
pub(super) struct Inputs<'a> {
    program: Option<&'a ProgramSource>,
    case: Option<&'a SelectedCase>,
    typed: &'a [(String, String)],
    variables: &'a [(String, String)],
}

impl<'a> Inputs<'a> {
    /// The inputs of `case` alone, as `krs cases` binds them.
    pub(super) const fn of_case(case: &'a SelectedCase) -> Self {
        Self {
            program: None,
            case: Some(case),
            typed: &[],
            variables: &[],
        }
    }

    fn of_run(request: &'a RunRequest, case: Option<&'a SelectedCase>) -> Self {
        Self {
            program: request.input.as_ref(),
            case,
            typed: &request.inputs,
            variables: &request.variables,
        }
    }

    fn of_search(request: &'a SearchRequest, case: Option<&'a SelectedCase>) -> Self {
        Self {
            program: request.input.as_ref(),
            case,
            typed: &request.inputs,
            variables: &request.variables,
        }
    }
}

/// The case `--case` and `--case-name` select, with the directory its document's paths are
/// relative to.
pub(super) struct SelectedCase {
    pub(super) case: Case,
    /// The case file as given, for messages.
    pub(super) path: PathBuf,
    /// The case file's directory.
    pub(super) base: PathBuf,
}

impl SelectedCase {
    fn files(&self) -> CaseFiles {
        CaseFiles {
            base: self.base.clone(),
        }
    }

    /// The expectation of `case`, if any, read against the definition, refused before the run
    /// for what every comparison of it would refuse; `None` without a case or an expectation.
    pub(super) fn expectation_of(
        case: Option<&Self>,
        semantics: &Semantics,
    ) -> Result<Option<Expectation>, Failure> {
        let Some((case, expect)) = case.and_then(|case| Some((case, case.case.expect.as_ref()?)))
        else {
            return Ok(None);
        };
        case.expectation(semantics, expect).map(Some)
    }

    fn expectation(
        &self,
        semantics: &Semantics,
        expect: &serde_json::Value,
    ) -> Result<Expectation, Failure> {
        semantics
            .expectation(expect, self.case.file.as_deref(), &mut self.files())
            .map_err(|error| Failure::Exec(self.refusal(&error.to_string())))
    }

    /// A refusal of the case, naming its file and its name.
    pub(super) fn refusal(&self, message: &str) -> ExecError {
        ExecError::Case(match &self.case.name {
            Some(name) => format!("case `{name}` of `{}`: {message}", self.path.display()),
            None => format!("case `{}`: {message}", self.path.display()),
        })
    }

    /// The run's stop criterion: the stop flags' (`--stop-before`, `--stop-after`,
    /// `--stop-count`) or the case's `run` stops (`stop_before`, `stop_after`, `stop_count`),
    /// which may not both be given: each says where the run ends, and one source bounds it.
    pub(super) fn stop(&self, flags: &StopCriterion) -> Result<StopCriterion, Failure> {
        let own = self
            .case
            .run
            .as_ref()
            .map_or(StopCriterion::None, krs_exec::CaseRun::stop);
        match (flags, own) {
            (StopCriterion::None, own) => Ok(own),
            (flags, StopCriterion::None) => Ok(flags.clone()),
            _ => Err(Failure::Usage(format!(
                "--stop-before, --stop-after and --stop-count, and the `run` stops of the case `{}`, both say where the run ends; give one",
                self.path.display()
            ))),
        }
    }

    /// The run's depth bound: `--depth` or the case's `run.depth`, which may not both be given.
    pub(super) fn depth(&self, flag: Option<u64>) -> Result<Option<u64>, Failure> {
        let own = self.case.run.as_ref().and_then(|run| run.depth);
        match (flag, own) {
            (Some(_), Some(_)) => Err(Failure::Usage(format!(
                "--depth and the `run.depth` of the case `{}` both bound the run; give one",
                self.path.display()
            ))),
            (flag, own) => Ok(flag.or(own)),
        }
    }
}

/// The files a case or an `--input` document names, read from the filesystem.
///
/// A path is relative to the directory of the document that names it: the case file's, the
/// data file's that includes it, or the working directory for an `--input` document. A file is
/// named by its canonical path, which is what tells a `$data-file` that includes itself from
/// one that includes another file of the same spelling.
struct CaseFiles {
    /// The directory of the top document's paths.
    base: PathBuf,
}

impl InputFiles for CaseFiles {
    fn read(&mut self, from: Option<&str>, path: &str) -> Result<(String, Vec<u8>), String> {
        let directory = match from {
            Some(from) => Path::new(from)
                .parent()
                .map_or_else(PathBuf::new, Path::to_path_buf),
            None => self.base.clone(),
        };
        let written = directory.join(path);
        let resolved = written
            .canonicalize()
            .map_err(|error| format!("could not read `{}`: {error}", written.display()))?;
        let name = resolved
            .to_str()
            .ok_or_else(|| format!("`{}` is not a UTF-8 path", resolved.display()))?
            .to_owned();
        let bytes = std::fs::read(&resolved)
            .map_err(|error| format!("could not read `{name}`: {error}"))?;
        Ok((name, bytes))
    }
}

/// The case `--case FILE` and `--case-name NAME` select, if any, and the run's depth bound:
/// `--depth` (`flag`) or the case's `run.depth`. The case is `read` when it was read before the
/// definition was loaded, and read here otherwise, which reports what is wrong with it.
fn case_and_depth(
    read: Option<SelectedCase>,
    path: Option<&Path>,
    name: Option<&str>,
    flag: Option<u64>,
) -> Result<(Option<SelectedCase>, Option<u64>), Failure> {
    let Some(path) = path else {
        return Ok((None, flag));
    };
    let case = match read {
        Some(case) => case,
        None => read_case(path, name)?,
    };
    let depth = case.depth(flag)?;
    Ok((Some(case), depth))
}

/// The most case names a message lists.
const LISTED_NAMES: usize = 10;

/// `names` as a message lists them: the first [`LISTED_NAMES`], then how many more.
fn listed_names<'a>(names: impl Iterator<Item = &'a str>) -> String {
    let names = names.collect::<Vec<_>>();
    let mut listed = names
        .iter()
        .take(LISTED_NAMES)
        .map(|name| format!("`{name}`"))
        .collect::<Vec<_>>()
        .join(", ");
    if names.len() > LISTED_NAMES {
        let _ = write!(listed, ", and {} more", names.len() - LISTED_NAMES);
    }
    if listed.is_empty() {
        listed.push_str("none");
    }
    listed
}

/// The case document `path` states, read by its extension (`.toml` or `.json`, which the
/// command line checked), with the directory its paths are relative to.
pub(super) fn read_case_document(path: &Path) -> Result<(CaseDocument, PathBuf), Failure> {
    let text = std::fs::read_to_string(path).map_err(|error| {
        Failure::Read(format!(
            "could not read the case `{}`: {error}",
            path.display()
        ))
    })?;
    let base = path.parent().map_or_else(PathBuf::new, Path::to_path_buf);
    let mut files = CaseFiles { base: base.clone() };
    // The document's own file, named as `files` names every file it reads, so that a file it
    // includes that includes it back is a cycle.
    let top = path
        .canonicalize()
        .ok()
        .and_then(|resolved| resolved.to_str().map(str::to_owned));
    let document = if path
        .extension()
        .is_some_and(|extension| extension == "json")
    {
        CaseDocument::from_json(&text, top.as_deref(), &mut files)
    } else {
        CaseDocument::from_toml(&text, top.as_deref(), &mut files)
    }
    .map_err(|error| {
        Failure::Exec(ExecError::Case(format!(
            "case `{}`: {error}",
            path.display()
        )))
    })?;
    Ok((document, base))
}

/// The case `--case FILE` and `--case-name NAME` select: the document `path` states, read by its
/// extension (`.toml` or `.json`, which the command line checked), and its one case or its case
/// named `name`.
fn read_case(path: &Path, name: Option<&str>) -> Result<SelectedCase, Failure> {
    let (document, base) = read_case_document(path)?;
    let case = match (document, name) {
        (CaseDocument::One(case), None) => case,
        (CaseDocument::One(_), Some(name)) => {
            return Err(Failure::Usage(format!(
                "--case-name `{name}`: the case document `{}` holds one case, which has no name; omit --case-name",
                path.display()
            )));
        }
        (document @ CaseDocument::Named(_), None) => {
            return Err(Failure::Usage(format!(
                "the case document `{}` holds named cases; select one with --case-name NAME: {}",
                path.display(),
                listed_names(document.names())
            )));
        }
        (document @ CaseDocument::Named(_), Some(name)) => {
            // A name the document does not hold is an error in the command line, as a missing
            // or a superfluous one is: each is corrected in `--case-name`.
            let Some(case) = document.named(name).cloned() else {
                return Err(Failure::Usage(format!(
                    "--case-name `{name}`: the case document `{}` holds no case of that name; its cases are {}",
                    path.display(),
                    listed_names(document.names())
                )));
            };
            case
        }
    };
    Ok(SelectedCase {
        case,
        path: path.to_path_buf(),
        base,
    })
}

/// What a `run` or `search` reads of its case before the definition is loaded
/// ([`execute`]): the case, read once, and the observer definition its views are evaluated in,
/// prepared, when it names one.
#[derive(Default)]
pub(super) struct ReadCase {
    /// The case `--case FILE` and `--case-name NAME` select; `None` with no `--case`, and for a
    /// case that cannot be read, which the run reads again and refuses.
    pub case: Option<SelectedCase>,
    /// The observer definition its expectation names, prepared.
    pub observer: Option<ObserverDefinition>,
}

/// The case `--case FILE` and `--case-name NAME` select, if it can be read; `None` otherwise,
/// and the run reads it again and refuses it.
pub(super) fn readable_case(path: &Path, name: Option<&str>) -> Option<SelectedCase> {
    read_case(path, name).ok()
}

/// The observer the expectation of `case` names where the definition must prepare it: one named
/// beside a table of views that names a view. An observer named without one is refused with the
/// expectation, before the run, and is not prepared for nothing.
pub(super) fn named_observer(case: &Case) -> Option<&str> {
    let expect = case.expect.as_ref()?;
    expect
        .get("views")
        .and_then(serde_json::Value::as_object)
        .filter(|views| !views.is_empty())?;
    expect.get("observer")?.as_str()
}

/// The views and the observer the expectation of `case` names, as it writes them: a record of a
/// case refused before its expectation was checked still names what the case observes.
pub(super) fn written_views(case: &Case) -> (BTreeMap<String, String>, Option<String>) {
    let Some(expect) = case.expect.as_ref() else {
        return (BTreeMap::new(), None);
    };
    let views = expect
        .get("views")
        .and_then(serde_json::Value::as_object)
        .map(|views| {
            views
                .iter()
                .filter_map(|(cell, function)| Some((cell.clone(), function.as_str()?.to_owned())))
                .collect()
        })
        .unwrap_or_default();
    let observer = expect
        .get("observer")
        .and_then(serde_json::Value::as_str)
        .map(str::to_owned);
    (views, observer)
}

/// The value the `--input NAME=JSON` document `document` gives the input `name`.
fn typed_input(
    semantics: &Semantics,
    name: &str,
    document: &str,
    files: &mut CaseFiles,
) -> Result<ConfigValue, Failure> {
    let parameter = semantics.parameter(name)?;
    let document = json_document(document).map_err(|error| {
        ExecError::Input(InputError {
            parameter: Some(parameter.name.clone()),
            declared: Some(parameter.ty.to_string()),
            ..error
        })
    })?;
    Ok(semantics.decode_input(name, &document, files)?)
}

pub(super) fn configure(
    semantics: &mut Semantics,
    inputs: Inputs<'_>,
    console_input: bool,
) -> Result<krs_exec::State, Failure> {
    let Inputs {
        program: input,
        case,
        typed,
        variables,
    } = inputs;
    // FILE is checked against the main parameter before it is read, so a stray FILE is
    // reported as such; an unbound main parameter is reported by `configure`.
    if input.is_some() {
        semantics.program_parameter()?;
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
    // FILE binds the main parameter as its type reads a file: as text, which `configure`
    // parses, or, for exactly `Bytes`, as the file's bytes, bound by name before every other
    // binding, so that a second binding of it is bound twice.
    let (program, file_bytes) = match input {
        None => (None, None),
        Some(source) => {
            let (name, bytes) = read_program_bytes(source)?;
            match semantics.program_file(&name, bytes)? {
                ProgramFile::Text(program) => (Some(program), None),
                ProgramFile::Bytes { parameter, value } => {
                    (None, Some((parameter, ConfigValue::Value(value))))
                }
            }
        }
    };
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
    // Every binding goes through `configure`'s one resolver, so a parameter that any two of
    // FILE, the case, `--input` and `-c` bind is bound twice.
    let mut bindings = file_bytes.into_iter().collect::<Vec<_>>();
    bindings.extend(match case {
        Some(case) => {
            semantics
                .case_inputs(&case.case, None, &mut case.files())?
                .variables
        }
        None => Vec::new(),
    });
    let mut files = CaseFiles {
        base: PathBuf::new(),
    };
    for (name, document) in typed {
        bindings.push((
            name.clone(),
            typed_input(semantics, name, document, &mut files)?,
        ));
    }
    bindings.extend(
        variables
            .iter()
            .map(|(name, text)| (name.clone(), text.as_str().into())),
    );
    Ok(semantics.configure(&ConfigInputs {
        program,
        variables: bindings,
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

fn run(
    semantics: &mut Semantics,
    observer: Option<&mut Semantics>,
    request: &RunRequest,
    read: Option<SelectedCase>,
) -> Result<CommandOutcome, Failure> {
    let smt = semantics.capabilities().smt;
    let (case, depth) = case_and_depth(
        read,
        request.case.as_deref(),
        request.case_name.as_deref(),
        request.depth,
    )?;
    let stop = match &case {
        Some(case) => case.stop(&request.stop)?,
        None => request.stop.clone(),
    };
    let state = configure(semantics, Inputs::of_run(request, case.as_ref()), true)?;
    let mut expectation = SelectedCase::expectation_of(case.as_ref(), semantics)?;
    if let (Some(case), Some(expectation)) = (&case, &mut expectation) {
        resolve_views(semantics, observer.as_deref(), case, expectation)?;
    }
    let options = RunOptions {
        depth,
        trace: request.trace,
        coverage: request.coverage.then(CoverageOptions::default),
        stop: stop.clone(),
        ..RunOptions::default()
    };
    let report = match (semantics.run(&state, options.clone()), &case, &expectation) {
        (Ok(report), _, _) => report,
        // A run that cannot decide which of several states it reaches has no one end, so it has
        // none to compare: the verdict is inconclusive, not a refusal of the case.
        (Err(error @ ExecError::Undecided { .. }), Some(case), Some(expectation)) => {
            return undecided_case(case, expectation, &error, request.output);
        }
        (Err(error), _, _) => return Err(error.into()),
    };
    let checked = match (&case, &mut expectation) {
        (Some(case), Some(expectation)) => Some(check_run(
            semantics,
            observer,
            Run {
                case,
                state: &state,
                options: &options,
                report: &report,
            },
            expectation,
            request.view_budget,
        )?),
        _ => None,
    };
    let mut stderr = log_text(&report.log);
    if request.output != TermOutput::Json {
        write_trace(&mut stderr, &report.trace);
        if let Some(coverage) = &report.coverage {
            write_coverage(&mut stderr, coverage);
        }
    }
    let color = request.color.enabled();
    let printed = match (request.output, &checked) {
        (TermOutput::Json, Some(checked)) => json_line(
            &json!({"schema": RUN_REPORT_SCHEMA, "run": report, "expectation": checked.document()}),
        )?,
        (TermOutput::Json, None) => {
            json_line(&json!({"schema": RUN_REPORT_SCHEMA, "run": report}))?
        }
        (TermOutput::None, _) => String::new(),
        (output, _) => format!(
            "{}\n",
            print(semantics, &report.state, output, color, &mut stderr)?
        ),
    };
    let mut prints = PrintCheck::new(request.output);
    prints.check(semantics, &report.state)?;
    prints.verdict()?;
    let head = main_cell_head(semantics, &report.state, request.output, &mut stderr);
    let stops = stops_passed(semantics, &report, &stop);
    let _ = write!(
        stderr,
        "krs run: {} after {} step{}{stops}{head}",
        status_word(report.halt.as_str(), smt),
        report.steps,
        if report.steps == 1 { "" } else { "s" }
    );
    stderr.push('\n');
    if request.output != TermOutput::Json {
        write_valueless(semantics, &report, request.output, &mut stderr)?;
    }
    let exit_code = match (&checked, report.exit_code) {
        (Some(checked), _) => {
            checked.write(&mut stderr, "krs run");
            checked.exit_code()
        }
        (None, Some(code)) if report.halt.is_complete() => i32::try_from(code & 0xff).unwrap_or(1),
        (None, _) => i32::from(!report.halt.is_complete()),
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

/// The notes on the terms with no value a run's state holds or its condition read, printed in
/// `output`'s notation (pretty for none).
fn write_valueless(
    semantics: &Semantics,
    report: &RunReport,
    output: TermOutput,
    stderr: &mut String,
) -> Result<(), Failure> {
    let notation = match output {
        TermOutput::None => TermOutput::Pretty,
        output => output,
    };
    for term in &report.valueless {
        let printed = print(semantics, term, notation, false, stderr)?;
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
    Ok(())
}

/// Refuse a case `krs search --mode mode` cannot check: one whose `run` names stop rules, and
/// one with an expectation under a mode other than `final`.
fn searchable(case: &SelectedCase, mode: SearchMode) -> Result<(), Failure> {
    if case
        .case
        .run
        .as_ref()
        .is_some_and(|run| run.stop() != StopCriterion::None)
    {
        return Err(Failure::Usage(format!(
            "the case `{}` names stop rules in `run`, which krs search does not apply: a search's final states are not the ends of runs cut at those rules; run the case with krs run",
            case.path.display()
        )));
    }
    if mode != SearchMode::Final && case.case.expect.is_some() {
        return Err(Failure::Usage(format!(
            "the case `{}` states an expectation, which is checked against ends: krs search --mode {} returns reachable states, not ends; search with --mode final",
            case.path.display(),
            mode.as_str()
        )));
    }
    Ok(())
}

fn search(
    semantics: &mut Semantics,
    observer: Option<&mut Semantics>,
    request: &SearchRequest,
    read: Option<SelectedCase>,
) -> Result<CommandOutcome, Failure> {
    let (case, depth) = case_and_depth(
        read,
        request.case.as_deref(),
        request.case_name.as_deref(),
        request.depth,
    )?;
    if let Some(case) = &case {
        searchable(case, request.mode)?;
    }
    let state = configure(semantics, Inputs::of_search(request, case.as_ref()), false)?;
    let mut expectation = SelectedCase::expectation_of(case.as_ref(), semantics)?;
    if let (Some(case), Some(expectation)) = (&case, &mut expectation) {
        resolve_views(semantics, observer.as_deref(), case, expectation)?;
    }
    let options = SearchOptions {
        mode: request.mode,
        depth,
        max_solutions: request.max_solutions,
        trace: request.trace,
    };
    let report = semantics.search(&state, options)?;
    let checked = match (&case, &mut expectation) {
        (Some(case), Some(expectation)) => {
            let mut actual = semantics
                .ends_of(&report, &options)
                .map_err(|error| end_failure(&error))?;
            if actual.incomplete.is_none() {
                actual.incomplete = open_values(&report.implementation_chosen_values)
                    .map(|reason| format!("the search {reason}"));
            }
            Some(check(
                semantics,
                observer,
                case,
                expectation,
                &actual,
                request.view_budget,
            )?)
        }
        _ => None,
    };
    let truncated = request
        .max_solutions
        .is_some_and(|limit| report.solutions.len() >= limit);
    let mut stderr = log_text(&report.log);
    let mut stdout = String::new();
    let color = request.color.enabled();
    let mut prints = PrintCheck::new(request.output);
    if request.output == TermOutput::Json {
        stdout = json_line(&match &checked {
            Some(checked) => {
                json!({"schema": SEARCH_REPORT_SCHEMA, "search": report, "expectation": checked.document()})
            }
            None => json!({"schema": SEARCH_REPORT_SCHEMA, "search": report}),
        })?;
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
    let exit_code = match &checked {
        Some(checked) => {
            checked.write(&mut stderr, "krs search");
            checked.exit_code()
        }
        None => i32::from(!report.complete && !truncated),
    };
    Ok(outcome(stdout, stderr, exit_code))
}

/// A run's or a search's ends that are no ends of the definition's configurations: the backend
/// returned a state KRS cannot read as one.
fn end_failure(error: &EndError) -> Failure {
    Failure::Exec(ExecError::Result(error.to_string()))
}

/// Resolve the views `expectation` names in its observer, `observer` when the case names one and
/// `semantics` otherwise, into its comparison, and refuse, before the case runs, a view that
/// does not apply to its cell or applies to a cell the expectation does not compare.
pub(super) fn resolve_views(
    semantics: &Semantics,
    observer: Option<&Semantics>,
    case: &SelectedCase,
    expectation: &mut Expectation,
) -> Result<(), Failure> {
    if expectation.views.is_empty() {
        return Ok(());
    }
    let refuse =
        |error: &EndError| Failure::Exec(case.refusal(&format!("`expect.views`: {error}")));
    expectation.comparison.views = semantics
        .cell_views(observer.unwrap_or(semantics), &expectation.views)
        .map_err(|error| refuse(&error))?;
    semantics
        .check_stated(&expectation.comparison, &expectation.end, "expected")
        .map_err(|error| refuse(&error))
}

/// The verdict of a case's expectation against the ends of its run or search.
pub(super) struct Checked {
    /// The case's name, in a document of named cases.
    case: Option<String>,
    pub(super) verdict: Compared,
    /// A note after the verdict's lines: what may decide an inconclusive one.
    note: Option<&'static str>,
    /// The views the comparison applied, by cell, and the observer they were evaluated in when
    /// the case names one.
    views: BTreeMap<String, String>,
    observer: Option<String>,
}

/// A run of a case: the case, the state it ran from under `options`, and its report.
#[derive(Clone, Copy)]
pub(super) struct Run<'a> {
    pub(super) case: &'a SelectedCase,
    pub(super) state: &'a krs_exec::State,
    pub(super) options: &'a RunOptions,
    pub(super) report: &'a RunReport,
}

/// Check the end of `run` against `expectation`, its views evaluated in `observer` (the case's
/// definition when `None`), each evaluation within `budget` polls.
///
/// One end that differs is unmet: it is an end the definition reaches. One end that agrees is
/// met only where it is the definition's only end from the run's state
/// ([`Semantics::other_ends`]); otherwise the verdict is inconclusive, since another path may end
/// otherwise, and a final-state search, which gives every end, may decide it. The run is followed
/// again for that only once its end agrees.
pub(super) fn check_run(
    semantics: &mut Semantics,
    mut observer: Option<&mut Semantics>,
    run: Run<'_>,
    expectation: &mut Expectation,
    budget: u64,
) -> Result<Checked, Failure> {
    let mut actual = semantics
        .end_of(run.report)
        .map_err(|error| end_failure(&error))?;
    let checked = check(
        semantics,
        observer.as_deref_mut(),
        run.case,
        expectation,
        &actual,
        budget,
    )?;
    if !matches!(checked.verdict, Compared::Equal) {
        return Ok(checked);
    }
    let Some(reason) = semantics.other_ends(run.state, run.options, run.report)? else {
        return Ok(checked);
    };
    actual.incomplete = Some(reason);
    let mut checked = check(semantics, observer, run.case, expectation, &actual, budget)?;
    // A search reads the same open values; it decides only where the path chose.
    if open_values(&run.report.implementation_chosen_values).is_none() {
        checked.note = Some("krs search --case checks every final state against the expectation");
    }
    Ok(checked)
}

/// The outcome of `krs run --case` for a case with an expectation whose run reaches several
/// states under conditions it cannot decide (`error`): the run has no one end, so the verdict is
/// inconclusive, with the error as its reason; no state is printed, since the run ended in none.
fn undecided_case(
    case: &SelectedCase,
    expectation: &Expectation,
    error: &ExecError,
    output: TermOutput,
) -> Result<CommandOutcome, Failure> {
    let checked = Checked::undecided(case, expectation, error);
    let stdout = if output == TermOutput::Json {
        json_line(&json!({"schema": RUN_REPORT_SCHEMA, "expectation": checked.document()}))?
    } else {
        String::new()
    };
    let mut stderr = String::new();
    checked.write(&mut stderr, "krs run");
    Ok(outcome(stdout, stderr, checked.exit_code()))
}

/// Check `actual` against `expectation`: every end must agree with it on the class and the
/// compared cells, each viewed cell compared on its view's value, evaluated in `observer` (the
/// case's definition when `None`) within `budget` polls.
///
/// A view without a value at an end refuses the case; one whose evaluation stopped before it
/// ended (it spent `budget`, or another stop of the backend ended it) makes the verdict
/// inconclusive, since it may yet have a value.
pub(super) fn check(
    semantics: &mut Semantics,
    observer: Option<&mut Semantics>,
    case: &SelectedCase,
    expectation: &mut Expectation,
    actual: &Ends,
    budget: u64,
) -> Result<Checked, Failure> {
    let expected = Ends::one(expectation.end.clone());
    let expected = Side {
        name: "expected",
        ends: &expected,
    };
    let actual = Side {
        name: "actual",
        ends: actual,
    };
    if !expectation.comparison.views.is_empty() {
        let observer = match observer {
            Some(observer) => observer,
            None => &mut *semantics,
        };
        match expectation.comparison.views.evaluate_within(
            observer,
            &[expected, actual],
            Some(budget),
        ) {
            Ok(()) => {}
            Err(error @ EndError::ViewStopped { .. }) => {
                return Ok(Checked::new(
                    case,
                    expectation,
                    Compared::Inconclusive(error.to_string()),
                ));
            }
            Err(error) => return Err(Failure::Exec(case.refusal(&error.to_string()))),
        }
    }
    let verdict = semantics
        .check_expectation(&expectation.comparison, expected, actual)
        .map_err(|error| Failure::Exec(case.refusal(&error.to_string())))?;
    Ok(Checked::new(case, expectation, verdict))
}

impl Checked {
    /// The verdict `verdict` of `expectation`, of the case `case`.
    fn new(case: &SelectedCase, expectation: &Expectation, verdict: Compared) -> Self {
        Self {
            case: case.case.name.clone(),
            verdict,
            note: None,
            views: expectation.views.clone(),
            observer: expectation.observer.clone(),
        }
    }

    /// The verdict of `expectation` for a run that cannot decide which of several states it
    /// reaches (`error`): it has no one end, so the verdict is inconclusive.
    pub(super) fn undecided(
        case: &SelectedCase,
        expectation: &Expectation,
        error: &ExecError,
    ) -> Self {
        Self::new(
            case,
            expectation,
            Compared::Inconclusive(format!("the run has no one end: {error}")),
        )
    }

    /// The exit status the verdict gives: 0 met, 1 unmet, 3 inconclusive (no end to compare,
    /// which calls for another action than ends that differ).
    pub(super) const fn exit_code(&self) -> i32 {
        match self.verdict {
            Compared::Equal => 0,
            Compared::Differs(_) => 1,
            Compared::Inconclusive(_) => 3,
        }
    }

    /// The verdict word.
    pub(super) const fn word(&self) -> &'static str {
        match self.verdict {
            Compared::Equal => "met",
            Compared::Differs(_) => "unmet",
            Compared::Inconclusive(_) => "inconclusive",
        }
    }

    /// The report's `expectation` object: the verdict, the case's name, the difference
    /// (`krs-difference/2`) or the reason, and the views applied and their observer.
    pub(super) fn document(&self) -> serde_json::Value {
        let mut document = json!({"verdict": self.word()});
        if let Some(name) = &self.case {
            document["case"] = json!(name);
        }
        self.extend(&mut document);
        document
    }

    /// Add the verdict's members other than its word and its case to `document`: `difference`
    /// (unmet) or `reason` (inconclusive), then `views` and `observer` when it applied views.
    pub(super) fn extend(&self, document: &mut serde_json::Value) {
        match &self.verdict {
            Compared::Equal => {}
            Compared::Differs(difference) => document["difference"] = json!(difference),
            Compared::Inconclusive(reason) => document["reason"] = json!(reason),
        }
        if !self.views.is_empty() {
            document["views"] = json!(self.views);
        }
        if let Some(observer) = &self.observer {
            document["observer"] = json!(observer);
        }
    }

    /// The verdict's lines: `<command>: expectation met`, else where the first difference is
    /// with both sides, or why nothing can be concluded; then the views the comparison applied.
    pub(super) fn write(&self, output: &mut String, command: &str) {
        match &self.verdict {
            Compared::Equal => {
                let _ = writeln!(output, "{command}: expectation met");
            }
            Compared::Inconclusive(reason) => {
                let _ = writeln!(output, "{command}: expectation inconclusive: {reason}");
            }
            Compared::Differs(difference) => write_difference(output, command, difference),
        }
        if !self.views.is_empty() {
            let views = self
                .views
                .iter()
                .map(|(cell, function)| format!("`{cell}` = `{function}`"))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = match &self.observer {
                Some(observer) => writeln!(output, "  views: {views}, in `{observer}`"),
                None => writeln!(output, "  views: {views}"),
            };
        }
        if let Some(note) = self.note {
            let _ = writeln!(output, "note: {note}");
        }
    }
}

/// An unmet expectation's first difference, as `krs run` prints it.
fn write_difference(output: &mut String, command: &str, difference: &Difference) {
    let (expected, actual) = (&difference.left, &difference.right);
    if let (DifferenceAt::Cell, Some(path)) = (difference.at, &difference.path) {
        let _ = writeln!(output, "{command}: expectation unmet at `{path}`");
        let _ = writeln!(
            output,
            "  expected: {}",
            rendered_text(expected.value.as_ref())
        );
        let _ = writeln!(
            output,
            "  actual:   {}",
            rendered_text(actual.value.as_ref())
        );
    } else {
        let class = |class: &krs_exec::EndClass| match &class.rule {
            Some(rule) => format!("{} at `{rule}`", class.halt.as_str()),
            None => class.halt.as_str().to_owned(),
        };
        let _ = writeln!(output, "{command}: expectation unmet at the end's halt");
        let _ = writeln!(output, "  expected: {}", class(&expected.class));
        let _ = writeln!(output, "  actual:   {}", class(&actual.class));
    }
    if !difference.also_differ.is_empty() {
        let cells = difference
            .also_differ
            .iter()
            .map(|cell| format!("`{cell}`"))
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(output, "  also differ: {cells}");
    }
    if actual.ends > 1 {
        let _ = writeln!(
            output,
            "  (one of the {} actual ends; the expectation holds of every end or is unmet)",
            actual.ends
        );
    }
}

/// A side's value at a difference: its canonical text, or its K text, marked; `nothing` where
/// the side lacks the position.
fn rendered_text(value: Option<&Rendered>) -> String {
    let Some(value) = value else {
        return "nothing (the position is absent on this side)".to_owned();
    };
    let mut text = match (&value.document, &value.text) {
        (Some(document), _) => canonical_text(document),
        (None, Some(text)) if value.rendering == "document" => text.clone(),
        (None, Some(text)) => {
            let opaque = value
                .opaque
                .as_deref()
                .filter(|opaque| !opaque.is_empty())
                .map_or_else(String::new, |opaque| format!(" at `{opaque}`"));
            format!(
                "{text} ({} text: no document for the part{opaque})",
                if value.rendering == "kore" {
                    "KORE"
                } else {
                    "K"
                }
            )
        }
        (None, None) => String::new(),
    };
    if value.truncated {
        let _ = write!(
            text,
            " (cut to {} characters, {} cut before)",
            krs_exec::VALUE_CAP,
            value.offset
        );
    }
    text
}

/// `krs prove`: each selected claim proved in turn and printed as it ends ([`ProveOutput`]), or,
/// in a worker of a supervising `krs prove` ([`ProveRequest::worker`]), written to it as events.
fn prove(semantics: &mut Semantics, request: &ProveRequest) -> Result<CommandOutcome, Failure> {
    let options = ProveOptions {
        module: request.spec_module.clone(),
        claims: request.claims.clone(),
        depth: request.depth,
        claim_timeout: request.claim_timeout,
    };
    let selection = semantics.prove_selection(&options)?;
    // A leaf is a printed state, as a run's and a search's are.
    let mut prints = PrintCheck::new(request.output);
    if request.worker {
        let mut events = std::io::stdout().lock();
        #[cfg(debug_assertions)]
        supervisor::test_crash("before-selection");
        supervisor::send_selected(&mut events, &selection).map_err(|error| worker_write(&error))?;
        #[cfg(debug_assertions)]
        supervisor::test_crash("before-claims");
        for claim in &selection {
            supervisor::send_started(&mut events, &claim.label)
                .map_err(|error| worker_write(&error))?;
            #[cfg(debug_assertions)]
            supervisor::test_crash(&claim.label);
            let report = semantics.prove_claim(&options, claim)?;
            let mut warnings = String::new();
            let text = claim_text(semantics, request, &report, &mut prints, &mut warnings)?;
            supervisor::send_finished(&mut events, request.output, &report, &text, &warnings)
                .map_err(|error| worker_write(&error))?;
        }
        #[cfg(debug_assertions)]
        supervisor::test_crash("after-claims");
        prints.verdict()?;
        return Ok(outcome(supervisor::end_event(), String::new(), 0));
    }
    let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
    let mut printed = ProveOutput::new(
        request.output,
        SolverReport::of(semantics.solver()),
        &mut stdout,
        &mut stderr,
    );
    for claim in &selection {
        printed
            .started(&claim.label)
            .map_err(|error| buffer_write(&error))?;
        let report = semantics.prove_claim(&options, claim)?;
        let mut warnings = String::new();
        let text = claim_text(semantics, request, &report, &mut prints, &mut warnings)?;
        let serialized = printed
            .wants_report()
            .then(|| supervisor::serialize_report(&report))
            .transpose()
            .map_err(|error| buffer_write(&error))?;
        printed
            .finished(serialized, report.verdict, &text, &warnings)
            .map_err(|error| buffer_write(&error))?;
    }
    prints.verdict()?;
    let exit_code = printed.close().map_err(|error| buffer_write(&error))?;
    Ok(CommandOutcome {
        stdout,
        stderr,
        exit_code,
        warnings: crate::DiagnosticReports {
            envelopes: Vec::new(),
        },
    })
}

fn worker_write(error: &std::io::Error) -> Failure {
    Failure::Read(format!(
        "could not write to the supervising krs prove: {error}"
    ))
}

fn buffer_write(error: &std::io::Error) -> Failure {
    Failure::Read(format!("could not write the proof output: {error}"))
}

/// The text `--output pretty`, `kast` or `kore` prints for `report`: its verdict line, then what
/// the proof applied, then, unless it is proven or trusted, each residual leaf; empty for the
/// JSON outputs. A print's warnings go to `warnings`.
fn claim_text(
    semantics: &mut Semantics,
    request: &ProveRequest,
    report: &ProofReport,
    prints: &mut PrintCheck,
    warnings: &mut String,
) -> Result<String, Failure> {
    let mut stdout = String::new();
    if matches!(request.output, TermOutput::Json | TermOutput::JsonLines) {
        return Ok(stdout);
    }
    let smt = semantics.capabilities().smt;
    let color = request.color.enabled();
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
    if report.verdict == Verdict::Timeout {
        let _ = writeln!(
            stdout,
            "  the proof did not end within --claim-timeout and was cancelled"
        );
    }
    if matches!(report.verdict, Verdict::Proven | Verdict::Trusted) {
        return Ok(stdout);
    }
    for (index, leaf) in report.leaves.iter().enumerate() {
        prints.check(semantics, &leaf.state)?;
        let text = print(semantics, &leaf.state, request.output, color, warnings)?;
        let _ = writeln!(
            stdout,
            "  leaf {} ({}, depth {}):\n{text}",
            index + 1,
            leaf.outcome,
            leaf.depth,
        );
    }
    Ok(stdout)
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

/// The status line's account of a run's stops under `criterion`, when it names stop rules: the
/// stop the run ended at, with its place in the count (``, after `frame_end` (stop 3 of 3)``),
/// or how many arrivals it counted when it ended on its own first (`, 2 of 3 stops reached`).
///
/// The stop is named so that the name, passed to the stop flags, selects its rule: by its KRS
/// item's spelling where that names the item alone (`crate::frame_end`), else by its K label
/// ([`Semantics::stop_name`]); where the report does not name the rule (a stop after a rule of a
/// name that selects several, without a trace), by the name written for that side when it is
/// one.
fn stops_passed(semantics: &Semantics, report: &RunReport, criterion: &StopCriterion) -> String {
    let StopCriterion::Rules { rules, count } = criterion else {
        return String::new();
    };
    let Some(stop) = &report.stop else {
        return format!(", {} of {count} stops reached", report.stops);
    };
    let (at, names) = match stop.at {
        StopAt::Before => ("before", &rules.before),
        StopAt::After => ("after", &rules.after),
    };
    let rule = stop
        .rule
        .as_ref()
        .and_then(|rule| semantics.stop_name(&rule.rule_id))
        .or_else(|| match names.as_slice() {
            [name] => Some(name.clone()),
            _ => None,
        })
        .map_or_else(|| "a stop rule".to_owned(), |name| format!("`{name}`"));
    format!(", {at} {rule} (stop {} of {count})", stop.nth)
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
        TermOutput::Kast | TermOutput::Json | TermOutput::JsonLines => state.computation_head(cell),
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
        TermOutput::Json | TermOutput::JsonLines => PrintStyle::Json,
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

pub(super) const fn outcome(stdout: String, stderr: String, exit_code: i32) -> CommandOutcome {
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

/// One line per rule and equation of the definition a run covered, with the predicates that hold
/// of it: `committed` (a path took its step) beside `applied ×N`, `applied ×N` alone, `matched`
/// (its condition was begun for a matched instance), or `offered`. N is the number of
/// applications, under `applied`'s name because it counts them, not commits: a step that found
/// its successor undefined, or a successor proposed and not taken, is an application and no
/// commit. A rule is named by its KRS item when it has one, else by its label. The sentences no
/// author wrote or named, those of K's builtin closure and those a compiler pass generated from no
/// authored source with neither an item nor a label, are counted on a last line; `--output json`
/// lists them.
fn write_coverage(output: &mut String, coverage: &Coverage) {
    let mut builtin = 0_usize;
    let mut passes = std::collections::BTreeMap::<&str, usize>::new();
    let mut rows = Vec::new();
    for rule in &coverage.rules {
        match &rule.origin {
            StepOrigin::Builtin { .. } => {
                builtin += 1;
                continue;
            }
            StepOrigin::Generated { pass, from: None }
                if rule.item.is_none() && rule.label.is_none() =>
            {
                *passes.entry(pass).or_default() += 1;
                continue;
            }
            _ => {}
        }
        let predicate = if rule.committed {
            format!("committed, applied ×{}", rule.applications)
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
    let mut unnamed = passes
        .iter()
        .map(|(pass, count)| format!("{count} generated by {pass}"))
        .collect::<Vec<_>>();
    if builtin > 0 {
        unnamed.push(format!("{builtin} of K's builtin modules"));
    }
    if !unnamed.is_empty() {
        let _ = writeln!(output, "coverage  and {}", unnamed.join(", "));
    }
}

/// The registered code of an exec failure.
pub(super) const fn diagnostic_code(error: &ExecError) -> Code {
    match error {
        ExecError::Compile(_) | ExecError::Backend(_) => codes::exec::BACKEND,
        ExecError::StrayProgram { .. }
        | ExecError::MissingProgram { .. }
        | ExecError::ProgramNotText { .. } => codes::exec::PROGRAM,
        ExecError::UnknownVariable { .. }
        | ExecError::StreamInput { .. }
        | ExecError::DuplicateVariable(_)
        | ExecError::MissingVariables(_)
        | ExecError::Value { .. }
        | ExecError::Input(_) => codes::exec::VARIABLE,
        ExecError::CollectionElementSort(_) => codes::exec::COLLECTION_ELEMENT_SORT,
        ExecError::Parse { .. } => codes::exec::PARSE,
        ExecError::UnknownSort { .. } | ExecError::NoProgramSort => codes::exec::SORT,
        ExecError::UnknownClaim { .. }
        | ExecError::AmbiguousClaim { .. }
        | ExecError::NoClaims
        | ExecError::NoSpecClaims(_)
        | ExecError::UnknownSpecModule { .. } => codes::exec::CLAIM,
        ExecError::UnknownRule { .. }
        | ExecError::AmbiguousRule { .. }
        | ExecError::UnknownItem { .. }
        | ExecError::AmbiguousItem { .. } => codes::exec::RULE,
        ExecError::SearchWithStreams => codes::exec::STREAMS,
        ExecError::Unavailable(_) => codes::exec::UNAVAILABLE,
        ExecError::Result(_) => codes::exec::RESULT,
        ExecError::Undecided(_) => codes::exec::UNDECIDED,
        ExecError::Case(_) => codes::exec::CASE,
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
                label: Some(format!("nat--{id}")),
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
                    CoveredRule {
                        label: None,
                        ..rule(
                            "g1",
                            None,
                            RuleKind::Equation,
                            StepOrigin::Generated {
                                pass: "concretize-cells".to_owned(),
                                from: None,
                            },
                            1,
                            false,
                        )
                    },
                ],
            },
        );
        assert_eq!(
            output,
            "coverage  matched  nat--r2  (rule)  src/lib.rs:60:1\n\
             coverage  applied ×2  plus_succ  (equation)  src/lib.rs:38:1\n\
             coverage  applied ×1  plus_zero  (equation)  src/lib.rs:31:1\n\
             coverage  committed, applied ×3  step  (rule)  src/lib.rs:50:1\n\
             coverage  and 1 generated by concretize-cells, 1 of K's builtin modules\n"
        );
    }
}
