//! `krs parse`, `krs run`, `krs search`, and `krs prove` over the prepared Definition IR.
//!
//! Each command compiles the Definition IR in-process through `krs-exec` and the k-rust symbolic backend, on a 64 MiB-stack worker.
//! Results are never cached: a run depends on its inputs, and the collector and lowering stages it shares with the other commands are already incremental.

use std::fmt::Write as _;
use std::io::{IsTerminal as _, Read};
use std::path::PathBuf;

use krs_diagnostic::{Code, codes};
use krs_exec::{
    ConfigInputs, ExecError, PrintStyle, Printed, ProgramInput, ProveOptions, REPORT_SCHEMA,
    RunOptions, SearchMode, SearchOptions, Semantics, SourceText, Step, StepOrigin, Term, Verdict,
};
use krs_ir::measure::Measurement;
use serde_json::json;

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

const WORKER_STACK: usize = 64 * 1024 * 1024;

/// Compile the prepared definition and run one parse, run, search, or prove command.
pub(super) fn execute(
    prepared: &PreparedDefinition,
    command: &Command,
    sources: &DiagnosticSources,
    measurement: &mut Measurement,
) -> Result<CommandOutcome, CommandError> {
    let sources = sources.clone();
    let timings = &mut measurement.timings;
    let definition = prepared.lowered.definition();
    let result = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("krs-exec".into())
            .stack_size(WORKER_STACK)
            .spawn_scoped(scope, move || {
                let provider: SourceText = Box::new(move |file| sources.source_text(file));
                let mut semantics = Semantics::compile_with(definition, Some(provider), timings)
                    .map_err(Failure::Exec)?;
                dispatch(&mut semantics, command)
            })
            .map_err(|error| {
                CommandError::InvalidRequest(format!("could not start the run worker: {error}"))
            })?
            .join()
            .map_err(|_| CommandError::InvalidRequest("the run worker panicked".into()))
    })?;
    result.map_err(|failure| match failure {
        Failure::Exec(ExecError::Compile(error)) => {
            native_command_error(prepared.lowered.source_map(), error)
        }
        Failure::Exec(error) => CommandError::Exec(error),
        Failure::Usage(message) => CommandError::Usage(message),
        Failure::Serialization(error) => CommandError::Serialization(error),
        Failure::Read(message) => CommandError::InvalidRequest(message),
    })
}

/// A worker failure, converted to a [`CommandError`] on the calling thread.
enum Failure {
    Exec(ExecError),
    Usage(String),
    Serialization(serde_json::Error),
    Read(String),
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
            };
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
        variables: variables.to_vec(),
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
        },
    )?;
    let mut stderr = String::new();
    if request.output != TermOutput::Json {
        write_trace(&mut stderr, &report.trace);
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
    let _ = write!(
        stderr,
        "krs run: {} after {} step{}",
        status_word(report.halt.as_str(), smt),
        report.steps,
        if report.steps == 1 { "" } else { "s" }
    );
    match report.state.k_head() {
        Some(Some(head)) => {
            let _ = write!(stderr, "; <k> starts with `{head}`");
        }
        Some(None) => stderr.push_str("; <k> is empty"),
        None => {}
    }
    stderr.push('\n');
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
    let mut stderr = String::new();
    let mut stdout = String::new();
    let color = request.color.enabled();
    if request.output == TermOutput::Json {
        stdout = json_line(&json!({"schema": REPORT_SCHEMA, "search": report}))?;
    } else {
        for (index, solution) in report.solutions.iter().enumerate() {
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
        module: None,
        claims: request.claims.clone(),
        depth: request.depth,
    })?;
    let proven = reports
        .iter()
        .filter(|report| report.verdict == Verdict::Proven)
        .count();
    let mut stdout = String::new();
    let mut warnings = String::new();
    let color = request.color.enabled();
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
            if report.verdict == Verdict::Proven {
                continue;
            }
            for (index, leaf) in report.leaves.iter().enumerate() {
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
    let stderr = format!(
        "{warnings}krs prove: {proven} of {} claim{} proven\n",
        reports.len(),
        if reports.len() == 1 { "" } else { "s" }
    );
    Ok(outcome(stdout, stderr, i32::from(proven != reports.len())))
}

/// A status word, marked when it is `indeterminate` in a build without an SMT solver.
fn status_word(word: &str, smt: bool) -> String {
    if word == "indeterminate" && !smt {
        "indeterminate (no SMT solver)".to_owned()
    } else {
        word.to_owned()
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
    Ok(semantics.print(term, style)?)
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
            unlocated: Vec::new(),
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

/// The registered code of an exec failure.
pub(super) const fn diagnostic_code(error: &ExecError) -> Code {
    match error {
        ExecError::Compile(_) | ExecError::Backend(_) => codes::exec::BACKEND,
        ExecError::StrayProgram | ExecError::MissingProgram => codes::exec::PROGRAM,
        ExecError::UnknownVariable { .. }
        | ExecError::DuplicateVariable(_)
        | ExecError::MissingVariables(_) => codes::exec::VARIABLE,
        ExecError::Parse { .. } => codes::exec::PARSE,
        ExecError::UnknownSort { .. } | ExecError::NoProgramSort => codes::exec::SORT,
        ExecError::UnknownClaim { .. } | ExecError::AmbiguousClaim { .. } | ExecError::NoClaims => {
            codes::exec::CLAIM
        }
        ExecError::SearchWithStreams => codes::exec::STREAMS,
        ExecError::Unavailable(_) => codes::exec::UNAVAILABLE,
        ExecError::Result(_) => codes::exec::RESULT,
    }
}

impl From<ExecError> for CommandError {
    fn from(error: ExecError) -> Self {
        Self::Exec(error)
    }
}

#[cfg(test)]
mod tests {
    use super::{status_word, write_trace};
    use krs_exec::{SourceSpan, Step, StepOrigin};

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
}
