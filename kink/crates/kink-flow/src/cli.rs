//! The `kink-flow` command line. Every command prints one JSON document on stdout, or with
//! `--output verdicts` (`results` and `run`) its deterministic rendering ([`crate::verdicts`]).
//!
//! Exit status: [`EXIT_OK`] when the command did its job and found nothing wrong with the
//! corpus, [`EXIT_CORPUS`] when the manifest, the specification, a program or a mutation is
//! refused (the document says which and why), or, for `check`, when a fact known before any
//! mutant runs makes a verdict impossible (a program cannot be judged on the baseline, or the
//! baseline has no data under `[spec] assume_joined`), and [`EXIT_USAGE`] on a usage error
//! (stderr).
//!
//! A mutation list (`MUTATIONS` below) is a `MUTATIONS.toml` file or a mutations directory of
//! `<topic>.toml` files ([`MutationList::read`]).
//!
//! The command layer is a library both front ends use: kink-flow's own command line, and the krs
//! front end, which binds a KRS corpus's manifest to the K it emits
//! ([`crate::manifest::ManifestFile::bind`]). [`FlowCommand::parse`] reads a verb's options
//! exactly as `kink-flow <verb>` does, the corpus's files given by the front end
//! ([`CommandFiles`]: kink-flow's operands, or the front end's layout); [`dispatch`] runs the
//! command on the large stack kink's definitions need. A [`FrontEnd`] adds how next steps spell
//! the front end's commands ([`CommandSpelling`]), the mutations it refused before the engine
//! ([`FrontEnd::refused`]), and an annotation of the document ([`FrontEnd::annotate`]). kink-flow
//! itself runs every command with [`FrontEnd::default`].

use crate::{
    admit::{FlowAdmission, admit, admit_spec},
    check::{CorpusCoverage, Finding, MutationCheck, check_mutations, corpus_coverage},
    fuzz::{FuzzJob, FuzzOptions, TemplateList},
    manifest::{FlowManifest, ManifestError},
    memo::MemoUse,
    mutation::{InvalidMutation, MutationList},
    pattern::PatternList,
    query::{QueryOptions, pattern_list_refused},
    report::{ReportOptions, render},
    results::{ResultsOptions, cache_directory},
    search::{ProgramOrder, RunMode, RunOptions, mutation_list_refused},
};
use kink_campaign::ScheduleMode;
use kink_corpus::cli::DEFINITION_STACK_BYTES;
use kink_native::execution::SolverProfile;
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    ffi::OsString,
    io::Write,
    path::{Path, PathBuf},
};

pub const EXIT_OK: u8 = 0;
pub const EXIT_CORPUS: u8 = 1;
pub const EXIT_USAGE: u8 = 2;

pub const USAGE: &str = "usage: kink-flow --version | kink-flow check FLOW.toml [--mutations \
                         MUTATIONS] [--cache DIR] | kink-flow \
                         results FLOW.toml [--verify] [--mutations MUTATIONS] [--cache DIR] \
                         [--output json|verdicts] | kink-flow run \
                         FLOW.toml MUTATIONS [--only ID]... [--verify] [--order cost|corpus] \
                         [--full] [--compile-workers N] [--no-memo] [--cache DIR] [--output \
                         json|verdicts] | kink-flow report \
                         FLOW.toml [--cache DIR] [--output json|verdicts] | kink-flow query FLOW.toml PATTERNS.toml \
                         [--only ID]... [--verify] [--cache DIR] | kink-flow fuzz FLOW.toml \
                         TEMPLATES.toml --template ID (--kill MUTATION --mutations MUTATIONS \
                         | --matched RULE | --fired RULE | --pattern ID --patterns PATTERNS.toml) \
                         [--cases N | --work W] [--seed S] [--max-work N] [--time-limit-ms T] \
                         [--assume-joined NAME]... [--one-path] [--cache DIR] [--no-confirm] \
                         [--no-filter]; MUTATIONS is a MUTATIONS.toml or a directory of \
                         <topic>.toml files";

/// Run one command; returns the process exit status.
pub fn execute(args: Vec<OsString>) -> u8 {
    let Ok(args) = args
        .into_iter()
        .map(|arg| arg.into_string())
        .collect::<Result<Vec<_>, _>>()
    else {
        return usage(USAGE);
    };
    // The builds a document's identity names, as `krust-fuzz --version` prints its own.
    if let [flag] = args.as_slice()
        && flag == "--version"
    {
        println!(
            "kink-flow {} (k-rust {})",
            env!("CARGO_PKG_VERSION"),
            crate::k_rust_revision()
        );
        return EXIT_OK;
    }
    let Some((verb, manifest, files, options)) = operands(&args) else {
        return usage(USAGE);
    };
    if !manifest.is_file() {
        return usage(&format!("{} is not a file", manifest.display()));
    }
    let command = match FlowCommand::parse(verb.as_str(), files, options) {
        Ok(command) => command,
        Err(message) => return usage(&message),
    };
    let output = command.output();
    let (document, status) = match FlowManifest::read(&manifest) {
        Err(error) => (command.manifest_refused(&error), EXIT_CORPUS),
        Ok(manifest) => match dispatch(manifest, command, FrontEnd::default()) {
            Ok(result) => result,
            Err(panicked) => {
                eprintln!("kink-flow: {panicked}");
                return EXIT_CORPUS;
            }
        },
    };
    let text = match output {
        OutputFormat::Json => format!("{}\n", render(&document)),
        OutputFormat::Verdicts => match crate::verdicts::verdicts(&document) {
            Ok(text) => {
                // The rendering names a refusal or a stop by its reason; its text goes to stderr.
                for detail in crate::verdicts::refusal_details(&document) {
                    eprintln!("kink-flow: {detail}");
                }
                text
            }
            Err(message) => {
                eprintln!("kink-flow: {message}");
                return EXIT_CORPUS;
            }
        },
    };
    let mut stdout = std::io::stdout().lock();
    if stdout.write_all(text.as_bytes()).is_err() {
        return EXIT_CORPUS;
    }
    status
}

/// A `kink-flow` command line's verb, manifest, operand files and options: `run`, `query` and
/// `fuzz` take one more operand (the mutation list, the patterns, the templates).
fn operands(args: &[String]) -> Option<(Verb, PathBuf, CommandFiles, &[String])> {
    let [command, manifest, rest @ ..] = args else {
        return None;
    };
    let verb = Verb::parse(command)?;
    let mut files = CommandFiles::default();
    let rest = match verb {
        Verb::Run | Verb::Query | Verb::Fuzz => {
            let (file, rest) = rest.split_first()?;
            let file = Some(PathBuf::from(file));
            match verb {
                Verb::Run => files.mutations = file,
                Verb::Query => files.patterns = file,
                _ => files.templates = file,
            }
            rest
        }
        Verb::Check | Verb::Results | Verb::Report => rest,
    };
    Some((verb, PathBuf::from(manifest), files, rest))
}

fn usage(message: &str) -> u8 {
    eprintln!("kink-flow: {message}");
    if message != USAGE {
        eprintln!("{USAGE}");
    }
    EXIT_USAGE
}

/// Run `body` on a thread with kink-corpus's definition stack allowance, and wait for it; `None`
/// when the thread cannot be started or `body` panics. `body` may borrow from the caller.
pub fn on_stack<T: Send>(body: impl FnOnce() -> T + Send) -> Option<T> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("kink-flow".into())
            .stack_size(DEFINITION_STACK_BYTES)
            .spawn_scoped(scope, body)
            .ok()?
            .join()
            .ok()
    })
}

/// A kink-flow verb, as both front ends spell it.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Verb {
    Check,
    Results,
    Run,
    Report,
    Query,
    Fuzz,
}

impl Verb {
    /// Every verb, in the order the usage lists them.
    pub const ALL: [Self; 6] = [
        Self::Check,
        Self::Results,
        Self::Run,
        Self::Report,
        Self::Query,
        Self::Fuzz,
    ];

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Check => "check",
            Self::Results => "results",
            Self::Run => "run",
            Self::Report => "report",
            Self::Query => "query",
            Self::Fuzz => "fuzz",
        }
    }

    /// The verb spelled `name`.
    pub fn parse(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|verb| verb.as_str() == name)
    }

    /// The operands `kink-flow <verb>` takes before its options.
    pub const fn operands(self) -> &'static str {
        match self {
            Self::Check | Self::Results | Self::Report => "FLOW.toml",
            Self::Run => "FLOW.toml MUTATIONS.toml",
            Self::Query => "FLOW.toml PATTERNS.toml",
            Self::Fuzz => "FLOW.toml TEMPLATES.toml",
        }
    }

    /// The document of this verb for a manifest that does not decode: the specification refused
    /// at stage `manifest` with the error, under the verb's schema (`fuzz`: its input refusal).
    /// A run's document also names its schedule, which only the parsed command knows
    /// ([`FlowCommand::manifest_refused`]).
    #[must_use]
    pub fn manifest_refused(self, error: &ManifestError) -> Value {
        let schema = match self {
            Self::Check => return manifest_refused(error),
            Self::Fuzz => return crate::fuzz::input_refused("FLOW.toml", error),
            Self::Results => "kink-flow-results",
            Self::Run => crate::report::RUN_SCHEMA,
            Self::Report => crate::report::MISSING_SCHEMA,
            Self::Query => crate::query::QUERY_SCHEMA,
        };
        let mut document = manifest_refused(error);
        document["schema"] = json!(schema);
        document
    }

    /// What the thread that runs the verb is named in a panic's message.
    const fn task(self) -> &'static str {
        match self {
            Self::Check => "admission",
            Self::Results => "results",
            Self::Run => "run",
            Self::Report => "report",
            Self::Query => "query",
            Self::Fuzz => "fuzz",
        }
    }
}

/// How a front end spells its commands in the next steps documents give ("run `kink-flow results
/// --verify`", "run `krs kink results --verify`"). A front end implements it with whatever
/// selects the corpus it runs on (a package path, a definition facet), so that a next step
/// reproduces the step for that corpus; kink-flow's own is [`KinkFlowSpelling`]. The texts a
/// document appends, such as ` --verify` or ` --only ID`, are the verb's own options, so both
/// methods end where the verb's options may start.
pub trait CommandSpelling: Sync {
    /// The command that runs `verb` on this corpus, its operands and selection included
    /// (`kink-flow run FLOW.toml MUTATIONS.toml`; `krs kink run --definition main`).
    fn command(&self, verb: Verb) -> String;

    /// The command that runs `verb`, as a text that names it in passing gives it (`kink-flow
    /// run`); the front end's selection is part of it as of [`Self::command`]. By default
    /// [`Self::command`].
    fn verb(&self, verb: Verb) -> String {
        self.command(verb)
    }
}

/// kink-flow's own spelling: `kink-flow <verb>` with the verb's operands ([`Verb::operands`]),
/// and without them where a text names the verb in passing.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct KinkFlowSpelling;

impl CommandSpelling for KinkFlowSpelling {
    fn command(&self, verb: Verb) -> String {
        format!("{} {}", self.verb(verb), verb.operands())
    }

    fn verb(&self, verb: Verb) -> String {
        format!("kink-flow {}", verb.as_str())
    }
}

/// What a command prints.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum OutputFormat {
    /// The JSON document.
    #[default]
    Json,
    /// The deterministic rendering of a `results` or `run` document ([`crate::verdicts`]).
    Verdicts,
}

/// The files a verb reads besides the manifest, as the front end finds them: kink-flow's
/// operands (`run`'s mutation list, `query`'s patterns, `fuzz`'s templates), or a front end's
/// layout. A verb's own flag (`--mutations`, `--patterns`) takes precedence over a file given
/// here.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CommandFiles {
    pub mutations: Option<PathBuf>,
    pub patterns: Option<PathBuf>,
    pub templates: Option<PathBuf>,
}

/// One parsed command ([`FlowCommand::parse`]).
#[derive(Clone, Debug)]
pub enum FlowCommand {
    Check(CheckOptions),
    Results {
        options: ResultsOptions,
        output: OutputFormat,
    },
    Run {
        mutations: PathBuf,
        options: RunOptions,
        mode: RunMode,
        output: OutputFormat,
    },
    Report {
        options: ReportOptions,
        output: OutputFormat,
    },
    Query {
        patterns: PathBuf,
        options: QueryOptions,
    },
    Fuzz {
        templates: PathBuf,
        request: FuzzRequest,
    },
}

impl FlowCommand {
    /// Parse `verb`'s `options` exactly as `kink-flow <verb>` does, with the files `files` gives:
    /// each file must exist, and each id `--only`, `--kill`, `--pattern` and `--template` names
    /// must be one of its list when the list decodes (a list that does not decode is the
    /// command's refusal, not a usage error). The error is the usage message.
    pub fn parse(verb: &str, files: CommandFiles, options: &[String]) -> Result<Self, String> {
        let verb = Verb::parse(verb).ok_or_else(|| format!("unknown command {verb:?}"))?;
        let not_found = |path: &Path| format!("{} is not a file or directory", path.display());
        let not_file = |path: &Path| format!("{} is not a file", path.display());
        match verb {
            Verb::Check => {
                let mut options = check_options(options)?;
                options.mutations = options.mutations.or(files.mutations);
                if let Some(list) = options.mutations.as_ref().filter(|list| !list.exists()) {
                    return Err(not_found(list));
                }
                Ok(Self::Check(options))
            }
            Verb::Results => {
                let (mut options, output) = results_options(options)?;
                options.mutations = options.mutations.or(files.mutations);
                if let Some(list) = options.mutations.as_ref().filter(|list| !list.exists()) {
                    return Err(not_found(list));
                }
                Ok(Self::Results { options, output })
            }
            Verb::Run => {
                let mutations = files.mutations.ok_or("run needs a mutation list")?;
                if !mutations.exists() {
                    return Err(not_found(&mutations));
                }
                let (options, mode, output) = run_options(options)?;
                if let Ok(list) = MutationList::read(&mutations)
                    && let Some(id) = options
                        .only
                        .iter()
                        .find(|id| !list.mutations.iter().any(|m| &m.id == *id))
                {
                    return Err(format!("--only {id}: no mutation has this id"));
                }
                Ok(Self::Run {
                    mutations,
                    options,
                    mode,
                    output,
                })
            }
            Verb::Report => {
                let (options, output) = report_options(options)?;
                Ok(Self::Report { options, output })
            }
            Verb::Query => {
                let patterns = files.patterns.ok_or("query needs a pattern list")?;
                if !patterns.is_file() {
                    return Err(not_file(&patterns));
                }
                let options = query_options(options)?;
                if let Ok(list) = PatternList::read(&patterns)
                    && let Some(id) = options
                        .only
                        .iter()
                        .find(|id| !list.patterns.iter().any(|p| &p.id == *id))
                {
                    return Err(format!("--only {id}: no pattern has this id"));
                }
                Ok(Self::Query { patterns, options })
            }
            Verb::Fuzz => {
                let templates = files
                    .templates
                    .clone()
                    .ok_or("fuzz needs a template list")?;
                if !templates.is_file() {
                    return Err(not_file(&templates));
                }
                let request = fuzz_options(options, &files)?;
                match &request.job {
                    FuzzJobRequest::Kill {
                        mutations: list, ..
                    } if !list.exists() => return Err(not_found(list)),
                    FuzzJobRequest::Pattern { patterns: file, .. } if !file.is_file() => {
                        return Err(not_file(file));
                    }
                    _ => {}
                }
                if let Ok(list) = TemplateList::read(&templates)
                    && list.get(&request.template).is_none()
                {
                    return Err(format!(
                        "--template {}: no template has this id",
                        request.template
                    ));
                }
                if let FuzzJobRequest::Kill {
                    mutation,
                    mutations,
                } = &request.job
                    && let Ok(list) = MutationList::read(mutations)
                    && !list.mutations.iter().any(|m| &m.id == mutation)
                {
                    return Err(format!("--kill {mutation}: no mutation has this id"));
                }
                if let FuzzJobRequest::Pattern { id, patterns } = &request.job
                    && let Ok(list) = PatternList::read(patterns)
                    && !list.patterns.iter().any(|p| &p.id == id)
                {
                    return Err(format!("--pattern {id}: no pattern has this id"));
                }
                Ok(Self::Fuzz { templates, request })
            }
        }
    }

    /// The command's verb.
    #[must_use]
    pub const fn verb(&self) -> Verb {
        match self {
            Self::Check(_) => Verb::Check,
            Self::Results { .. } => Verb::Results,
            Self::Run { .. } => Verb::Run,
            Self::Report { .. } => Verb::Report,
            Self::Query { .. } => Verb::Query,
            Self::Fuzz { .. } => Verb::Fuzz,
        }
    }

    /// The command's document for a manifest that does not decode ([`Verb::manifest_refused`]).
    /// A run's names the command's `schedule` and a null `matrix`, as every run document does,
    /// so that a refusal under `--full` reads as a full run's, whichever input was refused
    /// ([`mutation_list_refused`]).
    #[must_use]
    pub fn manifest_refused(&self, error: &ManifestError) -> Value {
        let mut document = self.verb().manifest_refused(error);
        if let Self::Run { options, .. } = self {
            document["schedule"] = json!(crate::search::schedule_name(options.schedule));
            document["matrix"] = Value::Null;
        }
        document
    }

    /// What the command prints: `--output` of `results`, `run` and `report`, the JSON document
    /// otherwise.
    #[must_use]
    pub const fn output(&self) -> OutputFormat {
        match self {
            Self::Results { output, .. }
            | Self::Run { output, .. }
            | Self::Report { output, .. } => *output,
            _ => OutputFormat::Json,
        }
    }
}

/// What a front end adds to a command ([`dispatch`]).
pub struct FrontEnd<'a> {
    /// How next steps spell the front end's commands.
    pub spelling: &'a dyn CommandSpelling,
    /// The mutations the front end refused before kink-flow resolved them, by id, each with the
    /// refusal its row shows (reason [`crate::InvalidReason::External`] for a check of the front
    /// end's own). `run` gives each the row of a mutation that does not resolve and runs nothing
    /// for it; `check --mutations` adds the refusal to its row; a `fuzz` kill job of one is
    /// refused. An id that is not in the list is ignored.
    pub refused: BTreeMap<String, InvalidMutation>,
    /// Applied to the document before it is returned, and, for `run`, before each write of the
    /// report, so that `report` prints what `run` printed. It must be idempotent: `report`
    /// applies it again to the document `run` stored.
    pub annotate: Option<&'a (dyn Fn(&mut Value) + Sync)>,
}

impl Default for FrontEnd<'_> {
    /// kink-flow's own: its spelling, nothing refused, no annotation.
    fn default() -> Self {
        Self {
            spelling: &KinkFlowSpelling,
            refused: BTreeMap::new(),
            annotate: None,
        }
    }
}

impl std::fmt::Debug for FrontEnd<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FrontEnd")
            .field("spelling", &self.spelling.command(Verb::Run))
            .field("refused", &self.refused)
            .field("annotate", &self.annotate.map(|_| ".."))
            .finish()
    }
}

impl FrontEnd<'_> {
    fn annotated(&self, mut document: Value) -> Value {
        if let Some(annotate) = self.annotate {
            annotate(&mut document);
        }
        document
    }

    /// Add each refused mutation's refusal to its row of `checked`.
    fn refuse(&self, checked: &mut CorpusMutationCheck) {
        let Some(mutations) = checked.mutations.as_mut() else {
            return;
        };
        for row in &mut mutations.rows {
            if let Some(refusal) = self.refused.get(&row.id) {
                row.findings.push(Finding::refused(
                    refusal.reason.as_str(),
                    refusal.edit,
                    None,
                    refusal.detail.clone(),
                    Some(refusal.reason.next_step().to_owned()),
                ));
            }
        }
    }
}

/// Run `command` on `manifest` on the large stack kink's definitions need ([`on_stack`];
/// `report`, which loads no definition, on the calling thread): the document and the exit status,
/// or the message of the command's thread panicking.
pub fn dispatch(
    manifest: FlowManifest,
    command: FlowCommand,
    front: FrontEnd<'_>,
) -> Result<(Value, u8), String> {
    let verb = command.verb();
    if verb == Verb::Report {
        return Ok(run_command(&manifest, &command, &front));
    }
    on_stack(|| run_command(&manifest, &command, &front))
        .ok_or_else(|| format!("the {} thread panicked", verb.task()))
}

/// Run `command` on `manifest` on the calling thread, which must have the stack kink's
/// definitions need ([`dispatch`] provides it): the document and the exit status of
/// `kink-flow <verb>`.
pub fn run_command(
    manifest: &FlowManifest,
    command: &FlowCommand,
    front: &FrontEnd<'_>,
) -> (Value, u8) {
    let exit = |ok: bool| if ok { EXIT_OK } else { EXIT_CORPUS };
    let (document, status) = match command {
        FlowCommand::Check(options) => match &options.mutations {
            None => check_admission(manifest),
            Some(path) => {
                let mut checked = check_corpus_mutations(
                    manifest,
                    MutationList::read(path),
                    options.cache.as_deref(),
                );
                front.refuse(&mut checked);
                check_mutations_document(&checked, front.spelling)
            }
        },
        FlowCommand::Results { options, .. } => {
            let (document, ok) = crate::results::results(manifest, options);
            (document, exit(ok))
        }
        FlowCommand::Run {
            mutations,
            options,
            mode,
            ..
        } => {
            // `run_front` annotates every document it writes and returns.
            return match MutationList::read(mutations) {
                Err(error) => (
                    front.annotated(mutation_list_refused(&error.to_string(), options.schedule)),
                    EXIT_CORPUS,
                ),
                Ok(list) => {
                    let (document, ok) =
                        crate::search::run_front(manifest, &list, options, *mode, front);
                    let status = exit(ok && invalid_mutations(&document) == 0);
                    (document, status)
                }
            };
        }
        FlowCommand::Report { options, .. } => {
            let (document, ok) = crate::report::report_spelled(manifest, options, front.spelling);
            (document, exit(ok))
        }
        FlowCommand::Query { patterns, options } => match PatternList::read(patterns) {
            Err(error) => (pattern_list_refused(&error), EXIT_CORPUS),
            Ok(list) => {
                let (document, ok) = crate::query::query(manifest, &list, options);
                (document, exit(ok))
            }
        },
        FlowCommand::Fuzz { templates, request } => {
            fuzz_command(manifest, templates, request, front)
        }
    };
    (front.annotated(document), status)
}

/// `fuzz` on a decoded manifest.
fn fuzz_command(
    manifest: &FlowManifest,
    templates: &Path,
    request: &FuzzRequest,
    front: &FrontEnd<'_>,
) -> (Value, u8) {
    let templates = match TemplateList::read(templates) {
        Ok(templates) => templates,
        Err(error) => {
            return (
                crate::fuzz::input_refused("TEMPLATES.toml", &error),
                EXIT_CORPUS,
            );
        }
    };
    let (document, ok) = match &request.job {
        FuzzJobRequest::Kill {
            mutation,
            mutations,
        } => {
            let list = match MutationList::read(mutations) {
                Ok(list) => list,
                Err(error) => {
                    return (
                        crate::fuzz::input_refused("MUTATIONS.toml", &error),
                        EXIT_CORPUS,
                    );
                }
            };
            crate::fuzz::fuzz_front(
                manifest,
                &templates,
                &request.template,
                FuzzJob::Kill {
                    list: &list,
                    mutation,
                },
                &request.options,
                front,
            )
        }
        FuzzJobRequest::Rule { rule, fired } => crate::fuzz::fuzz_front(
            manifest,
            &templates,
            &request.template,
            FuzzJob::Rule {
                rule,
                fired: *fired,
            },
            &request.options,
            front,
        ),
        FuzzJobRequest::Pattern { id, patterns } => {
            let list = match PatternList::read(patterns) {
                Ok(list) => list,
                Err(error) => {
                    return (
                        crate::fuzz::input_refused("PATTERNS.toml", &error),
                        EXIT_CORPUS,
                    );
                }
            };
            crate::fuzz::fuzz_front(
                manifest,
                &templates,
                &request.template,
                FuzzJob::Pattern { list: &list, id },
                &request.options,
                front,
            )
        }
    };
    (document, if ok { EXIT_OK } else { EXIT_CORPUS })
}

/// [`run_command`] of `command` on the manifest at `path`, as kink-flow runs it, on the calling
/// thread; a manifest that does not decode gives the command's refusal
/// ([`FlowCommand::manifest_refused`]).
fn on_manifest(path: &Path, command: &FlowCommand) -> (Value, u8) {
    match FlowManifest::read(path) {
        Err(error) => (command.manifest_refused(&error), EXIT_CORPUS),
        Ok(manifest) => run_command(&manifest, command, &FrontEnd::default()),
    }
}

/// Options of `kink-flow check`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CheckOptions {
    /// A mutation list to resolve against the specification ([`crate::check`]).
    pub mutations: Option<PathBuf>,
    /// The cache directory whose result records decide `unmatched-rule` and `unapplied-rule`;
    /// default `<directory of FLOW.toml>/.kink-flow`. Nothing is written to it.
    pub cache: Option<PathBuf>,
}

fn check_options(args: &[String]) -> Result<CheckOptions, String> {
    let mut options = CheckOptions::default();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--mutations" if options.mutations.is_none() => {
                let list = args.next().ok_or("--mutations needs a file or directory")?;
                options.mutations = Some(PathBuf::from(list));
            }
            "--cache" if options.cache.is_none() => {
                let directory = args.next().ok_or("--cache needs a directory")?;
                options.cache = Some(PathBuf::from(directory));
            }
            _ => return Err(format!("unexpected argument {arg:?}")),
        }
    }
    Ok(options)
}

fn output_format(value: Option<&String>) -> Result<OutputFormat, String> {
    let value = value.ok_or("--output needs json or verdicts")?;
    match value.as_str() {
        "json" => Ok(OutputFormat::Json),
        "verdicts" => Ok(OutputFormat::Verdicts),
        _ => Err(format!("--output {value:?}: expected json or verdicts")),
    }
}

fn results_options(args: &[String]) -> Result<(ResultsOptions, OutputFormat), String> {
    let mut options = ResultsOptions::default();
    let mut output = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--output" if output.is_none() => output = Some(output_format(args.next())?),
            "--verify" if !options.verify => options.verify = true,
            "--cache" if options.cache.is_none() => {
                let directory = args.next().ok_or("--cache needs a directory")?;
                options.cache = Some(PathBuf::from(directory));
            }
            "--mutations" if options.mutations.is_none() => {
                let list = args.next().ok_or("--mutations needs a file or directory")?;
                options.mutations = Some(PathBuf::from(list));
            }
            _ => return Err(format!("unexpected argument {arg:?}")),
        }
    }
    Ok((options, output.unwrap_or_default()))
}

fn run_options(args: &[String]) -> Result<(RunOptions, RunMode, OutputFormat), String> {
    let mut options = RunOptions::default();
    let mut mode = RunMode::Search;
    let mut order = None;
    let mut output = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--output" if output.is_none() => output = Some(output_format(args.next())?),
            "--verify" if mode == RunMode::Search => mode = RunMode::Verify,
            "--order" if order.is_none() => {
                let value = args.next().ok_or("--order needs cost or corpus")?;
                order = Some(match value.as_str() {
                    "cost" => ProgramOrder::Cost,
                    "corpus" => ProgramOrder::Corpus,
                    _ => return Err(format!("--order {value:?}: expected cost or corpus")),
                });
                options.order = order.unwrap_or_default();
            }
            "--compile-workers" if options.compile_workers.is_none() => {
                let value = args.next().ok_or("--compile-workers needs a number")?;
                options.compile_workers = Some(
                    value
                        .parse::<usize>()
                        .ok()
                        .filter(|workers| *workers >= 1)
                        .ok_or_else(|| {
                            format!("--compile-workers {value:?}: expected a positive integer")
                        })?,
                );
            }
            "--no-memo" if options.memo == MemoUse::On => options.memo = MemoUse::Off,
            "--full" if options.schedule == ScheduleMode::FirstKill => {
                options.schedule = ScheduleMode::Full;
            }
            "--only" => {
                let id = args.next().ok_or("--only needs a mutation id")?;
                if !options.only.contains(id) {
                    options.only.push(id.clone());
                }
            }
            "--cache" if options.cache.is_none() => {
                let directory = args.next().ok_or("--cache needs a directory")?;
                options.cache = Some(PathBuf::from(directory));
            }
            _ => return Err(format!("unexpected argument {arg:?}")),
        }
    }
    // Under `Full` no test is skipped, so the order changes no cell in the no-Z3 profile; under
    // Z3, where a mutant's reused backend carries solver answers from one program to the next, a
    // fixed order is the reproducible one.
    if options.schedule == ScheduleMode::Full && order.is_some() {
        return Err(
            "--order orders the first-kill search; --full runs every program in corpus order"
                .to_owned(),
        );
    }
    Ok((options, mode, output.unwrap_or_default()))
}

fn query_options(args: &[String]) -> Result<QueryOptions, String> {
    let mut options = QueryOptions::default();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--verify" if !options.verify => options.verify = true,
            "--only" => {
                let id = args.next().ok_or("--only needs a pattern id")?;
                if !options.only.contains(id) {
                    options.only.push(id.clone());
                }
            }
            "--cache" if options.cache.is_none() => {
                let directory = args.next().ok_or("--cache needs a directory")?;
                options.cache = Some(PathBuf::from(directory));
            }
            _ => return Err(format!("unexpected argument {arg:?}")),
        }
    }
    Ok(options)
}

/// A parsed `kink-flow fuzz` command line (after FLOW.toml and TEMPLATES.toml).
#[derive(Clone, Debug)]
pub struct FuzzRequest {
    pub template: String,
    pub job: FuzzJobRequest,
    pub options: FuzzOptions,
}

/// The job a `kink-flow fuzz` command line names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FuzzJobRequest {
    /// `--kill MUTATION --mutations MUTATIONS.toml`.
    Kill {
        mutation: String,
        mutations: PathBuf,
    },
    /// `--matched RULE` (`fired` false) or `--fired RULE`: a rule's `matched_by` or `fired_by`.
    Rule { rule: String, fired: bool },
    /// `--pattern ID --patterns PATTERNS.toml`.
    Pattern { id: String, patterns: PathBuf },
}

fn number(flag: &str, value: Option<&String>) -> Result<u64, String> {
    let value = value.ok_or_else(|| format!("{flag} needs a number"))?;
    value
        .parse::<u64>()
        .map_err(|_| format!("{flag} {value:?}: expected a nonnegative integer"))
}

/// The usage error of a `fuzz` command line that names more than one job.
const ONE_JOB: &str = "give one job: --kill, --matched, --fired or --pattern";

/// `kink-flow fuzz`'s options; a job's list is `--mutations` or `--patterns`, else the front
/// end's `files`.
fn fuzz_options(args: &[String], files: &CommandFiles) -> Result<FuzzRequest, String> {
    let mut options = FuzzOptions::default();
    let (mut template, mut mutation, mut mutations) = (None, None, None);
    let (mut rule, mut pattern, mut patterns, mut fired) = (None, None, None, false);
    let (mut budget, mut seed, mut max_work, mut time_limit) = (None, None, None, None);
    let (mut one_path, mut no_confirm, mut no_filter) = (false, false, false);
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--template" if template.is_none() => {
                template = Some(args.next().ok_or("--template needs a template id")?.clone());
            }
            "--kill" if mutation.is_none() => {
                mutation = Some(args.next().ok_or("--kill needs a mutation id")?.clone());
            }
            "--mutations" if mutations.is_none() => {
                mutations = Some(PathBuf::from(
                    args.next().ok_or("--mutations needs a file or directory")?,
                ));
            }
            // No rule is spelled with a leading `--` (a `FILE:LINE`, a label or a compiled id),
            // so an option there is a missing rule, not a rule kink-flow would then refuse.
            flag @ ("--matched" | "--fired") => {
                if rule.is_some() {
                    return Err(ONE_JOB.into());
                }
                let value = args
                    .next()
                    .filter(|value| !value.starts_with("--"))
                    .ok_or_else(|| format!("{flag} needs a rule"))?;
                rule = Some(value.clone());
                fired = flag == "--fired";
            }
            "--reach" => {
                return Err(
                    "--reach RULE is --matched RULE, and --reach RULE --fired is --fired \
                            RULE: each names the predicate its job targets"
                        .into(),
                );
            }
            "--pattern" if pattern.is_none() => {
                pattern = Some(args.next().ok_or("--pattern needs a pattern id")?.clone());
            }
            "--patterns" if patterns.is_none() => {
                patterns = Some(PathBuf::from(args.next().ok_or("--patterns needs a file")?));
            }
            "--attempts" => {
                return Err(
                    "--attempts: there is no seed retry; when kink refuses the shrunk witness the \
                     unshrunk one is confirmed, and nothing more (fz26 D33)"
                        .into(),
                );
            }
            "--cases" if budget.is_none() => {
                let cases = number("--cases", args.next())?;
                if cases == 0 {
                    return Err("--cases 0: give at least one case".into());
                }
                budget = Some(k_rust_fuzz::Budget::Cases(cases));
            }
            "--work" if budget.is_none() => {
                let work = number("--work", args.next())?;
                if work == 0 {
                    return Err("--work 0: give a positive work budget".into());
                }
                budget = Some(k_rust_fuzz::Budget::Work(work));
            }
            "--seed" if seed.is_none() => seed = Some(number("--seed", args.next())?),
            "--max-work" if max_work.is_none() => {
                let work = number("--max-work", args.next())?;
                if work == 0 {
                    return Err("--max-work 0: give a positive bound".into());
                }
                max_work = Some(work);
            }
            "--time-limit-ms" if time_limit.is_none() => {
                time_limit = Some(number("--time-limit-ms", args.next())?);
            }
            "--assume-joined" => {
                let name = args
                    .next()
                    .ok_or("--assume-joined needs a finding's name")?;
                if name.trim().is_empty() {
                    return Err("--assume-joined needs a nonempty name".into());
                }
                if !options.assume_joined.contains(name) {
                    options.assume_joined.push(name.clone());
                }
            }
            "--one-path" if !one_path => one_path = true,
            "--no-confirm" if !no_confirm => no_confirm = true,
            "--no-filter" if !no_filter => no_filter = true,
            "--cache" if options.cache.is_none() => {
                let directory = args.next().ok_or("--cache needs a directory")?;
                options.cache = Some(PathBuf::from(directory));
            }
            _ => return Err(format!("unexpected argument {arg:?}")),
        }
    }
    let template = template.ok_or("give --template ID")?;
    let job = match (mutation, rule, pattern) {
        (Some(mutation), None, None) => {
            if patterns.is_some() {
                return Err("--patterns belongs to --pattern".into());
            }
            let mutations = mutations
                .or_else(|| files.mutations.clone())
                .ok_or("--kill needs --mutations MUTATIONS.toml")?;
            FuzzJobRequest::Kill {
                mutation,
                mutations,
            }
        }
        (None, Some(rule), None) => {
            if mutations.is_some() || patterns.is_some() {
                return Err("--mutations and --patterns belong to --kill and --pattern".into());
            }
            FuzzJobRequest::Rule { rule, fired }
        }
        (None, None, Some(id)) => {
            if mutations.is_some() {
                return Err("--mutations belongs to --kill".into());
            }
            if !options.assume_joined.is_empty() {
                return Err(
                    "--assume-joined: a pattern job reads no data end, so it takes no assumed \
                     name"
                        .into(),
                );
            }
            let patterns = patterns
                .or_else(|| files.patterns.clone())
                .ok_or("--pattern needs --patterns PATTERNS.toml")?;
            FuzzJobRequest::Pattern { id, patterns }
        }
        (None, None, None) => {
            return Err(
                "give the job: --kill MUTATION --mutations MUTATIONS.toml, --matched RULE, \
                        --fired RULE, or --pattern ID --patterns PATTERNS.toml"
                    .into(),
            );
        }
        _ => return Err(ONE_JOB.into()),
    };
    options.confirm = !no_confirm;
    options.filter = !no_filter;
    if let Some(budget) = budget {
        options.budget = budget;
    }
    options.seed = seed.unwrap_or(0);
    options.max_work = max_work;
    options.time_limit_ms = time_limit;
    if one_path {
        options.paths = k_rust_fuzz::PathMode::OnePath;
    }
    Ok(FuzzRequest {
        template,
        job,
        options,
    })
}

fn report_options(args: &[String]) -> Result<(ReportOptions, OutputFormat), String> {
    let mut options = ReportOptions::default();
    let mut output = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--output" if output.is_none() => output = Some(output_format(args.next())?),
            "--cache" if options.cache.is_none() => {
                let directory = args.next().ok_or("--cache needs a directory")?;
                options.cache = Some(PathBuf::from(directory));
            }
            _ => return Err(format!("unexpected argument {arg:?}")),
        }
    }
    Ok((options, output.unwrap_or_default()))
}

/// `kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID (--kill MUTATION --mutations
/// MUTATIONS.toml | --matched RULE | --fired RULE | --pattern ID --patterns PATTERNS.toml) [options]
/// [--no-confirm] [--no-filter]`: the fuzz document ([`crate::fuzz`]) and the exit
/// status: [`EXIT_OK`] when the job reached a verdict (`stopped` is `null`, `budget`,
/// `client-refused`, `unconfirmed`, `assembly-mismatch`, `equivalent`, `rejected-out` or
/// `time-limit`); [`EXIT_CORPUS`] when an input, the template or the mutation is refused
/// (`refused`), the campaign is `not-comparable`, or it `aborted` (the README's and the guide's
/// table).
pub fn fuzz(manifest: &Path, templates: &Path, request: &FuzzRequest) -> (Value, u8) {
    on_manifest(
        manifest,
        &FlowCommand::Fuzz {
            templates: templates.to_path_buf(),
            request: request.clone(),
        },
    )
}

/// `kink-flow query FLOW.toml PATTERNS.toml [--only ID]... [--verify] [--cache DIR]`: the query
/// document (flow F-18, [`crate::query`]) and the exit status: [`EXIT_OK`] when every selected
/// (pattern, program) got its answer (`hit`, `no`, `unknown` or `invalid-pattern`; a refuted claim
/// included); [`EXIT_CORPUS`] when the manifest, the pattern list, the specification or a program
/// is refused, a search failed, an answer's record could not be written, or `--verify` found a
/// stored answer that differs from a live one.
pub fn query(manifest: &Path, patterns: &Path, options: &QueryOptions) -> (Value, u8) {
    on_manifest(
        manifest,
        &FlowCommand::Query {
            patterns: patterns.to_path_buf(),
            options: options.clone(),
        },
    )
}

/// `kink-flow report FLOW.toml [--cache DIR] [--output json|verdicts]`: the run document the last
/// `run` wrote, as `run` printed it, and [`EXIT_OK`]; or a `kink-flow-report` document saying why
/// there is none (`missing`, `unreadable`) and [`EXIT_CORPUS`], which is also the status when the
/// manifest does not decode. `--output verdicts` renders the same document ([`crate::verdicts`]).
pub fn report(manifest: &Path, options: &ReportOptions) -> (Value, u8) {
    on_manifest(
        manifest,
        &FlowCommand::Report {
            options: options.clone(),
            output: OutputFormat::Json,
        },
    )
}

/// `kink-flow run FLOW.toml MUTATIONS [--only ID]... [--verify] [--cache DIR]`: the run
/// document (README 5.6, 7.5) and the exit status: [`EXIT_OK`] when every selected mutation got
/// its status (survivors and timeouts included) and none is invalid; [`EXIT_CORPUS`] when the
/// manifest, the mutation list, the specification or a program is refused, a selected mutation
/// is invalid (`invalid-mutation` or `not-admitted`: [`invalid_mutations`]), a run failed, a
/// cache file could not be written, no program is comparable, a baseline run no longer matches
/// its cached result (the run then stops), or `--verify` found a cached outcome that differs
/// from a live run.
pub fn run(manifest: &Path, mutations: &Path, options: &RunOptions) -> (Value, u8) {
    run_mode(manifest, mutations, options, RunMode::Search)
}

/// `kink-flow run` ([`RunMode::Search`]) or `kink-flow run --verify` ([`RunMode::Verify`]);
/// see [`run`].
pub fn run_mode(
    manifest: &Path,
    mutations: &Path,
    options: &RunOptions,
    mode: RunMode,
) -> (Value, u8) {
    on_manifest(
        manifest,
        &FlowCommand::Run {
            mutations: mutations.to_path_buf(),
            options: options.clone(),
            mode,
            output: OutputFormat::Json,
        },
    )
}

/// The number of a run document's rows whose mutation its author must fix before it is judged:
/// status `invalid-mutation` (it does not resolve, or a front end refused it) or `not-admitted` (its
/// mutant does not compile, or may have no model: `inconsistent-mutant`). Every other status is a
/// verdict about the corpus or a fault of the tool or the host, not of the mutation.
pub fn invalid_mutations(document: &Value) -> u64 {
    [crate::search::INVALID_MUTATION, "not-admitted"]
        .iter()
        .map(|status| document["counts"][*status].as_u64().unwrap_or(0))
        .sum()
}

/// `kink-flow results FLOW.toml [--verify] [--cache DIR]`: the results document (README 5.3)
/// and the exit status: [`EXIT_OK`] unless the manifest, the specification or a program is
/// refused, a run failed, a record could not be written or `--verify` found a mismatch.
/// A timeout or unknown program is not an error: it is reported, and it cannot kill.
pub fn results(manifest: &Path, options: &ResultsOptions) -> (Value, u8) {
    on_manifest(
        manifest,
        &FlowCommand::Results {
            options: options.clone(),
            output: OutputFormat::Json,
        },
    )
}

/// `kink-flow check FLOW.toml`: the check document and the exit status.
pub fn check(manifest: &Path) -> (Value, u8) {
    check_with(manifest, &CheckOptions::default())
}

/// `kink-flow check FLOW.toml [--mutations MUTATIONS] [--cache DIR]`: the check document and the
/// exit status. With a mutation list, every mutation is also resolved against the admitted
/// specification and no program runs ([`crate::check`]): [`check_corpus_mutations`] then
/// [`check_mutations_document`], with nothing added between them.
pub fn check_with(manifest: &Path, options: &CheckOptions) -> (Value, u8) {
    on_manifest(manifest, &FlowCommand::Check(options.clone()))
}

/// `check --mutations` before it is rendered: the admission of the specification and the
/// programs, the mutation list, and, when the specification is admitted and the list decodes, the
/// check of every mutation ([`MutationCheck`]) and the coverage that decided `unmatched-rule` and
/// `unapplied-rule`. A front end adds its own findings to [`Self::mutations`] (the admitted
/// specification is `admission.spec`) and renders with [`check_mutations_document`].
#[derive(Debug)]
pub struct CorpusMutationCheck {
    pub admission: FlowAdmission,
    /// The decoded list, or why it does not decode.
    pub list: Result<MutationList, ManifestError>,
    /// `None` when the specification is refused or the list does not decode.
    pub mutations: Option<MutationCheck>,
    /// `None` when the specification is refused.
    pub coverage: Option<CorpusCoverage>,
}

/// Admit `manifest`'s specification and programs, read the cached coverage (from `cache`, default
/// `.kink-flow/` next to `FLOW.toml`; nothing is written) and check every mutation of `list`;
/// nothing is compiled or run.
pub fn check_corpus_mutations(
    manifest: &FlowManifest,
    list: Result<MutationList, ManifestError>,
    cache: Option<&Path>,
) -> CorpusMutationCheck {
    let (record, admitted) = admit_spec(manifest);
    let Some((spec, mut inputs)) = admitted else {
        return CorpusMutationCheck {
            admission: FlowAdmission {
                record,
                spec: None,
                programs: Vec::new(),
            },
            list,
            mutations: None,
            coverage: None,
        };
    };
    let (programs, coverage) = {
        let mut session = inputs.session(&spec);
        let programs = manifest
            .programs
            .iter()
            .map(|program| session.admit(program))
            .collect::<Vec<_>>();
        let cache = cache_directory(manifest, cache);
        (programs, corpus_coverage(&spec, manifest, &session, &cache))
    };
    let mutations = list
        .as_ref()
        .ok()
        .map(|list| check_mutations(manifest, &spec.loaded, list, Some(&coverage)));
    CorpusMutationCheck {
        admission: FlowAdmission {
            record,
            spec: Some(spec),
            programs,
        },
        list,
        mutations,
        coverage: Some(coverage),
    }
}

/// The document of `check --mutations` and its exit status: the check document
/// ([`check_document`]) with `mutation_list`, `mutations` and `coverage`, and [`EXIT_OK`] when
/// no fact known before any mutant runs makes a verdict impossible
/// ([`FlowAdmission::verdicts_possible`]), the list decodes and no mutation is refused (by
/// resolution or by a finding with `refusal: true`), else [`EXIT_CORPUS`]. Next steps are spelled
/// by `spelling`.
pub fn check_mutations_document(
    checked: &CorpusMutationCheck,
    spelling: &dyn CommandSpelling,
) -> (Value, u8) {
    let mut document = check_document(&checked.admission);
    match &checked.list {
        Err(error) => {
            document["mutation_list"] = json!({"outcome": "refused", "detail": error.to_string()});
        }
        Ok(_) if checked.admission.spec.is_none() => {}
        Ok(_) => {
            document["mutation_list"] = json!({"outcome": "ok", "detail": null});
            if let Some(mutations) = &checked.mutations {
                document["mutations"] = mutations.value();
            }
            if let Some(coverage) = &checked.coverage {
                document["coverage"] = coverage.value(spelling);
            }
        }
    }
    let refused = checked.list.is_err()
        || checked
            .mutations
            .as_ref()
            .is_some_and(MutationCheck::refused);
    let status = if checked.admission.verdicts_possible() && !refused {
        EXIT_OK
    } else {
        EXIT_CORPUS
    };
    (document, status)
}

/// `kink-flow check FLOW.toml` without a mutation list: admission alone, and [`EXIT_OK`] exactly
/// when no fact known before any mutant runs makes a verdict impossible
/// ([`FlowAdmission::verdicts_possible`]).
fn check_admission(manifest: &FlowManifest) -> (Value, u8) {
    let admission = admit(manifest);
    let status = if admission.verdicts_possible() {
        EXIT_OK
    } else {
        EXIT_CORPUS
    };
    (check_document(&admission), status)
}

/// The version of the check document: 2 adds `mutation_list`, `mutations` and `coverage` (null
/// without `--mutations`); 3 adds `spec.exclusion` and the program outcome `excluded`, and
/// exits 1 when any program cannot be judged on the baseline, a definition exclusion included;
/// 4 adds `data` and `spec.baseline_findings`, and exits 1 when the baseline has no data under
/// `[spec] assume_joined` ([`FlowAdmission::verdicts_possible`]); 5 adds `result`, the slots and
/// the cells the programs' second slot compares ([`crate::observed`]), and the specification's
/// refusal at stage `result`; 6 (CF-03) adds `spec.short_circuit`, the rules the short-circuit
/// analysis flags, which are no longer a definition exclusion: each run of such a definition is
/// judged by k-rust's list of that run, so no program is `excluded` for them before it runs; and
/// a program whose initial configuration applies a reading-dependent function is `excluded` at
/// stage `initial-state` only when its depth-0 run lists a reading that counts against it; 7
/// gives `unreached-rule` for an edited rule no comparable program reached (k-rust `matched`),
/// whatever the edit (before, an edit that left the `requires` alone was warned about when no
/// program applied the rule), and adds `unapplied-rule` for one some program reached and none
/// applied (`applied`), since `check` compiles no mutant and so cannot read `run`'s witness rule
/// ([`crate::check`]); 8 (CF-40c2) names the first `unmatched-rule`, after the predicate it
/// reads (k-rust `matched`), so that each coverage predicate has one name in every kink-flow
/// document, and says `matches` for `reaches` in both warnings' text.
pub const CHECK_VERSION: u64 = 8;

fn header(spec: Value, programs: Vec<Value>, data: Value, result: Value) -> Value {
    json!({
        "schema": "kink-flow-check",
        "version": CHECK_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "spec": spec,
        "programs": programs,
        "data": data,
        "result": result,
        "mutation_list": null,
        "mutations": null,
        "coverage": null,
    })
}

/// The document of a manifest that does not decode: the spec is refused at stage
/// `manifest` with the error, which names the key or program.
pub fn manifest_refused(error: &ManifestError) -> Value {
    header(
        json!({
            "outcome": "refused",
            "stage": "manifest",
            "reason": "invalid-manifest",
            "detail": error.to_string(),
            "files": [],
            "exclusion": null,
            "short_circuit": null,
            "baseline_findings": null,
        }),
        Vec::new(),
        Value::Null,
        Value::Null,
    )
}

/// The check document of an admission. `spec.exclusion` is the definition exclusion of the admitted
/// specification ([`crate::exclusion::definition_exclusion`], null when there is none or the
/// specification is refused), and `spec.short_circuit` the rules its short-circuit analysis flags
/// ([`crate::exclusion::short_circuit`], null when it flags none), which make no program
/// `excluded`: a run of such a definition is judged by its own list of readings. A program is `ok`,
/// `refused` (stage, reason and detail of the refusal), or `excluded`: admitted, but every run of
/// it on the baseline is excluded before it runs (stage `definition` or `initial-state`, the
/// exclusion's name as reason, and why). `data` is the baseline's full critical-pair check under
/// `[spec] assume_joined`, as the run, `results` and `query` documents print it (kink-native
/// `DataFacts::value`), and `spec.baseline_findings` says why the baseline has no data
/// ([`baseline_findings`]); `result` names the slots and the cells the programs' second slot
/// compares ([`crate::observed::ResultProjection::value`]); all three are null when the
/// specification is refused.
pub fn check_document(admission: &FlowAdmission) -> Value {
    let record = &admission.record;
    let refusal = record.refusal.as_ref();
    let exclusion = admission
        .spec
        .as_ref()
        .filter(|spec| spec.exclusions.definition_exclusion().is_some())
        .map_or(Value::Null, |spec| {
            crate::exclusion::definition_exclusion(
                spec,
                &crate::evidence::EndReader::of(&spec.compiled),
            )
        });
    let short_circuit = admission
        .spec
        .as_ref()
        .filter(|spec| spec.exclusions.short_circuit_flagged())
        .map_or(Value::Null, |spec| {
            crate::exclusion::short_circuit(spec, &crate::evidence::EndReader::of(&spec.compiled))
        });
    let spec = json!({
        "outcome": if refusal.is_some() { "refused" } else { "admitted" },
        "stage": refusal.map(|r| &r.stage),
        "reason": refusal.map(|r| &r.reason),
        "detail": refusal.map(|r| &r.detail),
        "files": record
            .files
            .iter()
            .map(|f| json!({"name": f.name, "sha256": f.sha256.to_string()}))
            .collect::<Vec<_>>(),
        "exclusion": exclusion,
        "short_circuit": short_circuit,
        "baseline_findings": admission
            .spec
            .as_ref()
            .map_or(Value::Null, |spec| baseline_findings(&spec.data)),
    });
    let programs = admission
        .programs
        .iter()
        .map(|program| match (&program.outcome, &program.exclusion) {
            (Err(refusal), _) => json!({
                "id": program.id,
                "outcome": "refused",
                "stage": refusal.stage,
                "reason": refusal.reason,
                "detail": refusal.detail,
            }),
            (Ok(_), Some(exclusion)) => json!({
                "id": program.id,
                "outcome": "excluded",
                "stage": exclusion.scope.name(),
                "reason": exclusion.exclusion.name(),
                "detail": exclusion.detail(),
            }),
            (Ok(_), None) => json!({
                "id": program.id,
                "outcome": "ok",
                "stage": null,
                "reason": null,
                "detail": null,
            }),
        })
        .collect();
    let data = admission
        .spec
        .as_ref()
        .map_or(Value::Null, |spec| spec.data.value());
    let result = admission
        .spec
        .as_ref()
        .map_or(Value::Null, |spec| spec.result.value());
    header(spec, programs, data, result)
}

/// Why the baseline has no data under `[spec] assume_joined`, so that no mutation can have a
/// verdict but `unknown` (`baseline-findings`) and no query a `no`: null when it has data, else
/// `{detail, findings, incomplete}`. `findings` lists each finding no name assumes,
/// `{name, verdict, description, next}`, `next` being what to do about it
/// ([`finding_next`]); `incomplete` is null, or `{detail, next}` when the check did not read the
/// whole definition (kink-native `DataFacts::incomplete`); `detail` says both in one text,
/// naming at most [`crate::exclusion::DETAIL_CAUSES`] findings.
#[must_use]
pub fn baseline_findings(data: &kink_native::data::DataFacts) -> Value {
    if data.has_data() {
        return Value::Null;
    }
    let unnamed = data.unnamed();
    let incomplete = data.incomplete();
    let mut reasons = Vec::new();
    if !unnamed.is_empty() {
        reasons.push(format!(
            "has {} finding(s) that [spec] assume_joined leaves unnamed",
            unnamed.len()
        ));
    }
    if let Some(why) = &incomplete {
        reasons.push(format!("did not read the whole definition ({why})"));
    }
    let mut items = unnamed
        .iter()
        .map(|finding| {
            format!(
                "{} ({}: {}): {}",
                finding.name.as_deref().map_or_else(
                    || "a finding with no name".to_owned(),
                    |name| format!("`{name}`")
                ),
                finding.verdict.name(),
                finding.description,
                finding_next(finding)
            )
        })
        .collect::<Vec<_>>();
    let shown = items.len().min(crate::exclusion::DETAIL_CAUSES);
    let more = items.len() - shown;
    items.truncate(shown);
    if more > 0 {
        items.push(format!("and {more} more (findings)"));
    }
    if incomplete.is_some() {
        items.push(format!(
            "for what the check did not read: {INCOMPLETE_NEXT}"
        ));
    }
    json!({
        "detail": format!(
            "the baseline's full critical-pair check {}, so no end of the definition is data: \
             every mutation with a program to run is unknown (baseline-findings) and no query \
             answers no; {}",
            reasons.join(" and "),
            items.join("; ")
        ),
        "findings": unnamed
            .iter()
            .map(|finding| json!({
                "name": finding.name,
                "verdict": finding.verdict.name(),
                "description": finding.description,
                "next": finding_next(finding),
            }))
            .collect::<Vec<_>>(),
        "incomplete": incomplete.map(|why| json!({"detail": why, "next": INCOMPLETE_NEXT})),
    })
}

/// What to do when the full critical-pair check did not read the whole definition: no name
/// assumes what the check did not read, so only k-rust's checker can remove it.
const INCOMPLETE_NEXT: &str = "report it: it is a limit of k-rust's checker, and no [spec] \
                               assume_joined name can assume a part of the definition the check \
                               did not read";

/// What to do about a finding that `[spec] assume_joined` leaves unnamed, by what it is
/// (kink-native `FindingVerdict`): a name assumes the finding away, so naming it is right only
/// where the definition is right and the checker could not show it. A decided finding is a fact
/// about the definition as written and no name assumes it (admission refuses one,
/// `name-refused`); a genuine one has a ground input with two normal forms, so a name would be a
/// premise known to be false; an undecided one may be a limit of the checker, which the author
/// reviews; a finding with no name cannot be named at all.
#[must_use]
pub fn finding_next(finding: &kink_native::data::NamedFinding) -> String {
    use kink_native::data::FindingVerdict;
    let Some(name) = &finding.name else {
        return "fix the definition: the finding has no name, so no [spec] assume_joined entry \
                assumes it"
            .to_owned();
    };
    match finding.verdict {
        FindingVerdict::Decided => "fix the definition: a decided finding is a fact about the \
                                    definition as written, which no [spec] assume_joined name \
                                    assumes"
            .to_owned(),
        FindingVerdict::Genuine => format!(
            "fix the definition: a ground input of this pair has two normal forms, so the pair \
             does not join; naming `{name}` in [spec] assume_joined makes every verdict hold \
             only under a premise known to be false"
        ),
        FindingVerdict::Undecided => format!(
            "review it: if the definition is right here and the checker only could not show it \
             (the pair joins, the equation agrees with its hook or applies as written, the \
             precondition is met), name `{name}` in [spec] assume_joined; otherwise fix the \
             definition"
        ),
    }
}
