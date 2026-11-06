//! `krs kink <verb>`: the corpus loop over a KRS package, with kink as its engine.
//!
//! The front end builds the selected package once, in process, as `krs emit-k` does
//! ([`crate::CollectedDefinition::emit_k`]), keeps `kink/definition.k` equal to that emission
//! (the `emit` submodule), decodes `kink/FLOW.toml` with kink-flow's own decoder, binds its
//! `[spec] krs = { definition = .. }` declaration to that file, and runs the verb through
//! kink-flow's command layer ([`kink_flow::FlowCommand::parse`], [`kink_flow::dispatch`]) with
//! the options kink-flow's own command line takes. The engine is kink-flow's: admission,
//! resolution, the kill definition and the caches are those of a K corpus over the same file.
//!
//! The front end adds, on the way in, how a case's typed inputs and its expectation are read
//! (the encoding KRS derives from the definition's declared types, the `inputs` and `render`
//! submodules), the K names of the cells `[result]` names by Rust path (the `cells` submodule),
//! the exact K labels of the rules `[stop]` names by KRS item or label as
//! `krs run --stop-before` does (the `stop` submodule, over the native compile the `inputs`
//! submodule makes; a name that selects no rewrite rule refuses the corpus at stage `stop`,
//! reason `stop-unresolved`), and the mutations its own checks refuse (`checks`); on the way
//! out, the labels each `[stop]` name selects (`stop.krs.items`), the compared cells by Rust path
//! (`result.krs`), to every rule a document names, the KRS item and the Rust position the
//! sentence was emitted from (`annotate`), and next steps spelled as `krs kink` commands
//! (`spelling`).
//!
//! Every verb but `emit` prints one kink-flow document (or, with `--output verdicts`, its
//! deterministic rendering) with one more key, `definition`: the path of `kink/definition.k`
//! and whether the command that made the document found it `unchanged` or `written` it. A
//! stale file is rewritten, since a mutation is re-resolved against the K on every command and
//! refused when the text it replaces changed, so a rewrite can make a mutation stale but never
//! change what it means;
//! under `--locked` the command is refused instead (stage `definition`, reason
//! `definition-stale`), and `krs kink emit --check` is the gate a CI runs.
//!
//! `report` builds nothing. The stored run document is a file of the corpus's cache, whose place
//! depends on the corpus directory and `--cache` alone, so `report` reads the corpus manifest and
//! prints that document as the run printed it; its `definition` is the run's, since the run
//! stores the document with it. It judges no `definition.k`, so it takes no `--locked`.
//!
//! A package krs refuses, from its selection (an unknown package or facet, a manifest Cargo
//! cannot read) to its emission, is answered by krs's diagnostics on stderr and the verb's
//! document with its specification refused at stage `krs-build`, reason `krs-refused`; `emit`'s
//! document has the refusal as its `refusal`.

mod annotate;
mod cells;
mod checks;
mod emit;
mod inputs;
mod render;
mod spelling;
mod stop;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use kink_flow::{
    CommandFiles, FlowCommand, FrontEnd, KrsSpec, ManifestError, ManifestFile, MutationList,
    OutputFormat, SpecDecl, SpecSection, Verb, cli::FuzzJobRequest,
};
use krs_ir::measure::Measurement;
use serde_json::{Value, json};

use crate::command::plan_collection;
use crate::{
    Command, CommandError, CommandRequest, DiagnosticReports, DiagnosticSources, EmittedDefinition,
    FacetSelector, KrsCfg, MessageFormat, RegistrationMode,
};

pub use emit::DefinitionStatus;

/// The corpus directory's name inside the root package, when `--corpus` names none.
pub const CORPUS_DIRECTORY: &str = "kink";
/// The corpus manifest's name inside the corpus directory.
pub const MANIFEST_FILE: &str = "FLOW.toml";
/// The emitted definition's name inside the corpus directory.
pub const DEFINITION_FILE: &str = "definition.k";

/// The exit statuses of kink-flow's command line, which `krs kink` keeps: the four actions of
/// krs's executing commands (`crate::exit_status`). The command answered its question.
pub const EXIT_YES: u8 = kink_flow::cli::EXIT_YES;
/// The answer is a finding (the document says which).
pub const EXIT_NO: u8 = kink_flow::cli::EXIT_NO;
/// The question could not be asked: a usage error, or a refusal the document names (a package
/// krs refuses, a stale `definition.k` under `--locked` or `emit --check`, a refused corpus).
pub const EXIT_UNASKED: u8 = kink_flow::cli::EXIT_UNASKED;
/// No answer (a timeout, an unknown).
pub const EXIT_UNANSWERED: u8 = kink_flow::cli::EXIT_UNANSWERED;

/// One `krs kink` command line.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KinkRequest {
    /// Cargo manifest used for metadata and collector planning (`--manifest-path`).
    pub manifest_path: PathBuf,
    /// The selected root definition facet (`--package`, `--package-id`, `--definition`).
    pub root: FacetSelector,
    /// Composed dependency facets (`--dependency`).
    pub dependencies: Vec<FacetSelector>,
    /// KRS-owned rustc cfg values (`--cfg`).
    pub cfg: Vec<KrsCfg>,
    /// Descriptor registration mechanism of the generated collector.
    pub registration: RegistrationMode,
    /// `--profile`.
    pub profile: Option<krs_ir::RawKProfile>,
    /// Presentation of krs's diagnostics (`--message-format`).
    pub message_format: MessageFormat,
    /// `--corpus DIR`: the corpus directory; default `<root package directory>/kink`.
    pub corpus: Option<PathBuf>,
    /// `--locked`: refuse a `kink/definition.k` that differs from the emission instead of
    /// rewriting it.
    pub locked: bool,
    /// The verb and its own options.
    pub verb: KinkVerb,
}

/// What `krs kink` does.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum KinkVerb {
    /// `emit [--check]`: write `kink/definition.k`, or, with `check`, write nothing and fail
    /// when it differs from the emission.
    Emit {
        /// `--check`.
        check: bool,
    },
    /// A kink-flow verb with its options, which kink-flow's parser reads.
    Flow {
        /// The verb.
        verb: Verb,
        /// Every option after the verb that is not one of krs's own.
        options: Vec<String>,
    },
}

/// The result of a `krs kink` command: what it prints and how it exits.
#[derive(Debug)]
pub struct KinkOutcome {
    /// The bytes to write to stdout: the document, or its verdicts rendering.
    pub stdout: Vec<u8>,
    /// Lines for stderr after krs's diagnostics: a usage message, a refusal's text under
    /// `--output verdicts`, a panic of the command's thread.
    pub notes: Vec<String>,
    /// The exit status: [`EXIT_YES`], [`EXIT_NO`], [`EXIT_UNASKED`] or [`EXIT_UNANSWERED`].
    pub status: u8,
    /// The command line is not one `krs kink` reads: `status` is [`EXIT_UNASKED`] and the
    /// caller prints the usage after the notes.
    pub usage: bool,
    /// krs's warnings about the definition, reported as other krs commands report them.
    pub warnings: DiagnosticReports,
    /// krs's refusal of the package (planning, collection, lowering or emission), whose
    /// diagnostics the caller renders against `sources`.
    pub error: Option<CommandError>,
    /// The selected packages' source roots, for rendering diagnostics.
    pub sources: DiagnosticSources,
}

impl KinkOutcome {
    fn new(sources: DiagnosticSources) -> Self {
        Self {
            stdout: Vec::new(),
            notes: Vec::new(),
            status: EXIT_YES,
            usage: false,
            warnings: DiagnosticReports::default(),
            error: None,
            sources,
        }
    }

    fn usage(mut self, message: String) -> Self {
        self.notes.push(message);
        self.status = EXIT_UNASKED;
        self.usage = true;
        self
    }

    fn json(mut self, document: &Value, status: u8) -> Self {
        self.stdout = format!("{}\n", kink_flow::report::render(document)).into_bytes();
        self.status = status;
        self
    }
}

/// Run one `krs kink` command, recording its stages' timings in `measurement`.
#[must_use]
pub fn execute_kink(request: &KinkRequest, measurement: &mut Measurement) -> KinkOutcome {
    let mut sources = DiagnosticSources::default();
    let selection = selection_request(request);
    let planned = match plan_collection(&selection, None, measurement, &mut sources) {
        Ok(planned) => planned,
        Err(error) => return selection_refused(request, error, KinkOutcome::new(sources)),
    };
    let outcome = KinkOutcome::new(sources);
    let root = planned.root_directory();
    let corpus = match (&request.corpus, &root) {
        (Some(corpus), _) => corpus.clone(),
        (None, Some(root)) => root.join(CORPUS_DIRECTORY),
        (None, None) => {
            return outcome.usage("the root package has no directory; give --corpus DIR".into());
        }
    };
    match &request.verb {
        KinkVerb::Emit { check } => emit_command(
            planned,
            &corpus,
            root.as_deref(),
            *check,
            outcome,
            measurement,
        ),
        KinkVerb::Flow { verb, options } => {
            let paths = CorpusPaths {
                corpus: &corpus,
                root: root.as_deref(),
            };
            flow_command(
                request,
                planned,
                paths,
                *verb,
                options,
                outcome,
                measurement,
            )
        }
    }
}

/// The detail of a document refused at stage `krs-build`.
fn krs_refused_detail(error: &CommandError) -> String {
    format!(
        "krs refuses the package, so no K is emitted for the corpus (stderr has krs's \
         diagnostics): {error}"
    )
}

/// The answer to a package krs refused while selecting it, before its directory, and so the
/// corpus's, is known: krs's diagnostics, and the verb's document refused at stage `krs-build`.
/// The verb's options are parsed against the corpus the command names, else `kink/` beside
/// `--manifest-path`, which is the package's when the manifest is the package's own; when its
/// layout files are not there, the document is the verb's refused one under kink-flow's default
/// options (`--output json`, a first-kill run).
fn selection_refused(
    request: &KinkRequest,
    error: CommandError,
    mut outcome: KinkOutcome,
) -> KinkOutcome {
    let detail = krs_refused_detail(&error);
    let corpus = request.corpus.clone().unwrap_or_else(|| {
        request
            .manifest_path
            .parent()
            .unwrap_or_else(|| Path::new(""))
            .join(CORPUS_DIRECTORY)
    });
    outcome.error = Some(error);
    match &request.verb {
        KinkVerb::Emit { check } => {
            let shown = request.corpus.as_ref().map_or_else(
                || format!("{CORPUS_DIRECTORY}/{DEFINITION_FILE}"),
                |corpus| emit::shown_path(&corpus.join(DEFINITION_FILE), None),
            );
            let document = emit::emit_document(&shown, None, *check, Some(&detail));
            outcome.json(&document, EXIT_UNASKED)
        }
        KinkVerb::Flow { verb, options } => {
            if let Ok(command) = command_files(&corpus, *verb, options)
                .and_then(|(files, options)| FlowCommand::parse(verb.as_str(), files, &options))
            {
                let document = refused(&command, "krs-build", "krs-refused", &detail);
                finish(outcome, &document, EXIT_UNASKED, command.output())
            } else {
                let document = refused_document(
                    verb.manifest_refused(&ManifestError::new("", &detail)),
                    "krs-build",
                    "krs-refused",
                    &detail,
                );
                outcome.json(&document, EXIT_UNASKED)
            }
        }
    }
}

/// Where a command's corpus is: its directory, and the root package's directory documents show
/// paths relative to.
#[derive(Clone, Copy)]
struct CorpusPaths<'a> {
    corpus: &'a Path,
    root: Option<&'a Path>,
}

/// A kink-flow verb: parse its options, read the corpus manifest, build the package, keep
/// `definition.k` fresh, and run the verb.
fn flow_command(
    request: &KinkRequest,
    planned: crate::command::PlannedCollection,
    paths: CorpusPaths<'_>,
    verb: Verb,
    options: &[String],
    mut outcome: KinkOutcome,
    measurement: &mut Measurement,
) -> KinkOutcome {
    let corpus = paths.corpus;
    let spelling = spelling::KrsSpelling::new(request);
    let command = match command_files(corpus, verb, options)
        .and_then(|(files, options)| FlowCommand::parse(verb.as_str(), files, &options))
    {
        Ok(command) => command,
        Err(message) => return outcome.usage(message),
    };
    let output = command.output();
    // The corpus manifest is read before the package is built, so a corpus that cannot run is
    // refused without a build.
    let manifest_path = corpus.join(MANIFEST_FILE);
    let declared = match corpus_manifest(&manifest_path, &request.root.definition) {
        Ok(declared) => declared,
        Err(error) => {
            let document = command.manifest_refused(&error);
            return finish(outcome, &document, EXIT_UNASKED, output);
        }
    };
    // `report` prints the stored run document, which needs nothing the build makes: no package is
    // built, and nothing is lowered or emitted.
    if let FlowCommand::Report { options, .. } = &command {
        let (document, ok) = measurement.timings.span("kink.report", |_| {
            kink_flow::report::stored_report(&declared.directory, options, &spelling)
        });
        let status = if ok {
            kink_flow::cli::run_status(&document)
        } else {
            EXIT_UNASKED
        };
        return finish(outcome, &document, status, output);
    }
    let retain = judges_mutations(&command);
    tell_progress(&command, "run: building the package and emitting its K");
    let (emitted, kept) = match build(planned, &mut outcome, measurement, retain) {
        Ok(built) => built,
        Err(error) => {
            let document = refused(
                &command,
                "krs-build",
                "krs-refused",
                &krs_refused_detail(&error),
            );
            outcome.error = Some(error);
            return finish(outcome, &document, EXIT_UNASKED, output);
        }
    };
    let definition_path = corpus.join(DEFINITION_FILE);
    let status = measurement.timings.span("kink.definition", |_| {
        emit::freshen(&definition_path, &emitted.definition, !request.locked)
    });
    let shown = emit::shown_path(&definition_path, paths.root);
    let status = match status {
        Ok(status) => status,
        Err(error) => {
            let document = refused(
                &command,
                "definition",
                error.reason(),
                &error.detail(&shown),
            );
            return finish(outcome, &document, EXIT_UNASKED, output);
        }
    };
    if status == DefinitionStatus::Stale {
        let mut document = refused(
            &command,
            "definition",
            "definition-stale",
            &format!(
                "{shown} differs from the K this krs emits for the package's current sources \
                 (--locked); run `{}` and commit the file",
                spelling.emit()
            ),
        );
        document["definition"] = emit::definition_value(&shown, status);
        return finish(outcome, &document, EXIT_UNASKED, output);
    }
    let definition = emit::definition_value(&shown, status);
    let observers = render::Observers::new(selection_request(request), outcome.sources.clone());
    run_flow(
        command,
        declared,
        Built {
            emitted: &emitted,
            kept,
            observers,
        },
        &spelling,
        definition,
        outcome,
        measurement,
    )
}

/// Whether `command` judges a mutation list, so that the front end's checks need the lowering
/// the K is emitted from: `check --mutations`, `run`, a `fuzz` kill job.
fn judges_mutations(command: &FlowCommand) -> bool {
    match command {
        FlowCommand::Check(options) => options.mutations.is_some(),
        command => checks::run_list(command).is_some(),
    }
}

/// The mutation list `command` judges (`check --mutations`, `run`, a `fuzz` kill job), whose
/// refused edits its document names by their anchors.
fn judged_list(command: &FlowCommand) -> Option<PathBuf> {
    match command {
        FlowCommand::Check(options) => options.mutations.clone(),
        command => checks::run_list(command).map(|run| run.path.to_path_buf()),
    }
}

/// The lowering an emission is emitted from, kept in process for the front end's checks.
struct KeptLowering {
    retained: krs_compiler::RetainedLowering,
    lowered: krs_compiler::LoweredDefinition,
}

/// A command's emission and, when it judges mutations, the lowering kept with it, which
/// [`run_flow`] releases once the front end's checks are made; and the observers the corpus's
/// expectations name, prepared when one first names each.
struct Built<'a> {
    emitted: &'a EmittedDefinition,
    kept: Option<KeptLowering>,
    observers: render::Observers,
}

/// Run the parsed `command` on the corpus `declared`, bound to the fresh `definition.k` of
/// `emitted`; `definition` is the document's `definition` object.
fn run_flow(
    mut command: FlowCommand,
    declared: ManifestFile,
    built: Built<'_>,
    spelling: &spelling::KrsSpelling,
    definition: Value,
    mut outcome: KinkOutcome,
    measurement: &mut Measurement,
) -> KinkOutcome {
    let Built {
        emitted,
        kept,
        observers,
    } = built;
    let output = command.output();
    let verb = command.verb();
    tell_progress(&command, "run: binding the corpus to the emitted K");
    let (manifest, stop_items, result_names) =
        match bound_manifest(&command, declared, emitted, observers) {
            Ok(bound) => bound,
            Err(mut document) => {
                document["definition"] = definition;
                return finish(outcome, &document, EXIT_UNASKED, output);
            }
        };
    resolve_rule(&mut command, emitted);
    let annotator = annotate::Annotator::new(emitted, manifest.clone(), judged_list(&command))
        .naming_stop(stop_items)
        .naming_result(result_names);
    let sources = outcome.sources.clone();
    let baseline = kept.as_ref().map(|kept| checks::Baseline {
        emitted,
        retained: &kept.retained,
        lowered: &kept.lowered,
        sources: &sources,
    });
    // `check --mutations`: kink-flow's check, with the front end's findings added to each row.
    if let (FlowCommand::Check(options), Some(baseline)) = (&command, &baseline)
        && let Some(path) = &options.mutations
    {
        let checked = measurement.timings.span("kink.check", |_| {
            kink_flow::on_stack(|| {
                let mut checked = kink_flow::cli::check_corpus_mutations(
                    &manifest,
                    MutationList::read(path),
                    options.cache.as_deref(),
                );
                if let Some(rows) = checked.mutations.as_mut() {
                    checks::KrsChecks::new(baseline, spelling).annotate_check(rows);
                }
                let (mut document, status) =
                    kink_flow::cli::check_mutations_document(&checked, spelling);
                annotator.annotate(&mut document);
                (document, status)
            })
        });
        let Some((mut document, status_code)) = checked else {
            outcome
                .notes
                .push("krs kink: the check thread panicked".into());
            outcome.status = EXIT_UNASKED;
            return outcome;
        };
        document["definition"] = definition;
        return finish(outcome, &document, status_code, output);
    }
    // `run` and a `fuzz` kill job: the mutations the front end refuses run nothing.
    let Some(refused_mutations) = front_refusals(
        &command,
        baseline.as_ref(),
        spelling,
        &manifest,
        measurement,
    ) else {
        outcome
            .notes
            .push("krs kink: the mutation check thread panicked".into());
        outcome.status = EXIT_UNASKED;
        return outcome;
    };
    // Every check that reads the lowering is made: the dispatch, which can hold a kill search's
    // mutants for minutes, runs without the retained theory and its second Definition IR.
    drop(kept);
    // The annotation also sets `definition`, so that a run stores its document with it and
    // `report` prints what the run printed; both parts are idempotent.
    let annotate = |document: &mut Value| {
        annotator.annotate(document);
        document["definition"] = definition.clone();
    };
    let front = FrontEnd {
        spelling,
        refused: refused_mutations,
        annotate: Some(&annotate as &(dyn Fn(&mut Value) + Sync)),
        progress: command.shows_progress().then_some(&print_progress),
    };
    let span = format!("kink.{}", verb.as_str());
    let dispatched = measurement
        .timings
        .span(&span, |_| kink_flow::dispatch(manifest, command, front));
    let (document, status_code) = match dispatched {
        Ok(result) => result,
        Err(panicked) => {
            outcome.notes.push(format!("krs kink: {panicked}"));
            outcome.status = EXIT_UNASKED;
            return outcome;
        }
    };
    finish(outcome, &document, status_code, output)
}

/// The mutations of the list `command` runs (`run`, a `fuzz` kill job) that the front end's
/// checks over `baseline` refuse, by id: none for another command or a list that does not
/// decode, which kink-flow refuses; `None` when the check thread panicked.
fn front_refusals(
    command: &FlowCommand,
    baseline: Option<&checks::Baseline<'_>>,
    spelling: &spelling::KrsSpelling,
    manifest: &kink_flow::FlowManifest,
    measurement: &mut Measurement,
) -> Option<std::collections::BTreeMap<String, kink_flow::InvalidMutation>> {
    let (Some(run), Some(baseline)) = (checks::run_list(command), baseline) else {
        return Some(std::collections::BTreeMap::new());
    };
    let Ok(list) = MutationList::read(run.path) else {
        // kink-flow refuses a list that does not decode.
        return Some(std::collections::BTreeMap::new());
    };
    tell_progress(
        command,
        &format!(
            "run: checking the list's {} mutation{} against the lowering",
            list.mutations.len(),
            if list.mutations.len() == 1 { "" } else { "s" }
        ),
    );
    measurement.timings.span("kink.krs-checks", |_| {
        kink_flow::on_stack(|| {
            checks::KrsChecks::new(baseline, spelling).refusals(manifest, &list, &run)
        })
    })
}

/// A run's progress line on stderr as it happens, as `kink-flow run` prints it, under the same
/// condition ([`FlowCommand::shows_progress`]); stdout stays the document.
fn print_progress(line: &str) {
    eprintln!("krs kink: {line}");
}

/// [`print_progress`] of a phase the front end runs before kink-flow's (the build and the
/// emission, the binding of the corpus, the front end's checks of the list), when `command`
/// shows its progress: each line is printed as its phase starts, so a cold run that spends
/// minutes there is seen to be in it.
fn tell_progress(command: &FlowCommand, line: &str) {
    if command.shows_progress() {
        print_progress(line);
    }
}

/// The corpus `declared` bound to the K of `emitted`, with what only the front end knows of it
/// ([`with_front_end_facts`], the expectations' views evaluated in `observers`), the cells
/// `[result]` names by Rust path or K name as the K names kink-flow reads ([`cells::bind`]), and
/// the rules `[stop]` names by KRS item or label as the exact K labels kink-flow reads
/// ([`stop::bind`]); the labels each `[stop]` name selects, and the cells by path that the
/// documents' `result` gains; or `command`'s document refusing the corpus.
fn bound_manifest(
    command: &FlowCommand,
    declared: ManifestFile,
    emitted: &EmittedDefinition,
    observers: render::Observers,
) -> Result<(kink_flow::FlowManifest, Option<Value>, cells::ResultNames), Value> {
    let manifest = declared
        .bind(Some(bound_spec(emitted)))
        .map_err(|error| command.manifest_refused(&error))?;
    let names = cells::CellNames::of(&emitted.ir);
    let (manifest, readings) = cells::bind(manifest, &names)
        .map_err(|unbound| refused(command, "result", unbound.reason, &unbound.detail))?;
    let result_names = cells::ResultNames::new(names, readings);
    // The decoder reads typed inputs and binds programs, and fuzz templates' own, to the main
    // parameter; it compiles nothing until one needs it, and the stop's names resolve over the
    // same compile.
    let decoder = Arc::new(inputs::KrsInputs::new(emitted.ir.clone()));
    let (manifest, stop_items) = stop::bind(
        with_front_end_facts(manifest, emitted, decoder.clone(), observers),
        &decoder,
    )
    .map_err(|unbound| refused(command, "stop", unbound.reason, &unbound.detail))?;
    Ok((manifest, stop_items, result_names))
}

/// `manifest` with what only the front end knows of `emitted`: how its programs' typed inputs are
/// read (`decoder`), when one has any, how a kill's evidence is shown and a case's expectation
/// read and checked (by Rust field path and canonical documents, over the decoder's compile, its
/// views evaluated in the definition or in one of `observers`), and which sentences are claim
/// helpers. Only claims apply a claim helper, and the claims are not in the K kink loads, so the
/// emission, which wrote both, names them.
fn with_front_end_facts(
    manifest: kink_flow::FlowManifest,
    emitted: &EmittedDefinition,
    decoder: Arc<inputs::KrsInputs>,
    observers: render::Observers,
) -> kink_flow::FlowManifest {
    manifest
        .with_end_renderer(Arc::new(render::KrsEnds::new(decoder.clone(), observers)))
        .with_input_decoder(decoder)
        .with_claim_helpers(
            emitted
                .rules
                .iter()
                .filter(|rule| rule.claim_helper)
                .map(|rule| (rule.module.clone(), rule.label.clone())),
        )
}

/// The command request every stage before kink runs on: `request`'s selection, judged as
/// `krs emit-k` judges it. `no_reuse` is moot: the front end collects through
/// [`plan_collection`], which never reads krs's result cache.
fn selection_request(request: &KinkRequest) -> CommandRequest {
    CommandRequest {
        command: Command::Check {
            backend: None,
            partition: false,
        },
        manifest_path: request.manifest_path.clone(),
        root: request.root.clone(),
        dependencies: request.dependencies.clone(),
        cfg: request.cfg.clone(),
        registration: request.registration,
        no_reuse: true,
        message_format: request.message_format,
        profile: request.profile,
    }
}

/// Collect, lower and emit the planned package; `outcome` takes the definition's warnings. With
/// `retain`, the lowering the K is emitted from is kept beside the emission.
fn build(
    planned: crate::command::PlannedCollection,
    outcome: &mut KinkOutcome,
    measurement: &mut Measurement,
    retain: bool,
) -> Result<(EmittedDefinition, Option<KeptLowering>), CommandError> {
    let collected = planned.collect(measurement)?;
    let bundle = collected.bundle.clone();
    let built = if retain {
        let crate::RetainedEmission {
            emitted,
            retained,
            lowered,
        } = collected.emit_k_retained_measured(bundle, measurement)?;
        (emitted, Some(KeptLowering { retained, lowered }))
    } else {
        (collected.emit_k_measured(bundle, measurement)?, None)
    };
    outcome.warnings = built.0.warnings.clone();
    Ok(built)
}

/// `krs kink emit [--check]`.
fn emit_command(
    planned: crate::command::PlannedCollection,
    corpus: &Path,
    root: Option<&Path>,
    check: bool,
    outcome: KinkOutcome,
    measurement: &mut Measurement,
) -> KinkOutcome {
    let definition_path = corpus.join(DEFINITION_FILE);
    let shown = emit::shown_path(&definition_path, root);
    let mut outcome = outcome;
    let emitted = match build(planned, &mut outcome, measurement, false) {
        Ok((emitted, _)) => emitted,
        Err(error) => {
            let document =
                emit::emit_document(&shown, None, check, Some(&krs_refused_detail(&error)));
            outcome.error = Some(error);
            return outcome.json(&document, EXIT_UNASKED);
        }
    };
    let status = measurement.timings.span("kink.definition", |_| {
        emit::freshen(&definition_path, &emitted.definition, !check)
    });
    match status {
        Ok(status) => {
            let document = emit::emit_document(&shown, Some(status), check, None);
            // A stale file is an input to regenerate, as `--locked` refuses it: no answer about
            // the package or its corpus.
            let code = if status == DefinitionStatus::Stale {
                EXIT_UNASKED
            } else {
                EXIT_YES
            };
            outcome.json(&document, code)
        }
        Err(error) => {
            let document = emit::emit_document(&shown, None, check, Some(&error.detail(&shown)));
            outcome.json(&document, EXIT_UNASKED)
        }
    }
}

/// The flag by which `krs kink <verb>` names a list that kink-flow's verb takes as an operand:
/// `run --mutations`, `query --patterns`, `fuzz --templates`. kink-flow's own parser takes the
/// other list flags (`check` and `results --mutations`, `fuzz --mutations` and `--patterns`).
const fn operand_flag(verb: Verb) -> Option<&'static str> {
    match verb {
        Verb::Run => Some("--mutations"),
        Verb::Query => Some("--patterns"),
        Verb::Fuzz => Some("--templates"),
        Verb::Check | Verb::Results | Verb::Report => None,
    }
}

/// The files `verb` reads ([`layout_files`]), the list its [`operand_flag`] names replacing the
/// layout's, and the options left for kink-flow's parser; the error is the usage message.
fn command_files(
    corpus: &Path,
    verb: Verb,
    options: &[String],
) -> Result<(CommandFiles, Vec<String>), String> {
    let mut files = layout_files(corpus, verb);
    let Some(flag) = operand_flag(verb) else {
        return Ok((files, options.to_vec()));
    };
    let mut rest = Vec::with_capacity(options.len());
    let mut given = None;
    let mut args = options.iter();
    while let Some(arg) = args.next() {
        if arg != flag {
            rest.push(arg.clone());
        } else if given.is_some() {
            return Err(format!("{flag} is given twice"));
        } else {
            let path = args.next().ok_or_else(|| format!("{flag} needs a path"))?;
            given = Some(PathBuf::from(path));
        }
    }
    if let Some(path) = given {
        match verb {
            Verb::Run => files.mutations = Some(path),
            Verb::Query => files.patterns = Some(path),
            _ => files.templates = Some(path),
        }
    }
    Ok((files, rest))
}

/// The files a verb reads from the corpus layout: the mutations directory `mutations/`, else
/// `MUTATIONS.toml`; `PATTERNS.toml`; `TEMPLATES.toml`. A verb that needs a list gets its
/// layout path even when it is missing, so that kink-flow's refusal names the file the layout
/// expects; a verb that only may read one gets it only when it exists. A verb's own flag
/// (`--mutations`, `--patterns`, `--templates`) takes precedence ([`command_files`]).
fn layout_files(corpus: &Path, verb: Verb) -> CommandFiles {
    let directory = corpus.join("mutations");
    let single = corpus.join("MUTATIONS.toml");
    let mutations = if directory.is_dir() {
        Some(directory)
    } else if single.is_file() {
        Some(single)
    } else if verb == Verb::Run {
        Some(directory)
    } else {
        None
    };
    let optional = |path: PathBuf| path.is_file().then_some(path);
    CommandFiles {
        mutations,
        patterns: match verb {
            Verb::Query => Some(corpus.join("PATTERNS.toml")),
            _ => optional(corpus.join("PATTERNS.toml")),
        },
        templates: Some(corpus.join("TEMPLATES.toml")),
    }
}

/// The corpus manifest at `path`, decoded by kink-flow, when it declares a KRS corpus for the
/// facet `definition`: a K corpus is refused naming kink-flow, and a KRS corpus of another facet
/// naming both.
fn corpus_manifest(path: &Path, definition: &str) -> Result<ManifestFile, ManifestError> {
    if !path.is_file() {
        return Err(ManifestError::new(
            "",
            format!(
                "{} is not a file: a KRS corpus is described by kink/FLOW.toml in the package \
                 (or FLOW.toml in the directory --corpus names), with `[spec] krs = {{ \
                 definition = \"{definition}\" }}`",
                path.display()
            ),
        ));
    }
    let file = ManifestFile::read(path)?;
    match &file.spec {
        SpecDecl::K(_) => Err(ManifestError::new(
            "spec.entry",
            "a K corpus: its [spec] declares the K specification, so the krs front end binds \
             none; run `kink-flow <command>` on FLOW.toml, or declare `[spec] krs = { \
             definition = .. }` for this package",
        )),
        SpecDecl::Krs(KrsSpec {
            definition: declared,
            ..
        }) if declared != definition => Err(ManifestError::new(
            "spec.krs.definition",
            format!(
                "the corpus is for the definition facet `{declared}`, and this command selected \
                 `{definition}`; run it with `--definition {declared}`, or declare \
                 `definition = \"{definition}\"`"
            ),
        )),
        SpecDecl::Krs(_) => Ok(file),
    }
}

/// The specification a KRS corpus is bound to: `definition.k` in the corpus directory, loaded
/// at the emitted main module with K's default program-syntax module (`<MAIN>-SYNTAX`, which
/// the emission names so) and kink-flow's default includes and Markdown selector. The corpus's
/// `assume_joined` replaces the empty one here ([`ManifestFile::bind`]).
fn bound_spec(emitted: &EmittedDefinition) -> SpecSection {
    SpecSection {
        entry: DEFINITION_FILE.to_owned(),
        main_module: emitted.ir.main_module().as_str().to_owned(),
        syntax_module: None,
        include_dirs: kink_flow::manifest::DEFAULT_INCLUDE_DIRS
            .iter()
            .map(|dir| (*dir).to_owned())
            .collect(),
        md_selector: kink_flow::manifest::DEFAULT_MD_SELECTOR.to_owned(),
        assume_joined: Vec::new(),
    }
}

/// `fuzz --matched RULE` and `fuzz --fired RULE` take a label or a suffix of whole components of
/// one, as a mutation's `rule` anchor does: a `RULE` that names exactly one emitted rule this way
/// is given to kink-flow as that rule's module-qualified label; anything else (`FILE:LINE`, a
/// compiled id, a name that matches no rule or several) is given unchanged, and kink-flow resolves
/// or refuses it with its own listing.
fn resolve_rule(command: &mut FlowCommand, emitted: &EmittedDefinition) {
    let FlowCommand::Fuzz { request, .. } = command else {
        return;
    };
    let FuzzJobRequest::Rule { rule, .. } = &mut request.job else {
        return;
    };
    let matches = emitted
        .rules
        .iter()
        .filter(|candidate| {
            kink_flow::label_match(&candidate.label, &candidate.module, rule).is_some()
        })
        .collect::<Vec<_>>();
    if let [one] = matches.as_slice() {
        *rule = annotate::qualified(&one.label, &one.module);
    }
}

/// `command`'s document for a corpus refused before kink-flow ran: the verb's document of a
/// refused manifest, with the stage, reason and detail of the refusal.
fn refused(command: &FlowCommand, stage: &str, reason: &str, detail: &str) -> Value {
    refused_document(
        command.manifest_refused(&ManifestError::new("", detail)),
        stage,
        reason,
        detail,
    )
}

/// `document`, a verb's document of a refused manifest, with the stage, reason and detail of
/// the refusal.
fn refused_document(mut document: Value, stage: &str, reason: &str, detail: &str) -> Value {
    if let Some(spec) = document.get_mut("spec").and_then(Value::as_object_mut) {
        spec.insert("stage".into(), json!(stage));
        spec.insert("reason".into(), json!(reason));
        spec.insert("detail".into(), json!(detail));
    }
    if document.get("action").is_some() {
        document["action"] = json!(detail);
    }
    document
}

/// Print `document` as `output` asks, with kink-flow's exit status `status`.
fn finish(
    mut outcome: KinkOutcome,
    document: &Value,
    status: u8,
    output: OutputFormat,
) -> KinkOutcome {
    match output {
        OutputFormat::Json => outcome.json(document, status),
        OutputFormat::Verdicts => match kink_flow::verdicts(document) {
            Ok(text) => {
                outcome.notes.extend(
                    kink_flow::verdicts::refusal_details(document)
                        .into_iter()
                        .map(|detail| format!("krs kink: {detail}")),
                );
                outcome.stdout = text.into_bytes();
                outcome.status = status;
                outcome
            }
            Err(message) => {
                outcome.notes.push(format!("krs kink: {message}"));
                outcome.status = EXIT_UNASKED;
                outcome
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::{Verb, command_files};
    use std::path::{Path, PathBuf};

    fn strings(list: &[&str]) -> Vec<String> {
        list.iter().map(|arg| (*arg).to_owned()).collect()
    }

    /// `run --mutations`, `query --patterns` and `fuzz --templates` name the list kink-flow's
    /// verb takes as an operand, in place of the layout's; kink-flow's parser reads the rest.
    #[test]
    fn a_list_flag_names_the_list_kink_flow_takes_as_an_operand() {
        let corpus = Path::new("no-such-corpus");
        let (files, rest) = command_files(
            corpus,
            Verb::Run,
            &strings(&[
                "--full",
                "--mutations",
                "other.toml",
                "--output",
                "verdicts",
            ]),
        )
        .unwrap();
        assert_eq!(files.mutations, Some(PathBuf::from("other.toml")));
        assert_eq!(rest, strings(&["--full", "--output", "verdicts"]));

        let (files, rest) =
            command_files(corpus, Verb::Query, &strings(&["--patterns", "p.toml"])).unwrap();
        assert_eq!(files.patterns, Some(PathBuf::from("p.toml")));
        assert!(rest.is_empty());

        let (files, rest) = command_files(
            corpus,
            Verb::Fuzz,
            &strings(&["--templates", "t.toml", "--template", "a"]),
        )
        .unwrap();
        assert_eq!(files.templates, Some(PathBuf::from("t.toml")));
        assert_eq!(rest, strings(&["--template", "a"]));

        // check's flag is kink-flow's own, so it stays among the options.
        let (files, rest) =
            command_files(corpus, Verb::Check, &strings(&["--mutations", "m.toml"])).unwrap();
        assert_eq!(files.mutations, None);
        assert_eq!(rest, strings(&["--mutations", "m.toml"]));

        // Without the flag the layout's list stands.
        let (files, _) = command_files(corpus, Verb::Run, &[]).unwrap();
        assert_eq!(files.mutations, Some(corpus.join("mutations")));

        assert!(command_files(corpus, Verb::Run, &strings(&["--mutations"])).is_err());
        assert!(
            command_files(
                corpus,
                Verb::Run,
                &strings(&["--mutations", "a", "--mutations", "b"])
            )
            .is_err()
        );
    }
}
