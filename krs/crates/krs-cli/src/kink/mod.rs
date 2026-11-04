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
//! The front end adds, on the way in, how a case's typed inputs are read (the encoding KRS
//! derives from the definition's declared types, the `inputs` submodule) and the mutations its
//! own checks refuse (`checks`); on the way out, to every rule a document names, the KRS item and
//! the Rust position the sentence was emitted from (`annotate`), and next steps spelled as
//! `krs kink` commands (`spelling`).
//!
//! Every verb but `emit` prints one kink-flow document (or, with `--output verdicts`, its
//! deterministic rendering) with one more key, `definition`: the path of `kink/definition.k`
//! and whether this command found it `unchanged` or `written` it. A stale file is rewritten,
//! since a mutation is re-resolved against the K on every command and refused when the text it
//! replaces changed, so a rewrite can make a mutation stale but never change what it means;
//! under `--locked` the command is refused instead (stage `definition`, reason
//! `definition-stale`), and `krs kink emit --check` is the gate a CI runs.
//!
//! A package krs refuses, from its selection (an unknown package or facet, a manifest Cargo
//! cannot read) to its emission, is answered by krs's diagnostics on stderr and the verb's
//! document with its specification refused at stage `krs-build`, reason `krs-refused`; `emit`'s
//! document has the refusal as its `refusal`.

mod annotate;
mod checks;
mod emit;
mod inputs;
mod spelling;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use kink_flow::{
    CommandFiles, FlowCommand, FrontEnd, KrsSpec, ManifestError, ManifestFile, OutputFormat,
    SpecDecl, SpecSection, Verb, cli::FuzzJobRequest,
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

/// The exit statuses of kink-flow's command line, which `krs kink` keeps.
pub const EXIT_OK: u8 = kink_flow::cli::EXIT_OK;
/// Something is refused (the document says what and why).
pub const EXIT_CORPUS: u8 = kink_flow::cli::EXIT_CORPUS;
/// A usage error.
pub const EXIT_USAGE: u8 = kink_flow::cli::EXIT_USAGE;

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
    /// The exit status: [`EXIT_OK`], [`EXIT_CORPUS`] or [`EXIT_USAGE`].
    pub status: u8,
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
            status: EXIT_OK,
            warnings: DiagnosticReports::default(),
            error: None,
            sources,
        }
    }

    fn usage(mut self, message: String) -> Self {
        self.notes.push(message);
        self.status = EXIT_USAGE;
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
            outcome.json(&document, EXIT_CORPUS)
        }
        KinkVerb::Flow { verb, options } => {
            if let Ok(command) =
                FlowCommand::parse(verb.as_str(), layout_files(&corpus, *verb), options)
            {
                let document = refused(&command, "krs-build", "krs-refused", &detail);
                finish(outcome, &document, EXIT_CORPUS, command.output())
            } else {
                let document = refused_document(
                    verb.manifest_refused(&ManifestError::new("", &detail)),
                    "krs-build",
                    "krs-refused",
                    &detail,
                );
                outcome.json(&document, EXIT_CORPUS)
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
    let command = match FlowCommand::parse(verb.as_str(), layout_files(corpus, verb), options) {
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
            return finish(outcome, &document, EXIT_CORPUS, output);
        }
    };
    let emitted = match build(planned, &mut outcome, measurement) {
        Ok(emitted) => emitted,
        Err(error) => {
            let document = refused(
                &command,
                "krs-build",
                "krs-refused",
                &krs_refused_detail(&error),
            );
            outcome.error = Some(error);
            return finish(outcome, &document, EXIT_CORPUS, output);
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
            return finish(outcome, &document, EXIT_CORPUS, output);
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
        return finish(outcome, &document, EXIT_CORPUS, output);
    }
    let definition = emit::definition_value(&shown, status);
    run_flow(
        command,
        declared,
        &emitted,
        &spelling,
        definition,
        outcome,
        measurement,
    )
}

/// Run the parsed `command` on the corpus `declared`, bound to the fresh `definition.k` of
/// `emitted`; `definition` is the document's `definition` object.
fn run_flow(
    mut command: FlowCommand,
    declared: ManifestFile,
    emitted: &EmittedDefinition,
    spelling: &spelling::KrsSpelling,
    definition: Value,
    mut outcome: KinkOutcome,
    measurement: &mut Measurement,
) -> KinkOutcome {
    let output = command.output();
    let verb = command.verb();
    let manifest = match declared.bind(Some(bound_spec(emitted))) {
        Ok(manifest) => manifest,
        Err(error) => {
            let mut document = command.manifest_refused(&error);
            document["definition"] = definition;
            return finish(outcome, &document, EXIT_CORPUS, output);
        }
    };
    let manifest = if manifest
        .programs
        .iter()
        .any(|program| !program.inputs.is_empty())
    {
        manifest.with_input_decoder(Arc::new(inputs::KrsInputs::new(emitted.ir.clone())))
    } else {
        manifest
    };
    resolve_reach(&mut command, emitted);
    let refused_mutations = checks::refused(&checks::all(), emitted, &manifest, &command);
    let annotator = annotate::Annotator::new(emitted, manifest.clone());
    let annotate = |document: &mut Value| annotator.annotate(document);
    // `report` prints the stored run document as the run wrote it, its rules already named by
    // the emission that run judged. This command's emission may be another one (the sources
    // changed since), whose table would name the run's rules by the current items and
    // positions, or not at all; so the stored document is not annotated again.
    let front = FrontEnd {
        spelling,
        refused: refused_mutations,
        annotate: (verb != Verb::Report).then_some(&annotate as &(dyn Fn(&mut Value) + Sync)),
    };
    let span = format!("kink.{}", verb.as_str());
    let dispatched = measurement
        .timings
        .span(&span, |_| kink_flow::dispatch(manifest, command, front));
    let (mut document, status_code) = match dispatched {
        Ok(result) => result,
        Err(panicked) => {
            outcome.notes.push(format!("krs kink: {panicked}"));
            outcome.status = EXIT_CORPUS;
            return outcome;
        }
    };
    document["definition"] = definition;
    finish(outcome, &document, status_code, output)
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

/// Collect, lower and emit the planned package; `outcome` takes the definition's warnings.
fn build(
    planned: crate::command::PlannedCollection,
    outcome: &mut KinkOutcome,
    measurement: &mut Measurement,
) -> Result<EmittedDefinition, CommandError> {
    let collected = planned.collect(measurement)?;
    let bundle = collected.bundle.clone();
    let emitted = collected.emit_k_measured(bundle, measurement)?;
    outcome.warnings = emitted.warnings.clone();
    Ok(emitted)
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
    let emitted = match build(planned, &mut outcome, measurement) {
        Ok(emitted) => emitted,
        Err(error) => {
            let document =
                emit::emit_document(&shown, None, check, Some(&krs_refused_detail(&error)));
            outcome.error = Some(error);
            return outcome.json(&document, EXIT_CORPUS);
        }
    };
    let status = measurement.timings.span("kink.definition", |_| {
        emit::freshen(&definition_path, &emitted.definition, !check)
    });
    match status {
        Ok(status) => {
            let document = emit::emit_document(&shown, Some(status), check, None);
            let code = if status == DefinitionStatus::Stale {
                EXIT_CORPUS
            } else {
                EXIT_OK
            };
            outcome.json(&document, code)
        }
        Err(error) => {
            let document = emit::emit_document(&shown, None, check, Some(&error.detail(&shown)));
            outcome.json(&document, EXIT_CORPUS)
        }
    }
}

/// The files a verb reads from the corpus layout: the mutations directory `mutations/`, else
/// `MUTATIONS.toml`; `PATTERNS.toml`; `TEMPLATES.toml`. A verb that needs a list gets its
/// layout path even when it is missing, so that kink-flow's refusal names the file the layout
/// expects; a verb that only may read one gets it only when it exists. A verb's own flag
/// (`--mutations`, `--patterns`) takes precedence.
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

/// `fuzz --reach RULE` takes a label or a suffix of whole components of one, as a mutation's
/// `rule` anchor does: a `RULE` that names exactly one emitted rule this way is given to
/// kink-flow as that rule's module-qualified label; anything else (`FILE:LINE`, a compiled id,
/// a name that matches no rule or several) is given unchanged, and kink-flow resolves or refuses
/// it with its own listing.
fn resolve_reach(command: &mut FlowCommand, emitted: &EmittedDefinition) {
    let FlowCommand::Fuzz { request, .. } = command else {
        return;
    };
    let FuzzJobRequest::Reach { rule, .. } = &mut request.job else {
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
                outcome.status = EXIT_CORPUS;
                outcome
            }
        },
    }
}
