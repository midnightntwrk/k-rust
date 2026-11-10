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
//! reason `stop-unresolved`), the stop condition `[stop] when` names with KRS's spellings,
//! resolved as `krs run --stop-when` resolves one and handed to kink as the condition it asks at
//! each arrival (the `condition` submodule; reason `stop-condition-unresolved`), the observation
//! channels `[observe]` names with KRS's spellings, resolved as `krs run --observe` resolves them,
//! their rules mapped to exact K labels and their cells to K names, and handed to kink with the
//! functions of an observer that give their elements (the `observe` submodule; stage `observe`,
//! reasons `observe-unresolved` and `point-unresolved`), the syntax
//! family's authored sorts and the `k::bits!` binders whose values every baseline run records
//! (the `syntax` submodule), the mutations its own checks refuse (`checks`), and the
//! definition's condition flips, which `coverage` runs as its flips family and `fuzz --kill
//! <flip-id>` names (`flips`, each with the guard nodes it changes, which `guards` places); on
//! the way
//! out, the labels each `[stop]` name selects (`stop.krs.items`), the labels and cells each
//! `[observe]` name reads as (`observe.krs`), the compared cells by Rust path
//! (`result.krs`), to every rule a document names, the KRS item and the Rust position the
//! sentence was emitted from (`annotate`), the syntax family's productions by Rust path and its
//! templates' field values with their encodings (`syntax`), and next steps spelled as `krs kink`
//! commands (`spelling`).
//!
//! `compare` runs each `[[implementation]]` of the corpus on every case and compares its end with
//! the definition's under each of its views; the front end gives kink-flow the cell vocabulary in
//! which an implementation reads the definition's start and writes its end (the
//! `implementations` submodule: cells by Rust field path, values as documents of the typed
//! encoding, views resolved as an expectation's are).
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
//! The corpus keeps one record, `<corpus>/kink.lock` (kink-flow `--lock`), one section per
//! command. `run` keeps its `[run]` section, the killer record (one recorded killer per killed
//! mutation, kept while it still kills), when it reads the corpus's own mutation list: the front
//! end gives kink-flow `--lock <corpus>/kink.lock` unless the command names a lock or another list
//! (`--mutations`), since the section describes the corpus with its own list, and one corpus is
//! also run with other lists. A run of the whole list rewrites the section; under `--locked` the
//! run leaves it unwritten, kink-flow's `--locked` compares the section it would write with the
//! file's, and a difference is a finding (exit 1). So a CI runs `krs kink emit --check` and `krs
//! kink run --locked`.
//!
//! `coverage` keeps the `[coverage]` section (one recorded killer per distinguished flip, by the
//! same rule), unless the command names a lock. A run with the manifest's own settings rewrites
//! it; `--tier 1` and `--depth` leave it unwritten, and krs's `--locked` adds kink-flow's only to
//! a run with the manifest's own settings. So a CI also runs `krs kink coverage --locked`.
//!
//! `compare` keeps the `[compare]` section (one verdict per implementation, case and view),
//! unless the command names a lock: a run of every implementation rewrites it, `--only` leaves it
//! unwritten, and under krs's `--locked` kink-flow's `--locked` compares it. So a corpus with
//! `[[implementation]]`s also runs `krs kink compare --locked` in CI.
//!
//! `query` and a `fuzz` pattern job ask the patterns the corpus manifest declares (`[[patterns]]`,
//! kink-flow's `pattern::declared_patterns`), else, for a corpus that declares none, the layout's
//! `PATTERNS.toml`; `--patterns` names another list in place of either. A `[[patterns]] krs`
//! package is refused for now: krs does not build KRS patterns packages yet.
//!
//! `query` keeps the `[query]` section (each pattern's obligation and its one recorded witness,
//! kept while it still hits) when it reads the corpus's own patterns, unless the command
//! names a lock or another list (`--patterns`): a query of the whole list rewrites it, `--only`
//! and `--verify` leave it unwritten, and under krs's `--locked` kink-flow's `--locked` compares
//! it. Each command keeps the others' sections as they are.
//!
//! Before version 24 the two locks were `<corpus>/verdicts.lock` and `<corpus>/coverage.lock`.
//! Where the command keeps the record by default and its old file is there, the front end names
//! it to kink-flow ([`kink_flow::FlowCommand::set_legacy_lock`]): without `--locked` its killers
//! are read while the record has no section of the command and the write moves them into
//! `kink.lock`, and stderr says to delete the old file; under `--locked` the command is refused
//! while it is there, naming the command that moves it. Nothing is deleted.
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
mod condition;
mod emit;
mod flips;
mod guards;
mod implementations;
mod inputs;
mod invariant;
mod observe;
mod render;
mod spelling;
mod stop;
mod syntax;

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
pub use flips::{DerivedFlip, DerivedFlips, FlipAtom, FlipNotGenerated, FlipSentence, FlipStatus};

/// The corpus directory's name inside the root package, when `--corpus` names none.
pub const CORPUS_DIRECTORY: &str = "kink";
/// The corpus manifest's name inside the corpus directory.
pub const MANIFEST_FILE: &str = "FLOW.toml";
/// The emitted definition's name inside the corpus directory.
pub const DEFINITION_FILE: &str = "definition.k";
/// The corpus record's name inside the corpus directory (kink-flow `run --lock`, `coverage
/// --lock` and `compare --lock`), one section per command.
pub const LOCK_FILE: &str = kink_flow::lock::LOCK_FILE;

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
    /// rewriting it, and under `run` and `coverage` with a lock leave `kink.lock` unwritten, a
    /// run that would change the command's section being a finding.
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

    /// A usage error: `message` on stderr with the `krs kink:` prefix every usage error of the
    /// front end carries, whether its parser or kink-flow's found it, then the usage.
    fn usage(mut self, message: &str) -> Self {
        self.notes.push(format!("krs kink: {message}"));
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
            return outcome.usage("the root package has no directory; give --corpus DIR");
        }
    };
    match &request.verb {
        KinkVerb::Emit { check } => emit_command(
            planned,
            &corpus,
            root.as_deref(),
            *check,
            &spelling::KrsSpelling::new(request),
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

/// The condition flips of the definition `request` selects ([`DerivedFlips`]), each spelled as a
/// K patch of the corpus's `definition.k` and judged by the front end's checks through the
/// corpus's judge cache, as `run` judges a list's mutation; `request.verb` plays no part. The
/// corpus manifest is read and `definition.k` kept fresh as every verb does (under
/// `request.locked`, a stale file refuses). `target_directory` is Cargo's target directory for the
/// package and its collector, in place of the environment's.
///
/// # Errors
///
/// The outcome of a command refused before any flip is judged, whose `notes` say why: a package
/// krs refuses, a corpus that is not this package's, a stale or unwritable `definition.k`, a
/// specification kink-flow cannot load.
pub fn condition_flips(
    request: &KinkRequest,
    target_directory: Option<&Path>,
    measurement: &mut Measurement,
) -> Result<DerivedFlips, Box<KinkOutcome>> {
    condition_flips_reading(request, target_directory, measurement, None)
}

/// [`condition_flips`], the judge reading every authored source from the directory `authored`,
/// when given, in place of its package's root: a way to judge against a source that is not the
/// revision the build read, as when a file is edited while a command runs.
///
/// # Errors
///
/// As [`condition_flips`].
#[doc(hidden)]
pub fn condition_flips_reading(
    request: &KinkRequest,
    target_directory: Option<&Path>,
    measurement: &mut Measurement,
    authored: Option<&Path>,
) -> Result<DerivedFlips, Box<KinkOutcome>> {
    let mut sources = DiagnosticSources::default();
    let selection = selection_request(request);
    let planned = match plan_collection(&selection, target_directory, measurement, &mut sources) {
        Ok(planned) => planned,
        Err(error) => {
            let mut outcome = KinkOutcome::new(sources);
            outcome
                .notes
                .push(format!("krs kink: {}", krs_refused_detail(&error)));
            outcome.error = Some(error);
            outcome.status = EXIT_UNASKED;
            return Err(Box::new(outcome));
        }
    };
    let mut outcome = KinkOutcome::new(sources);
    let refuse = |mut outcome: KinkOutcome, detail: String| {
        outcome.notes.push(format!("krs kink: {detail}"));
        outcome.status = EXIT_UNASKED;
        Box::new(outcome)
    };
    let root = planned.root_directory();
    let Some(corpus) = request
        .corpus
        .clone()
        .or_else(|| root.as_ref().map(|root| root.join(CORPUS_DIRECTORY)))
    else {
        return Err(refuse(
            outcome,
            "the root package has no directory; give --corpus DIR".to_owned(),
        ));
    };
    let declared = match corpus_manifest(&corpus.join(MANIFEST_FILE), &request.root.definition) {
        Ok(declared) => declared,
        Err(error) => return Err(refuse(outcome, error.to_string())),
    };
    let (emitted, kept) = match build(planned, &mut outcome, measurement, true) {
        Ok((emitted, Some(kept))) => (emitted, kept),
        Ok((_, None)) => unreachable!("a retained build keeps its lowering"),
        Err(error) => {
            let detail = krs_refused_detail(&error);
            outcome.error = Some(error);
            return Err(refuse(outcome, detail));
        }
    };
    let definition_path = corpus.join(DEFINITION_FILE);
    let shown = emit::shown_path(&definition_path, root.as_deref());
    match emit::freshen(&definition_path, &emitted.definition, !request.locked) {
        Ok(DefinitionStatus::Stale) => {
            let spelling = spelling::KrsSpelling::new(request);
            return Err(refuse(outcome, stale_detail(&shown, "--locked", &spelling)));
        }
        Ok(_) => {}
        Err(error) => return Err(refuse(outcome, error.detail(&shown))),
    }
    // The flips skip a family with a claim helper, which they ask of the manifest as every
    // coverage family does.
    let manifest = match declared.bind(Some(bound_spec(&emitted))) {
        Ok(manifest) => manifest.with_claim_helpers(claim_helpers(&emitted)),
        Err(error) => return Err(refuse(outcome, error.to_string())),
    };
    let loaded =
        match kink_corpus::resolver::load_source(&kink_flow::admit::corpus_source(&manifest)) {
            Ok(loaded) => loaded,
            Err(error) => {
                return Err(refuse(
                    outcome,
                    format!("kink cannot load {shown}: {error}"),
                ));
            }
        };
    let sources = authored.map_or_else(
        || outcome.sources.clone(),
        |root| outcome.sources.rooted_at(root),
    );
    let baseline = checks::Baseline {
        emitted: &emitted,
        retained: &kept.retained,
        lowered: &kept.lowered,
        sources: &sources,
    };
    let derived = kink_flow::on_stack(|| {
        let checks = judged_checks(&baseline, &manifest, None);
        flips::derive(&baseline, &checks, &manifest, &loaded)
    });
    derived.ok_or_else(|| refuse(outcome, "the flip thread panicked".to_owned()))
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
            if let Ok(command) = flow_arguments(&corpus, *verb, options, request.locked)
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
    let spelling = spelling::KrsSpelling::new(request)
        .with_own_mutations(layout_files(corpus, Verb::Run).mutations);
    let mut command = match flow_arguments(corpus, verb, options, request.locked)
        .and_then(|(files, options)| FlowCommand::parse(verb.as_str(), files, &options))
    {
        Ok(command) => command,
        Err(message) => return outcome.usage(&message),
    };
    // A command that keeps the corpus record by default is given the file it kept its lock in
    // before version 24, so that kink-flow migrates it (its killers are read while the record
    // has no section of the command) or, under `--locked`, refuses the corpus while it is there.
    if let Some(legacy) = legacy_lock(corpus, verb, options) {
        command.set_legacy_lock(legacy);
    }
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
            &stale_detail(&shown, "--locked", &spelling),
        );
        document["definition"] = emit::definition_value(&shown, status);
        return finish(outcome, &document, EXIT_UNASKED, output);
    }
    let definition = emit::definition_value(&shown, status);
    let observers = render::Observers::new(selection_request(request), outcome.sources.clone());
    // The lock's path as kink-flow reads it, and as documents show it: relative to the root
    // package, as `definition.path` is.
    let lock = corpus.join(LOCK_FILE);
    let lock = (
        lock.display().to_string(),
        emit::shown_path(&lock, paths.root),
    );
    run_flow(
        command,
        declared,
        Built {
            emitted: &emitted,
            kept,
            observers,
            lock,
        },
        &spelling,
        definition,
        outcome,
        measurement,
    )
}

/// Whether `command` judges a mutation list or the definition's condition flips, so that the
/// front end's checks need the lowering the K is emitted from: `check --mutations`, `run`, a
/// `fuzz` kill job, `coverage`.
fn judges_mutations(command: &FlowCommand) -> bool {
    match command {
        FlowCommand::Check(options) => options.mutations.is_some(),
        command => checks::run_list(command).is_some() || derives_flips(command),
    }
}

/// Whether `command` reads the definition's condition flips: `coverage`, whose flips family they
/// are (under `--tier 1` it shows how many there are), and a `fuzz` kill job of an id no list
/// holds, which names a flip.
fn derives_flips(command: &FlowCommand) -> bool {
    match command {
        FlowCommand::Coverage { .. } => true,
        FlowCommand::Fuzz { request, .. } => {
            matches!(request.job, FuzzJobRequest::Derived { .. })
        }
        _ => false,
    }
}

/// The definition's condition flips as `command`'s front end hands them to kink-flow
/// ([`flips::derived_list`]), each judged through the corpus's judge cache; `None` for a command
/// that reads none ([`derives_flips`]), `Err` with why the definition derives none, or why they
/// could not be derived.
fn derived_flips(
    command: &FlowCommand,
    baseline: Option<&checks::Baseline<'_>>,
    manifest: &kink_flow::FlowManifest,
    measurement: &mut Measurement,
) -> Option<Result<kink_flow::flips::DerivedList, String>> {
    if !derives_flips(command) {
        return None;
    }
    let baseline = baseline?;
    tell_progress(
        command,
        "run: deriving and judging the definition's condition flips",
    );
    let loaded =
        match kink_corpus::resolver::load_source(&kink_flow::admit::corpus_source(manifest)) {
            Ok(loaded) => loaded,
            Err(error) => {
                return Some(Err(format!(
                    "kink cannot load the specification, so no condition flip is judged: {error}"
                )));
            }
        };
    let derived = measurement.timings.span("kink.flips", |_| {
        kink_flow::on_stack(|| {
            let checks = judged_checks(baseline, manifest, command_cache(command));
            flips::derive(baseline, &checks, manifest, &loaded)
        })
    });
    let Some(derived) = derived else {
        return Some(Err("the flip thread panicked".to_owned()));
    };
    let read = baseline.sources.clone();
    let names = guards::GuardNames::new(
        &baseline.emitted.definition,
        &baseline.emitted.source_map,
        &baseline.emitted.ir,
        move |file| read.source_text(file),
    );
    Some(flips::derived_list(&derived, &names))
}

/// What the front end hands kink-flow of the flips [`derived_flips`] gave: the list, why there is
/// none, or, for a command that reads none, kink-flow's own default.
fn front_derived(
    derived: Option<&Result<kink_flow::flips::DerivedList, String>>,
) -> kink_flow::flips::Derived<'_> {
    match derived {
        Some(Ok(list)) => kink_flow::flips::Derived::Flips(list),
        Some(Err(reason)) => kink_flow::flips::Derived::None(reason),
        None => kink_flow::flips::Derived::default(),
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
    /// The corpus record's path as kink-flow reads it, and as documents show it.
    lock: (String, String),
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
        lock,
    } = built;
    let output = command.output();
    let verb = command.verb();
    tell_progress(&command, "run: binding the corpus to the emitted K");
    let sources = outcome.sources.clone();
    let (guard_names, syntax) = front_syntax(emitted, &sources);
    let (manifest, names, resolvers) =
        match bound_manifest(&command, declared, emitted, observers, &syntax) {
            Ok(bound) => bound,
            Err(mut document) => {
                document["definition"] = definition;
                return finish(outcome, &document, EXIT_UNASKED, output);
            }
        };
    resolve_rule(&mut command, emitted);
    let annotator = naming_guards(
        names
            .annotator(emitted, &manifest, judged_list(&command))
            .naming_syntax(syntax),
        &command,
        guard_names,
    );
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
                    judged_checks(baseline, &manifest, options.cache.as_deref())
                        .annotate_check(rows);
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
    let Some(refused_mutations) =
        front_refusals(&command, baseline.as_ref(), &manifest, measurement)
    else {
        outcome
            .notes
            .push("krs kink: the mutation check thread panicked".into());
        outcome.status = EXIT_UNASKED;
        return outcome;
    };
    // `coverage` and a kill job of a flip: the condition flips, judged against the lowering.
    let derived = derived_flips(&command, baseline.as_ref(), &manifest, measurement);
    // Every check that reads the lowering is made: the dispatch, which can hold a kill search's
    // mutants for minutes, runs without the retained theory and its second Definition IR.
    drop(kept);
    // The annotation also sets `definition`, so that a run stores its document with it and
    // `report` prints what the run printed; both parts are idempotent.
    let annotate = |document: &mut Value| {
        annotator.annotate(document);
        document["definition"] = definition.clone();
        shown_lock(document, &lock);
    };
    let front = FrontEnd {
        spelling,
        refused: refused_mutations,
        annotate: Some(&annotate as &(dyn Fn(&mut Value) + Sync)),
        progress: command.shows_progress().then_some(&print_progress),
        derived: front_derived(derived.as_ref()),
        ..resolvers.front_end()
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

/// `annotator`, naming the guard nodes of the rows by KRS construct by `guard_names` where
/// `command` is `coverage`, the one command whose document has guards ([`guards`]).
fn naming_guards(
    annotator: annotate::Annotator,
    command: &FlowCommand,
    guard_names: guards::GuardNames,
) -> annotate::Annotator {
    if matches!(command, FlowCommand::Coverage { .. }) {
        annotator.naming_guards(guard_names)
    } else {
        annotator
    }
}

/// The guard names of `emitted` ([`guards`]), reading authored files from `sources`, and its
/// syntax family at the KRS level ([`syntax`]). Every verb binds the family's selection: the
/// bindings a baseline run records are part of its result's key, so every verb reads and writes
/// the records of one key.
fn front_syntax(
    emitted: &EmittedDefinition,
    sources: &DiagnosticSources,
) -> (guards::GuardNames, Arc<syntax::KrsSyntax>) {
    let read = sources.clone();
    let guard_names = guards::GuardNames::new(
        &emitted.definition,
        &emitted.source_map,
        &emitted.ir,
        move |file| read.source_text(file),
    );
    let syntax = Arc::new(syntax::KrsSyntax::new(emitted, &guard_names, sources));
    (guard_names, syntax)
}

/// `document`'s lock named by its path as documents show it, `lock.1`, where kink-flow named it
/// `lock.0`: its `path`, every path of the corpus directory in a refused lock's `detail` (the
/// record's, which starts it, and an old lock file's), and an old lock file's `legacy.path`, so
/// that the document spells each file one way, relative to the root package.
fn shown_lock(document: &mut Value, lock: &(String, String)) {
    if document["lock"]["path"] != lock.0.as_str() {
        return;
    }
    document["lock"]["path"] = json!(lock.1);
    // The corpus directory as kink-flow and as documents spell it, each with its separator.
    let directory = |path: &str| {
        path.rfind(['/', '\\'])
            .map_or_else(String::new, |at| path[..=at].to_owned())
    };
    let (full, shown) = (directory(&lock.0), directory(&lock.1));
    if full.is_empty() {
        return;
    }
    let show = |text: &str| text.replace(&full, &shown);
    if let Some(text) = document["lock"]["detail"].as_str() {
        document["lock"]["detail"] = json!(show(text));
    }
    if let Some(text) = document["lock"]["legacy"]["path"].as_str() {
        document["lock"]["legacy"]["path"] = json!(show(text));
    }
}

/// The mutations of the list `command` runs (`run`, a `fuzz` kill job) that the front end's
/// checks over `baseline` refuse, by id: none for another command or a list that does not
/// decode, which kink-flow refuses; `None` when the check thread panicked.
fn front_refusals(
    command: &FlowCommand,
    baseline: Option<&checks::Baseline<'_>>,
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
            judged_checks(baseline, manifest, command_cache(command))
                .refusals(manifest, &list, &run)
        })
    })
}

/// The front end's checks over `baseline`, reading and writing the judge cache of the corpus
/// `manifest` describes, whose cache directory `cache` names, else its default.
fn judged_checks<'a>(
    baseline: &checks::Baseline<'a>,
    manifest: &kink_flow::FlowManifest,
    cache: Option<&Path>,
) -> checks::KrsChecks<'a> {
    checks::KrsChecks::new(baseline)
        .with_cache(&kink_flow::results::cache_directory(manifest, cache))
}

/// The corpus cache directory `command` names (`--cache`), if any.
fn command_cache(command: &FlowCommand) -> Option<&Path> {
    match command {
        FlowCommand::Check(options) => options.cache.as_deref(),
        FlowCommand::Coverage { options, .. } => options.cache.as_deref(),
        FlowCommand::Run { options, .. } => options.cache.as_deref(),
        FlowCommand::Report { options, .. } => options.cache.as_deref(),
        FlowCommand::Query { options, .. } => options.cache.as_deref(),
        FlowCommand::Fuzz { request, .. } => request.options.cache.as_deref(),
        FlowCommand::Compare { options, .. } => options.cache.as_deref(),
    }
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

/// What binding a corpus names at the KRS level ([`bound_manifest`]), which every document of the
/// command gains: the labels each `[stop]` name selects, the labels and cells each `[observe]`
/// name reads as, and the compared cells by Rust path.
struct BoundNames {
    stop: Option<Value>,
    observe: Option<Value>,
    result: cells::ResultNames,
}

impl BoundNames {
    /// The annotator of `emitted`'s documents on `manifest` ([`annotate::Annotator::new`],
    /// `mutations` the command's list) naming them.
    fn annotator(
        self,
        emitted: &EmittedDefinition,
        manifest: &kink_flow::FlowManifest,
        mutations: Option<PathBuf>,
    ) -> annotate::Annotator {
        annotate::Annotator::new(emitted, manifest.clone(), mutations)
            .naming_stop(self.stop)
            .naming_observe(self.observe)
            .naming_result(self.result)
    }
}

/// The corpus `declared` bound to the K of `emitted`, with what only the front end knows of it
/// ([`with_front_end_facts`], the expectations' views evaluated in `observers`, and the syntax
/// family's authored sorts and template binders, `syntax`'s selection), the cells
/// `[result]` names by Rust path or K name as the K names kink-flow reads ([`cells::bind`]), and
/// the rules `[stop]` names by KRS item or label as the exact K labels kink-flow reads
/// ([`stop::bind`]), and `[observe]` named with KRS's spellings resolved, its rules as exact K
/// labels and its cells as K names, with the functions that give its elements
/// ([`observe::bind`]); the labels each `[stop]` name selects, the labels and cells each
/// `[observe]` name reads as, and the cells by path that the documents' `result` gains; and the
/// resolvers over the decoder's compile ([`Resolvers`]: `[[coverage.invariant]]`'s KRS spellings
/// and `compare`'s cell vocabulary); or `command`'s document refusing the corpus.
fn bound_manifest(
    command: &FlowCommand,
    declared: ManifestFile,
    emitted: &EmittedDefinition,
    observers: render::Observers,
    syntax: &syntax::KrsSyntax,
) -> Result<(kink_flow::FlowManifest, BoundNames, Resolvers), Value> {
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
    let observers = Arc::new(observers);
    // A selection that names one binder twice is refused as a manifest is: no run records it.
    let manifest = with_front_end_facts(manifest, emitted, decoder.clone(), Arc::clone(&observers))
        .with_syntax(syntax.selection())
        .map_err(|error| command.manifest_refused(&error))?;
    let (manifest, stop_items) = stop::bind(manifest, &decoder, &observers, &emitted.ir)
        .map_err(|unbound| refused(command, "stop", unbound.reason, &unbound.detail))?;
    let (manifest, observe_items) = observe::bind(manifest, &decoder, &observers, &emitted.ir)
        .map_err(|unbound| refused(command, "observe", unbound.reason, &unbound.detail))?;
    let implementations =
        implementations::KrsImplementations::new(Arc::clone(&decoder), Arc::clone(&observers));
    let invariants = invariant::KrsInvariants::new(decoder);
    let krs_patterns = krs_patterns(&manifest);
    Ok((
        manifest,
        BoundNames {
            stop: stop_items,
            observe: observe_items,
            result: result_names,
        },
        Resolvers {
            invariants,
            implementations,
            krs_patterns,
        },
    ))
}

/// The resolvers of a corpus's KRS spellings over the decoder's compile: of
/// `[[coverage.invariant]]` ([`invariant`]), and `compare`'s cell vocabulary
/// ([`implementations`]); and the patterns of the corpus's KRS patterns packages
/// ([`krs_patterns`]).
struct Resolvers {
    invariants: invariant::KrsInvariants,
    implementations: implementations::KrsImplementations,
    krs_patterns: kink_flow::pattern::KrsPatterns,
}

impl Resolvers {
    /// kink-flow's own front end with these resolvers.
    fn front_end(&self) -> FrontEnd<'_> {
        FrontEnd {
            invariants: Some(&self.invariants),
            implementations: Some(&self.implementations),
            krs_patterns: Some(&self.krs_patterns),
            ..FrontEnd::default()
        }
    }
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
    observers: Arc<render::Observers>,
) -> kink_flow::FlowManifest {
    manifest
        .with_end_renderer(Arc::new(render::KrsEnds::new(decoder.clone(), observers)))
        .with_input_decoder(decoder)
        .with_claim_helpers(claim_helpers(emitted))
        .with_sentence_names(sentence_names(emitted))
}

/// How a finding's name spells each sentence of `emitted` (kink-flow
/// [`kink_flow::FlowManifest::with_sentence_names`]): by the KRS item that wrote it, spelled as a
/// stop reads it (`crate::plus_zero`, `lang::step`), where the item wrote that sentence alone; a
/// sentence with no authored item, or one of several sentences of one item, keeps its K label,
/// which the emission derives from the item's path. A corpus's `[spec] assume_joined` is written
/// in this spelling, and every document prints names in it.
fn sentence_names(emitted: &EmittedDefinition) -> kink_flow::SentenceNames {
    kink_flow::SentenceNames::new(
        emitted
            .rules
            .iter()
            .filter_map(|rule| Some((rule.label.clone(), rule.item.clone()?))),
    )
}

/// The claim helpers of `emitted`, each by its K module and label, as a manifest's
/// [`kink_flow::FlowManifest::with_claim_helpers`] takes them ([`with_front_end_facts`]).
fn claim_helpers(emitted: &EmittedDefinition) -> impl Iterator<Item = (String, String)> + '_ {
    emitted
        .rules
        .iter()
        .filter(|rule| rule.claim_helper)
        .map(|rule| (rule.module.clone(), rule.label.clone()))
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

/// Why a stale `definition.k` at `shown` stops a command run with `flag` (`--locked`, `emit
/// --check`), and the command that writes it.
fn stale_detail(shown: &str, flag: &str, spelling: &spelling::KrsSpelling) -> String {
    format!(
        "{shown} differs from the K this krs emits for the package's current sources ({flag}); \
         run `{}` and commit the file",
        spelling.emit()
    )
}

/// `krs kink emit [--check]`.
fn emit_command(
    planned: crate::command::PlannedCollection,
    corpus: &Path,
    root: Option<&Path>,
    check: bool,
    spelling: &spelling::KrsSpelling,
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
            // A stale file is an input to regenerate, as `--locked` refuses it: no answer about
            // the package or its corpus, and the refusal names the command that regenerates it.
            if status == DefinitionStatus::Stale {
                let detail = stale_detail(&shown, "emit --check", spelling);
                let document = emit::emit_document(&shown, Some(status), check, Some(&detail));
                return outcome.json(&document, EXIT_UNASKED);
            }
            let document = emit::emit_document(&shown, Some(status), check, None);
            outcome.json(&document, EXIT_YES)
        }
        Err(error) => {
            let document = emit::emit_document(&shown, None, check, Some(&error.detail(&shown)));
            outcome.json(&document, EXIT_UNASKED)
        }
    }
}

/// The flag by which `krs kink <verb>` names a list that kink-flow's verb takes as an operand:
/// `run --mutations`, `query --patterns`, `fuzz --templates`. kink-flow's own parser takes the
/// other list flags (`check --mutations`, `fuzz --mutations` and `--patterns`).
const fn operand_flag(verb: Verb) -> Option<&'static str> {
    match verb {
        Verb::Run => Some("--mutations"),
        Verb::Query => Some("--patterns"),
        Verb::Fuzz => Some("--templates"),
        Verb::Check | Verb::Coverage | Verb::Report | Verb::Compare => None,
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

/// [`command_files`], with the corpus record. A `run` of the corpus's own mutation list, a `query`
/// of its own pattern list, a `coverage` and a `compare` command get `--lock <corpus>/kink.lock`,
/// unless the command names a lock, or, for a run or a query, another list (`--mutations`,
/// `--patterns`): `run` reads and rewrites its `[run]` section, `query` its `[query]` section,
/// each pattern's recorded witness, and `coverage` its `[coverage]` section, each flip's recorded
/// killer, only after a run with the manifest's own settings. kink-flow's
/// `--locked` is added when krs's `--locked` is given and a lock is in use, so that the command
/// leaves the lock unwritten and one that would change it is a finding; for `coverage`, only
/// when the command runs the manifest's own settings (neither `--tier 1` nor `--depth`), since
/// another run leaves the lock unwritten and cannot say whether the manifest's run would change
/// it.
fn flow_arguments(
    corpus: &Path,
    verb: Verb,
    options: &[String],
    locked: bool,
) -> Result<(CommandFiles, Vec<String>), String> {
    let (files, mut rest) = command_files(corpus, verb, options)?;
    let named = |flag: &str| options.iter().any(|arg| arg == flag);
    // The lock a verb keeps by default: none for a run of another list.
    let default = match verb {
        Verb::Run if named("--mutations") => None,
        Verb::Query if named("--patterns") => None,
        Verb::Run | Verb::Coverage | Verb::Compare | Verb::Query => Some(LOCK_FILE),
        _ => return Ok((files, rest)),
    };
    if let Some(lock) = default.filter(|_| !named("--lock")) {
        rest.push("--lock".to_owned());
        rest.push(corpus.join(lock).display().to_string());
    }
    let manifest_settings = verb != Verb::Coverage
        || (!named("--depth")
            && !options
                .windows(2)
                .any(|pair| pair[0] == "--tier" && pair[1] == "1"));
    if locked && manifest_settings && rest.iter().any(|arg| arg == "--lock") {
        rest.push("--locked".to_owned());
    }
    Ok((files, rest))
}

/// The old file a verb kept its lock in before version 24, `<corpus>/verdicts.lock` for a run of
/// the corpus's own list and `<corpus>/coverage.lock` for `coverage`, where it exists and the
/// command keeps the corpus record by default (it names no `--lock`).
fn legacy_lock(corpus: &Path, verb: Verb, options: &[String]) -> Option<PathBuf> {
    let named = |flag: &str| options.iter().any(|arg| arg == flag);
    let kind = match verb {
        Verb::Run if !named("--mutations") => kink_flow::lock::LockKind::Run,
        Verb::Coverage => kink_flow::lock::LockKind::Coverage,
        _ => return None,
    };
    let path = corpus.join(kind.legacy_file()?);
    (!named("--lock") && path.exists()).then_some(path)
}

/// The files a verb reads from the corpus layout: the mutations directory `mutations/`, else
/// `MUTATIONS.toml`; `PATTERNS.toml`; `TEMPLATES.toml`. A verb that needs a list gets its
/// layout path even when it is missing, so that kink-flow's refusal names the file the layout
/// expects; a verb that only may read one gets it only when it exists. A verb's own flag
/// (`--mutations`, `--patterns`, `--templates`) takes precedence ([`command_files`]).
///
/// A corpus whose manifest declares its patterns (`[[patterns]]`) has no layout pattern list:
/// kink-flow then asks the declared patterns, and `PATTERNS.toml` is read only where `--patterns`
/// names it. The layout's `PATTERNS.toml` is the default of a corpus that declares none.
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
            _ if declares_patterns(corpus) => None,
            Verb::Query => Some(corpus.join("PATTERNS.toml")),
            _ => optional(corpus.join("PATTERNS.toml")),
        },
        templates: Some(corpus.join("TEMPLATES.toml")),
    }
}

/// Whether the corpus manifest declares its patterns: its top level has the key `patterns`. A
/// manifest that cannot be read or is no TOML declares none here; the command refuses it when it
/// decodes the manifest, as it refuses a `patterns` that is no array of `[[patterns]]` tables.
fn declares_patterns(corpus: &Path) -> bool {
    std::fs::read_to_string(corpus.join(MANIFEST_FILE))
        .ok()
        .and_then(|text| text.parse::<toml::Table>().ok())
        .is_some_and(|top| top.contains_key("patterns"))
}

/// The patterns krs provides for each `[[patterns]] krs` package of `manifest`
/// ([`kink_flow::pattern::KrsPatterns`]): none yet, since krs does not build a patterns package,
/// so each entry is refused with that reason rather than skipped.
fn krs_patterns(manifest: &kink_flow::FlowManifest) -> kink_flow::pattern::KrsPatterns {
    manifest
        .patterns
        .iter()
        .filter_map(|entry| match entry {
            kink_flow::PatternsEntry::Krs { package } => Some((
                package.clone(),
                Err(format!(
                    "the KRS patterns package {package:?}: krs kink does not build KRS patterns \
                     packages yet; declare the patterns as kink pattern lists (`[[patterns]] \
                     files = \"GLOB\"`) until it does"
                )),
            )),
            kink_flow::PatternsEntry::Files { .. } => None,
        })
        .collect()
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

/// `fuzz --matched RULE`, `fuzz --fired RULE` and `fuzz --refuted RULE` take a label or a suffix
/// of whole components of one, as a mutation's `rule` anchor does: a `RULE` that names exactly one emitted rule this way
/// is given to kink-flow as that rule's module-qualified label; anything else (`FILE:LINE`, a
/// compiled id, a name that matches no rule or several) is given unchanged, and kink-flow resolves
/// or refuses it with its own listing.
fn resolve_rule(command: &mut FlowCommand, emitted: &EmittedDefinition) {
    let FlowCommand::Fuzz { request, .. } = command else {
        return;
    };
    let (FuzzJobRequest::Rule { rule, .. } | FuzzJobRequest::Refuted { rule }) = &mut request.job
    else {
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
    // A lock `--locked` found stale: what would change, one line each, whatever the output.
    outcome.notes.extend(
        kink_flow::lock::stale_lines(document)
            .into_iter()
            .chain(kink_flow::lock::lock_notes(document))
            .map(|line| format!("krs kink: {line}")),
    );
    // What of the lock rests on a run the clock stopped, and each entry it kept unverified.
    outcome.notes.extend(
        kink_flow::clock::clock_lines(document)
            .into_iter()
            .map(|line| format!("krs kink: {line}")),
    );
    // A mutation's expectation the run does not meet, or cannot confirm: one line each.
    outcome.notes.extend(
        kink_flow::report::expectation_lines(document)
            .into_iter()
            .map(|line| format!("krs kink: {line}")),
    );
    match output {
        OutputFormat::Json => outcome.json(document, status),
        OutputFormat::Text => match kink_flow::cli::text(document) {
            Ok(text) => {
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
    use super::{MANIFEST_FILE, Verb, command_files, layout_files, shown_lock};
    use serde_json::json;
    use std::path::{Path, PathBuf};

    /// A lock kink-flow named by its own path is shown by the root-relative one, in its `path`
    /// and at the head of a refused lock's `detail`; a lock of another path is left alone.
    #[test]
    fn a_lock_is_shown_by_its_root_relative_path() {
        let lock = (
            "/abs/root/verdicts.lock".to_owned(),
            "verdicts.lock".to_owned(),
        );
        let mut document = json!({"lock": {
            "path": "/abs/root/verdicts.lock",
            "status": "refused",
            "detail": "/abs/root/verdicts.lock: is not TOML",
        }});
        shown_lock(&mut document, &lock);
        assert_eq!(document["lock"]["path"], "verdicts.lock");
        assert_eq!(document["lock"]["detail"], "verdicts.lock: is not TOML");
        let mut other = json!({"lock": {"path": "elsewhere.lock", "detail": "elsewhere.lock: x"}});
        let before = other.clone();
        shown_lock(&mut other, &lock);
        assert_eq!(other, before);
    }

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

    /// A corpus whose manifest declares its patterns (`[[patterns]]`) has no layout pattern
    /// list, so kink-flow asks the declared patterns; one that declares none keeps the layout's
    /// `PATTERNS.toml`; `--patterns` names the list in either case.
    #[test]
    fn declared_patterns_replace_the_layouts_pattern_list() {
        let corpus =
            std::env::temp_dir().join(format!("krs-cli-declared-patterns-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&corpus);
        std::fs::create_dir_all(&corpus).unwrap();
        std::fs::write(corpus.join("PATTERNS.toml"), "").unwrap();
        let spec = "[spec]\nkrs = { definition = \"main\" }\n";
        std::fs::write(corpus.join(MANIFEST_FILE), spec).unwrap();
        assert_eq!(
            layout_files(&corpus, Verb::Query).patterns,
            Some(corpus.join("PATTERNS.toml"))
        );
        assert_eq!(
            layout_files(&corpus, Verb::Fuzz).patterns,
            Some(corpus.join("PATTERNS.toml"))
        );
        std::fs::write(
            corpus.join(MANIFEST_FILE),
            format!("{spec}\n[[patterns]]\nfiles = \"patterns/*.toml\"\n"),
        )
        .unwrap();
        for verb in [Verb::Query, Verb::Fuzz] {
            assert_eq!(layout_files(&corpus, verb).patterns, None, "{verb:?}");
            let (files, _) = command_files(&corpus, verb, &[]).unwrap();
            assert_eq!(files.patterns, None, "{verb:?}");
        }
        let (files, rest) =
            command_files(&corpus, Verb::Query, &strings(&["--patterns", "p.toml"])).unwrap();
        assert_eq!(files.patterns, Some(PathBuf::from("p.toml")));
        assert!(rest.is_empty());
        let _ = std::fs::remove_dir_all(&corpus);
    }
}
