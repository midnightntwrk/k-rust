use crate::{
    CargoMetadata, CollectorPlan, CollectorRuntime, DefinitionRequest, DiagnosticEnvelope,
    DiagnosticStage, FacetSelector, GeneratedCollector, GenerationError, KrsCfg, PlanningError,
    RegistrationMode, diagnostic_envelope,
};
use krs_compiler::{
    DEFINITION_ARTIFACT, DescriptorLoweringError, EmitError, LoweringError,
    ReferenceExpansionError, SPEC_ARTIFACT, emit_k, expand_package_reference_source,
    lower_descriptor_bundle, lower_semantic_theory,
};
use krs_diagnostic::{Code, Diagnostic, Location, ToDiagnostic, codes};
use krs_ir::measure::{
    COLLECTOR_DIAGNOSTIC_ENV, COLLECTOR_MEASURE_ENV, COLLECTOR_READ_SET_ENV,
    CollectorMeasureDocument, CollectorReadSet, Counters, Measurement, unix_seconds,
};
use krs_ir::{
    DefinitionSentence, DescriptorBundle, PackageId, Sha256Digest, SourceFileId, SourceRange,
    StableText,
};
use krs_k_rust::{
    Backend, CompileOptions, DefinitionCompileError, FRONTEND_CAPABILITIES, adapt_definition,
    adapt_definition_for, compile_definition_timed, diagnostic_source_map_key,
};
use sha2::{Digest, Sha256};
use std::borrow::Cow;
use std::error::Error;
use std::ffi::OsStr;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, Output};

mod result_cache;
use result_cache::ResultCache;

use krs_compiler::{
    ARTIFACT_MARKER, ARTIFACT_MARKER_FILE, DEFINITION_IR_ARTIFACT, DESCRIPTOR_ARTIFACT,
    SEMANTIC_ARTIFACT, SOURCES_ARTIFACT, SYMBOLS_ARTIFACT,
};

/// Category of a production KRS command.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CommandKind {
    /// Check Rust and the complete selected KRS theory.
    Check,
    /// Print the deterministic layer-2 Rust reference surface.
    Expand,
    /// Emit the complete canonical source projection and shared sidecars.
    EmitK,
    /// Compile the same Definition IR through the native frontend.
    Build,
}

impl CommandKind {
    /// The command-line spelling, as recorded in measurement documents.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Check => "check",
            Self::Expand => "expand",
            Self::EmitK => "emit-k",
            Self::Build => "build",
        }
    }
}

/// A production command with its command-specific inputs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Command {
    /// Check Rust and the selected KRS theory with a native backend dialect.
    Check {
        /// Native backend dialect to check.
        backend: Backend,
    },
    /// Print the deterministic layer-2 Rust reference surface.
    Expand,
    /// Emit the canonical source projection and shared sidecars.
    EmitK {
        /// Artifact directory to populate.
        output: PathBuf,
    },
    /// Compile Definition IR with a native backend dialect into an artifact directory.
    Build {
        /// Native backend dialect to compile.
        backend: Backend,
        /// Artifact directory to populate.
        output: PathBuf,
    },
}

impl Command {
    /// Return the command category recorded in measurements and cache file names.
    #[must_use]
    pub const fn kind(&self) -> CommandKind {
        match self {
            Self::Check { .. } => CommandKind::Check,
            Self::Expand => CommandKind::Expand,
            Self::EmitK { .. } => CommandKind::EmitK,
            Self::Build { .. } => CommandKind::Build,
        }
    }

    /// The native backend dialect, for the commands that check or compile one.
    #[must_use]
    pub const fn backend(&self) -> Option<Backend> {
        match self {
            Self::Check { backend } | Self::Build { backend, .. } => Some(*backend),
            Self::Expand | Self::EmitK { .. } => None,
        }
    }

    /// The artifact directory, for the commands that write one.
    #[must_use]
    pub fn output(&self) -> Option<&Path> {
        match self {
            Self::EmitK { output } | Self::Build { output, .. } => Some(output),
            Self::Check { .. } | Self::Expand => None,
        }
    }
}

/// Explicit input to one production command execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandRequest {
    /// Command to execute.
    pub command: Command,
    /// Cargo manifest used for metadata and collector planning.
    pub manifest_path: PathBuf,
    /// Selected root definition facet.
    pub root: FacetSelector,
    /// Explicitly composed dependency facets.
    pub dependencies: Vec<FacetSelector>,
    /// KRS-owned rustc cfg values.
    pub cfg: Vec<KrsCfg>,
    /// Descriptor registration mechanism of the generated collector.
    ///
    /// [`RegistrationMode::Explicit`] is build and parity tooling; authored
    /// packages use the default.
    pub registration: RegistrationMode,
    /// Force the full pipeline even when an unchanged result is available.
    pub no_reuse: bool,
}

/// Stable command output intended for stdout.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandOutcome {
    stdout: Vec<u8>,
}

impl CommandOutcome {
    /// Bytes to write to stdout after successful execution.
    #[must_use]
    pub fn stdout(&self) -> &[u8] {
        &self.stdout
    }
}

struct PreparedDefinition {
    bundle: DescriptorBundle,
    semantic: krs_ir::SemanticTheory,
    lowered: krs_compiler::LoweredDefinition,
}

type OutputArtifact = (String, Vec<u8>);

struct CommandExecution {
    outcome: CommandOutcome,
    artifacts: Vec<OutputArtifact>,
}

impl CommandExecution {
    fn without_artifacts(outcome: CommandOutcome) -> Self {
        Self {
            outcome,
            artifacts: Vec::new(),
        }
    }
}

/// Execute one complete Cargo/collector/compiler command pipeline.
///
/// Every command collects the same canonical [`DescriptorBundle`], lowers it
/// through the same semantic theory and Definition IR, and then dispatches
/// only at the final command-specific stage. `build` calls only the permanent
/// structured native seam; it never invokes the provisional oracle or parses
/// emitted K source.
///
/// # Errors
///
/// Returns a typed stage error.
/// A native compilation or adapter failure is [`CommandError::Native`],
/// except that a compilation failure whose every diagnostic maps to an
/// authored source range is [`CommandError::Diagnostics`].
pub fn execute_command(request: &CommandRequest) -> Result<CommandOutcome, CommandError> {
    execute_command_measured(request, &mut Measurement::disabled())
}

/// [`execute_command`] that records opt-in phase timings and work counters
/// (`krs-timings/1` and `krs-counters/1`, documented in [`krs_ir::measure`]).
///
/// Measurement never changes stdout or any artifact. On failure, `measurement`
/// holds every completed span and names the failing one.
///
/// # Errors
///
/// Fails exactly when [`execute_command`] fails.
pub fn execute_command_measured(
    request: &CommandRequest,
    measurement: &mut Measurement,
) -> Result<CommandOutcome, CommandError> {
    measurement.counters.set("result.reused", 0u64);
    validate_request(request)?;
    let timings = &mut measurement.timings;
    let metadata = timings.try_span("cargo.metadata.input", |_| {
        cargo_metadata(&request.manifest_path)
    })?;
    let host_target = timings.try_span("host.discover", |_| rustc_host_target())?;

    let runtime = timings.try_span("cargo.metadata.runtime", |_| discover_runtime())?;
    let plan = timings.try_span("collector.plan", |_| {
        let plan = CollectorPlan::resolve_definition(
            &metadata,
            &DefinitionRequest {
                root: request.root.clone(),
                dependencies: request.dependencies.clone(),
                host_target,
                cfg: request.cfg.clone(),
            },
            runtime,
        )?;
        Ok::<_, CommandError>(match request.registration {
            RegistrationMode::Inventory => plan,
            RegistrationMode::Explicit => plan.with_explicit_registration()?,
        })
    })?;
    let collector_directory = generate_collector(&metadata, &plan, measurement)?;
    let executable = build_collector_measured(&collector_directory, &plan, measurement)?;
    let cache = ResultCache::new(&collector_directory, &executable, request);
    if request.command.kind() != CommandKind::Expand
        && !request.no_reuse
        && std::env::var_os("KRS_NO_REUSE").as_deref() != Some(OsStr::new("1"))
    {
        let started = std::time::Instant::now();
        if let Some(outcome) = cache.restore(request, &mut measurement.counters)? {
            measurement
                .timings
                .record("result.reuse", started.elapsed().as_secs_f64(), 0);
            measurement.counters.set("result.reused", 1u64);
            return Ok(outcome);
        }
    }
    let (stdout, read_set) = run_collector(&collector_directory, &executable, measurement)?;
    let prepared = prepare(stdout, measurement)?;

    let outcome = match &request.command {
        Command::Check { backend } => measurement
            .timings
            .try_span("check.adapt", |_| check(&prepared, *backend))
            .map(CommandExecution::without_artifacts),
        Command::Expand => measurement
            .timings
            .try_span("expand.render", |_| expand(&prepared, &plan))
            .map(CommandExecution::without_artifacts),
        Command::EmitK { output } => emit(&prepared, output, measurement),
        Command::Build { backend, output } => build(&prepared, *backend, output, measurement),
    };
    measurement.timings.span("release", |_| drop(prepared));
    if let Ok(ref value) = outcome
        && request.command.kind() != CommandKind::Expand
    {
        cache.store(
            request,
            &value.outcome,
            &value.artifacts,
            &read_set,
            &measurement.counters,
        );
    }
    outcome.map(|value| value.outcome)
}

fn validate_request(request: &CommandRequest) -> Result<(), CommandError> {
    if request.manifest_path.file_name() != Some(OsStr::new("Cargo.toml")) {
        return Err(CommandError::InvalidRequest(format!(
            "manifest path must end in Cargo.toml: `{}`",
            request.manifest_path.display()
        )));
    }
    Ok(())
}

fn generate_collector(
    metadata: &CargoMetadata,
    plan: &CollectorPlan,
    measurement: &mut Measurement,
) -> Result<PathBuf, CommandError> {
    measurement.timings.try_span("collector.generate", |_| {
        let target = metadata.target_directory.as_deref().ok_or_else(|| {
            CommandError::InvalidMetadata(
                "Cargo metadata did not provide an absolute target_directory".to_owned(),
            )
        })?;
        let target = Path::new(target);
        if !target.is_absolute() {
            return Err(CommandError::InvalidMetadata(
                "Cargo metadata target_directory is not absolute".to_owned(),
            ));
        }
        let collector = GeneratedCollector::from_plan(plan)?;
        let collector_directory = collector_directory(target, &collector);
        collector.write_to(&collector_directory)?;
        Ok(collector_directory)
    })
}

fn prepare(
    stdout: Vec<u8>,
    measurement: &mut Measurement,
) -> Result<PreparedDefinition, CommandError> {
    let bundle: DescriptorBundle = measurement
        .timings
        .try_span("protocol.decode", |_| {
            let bundle = DescriptorBundle::from_collector_protocol(&stdout)
                .map_err(CommandError::DescriptorProtocol);
            let bytes = stdout.len();
            drop(stdout);
            bundle.map(|bundle| (bundle, bytes))
        })
        .map(|(bundle, bytes)| {
            count_bundle(&mut measurement.counters, &bundle, bytes);
            bundle
        })?;
    let semantic = measurement
        .timings
        .try_span("semantic.lower", |_| lower_semantic(&bundle))?;
    measurement
        .counters
        .set("semantic.modules", semantic.modules().len());
    let lowered = measurement
        .timings
        .try_span("definition.lower", |_| lower_definition(&semantic))?;
    count_definition(&mut measurement.counters, &lowered);
    Ok(PreparedDefinition {
        bundle,
        semantic,
        lowered,
    })
}

/// Build and run the generated collector.
///
/// When measuring, the collector records its own phases in a sidecar file
/// named by [`COLLECTOR_MEASURE_ENV`]; they are nested below `collector.run`
/// after `collector.exec`, the time from spawning the executable until it
/// started collecting.
fn run_collector(
    collector_directory: &Path,
    executable: &Path,
    measurement: &mut Measurement,
) -> Result<(Vec<u8>, CollectorReadSet), CommandError> {
    let read_set = scratch_file("krs-collector-read-set-")?;
    let diagnostics = scratch_file("krs-collector-diagnostics-")?;
    let mut command = ProcessCommand::new(executable);
    command
        .current_dir(collector_directory)
        .env(COLLECTOR_READ_SET_ENV, read_set.path())
        .env(COLLECTOR_DIAGNOSTIC_ENV, diagnostics.path());
    let sidecar = measurement
        .is_enabled()
        .then(|| scratch_file("krs-collector-measure-"))
        .transpose()?;
    if let Some(sidecar) = &sidecar {
        command.env(COLLECTOR_MEASURE_ENV, sidecar.path());
    }
    let spawned = sidecar.as_ref().map(|_| unix_seconds());
    let output = measurement.timings.try_span("collector.run", |_| {
        process("collector execution", &mut command)
    });
    if let (Some(sidecar), Some(spawned)) = (sidecar, spawned) {
        let document = fs::read(sidecar.path())
            .ok()
            .and_then(|bytes| serde_json::from_slice::<CollectorMeasureDocument>(&bytes).ok());
        if let Some(document) = document {
            let timings = &mut measurement.timings;
            timings.record("collector.exec", document.started_unix_seconds - spawned, 1);
            for span in document.spans {
                timings.record(&span.id, span.seconds, span.depth.saturating_add(1));
            }
            for (name, value) in document.counters {
                measurement.counters.set(name, value);
            }
        }
    }
    let output = collector_result(output, diagnostics.path())?;
    let bytes = fs::read(read_set.path()).map_err(|source| CommandError::Io {
        path: read_set.path().to_path_buf(),
        source,
    });
    let read_set = serde_json::from_slice(&bytes?).map_err(CommandError::Serialization)?;
    Ok((output.stdout, read_set))
}

fn collector_result(
    output: Result<Output, CommandError>,
    path: &Path,
) -> Result<Output, CommandError> {
    if matches!(output, Err(CommandError::ProcessFailed { .. })) {
        let text = fs::read_to_string(path).map_err(|source| CommandError::Io {
            path: path.to_path_buf(),
            source,
        })?;
        let diagnostics =
            DiagnosticEnvelope::from_json_lines(&text).map_err(CommandError::DiagnosticProtocol)?;
        if !diagnostics.is_empty() {
            return Err(CommandError::Diagnostics(diagnostics));
        }
    }
    output
}

/// A JSON scratch file in the system temporary directory, removed on drop.
fn scratch_file(prefix: &str) -> Result<tempfile::NamedTempFile, CommandError> {
    tempfile::Builder::new()
        .prefix(prefix)
        .suffix(".json")
        .tempfile()
        .map_err(|source| CommandError::Io {
            path: std::env::temp_dir(),
            source,
        })
}

fn build_collector_measured(
    collector_directory: &Path,
    plan: &CollectorPlan,
    measurement: &mut Measurement,
) -> Result<PathBuf, CommandError> {
    // Cargo discovers hierarchical config from its working directory, not from
    // an arbitrary `--manifest-path`; this activates the generated cfg rustflags.
    let mut build = crate::cargo::command();
    build
        .current_dir(collector_directory)
        .args(["build", "--manifest-path"])
        .arg(collector_directory.join("Cargo.toml"))
        .args(["--message-format", "json-diagnostic-rendered-ansi"]);
    measurement
        .timings
        .try_span("collector.build", |_| build_collector(&mut build, plan))
}

fn count_bundle(counters: &mut Counters, bundle: &DescriptorBundle, bytes: usize) {
    if !counters.is_enabled() {
        return;
    }
    counters.set("bundle.bytes", bytes);
    if let Some(provenance) = counters.get("bundle.provenance_bytes") {
        let bytes = u64::try_from(bytes).unwrap_or(u64::MAX);
        counters.set("bundle.other_bytes", bytes.saturating_sub(provenance));
    }
    counters.set("descriptors.total", bundle.descriptors.len());
    counters.set("declarations.total", bundle.declarations.len());
    let mut anchors = 0;
    let mut frames = 0;
    for descriptor in &bundle.descriptors {
        counters.add(
            format!(
                "descriptors.kind.{}",
                descriptor.id.item_kind().stable_text()
            ),
            1u64,
        );
        let origins = descriptor.provenance.origins();
        anchors += origins.len();
        frames += origins
            .iter()
            .map(|node| node.origin.frames().len())
            .sum::<usize>();
    }
    counters.set("provenance.anchors", anchors);
    counters.set("provenance.origin_frames", frames);
}

fn count_definition(counters: &mut Counters, lowered: &krs_compiler::LoweredDefinition) {
    if !counters.is_enabled() {
        return;
    }
    let definition = lowered.definition();
    counters.set("definition.modules", definition.modules().len());
    let mut sentences = 0;
    for module in definition.modules() {
        sentences += module.sentences().len();
        for sentence in module.sentences() {
            let kind = match sentence {
                DefinitionSentence::SyntaxSort(_) => "syntax_sort",
                DefinitionSentence::Subsort(_) => "subsort",
                DefinitionSentence::Production(_) => "production",
                DefinitionSentence::Precedence(_) => "precedence",
                DefinitionSentence::Associativity(_) => "associativity",
                DefinitionSentence::Configuration(_) => "configuration",
                DefinitionSentence::ContextAlias(_) => "context_alias",
                DefinitionSentence::Rule(_) => "rule",
            };
            counters.add(format!("definition.sentences.{kind}"), 1u64);
        }
    }
    counters.set("definition.sentences", sentences);
    counters.set("definition.symbols", lowered.symbol_map().entries().len());
    counters.set(
        "definition.source_map_entries",
        lowered.source_map().entries().len(),
    );
}

fn lower_semantic(bundle: &DescriptorBundle) -> Result<krs_ir::SemanticTheory, CommandError> {
    lower_descriptor_bundle(bundle).map_err(CommandError::DescriptorLowering)
}

fn lower_definition(
    semantic: &krs_ir::SemanticTheory,
) -> Result<krs_compiler::LoweredDefinition, CommandError> {
    lower_semantic_theory(semantic).map_err(CommandError::Lowering)
}

fn collector_directory(target: &Path, collector: &GeneratedCollector) -> PathBuf {
    let mut digest = Sha256::new();
    for bytes in [
        collector.manifest.as_slice(),
        collector.main_source.as_slice(),
        collector.cargo_config.as_slice(),
        collector.canonical_selection.as_slice(),
    ] {
        digest.update(bytes.len().to_le_bytes());
        digest.update(bytes);
    }
    target
        .join("krs")
        .join("collectors")
        .join(format!("{:x}", digest.finalize()))
}

fn check(prepared: &PreparedDefinition, backend: Backend) -> Result<CommandOutcome, CommandError> {
    if !FRONTEND_CAPABILITIES.supports_backend(backend) {
        return Err(CommandError::UnsupportedBackend(backend));
    }
    // Structural adaptation checks the selected target-neutral definition
    // without claiming that the unavailable preparation seam can compile it.
    adapt_definition(prepared.lowered.definition())
        .map_err(|error| CommandError::Native(DefinitionCompileError::Adapter(error)))?;
    Ok(CommandOutcome {
        stdout: format!(
            "KRS check passed: {} descriptors, {} semantic modules\n",
            prepared.bundle.descriptors.len(),
            prepared.semantic.modules().len()
        )
        .into_bytes(),
    })
}

fn expand(
    prepared: &PreparedDefinition,
    plan: &CollectorPlan,
) -> Result<CommandOutcome, CommandError> {
    let root = plan
        .facets()
        .iter()
        .find(|facet| facet.is_root)
        .ok_or_else(|| CommandError::InvalidMetadata("collector plan has no root facet".into()))?;
    let package = PackageId::new(
        &root.k_namespace,
        &root.package_name,
        &root.package_version,
        &root.cargo_source,
    )
    .map_err(|error| {
        CommandError::InvalidMetadata(format!("root package identity is invalid: {error}"))
    })?;
    let expanded = expand_package_reference_source(
        &prepared.bundle,
        &prepared.semantic,
        &package,
        &root.manifest_path,
    )?;
    Ok(CommandOutcome {
        stdout: expanded.into_bytes(),
    })
}

fn emit(
    prepared: &PreparedDefinition,
    output: &Path,
    measurement: &mut Measurement,
) -> Result<CommandExecution, CommandError> {
    let (descriptor_bundle, semantic_ir, definition_ir, emitted, symbols, sources) =
        measurement.timings.try_span("emit_k.render", |_| {
            let descriptor_bundle = prepared.bundle.to_canonical_json()?;
            let semantic_ir = prepared.semantic.to_canonical_json()?;
            let definition_ir = prepared.lowered.definition().to_canonical_json()?;
            let emitted = emit_k(&prepared.lowered)?;
            let symbols = emitted.symbol_map().to_canonical_json()?;
            let sources = emitted.source_map().to_canonical_json()?;
            Ok::<_, CommandError>((
                descriptor_bundle,
                semantic_ir,
                definition_ir,
                emitted,
                symbols,
                sources,
            ))
        })?;
    let mut artifacts = vec![
        (DESCRIPTOR_ARTIFACT, descriptor_bundle.as_bytes()),
        (SEMANTIC_ARTIFACT, semantic_ir.as_bytes()),
        (DEFINITION_IR_ARTIFACT, definition_ir.as_bytes()),
        (DEFINITION_ARTIFACT, emitted.source().as_bytes()),
    ];
    if let Some(spec) = emitted.spec() {
        artifacts.push((SPEC_ARTIFACT, spec.source().as_bytes()));
    }
    artifacts.extend([
        (SYMBOLS_ARTIFACT, symbols.as_bytes()),
        (SOURCES_ARTIFACT, sources.as_bytes()),
    ]);
    let stdout = emission_stdout(&artifacts);
    let mut artifacts = artifacts
        .into_iter()
        .map(|(name, bytes)| (name.to_owned(), bytes.to_vec()))
        .collect::<Vec<_>>();
    artifacts.sort_unstable_by(|(left, _), (right, _)| left.cmp(right));
    measurement.timings.try_span("emit_k.write", |_| {
        prepare_output(output)?;
        for (name, bytes) in &artifacts {
            write_output(output, name, bytes)?;
        }
        Ok::<_, CommandError>(())
    })?;
    for (name, bytes) in &artifacts {
        measurement
            .counters
            .set(format!("emit_k.bytes.{name}"), bytes.len());
    }
    Ok(CommandExecution {
        outcome: CommandOutcome { stdout },
        artifacts,
    })
}

fn emission_stdout(artifacts: &[(&str, &[u8])]) -> Vec<u8> {
    let names = artifacts.iter().map(|(name, _)| *name).collect::<Vec<_>>();
    format!("emitted {}\n", names.join(", ")).into_bytes()
}

fn build(
    prepared: &PreparedDefinition,
    backend: Backend,
    output: &Path,
    measurement: &mut Measurement,
) -> Result<CommandExecution, CommandError> {
    let artifacts = compile_definition_timed(
        prepared.lowered.definition(),
        CompileOptions {
            backend,
            ..CompileOptions::default()
        },
        &mut measurement.timings,
    )
    .map_err(|error| {
        measurement.timings.span("native.diagnostics", |_| {
            native_command_error(prepared, backend, error)
        })
    })?;
    let files = vec![
        (
            "definition.kore".to_owned(),
            artifacts.definition_kore.into_bytes(),
        ),
        (
            "syntaxDefinition.kore".to_owned(),
            artifacts.syntax_definition_kore.into_bytes(),
        ),
        ("macros.kore".to_owned(), artifacts.macros_kore.into_bytes()),
    ];
    // Do not create the output directory until structured compilation has
    // succeeded. A native rejection therefore leaves no artifacts.
    measurement.timings.try_span("native.write", |_| {
        prepare_output(output)?;
        for (name, bytes) in &files {
            write_output(output, name, bytes)?;
        }
        Ok::<_, CommandError>(())
    })?;
    for (name, bytes) in &files {
        measurement
            .counters
            .set(format!("native.bytes.{name}"), bytes.len());
    }
    measurement
        .counters
        .set("native.omitted_claims", artifacts.omitted_claims);
    // Only a backend that does not prove omits claims.
    let omitted = match artifacts.omitted_claims {
        0 => String::new(),
        1 => "omitted 1 claim: the llvm backend executes but does not prove\n".to_owned(),
        count => format!("omitted {count} claims: the llvm backend executes but does not prove\n"),
    };
    let stdout = format!("built definition.kore, syntaxDefinition.kore, macros.kore\n{omitted}");
    Ok(CommandExecution {
        outcome: CommandOutcome {
            stdout: stdout.into_bytes(),
        },
        artifacts: files,
    })
}

fn native_command_error(
    prepared: &PreparedDefinition,
    backend: Backend,
    error: DefinitionCompileError,
) -> CommandError {
    let DefinitionCompileError::Compile { diagnostics, .. } = &error else {
        return CommandError::Native(error);
    };
    if diagnostics.is_empty() {
        return CommandError::Native(error);
    }
    let Ok(adapted) = adapt_definition_for(prepared.lowered.definition(), backend) else {
        return CommandError::Native(error);
    };
    let mut translated = Vec::with_capacity(diagnostics.len());
    for diagnostic in diagnostics {
        let Some(key) = diagnostic_source_map_key(adapted.origins(), diagnostic) else {
            return CommandError::Native(error);
        };
        let Some(envelope) =
            crate::translate_native_diagnostic(prepared.lowered.source_map(), &key, diagnostic)
        else {
            return CommandError::Native(error);
        };
        translated.push(envelope);
    }
    translated.sort_by(|left, right| {
        (&left.code, &left.authored_range).cmp(&(&right.code, &right.authored_range))
    });
    translated.dedup();
    CommandError::Diagnostics(translated)
}

fn prepare_output(path: &Path) -> Result<(), CommandError> {
    if path.exists() {
        let empty = fs::read_dir(path)
            .map_err(|source| CommandError::Io {
                path: path.to_path_buf(),
                source,
            })?
            .next()
            .is_none();
        if !empty {
            let marker = path.join(ARTIFACT_MARKER_FILE);
            let owned =
                fs::read_to_string(&marker).is_ok_and(|contents| contents == ARTIFACT_MARKER);
            if !owned {
                return Err(CommandError::UnsafeOutput(path.to_path_buf()));
            }
        }
    }
    fs::create_dir_all(path).map_err(|source| CommandError::Io {
        path: path.to_path_buf(),
        source,
    })?;
    write_output_if_different(path, ARTIFACT_MARKER_FILE, ARTIFACT_MARKER.as_bytes())
}

fn write_output_if_different(
    directory: &Path,
    name: &str,
    bytes: &[u8],
) -> Result<(), CommandError> {
    let path = directory.join(name);
    if fs::read(&path).is_ok_and(|existing| existing == bytes) {
        return Ok(());
    }
    write_output(directory, name, bytes)
}

fn write_output(directory: &Path, name: &str, bytes: &[u8]) -> Result<(), CommandError> {
    let path = directory.join(name);
    fs::write(&path, bytes).map_err(|source| CommandError::Io { path, source })
}

fn cargo_metadata(manifest: &Path) -> Result<CargoMetadata, CommandError> {
    let output = cargo(
        "Cargo metadata",
        crate::cargo::command()
            .args(["metadata", "--format-version", "1", "--manifest-path"])
            .arg(manifest),
    )?;
    CargoMetadata::from_json(&output.stdout).map_err(CommandError::Metadata)
}

fn discover_runtime() -> Result<CollectorRuntime, CommandError> {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    let metadata = cargo_metadata(&manifest)?;
    Ok(CollectorRuntime {
        host_manifest: unique_manifest(&metadata, "krs")?,
        collector_manifest: unique_manifest(&metadata, "krs-collector")?,
    })
}

fn unique_manifest(metadata: &CargoMetadata, name: &str) -> Result<PathBuf, CommandError> {
    let manifests = metadata
        .packages
        .iter()
        .filter(|package| package.name == name)
        .map(|package| PathBuf::from(&package.manifest_path))
        .collect::<Vec<_>>();
    match manifests.as_slice() {
        [manifest] => Ok(manifest.clone()),
        [] => Err(CommandError::InvalidMetadata(format!(
            "KRS installation metadata contains no `{name}` package"
        ))),
        _ => Err(CommandError::InvalidMetadata(format!(
            "KRS installation metadata contains multiple `{name}` packages"
        ))),
    }
}

fn rustc_host_target() -> Result<String, CommandError> {
    let output = process(
        "rustc host discovery",
        ProcessCommand::new("rustc").arg("-vV"),
    )?;
    let stdout = String::from_utf8(output.stdout)
        .map_err(|_| CommandError::InvalidMetadata("rustc -vV output is not UTF-8".to_owned()))?;
    stdout
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .map(str::to_owned)
        .ok_or_else(|| {
            CommandError::InvalidMetadata("rustc -vV omitted its host target".to_owned())
        })
}

fn build_collector(
    command: &mut ProcessCommand,
    plan: &CollectorPlan,
) -> Result<PathBuf, CommandError> {
    let output = command
        .output()
        .map_err(|source| CommandError::ProcessStart {
            stage: "collector build",
            source,
        })?;
    if !output.status.success() {
        let diagnostics = rust_diagnostics(&output.stdout, plan)?;
        return if diagnostics.is_empty() {
            Err(CommandError::ProcessFailed {
                stage: "collector build",
                status: output.status.code(),
                stderr: cargo_failure_text(&output),
            })
        } else {
            Err(CommandError::Diagnostics(diagnostics))
        };
    }
    let executables = output
        .stdout
        .split(|byte| *byte == b'\n')
        .filter_map(|line| serde_json::from_slice::<CargoArtifact>(line).ok())
        .filter(|message| {
            message.reason == "compiler-artifact"
                && message.target.kind.iter().any(|kind| kind == "bin")
        })
        .filter_map(|message| message.executable)
        .collect::<Vec<_>>();
    match executables.as_slice() {
        [executable] => Ok(executable.clone()),
        _ => Err(CommandError::InvalidMetadata(format!(
            "collector build reported {} executables; expected one",
            executables.len()
        ))),
    }
}

#[derive(serde::Deserialize)]
struct CargoArtifact {
    reason: String,
    target: CargoArtifactTarget,
    executable: Option<PathBuf>,
}

#[derive(serde::Deserialize)]
struct CargoArtifactTarget {
    kind: Vec<String>,
}

fn cargo_failure_text(output: &Output) -> String {
    let mut rendered = String::new();
    for line in output.stdout.split(|byte| *byte == b'\n') {
        let Ok(message) = serde_json::from_slice::<CargoCompilerMessage>(line) else {
            continue;
        };
        if message.reason == "compiler-message"
            && let Some(message_text) = message.message.and_then(|diagnostic| diagnostic.rendered)
        {
            rendered.push_str(&message_text);
        }
    }
    rendered.push_str(&String::from_utf8_lossy(&output.stderr));
    rendered
}

#[derive(serde::Deserialize)]
struct CargoCompilerMessage {
    reason: String,
    manifest_path: Option<String>,
    message: Option<RustDiagnostic>,
}

#[derive(serde::Deserialize)]
struct RustDiagnostic {
    level: String,
    message: String,
    code: Option<RustDiagnosticCode>,
    spans: Vec<RustDiagnosticSpan>,
    rendered: Option<String>,
}

#[derive(serde::Deserialize)]
struct RustDiagnosticCode {
    code: String,
}

#[derive(serde::Deserialize)]
struct RustDiagnosticSpan {
    file_name: String,
    byte_start: u32,
    byte_end: u32,
    is_primary: bool,
}

fn rust_diagnostics(
    stdout: &[u8],
    plan: &CollectorPlan,
) -> Result<Vec<DiagnosticEnvelope>, CommandError> {
    let mut diagnostics = Vec::new();
    for line in stdout.split(|byte| *byte == b'\n') {
        let Ok(message) = serde_json::from_slice::<CargoCompilerMessage>(line) else {
            continue;
        };
        if message.reason != "compiler-message" {
            continue;
        }
        let Some(diagnostic) = message.message.filter(|value| value.level == "error") else {
            continue;
        };
        let Some(manifest) = message.manifest_path.as_deref() else {
            continue;
        };
        let code = diagnostic.code.as_ref().map_or_else(
            || codes::rust_expansion::UNCODED_ERROR,
            |code| Code::foreign(code.code.clone()),
        );
        for span in diagnostic.spans.iter().filter(|span| span.is_primary) {
            if let Some(range) = rust_source_range(plan, manifest, span)? {
                let view = diagnostic_envelope(
                    Diagnostic::error(
                        code.clone(),
                        diagnostic.message.clone(),
                        Location::Source(range),
                    ),
                    DiagnosticStage::RustExpansion,
                    None,
                );
                diagnostics.extend(view);
            }
        }
    }
    diagnostics.sort_by(|left, right| {
        (&left.code, &left.authored_range).cmp(&(&right.code, &right.authored_range))
    });
    diagnostics.dedup();
    Ok(diagnostics)
}

fn rust_source_range(
    plan: &CollectorPlan,
    manifest: &str,
    span: &RustDiagnosticSpan,
) -> Result<Option<SourceRange>, CommandError> {
    let Some(facet) = plan
        .facets()
        .iter()
        .find(|facet| facet.manifest_path == Path::new(manifest))
    else {
        return Ok(None);
    };
    let manifest_directory = facet.manifest_path.parent().ok_or_else(|| {
        CommandError::InvalidMetadata("selected package manifest has no parent".to_owned())
    })?;
    let path = Path::new(&span.file_name);
    let path = if path.is_absolute() {
        path.to_path_buf()
    } else {
        manifest_directory.join(path)
    };
    let Ok(relative) = path.strip_prefix(manifest_directory) else {
        return Ok(None);
    };
    let relative = relative
        .to_str()
        .ok_or_else(|| {
            CommandError::InvalidMetadata("Rust diagnostic source path is not UTF-8".to_owned())
        })?
        .replace('\\', "/");
    let source = fs::read(&path).map_err(|source| CommandError::Io {
        path: path.clone(),
        source,
    })?;
    if span.byte_end as usize > source.len() {
        return Err(CommandError::InvalidMetadata(
            "Rust diagnostic range exceeds its source revision".to_owned(),
        ));
    }
    let package = PackageId::new(
        &facet.k_namespace,
        &facet.package_name,
        &facet.package_version,
        &facet.cargo_source,
    )
    .map_err(|error| CommandError::InvalidMetadata(error.to_string()))?;
    let file = SourceFileId::new(
        package,
        relative,
        Sha256Digest::from_bytes(Sha256::digest(&source).into()),
    )
    .map_err(|error| CommandError::InvalidMetadata(error.to_string()))?;
    SourceRange::new(file, span.byte_start, span.byte_end)
        .map(Some)
        .map_err(|error| CommandError::InvalidMetadata(error.to_string()))
}

fn cargo(stage: &'static str, command: &mut ProcessCommand) -> Result<Output, CommandError> {
    process(stage, command)
}

fn process(stage: &'static str, command: &mut ProcessCommand) -> Result<Output, CommandError> {
    let output = command
        .output()
        .map_err(|source| CommandError::ProcessStart { stage, source })?;
    if output.status.success() {
        Ok(output)
    } else {
        Err(CommandError::ProcessFailed {
            stage,
            status: output.status.code(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        })
    }
}

/// Failure from a named production-command stage.
#[derive(Debug)]
pub enum CommandError {
    /// The request or its selected source cannot satisfy the command.
    InvalidRequest(String),
    /// Cargo metadata output was malformed.
    Metadata(crate::MetadataError),
    /// Cargo metadata omitted a required execution field or runtime package.
    InvalidMetadata(String),
    /// Definition-facet planning failed.
    Planning(PlanningError),
    /// Collector package generation failed.
    Generation(GenerationError),
    /// A subprocess could not be started.
    ProcessStart {
        /// Stage being executed.
        stage: &'static str,
        /// Operating-system error.
        source: io::Error,
    },
    /// A subprocess returned a nonzero status.
    ProcessFailed {
        /// Stage being executed.
        stage: &'static str,
        /// Numeric exit status, absent when terminated by a signal.
        status: Option<i32>,
        /// Captured diagnostic stream.
        stderr: String,
    },
    /// One or more renderer-independent diagnostics with exact authored ranges.
    Diagnostics(Vec<DiagnosticEnvelope>),
    /// Collector stdout was not a current canonical descriptor protocol.
    DescriptorProtocol(serde_json::Error),
    /// Collector diagnostics were malformed or used an unsupported schema.
    DiagnosticProtocol(serde_json::Error),
    /// Descriptor-to-semantic lowering failed.
    DescriptorLowering(DescriptorLoweringError),
    /// Semantic-to-Definition lowering failed.
    Lowering(LoweringError),
    /// Canonical K emission failed.
    Emission(EmitError),
    /// Readable source could not be projected to deterministic layer-2 Rust.
    ReferenceExpansion(ReferenceExpansionError),
    /// Native structured compilation failed, including typed capabilities.
    Native(DefinitionCompileError),
    /// The selected native backend is unavailable in this build.
    UnsupportedBackend(Backend),
    /// Canonical JSON serialization failed.
    Serialization(serde_json::Error),
    /// A filesystem operation failed.
    Io {
        /// Affected path.
        path: PathBuf,
        /// Operating-system error.
        source: io::Error,
    },
    /// Artifact output appears to belong to the user or another tool.
    UnsafeOutput(PathBuf),
}

impl fmt::Display for CommandError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRequest(message) | Self::InvalidMetadata(message) => {
                formatter.write_str(message)
            }
            Self::Metadata(error) => error.fmt(formatter),
            Self::Planning(error) => write!(formatter, "could not plan collector: {error}"),
            Self::Generation(error) => error.fmt(formatter),
            Self::ProcessStart { stage, source } => {
                write!(formatter, "could not start {stage}: {source}")
            }
            Self::ProcessFailed {
                stage,
                status,
                stderr,
            } => write!(
                formatter,
                "{stage} failed with status {}: {}",
                status.map_or_else(|| "signal".to_owned(), |status| status.to_string()),
                stderr.trim_end()
            ),
            Self::Diagnostics(diagnostics) => write!(
                formatter,
                "compilation failed with {} structured diagnostic{}",
                diagnostics.len(),
                if diagnostics.len() == 1 { "" } else { "s" }
            ),
            Self::DiagnosticProtocol(error) => write!(
                formatter,
                "collector returned invalid diagnostic protocol: {error}"
            ),
            Self::DescriptorProtocol(error) => {
                write!(
                    formatter,
                    "collector returned invalid descriptor protocol: {error}"
                )
            }
            Self::DescriptorLowering(error) => error.fmt(formatter),
            Self::Lowering(error) => error.fmt(formatter),
            Self::Emission(error) => error.fmt(formatter),
            Self::ReferenceExpansion(error) => error.fmt(formatter),
            Self::Native(error) => error.fmt(formatter),
            Self::UnsupportedBackend(backend) => {
                write!(
                    formatter,
                    "native backend `{}` is unavailable",
                    backend.as_str()
                )
            }
            Self::Serialization(error) => {
                write!(
                    formatter,
                    "could not serialize deterministic output: {error}"
                )
            }
            Self::Io { path, source } => {
                write!(formatter, "could not write `{}`: {source}", path.display())
            }
            Self::UnsafeOutput(path) => write!(
                formatter,
                "refusing to replace non-KRS artifact directory `{}`",
                path.display()
            ),
        }
    }
}

impl Error for CommandError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Metadata(error) => Some(error),
            Self::Planning(error) => Some(error),
            Self::Generation(error) => Some(error),
            Self::ProcessStart { source, .. } | Self::Io { source, .. } => Some(source),
            Self::DescriptorProtocol(error)
            | Self::DiagnosticProtocol(error)
            | Self::Serialization(error) => Some(error),
            Self::DescriptorLowering(error) => Some(error),
            Self::Lowering(error) => Some(error),
            Self::Emission(error) => Some(error),
            Self::ReferenceExpansion(error) => Some(error),
            Self::Native(error) => Some(error),
            Self::InvalidRequest(_)
            | Self::InvalidMetadata(_)
            | Self::ProcessFailed { .. }
            | Self::Diagnostics(_)
            | Self::UnsupportedBackend(_)
            | Self::UnsafeOutput(_) => None,
        }
    }
}

impl CommandError {
    /// Returns envelopes when the producing diagnostic has an exact authored range.
    #[must_use]
    pub fn diagnostics(&self) -> Option<Cow<'_, [DiagnosticEnvelope]>> {
        let diagnostic = match self {
            Self::Diagnostics(diagnostics) => return Some(Cow::Borrowed(diagnostics)),
            Self::DescriptorLowering(error) => error.to_diagnostic(),
            Self::Lowering(error) => error.to_diagnostic(),
            _ => return None,
        };
        diagnostic_envelope(diagnostic, DiagnosticStage::Analysis, None)
            .map(|envelope| Cow::Owned(vec![envelope]))
    }
}

impl From<PlanningError> for CommandError {
    fn from(value: PlanningError) -> Self {
        Self::Planning(value)
    }
}

impl From<GenerationError> for CommandError {
    fn from(value: GenerationError) -> Self {
        Self::Generation(value)
    }
}

impl From<DescriptorLoweringError> for CommandError {
    fn from(value: DescriptorLoweringError) -> Self {
        Self::DescriptorLowering(value)
    }
}

impl From<LoweringError> for CommandError {
    fn from(value: LoweringError) -> Self {
        Self::Lowering(value)
    }
}

impl From<EmitError> for CommandError {
    fn from(value: EmitError) -> Self {
        Self::Emission(value)
    }
}

impl From<ReferenceExpansionError> for CommandError {
    fn from(value: ReferenceExpansionError) -> Self {
        Self::ReferenceExpansion(value)
    }
}

impl From<DefinitionCompileError> for CommandError {
    fn from(value: DefinitionCompileError) -> Self {
        Self::Native(value)
    }
}

impl From<serde_json::Error> for CommandError {
    fn from(value: serde_json::Error) -> Self {
        Self::Serialization(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PackageSelector;

    #[test]
    fn emission_stdout_preserves_artifact_names_and_claims_spelling() {
        let mut artifacts: Vec<(&str, &[u8])> = vec![
            (DESCRIPTOR_ARTIFACT, b""),
            (SEMANTIC_ARTIFACT, b""),
            (DEFINITION_IR_ARTIFACT, b""),
            (DEFINITION_ARTIFACT, b""),
            (SYMBOLS_ARTIFACT, b""),
            (SOURCES_ARTIFACT, b""),
        ];
        assert_eq!(
            emission_stdout(&artifacts),
            b"emitted descriptor-bundle.json, semantic-ir.json, definition-ir.json, definition.k, symbols.json, sources.json\n"
        );
        artifacts.insert(4, (SPEC_ARTIFACT, b""));
        assert_eq!(
            emission_stdout(&artifacts),
            b"emitted descriptor-bundle.json, semantic-ir.json, definition-ir.json, definition.k, spec.k, symbols.json, sources.json\n"
        );
    }

    #[test]
    fn analysis_failures_expose_envelopes_only_with_an_exact_authored_range() {
        let package = PackageId::new("diag", "diag", "0.1.0", "workspace").unwrap();
        let file = SourceFileId::new(
            package,
            "src/lib.rs",
            Sha256Digest::new("11".repeat(32)).unwrap(),
        )
        .unwrap();
        let range = SourceRange::new(file, 7, 16).unwrap();
        let error = LoweringError::NameCollision {
            namespace: krs_compiler::CollisionNamespace::EmittedSymbol,
            value: "name".to_owned(),
            first: "first".to_owned(),
            second: "second".to_owned(),
            second_origin: krs_ir::OriginStack::authored(range.clone()),
        };
        let message = error.to_string();
        let failure = CommandError::from(error);
        let envelopes = failure.diagnostics().unwrap();
        assert_eq!(envelopes.len(), 1);
        assert_eq!(envelopes[0].code, "krs::analysis::symbol-name-collision");
        assert_eq!(envelopes[0].message, message);
        assert_eq!(envelopes[0].authored_range, range);
        let unlocated = CommandError::Lowering(LoweringError::InvalidSidecar("detail".to_owned()));
        assert!(unlocated.diagnostics().is_none());
        assert_eq!(unlocated.to_string(), "invalid lowered sidecar: detail");
    }

    #[test]
    fn rust_spans_use_validated_facet_identity_and_do_not_hide_selected_source_errors() {
        let directory = tempfile::tempdir().unwrap();
        let manifest = directory.path().join("Cargo.toml");
        fs::create_dir(directory.path().join("src")).unwrap();
        let source = "pub trait Expr {}\n";
        fs::write(directory.path().join("src/lib.rs"), source).unwrap();
        let metadata = CargoMetadata::from_json(&serde_json::to_vec(&serde_json::json!({
            "packages": [{
                "id": "language", "name": "language", "version": "0.1.0", "source": null,
                "manifest_path": manifest,
                "metadata": { "krs": { "k-namespace": "ORG-LANGUAGE", "definitions": { "main": {} } } },
                "targets": [{ "name": "language", "kind": ["lib"], "crate_types": ["lib"] }],
            }],
            "resolve": { "nodes": [{ "id": "language", "features": [], "dependencies": [] }] },
            "workspace_members": ["language"],
        })).unwrap()).unwrap();
        let plan = CollectorPlan::resolve_definition(
            &metadata,
            &DefinitionRequest {
                root: FacetSelector {
                    package: PackageSelector::Name("language".to_owned()),
                    definition: "main".to_owned(),
                },
                dependencies: vec![],
                host_target: "x86_64-unknown-linux-gnu".to_owned(),
                cfg: vec![],
            },
            CollectorRuntime {
                host_manifest: "/tool/krs/Cargo.toml".into(),
                collector_manifest: "/tool/krs-collector/Cargo.toml".into(),
            },
        )
        .unwrap();
        let mut span = RustDiagnosticSpan {
            file_name: "src/lib.rs".to_owned(),
            byte_start: 10,
            byte_end: 14,
            is_primary: true,
        };
        let range = rust_source_range(&plan, manifest.to_str().unwrap(), &span)
            .unwrap()
            .unwrap();
        assert_eq!(range.file.package().k_namespace(), "ORG-LANGUAGE");
        assert_eq!(range.file.package_relative_path(), "src/lib.rs");
        assert_eq!(
            range.file.content_sha256(),
            &Sha256Digest::from_bytes(Sha256::digest(source.as_bytes()).into())
        );
        assert_eq!((range.start_byte, range.end_byte), (10, 14));
        assert!(
            rust_source_range(&plan, "/outside/Cargo.toml", &span)
                .unwrap()
                .is_none()
        );
        span.byte_end = 100;
        assert!(matches!(
            rust_source_range(&plan, manifest.to_str().unwrap(), &span),
            Err(CommandError::InvalidMetadata(_))
        ));
        span.file_name = "src/missing.rs".to_owned();
        assert!(matches!(
            rust_source_range(&plan, manifest.to_str().unwrap(), &span),
            Err(CommandError::Io { .. })
        ));
    }

    #[test]
    fn collector_failure_sidecar_is_validated_before_forwarding() {
        let sidecar = tempfile::NamedTempFile::new().unwrap();
        let failure = || {
            Err(CommandError::ProcessFailed {
                stage: "collector execution",
                status: Some(1),
                stderr: "human detail".to_owned(),
            })
        };
        assert!(matches!(
            collector_result(failure(), sidecar.path()),
            Err(CommandError::ProcessFailed { .. })
        ));
        let file = SourceFileId::new(
            PackageId::new("diag", "diag", "0.1.0", "workspace").unwrap(),
            "src/lib.rs",
            Sha256Digest::new("11".repeat(32)).unwrap(),
        )
        .unwrap();
        let envelope = DiagnosticEnvelope::error(
            DiagnosticStage::Analysis,
            "krs::collect::source-syntax",
            "detail",
            SourceRange::new(file, 7, 16).unwrap(),
        );
        let json = envelope.to_json_line().unwrap();
        fs::write(sidecar.path(), json.repeat(2)).unwrap();
        let error = collector_result(failure(), sidecar.path()).unwrap_err();
        assert_eq!(
            error.diagnostics().unwrap().as_ref(),
            &[envelope.clone(), envelope.clone()]
        );
        for invalid in [
            "not json".to_owned(),
            json.replace("\"schema_version\":1", "\"schema_version\":2"),
            json.replace(
                "\"schema_version\":1",
                "\"unknown\":true,\"schema_version\":1",
            ),
            format!("{json}not json\n"),
        ] {
            fs::write(sidecar.path(), invalid).unwrap();
            assert!(matches!(
                collector_result(failure(), sidecar.path()),
                Err(CommandError::DiagnosticProtocol(_))
            ));
        }
    }

    #[test]
    fn manifest_path_must_name_cargo_toml() {
        let base = CommandRequest {
            command: Command::Check {
                backend: Backend::Llvm,
            },
            manifest_path: PathBuf::from("Cargo.toml"),
            root: FacetSelector {
                package: PackageSelector::Name("language".to_owned()),
                definition: "main".to_owned(),
            },
            dependencies: Vec::new(),
            cfg: Vec::new(),
            registration: RegistrationMode::Inventory,
            no_reuse: false,
        };
        assert!(validate_request(&base).is_ok());
        let mut invalid = base;
        invalid.manifest_path = PathBuf::from("Other.toml");
        assert!(matches!(
            validate_request(&invalid),
            Err(CommandError::InvalidRequest(_))
        ));
    }
}
