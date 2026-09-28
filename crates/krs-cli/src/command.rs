use crate::{
    CargoMetadata, CollectorPlan, CollectorRuntime, DefinitionRequest, DiagnosticEnvelope,
    DiagnosticStage, FacetSelector, GeneratedCollector, GenerationError, KrsCfg, PlanningError,
    RegistrationMode, exact_authored_range_from_origin,
};
use krs_compiler::{
    DEFINITION_ARTIFACT, DescriptorLoweringError, EmitError, LoweringError,
    ReferenceExpansionError, SPEC_ARTIFACT, emit_k, expand_reference_source,
    lower_descriptor_bundle, lower_semantic_theory,
};
use krs_ir::measure::{
    COLLECTOR_MEASURE_ENV, COLLECTOR_READ_SET_ENV, CollectorMeasureDocument, CollectorReadSet,
    Counters, Measurement, unix_seconds,
};
use krs_ir::{
    DefinitionSentence, Descriptor, DescriptorBundle, DescriptorPayload, OriginFrame, PackageId,
    ProvenanceRole, RangedOriginKind, Sha256Digest, SourceFileId, SourceRange, StableText,
};
use krs_k_rust::{
    Backend, CompileOptions, DefinitionCompileError, FRONTEND_CAPABILITIES, adapt_definition,
    adapt_definition_for, compile_definition_timed, diagnostic_source_map_key,
};
use sha2::{Digest, Sha256};
use std::error::Error;
use std::ffi::OsStr;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, Output};

mod result_cache;
use result_cache::ResultCache;

const ARTIFACT_MARKER: &str = "KRS artifact directory schema 1; safe to update.\n";

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
/// Returns a typed stage error. In particular, the currently pinned native
/// frontend blocker is preserved as [`CommandError::Native`].
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
    let executable = build_collector_measured(&collector_directory, &metadata, measurement)?;
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
    let read_set_path = std::env::temp_dir().join(format!(
        "krs-collector-read-set-{}-{}.json",
        std::process::id(),
        unix_seconds().to_bits()
    ));
    let _ = fs::remove_file(&read_set_path);
    let mut command = ProcessCommand::new(executable);
    command
        .current_dir(collector_directory)
        .env(COLLECTOR_READ_SET_ENV, &read_set_path);
    let sidecar = measurement.is_enabled().then(|| {
        std::env::temp_dir().join(format!(
            "krs-collector-measure-{}-{}.json",
            std::process::id(),
            unix_seconds().to_bits()
        ))
    });
    if let Some(sidecar) = &sidecar {
        let _ = fs::remove_file(sidecar);
        command.env(COLLECTOR_MEASURE_ENV, sidecar);
    }
    let spawned = sidecar.as_ref().map(|_| unix_seconds());
    let output = measurement.timings.try_span("collector.run", |_| {
        process("collector execution", &mut command)
    });
    if let (Some(sidecar), Some(spawned)) = (sidecar, spawned) {
        let document = fs::read(&sidecar)
            .ok()
            .and_then(|bytes| serde_json::from_slice::<CollectorMeasureDocument>(&bytes).ok());
        let _ = fs::remove_file(&sidecar);
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
    let output = output?;
    let bytes = fs::read(&read_set_path).map_err(|source| CommandError::Io {
        path: read_set_path.clone(),
        source,
    });
    let _ = fs::remove_file(&read_set_path);
    let read_set = serde_json::from_slice(&bytes?).map_err(CommandError::Serialization)?;
    Ok((output.stdout, read_set))
}

fn build_collector_measured(
    collector_directory: &Path,
    metadata: &CargoMetadata,
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
        .try_span("collector.build", |_| build_collector(&mut build, metadata))
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
    lower_descriptor_bundle(bundle).map_err(|error| {
        if let DescriptorLoweringError::OverlappingRules { first, second } = &error
            && let Some(descriptor) = bundle
                .descriptors
                .iter()
                .find(|descriptor| &descriptor.id == second.as_ref())
            && let Some(head_origin) = descriptor.provenance.origins().iter().find(|node| {
                node.key.role() == ProvenanceRole::RuleLeftApplicationHead
                    && node.key.ordinal() == 0
            })
            && let Some(range) = exact_authored_range_from_origin(&head_origin.origin)
        {
            let mut diagnostic = DiagnosticEnvelope::error(
                DiagnosticStage::Analysis,
                "overlapping-rule-heads",
                error.to_string(),
                range,
            );
            diagnostic.notes = vec![
                format!("first rule: {first}"),
                format!("second rule: {second}"),
            ];
            return CommandError::Diagnostics(vec![diagnostic]);
        }
        CommandError::DescriptorLowering(error)
    })
}

fn lower_definition(
    semantic: &krs_ir::SemanticTheory,
) -> Result<krs_compiler::LoweredDefinition, CommandError> {
    lower_semantic_theory(semantic).map_err(|error| {
        if let LoweringError::NameCollision {
            namespace,
            value: _,
            second_origin,
            ..
        } = &error
            && let Some(range) = exact_authored_range_from_origin(second_origin)
        {
            let code = if *namespace == "emitted symbol" {
                "symbol-name-collision"
            } else {
                "name-collision"
            };
            return CommandError::Diagnostics(vec![DiagnosticEnvelope::error(
                DiagnosticStage::Analysis,
                code,
                error.to_string(),
                range,
            )]);
        }
        CommandError::Lowering(error)
    })
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

#[allow(clippy::too_many_lines)] // Fail-closed source selection and rendering form one boundary.
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
    let head_rules = prepared
        .bundle
        .descriptors
        .iter()
        .filter(|descriptor| {
            descriptor.id.package() == &package
                && matches!(descriptor.payload, DescriptorPayload::HeadRule(_))
        })
        .collect::<Vec<_>>();
    let candidates = if head_rules.is_empty() {
        prepared
            .bundle
            .descriptors
            .iter()
            .filter(|descriptor| descriptor.id.package() == &package)
            .collect::<Vec<_>>()
    } else {
        head_rules
    };
    let mut sources =
        std::collections::BTreeMap::<SourceFileId, std::collections::BTreeSet<Vec<String>>>::new();
    for descriptor in candidates {
        if let Some(file) = authored_source_file(descriptor) {
            sources
                .entry(file.clone())
                .or_default()
                .insert(descriptor.id.module_path().to_vec());
        }
    }
    if sources.len() != 1 {
        let paths = sources
            .keys()
            .map(SourceFileId::package_relative_path)
            .collect::<Vec<_>>()
            .join(", ");
        return Err(CommandError::InvalidRequest(format!(
            "expand requires one readable root source file; found {}{}",
            sources.len(),
            if paths.is_empty() {
                String::new()
            } else {
                format!(": {paths}")
            }
        )));
    }
    let (file, module_paths) = sources
        .first_key_value()
        .expect("the source count was checked above");
    if module_paths.len() != 1 {
        let paths = module_paths
            .iter()
            .map(|path| path.join("::"))
            .collect::<Vec<_>>()
            .join(", ");
        return Err(CommandError::InvalidRequest(format!(
            "expand source `{}` contains descriptors from multiple Rust modules: {paths}",
            file.package_relative_path()
        )));
    }
    let module_path = module_paths
        .first()
        .expect("the selected source has at least one descriptor module");
    let manifest_directory = root.manifest_path.parent().ok_or_else(|| {
        CommandError::InvalidMetadata(format!(
            "manifest has no parent directory: `{}`",
            root.manifest_path.display()
        ))
    })?;
    let source_path = manifest_directory.join(file.package_relative_path());
    let source = fs::read(&source_path).map_err(|source| CommandError::Io {
        path: source_path.clone(),
        source,
    })?;
    let digest = Sha256::digest(&source);
    if format!("{digest:x}") != file.content_sha256().as_str() {
        return Err(CommandError::InvalidRequest(format!(
            "expand source changed after collection: `{}`",
            source_path.display()
        )));
    }
    let source = std::str::from_utf8(&source).map_err(|error| {
        CommandError::InvalidRequest(format!(
            "expand source is not UTF-8: `{}`: {error}",
            source_path.display()
        ))
    })?;
    let expanded = expand_reference_source(
        source,
        &root.manifest_path,
        &package,
        module_path,
        &prepared.bundle,
        &prepared.semantic,
    )?;
    Ok(CommandOutcome {
        stdout: expanded.into_bytes(),
    })
}

fn authored_source_file(descriptor: &Descriptor) -> Option<&SourceFileId> {
    descriptor
        .origin()
        .frames()
        .iter()
        .find_map(|frame| match frame {
            OriginFrame::Ranged {
                kind: RangedOriginKind::Authored,
                range,
                ..
            } => Some(&range.file),
            OriginFrame::Ranged { .. } | OriginFrame::Transformation { .. } => None,
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
        (
            "descriptor-bundle.json".to_owned(),
            descriptor_bundle.into_bytes(),
        ),
        ("semantic-ir.json".to_owned(), semantic_ir.into_bytes()),
        ("definition-ir.json".to_owned(), definition_ir.into_bytes()),
        (
            DEFINITION_ARTIFACT.to_owned(),
            emitted.source().as_bytes().to_vec(),
        ),
    ];
    if let Some(spec) = emitted.spec() {
        artifacts.push((SPEC_ARTIFACT.to_owned(), spec.source().as_bytes().to_vec()));
    }
    artifacts.push(("symbols.json".to_owned(), symbols.into_bytes()));
    artifacts.push(("sources.json".to_owned(), sources.into_bytes()));
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
    let spec = if emitted.spec().is_some() {
        format!(" {SPEC_ARTIFACT},")
    } else {
        String::new()
    };
    Ok(CommandExecution {
        outcome: CommandOutcome {
            stdout: format!(
                "emitted descriptor-bundle.json, semantic-ir.json, definition-ir.json, \
                 {DEFINITION_ARTIFACT},{spec} symbols.json, sources.json\n"
            )
            .into_bytes(),
        },
        artifacts,
    })
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
            let marker = path.join(".krs-artifacts");
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
    write_output_if_different(path, ".krs-artifacts", ARTIFACT_MARKER.as_bytes())
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
        compiler_manifest: unique_manifest(&metadata, "krs-compiler")?,
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
    metadata: &CargoMetadata,
) -> Result<PathBuf, CommandError> {
    let output = command
        .output()
        .map_err(|source| CommandError::ProcessStart {
            stage: "collector build",
            source,
        })?;
    if !output.status.success() {
        let diagnostics = rust_diagnostics(&output.stdout, metadata);
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

fn rust_diagnostics(stdout: &[u8], metadata: &CargoMetadata) -> Vec<DiagnosticEnvelope> {
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
        for span in diagnostic.spans.iter().filter(|span| span.is_primary) {
            if let Some(range) = rust_source_range(metadata, manifest, span) {
                diagnostics.push(DiagnosticEnvelope::error(
                    DiagnosticStage::RustExpansion,
                    diagnostic.code.as_ref().map_or_else(
                        || "rust-expansion-error".to_owned(),
                        |code| code.code.clone(),
                    ),
                    diagnostic.message.clone(),
                    range,
                ));
            }
        }
    }
    diagnostics.sort_by(|left, right| {
        (&left.code, &left.authored_range).cmp(&(&right.code, &right.authored_range))
    });
    diagnostics.dedup();
    diagnostics
}

fn rust_source_range(
    metadata: &CargoMetadata,
    manifest: &str,
    span: &RustDiagnosticSpan,
) -> Option<SourceRange> {
    let package = metadata
        .packages
        .iter()
        .find(|package| package.manifest_path == manifest)?;
    package.metadata.get("krs")?.get("definitions")?;
    let manifest_directory = Path::new(manifest).parent()?;
    let path = Path::new(&span.file_name);
    let path = if path.is_absolute() {
        path.to_path_buf()
    } else {
        manifest_directory.join(path)
    };
    let source = fs::read(&path).ok()?;
    if usize::try_from(span.byte_end).ok()? > source.len() {
        return None;
    }
    let relative = path.strip_prefix(manifest_directory).ok()?;
    let relative = relative.to_str()?.replace('\\', "/");
    let namespace = package
        .metadata
        .get("krs")
        .and_then(|value| value.get("k-namespace"))
        .and_then(serde_json::Value::as_str)
        .unwrap_or(&package.name);
    let package_id = PackageId::new(
        namespace,
        &package.name,
        &package.version,
        package.source.as_deref().unwrap_or("workspace"),
    )
    .ok()?;
    let digest = Sha256::digest(&source);
    let file = SourceFileId::new(
        package_id,
        relative,
        Sha256Digest::new(format!("{digest:x}")).ok()?,
    )
    .ok()?;
    SourceRange::new(file, span.byte_start, span.byte_end).ok()
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
    /// Artifact filesystem operation failed.
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
            Self::DescriptorProtocol(error) | Self::Serialization(error) => Some(error),
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
    /// Returns structured diagnostics when this failure crossed a diagnostic boundary.
    #[must_use]
    pub fn diagnostics(&self) -> Option<&[DiagnosticEnvelope]> {
        match self {
            Self::Diagnostics(diagnostics) => Some(diagnostics),
            _ => None,
        }
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
