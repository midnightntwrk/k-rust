use crate::{
    CargoMetadata, CollectorPlan, CollectorRuntime, DefinitionRequest, DiagnosticEnvelope,
    DiagnosticStage, FacetSelector, GeneratedCollector, GenerationError, KrsCfg, PlanningError,
    RegistrationMode, exact_authored_range_from_origin,
};
use krs_compiler::{
    DescriptorLoweringError, EmitError, LoweringError, ReferenceExpansionError, emit_k,
    expand_reference_source, lower_descriptor_bundle, lower_semantic_theory,
};
use krs_ir::{
    Descriptor, DescriptorBundle, DescriptorPayload, OriginFrame, PackageId, RangedOriginKind,
    Sha256Digest, SourceFileId, SourceRange,
};
use krs_k_rust::{
    Backend, CompileOptions, DefinitionCompileError, FRONTEND_CAPABILITIES, FrontendDiagnostic,
    adapt_definition, compile_definition,
};
use sha2::{Digest, Sha256};
use std::error::Error;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const ARTIFACT_MARKER: &str = "KRS artifact directory schema 1; safe to update.\n";

/// One production KRS command.
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

/// Explicit input to one production command execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandRequest {
    /// Command to execute.
    pub command: CommandKind,
    /// Cargo manifest used for metadata and Rust checking.
    pub manifest_path: PathBuf,
    /// Selected root definition facet.
    pub root: FacetSelector,
    /// Explicitly composed dependency facets.
    pub dependencies: Vec<FacetSelector>,
    /// KRS-owned rustc cfg values.
    pub cfg: Vec<KrsCfg>,
    /// Native backend dialect checked or built.
    pub backend: Backend,
    /// Artifact directory for `emit-k` and `build`.
    pub output_directory: Option<PathBuf>,
    /// Descriptor registration mechanism of the generated collector.
    ///
    /// [`RegistrationMode::Explicit`] is build and parity tooling; authored
    /// packages use the default.
    pub registration: RegistrationMode,
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
    validate_request(request)?;
    let metadata = cargo_metadata(&request.manifest_path)?;
    let host_target = rustc_host_target()?;

    if request.command == CommandKind::Check {
        cargo_check(request, &host_target, &metadata)?;
    }

    let runtime = discover_runtime()?;
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
    let plan = match request.registration {
        RegistrationMode::Inventory => plan,
        RegistrationMode::Explicit => plan.with_explicit_registration()?,
    };
    let prepared = prepare(&metadata, &plan)?;

    match request.command {
        CommandKind::Check => check(&prepared, request.backend),
        CommandKind::Expand => expand(&prepared, &plan),
        CommandKind::EmitK => emit(&prepared, required_output(request)?),
        CommandKind::Build => build(&prepared, request.backend, required_output(request)?),
    }
}

fn validate_request(request: &CommandRequest) -> Result<(), CommandError> {
    if request.manifest_path.file_name() != Some(OsStr::new("Cargo.toml")) {
        return Err(CommandError::InvalidRequest(format!(
            "manifest path must end in Cargo.toml: `{}`",
            request.manifest_path.display()
        )));
    }
    match (request.command, &request.output_directory) {
        (CommandKind::EmitK | CommandKind::Build, None) => Err(CommandError::InvalidRequest(
            "emit-k and build require an output directory".to_owned(),
        )),
        (CommandKind::Check | CommandKind::Expand, Some(_)) => Err(CommandError::InvalidRequest(
            "check and expand do not accept an output directory".to_owned(),
        )),
        _ => Ok(()),
    }
}

fn required_output(request: &CommandRequest) -> Result<&Path, CommandError> {
    request.output_directory.as_deref().ok_or_else(|| {
        CommandError::InvalidRequest("command requires an output directory".to_owned())
    })
}

fn prepare(
    metadata: &CargoMetadata,
    plan: &CollectorPlan,
) -> Result<PreparedDefinition, CommandError> {
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
    // Cargo discovers hierarchical config from its working directory, not from
    // an arbitrary `--manifest-path`; this activates the generated cfg rustflags.
    let output = cargo(
        "collector execution",
        Command::new("cargo")
            .current_dir(&collector_directory)
            .args(["run", "--quiet", "--manifest-path"])
            .arg(collector_directory.join("Cargo.toml")),
    )?;
    let bundle: DescriptorBundle =
        serde_json::from_slice(&output.stdout).map_err(CommandError::DescriptorProtocol)?;
    let semantic = lower_descriptor_bundle(&bundle).map_err(|error| {
        if let DescriptorLoweringError::OverlappingRules { first, second } = &error
            && let Some(descriptor) = bundle
                .descriptors
                .iter()
                .find(|descriptor| &descriptor.id == second.as_ref())
            && let Some(head_origin) = descriptor.provenance.origins().iter().find(|node| {
                node.key.role() == "rule_left_application_head" && node.key.ordinal() == 0
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
                format!("first rule: {first:?}"),
                format!("second rule: {second:?}"),
            ];
            return CommandError::Diagnostics(vec![diagnostic]);
        }
        CommandError::DescriptorLowering(error)
    })?;
    let lowered = lower_semantic_theory(&semantic).map_err(|error| {
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
    })?;
    Ok(PreparedDefinition {
        bundle,
        semantic,
        lowered,
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
        .facets
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

fn emit(prepared: &PreparedDefinition, output: &Path) -> Result<CommandOutcome, CommandError> {
    let descriptor_bundle = prepared.bundle.to_canonical_json()?;
    let semantic_ir = prepared.semantic.to_canonical_json()?;
    let definition_ir = prepared.lowered.definition().to_canonical_json()?;
    let emitted = emit_k(&prepared.lowered)?;
    let symbols = emitted.symbol_map().to_canonical_json()?;
    let sources = emitted.source_map().to_canonical_json()?;
    prepare_output(output)?;
    write_output(
        output,
        "descriptor-bundle.json",
        descriptor_bundle.as_bytes(),
    )?;
    write_output(output, "semantic-ir.json", semantic_ir.as_bytes())?;
    write_output(output, "definition-ir.json", definition_ir.as_bytes())?;
    write_output(output, "definition.k", emitted.source().as_bytes())?;
    write_output(output, "symbols.json", symbols.as_bytes())?;
    write_output(output, "sources.json", sources.as_bytes())?;
    Ok(CommandOutcome {
        stdout: b"emitted descriptor-bundle.json, semantic-ir.json, definition-ir.json, definition.k, symbols.json, sources.json\n".to_vec(),
    })
}

fn build(
    prepared: &PreparedDefinition,
    backend: Backend,
    output: &Path,
) -> Result<CommandOutcome, CommandError> {
    let artifacts = compile_definition(
        prepared.lowered.definition(),
        CompileOptions {
            backend,
            ..CompileOptions::default()
        },
    )
    .map_err(|error| native_command_error(prepared, error))?;
    // Do not create the output directory until structured compilation has
    // succeeded. A typed capability failure therefore leaves no artifacts.
    prepare_output(output)?;
    write_output(
        output,
        "definition.kore",
        artifacts.definition_kore.as_bytes(),
    )?;
    write_output(
        output,
        "syntaxDefinition.kore",
        artifacts.syntax_definition_kore.as_bytes(),
    )?;
    write_output(output, "macros.kore", artifacts.macros_kore.as_bytes())?;
    Ok(CommandOutcome {
        stdout: b"built definition.kore, syntaxDefinition.kore, macros.kore\n".to_vec(),
    })
}

fn native_command_error(
    prepared: &PreparedDefinition,
    error: DefinitionCompileError,
) -> CommandError {
    let DefinitionCompileError::Compile { diagnostics, .. } = &error else {
        return CommandError::Native(error);
    };
    if diagnostics.is_empty() {
        return CommandError::Native(error);
    }
    let mut translated = Vec::with_capacity(diagnostics.len());
    for diagnostic in diagnostics {
        let Some(key) = native_diagnostic_key(diagnostic) else {
            return CommandError::Native(error);
        };
        let Some(mut envelope) =
            crate::translate_native_diagnostic(prepared.lowered.source_map(), &key, diagnostic)
        else {
            return CommandError::Native(error);
        };
        if diagnostic.code == "UnsupportedExistentialVariable" {
            envelope.stage = DiagnosticStage::BackendCapability;
        }
        translated.push(envelope);
    }
    translated.sort_by(|left, right| {
        (&left.code, &left.authored_range).cmp(&(&right.code, &right.authored_range))
    });
    translated.dedup();
    CommandError::Diagnostics(translated)
}

fn native_diagnostic_key(diagnostic: &FrontendDiagnostic) -> Option<krs_ir::SourceMapKey> {
    let value = diagnostic.source.as_deref()?;
    let (_, key) = value.rsplit_once("#krs-source-map=")?;
    krs_ir::SourceMapKey::new(key).ok()
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
    write_output(path, ".krs-artifacts", ARTIFACT_MARKER.as_bytes())
}

fn write_output(directory: &Path, name: &str, bytes: &[u8]) -> Result<(), CommandError> {
    let path = directory.join(name);
    fs::write(&path, bytes).map_err(|source| CommandError::Io { path, source })
}

fn cargo_metadata(manifest: &Path) -> Result<CargoMetadata, CommandError> {
    let output = cargo(
        "Cargo metadata",
        Command::new("cargo")
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
    let output = process("rustc host discovery", Command::new("rustc").arg("-vV"))?;
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

fn cargo_check(
    request: &CommandRequest,
    host_target: &str,
    metadata: &CargoMetadata,
) -> Result<(), CommandError> {
    let mut command = Command::new("cargo");
    command
        .args(["check", "--manifest-path"])
        .arg(&request.manifest_path)
        .args(["--target", host_target, "--message-format", "json"]);
    let flags = cfg_rustflags(&request.cfg);
    if !flags.is_empty() {
        let mut combined = std::env::var_os("RUSTFLAGS").unwrap_or_default();
        if !combined.is_empty() {
            combined.push(" ");
        }
        combined.push(flags);
        command.env("RUSTFLAGS", combined);
    }
    let output = command
        .output()
        .map_err(|source| CommandError::ProcessStart {
            stage: "Cargo check",
            source,
        })?;
    if output.status.success() {
        return Ok(());
    }
    let diagnostics = rust_diagnostics(&output.stdout, metadata);
    if diagnostics.is_empty() {
        Err(CommandError::ProcessFailed {
            stage: "Cargo check",
            status: output.status.code(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        })
    } else {
        Err(CommandError::Diagnostics(diagnostics))
    }
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

fn cfg_rustflags(cfg: &[KrsCfg]) -> OsString {
    let mut cfg = cfg.to_vec();
    cfg.sort();
    cfg.dedup();
    let mut output = String::new();
    for predicate in &cfg {
        if !output.is_empty() {
            output.push(' ');
        }
        output.push_str("--check-cfg=cfg(");
        output.push_str(&predicate.key);
        if let Some(value) = &predicate.value {
            output.push_str(",values(");
            output.push_str(
                &serde_json::to_string(value).expect("cfg strings are infallibly serializable"),
            );
            output.push(')');
        }
        output.push(')');
    }
    for predicate in cfg {
        output.push(' ');
        output.push_str("--cfg ");
        output.push_str(&predicate.key);
        if let Some(value) = predicate.value {
            output.push('=');
            output.push_str(
                &serde_json::to_string(&value).expect("cfg strings are infallibly serializable"),
            );
        }
    }
    output.into()
}

fn cargo(stage: &'static str, command: &mut Command) -> Result<Output, CommandError> {
    process(stage, command)
}

fn process(stage: &'static str, command: &mut Command) -> Result<Output, CommandError> {
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
    /// Command options are internally inconsistent.
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
                write!(formatter, "native backend {backend:?} is unavailable")
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
    fn cfg_flags_are_canonical() {
        let flags = cfg_rustflags(&[
            KrsCfg {
                key: "z".to_owned(),
                value: None,
            },
            KrsCfg {
                key: "backend".to_owned(),
                value: Some("llvm".to_owned()),
            },
            KrsCfg {
                key: "z".to_owned(),
                value: None,
            },
        ]);
        assert_eq!(
            flags,
            "--check-cfg=cfg(backend,values(\"llvm\")) --check-cfg=cfg(z) --cfg backend=\"llvm\" --cfg z"
        );
    }

    #[test]
    fn output_contract_is_command_specific() {
        let base = CommandRequest {
            command: CommandKind::Check,
            manifest_path: PathBuf::from("Cargo.toml"),
            root: FacetSelector {
                package: PackageSelector::Name("language".to_owned()),
                definition: "main".to_owned(),
            },
            dependencies: Vec::new(),
            cfg: Vec::new(),
            backend: Backend::Llvm,
            output_directory: None,
            registration: RegistrationMode::Inventory,
        };
        assert!(validate_request(&base).is_ok());
        let mut emit = base.clone();
        emit.command = CommandKind::EmitK;
        assert!(matches!(
            validate_request(&emit),
            Err(CommandError::InvalidRequest(_))
        ));
        emit.output_directory = Some(PathBuf::from("out"));
        assert!(validate_request(&emit).is_ok());
    }
}
