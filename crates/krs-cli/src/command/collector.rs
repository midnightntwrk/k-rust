use super::CommandError;
use crate::{
    CargoMetadata, CollectorPlan, CollectorRuntime, DiagnosticEnvelope, DiagnosticStage,
    GeneratedCollector, diagnostic_envelope, metadata::cargo_metadata,
};
use krs_diagnostic::{Code, Diagnostic, Location, codes};
use krs_ir::measure::{
    COLLECTOR_DIAGNOSTIC_ENV, COLLECTOR_MEASURE_ENV, COLLECTOR_READ_SET_ENV,
    CollectorMeasureDocument, CollectorReadSet, Measurement, unix_seconds,
};
use krs_ir::{PackageId, Sha256Digest, SourceFileId, SourceRange};
use sha2::{Digest, Sha256};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, Output};

pub(super) fn generate_collector(
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

/// Build and run the generated collector.
///
/// When measuring, the collector records its own phases in a sidecar file
/// named by [`COLLECTOR_MEASURE_ENV`]; they are nested below `collector.run`
/// after `collector.exec`, the time from spawning the executable until it
/// started collecting.
pub(super) fn run_collector(
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
        crate::process::run("collector execution", &mut command)
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

pub(super) fn build_collector_measured(
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

pub(super) fn discover_runtime() -> Result<CollectorRuntime, CommandError> {
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

pub(super) fn rustc_host_target() -> Result<String, CommandError> {
    let output = crate::process::run(
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
        // Rustc's own report stays the failure whenever its spans cannot be
        // translated into authored ranges.
        return Err(match rust_diagnostics(&output.stdout, plan) {
            Ok(diagnostics) if !diagnostics.is_empty() => CommandError::Diagnostics(diagnostics),
            _ => CommandError::ProcessFailed {
                stage: "collector build",
                status: output.status.code(),
                stderr: cargo_failure_text(&output),
            },
        });
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{DefinitionRequest, FacetSelector, PackageSelector};

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
}
