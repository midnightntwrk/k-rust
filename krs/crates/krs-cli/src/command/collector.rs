use super::CommandError;
use super::failed_items;
use crate::{
    CargoMetadata, CollectorPlan, CollectorRuntime, DiagnosticEnvelope, DiagnosticStage,
    GeneratedCollector, diagnostic_envelope, metadata::cargo_metadata,
};
use krs_diagnostic::{Code, Diagnostic, Location, codes, untag_rustc_message};
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
    target: Option<&Path>,
    measurement: &mut Measurement,
) -> Result<PathBuf, CommandError> {
    // Cargo discovers hierarchical config from its working directory, not from
    // an arbitrary `--manifest-path`; this activates the generated cfg rustflags.
    let mut build = crate::cargo::command_in(target);
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
    #[serde(default)]
    children: Vec<RustDiagnosticChild>,
    rendered: Option<String>,
}

#[derive(serde::Deserialize)]
struct RustDiagnosticCode {
    code: String,
}

/// A note, help, or suggestion that rustc attaches to a diagnostic.
#[derive(serde::Deserialize)]
struct RustDiagnosticChild {
    level: String,
    message: String,
    #[serde(default)]
    spans: Vec<RustDiagnosticSpan>,
}

#[derive(serde::Deserialize)]
struct RustDiagnosticSpan {
    file_name: String,
    byte_start: u32,
    byte_end: u32,
    is_primary: bool,
    #[serde(default)]
    line_start: u32,
    #[serde(default)]
    column_start: u32,
    #[serde(default)]
    suggested_replacement: Option<String>,
    /// Present when the span lies in macro-generated code rather than in tokens the author wrote.
    #[serde(default)]
    expansion: Option<serde::de::IgnoredAny>,
}

/// The rustc lint whose verdict a failed KRS item can falsify.
const UNUSED_IMPORTS: &str = "unused_imports";

fn rust_diagnostics(
    stdout: &[u8],
    plan: &CollectorPlan,
) -> Result<Vec<DiagnosticEnvelope>, CommandError> {
    let mut errors = Vec::new();
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
        let Some(manifest) = message.manifest_path else {
            continue;
        };
        errors.push((manifest, diagnostic));
    }
    let mut failed = FailedItems::new(plan, &errors);
    let mut diagnostics = Vec::new();
    for (manifest, diagnostic) in &errors {
        let manifest = manifest.as_str();
        if diagnostic
            .code
            .as_ref()
            .is_some_and(|code| code.code == UNUSED_IMPORTS)
        {
            relay_unused_imports(plan, manifest, diagnostic, &mut failed, &mut diagnostics)?;
            continue;
        }
        // A KRS proc macro's `compile_error!`, or a facade trait's
        // `on_unimplemented` message, carries its registered code in the
        // message; only KRS writes the tag, so it wins over rustc's code.
        let untagged = untag_rustc_message(&diagnostic.message);
        let tagged = untagged.is_some();
        let (code, text) = match (&diagnostic.code, untagged) {
            (_, Some((code, text))) => (code, text),
            (Some(code), None) => (
                Code::foreign(code.code.clone()),
                diagnostic.message.as_str(),
            ),
            (None, None) => (
                codes::rust_expansion::UNCODED_ERROR,
                diagnostic.message.as_str(),
            ),
        };
        let (notes, help) = rust_children(plan, manifest, &diagnostic.children, tagged, |_| true)?;
        for span in diagnostic.spans.iter().filter(|span| span.is_primary) {
            if let Some(range) = rust_source_range(plan, manifest, span)? {
                let mut relayed =
                    Diagnostic::error(code.clone(), text.to_owned(), Location::Source(range));
                relayed.notes.clone_from(&notes);
                relayed.help.clone_from(&help);
                diagnostics.push(diagnostic_envelope(
                    relayed,
                    DiagnosticStage::RustExpansion,
                    None,
                ));
            }
        }
    }
    diagnostics.sort_by(|left, right| {
        (&left.code, &left.authored_range).cmp(&(&right.code, &right.authored_range))
    });
    diagnostics.dedup();
    Ok(diagnostics)
}

/// Relays an `unused_imports` error one import at a time, leaving out each
/// import that a failed KRS item in the import's module names.
///
/// The lint judges the expanded crate, which lacks a failed item's code, so
/// its verdict about an import that item names is a consequence of the KRS
/// error, not a second fact: once the item compiles the use exists, and if the
/// fix removes it rustc reports the import then. An import that no failed item
/// names, a glob, and an underscore import are reported as rustc reports them.
/// Each kept import is relayed with its own text (rustc's message lists every
/// name of the `use` item, once per name), and with only the suggested edits
/// that remove it and no import a failed item names.
fn relay_unused_imports(
    plan: &CollectorPlan,
    manifest: &str,
    diagnostic: &RustDiagnostic,
    failed: &mut FailedItems,
    diagnostics: &mut Vec<DiagnosticEnvelope>,
) -> Result<(), CommandError> {
    let code = Code::foreign(UNUSED_IMPORTS.to_owned());
    let primary = diagnostic
        .spans
        .iter()
        .filter(|span| span.is_primary)
        .collect::<Vec<_>>();
    let mut texts = Vec::with_capacity(primary.len());
    let mut credited = Vec::with_capacity(primary.len());
    for span in &primary {
        let text = match facet_source(plan, manifest, &span.file_name)? {
            Some(source) => Some(source.text(span)?),
            None => None,
        };
        let names = text.as_deref().and_then(failed_items::imported_name);
        credited.push(names.is_some_and(|name| failed.credit(manifest, span, name)));
        texts.push(text);
    }
    for ((span, text), dropped) in primary.iter().zip(&texts).zip(&credited) {
        if *dropped {
            continue;
        }
        let Some(range) = rust_source_range(plan, manifest, span)? else {
            continue;
        };
        let covers = |edit: &RustDiagnosticSpan, import: &RustDiagnosticSpan| {
            edit.file_name == import.file_name
                && edit.byte_start <= import.byte_start
                && import.byte_end <= edit.byte_end
        };
        let (notes, help) = rust_children(plan, manifest, &diagnostic.children, false, |edit| {
            covers(edit, span)
                && !primary
                    .iter()
                    .zip(&credited)
                    .any(|(other, credited)| *credited && covers(edit, other))
        })?;
        let message = text.as_deref().map_or_else(
            || diagnostic.message.clone(),
            |text| format!("unused import: `{text}`"),
        );
        let mut relayed = Diagnostic::error(code.clone(), message, Location::Source(range));
        relayed.notes = notes;
        relayed.help = help;
        diagnostics.push(diagnostic_envelope(
            relayed,
            DiagnosticStage::RustExpansion,
            None,
        ));
    }
    Ok(())
}

/// The KRS items that failed in one collector build: for each relayed error a
/// KRS proc macro tagged, the innermost item containing its primary span.
/// Computed on first use, since only an unused-import error needs it.
struct FailedItems<'a> {
    plan: &'a CollectorPlan,
    errors: &'a [(String, RustDiagnostic)],
    /// The failed items by manifest and rustc file name, once computed.
    items: Option<Vec<(String, String, failed_items::FailedItem)>>,
    /// Parsed sources by manifest and rustc file name; `None` when unreadable.
    sources: std::collections::BTreeMap<(String, String), Option<failed_items::ParsedSource>>,
}

impl<'a> FailedItems<'a> {
    const fn new(plan: &'a CollectorPlan, errors: &'a [(String, RustDiagnostic)]) -> Self {
        Self {
            plan,
            errors,
            items: None,
            sources: std::collections::BTreeMap::new(),
        }
    }

    /// The parsed source rustc names `file_name` in `manifest`'s package; a
    /// file outside the selected packages, unreadable, or not parsable by `syn`
    /// has none, so nothing in it is credited.
    fn source(&mut self, manifest: &str, file_name: &str) -> Option<&failed_items::ParsedSource> {
        let plan = self.plan;
        self.sources
            .entry((manifest.to_owned(), file_name.to_owned()))
            .or_insert_with(|| {
                let source = facet_source(plan, manifest, file_name).ok()??;
                failed_items::ParsedSource::parse(&source.bytes)
            })
            .as_ref()
    }

    /// Whether a failed item in the file and the innermost inline module of
    /// the module-level `use` at `span` names `name`.
    fn credit(&mut self, manifest: &str, span: &RustDiagnosticSpan, name: &str) -> bool {
        if self.items.is_none() {
            let mut items = Vec::new();
            for (manifest, diagnostic) in self.errors {
                let krs =
                    diagnostic.code.is_none() && untag_rustc_message(&diagnostic.message).is_some();
                if !krs {
                    continue;
                }
                for span in diagnostic.spans.iter().filter(|span| span.is_primary) {
                    let item = self
                        .source(manifest, &span.file_name)
                        .and_then(|source| source.failed_item(span.byte_start as usize));
                    if let Some(item) = item {
                        items.push((manifest.clone(), span.file_name.clone(), item));
                    }
                }
            }
            self.items = Some(items);
        }
        let Some(modules) = self
            .source(manifest, &span.file_name)
            .and_then(|source| source.use_module(span.byte_start as usize))
        else {
            return false;
        };
        self.items
            .iter()
            .flatten()
            .any(|(item_manifest, file, item)| {
                item_manifest == manifest
                    && *file == span.file_name
                    && item.modules == modules
                    && item.identifiers.contains(name)
            })
    }
}

/// Translates rustc's children of one diagnostic into KRS notes and help, in rustc's order.
///
/// A suggested edit is relayed only when `keep_edit` accepts its span; a
/// suggestion whose every edit is left out is omitted.
///
/// For a `tagged` diagnostic, whose message KRS wrote, a child that names a
/// hidden generated item (`__krs…`, `__Krs…`) describes the mechanism that
/// raised it, not the author's code, so it is omitted. An untagged rustc error
/// keeps such a child, which may be the only hint of what rustc tried.
///
/// A child whose every span lies in macro-generated code describes tokens the author did not
/// write, such as a KRS expansion's hidden helper items, so it is omitted. A suggested
/// replacement is relayed as the edit it makes to the authored source; one that would edit
/// generated code or a file outside the selected packages is not an edit the author can make.
fn rust_children(
    plan: &CollectorPlan,
    manifest: &str,
    children: &[RustDiagnosticChild],
    tagged: bool,
    keep_edit: impl Fn(&RustDiagnosticSpan) -> bool,
) -> Result<(Vec<String>, Vec<String>), CommandError> {
    let mut notes = Vec::new();
    let mut help = Vec::new();
    for child in children {
        if !child.spans.is_empty() && child.spans.iter().all(|span| span.expansion.is_some()) {
            continue;
        }
        if tagged && names_hidden_item(&child.message) {
            continue;
        }
        let mut edits = Vec::new();
        let mut location = None;
        let mut left_out = false;
        for span in child.spans.iter().filter(|span| span.expansion.is_none()) {
            if span.suggested_replacement.is_some() && !keep_edit(span) {
                left_out = true;
                continue;
            }
            let Some(source) = facet_source(plan, manifest, &span.file_name)? else {
                continue;
            };
            let original = source.text(span)?;
            let at = format!(
                "{}:{}:{}",
                source.relative, span.line_start, span.column_start
            );
            match span.suggested_replacement.as_deref() {
                Some("") => edits.push(format!("remove `{original}` at {at}")),
                Some(replacement) if original.is_empty() => {
                    edits.push(format!("insert `{replacement}` at {at}"));
                }
                Some(replacement) => {
                    edits.push(format!("replace `{original}` with `{replacement}` at {at}"));
                }
                None => {
                    location.get_or_insert(at);
                }
            }
        }
        if left_out && edits.is_empty() && location.is_none() {
            // Every edit this suggestion made was left out.
            continue;
        }
        let text = match (edits.is_empty(), location) {
            (false, _) => format!("{}: {}", child.message, edits.join("; ")),
            (true, Some(at)) => format!("{} ({at})", child.message),
            (true, None) => child.message.clone(),
        };
        match child.level.as_str() {
            "help" => help.push(text),
            "note" => notes.push(text),
            level => notes.push(format!("{level}: {text}")),
        }
    }
    Ok((notes, help))
}

/// Whether a rustc message names an item KRS generates and hides from authors.
fn names_hidden_item(message: &str) -> bool {
    message.contains("__krs") || message.contains("__Krs")
}

/// A source file of a selected package, read at the revision rustc diagnosed.
struct FacetSource<'a> {
    facet: &'a crate::plan::ResolvedFacet,
    relative: String,
    bytes: Vec<u8>,
}

impl FacetSource<'_> {
    /// The authored text a span covers.
    fn text(&self, span: &RustDiagnosticSpan) -> Result<String, CommandError> {
        self.bytes
            .get(span.byte_start as usize..span.byte_end as usize)
            .map(|bytes| String::from_utf8_lossy(bytes).into_owned())
            .ok_or_else(|| {
                CommandError::InvalidMetadata(
                    "Rust diagnostic range exceeds its source revision".to_owned(),
                )
            })
    }
}

/// The selected package source a rustc span names, or `None` outside the selected packages.
fn facet_source<'a>(
    plan: &'a CollectorPlan,
    manifest: &str,
    file_name: &str,
) -> Result<Option<FacetSource<'a>>, CommandError> {
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
    let path = Path::new(file_name);
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
    let bytes = fs::read(&path).map_err(|source| CommandError::Io {
        path: path.clone(),
        source,
    })?;
    Ok(Some(FacetSource {
        facet,
        relative,
        bytes,
    }))
}

fn rust_source_range(
    plan: &CollectorPlan,
    manifest: &str,
    span: &RustDiagnosticSpan,
) -> Result<Option<SourceRange>, CommandError> {
    let Some(source) = facet_source(plan, manifest, &span.file_name)? else {
        return Ok(None);
    };
    if span.byte_end as usize > source.bytes.len() {
        return Err(CommandError::InvalidMetadata(
            "Rust diagnostic range exceeds its source revision".to_owned(),
        ));
    }
    let facet = source.facet;
    let package = PackageId::new(
        &facet.k_namespace,
        &facet.package_name,
        &facet.package_version,
        &facet.cargo_source,
    )
    .map_err(|error| CommandError::InvalidMetadata(error.to_string()))?;
    let file = SourceFileId::new(
        package,
        source.relative,
        Sha256Digest::from_bytes(Sha256::digest(&source.bytes).into()),
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

    /// Plans the one-package `language` definition whose `src/lib.rs` is `source`.
    fn language_plan(source: &str) -> (tempfile::TempDir, PathBuf, CollectorPlan) {
        let directory = tempfile::tempdir().unwrap();
        let manifest = directory.path().join("Cargo.toml");
        fs::create_dir(directory.path().join("src")).unwrap();
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
        (directory, manifest, plan)
    }

    #[test]
    fn rust_spans_use_validated_facet_identity_and_do_not_hide_selected_source_errors() {
        let source = "pub trait Expr {}\n";
        let (_directory, manifest, plan) = language_plan(source);
        let mut span = RustDiagnosticSpan {
            file_name: "src/lib.rs".to_owned(),
            byte_start: 10,
            byte_end: 14,
            is_primary: true,
            line_start: 1,
            column_start: 11,
            suggested_replacement: None,
            expansion: None,
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
    fn tagged_proc_macro_errors_recover_their_registered_code() {
        let (_directory, manifest, plan) = language_plan("pub trait Expr {}\n");
        let message = |text: &str, code: Option<&str>| {
            serde_json::json!({
                "reason": "compiler-message",
                "manifest_path": manifest,
                "message": {
                    "level": "error",
                    "message": text,
                    "code": code.map(|code| serde_json::json!({ "code": code })),
                    "spans": [{
                        "file_name": "src/lib.rs", "byte_start": 10, "byte_end": 14,
                        "is_primary": true,
                    }],
                    "rendered": null,
                },
            })
            .to_string()
        };
        let stdout = [
            message("[krs::syntax::invalid-color] bad colours", None),
            message("[krs::syntax::no-such-code] kept", None),
            message("mismatched types", Some("E0308")),
        ]
        .join("\n");
        let reported: Vec<_> = rust_diagnostics(stdout.as_bytes(), &plan)
            .unwrap()
            .into_iter()
            .map(|envelope| (envelope.code, envelope.message))
            .collect();
        assert_eq!(
            reported,
            [
                ("E0308".to_owned(), "mismatched types".to_owned()),
                (
                    "krs::rust-expansion::uncoded-error".to_owned(),
                    "[krs::syntax::no-such-code] kept".to_owned()
                ),
                (
                    "krs::syntax::invalid-color".to_owned(),
                    "bad colours".to_owned()
                ),
            ]
        );
    }

    #[test]
    fn rustc_children_are_relayed_as_notes_and_help_with_authored_edits() {
        let source = "pub fn plain() {\n    let _ = Register::A();\n}\n";
        let (_directory, manifest, plan) = language_plan(source);
        let call = source.find("Register::A()").unwrap();
        let parentheses = call + "Register::A".len();
        let line = source.find('\n').unwrap() + 1;
        let span = |start: usize, end: usize, primary: bool| {
            serde_json::json!({
                "file_name": "src/lib.rs",
                "byte_start": start, "byte_end": end,
                "line_start": 2, "column_start": start.saturating_sub(line) + 1,
                "is_primary": primary, "expansion": null,
            })
        };
        let mut removal = span(parentheses, parentheses + 2, true);
        removal["suggested_replacement"] = serde_json::json!("");
        let mut generated = span(0, 3, true);
        generated["expansion"] = serde_json::json!({ "macro_decl_name": "#[k::constructors]" });
        let stdout = serde_json::json!({
            "reason": "compiler-message",
            "manifest_path": manifest,
            "message": {
                "level": "error",
                "message": "expected function, found enum variant `Register::A`",
                "code": { "code": "E0618" },
                "spans": [span(call, parentheses, true)],
                "children": [
                    {
                        "level": "note",
                        "message": "enum variant `Register::A` defined here",
                        "spans": [span(call, call + 8, true)],
                    },
                    {
                        "level": "help",
                        "message": "`Register::A` is a unit enum variant, and does not take parentheses to be constructed",
                        "spans": [removal],
                    },
                    {
                        "level": "help",
                        "message": "there is an associated function `__krs_hidden` with a similar name",
                        "spans": [generated],
                    },
                    { "level": "note", "message": "spanless detail", "spans": [] },
                ],
                "rendered": null,
            },
        })
        .to_string();
        let [envelope] = rust_diagnostics(stdout.as_bytes(), &plan)
            .unwrap()
            .try_into()
            .unwrap();
        assert_eq!(envelope.code, "E0618");
        assert_eq!(
            envelope.message,
            "expected function, found enum variant `Register::A`"
        );
        assert_eq!(
            envelope.notes,
            [
                "enum variant `Register::A` defined here (src/lib.rs:2:13)",
                "spanless detail",
            ]
        );
        assert_eq!(
            envelope.help,
            [
                "`Register::A` is a unit enum variant, and does not take parentheses to be constructed: remove `()` at src/lib.rs:2:24"
            ]
        );
    }

    #[test]
    fn unused_imports_a_failed_krs_item_names_are_left_out_and_the_rest_relayed_per_name() {
        let source = "use k::builtin::{list, map, set};\nuse Cmd::*;\n\nk::rules! {\n    go: Go() => list::item(set);\n}\n";
        let (_directory, manifest, plan) = language_plan(source);
        let at = |text: &str| source.find(text).unwrap();
        let span = |start: usize, end: usize, primary: bool| {
            serde_json::json!({
                "file_name": "src/lib.rs",
                "byte_start": start, "byte_end": end,
                "line_start": 1, "column_start": start + 1,
                "is_primary": primary, "expansion": null,
            })
        };
        let removal = |start: usize, end: usize| {
            let mut removal = span(start, end, true);
            removal["suggested_replacement"] = serde_json::json!("");
            removal
        };
        let message = |text: &str, code: Option<&str>, spans: serde_json::Value, children| {
            serde_json::json!({
                "reason": "compiler-message",
                "manifest_path": manifest,
                "message": {
                    "level": "error",
                    "message": text,
                    "code": code.map(|code| serde_json::json!({ "code": code })),
                    "spans": spans,
                    "children": children,
                    "rendered": null,
                },
            })
            .to_string()
        };
        let (list, map, set) = (at("list,"), at("map,"), at("set}"));
        let stdout = [
            message(
                "[krs::syntax::rust-syntax] expected an equation",
                None,
                serde_json::json!([span(at("go:"), at("go:") + 2, true)]),
                serde_json::json!([]),
            ),
            // `list` is named by the failed rule; `set` only as its binder.
            message(
                "unused imports: `list`, `map`, and `set`",
                Some("unused_imports"),
                serde_json::json!([
                    span(list, list + 4, true),
                    span(map, map + 3, true),
                    span(set, set + 3, true),
                ]),
                serde_json::json!([
                    { "level": "note", "message": "`-D unused-imports` implied by `-D warnings`", "spans": [] },
                    {
                        "level": "help",
                        "message": "remove the unused imports",
                        "spans": [removal(list, map), removal(map - 2, map + 3), removal(set - 2, set + 3)],
                    },
                ]),
            ),
            message(
                "unused import: `Cmd::*`",
                Some("unused_imports"),
                serde_json::json!([span(at("Cmd::*"), at("Cmd::*") + 6, true)]),
                serde_json::json!([]),
            ),
        ]
        .join("\n");
        let reported: Vec<_> = rust_diagnostics(stdout.as_bytes(), &plan)
            .unwrap()
            .into_iter()
            .map(|envelope| (envelope.code, envelope.message, envelope.help))
            .collect();
        assert_eq!(
            reported,
            [
                (
                    "krs::syntax::rust-syntax".to_owned(),
                    "expected an equation".to_owned(),
                    vec![],
                ),
                (
                    "unused_imports".to_owned(),
                    "unused import: `map`".to_owned(),
                    vec!["remove the unused imports: remove `, map` at src/lib.rs:1:22".to_owned()],
                ),
                (
                    "unused_imports".to_owned(),
                    "unused import: `set`".to_owned(),
                    vec!["remove the unused imports: remove `, set` at src/lib.rs:1:27".to_owned()],
                ),
                // A glob's names are not known, so it is never left out.
                (
                    "unused_imports".to_owned(),
                    "unused import: `Cmd::*`".to_owned(),
                    vec![],
                ),
            ]
        );
    }

    #[test]
    fn a_tagged_rustc_error_takes_the_krs_code_and_drops_hidden_item_children() {
        let source = "pub struct Machine {}\n";
        let (_directory, manifest, plan) = language_plan(source);
        let name = source.find("Machine").unwrap();
        let message = |text: &str| {
            serde_json::json!({
                "reason": "compiler-message",
                "manifest_path": manifest,
                "message": {
                    "level": "error",
                    "message": text,
                    "code": { "code": "E0277" },
                    "spans": [{
                        "file_name": "src/lib.rs", "byte_start": name, "byte_end": name + 7,
                        "line_start": 1, "column_start": name + 1, "is_primary": true,
                    }],
                    "children": [
                        { "level": "help", "message": "the trait `krs::configuration::__KrsInitializer` is not implemented for `Machine`", "spans": [] },
                        { "level": "note", "message": "an initializer gives each cell its initial value", "spans": [] },
                        { "level": "note", "message": "required by a bound in `__KrsInitializerFallback::__krs_initializer_payload`", "spans": [] },
                    ],
                    "rendered": null,
                },
            })
            .to_string()
        };
        let stdout = [
            message("[krs::expand::missing-initializer] configuration `Machine` has no `#[k::init]` initializer"),
            message("the trait bound `Machine: Rule` is not satisfied"),
        ]
        .join("\n");
        let reported: Vec<_> = rust_diagnostics(stdout.as_bytes(), &plan)
            .unwrap()
            .into_iter()
            .map(|envelope| {
                (
                    envelope.code,
                    envelope.message,
                    envelope.notes,
                    envelope.help,
                )
            })
            .collect();
        assert_eq!(
            reported,
            [
                (
                    "E0277".to_owned(),
                    "the trait bound `Machine: Rule` is not satisfied".to_owned(),
                    vec![
                        "an initializer gives each cell its initial value".to_owned(),
                        "required by a bound in `__KrsInitializerFallback::__krs_initializer_payload`".to_owned(),
                    ],
                    vec!["the trait `krs::configuration::__KrsInitializer` is not implemented for `Machine`".to_owned()],
                ),
                (
                    "krs::expand::missing-initializer".to_owned(),
                    "configuration `Machine` has no `#[k::init]` initializer".to_owned(),
                    vec!["an initializer gives each cell its initial value".to_owned()],
                    vec![],
                ),
            ]
        );
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
            json.replace("\"schema_version\":2", "\"schema_version\":1"),
            json.replace(
                "\"schema_version\":2",
                "\"unknown\":true,\"schema_version\":2",
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
