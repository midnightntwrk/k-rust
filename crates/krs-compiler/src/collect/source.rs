//! Reading authored Rust sources named by host display hints.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};

use krs_ir::measure::CollectorPathProbe;
use krs_ir::{Sha256Digest, SourceFileId};
use sha2::{Digest, Sha256};

use super::PreparedContext;
use super::invocation::{ParsedInvocation, collect_invocations};
use super::provenance::SourceLineIndex;
use super::trivia::validate_dsl_trivia;
use crate::facade::AttributeResolver;
use crate::{CollectionError, CollectionErrorKind};

static READ_FILES: Mutex<Vec<(PathBuf, String)>> = Mutex::new(Vec::new());
static PROBES: Mutex<Vec<CollectorPathProbe>> = Mutex::new(Vec::new());
static TRACK_READS: AtomicBool = AtomicBool::new(false);

pub(super) fn start_read_set() {
    READ_FILES.lock().expect("read set lock poisoned").clear();
    PROBES.lock().expect("probe lock poisoned").clear();
    TRACK_READS.store(true, Ordering::Relaxed);
}

pub(super) fn take_read_set() -> krs_ir::measure::CollectorReadSet {
    TRACK_READS.store(false, Ordering::Relaxed);
    let mut files = std::mem::take(&mut *READ_FILES.lock().expect("read set lock poisoned"));
    files.sort();
    files.dedup();
    let mut probes = std::mem::take(&mut *PROBES.lock().expect("probe lock poisoned"));
    probes.sort_by(|left, right| left.path.cmp(&right.path));
    probes.dedup();
    krs_ir::measure::CollectorReadSet { files, probes }
}

pub(crate) fn record_file(path: &Path, bytes: &[u8]) {
    if !TRACK_READS.load(Ordering::Relaxed) {
        return;
    }
    READ_FILES.lock().expect("read set lock poisoned").push((
        path.canonicalize().unwrap_or_else(|_| path.to_path_buf()),
        format!("{:x}", Sha256::digest(bytes)),
    ));
}

pub(crate) fn record_probe(path: &Path) {
    if !TRACK_READS.load(Ordering::Relaxed) {
        return;
    }
    PROBES
        .lock()
        .expect("probe lock poisoned")
        .push(CollectorPathProbe {
            path: path.to_path_buf(),
            canonical: fs::canonicalize(path).ok(),
            is_file: path.is_file(),
        });
}

#[derive(Debug)]
pub(super) struct SourceDocument {
    pub(super) text: String,
    pub(super) line_index: SourceLineIndex,
    pub(super) file: SourceFileId,
    pub(super) invocations: Vec<ParsedInvocation>,
}

pub(super) fn load_source_document(
    context: &PreparedContext,
    display_hint: &str,
) -> Result<SourceDocument, CollectionError> {
    let (canonical, package_relative) = resolve_display_source(context, display_hint)?;
    let bytes = fs::read(&canonical).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::HostIo,
            format!(
                "cannot read authored source `{}`: {error}",
                canonical.display()
            ),
        )
    })?;
    record_file(&canonical, &bytes);
    let text = String::from_utf8(bytes).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::SourceSyntax,
            format!("authored Rust source `{display_hint}` is not UTF-8: {error}"),
        )
    })?;
    let line_index = SourceLineIndex::new(&text);
    let digest = Sha256::digest(text.as_bytes());
    let digest = Sha256Digest::new(format!("{digest:x}")).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::InvalidStableIdentity,
            format!("cannot construct source content identity: {error}"),
        )
    })?;
    let file =
        SourceFileId::new(context.package.clone(), &package_relative, digest).map_err(|error| {
            CollectionError::new(
                CollectionErrorKind::InvalidDisplayFile,
                format!("invalid package-relative source `{package_relative}`: {error}"),
            )
        })?;
    let syntax = syn::parse_file(&text).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::SourceSyntax,
            format!("cannot parse authored Rust source `{display_hint}`: {error}"),
        )
    })?;
    let resolver = AttributeResolver::new(&context.facade, display_hint);
    resolver.check_items(&syntax.items)?;
    validate_dsl_trivia(&syntax, &text, &line_index, &resolver)?;
    let mut invocations = Vec::new();
    collect_invocations(&syntax.items, &resolver, &mut invocations)?;
    Ok(SourceDocument {
        text,
        line_index,
        file,
        invocations,
    })
}

fn resolve_display_source(
    context: &PreparedContext,
    display_hint: &str,
) -> Result<(PathBuf, String), CollectionError> {
    let mut lexical_candidates = BTreeSet::new();
    let mut valid = BTreeSet::new();
    let mut outside = BTreeSet::new();
    for base in context.package_dir.ancestors() {
        let lexical = base.join(display_hint);
        if !lexical_candidates.insert(lexical.clone()) {
            continue;
        }
        record_probe(&lexical);
        let canonical = match fs::canonicalize(&lexical) {
            Ok(canonical) => canonical,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(error) => {
                return Err(CollectionError::new(
                    CollectionErrorKind::HostIo,
                    format!(
                        "cannot canonicalize source candidate for display hint `{display_hint}`: {error}"
                    ),
                ));
            }
        };
        if !canonical.is_file() {
            continue;
        }
        if canonical.starts_with(&context.package_dir) {
            valid.insert(canonical);
        } else {
            outside.insert(canonical);
        }
    }

    let canonical = match valid.len() {
        0 if !outside.is_empty() => {
            return Err(CollectionError::new(
                CollectionErrorKind::SourceOutsidePackage,
                format!(
                    "display source `{display_hint}` resolves only outside selected package `{}`",
                    context.package.cargo_name()
                ),
            ));
        }
        0 => {
            return Err(CollectionError::new(
                CollectionErrorKind::HostIo,
                format!(
                    "display source `{display_hint}` does not resolve to an existing file in selected package `{}`",
                    context.package.cargo_name()
                ),
            ));
        }
        1 => valid.into_iter().next().ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::HostIo,
                "internal source candidate selection failed",
            )
        })?,
        count => {
            return Err(CollectionError::new(
                CollectionErrorKind::AmbiguousSourcePath,
                format!(
                    "display source `{display_hint}` resolves to {count} distinct files in selected package `{}`",
                    context.package.cargo_name()
                ),
            ));
        }
    };
    let relative = canonical
        .strip_prefix(&context.package_dir)
        .map_err(|error| {
            CollectionError::new(
                CollectionErrorKind::SourceOutsidePackage,
                format!("resolved source escaped its selected package: {error}"),
            )
        })?;
    let relative = normalized_relative_path(relative)?;
    Ok((canonical, relative))
}

fn normalized_relative_path(path: &Path) -> Result<String, CollectionError> {
    let mut components = Vec::new();
    for component in path.components() {
        let Component::Normal(component) = component else {
            return Err(CollectionError::new(
                CollectionErrorKind::InvalidDisplayFile,
                format!(
                    "resolved package source `{}` is not a normalized relative path",
                    path.display()
                ),
            ));
        };
        let component = component.to_str().ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::InvalidDisplayFile,
                "resolved package source path is not UTF-8",
            )
        })?;
        components.push(component);
    }
    if components.is_empty() {
        return Err(CollectionError::new(
            CollectionErrorKind::InvalidDisplayFile,
            "resolved package source path is empty",
        ));
    }
    Ok(components.join("/"))
}

pub(super) fn normalize_display_file(display_file: &str) -> Result<String, CollectionError> {
    let normalized = display_file.replace('\\', "/");
    let path = Path::new(&normalized);
    if normalized.is_empty()
        || path.is_absolute()
        || path
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
        || normalized.split('/').any(str::is_empty)
    {
        return Err(CollectionError::new(
            CollectionErrorKind::InvalidDisplayFile,
            format!("display filename `{display_file}` is not normalized and package-relative"),
        ));
    }
    Ok(normalized)
}

pub(super) fn canonicalize_path(path: &Path, role: &str) -> Result<PathBuf, CollectionError> {
    record_probe(path);
    fs::canonicalize(path).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::HostIo,
            format!("cannot canonicalize {role} `{}`: {error}", path.display()),
        )
    })
}
