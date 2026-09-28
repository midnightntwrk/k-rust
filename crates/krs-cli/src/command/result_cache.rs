use super::{
    CommandError, CommandOutcome, CommandRequest, Counters, OutputArtifact, prepare_output,
    write_output_if_different,
};
use crate::{FacetSelector, KrsCfg, RegistrationMode};
use krs_ir::measure::CollectorReadSet;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::time::UNIX_EPOCH;

const SCHEMA: u32 = 3;

#[derive(Serialize)]
struct CacheRequest<'a> {
    command: &'static str,
    manifest_path: &'a [u8],
    root: &'a FacetSelector,
    dependencies: &'a [FacetSelector],
    cfg: &'a [KrsCfg],
    backend: &'static str,
    registration: &'static str,
}

pub(super) struct ResultCache {
    path: PathBuf,
    collector: PathBuf,
}

#[derive(Serialize, Deserialize)]
struct Image {
    schema: u32,
    request: String,
    krs: Executable,
    collector: Executable,
    read_set: CollectorReadSet,
    counters_recorded: bool,
    counters: BTreeMap<String, u64>,
    stdout_len: usize,
    stdout_sha256: String,
    files: Vec<FileEntry>,
}

#[derive(Serialize, Deserialize, PartialEq, Eq)]
struct Executable {
    path: PathBuf,
    dev: u64,
    ino: u64,
    size: u64,
    mtime_ns: u128,
    version: Option<String>,
}

#[derive(Serialize, Deserialize)]
struct FileEntry {
    name: String,
    len: usize,
    sha256: String,
}

impl ResultCache {
    pub(super) fn new(directory: &Path, collector: &Path, request: &CommandRequest) -> Self {
        Self {
            path: directory.join(format!(
                "krs-result-{}-{}.bin",
                request.command.as_str(),
                request.backend.as_str()
            )),
            collector: collector.to_path_buf(),
        }
    }

    pub(super) fn restore(
        &self,
        request: &CommandRequest,
        counters: &mut Counters,
    ) -> Result<Option<CommandOutcome>, CommandError> {
        let Ok(bytes) = fs::read(&self.path) else {
            return Ok(None);
        };
        let Some((image, body)) = decode(&bytes) else {
            return Ok(None);
        };
        if image.schema != SCHEMA
            || image.request != request_key(request)
            || (counters.is_enabled() && !image.counters_recorded)
            || std::env::current_exe()
                .ok()
                .and_then(|path| executable(&path, true))
                .as_ref()
                != Some(&image.krs)
            || executable(&self.collector, false).as_ref() != Some(&image.collector)
            || !read_set_matches(&image.read_set)
        {
            return Ok(None);
        }
        let Some(stdout) = body.get(..image.stdout_len) else {
            return Ok(None);
        };
        if sha256(stdout) != image.stdout_sha256 {
            return Ok(None);
        }
        let mut tail = &body[image.stdout_len..];
        let mut files = Vec::new();
        let mut names = BTreeSet::new();
        for file in image.files {
            if !valid_name(&file.name) || !names.insert(file.name.clone()) {
                return Ok(None);
            }
            let Some(contents) = tail.get(..file.len) else {
                return Ok(None);
            };
            if sha256(contents) != file.sha256 {
                return Ok(None);
            }
            files.push((file.name, contents));
            tail = &tail[file.len..];
        }
        if !tail.is_empty() {
            return Ok(None);
        }
        if let Some(directory) = &request.output_directory {
            prepare_output(directory)?;
            for (name, contents) in files {
                write_output_if_different(directory, &name, contents)?;
            }
        } else if !files.is_empty() {
            return Ok(None);
        }
        for (name, value) in image.counters {
            counters.set(name, value);
        }
        Ok(Some(CommandOutcome {
            stdout: stdout.to_vec(),
        }))
    }

    pub(super) fn store(
        &self,
        request: &CommandRequest,
        outcome: &CommandOutcome,
        artifacts: &[OutputArtifact],
        read_set: &CollectorReadSet,
        counters: &Counters,
    ) {
        let Some(krs) = std::env::current_exe()
            .ok()
            .and_then(|path| executable(&path, true))
        else {
            return;
        };
        let Some(collector) = executable(&self.collector, false) else {
            return;
        };
        let mut body = outcome.stdout.clone();
        let mut files = Vec::new();
        let mut names = BTreeSet::new();
        for (name, bytes) in artifacts {
            if !valid_name(name) || !names.insert(name) {
                return;
            }
            files.push(FileEntry {
                name: name.clone(),
                len: bytes.len(),
                sha256: sha256(bytes),
            });
            body.extend_from_slice(bytes);
        }
        let image = Image {
            schema: SCHEMA,
            request: request_key(request),
            krs,
            collector,
            read_set: read_set.clone(),
            counters_recorded: counters.is_enabled(),
            counters: counters.values().clone(),
            stdout_len: outcome.stdout.len(),
            stdout_sha256: sha256(&outcome.stdout),
            files,
        };
        let Ok(header) = serde_json::to_vec(&image) else {
            return;
        };
        let mut bytes = Vec::with_capacity(8 + header.len() + body.len());
        bytes.extend_from_slice(&(header.len() as u64).to_le_bytes());
        bytes.extend_from_slice(&header);
        bytes.extend_from_slice(&body);
        let temporary = self
            .path
            .with_extension(format!("tmp-{}", std::process::id()));
        if fs::write(&temporary, bytes).is_ok() {
            let _ = fs::rename(&temporary, &self.path);
        }
        let _ = fs::remove_file(temporary);
    }
}

fn decode(bytes: &[u8]) -> Option<(Image, &[u8])> {
    let length = usize::try_from(u64::from_le_bytes(bytes.get(..8)?.try_into().ok()?)).ok()?;
    let header = bytes.get(8..8usize.checked_add(length)?)?;
    Some((
        serde_json::from_slice(header).ok()?,
        bytes.get(8 + length..)?,
    ))
}

fn request_key(request: &CommandRequest) -> String {
    let CommandRequest {
        command,
        manifest_path,
        root,
        dependencies,
        cfg,
        backend,
        output_directory: _,
        registration,
        no_reuse: _,
    } = request;
    let key = CacheRequest {
        command: command.as_str(),
        manifest_path: manifest_path.as_os_str().as_bytes(),
        root,
        dependencies,
        cfg,
        backend: backend.as_str(),
        registration: match registration {
            RegistrationMode::Inventory => "inventory",
            RegistrationMode::Explicit => "explicit",
        },
    };
    serde_json::to_string(&key).expect("cache request serialization cannot fail")
}

fn executable(path: &Path, krs: bool) -> Option<Executable> {
    let metadata = fs::metadata(path).ok()?;
    let modified = metadata.modified().ok()?.duration_since(UNIX_EPOCH).ok()?;
    Some(Executable {
        path: path.to_path_buf(),
        dev: metadata.dev(),
        ino: metadata.ino(),
        size: metadata.len(),
        mtime_ns: modified.as_nanos(),
        version: krs.then(|| env!("CARGO_PKG_VERSION").to_owned()),
    })
}

fn read_set_matches(read_set: &CollectorReadSet) -> bool {
    for (path, expected) in &read_set.files {
        let Ok(bytes) = fs::read(path) else {
            return false;
        };
        if sha256(&bytes) != *expected {
            return false;
        }
    }
    for probe in &read_set.probes {
        if fs::canonicalize(&probe.path).ok() != probe.canonical
            || probe.path.is_file() != probe.is_file
        {
            return false;
        }
    }
    true
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
fn valid_name(name: &str) -> bool {
    !name.is_empty() && !name.contains('/') && !name.contains('\\') && name != ".krs-artifacts"
}
