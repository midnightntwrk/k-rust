//! The prepared definition of `krs parse`, `run`, `search`, `prove`, `cases`, and `compare`, stored beside the collector so that a later command restores it instead of running the frontend.
//!
//! Those commands read three things of the frontend's work: the Definition IR, its source map (to locate a native compile's diagnostics), and the definition's warnings.
//! All three are a function of the collector's output, the composition's root package, the raw-K profile, and the `krs` executable that lowers them.
//! The collector's output is in turn a function of the collector executable and of the files it read and the paths it probed.
//! A record is therefore restored only when all of these are what they were when it was stored: the composition ([`composition_key`]), the running `krs` executable, the collector executable Cargo just brought up to date, and the collector's read set, each file by content digest and each probe by its resolution.
//! These are the conditions under which the result cache restores a `check`, `emit-k`, or `build` outcome, read through the same functions.
//! Nothing a single run gives (its case, inputs, depth, output, stops, observations, solver options) is read by the frontend, so none of it is part of the key.
//!
//! The record lies in the generated collector's directory, whose name digests the generated collector, so each composition has its own.
//! It holds the canonical JSON of the Definition IR, whose digest is the stage cache's key, so a restored definition names its compiled stage without being serialized again.
//! A definition whose encoding does not decode to an equal definition is not stored, and every failure to read or write a record only means the frontend runs.

use super::result_cache::{Executable, composition_key, executable, read_set_matches, sha256};
use super::{Counters, PreparedDefinition, definition_warnings};
use crate::{CommandRequest, DiagnosticReports};
use krs_compiler::SourceMap;
use krs_ir::measure::CollectorReadSet;
use krs_ir_levels::DefinitionIr;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// The schema of a record's header and sections.
const SCHEMA: u32 = 1;
/// The record's file name in the collector directory.
const FILE: &str = "krs-definition.bin";

/// What a command that executes a definition reads of the frontend's work.
pub(super) struct RunDefinition {
    /// The definition's warnings ([`definition_warnings`]).
    warnings: DiagnosticReports,
    definition: DefinitionIr,
    source_map: StoredSourceMap,
    /// The SHA-256 of the canonical JSON of `definition`, when it has one: the stage cache's
    /// key.
    definition_sha256: Option<String>,
}

/// The canonical JSON of the Definition IR the frontend just lowered, with what its record
/// states beside it, until [`DefinitionCache::store`] writes the record.
pub(super) struct Lowered {
    canonical: String,
    read_set: CollectorReadSet,
    counters_recorded: bool,
    counters: BTreeMap<String, u64>,
}

/// A source map, held or still encoded: only a failed native compile reads it.
enum StoredSourceMap {
    Held(SourceMap),
    /// The JSON a record held, whose digest was checked, decoded on first use.
    Encoded {
        json: Vec<u8>,
        decoded: OnceLock<Option<SourceMap>>,
    },
}

impl RunDefinition {
    /// What the executing commands read of `prepared`, the rest of which is dropped, and what
    /// its record holds: the frontend made `prepared` from a collector run that read
    /// `read_set`, recording `counters`. A definition without canonical JSON has no record.
    pub(super) fn new(
        prepared: PreparedDefinition,
        read_set: CollectorReadSet,
        counters: &Counters,
    ) -> (Self, Option<Lowered>) {
        let warnings = definition_warnings(&prepared);
        let (definition, source_map) = prepared.lowered.into_definition_and_source_map();
        let lowered = definition
            .to_canonical_json()
            .ok()
            .map(|canonical| Lowered {
                canonical,
                read_set,
                counters_recorded: counters.is_enabled(),
                counters: counters.values().clone(),
            });
        let definition = Self {
            warnings,
            definition,
            source_map: StoredSourceMap::Held(source_map),
            definition_sha256: lowered
                .as_ref()
                .map(|lowered| sha256(lowered.canonical.as_bytes())),
        };
        (definition, lowered)
    }

    /// The definition's warnings ([`definition_warnings`]).
    pub(super) const fn warnings(&self) -> &DiagnosticReports {
        &self.warnings
    }

    /// The Definition IR.
    pub(super) const fn definition(&self) -> &DefinitionIr {
        &self.definition
    }

    /// The Definition IR, owned.
    pub(super) fn into_definition(self) -> DefinitionIr {
        self.definition
    }

    /// The SHA-256 of the Definition IR's canonical JSON, when it has one.
    pub(super) fn definition_sha256(&self) -> Option<&str> {
        self.definition_sha256.as_deref()
    }

    /// The source map; `None` for a restored one that does not decode, which then locates
    /// nothing.
    pub(super) fn source_map(&self) -> Option<&SourceMap> {
        match &self.source_map {
            StoredSourceMap::Held(source_map) => Some(source_map),
            StoredSourceMap::Encoded { json, decoded } => decoded
                .get_or_init(|| krs_ir::json::from_slice(json).ok())
                .as_ref(),
        }
    }
}

/// What a record states ahead of its two sections, the Definition IR and the source map.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    schema: u32,
    composition: String,
    krs: Executable,
    collector: Executable,
    read_set: CollectorReadSet,
    counters_recorded: bool,
    counters: BTreeMap<String, u64>,
    warnings: DiagnosticReports,
    definition_len: usize,
    definition_sha256: String,
    source_map_len: usize,
    source_map_sha256: String,
}

/// One composition's record.
pub(super) struct DefinitionCache {
    path: PathBuf,
    collector: PathBuf,
    composition: String,
}

impl DefinitionCache {
    /// The record of the composition `request` selects, whose generated collector is
    /// `collector`, in `directory`.
    pub(super) fn new(directory: &Path, collector: &Path, request: &CommandRequest) -> Self {
        Self {
            path: directory.join(FILE),
            collector: collector.to_path_buf(),
            composition: composition_key(request),
        }
    }

    /// The stored definition, when the record is intact and everything it is a function of is
    /// unchanged; `counters` then gains the counters the frontend recorded when it was stored.
    /// A record stored without counters is not restored for a command that records them.
    pub(super) fn restore(&self, counters: &mut Counters) -> Option<RunDefinition> {
        let mut bytes = fs::read(&self.path).ok()?;
        let length = usize::try_from(u64::from_le_bytes(bytes.get(..8)?.try_into().ok()?)).ok()?;
        let body_start = 8usize.checked_add(length)?;
        let header: Header = serde_json::from_slice(bytes.get(8..body_start)?).ok()?;
        if header.schema != SCHEMA
            || header.composition != self.composition
            || (counters.is_enabled() && !header.counters_recorded)
            || running_krs().as_ref() != Some(&header.krs)
            || executable(&self.collector, false).as_ref() != Some(&header.collector)
            || !read_set_matches(&header.read_set)
        {
            return None;
        }
        let source_map_start = body_start.checked_add(header.definition_len)?;
        if bytes.len() != source_map_start.checked_add(header.source_map_len)? {
            return None;
        }
        let definition_json = &bytes[body_start..source_map_start];
        if sha256(definition_json) != header.definition_sha256
            || sha256(&bytes[source_map_start..]) != header.source_map_sha256
        {
            return None;
        }
        let definition: DefinitionIr = krs_ir::json::from_slice(definition_json).ok()?;
        bytes.drain(..source_map_start);
        for (name, value) in header.counters {
            counters.set(name, value);
        }
        Some(RunDefinition {
            warnings: header.warnings,
            definition,
            source_map: StoredSourceMap::Encoded {
                json: bytes,
                decoded: OnceLock::new(),
            },
            definition_sha256: Some(header.definition_sha256),
        })
    }

    /// Store `definition`, which the frontend just lowered as `lowered` states, replacing the
    /// record atomically. A definition whose canonical JSON does not decode to an equal
    /// definition is not stored: the record must restore the definition the run was made on.
    /// The source map only locates diagnostics, and one that does not decode locates none.
    pub(super) fn store(&self, definition: &RunDefinition, lowered: Lowered) {
        let Lowered {
            canonical,
            read_set,
            counters_recorded,
            counters,
        } = lowered;
        let (Some(krs), Some(collector), Some(definition_sha256)) = (
            running_krs(),
            executable(&self.collector, false),
            definition.definition_sha256(),
        ) else {
            return;
        };
        let StoredSourceMap::Held(source_map) = &definition.source_map else {
            return;
        };
        let faithful = krs_ir::json::from_slice::<DefinitionIr>(canonical.as_bytes())
            .is_ok_and(|decoded| decoded == definition.definition);
        if !faithful {
            return;
        }
        let Ok(source_map) = serde_json::to_vec(source_map) else {
            return;
        };
        let header = Header {
            schema: SCHEMA,
            composition: self.composition.clone(),
            krs,
            collector,
            read_set,
            counters_recorded,
            counters,
            warnings: definition.warnings.clone(),
            definition_len: canonical.len(),
            definition_sha256: definition_sha256.to_owned(),
            source_map_len: source_map.len(),
            source_map_sha256: sha256(&source_map),
        };
        let Ok(header) = serde_json::to_vec(&header) else {
            return;
        };
        let Some(directory) = self.path.parent() else {
            return;
        };
        let Ok(mut temporary) = tempfile::NamedTempFile::new_in(directory) else {
            return;
        };
        let written = temporary
            .write_all(&(header.len() as u64).to_le_bytes())
            .and_then(|()| temporary.write_all(&header))
            .and_then(|()| temporary.write_all(canonical.as_bytes()))
            .and_then(|()| temporary.write_all(&source_map));
        if written.is_ok() {
            let _ = temporary.persist(&self.path);
        }
    }
}

/// The identity of the running `krs` executable.
fn running_krs() -> Option<Executable> {
    executable(&std::env::current_exe().ok()?, true)
}
