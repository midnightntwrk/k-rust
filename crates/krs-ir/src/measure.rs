//! Opt-in compile-performance measurement shared by `krs`, generated
//! collectors, and the native adapter.
//!
//! Nothing here affects what KRS emits. A disabled [`Timings`] or [`Counters`]
//! records nothing and never reads a clock, so the default command path pays
//! only a branch per phase.
//!
//! # `krs-timings/1`
//!
//! `krs <check|expand|emit-k|build> --timings FILE` and
//! `krs-gate compile --timings FILE` write one [`TimingsDocument`] as pretty
//! JSON, on success and on failure:
//!
//! ```json
//! {
//!   "schema": "krs-timings/1",
//!   "command": "build",
//!   "status": "ok",
//!   "failed_span": null,
//!   "total_wall_seconds": 14.9,
//!   "attributed_seconds": 14.8,
//!   "unattributed_seconds": 0.1,
//!   "spans": [
//!     { "id": "cargo.metadata.input", "seconds": 0.02, "depth": 0 },
//!     { "id": "collector.build", "seconds": 8.0, "depth": 0 },
//!     { "id": "collector.run", "seconds": 5.1, "depth": 0 },
//!     { "id": "collector.exec", "seconds": 0.1, "depth": 1 }
//!   ]
//! }
//! ```
//!
//! - `spans` is in pre-order: a parent precedes its children, and a child has
//!   its parent's `depth` plus one. A parent's `seconds` include its children.
//!   An id may repeat (k-rust stage names do).
//! - `total_wall_seconds` is measured from the start of command execution to
//!   the moment the document is built; process startup, argument parsing, and
//!   writing the document itself are excluded.
//! - `attributed_seconds` is the sum of depth-0 spans, and
//!   `unattributed_seconds` is `max(0, total - attributed)`.
//! - `status` is `"ok"` or `"failed"`. On failure every span that completed
//!   is present, including the failing one, and `failed_span` names the
//!   innermost span whose stage returned the error (or `null` when the
//!   failure happened outside every span).
//!
//! Stable `krs` span ids, in execution order (`check`, `expand`, `emit_k`,
//! `stage`, and `exec` ids belong to their command only; the `native` ids
//! belong to `build` and, on a stage-cache miss, to `parse`, `run`, `search`,
//! and `prove`):
//!
//! | Id | Stage |
//! |---|---|
//! | `cargo.metadata.input` | `cargo metadata` on the input manifest |
//! | `host.discover` | `rustc -vV` host-triple discovery |
//! | `cargo.metadata.runtime` | `cargo metadata` of the KRS installation |
//! | `collector.plan` | facet and dependency-closure planning |
//! | `collector.generate` | render and write the collector package |
//! | `collector.build` | `cargo build` of the generated collector package |
//! | `result.reuse` | validate and restore a cached successful result |
//! | `collector.run` | execute the built collector binary, with children below |
//! | `protocol.decode` | decode collector stdout as a descriptor bundle |
//! | `semantic.lower` | descriptor bundle to semantic theory |
//! | `definition.lower` | semantic theory to Definition IR and sidecars |
//! | `check.adapt` | `check`: backend support and structural adaptation |
//! | `expand.render` | `expand`: select, reread, and render the source |
//! | `emit_k.render` | `emit-k`: canonical JSON and K rendering |
//! | `emit_k.write` | `emit-k`: artifact writes |
//! | `native.adapt` | `build`: structural adaptation |
//! | `native.prepare` | `build`: k-rust structured loading |
//! | `native.compile` | `build`: k-rust compilation, k-rust phases below |
//! | `native.diagnostics` | `build`, on compilation failure: translate compiler diagnostics |
//! | `native.reparse.definition` | `build`: reparse `definition.kore` |
//! | `native.reparse.syntax` | `build`: reparse `syntaxDefinition.kore` |
//! | `native.provenance` | `build`: join emitted-sentence provenance |
//! | `native.write` | `build`: artifact writes |
//! | `stage.reuse` | `parse`, `run`, `search`, `prove`: validate and restore the cached compiled stage, in place of the `native.*` spans |
//! | `stage.store` | `parse`, `run`, `search`, `prove`, after the `native.*` spans: encode and store the compiled stage |
//! | `exec.configuration`, `exec.unparser`, `exec.backend` | `parse`, `run`, `search`, `prove`: build the program grammar, the printer, and the backend from the compiled stage |
//! | `release` | drop the in-memory bundle, theory, and Definition IR |
//!
//! `collector.run` children (depth 1, grandchildren at depth 2):
//! `collector.exec` is the time from spawning the built binary until it entered
//! `main`, derived from wall-clock timestamps in both processes. It is followed
//! by the collector's own spans: `collector.factories` (descriptor
//! factory invocation over the registrations), `collector.builtins`,
//! `collector.resolve` (with `collector.resolve.builtins`,
//! `collector.resolve.intake`, `collector.resolve.tables`,
//! `collector.resolve.provenance`, `collector.resolve.payload`, and
//! `collector.resolve.bundle`; provenance and payload are accumulated over the
//! per-descriptor loop that interleaves them), `collector.serialize`,
//! `collector.write` (stdout, including the reader's pace), and
//! `collector.release`. Collector exit remains unattributed inside `collector.run`.
//!
//! `native.compile` children are k-rust's own `PhaseTimings` names, unchanged
//! and in k-rust's order, one level deeper than in k-rust. A native failure
//! loses them, because k-rust returns no timings with its error (upstream
//! k-rust/compile-error-phase-timings).
//!
//! `krs-gate compile` uses `native.input` (read and decode the Definition
//! IR JSON), then the `native.*` ids above.
//!
//! # `krs-counters/1`
//!
//! `--counters FILE` writes one [`CountersDocument`]: deterministic work sizes
//! computed from data already in hand. Repeated runs over the same inputs
//! produce byte-identical documents; keys are sorted.
//!
//! ```json
//! {
//!   "schema": "krs-counters/1",
//!   "command": "build",
//!   "status": "ok",
//!   "counters": { "bundle.bytes": 12345, "descriptors.total": 1100 }
//! }
//! ```
//!
//! | Key | Meaning |
//! |---|---|
//! | `bundle.bytes` | collector stdout bytes (compact collector wire, including the trailing newline) |
//! | `bundle.provenance_bytes` | bytes of every descriptor `provenance` value in that stdout |
//! | `bundle.other_bytes` | `bundle.bytes - bundle.provenance_bytes` |
//! | `collector.host_descriptors` | host descriptors returned by the factories |
//! | `descriptors.total`, `descriptors.kind.<ItemKind>` | bundle descriptors |
//! | `declarations.total` | bundle declaration metadata entries |
//! | `provenance.anchors` | parser-keyed node origins over all descriptors |
//! | `provenance.origin_frames` | origin-stack frames over those anchors |
//! | `semantic.modules` | semantic theory modules |
//! | `definition.modules`, `definition.sentences`, `definition.sentences.<kind>` | Definition IR |
//! | `definition.symbols`, `definition.source_map_entries` | lowering sidecars |
//! | `emit_k.bytes.<artifact>` | `emit-k` artifact bytes |
//! | `native.omitted_claims`, `native.bytes.<artifact>` | `build` KORE bytes |
//! | `result.reused` | 1 when a saved result was restored, otherwise 0 |
//! | `stage.reused` | `parse`, `run`, `search`, `prove`: 1 when the compiled stage was restored from the stage cache, otherwise 0 |
//!
//! A counter is present only when its stage ran.
//!
//! # Collector sidecar
//!
//! When `krs` measures, it sets [`COLLECTOR_MEASURE_ENV`] on the collector
//! process to a file path; stdout stays reserved for the descriptor protocol.
//! The generated collector writes a [`CollectorMeasureDocument`] there, which
//! `krs` folds into its own documents.

use std::cell::Cell;
use std::collections::BTreeMap;
use std::io;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};

/// Schema identifier of [`TimingsDocument`].
pub const TIMINGS_SCHEMA: &str = "krs-timings/1";
/// Schema identifier of [`CountersDocument`].
pub const COUNTERS_SCHEMA: &str = "krs-counters/1";
/// Schema identifier of [`CollectorMeasureDocument`].
pub const COLLECTOR_MEASURE_SCHEMA: &str = "krs-collector-measure/1";
/// Environment variable naming the collector diagnostic JSON-lines sidecar path.
/// Located collection failures use schema-versioned analysis envelopes.
pub const COLLECTOR_DIAGNOSTIC_ENV: &str = "KRS_COLLECTOR_DIAGNOSTIC";

/// Environment variable naming the collector measurement sidecar path.
pub const COLLECTOR_MEASURE_ENV: &str = "KRS_COLLECTOR_MEASURE";
/// Environment variable naming the collector's source read-set sidecar.
pub const COLLECTOR_READ_SET_ENV: &str = "KRS_COLLECTOR_READ_SET";

/// Files actually read by one collector execution.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CollectorReadSet {
    /// Canonical paths and SHA-256 digests of their bytes.
    pub files: Vec<(std::path::PathBuf, String)>,
    /// Paths whose resolution or existence affected collection.
    pub probes: Vec<CollectorPathProbe>,
}

/// One path observation made during collection.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CollectorPathProbe {
    /// The path tested by the collector.
    pub path: std::path::PathBuf,
    /// Its canonical target, when it existed.
    pub canonical: Option<std::path::PathBuf>,
    /// Whether it resolved to a regular file.
    pub is_file: bool,
}

/// One completed phase.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Span {
    /// Stable dotted id, or a k-rust stage name below `native.compile`.
    pub id: String,
    /// Wall-clock seconds, including children.
    pub seconds: f64,
    /// Nesting depth; top-level spans have depth zero.
    pub depth: u8,
}

/// Ordered, nestable phase recorder.
#[derive(Debug, Default)]
pub struct Timings {
    enabled: bool,
    spans: Vec<Span>,
    depth: u8,
    failed_span: Option<String>,
    started: Option<Instant>,
}

impl Timings {
    /// A recorder that records nothing and never reads a clock.
    #[must_use]
    pub fn disabled() -> Self {
        Self::default()
    }

    /// A recorder whose total wall time starts now.
    #[must_use]
    pub fn enabled() -> Self {
        Self {
            enabled: true,
            started: Some(Instant::now()),
            ..Self::default()
        }
    }

    /// Whether spans are recorded.
    #[must_use]
    pub const fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Run `run` as span `id`; spans it records become children.
    pub fn span<T>(&mut self, id: &str, run: impl FnOnce(&mut Self) -> T) -> T {
        if !self.enabled {
            return run(self);
        }
        let index = self.spans.len();
        self.spans.push(Span {
            id: id.to_owned(),
            seconds: 0.0,
            depth: self.depth,
        });
        self.depth = self.depth.saturating_add(1);
        let started = Instant::now();
        let value = run(self);
        self.spans[index].seconds = started.elapsed().as_secs_f64();
        self.depth = self.depth.saturating_sub(1);
        value
    }

    /// [`Self::span`] for a fallible stage: an error marks `id` as the failed
    /// span unless a child already claimed the failure.
    ///
    /// # Errors
    ///
    /// Returns the stage's own error unchanged.
    pub fn try_span<T, E>(
        &mut self,
        id: &str,
        run: impl FnOnce(&mut Self) -> Result<T, E>,
    ) -> Result<T, E> {
        let result = self.span(id, run);
        if result.is_err() {
            self.mark_failed(id);
        }
        result
    }

    /// Name `id` as the failed span unless one is already named; for a
    /// failure inside an accumulated or imported span.
    pub fn mark_failed(&mut self, id: &str) {
        if self.enabled && self.failed_span.is_none() {
            self.failed_span = Some(id.to_owned());
        }
    }

    /// Append an already measured span at the current depth plus `depth`.
    pub fn record(&mut self, id: &str, seconds: f64, depth: u8) {
        if self.enabled {
            self.spans.push(Span {
                id: id.to_owned(),
                seconds: seconds.max(0.0),
                depth: self.depth.saturating_add(depth),
            });
        }
    }

    /// Append spans measured elsewhere, shifting their depths below the
    /// current one.
    pub fn import(&mut self, spans: impl IntoIterator<Item = Span>) {
        if self.enabled {
            for span in spans {
                self.record(&span.id, span.seconds, span.depth);
            }
        }
    }

    /// A start instant for accumulated timing, `None` when disabled.
    #[must_use]
    pub fn now(&self) -> Option<Instant> {
        self.enabled.then(Instant::now)
    }

    /// Seconds since `started`, or zero for a disabled start.
    #[must_use]
    pub fn since(started: Option<Instant>) -> f64 {
        started.map_or(0.0, |started| started.elapsed().as_secs_f64())
    }

    /// Recorded spans in pre-order.
    #[must_use]
    pub fn spans(&self) -> &[Span] {
        &self.spans
    }

    /// Take the recorded spans, leaving the recorder empty but enabled.
    pub fn take_spans(&mut self) -> Vec<Span> {
        std::mem::take(&mut self.spans)
    }

    /// The innermost span whose stage failed, if any.
    #[must_use]
    pub fn failed_span(&self) -> Option<&str> {
        self.failed_span.as_deref()
    }

    /// Build the `krs-timings/1` document for `command`.
    #[must_use]
    pub fn document(&self, command: &str, succeeded: bool) -> TimingsDocument {
        let total_wall_seconds = Self::since(self.started);
        let attributed_seconds = self
            .spans
            .iter()
            .filter(|span| span.depth == 0)
            .map(|span| span.seconds)
            .sum::<f64>();
        TimingsDocument {
            schema: TIMINGS_SCHEMA.to_owned(),
            command: command.to_owned(),
            status: status(succeeded),
            failed_span: if succeeded {
                None
            } else {
                self.failed_span.clone()
            },
            total_wall_seconds,
            attributed_seconds,
            unattributed_seconds: (total_wall_seconds - attributed_seconds).max(0.0),
            spans: self.spans.clone(),
        }
    }
}

/// Deterministic named work sizes.
#[derive(Debug, Default)]
pub struct Counters {
    enabled: bool,
    values: BTreeMap<String, u64>,
}

impl Counters {
    /// A counter set that records nothing.
    #[must_use]
    pub fn disabled() -> Self {
        Self::default()
    }

    /// A counter set that records.
    #[must_use]
    pub fn enabled() -> Self {
        Self {
            enabled: true,
            values: BTreeMap::new(),
        }
    }

    /// Whether counters are recorded; callers skip counting work otherwise.
    #[must_use]
    pub const fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Set counter `name` to `value`.
    pub fn set(&mut self, name: impl Into<String>, value: impl TryInto<u64>) {
        if self.enabled {
            self.values
                .insert(name.into(), value.try_into().unwrap_or(u64::MAX));
        }
    }

    /// Add `value` to counter `name`.
    pub fn add(&mut self, name: impl Into<String>, value: impl TryInto<u64>) {
        if self.enabled {
            let entry = self.values.entry(name.into()).or_default();
            *entry = entry.saturating_add(value.try_into().unwrap_or(u64::MAX));
        }
    }

    /// Look up one counter.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<u64> {
        self.values.get(name).copied()
    }

    /// Recorded counters in key order.
    #[must_use]
    pub const fn values(&self) -> &BTreeMap<String, u64> {
        &self.values
    }

    /// Build the `krs-counters/1` document for `command`.
    #[must_use]
    pub fn document(&self, command: &str, succeeded: bool) -> CountersDocument {
        CountersDocument {
            schema: COUNTERS_SCHEMA.to_owned(),
            command: command.to_owned(),
            status: status(succeeded),
            counters: self.values.clone(),
        }
    }
}

/// Both recorders of one command execution.
#[derive(Debug, Default)]
pub struct Measurement {
    /// Phase timings.
    pub timings: Timings,
    /// Work counters.
    pub counters: Counters,
}

impl Measurement {
    /// Measure nothing.
    #[must_use]
    pub fn disabled() -> Self {
        Self::default()
    }

    /// Measure the selected kinds.
    #[must_use]
    pub fn new(timings: bool, counters: bool) -> Self {
        Self {
            timings: if timings {
                Timings::enabled()
            } else {
                Timings::disabled()
            },
            counters: if counters {
                Counters::enabled()
            } else {
                Counters::disabled()
            },
        }
    }

    /// Whether either recorder is enabled.
    #[must_use]
    pub const fn is_enabled(&self) -> bool {
        self.timings.is_enabled() || self.counters.is_enabled()
    }
}

fn status(succeeded: bool) -> String {
    if succeeded { "ok" } else { "failed" }.to_owned()
}

/// The `krs-timings/1` document; see the module documentation.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct TimingsDocument {
    /// Always [`TIMINGS_SCHEMA`].
    pub schema: String,
    /// `check`, `expand`, `emit-k`, `build`, or `native-compile`.
    pub command: String,
    /// `ok` or `failed`.
    pub status: String,
    /// Innermost failing span on failure.
    pub failed_span: Option<String>,
    /// Wall time of command execution.
    pub total_wall_seconds: f64,
    /// Sum of depth-0 spans.
    pub attributed_seconds: f64,
    /// Wall time no depth-0 span claims.
    pub unattributed_seconds: f64,
    /// Spans in pre-order.
    pub spans: Vec<Span>,
}

/// The `krs-counters/1` document; see the module documentation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CountersDocument {
    /// Always [`COUNTERS_SCHEMA`].
    pub schema: String,
    /// `check`, `expand`, `emit-k`, or `build`.
    pub command: String,
    /// `ok` or `failed`.
    pub status: String,
    /// Counters in key order.
    pub counters: BTreeMap<String, u64>,
}

/// Measurement a generated collector hands back to `krs` out of band.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CollectorMeasureDocument {
    /// Always [`COLLECTOR_MEASURE_SCHEMA`].
    pub schema: String,
    /// Wall-clock time at which collection started, in seconds since the
    /// Unix epoch.
    pub started_unix_seconds: f64,
    /// Collector spans, rooted at depth zero.
    pub spans: Vec<Span>,
    /// Collector-side counters.
    pub counters: BTreeMap<String, u64>,
}

/// Seconds since the Unix epoch, for timestamps compared across processes.
#[must_use]
pub fn unix_seconds() -> f64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0.0, |elapsed| elapsed.as_secs_f64())
}

thread_local! {
    static PROVENANCE_DEPTH: Cell<u32> = const { Cell::new(0) };
}

/// Marks bytes written during descriptor provenance serialization.
pub(crate) struct ProvenanceScope;

impl ProvenanceScope {
    pub(crate) fn enter() -> Self {
        PROVENANCE_DEPTH.with(|depth| depth.set(depth.get().saturating_add(1)));
        Self
    }
}

impl Drop for ProvenanceScope {
    fn drop(&mut self) {
        PROVENANCE_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
    }
}

/// A byte sink that counts provenance value bytes in the serialized pipe payload.
pub(crate) struct ProvenanceCountingWriter {
    pub(crate) bytes: Vec<u8>,
    pub(crate) provenance: u64,
}

impl io::Write for ProvenanceCountingWriter {
    fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
        self.write_all(buffer)?;
        Ok(buffer.len())
    }

    fn write_all(&mut self, buffer: &[u8]) -> io::Result<()> {
        if PROVENANCE_DEPTH.with(Cell::get) > 0 {
            self.provenance = self
                .provenance
                .saturating_add(u64::try_from(buffer.len()).unwrap_or(u64::MAX));
        }
        self.bytes.extend_from_slice(buffer);
        Ok(())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use krs_test_support::assert_rejects;

    #[test]
    fn disabled_recorders_record_nothing() {
        let mut timings = Timings::disabled();
        let value = timings.span("outer", |timings| timings.span("inner", |_| 7));
        assert_eq!(value, 7);
        assert!(timings.spans().is_empty());
        let mut counters = Counters::disabled();
        counters.set("a", 1u64);
        assert!(counters.values().is_empty());
    }

    #[test]
    fn spans_are_pre_order_and_failures_name_the_innermost_span() {
        let mut timings = Timings::enabled();
        let result: Result<(), &str> = timings.try_span("outer", |timings| {
            timings.span("first", |_| ());
            timings.try_span("second", |timings| {
                timings.record("imported", 0.5, 1);
                Err("no")
            })
        });
        assert_rejects!(result, "no");
        let ids = timings
            .spans()
            .iter()
            .map(|span| (span.id.as_str(), span.depth))
            .collect::<Vec<_>>();
        assert_eq!(
            ids,
            [("outer", 0), ("first", 1), ("second", 1), ("imported", 3)]
        );
        let document = timings.document("check", false);
        assert_eq!(document.failed_span.as_deref(), Some("second"));
        assert_eq!(document.status, "failed");
        assert!(document.unattributed_seconds >= 0.0);
        assert!(document.total_wall_seconds >= document.spans[0].seconds);
    }

    #[test]
    fn counted_provenance_bytes_match_the_serialized_value() {
        use std::io::Write as _;
        let mut writer = ProvenanceCountingWriter {
            bytes: Vec::new(),
            provenance: 0,
        };
        writer.write_all(b"ab").unwrap();
        {
            let _scope = ProvenanceScope::enter();
            writer.write_all(b"cde").unwrap();
        }
        writer.write_all(b"f").unwrap();
        assert_eq!(writer.bytes, b"abcdef");
        assert_eq!(writer.provenance, 3);
    }
}
