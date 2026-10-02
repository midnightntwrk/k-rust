//! The body of a generated production collector executable.

use std::error::Error;
use std::io::{BufWriter, Write as _};
use std::path::PathBuf;

use krs_ir::measure::{
    COLLECTOR_DIAGNOSTIC_ENV, COLLECTOR_MEASURE_ENV, COLLECTOR_MEASURE_SCHEMA,
    COLLECTOR_READ_SET_ENV, CollectorMeasureDocument, Counters, Timings, unix_seconds,
};
use krs_ir::{HostBuiltinRegistry, HostDescriptor, HostProvenanceError};

use crate::CollectionError;
use krs_diagnostic::{
    ToDiagnostic,
    envelope::{DiagnosticStage, diagnostic_envelope},
};

use super::{PackageContext, collect_host_descriptors_with_builtins_timed, source};

/// Collect the host descriptor factory results of `contexts` and write compact canonical descriptor bundle JSON to stdout.
///
/// Generated collectors call this once from `main`. When `krs` sets
/// [`COLLECTOR_MEASURE_ENV`] to a path, the collector also records its phases
/// and counters there as a `krs-collector-measure/1` document, on success and
/// on failure; stdout carries exactly the same bytes either way.
/// When [`COLLECTOR_DIAGNOSTIC_ENV`] is set, a located collection failure writes an analysis envelope as JSON lines to that sidecar.
///
/// # Errors
///
/// Returns collection, serialization, stdout, or measurement-sidecar write failures.
/// Diagnostic-sidecar write failures must be reported on stderr without replacing the collection failure.
pub fn run_collector<I>(
    contexts: Vec<PackageContext>,
    descriptors: impl FnOnce() -> I,
    builtins: impl FnOnce() -> HostBuiltinRegistry,
) -> Result<(), Box<dyn Error>>
where
    I: IntoIterator<Item = Result<HostDescriptor, HostProvenanceError>>,
{
    let read_set = std::env::var_os(COLLECTOR_READ_SET_ENV).map(PathBuf::from);
    if read_set.is_some() {
        source::start_read_set();
    }
    let sidecar = std::env::var_os(COLLECTOR_MEASURE_ENV).map(PathBuf::from);
    let result = if let Some(sidecar) = sidecar {
        let started_unix_seconds = unix_seconds();
        let mut timings = Timings::enabled();
        let mut counters = Counters::enabled();
        let result =
            collect_and_write(contexts, descriptors, builtins, &mut timings, &mut counters);
        let document = CollectorMeasureDocument {
            schema: COLLECTOR_MEASURE_SCHEMA.to_owned(),
            started_unix_seconds,
            spans: timings.take_spans(),
            counters: counters.values().clone(),
        };
        let written = serde_json::to_vec_pretty(&document)
            .map_err(RunError::from)
            .and_then(|bytes| std::fs::write(&sidecar, bytes).map_err(Into::into));
        result.and(written)
    } else {
        collect_and_write(
            contexts,
            descriptors,
            builtins,
            &mut Timings::disabled(),
            &mut Counters::disabled(),
        )
    };
    if let Some(path) = read_set {
        let bytes = serde_json::to_vec(&source::take_read_set())?;
        std::fs::write(path, bytes)?;
    }
    let result = match std::env::var_os(COLLECTOR_DIAGNOSTIC_ENV) {
        Some(path) => with_diagnostic_sidecar(result, &PathBuf::from(path)),
        None => result,
    };
    result.map_err(Into::into)
}

fn with_diagnostic_sidecar(
    result: Result<(), RunError>,
    path: &std::path::Path,
) -> Result<(), RunError> {
    if let Err(RunError::Collection(error)) = &result
        && let Err(secondary) = write_diagnostic(error, path)
    {
        let _ = writeln!(
            std::io::stderr().lock(),
            "could not write collection diagnostic sidecar {}: {secondary}",
            path.display(),
        );
    }
    result
}

fn write_diagnostic(error: &CollectionError, path: &std::path::Path) -> Result<(), RunError> {
    if let Some(envelope) =
        diagnostic_envelope(error.to_diagnostic(), DiagnosticStage::Analysis, |_| None)
    {
        std::fs::write(path, envelope.to_json_line()?)?;
    }
    Ok(())
}

#[derive(Debug)]
enum RunError {
    Collection(CollectionError),
    Json(serde_json::Error),
    Io(std::io::Error),
}

impl std::fmt::Display for RunError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Collection(error) => error.fmt(formatter),
            Self::Json(error) => error.fmt(formatter),
            Self::Io(error) => error.fmt(formatter),
        }
    }
}

impl Error for RunError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Collection(error) => Some(error),
            Self::Json(error) => Some(error),
            Self::Io(error) => Some(error),
        }
    }
}

impl From<CollectionError> for RunError {
    fn from(error: CollectionError) -> Self {
        Self::Collection(error)
    }
}
impl From<serde_json::Error> for RunError {
    fn from(error: serde_json::Error) -> Self {
        Self::Json(error)
    }
}
impl From<std::io::Error> for RunError {
    fn from(error: std::io::Error) -> Self {
        Self::Io(error)
    }
}

fn collect_and_write<I>(
    contexts: Vec<PackageContext>,
    descriptors: impl FnOnce() -> I,
    builtins: impl FnOnce() -> HostBuiltinRegistry,
    timings: &mut Timings,
    counters: &mut Counters,
) -> Result<(), RunError>
where
    I: IntoIterator<Item = Result<HostDescriptor, HostProvenanceError>>,
{
    let descriptors = timings.span("collector.factories", |_| {
        descriptors().into_iter().collect::<Vec<_>>()
    });
    counters.set("collector.host_descriptors", descriptors.len());
    let builtins = timings.span("collector.builtins", |_| builtins());
    let bundle = timings.try_span("collector.resolve", |timings| {
        collect_host_descriptors_with_builtins_timed(contexts, descriptors, &builtins, timings)
    })?;
    if counters.is_enabled() {
        let json = timings.try_span("collector.serialize", |_| {
            let (bytes, provenance) = bundle.to_collector_protocol_measured()?;
            counters.set("bundle.provenance_bytes", provenance);
            Ok::<_, serde_json::Error>(bytes)
        })?;
        timings.try_span("collector.write", |_| {
            let mut stdout = std::io::stdout().lock();
            stdout.write_all(&json)?;
            stdout.flush()
        })?;
        timings.span("collector.release", |_| drop((bundle, json, builtins)));
    } else {
        timings.try_span("collector.serialize", |_| -> Result<(), RunError> {
            let stdout = std::io::stdout().lock();
            let mut writer = BufWriter::with_capacity(64 * 1024, stdout);
            bundle.write_collector_protocol(&mut writer)?;
            writer.flush()?;
            Ok(())
        })?;
        timings.span("collector.release", |_| drop((bundle, builtins)));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CollectionErrorKind;
    use krs_diagnostic::envelope::DiagnosticEnvelope;
    use krs_ir::{PackageId, Sha256Digest, SourceFileId, SourceRange};

    #[test]
    fn sidecar_failure_preserves_the_collection_error() {
        let directory = tempfile::tempdir().unwrap();
        let file = SourceFileId::new(
            PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap(),
            "src/lib.rs",
            Sha256Digest::new("11".repeat(32)).unwrap(),
        )
        .unwrap();
        let error =
            CollectionError::new(CollectionErrorKind::SourceSyntax, "original syntax error")
                .with_source_range(SourceRange::new(file, 7, 16).unwrap());
        let result =
            with_diagnostic_sidecar(Err(RunError::Collection(error.clone())), directory.path());
        let Err(RunError::Collection(retained)) = result else {
            panic!("sidecar failure replaced the collection error");
        };
        assert_eq!(retained, error);
    }

    #[test]
    fn failure_sidecar_round_trip_requires_an_exact_location() {
        let sidecar = tempfile::NamedTempFile::new().unwrap();
        let error =
            CollectionError::new(CollectionErrorKind::UnresolvedTypeReference, "unresolved");
        write_diagnostic(&error, sidecar.path()).unwrap();
        assert!(std::fs::read(sidecar.path()).unwrap().is_empty());
        let file = SourceFileId::new(
            PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap(),
            "src/lib.rs",
            Sha256Digest::new("11".repeat(32)).unwrap(),
        )
        .unwrap();
        let range = SourceRange::new(file, 7, 16).unwrap();
        write_diagnostic(&error.with_source_range(range.clone()), sidecar.path()).unwrap();
        let text = std::fs::read_to_string(sidecar.path()).unwrap();
        let envelopes = DiagnosticEnvelope::from_json_lines(&text).unwrap();
        assert_eq!(envelopes.len(), 1);
        assert_eq!(envelopes[0].stage, DiagnosticStage::Analysis);
        assert_eq!(envelopes[0].code, "krs::collect::unresolved-type-reference");
        assert_eq!(envelopes[0].authored_range, range);
        assert_eq!(envelopes[0].message, "unresolved");
    }
}
