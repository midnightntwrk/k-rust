//! The body of a generated production collector executable.

use std::error::Error;
use std::io::Write as _;
use std::path::PathBuf;

use krs_ir::measure::{
    COLLECTOR_MEASURE_ENV, COLLECTOR_MEASURE_SCHEMA, CollectorMeasureDocument, Counters, Timings,
    unix_seconds,
};
use krs_ir::{HostBuiltinRegistry, HostDescriptor};

use super::{PackageContext, collect_host_descriptors_with_builtins_timed};

/// Collect the host descriptors of `contexts` and write the canonical
/// descriptor bundle JSON to stdout.
///
/// Generated collectors call this once from `main`. When `krs` sets
/// [`COLLECTOR_MEASURE_ENV`] to a path, the collector also records its phases
/// and counters there as a `krs-collector-measure/1` document, on success and
/// on failure; stdout carries exactly the same bytes either way.
///
/// # Errors
///
/// Returns collection, serialization, stdout, or sidecar-write failures.
pub fn run_collector<I>(
    contexts: Vec<PackageContext>,
    descriptors: impl FnOnce() -> I,
    builtins: impl FnOnce() -> HostBuiltinRegistry,
) -> Result<(), Box<dyn Error>>
where
    I: IntoIterator<Item = HostDescriptor>,
{
    let sidecar = std::env::var_os(COLLECTOR_MEASURE_ENV).map(PathBuf::from);
    let Some(sidecar) = sidecar else {
        return collect_and_write(
            contexts,
            descriptors,
            builtins,
            &mut Timings::disabled(),
            &mut Counters::disabled(),
        );
    };
    let started_unix_seconds = unix_seconds();
    let mut timings = Timings::enabled();
    let mut counters = Counters::enabled();
    let result = collect_and_write(contexts, descriptors, builtins, &mut timings, &mut counters);
    let document = CollectorMeasureDocument {
        schema: COLLECTOR_MEASURE_SCHEMA.to_owned(),
        started_unix_seconds,
        spans: timings.take_spans(),
        counters: counters.values().clone(),
    };
    let written = serde_json::to_vec_pretty(&document)
        .map_err(Box::<dyn Error>::from)
        .and_then(|bytes| std::fs::write(&sidecar, bytes).map_err(Into::into));
    result?;
    written.map_err(|error| {
        format!(
            "could not write collector measurement `{}`: {error}",
            sidecar.display()
        )
        .into()
    })
}

fn collect_and_write<I>(
    contexts: Vec<PackageContext>,
    descriptors: impl FnOnce() -> I,
    builtins: impl FnOnce() -> HostBuiltinRegistry,
    timings: &mut Timings,
    counters: &mut Counters,
) -> Result<(), Box<dyn Error>>
where
    I: IntoIterator<Item = HostDescriptor>,
{
    let descriptors = timings.span("collector.factories", |_| {
        descriptors().into_iter().collect::<Vec<_>>()
    });
    counters.set("collector.host_descriptors", descriptors.len());
    let builtins = timings.span("collector.builtins", |_| builtins());
    let bundle = timings.try_span("collector.resolve", |timings| {
        collect_host_descriptors_with_builtins_timed(contexts, descriptors, &builtins, timings)
    })?;
    let json = timings.try_span("collector.serialize", |_| {
        if counters.is_enabled() {
            let (bytes, provenance) = bundle.to_canonical_json_measured()?;
            counters.set("bundle.provenance_bytes", provenance);
            Ok(bytes)
        } else {
            bundle.to_canonical_json().map(String::into_bytes)
        }
    })?;
    timings.try_span("collector.write", |_| {
        let mut stdout = std::io::stdout().lock();
        stdout.write_all(&json)?;
        stdout.flush()
    })?;
    timings.span("collector.release", |_| drop((bundle, json, builtins)));
    Ok(())
}
