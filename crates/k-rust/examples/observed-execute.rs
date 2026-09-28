//! Cargo example that measures the public observed backend API.
//!
//! Build with `with-z3-static-4.16.0 cargo build --profile profiling -p k-rust
//! --no-default-features --features cli,measure --example observed-execute --locked`.

use std::{
    env,
    fs::{self, File},
    io::{self, BufWriter, Write},
    path::PathBuf,
};

use k_rust::backend::{Backend, BackendOptions, ExecuteRequest, ObservedRequest};
use k_rust_kore::{measure, trace_aggregate::SpanAggregator};
use serde_json::Value;

#[global_allocator]
static ALLOCATOR: measure::CountingAllocator = measure::CountingAllocator;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = env::args().skip(1);
    let mut definition = None;
    let mut module = None;
    let mut request = None;
    let mut depth = None;
    let mut timings = None;
    let mut trace_aggregate = None;
    let mut response_mode = String::from("writer");
    while let Some(option) = args.next() {
        let value = args.next().ok_or(format!("missing value for {option}"))?;
        match option.as_str() {
            "--definition" => definition = Some(PathBuf::from(value)),
            "--module" => module = Some(value),
            "--request" => request = Some(PathBuf::from(value)),
            "--depth" => depth = Some(value.parse::<u64>()?),
            "--timings" => timings = Some(PathBuf::from(value)),
            "--trace-aggregate" => trace_aggregate = Some(PathBuf::from(value)),
            "--response-mode" => response_mode = value,
            _ => return Err(format!("unknown option {option}").into()),
        }
    }
    let definition = definition.ok_or("missing --definition")?;
    let module = module.ok_or("missing --module")?;
    let request = request.ok_or("missing --request")?;
    let depth = depth.ok_or("missing --depth")?;

    let result = (|| -> Result<(), Box<dyn std::error::Error>> {
        let envelope: Value = serde_json::from_reader(File::open(request)?)?;
        let state = envelope
            .pointer("/params/state")
            .ok_or("request has no params.state")?
            .clone();
        let mut backend = Backend::new(
            &fs::read_to_string(definition)?,
            module,
            BackendOptions::default(),
        )?;
        let request = ObservedRequest {
            request: ExecuteRequest {
                state,
                max_depth: Some(depth),
                ..ExecuteRequest::default()
            },
            rules: None,
        };
        match response_mode.as_str() {
            "writer" => {
                backend.execute_observed_to_writer(request, BufWriter::new(io::stdout().lock()))?
            }
            "string" => io::stdout()
                .lock()
                .write_all(backend.execute_observed_json(request)?.as_bytes())?,
            _ => return Err(format!("unknown response mode {response_mode}").into()),
        }
        Ok(())
    })();

    if let Some(path) = env::var_os("KRUST_COUNTERS") {
        let mut snapshot = measure::process_snapshot();
        measure::set_allocation_counters(&mut snapshot);
        let counters = snapshot
            .iter()
            .map(|(name, value)| (name.to_owned(), Value::from(value)))
            .collect::<serde_json::Map<String, Value>>();
        let dump = serde_json::json!({
            "format": "krust-counters",
            "version": measure::COUNTER_SCHEMA_VERSION,
            "counters": counters,
        });
        fs::write(path, serde_json::to_vec(&dump)?)?;
    }
    if let Some(path) = timings {
        // No CLI pipeline phases are run by this library driver.
        fs::write(path, b"{}")?;
    }
    if let Some(path) = trace_aggregate {
        let aggregate = SpanAggregator::default().finish()?;
        fs::write(
            path,
            serde_json::to_vec(&aggregate.to_json("algo-receipt"))?,
        )?;
    }
    result
}
