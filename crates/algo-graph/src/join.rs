use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

use k_rust_kore::measure::COUNTER_SCHEMA_VERSION;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};

use crate::{Cost, Edge, Error, Graph};

/// Schema of the canonical run-projection TOML.
pub const JOIN_SCHEMA_VERSION: u32 = 1;

/// The exact rule used to aggregate span observations by algorithm id.
pub const AGGREGATION_RULE: &str = "per algorithm id: invocation count; total duration is the sum of inclusive invocation durations; self duration subtracts direct nested algorithm durations; counter totals are summed across invocations and self counters subtract direct nested algorithm deltas";

/// A static graph joined to one trace and its receipt.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Join {
    pub schema_version: u32,
    pub aggregation_rule: String,
    pub receipt: Receipt,
    pub summary: Summary,
    #[serde(rename = "algorithm", default)]
    pub algorithms: Vec<AlgorithmRun>,
    #[serde(rename = "phase", default)]
    pub phases: Vec<PhaseRun>,
    #[serde(rename = "observed_nest", default)]
    pub observed_nests: Vec<ObservedEdge>,
    #[serde(rename = "observed_contains", default)]
    pub observed_contains: Vec<ObservedContain>,
    #[serde(rename = "receipt_counter", default)]
    pub receipt_counters: Vec<ReceiptCounter>,
    #[serde(rename = "node", default)]
    pub nodes: Vec<NodeRun>,
    #[serde(rename = "edge", default)]
    pub edges: Vec<EdgeRun>,
}

/// Workload identity and schema selection read from the receipt.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Receipt {
    pub directory: String,
    pub workload: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub claim: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timestamp: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub krust_revision: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub binary_sha256: Option<String>,
    pub metadata_schema: String,
    pub timings_schema: String,
    pub current_timings_schema: u32,
    pub timings_partial: bool,
    pub counter_schema: String,
    pub current_counter_schema: u64,
    pub counters_partial: bool,
    pub trace_schema: String,
    #[serde(rename = "tool", default)]
    pub tools: Vec<ToolVersion>,
    #[serde(rename = "revision", default)]
    pub revisions: Vec<Revision>,
}

/// One tool version copied out of `metadata.json`.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ToolVersion {
    pub name: String,
    pub version: String,
}

/// One source revision copied out of `metadata.json`.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Revision {
    pub name: String,
    pub commit: String,
}

/// Run-wide facts which are useful without scanning every algorithm row.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Summary {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub largest_self_time_algorithm: Option<String>,
    pub largest_self_seconds: f64,
    pub declared_algorithms: usize,
    pub exercised_algorithms: usize,
    pub unexercised_backend_algorithms: Vec<String>,
}

/// Static claims and dynamic observations for one stable algorithm id.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct AlgorithmRun {
    pub id: String,
    pub declared: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub area: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span_policy: Option<String>,
    pub count: u64,
    pub total_seconds: f64,
    pub self_seconds: f64,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub cost: Vec<Cost>,
    #[serde(rename = "counter", default, skip_serializing_if = "Vec::is_empty")]
    pub counters: Vec<AlgorithmCounter>,
}

/// One counter beside the algorithm that declares it.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct AlgorithmCounter {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub observation: Option<String>,
    pub declared: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trace_total: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trace_self: Option<u64>,
    /// Receipt-wide value. It is deliberately not attributed to this algorithm because counters
    /// can be declared by more than one card.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub receipt_total: Option<u64>,
}

/// Dynamic observations for one phase identity.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct PhaseRun {
    pub id: String,
    pub declared: bool,
    pub count: u64,
    pub total_seconds: f64,
    pub algorithm_self_seconds: f64,
    pub unattributed_seconds: f64,
}

/// One dynamic parent-child relationship aggregated by stable ids.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
pub struct ObservedEdge {
    pub from: String,
    pub to: String,
    pub count: u64,
}

/// Algorithm time attributed to one containing phase.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ObservedContain {
    pub from: String,
    pub to: String,
    pub count: u64,
    pub total_seconds: f64,
    pub self_seconds: f64,
}

/// One process-wide counter from `counters.json`.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ReceiptCounter {
    pub name: String,
    pub value: u64,
    pub declared_in_graph: bool,
}

/// Exercise status for every static graph node.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct NodeRun {
    pub kind: String,
    pub id: String,
    pub exercised: bool,
    pub evidence: String,
}

/// Exercise status for every static graph edge.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct EdgeRun {
    pub kind: String,
    pub from: String,
    pub to: String,
    pub provenance: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub order: Option<usize>,
    pub exercised: bool,
}

#[derive(Clone, Debug, Default)]
struct Aggregate {
    count: u64,
    total_micros: f64,
    self_micros: f64,
    counters: BTreeMap<String, u64>,
    self_counters: BTreeMap<String, u64>,
}

#[derive(Clone, Debug)]
enum FrameKind {
    Algorithm {
        id: String,
        parent: Option<String>,
        phase: Option<String>,
        child_micros: f64,
        child_counters: BTreeMap<String, u64>,
    },
    Phase {
        name: String,
    },
    Other,
}

#[derive(Clone, Debug)]
struct Frame {
    name: String,
    started: f64,
    kind: FrameKind,
}

#[derive(Clone, Debug, Default)]
struct TraceObservations {
    algorithms: BTreeMap<String, Aggregate>,
    phases: BTreeMap<String, Aggregate>,
    nests: BTreeMap<(String, String), u64>,
    contains: BTreeMap<(String, String), Aggregate>,
    follows: BTreeSet<(String, String)>,
}

#[derive(Debug, Deserialize)]
struct CounterDump {
    version: u64,
    counters: BTreeMap<String, u64>,
}

/// Read the three inputs and project one run onto the static graph.
pub fn join_files(graph: &Path, trace: &Path, receipt: &Path) -> Result<(Graph, Join), Error> {
    let mut graph: Graph = toml::from_str(&fs::read_to_string(graph)?)?;
    graph.sort();
    let events: Value = serde_json::from_str(&fs::read_to_string(trace)?)?;
    let observations = parse_trace(&events)?;
    let (receipt_info, receipt_counters) = read_receipt(receipt)?;
    let joined = project(&graph, observations, receipt_info, receipt_counters);
    Ok((graph, joined))
}

/// Serialize a run projection in its canonical TOML form.
pub fn canonical_join_toml(join: &Join) -> Result<String, Error> {
    let mut output = toml::to_string_pretty(join)?;
    if !output.ends_with('\n') {
        output.push('\n');
    }
    Ok(output)
}

fn parse_trace(document: &Value) -> Result<TraceObservations, Error> {
    let events = match document {
        Value::Array(events) => events,
        Value::Object(root) => root
            .get("traceEvents")
            .and_then(Value::as_array)
            .ok_or_else(|| Error::Invalid("trace object has no traceEvents array".to_owned()))?,
        _ => {
            return Err(Error::Invalid(
                "trace must be an event array or an object with traceEvents".to_owned(),
            ));
        }
    };
    let mut result = TraceObservations::default();
    let mut stacks = BTreeMap::<(String, String), Vec<Frame>>::new();
    let mut phase_sequences = BTreeMap::<(String, String, usize), Vec<String>>::new();

    for (index, event) in events.iter().enumerate() {
        let Some(event) = event.as_object() else {
            return Err(Error::Invalid(format!(
                "trace event {index} is not an object"
            )));
        };
        let Some(kind) = event.get("ph").and_then(Value::as_str) else {
            continue;
        };
        if kind != "B" && kind != "E" {
            continue;
        }
        let key = (
            json_identity(event.get("pid")),
            json_identity(event.get("tid")),
        );
        let timestamp = event
            .get("ts")
            .and_then(Value::as_f64)
            .ok_or_else(|| Error::Invalid(format!("trace event {index} has no numeric ts")))?;
        let args = event
            .get("args")
            .and_then(Value::as_object)
            .cloned()
            .unwrap_or_default();
        let stack = stacks.entry(key.clone()).or_default();

        if kind == "B" {
            let name = event
                .get("name")
                .and_then(Value::as_str)
                .ok_or_else(|| Error::Invalid(format!("begin event {index} has no name")))?
                .to_owned();
            let frame_kind = match name.as_str() {
                "algo" => {
                    let id = string_arg(&args, "id", index)?;
                    let parent = stack.iter().rev().find_map(|frame| match &frame.kind {
                        FrameKind::Algorithm { id, .. } => Some(id.clone()),
                        _ => None,
                    });
                    let phase = stack.iter().rev().find_map(|frame| match &frame.kind {
                        FrameKind::Phase { name } => Some(name.clone()),
                        _ => None,
                    });
                    if let Some(parent) = &parent {
                        checked_increment(&mut result.nests, (parent.clone(), id.clone()))?;
                    }
                    FrameKind::Algorithm {
                        id,
                        parent,
                        phase,
                        child_micros: 0.0,
                        child_counters: BTreeMap::new(),
                    }
                }
                "phase" => {
                    let phase = string_arg(&args, "name", index)?;
                    let depth = stack
                        .iter()
                        .filter(|frame| matches!(frame.kind, FrameKind::Phase { .. }))
                        .count();
                    phase_sequences
                        .entry((key.0.clone(), key.1.clone(), depth))
                        .or_default()
                        .push(phase.clone());
                    FrameKind::Phase { name: phase }
                }
                _ => FrameKind::Other,
            };
            stack.push(Frame {
                name,
                started: timestamp,
                kind: frame_kind,
            });
            continue;
        }

        let mut frame = stack
            .pop()
            .ok_or_else(|| Error::Invalid(format!("end event {index} has no matching begin")))?;
        let event_name = event.get("name").and_then(Value::as_str).unwrap_or("");
        if !event_name.is_empty() && event_name != frame.name {
            return Err(Error::Invalid(format!(
                "end event {index} closes {event_name}, but {} is open",
                frame.name
            )));
        }
        let duration = timestamp - frame.started;
        if duration < 0.0 {
            return Err(Error::Invalid(format!(
                "end event {index} precedes its begin event"
            )));
        }
        match &mut frame.kind {
            FrameKind::Algorithm {
                id,
                parent,
                phase,
                child_micros,
                child_counters,
            } => {
                let counters = parse_counter_args(&args, index)?;
                let aggregate = result.algorithms.entry(id.clone()).or_default();
                aggregate.count = aggregate
                    .count
                    .checked_add(1)
                    .ok_or_else(|| Error::Invalid("algorithm count overflow".to_owned()))?;
                aggregate.total_micros += duration;
                aggregate.self_micros += (duration - *child_micros).max(0.0);
                add_counters(&mut aggregate.counters, &counters)?;
                for (name, value) in &counters {
                    let child = child_counters.get(name).copied().unwrap_or(0);
                    checked_add(
                        &mut aggregate.self_counters,
                        name,
                        value.saturating_sub(child),
                    )?;
                }
                if let Some(phase) = phase {
                    let contained = result
                        .contains
                        .entry((phase.clone(), id.clone()))
                        .or_default();
                    contained.count = contained
                        .count
                        .checked_add(1)
                        .ok_or_else(|| Error::Invalid("containment count overflow".to_owned()))?;
                    contained.total_micros += duration;
                    contained.self_micros += (duration - *child_micros).max(0.0);
                }
                if let Some(parent) = parent
                    && let Some((parent_child_micros, parent_child_counters)) = stack
                        .iter_mut()
                        .rev()
                        .find_map(|open| match &mut open.kind {
                            FrameKind::Algorithm {
                                id,
                                child_micros,
                                child_counters,
                                ..
                            } if id == parent => Some((child_micros, child_counters)),
                            _ => None,
                        })
                {
                    *parent_child_micros += duration;
                    add_counters(parent_child_counters, &counters)?;
                }
                let _ = phase;
            }
            FrameKind::Phase { name } => {
                let aggregate = result.phases.entry(name.clone()).or_default();
                aggregate.count = aggregate
                    .count
                    .checked_add(1)
                    .ok_or_else(|| Error::Invalid("phase count overflow".to_owned()))?;
                aggregate.total_micros += duration;
                aggregate.self_micros += duration;
            }
            FrameKind::Other => {}
        }
    }
    if let Some((thread, stack)) = stacks.iter().find(|(_, stack)| !stack.is_empty()) {
        return Err(Error::Invalid(format!(
            "trace ends with {} open span(s) on process/thread {thread:?}",
            stack.len()
        )));
    }
    for sequence in phase_sequences.values() {
        for pair in sequence.windows(2) {
            result.follows.insert((pair[0].clone(), pair[1].clone()));
        }
    }
    Ok(result)
}

fn string_arg(args: &Map<String, Value>, name: &str, index: usize) -> Result<String, Error> {
    args.get(name)
        .and_then(Value::as_str)
        .map(ToOwned::to_owned)
        .ok_or_else(|| Error::Invalid(format!("trace event {index} has no string args.{name}")))
}

fn parse_counter_args(
    args: &Map<String, Value>,
    index: usize,
) -> Result<BTreeMap<String, u64>, Error> {
    let Some(value) = args.get("counters") else {
        return Ok(BTreeMap::new());
    };
    match value {
        Value::String(encoded) => serde_json::from_str(encoded).map_err(Error::from),
        Value::Object(_) => serde_json::from_value(value.clone()).map_err(Error::from),
        Value::Null => Ok(BTreeMap::new()),
        _ => Err(Error::Invalid(format!(
            "trace event {index} has invalid args.counters"
        ))),
    }
}

fn json_identity(value: Option<&Value>) -> String {
    value.map_or_else(|| "null".to_owned(), Value::to_string)
}

fn checked_increment<K: Ord + Clone>(map: &mut BTreeMap<K, u64>, key: K) -> Result<(), Error> {
    let value = map.entry(key).or_default();
    *value = value
        .checked_add(1)
        .ok_or_else(|| Error::Invalid("observation count overflow".to_owned()))?;
    Ok(())
}

fn checked_add(map: &mut BTreeMap<String, u64>, name: &str, addition: u64) -> Result<(), Error> {
    let value = map.entry(name.to_owned()).or_default();
    *value = value
        .checked_add(addition)
        .ok_or_else(|| Error::Invalid(format!("counter {name} overflow")))?;
    Ok(())
}

fn add_counters(
    target: &mut BTreeMap<String, u64>,
    additions: &BTreeMap<String, u64>,
) -> Result<(), Error> {
    for (name, value) in additions {
        checked_add(target, name, *value)?;
    }
    Ok(())
}

fn read_receipt(receipt: &Path) -> Result<(Receipt, BTreeMap<String, u64>), Error> {
    let metadata: Value =
        serde_json::from_str(&fs::read_to_string(receipt.join("metadata.json"))?)?;
    let metadata = metadata
        .as_object()
        .ok_or_else(|| Error::Invalid("metadata.json is not an object".to_owned()))?;
    let workload = metadata
        .get("workload")
        .and_then(Value::as_str)
        .unwrap_or("unknown")
        .to_owned();
    let metadata_schema = schema_label(metadata.get("version"), "unversioned")?;
    let timings_path = receipt.join("timings.json");
    let (timings_schema, timings_partial) = if timings_path.exists() {
        let timings: Value = serde_json::from_str(&fs::read_to_string(&timings_path)?)?;
        let timings = timings
            .as_object()
            .ok_or_else(|| Error::Invalid("timings.json is not an object".to_owned()))?;
        (
            schema_label(timings.get("version"), "pre-versioned")?,
            timings.get("version").and_then(Value::as_u64)
                != Some(u64::from(k_rust::timings::TIMINGS_SCHEMA_VERSION)),
        )
    } else {
        ("missing".to_owned(), true)
    };
    let counters_path = receipt.join("counters.json");
    let (counter_schema, counters_partial, counters) = if counters_path.exists() {
        let dump: CounterDump = serde_json::from_str(&fs::read_to_string(counters_path)?)?;
        (
            dump.version.to_string(),
            dump.version != COUNTER_SCHEMA_VERSION,
            dump.counters,
        )
    } else {
        ("missing".to_owned(), true, BTreeMap::new())
    };
    let tools = metadata
        .get("tools")
        .and_then(Value::as_object)
        .into_iter()
        .flat_map(|tools| tools.iter())
        .map(|(name, version)| ToolVersion {
            name: name.clone(),
            version: scalar_text(version),
        })
        .collect();
    let revisions = metadata
        .get("revisions")
        .and_then(Value::as_object)
        .into_iter()
        .flat_map(|revisions| revisions.iter())
        .filter_map(|(name, revision)| {
            revision.as_str().map(|commit| Revision {
                name: name.clone(),
                commit: commit.to_owned(),
            })
        })
        .collect();
    let info = Receipt {
        directory: receipt.to_string_lossy().replace('\\', "/"),
        workload,
        claim: optional_string(metadata.get("claim")),
        timestamp: optional_string(metadata.get("timestamp")),
        krust_revision: metadata
            .get("revisions")
            .and_then(Value::as_object)
            .and_then(|revisions| optional_string(revisions.get("krust"))),
        binary_sha256: metadata
            .get("binary")
            .and_then(Value::as_object)
            .and_then(|binary| optional_string(binary.get("sha256"))),
        metadata_schema,
        timings_schema,
        current_timings_schema: k_rust::timings::TIMINGS_SCHEMA_VERSION,
        timings_partial,
        counter_schema,
        current_counter_schema: COUNTER_SCHEMA_VERSION,
        counters_partial,
        trace_schema: "chrome-trace-event-B/E".to_owned(),
        tools,
        revisions,
    };
    Ok((info, counters))
}

fn schema_label(version: Option<&Value>, absent: &str) -> Result<String, Error> {
    match version {
        None | Some(Value::Null) => Ok(absent.to_owned()),
        Some(Value::Number(version)) => Ok(version.to_string()),
        Some(Value::String(version)) => Ok(version.clone()),
        Some(_) => Err(Error::Invalid("schema version is not scalar".to_owned())),
    }
}

fn scalar_text(value: &Value) -> String {
    value
        .as_str()
        .map_or_else(|| value.to_string(), ToOwned::to_owned)
}

fn optional_string(value: Option<&Value>) -> Option<String> {
    value.filter(|value| !value.is_null()).map(scalar_text)
}

fn project(
    graph: &Graph,
    observations: TraceObservations,
    receipt: Receipt,
    receipt_counter_values: BTreeMap<String, u64>,
) -> Join {
    let node_by_id = graph
        .nodes
        .iter()
        .map(|node| (node.id.as_str(), node))
        .collect::<BTreeMap<_, _>>();
    let observation_names = graph
        .nodes
        .iter()
        .filter(|node| node.kind == "observation")
        .filter_map(|node| {
            node.registry_name
                .as_ref()
                .map(|name| (node.id.clone(), name.clone()))
        })
        .collect::<BTreeMap<_, _>>();
    let mut declared_counters = BTreeMap::<String, Vec<(String, String)>>::new();
    for edge in graph.edges.iter().filter(|edge| edge.kind == "measured-by") {
        if let Some(name) = observation_names.get(&edge.to) {
            declared_counters
                .entry(edge.from.clone())
                .or_default()
                .push((edge.to.clone(), name.clone()));
        }
    }
    let mut algorithm_ids = graph
        .nodes
        .iter()
        .filter(|node| node.kind == "algorithm")
        .map(|node| node.id.clone())
        .collect::<BTreeSet<_>>();
    algorithm_ids.extend(observations.algorithms.keys().cloned());
    let algorithms = algorithm_ids
        .into_iter()
        .map(|id| {
            let node = node_by_id
                .get(id.as_str())
                .filter(|node| node.kind == "algorithm")
                .copied();
            let aggregate = observations
                .algorithms
                .get(&id)
                .cloned()
                .unwrap_or_default();
            let mut counter_names = aggregate
                .counters
                .keys()
                .chain(aggregate.self_counters.keys())
                .cloned()
                .collect::<BTreeSet<_>>();
            if let Some(declared) = declared_counters.get(&id) {
                counter_names.extend(declared.iter().map(|(_, name)| name.clone()));
            }
            let counters = counter_names
                .into_iter()
                .map(|name| {
                    let observation = declared_counters.get(&id).and_then(|declared| {
                        declared
                            .iter()
                            .find(|(_, declared_name)| *declared_name == name)
                            .map(|(observation, _)| observation.clone())
                    });
                    AlgorithmCounter {
                        name: name.clone(),
                        declared: observation.is_some(),
                        observation,
                        trace_total: aggregate.counters.get(&name).copied(),
                        trace_self: aggregate.self_counters.get(&name).copied(),
                        receipt_total: receipt_counter_values.get(&name).copied(),
                    }
                })
                .collect();
            AlgorithmRun {
                id,
                declared: node.is_some(),
                area: node.and_then(|node| node.area.clone()),
                span_policy: node.and_then(|node| node.span.clone()),
                count: aggregate.count,
                total_seconds: aggregate.total_micros / 1_000_000.0,
                self_seconds: aggregate.self_micros / 1_000_000.0,
                cost: node.map_or_else(Vec::new, |node| node.cost.clone()),
                counters,
            }
        })
        .collect::<Vec<_>>();
    let observed_nests = observed_edges(&observations.nests);
    let observed_contains = observations
        .contains
        .iter()
        .map(|((from, to), aggregate)| ObservedContain {
            from: from.clone(),
            to: to.clone(),
            count: aggregate.count,
            total_seconds: aggregate.total_micros / 1_000_000.0,
            self_seconds: aggregate.self_micros / 1_000_000.0,
        })
        .collect::<Vec<_>>();
    let mut phase_ids = graph
        .nodes
        .iter()
        .filter(|node| node.kind == "phase")
        .map(|node| node.id.clone())
        .collect::<BTreeSet<_>>();
    phase_ids.extend(observations.phases.keys().cloned());
    let phases = phase_ids
        .into_iter()
        .map(|id| {
            let aggregate = observations.phases.get(&id).cloned().unwrap_or_default();
            let algorithm_self_micros = observations
                .contains
                .iter()
                .filter(|((phase, _), _)| phase == &id)
                .fold(0.0, |total, (_, algorithm)| total + algorithm.self_micros);
            PhaseRun {
                declared: graph
                    .nodes
                    .iter()
                    .any(|node| node.kind == "phase" && node.id == id),
                id,
                count: aggregate.count,
                total_seconds: aggregate.total_micros / 1_000_000.0,
                algorithm_self_seconds: algorithm_self_micros / 1_000_000.0,
                unattributed_seconds: (aggregate.total_micros - algorithm_self_micros).max(0.0)
                    / 1_000_000.0,
            }
        })
        .collect::<Vec<_>>();
    let receipt_counters = receipt_counter_values
        .iter()
        .map(|(name, value)| ReceiptCounter {
            name: name.clone(),
            value: *value,
            declared_in_graph: observation_names.values().any(|declared| declared == name),
        })
        .collect::<Vec<_>>();
    let base_exercised = graph
        .nodes
        .iter()
        .map(|node| {
            let (exercised, evidence) = match node.kind.as_str() {
                "algorithm" => (
                    observations
                        .algorithms
                        .get(&node.id)
                        .is_some_and(|aggregate| aggregate.count > 0),
                    if node.span.as_deref() == Some("none") {
                        "no-span-policy"
                    } else {
                        "algorithm-span"
                    },
                ),
                "phase" => (
                    observations
                        .phases
                        .get(&node.id)
                        .is_some_and(|aggregate| aggregate.count > 0),
                    "phase-span",
                ),
                "observation" => (
                    node.registry_name.as_ref().is_some_and(|name| {
                        receipt_counter_values
                            .get(name)
                            .is_some_and(|value| *value > 0)
                            || observations.algorithms.values().any(|aggregate| {
                                aggregate.counters.get(name).is_some_and(|value| *value > 0)
                            })
                    }),
                    "counter",
                ),
                _ => (false, "none"),
            };
            (node.id.clone(), (exercised, evidence.to_owned()))
        })
        .collect::<BTreeMap<_, _>>();
    let nodes = graph
        .nodes
        .iter()
        .map(|node| {
            let (mut exercised, mut evidence) = base_exercised
                .get(&node.id)
                .cloned()
                .unwrap_or((false, "none".to_owned()));
            if node.kind == "representation" {
                exercised = graph.edges.iter().any(|edge| {
                    matches!(edge.kind.as_str(), "consumes" | "produces")
                        && (edge.from == node.id || edge.to == node.id)
                        && [edge.from.as_str(), edge.to.as_str()].iter().any(|id| {
                            base_exercised
                                .get(*id)
                                .is_some_and(|(exercised, _)| *exercised)
                        })
                });
                evidence = "adjacent-algorithm".to_owned();
            }
            NodeRun {
                kind: node.kind.clone(),
                id: node.id.clone(),
                exercised,
                evidence,
            }
        })
        .collect::<Vec<_>>();
    let node_exercised = nodes
        .iter()
        .map(|node| (node.id.as_str(), node.exercised))
        .collect::<BTreeMap<_, _>>();
    let edges = graph
        .edges
        .iter()
        .map(|edge| EdgeRun {
            kind: edge.kind.clone(),
            from: edge.from.clone(),
            to: edge.to.clone(),
            provenance: edge.provenance.clone(),
            detail: edge.detail.clone(),
            order: edge.order,
            exercised: edge_exercised(edge, &observations, &observation_names, &node_exercised),
        })
        .collect::<Vec<_>>();
    let largest = algorithms.iter().max_by(|left, right| {
        left.self_seconds
            .total_cmp(&right.self_seconds)
            .then_with(|| right.id.cmp(&left.id))
    });
    let summary = Summary {
        largest_self_time_algorithm: largest
            .filter(|algorithm| algorithm.count > 0)
            .map(|algorithm| algorithm.id.clone()),
        largest_self_seconds: largest
            .filter(|algorithm| algorithm.count > 0)
            .map_or(0.0, |algorithm| algorithm.self_seconds),
        declared_algorithms: algorithms
            .iter()
            .filter(|algorithm| algorithm.declared)
            .count(),
        exercised_algorithms: algorithms
            .iter()
            .filter(|algorithm| algorithm.count > 0)
            .count(),
        unexercised_backend_algorithms: algorithms
            .iter()
            .filter(|algorithm| algorithm.declared)
            .filter(|algorithm| algorithm.area.as_deref() == Some("backend"))
            .filter(|algorithm| algorithm.count == 0)
            .map(|algorithm| algorithm.id.clone())
            .collect(),
    };
    Join {
        schema_version: JOIN_SCHEMA_VERSION,
        aggregation_rule: AGGREGATION_RULE.to_owned(),
        receipt,
        summary,
        algorithms,
        phases,
        observed_nests,
        observed_contains,
        receipt_counters,
        nodes,
        edges,
    }
}

fn observed_edges(edges: &BTreeMap<(String, String), u64>) -> Vec<ObservedEdge> {
    edges
        .iter()
        .map(|((from, to), count)| ObservedEdge {
            from: from.clone(),
            to: to.clone(),
            count: *count,
        })
        .collect()
}

fn edge_exercised(
    edge: &Edge,
    observations: &TraceObservations,
    observation_names: &BTreeMap<String, String>,
    node_exercised: &BTreeMap<&str, bool>,
) -> bool {
    match edge.kind.as_str() {
        "contains" => observations
            .contains
            .contains_key(&(edge.from.clone(), edge.to.clone())),
        "nests" => observations
            .nests
            .contains_key(&(edge.from.clone(), edge.to.clone())),
        "follows" => observations
            .follows
            .contains(&(edge.from.clone(), edge.to.clone())),
        "measured-by" => observation_names.get(&edge.to).is_some_and(|name| {
            observations
                .algorithms
                .get(&edge.from)
                .and_then(|algorithm| algorithm.counters.get(name))
                .is_some_and(|value| *value > 0)
        }),
        "consumes" | "produces" => [edge.from.as_str(), edge.to.as_str()]
            .iter()
            .any(|id| node_exercised.get(id).copied().unwrap_or(false)),
        _ => {
            node_exercised
                .get(edge.from.as_str())
                .copied()
                .unwrap_or(false)
                && node_exercised
                    .get(edge.to.as_str())
                    .copied()
                    .unwrap_or(false)
        }
    }
}

/// Render a complete run overlay. Static cost bounds stay in the algorithm label beside the
/// trace observations, and unexercised nodes and edges are dimmed.
pub fn render_run_overlay(graph: &Graph, join: &Join) -> String {
    let algorithm = join
        .algorithms
        .iter()
        .map(|algorithm| (algorithm.id.as_str(), algorithm))
        .collect::<BTreeMap<_, _>>();
    let phase = join
        .phases
        .iter()
        .map(|phase| (phase.id.as_str(), phase))
        .collect::<BTreeMap<_, _>>();
    let receipt_counter = join
        .receipt_counters
        .iter()
        .map(|counter| (counter.name.as_str(), counter.value))
        .collect::<BTreeMap<_, _>>();
    let status = join
        .nodes
        .iter()
        .map(|node| ((node.kind.as_str(), node.id.as_str()), node.exercised))
        .collect::<BTreeMap<_, _>>();
    let mut nodes = graph.nodes.iter().collect::<Vec<_>>();
    nodes.sort_by(|left, right| (&left.id, &left.kind).cmp(&(&right.id, &right.kind)));
    let ids = nodes
        .iter()
        .enumerate()
        .map(|(index, node)| {
            (
                (node.kind.as_str(), node.id.as_str()),
                format!("n{index:04}"),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let first_id = nodes
        .iter()
        .map(|node| {
            (
                node.id.as_str(),
                ids[&(node.kind.as_str(), node.id.as_str())].as_str(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut output = String::new();
    output.push_str(
        "%% generated by algo-graph join; static bounds and run observations are distinct\n",
    );
    output.push_str("flowchart LR\n");
    for node in &nodes {
        let id = &ids[&(node.kind.as_str(), node.id.as_str())];
        let mut label = escape(&node.id);
        if let Some(run) = algorithm.get(node.id.as_str()) {
            label.push_str(&format!(
                "<br/>count: {} total: {:.6}s self: {:.6}s",
                run.count, run.total_seconds, run.self_seconds
            ));
            for cost in &run.cost {
                label.push_str(&format!(
                    "<br/>bound ({}): {}",
                    escape(&cost.mode),
                    escape(&cost.bound)
                ));
            }
        } else if let Some(run) = phase.get(node.id.as_str()) {
            label.push_str(&format!(
                "<br/>count: {} total: {:.6}s attributed: {:.6}s remainder: {:.6}s",
                run.count, run.total_seconds, run.algorithm_self_seconds, run.unattributed_seconds
            ));
        } else if node.kind == "observation"
            && let Some(value) = node
                .registry_name
                .as_deref()
                .and_then(|name| receipt_counter.get(name))
        {
            label.push_str(&format!("<br/>receipt n: {value}"));
        }
        match node.kind.as_str() {
            "algorithm" => output.push_str(&format!("  {id}([\"{label}\"])\n")),
            "representation" => output.push_str(&format!("  {id}[[\"{label}\"]]\n")),
            "observation" => output.push_str(&format!("  {id}{{{{\"{label}\"}}}}\n")),
            _ => output.push_str(&format!("  {id}[\"{label}\"]\n")),
        }
    }
    let edge_status = join
        .edges
        .iter()
        .map(|edge| {
            (
                (
                    edge.kind.as_str(),
                    edge.from.as_str(),
                    edge.to.as_str(),
                    edge.detail.as_deref(),
                    edge.order,
                ),
                edge.exercised,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut unexercised_links = Vec::new();
    for (index, edge) in graph.edges.iter().enumerate() {
        let Some(from) = first_id.get(edge.from.as_str()) else {
            continue;
        };
        let Some(to) = first_id.get(edge.to.as_str()) else {
            continue;
        };
        output.push_str(&format!(
            "  {from} -->|\"{} [{}]\"| {to}\n",
            escape(&edge.kind),
            escape(&edge.provenance)
        ));
        let exercised = edge_status
            .get(&(
                edge.kind.as_str(),
                edge.from.as_str(),
                edge.to.as_str(),
                edge.detail.as_deref(),
                edge.order,
            ))
            .copied()
            .unwrap_or(false);
        if !exercised {
            unexercised_links.push(index);
        }
    }
    for edge in &join.observed_nests {
        let (Some(from), Some(to)) = (
            first_id.get(edge.from.as_str()),
            first_id.get(edge.to.as_str()),
        ) else {
            continue;
        };
        output.push_str(&format!(
            "  {from} -.->|\"observed nests ×{}\"| {to}\n",
            edge.count
        ));
    }
    output.push_str("  classDef exercised fill:#e5f6e8,stroke:#2f6f3e,color:#17251b\n");
    output.push_str("  classDef unexercised fill:#f1f1f1,stroke:#aaa,color:#999\n");
    let exercised = nodes
        .iter()
        .filter(|node| {
            status
                .get(&(node.kind.as_str(), node.id.as_str()))
                .copied()
                .unwrap_or(false)
        })
        .map(|node| ids[&(node.kind.as_str(), node.id.as_str())].as_str())
        .collect::<Vec<_>>();
    let unexercised = nodes
        .iter()
        .filter(|node| {
            !status
                .get(&(node.kind.as_str(), node.id.as_str()))
                .copied()
                .unwrap_or(false)
        })
        .map(|node| ids[&(node.kind.as_str(), node.id.as_str())].as_str())
        .collect::<Vec<_>>();
    if !exercised.is_empty() {
        output.push_str(&format!("  class {} exercised\n", exercised.join(",")));
    }
    if !unexercised.is_empty() {
        output.push_str(&format!("  class {} unexercised\n", unexercised.join(",")));
    }
    if !unexercised_links.is_empty() {
        output.push_str(&format!(
            "  linkStyle {} stroke:#bbb,color:#999,opacity:0.35\n",
            unexercised_links
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join(",")
        ));
    }
    output
}

fn escape(value: &str) -> String {
    value
        .replace('&', "&amp;")
        .replace('"', "&quot;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('\n', " ")
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;

    fn fixture() -> std::path::PathBuf {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let root = std::env::temp_dir().join(format!(
            "algo-graph-join-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).unwrap();
        root
    }

    #[test]
    fn joins_nested_spans_and_old_receipt_schemas_deterministically() {
        let root = fixture();
        let graph_path = root.join("graph.toml");
        let trace_path = root.join("trace.json");
        let receipt = root.join("receipt");
        fs::create_dir(&receipt).unwrap();
        fs::write(
            &graph_path,
            r#"
[[node]]
kind = "algorithm"
id = "backend.a"
provenance = "declared"
area = "backend"
span = "per call"
[[node.cost]]
mode = "worst-case"
bound = "O(n)"
[node.anchor]
crate = "demo"
file = "a.rs"
symbol = "a"

[[node]]
kind = "algorithm"
id = "backend.b"
provenance = "declared"
area = "backend"
span = "per call"
[node.anchor]
crate = "demo"
file = "b.rs"
symbol = "b"

[[node]]
kind = "algorithm"
id = "backend.unused"
provenance = "declared"
area = "backend"
span = "per call"
[node.anchor]
crate = "demo"
file = "unused.rs"
symbol = "unused"

[[node]]
kind = "phase"
id = "proof"
provenance = "table"
[node.anchor]
crate = "demo"
file = "pipeline.rs"
symbol = "PHASES"

[[node]]
kind = "observation"
id = "CounterA"
provenance = "table"
registry_name = "work.a"
[node.anchor]
crate = "demo"
file = "measure.rs"
symbol = "Counter::A"

[[node]]
kind = "observation"
id = "CounterB"
provenance = "table"
registry_name = "work.b"
[node.anchor]
crate = "demo"
file = "measure.rs"
symbol = "Counter::B"

[[edge]]
kind = "contains"
from = "proof"
to = "backend.a"
provenance = "table"

[[edge]]
kind = "contains"
from = "proof"
to = "backend.b"
provenance = "table"

[[edge]]
kind = "measured-by"
from = "backend.a"
to = "CounterA"
provenance = "declared"

[[edge]]
kind = "measured-by"
from = "backend.b"
to = "CounterB"
provenance = "declared"
"#,
        )
        .unwrap();
        fs::write(
            &trace_path,
            r#"[
{"ph":"i","name":"metadata","ts":0,"pid":1,"tid":1,"args":{"aggregation_rule":"ignored by parser"}},
{"ph":"B","name":"phase","ts":0,"pid":1,"tid":1,"args":{"name":"proof"}},
{"ph":"B","name":"algo","ts":10,"pid":1,"tid":1,"args":{"id":"backend.a"}},
{"ph":"B","name":"algo","ts":20,"pid":1,"tid":1,"args":{"id":"backend.b"}},
{"ph":"E","name":"algo","ts":50,"pid":1,"tid":1,"args":{"counters":"{\"work.b\":3}"}},
{"ph":"E","name":"algo","ts":100,"pid":1,"tid":1,"args":{"counters":"{\"work.a\":10,\"work.b\":3}"}},
{"ph":"E","name":"phase","ts":120,"pid":1,"tid":1}
]"#,
        )
        .unwrap();
        fs::write(
            receipt.join("metadata.json"),
            r#"{"workload":"imp-prove","claim":"sum","timestamp":"now","revisions":{"krust":"abc"},"tools":{"krust":"0.4"}}"#,
        )
        .unwrap();
        fs::write(receipt.join("timings.json"), r#"{"proof_seconds":0.1}"#).unwrap();
        fs::write(
            receipt.join("counters.json"),
            r#"{"format":"krust-counters","version":1,"counters":{"work.a":10,"work.b":3}}"#,
        )
        .unwrap();

        let (graph, join) = join_files(&graph_path, &trace_path, &receipt).unwrap();
        assert_eq!(join.receipt.timings_schema, "pre-versioned");
        assert!(join.receipt.timings_partial);
        assert_eq!(
            join.receipt.current_timings_schema,
            k_rust::timings::TIMINGS_SCHEMA_VERSION
        );
        assert_eq!(join.receipt.counter_schema, "1");
        assert!(join.receipt.counters_partial);
        assert_eq!(
            join.summary.largest_self_time_algorithm.as_deref(),
            Some("backend.a")
        );
        assert_eq!(
            join.summary.unexercised_backend_algorithms,
            ["backend.unused"]
        );
        let a = join
            .algorithms
            .iter()
            .find(|algorithm| algorithm.id == "backend.a")
            .unwrap();
        assert_eq!(a.count, 1);
        assert_eq!(a.total_seconds, 90.0 / 1_000_000.0);
        assert_eq!(a.self_seconds, 60.0 / 1_000_000.0);
        assert_eq!(a.cost[0].bound, "O(n)");
        let b_in_a = a
            .counters
            .iter()
            .find(|counter| counter.name == "work.b")
            .unwrap();
        assert_eq!(b_in_a.trace_total, Some(3));
        assert_eq!(b_in_a.trace_self, Some(0));
        assert_eq!(
            join.observed_nests,
            [ObservedEdge {
                from: "backend.a".to_owned(),
                to: "backend.b".to_owned(),
                count: 1,
            }]
        );
        assert_eq!(join.phases[0].id, "proof");
        assert_eq!(join.phases[0].total_seconds, 120.0 / 1_000_000.0);
        assert_eq!(join.phases[0].algorithm_self_seconds, 90.0 / 1_000_000.0);
        assert_eq!(join.phases[0].unattributed_seconds, 30.0 / 1_000_000.0);
        assert_eq!(join.observed_contains.len(), 2);
        let first = canonical_join_toml(&join).unwrap();
        let second = canonical_join_toml(&join).unwrap();
        assert_eq!(first, second);
        assert_eq!(toml::from_str::<Join>(&first).unwrap(), join);
        let overlay = render_run_overlay(&graph, &join);
        assert!(overlay.contains("bound (worst-case): O(n)"));
        assert!(overlay.contains("receipt n: 10"));
        assert!(overlay.contains("observed nests ×1"));
        assert!(overlay.contains("unexercised"));

        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn rejects_mismatched_begin_end_events() {
        let error = parse_trace(&serde_json::json!([
            {"ph":"B","name":"algo","ts":0,"pid":1,"tid":1,"args":{"id":"backend.a"}},
            {"ph":"E","name":"phase","ts":1,"pid":1,"tid":1}
        ]))
        .unwrap_err();
        assert!(error.to_string().contains("closes phase, but algo is open"));
    }
}
