use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path},
};

use k_rust_kore::measure::COUNTER_SCHEMA_VERSION;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};

use crate::{Cost, Edge, Error, Graph};

/// Schema of the canonical run-projection TOML.
pub const JOIN_SCHEMA_VERSION: u32 = 2;

/// The exact rule used to aggregate span observations by algorithm id.
pub const AGGREGATION_RULE: &str = "per algorithm id: invocation count; total duration is the sum of inclusive invocation durations, where an invocation nested inside an open invocation of the same id (recursion) adds nothing because the outermost one already includes it; self duration subtracts direct nested algorithm durations; counter totals are summed across invocations with the same recursion rule and self counters subtract direct nested algorithm deltas";

/// How a run's evidence decides each node's verdict; [`edge_verdict_rule`] gives the edge rules.
pub const VERDICT_RULE: &str = "each node and edge is ran, not-run, or unknown: a positive observation proves presence, and absence proves absence only where the instrumentation would have recorded it. An algorithm ran when its own span opened and is unknown otherwise: some entries do an algorithm's work without opening its span, so a zero span count proves nothing, and a counter is incremented wherever its code runs, so a moved counter is not attributed to the card that declares it. A phase ran when its span opened or the receipt's timings list names it, and did not run when neither holds and the receipt has a current-schema timings list. A counter ran when it moved and did not run when a current-schema dump records it at zero. Representations, contracts, and registries are unknown: nothing records them. Span policies are those of the joined graph, which must be generated at the receipt's commit";

/// What one run's evidence establishes about a node or an edge.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Verdict {
    /// A positive observation shows that it happened in the run.
    Ran,
    /// Instrumentation that would have recorded it recorded nothing.
    NotRun,
    /// The run's evidence cannot tell.
    Unknown,
}

impl Verdict {
    /// The serialized name: `ran`, `not-run`, or `unknown`.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Ran => "ran",
            Self::NotRun => "not-run",
            Self::Unknown => "unknown",
        }
    }
}

/// A static graph joined to one trace and its receipt.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Join {
    pub schema_version: u32,
    pub aggregation_rule: String,
    /// [`VERDICT_RULE`] at the time of the join.
    pub verdict_rule: String,
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
    /// Declared algorithms by verdict; the three counts sum to `declared_algorithms`.
    pub ran_algorithms: usize,
    pub not_run_algorithms: usize,
    pub unknown_algorithms: usize,
    pub not_run_backend_algorithms: Vec<String>,
    pub unknown_backend_algorithms: Vec<String>,
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

/// The verdict for every static graph node.
///
/// `evidence` names the fact that decided the verdict. Algorithms: `span` (ran), `zero-span`,
/// `unobservable`, `counter-moved`, `counter-idle` (unknown). Phases:
/// `span`, `timings` (ran), `absent` (not-run), `unrecorded` (unknown). Counters: `counter`
/// (ran), `counter-zero` (not-run), `counter-unrecorded` (unknown). Every other node kind:
/// `unobserved` (unknown). `reason` states the same fact with the run's values.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct NodeRun {
    pub kind: String,
    pub id: String,
    pub verdict: Verdict,
    pub evidence: String,
    pub reason: String,
}

/// The verdict for every static graph edge.
///
/// `evidence` is `observed` (ran), `endpoint-not-run` (not-run), or `unobserved` (unknown);
/// [`edge_verdict_rule`] states the rule per kind.
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
    pub verdict: Verdict,
    pub evidence: String,
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
        serial: usize,
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
pub(crate) struct TraceObservations {
    algorithms: BTreeMap<String, Aggregate>,
    phases: BTreeMap<String, Aggregate>,
    nests: BTreeMap<(String, String), u64>,
    contains: BTreeMap<(String, String), Aggregate>,
    /// (phase, algorithm) for every algorithm span opened inside a phase span at any depth.
    within: BTreeSet<(String, String)>,
    follows: BTreeSet<(String, String)>,
}

#[derive(Debug, Deserialize)]
struct CounterDump {
    version: u64,
    counters: BTreeMap<String, u64>,
}

/// Read the three inputs and project one run onto the static graph.
///
/// `root` is the workspace root; the receipt directory is recorded relative to it.
pub fn join_files(
    root: &Path,
    graph: &Path,
    trace: &Path,
    receipt: &Path,
) -> Result<(Graph, Join), Error> {
    let mut graph: Graph = toml::from_str(&fs::read_to_string(graph)?)?;
    graph.sort();
    let events: Value = serde_json::from_str(&fs::read_to_string(trace)?)?;
    let observations = parse_trace(&events)?;
    let (mut receipt_info, receipt_counters, timings_phases) = read_receipt(receipt)?;
    receipt_info.directory = receipt_directory(root, receipt);
    let joined = project_with_timings(
        &graph,
        observations,
        receipt_info,
        receipt_counters,
        timings_phases,
    );
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

pub(crate) fn parse_trace(document: &Value) -> Result<TraceObservations, Error> {
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
    // Sibling phases are sequenced under their enclosing phase instance (None at top level).
    let mut phase_sequences = BTreeMap::<(String, String, Option<usize>), Vec<String>>::new();

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
                        FrameKind::Phase { name, .. } => Some(name.clone()),
                        _ => None,
                    });
                    if let Some(parent) = &parent {
                        checked_increment(&mut result.nests, (parent.clone(), id.clone()))?;
                    }
                    for frame in stack.iter() {
                        if let FrameKind::Phase { name, .. } = &frame.kind {
                            result.within.insert((name.clone(), id.clone()));
                        }
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
                    let parent = stack.iter().rev().find_map(|frame| match &frame.kind {
                        FrameKind::Phase { serial, .. } => Some(*serial),
                        _ => None,
                    });
                    phase_sequences
                        .entry((key.0.clone(), key.1.clone(), parent))
                        .or_default()
                        .push(phase.clone());
                    FrameKind::Phase {
                        name: phase,
                        serial: index,
                    }
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
                // A recursive invocation lies inside an open invocation of the same id, whose
                // inclusive duration and counter delta already contain it.
                let recursive = stack.iter().any(|open| {
                    matches!(&open.kind, FrameKind::Algorithm { id: open_id, .. } if open_id == id)
                });
                let recursive_in_phase = stack.iter().any(|open| {
                    matches!(
                        &open.kind,
                        FrameKind::Algorithm { id: open_id, phase: open_phase, .. }
                            if open_id == id && open_phase == phase
                    )
                });
                let aggregate = result.algorithms.entry(id.clone()).or_default();
                aggregate.count = aggregate
                    .count
                    .checked_add(1)
                    .ok_or_else(|| Error::Invalid("algorithm count overflow".to_owned()))?;
                if !recursive {
                    aggregate.total_micros += duration;
                    add_counters(&mut aggregate.counters, &counters)?;
                }
                aggregate.self_micros += (duration - *child_micros).max(0.0);
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
                    if !recursive_in_phase {
                        contained.total_micros += duration;
                    }
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
            FrameKind::Phase { name, .. } => {
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

/// The receipt identity, its counter dump, and the phase names of a current-schema timings list.
type ReceiptFiles = (Receipt, BTreeMap<String, u64>, Option<BTreeSet<String>>);

fn read_receipt(receipt: &Path) -> Result<ReceiptFiles, Error> {
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
    let (timings_schema, timings_partial, timings_phases) = if timings_path.exists() {
        let timings: Value = serde_json::from_str(&fs::read_to_string(&timings_path)?)?;
        let timings = timings
            .as_object()
            .ok_or_else(|| Error::Invalid("timings.json is not an object".to_owned()))?;
        let partial = timings.get("version").and_then(Value::as_u64)
            != Some(u64::from(k_rust::timings::TIMINGS_SCHEMA_VERSION));
        let phases = timings
            .get("phases")
            .and_then(Value::as_array)
            .filter(|_| !partial)
            .map(|phases| {
                phases
                    .iter()
                    .filter_map(|phase| phase.get("name").and_then(Value::as_str))
                    .map(ToOwned::to_owned)
                    .collect::<BTreeSet<_>>()
            });
        (
            schema_label(timings.get("version"), "pre-versioned")?,
            partial,
            phases,
        )
    } else {
        ("missing".to_owned(), true, None)
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
    Ok((info, counters, timings_phases))
}

/// The receipt directory relative to the workspace root, or its last two components (the
/// `evidence/<workload>/<commit>` shape) when it lies outside the root; never an absolute path.
fn receipt_directory(root: &Path, receipt: &Path) -> String {
    let absolute = if receipt.is_absolute() {
        receipt.to_owned()
    } else {
        std::env::current_dir()
            .map(|directory| directory.join(receipt))
            .unwrap_or_else(|_| receipt.to_owned())
    };
    let absolute = fs::canonicalize(&absolute).unwrap_or(absolute);
    let root = fs::canonicalize(root).unwrap_or_else(|_| root.to_owned());
    let normal = |path: &Path| {
        path.components()
            .filter_map(|component| match component {
                Component::Normal(part) => Some(part.to_string_lossy().into_owned()),
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    if let Ok(relative) = absolute.strip_prefix(&root) {
        let parts = normal(relative);
        return if parts.is_empty() {
            ".".to_owned()
        } else {
            parts.join("/")
        };
    }
    let parts = normal(&absolute);
    parts[parts.len().saturating_sub(2)..].join("/")
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

/// Project a run whose receipt holds no timings phase list.
#[cfg(test)]
pub(crate) fn project(
    graph: &Graph,
    observations: TraceObservations,
    receipt: Receipt,
    receipt_counter_values: BTreeMap<String, u64>,
) -> Join {
    project_with_timings(graph, observations, receipt, receipt_counter_values, None)
}

pub(crate) fn project_with_timings(
    graph: &Graph,
    observations: TraceObservations,
    receipt: Receipt,
    receipt_counter_values: BTreeMap<String, u64>,
    timings_phases: Option<BTreeSet<String>>,
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
    let mut declarers = BTreeMap::<&str, BTreeSet<&str>>::new();
    for (algorithm, declared) in &declared_counters {
        for (_, name) in declared {
            declarers
                .entry(name.as_str())
                .or_default()
                .insert(algorithm.as_str());
        }
    }
    let facts = RunFacts {
        observations: &observations,
        receipt_counters: &receipt_counter_values,
        counters_current: !receipt.counters_partial,
        timings_phases: timings_phases.as_ref(),
        declarers: &declarers,
    };
    let nodes = graph
        .nodes
        .iter()
        .map(|node| {
            let decided = match node.kind.as_str() {
                "algorithm" => facts.algorithm(node, declared_counters.get(&node.id)),
                "phase" => facts.phase(&node.id),
                "observation" => facts.observation(node),
                kind => Decided::unknown(
                    "unobserved",
                    format!("no instrumentation records a {kind} node"),
                ),
            };
            NodeRun {
                kind: node.kind.clone(),
                id: node.id.clone(),
                verdict: decided.verdict,
                evidence: decided.evidence.to_owned(),
                reason: decided.reason,
            }
        })
        .collect::<Vec<_>>();
    let node_verdicts = nodes
        .iter()
        .map(|node| (node.id.as_str(), node.verdict))
        .collect::<BTreeMap<_, _>>();
    let edges = graph
        .edges
        .iter()
        .map(|edge| {
            let (verdict, evidence) = facts.edge(edge, &observation_names, &node_verdicts);
            EdgeRun {
                kind: edge.kind.clone(),
                from: edge.from.clone(),
                to: edge.to.clone(),
                provenance: edge.provenance.clone(),
                detail: edge.detail.clone(),
                order: edge.order,
                verdict,
                evidence: evidence.to_owned(),
            }
        })
        .collect::<Vec<_>>();
    let largest = algorithms.iter().max_by(|left, right| {
        left.self_seconds
            .total_cmp(&right.self_seconds)
            .then_with(|| right.id.cmp(&left.id))
    });
    let declared_verdicts = nodes
        .iter()
        .filter(|node| node.kind == "algorithm")
        .collect::<Vec<_>>();
    let count_verdict = |verdict: Verdict| {
        declared_verdicts
            .iter()
            .filter(|node| node.verdict == verdict)
            .count()
    };
    let backend_with = |verdict: Verdict| {
        algorithms
            .iter()
            .filter(|algorithm| algorithm.declared && algorithm.area.as_deref() == Some("backend"))
            .filter(|algorithm| node_verdicts.get(algorithm.id.as_str()) == Some(&verdict))
            .map(|algorithm| algorithm.id.clone())
            .collect::<Vec<_>>()
    };
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
        ran_algorithms: count_verdict(Verdict::Ran),
        not_run_algorithms: count_verdict(Verdict::NotRun),
        unknown_algorithms: count_verdict(Verdict::Unknown),
        not_run_backend_algorithms: backend_with(Verdict::NotRun),
        unknown_backend_algorithms: backend_with(Verdict::Unknown),
    };
    Join {
        schema_version: JOIN_SCHEMA_VERSION,
        aggregation_rule: AGGREGATION_RULE.to_owned(),
        verdict_rule: VERDICT_RULE.to_owned(),
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

/// The facts of one run that verdicts are decided from.
struct RunFacts<'a> {
    observations: &'a TraceObservations,
    receipt_counters: &'a BTreeMap<String, u64>,
    /// The receipt holds a counter dump at the current schema, so a counter absent from a span's
    /// delta or zero in the dump did not move, and spans carry counter deltas.
    counters_current: bool,
    /// Phase names in the receipt's `timings.json` `phases` list; `None` when the receipt has no
    /// such list at the current timings schema.
    timings_phases: Option<&'a BTreeSet<String>>,
    /// Counter registry name to the algorithms whose cards declare it.
    declarers: &'a BTreeMap<&'a str, BTreeSet<&'a str>>,
}

/// A verdict with the evidence code and sentence that decided it.
struct Decided {
    verdict: Verdict,
    evidence: &'static str,
    reason: String,
}

impl Decided {
    fn ran(evidence: &'static str, reason: String) -> Self {
        Self {
            verdict: Verdict::Ran,
            evidence,
            reason,
        }
    }

    fn not_run(evidence: &'static str, reason: String) -> Self {
        Self {
            verdict: Verdict::NotRun,
            evidence,
            reason,
        }
    }

    fn unknown(evidence: &'static str, reason: String) -> Self {
        Self {
            verdict: Verdict::Unknown,
            evidence,
            reason,
        }
    }
}

/// What the run recorded for one counter.
enum CounterState {
    /// Positive in the receipt dump or in some algorithm span's delta.
    Moved(u64),
    /// Zero in a counter dump at the current schema.
    Zero,
    /// The receipt holds no current-schema value and no span saw it move.
    Unrecorded,
}

impl RunFacts<'_> {
    fn counter(&self, name: &str) -> CounterState {
        let in_spans = self
            .observations
            .algorithms
            .values()
            .filter_map(|aggregate| aggregate.counters.get(name))
            .copied()
            .max()
            .unwrap_or(0);
        match self.receipt_counters.get(name).copied() {
            Some(value) if value > 0 => CounterState::Moved(value),
            _ if in_spans > 0 => CounterState::Moved(in_spans),
            Some(_) if self.counters_current => CounterState::Zero,
            _ => CounterState::Unrecorded,
        }
    }

    /// An algorithm ran when its own span opened; nothing else decides a verdict.
    ///
    /// A zero span count does not prove that it did not run: the source gate checks that some
    /// site file opens the span, not that every entry does, and entries that do the work without
    /// the span exist (the prelude check calls `Z3Solver::solve_uncached` directly, and predicate
    /// simplification calls `simplify_with_budget` outside the term span). Counters decide
    /// nothing either: a counter is incremented wherever its code runs, which can lie outside the
    /// declaring algorithm even when one card alone declares it (`provenance.receipt_renders`
    /// moves inside `parser.grammar.build` spans), and a counter that counts part of the work can
    /// stay zero while the algorithm runs.
    fn algorithm(&self, node: &crate::Node, declared: Option<&Vec<(String, String)>>) -> Decided {
        let count = self
            .observations
            .algorithms
            .get(&node.id)
            .map_or(0, |aggregate| aggregate.count);
        if count > 0 {
            return Decided::ran("span", format!("its span opened {count} times"));
        }
        let policy = node.span.as_deref().unwrap_or("absent");
        if matches!(policy, "per call" | "per problem") {
            return Decided::unknown(
                "zero-span",
                format!(
                    "span policy {policy} and its span never opened, but not every entry opens the span, so a zero count does not show that it did not run"
                ),
            );
        }
        let declared = declared.map(Vec::as_slice).unwrap_or_default();
        if declared.is_empty() {
            return Decided::unknown(
                "unobservable",
                format!(
                    "span policy {policy} and no declared counter, so no run can show whether it ran"
                ),
            );
        }
        let describe = |name: &str, value: Option<u64>| {
            let cards = self.declarers.get(name).map_or(0, BTreeSet::len);
            let value = value.map_or_else(|| "unrecorded".to_owned(), |value| value.to_string());
            if cards > 1 {
                format!("{name} = {value} (declared by {cards} cards)")
            } else {
                format!("{name} = {value} (declared by this card alone)")
            }
        };
        let states = declared
            .iter()
            .map(|(_, name)| (name.as_str(), self.counter(name)))
            .collect::<Vec<_>>();
        let moved = states
            .iter()
            .filter_map(|(name, state)| match state {
                CounterState::Moved(value) => Some(describe(name, Some(*value))),
                _ => None,
            })
            .collect::<Vec<_>>();
        if moved.is_empty() {
            let idle = states
                .iter()
                .map(|(name, state)| {
                    describe(
                        name,
                        match state {
                            CounterState::Zero => Some(0),
                            _ => None,
                        },
                    )
                })
                .collect::<Vec<_>>();
            Decided::unknown(
                "counter-idle",
                format!(
                    "span policy {policy}; no declared counter moved ({}), and a counter that counts part of the work does not show that the algorithm did not run",
                    idle.join("; ")
                ),
            )
        } else {
            Decided::unknown(
                "counter-moved",
                format!(
                    "span policy {policy}; declared counters moved ({}), but a counter is incremented wherever its code runs, so it does not show that this algorithm ran",
                    moved.join("; ")
                ),
            )
        }
    }

    /// A phase ran when its span opened or when the receipt's timings list names it; some phases
    /// are recorded in timings without a span. A phase with neither did not run when the receipt
    /// holds a current-schema timings list, which records every phase the pipeline executed.
    fn phase(&self, id: &str) -> Decided {
        let count = self
            .observations
            .phases
            .get(id)
            .map_or(0, |aggregate| aggregate.count);
        if count > 0 {
            return Decided::ran("span", format!("its span opened {count} times"));
        }
        match self.timings_phases {
            Some(names) if names.contains(id) => Decided::ran(
                "timings",
                "the receipt's timings list records it; it has no phase span".to_owned(),
            ),
            Some(_) => Decided::not_run(
                "absent",
                "no phase span and no entry in the receipt's timings list".to_owned(),
            ),
            None => Decided::unknown(
                "unrecorded",
                "no phase span, and the receipt has no current-schema timings list that would record a phase without one".to_owned(),
            ),
        }
    }

    /// A counter node ran when the counter moved and did not run when a current-schema dump
    /// records it at zero.
    fn observation(&self, node: &crate::Node) -> Decided {
        let Some(name) = node.registry_name.as_deref() else {
            return Decided::unknown("unobserved", "the node names no counter".to_owned());
        };
        match self.counter(name) {
            CounterState::Moved(value) => Decided::ran("counter", format!("{name} = {value}")),
            CounterState::Zero => Decided::not_run(
                "counter-zero",
                format!("{name} is zero in a current-schema counter dump"),
            ),
            CounterState::Unrecorded => Decided::unknown(
                "counter-unrecorded",
                format!("the receipt holds no current-schema value for {name}"),
            ),
        }
    }

    /// The verdict of one static edge; [`edge_verdict_rule`] states the rule per kind.
    fn edge(
        &self,
        edge: &Edge,
        observation_names: &BTreeMap<String, String>,
        node_verdicts: &BTreeMap<&str, Verdict>,
    ) -> (Verdict, &'static str) {
        let verdict = |id: &str| node_verdicts.get(id).copied().unwrap_or(Verdict::Unknown);
        let from = verdict(&edge.from);
        let to = verdict(&edge.to);
        let key = (edge.from.clone(), edge.to.clone());
        let either_not_run = from == Verdict::NotRun || to == Verdict::NotRun;
        let not_run = (Verdict::NotRun, "endpoint-not-run");
        let unknown = (Verdict::Unknown, "unobserved");
        match edge.kind.as_str() {
            "contains" => {
                if self.observations.within.contains(&key) {
                    (Verdict::Ran, "observed")
                } else if either_not_run {
                    not_run
                } else {
                    unknown
                }
            }
            "nests" => {
                if self.observations.nests.contains_key(&key) {
                    (Verdict::Ran, "observed")
                } else if either_not_run {
                    not_run
                } else {
                    unknown
                }
            }
            "follows" => {
                if self.observations.follows.contains(&key) {
                    (Verdict::Ran, "observed")
                } else if either_not_run {
                    not_run
                } else {
                    unknown
                }
            }
            "measured-by" => {
                let moved = observation_names.get(&edge.to).and_then(|name| {
                    self.observations
                        .algorithms
                        .get(&edge.from)
                        .and_then(|algorithm| algorithm.counters.get(name).copied())
                });
                if moved.is_some_and(|value| value > 0) {
                    (Verdict::Ran, "observed")
                } else if either_not_run {
                    not_run
                } else {
                    unknown
                }
            }
            "consumes" | "produces" if from == Verdict::NotRun => not_run,
            "constrains" if to == Verdict::NotRun => not_run,
            "falls-back-to" if either_not_run => not_run,
            "consumes" | "produces" | "constrains" | "falls-back-to" => unknown,
            _ if from == Verdict::NotRun && to == Verdict::NotRun => not_run,
            _ => unknown,
        }
    }
}

/// The rule that decides one edge kind's verdict, stated for the reader.
pub fn edge_verdict_rule(kind: &str) -> &'static str {
    match kind {
        "contains" => {
            "ran when the algorithm's span opened inside the phase's span, at any depth; not-run when either endpoint did not run; otherwise unknown, because the algorithm may run inside the phase through an entry without its span"
        }
        "nests" => {
            "ran when the inner algorithm's span opened directly inside the outer one's; not-run when either endpoint did not run; otherwise unknown"
        }
        "follows" => {
            "ran when the later phase's span started next after the earlier one under the same parent; not-run when either phase did not run; otherwise unknown, because an optional phase between them hides the order"
        }
        "measured-by" => {
            "ran when the counter moved inside the algorithm's spans; not-run when either endpoint did not run, including a counter that stayed zero; otherwise unknown, because the algorithm may move the counter through an entry without its span"
        }
        "consumes" | "produces" => {
            "not-run when the algorithm did not run; otherwise unknown, because no instrumentation records a representation"
        }
        "constrains" => {
            "not-run when the consumer did not run; otherwise unknown, because the carrier is not a call and may cross processes (a compiled definition read by the backend)"
        }
        "falls-back-to" => {
            "not-run when either algorithm did not run; otherwise unknown, because no instrumentation records the fallback itself"
        }
        _ => "not-run when both endpoints did not run; otherwise unknown",
    }
}

/// Render a complete run overlay. Static cost bounds stay in the algorithm label beside the
/// trace observations. Nodes and edges carry their verdict: `ran` in green, `not-run` dimmed,
/// and `unknown` with a dashed outline or a dashed link, so the evidence gap stays visible.
///
/// A counter node whose receipt value is zero is omitted together with its edges: the run
/// observed nothing on it, so it carries no run information. A counter the receipt does not
/// record is kept, because its value is unknown rather than zero.
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
        .map(|node| ((node.kind.as_str(), node.id.as_str()), node.verdict))
        .collect::<BTreeMap<_, _>>();
    let observed_zero = |node: &&crate::Node| {
        node.kind == "observation"
            && node
                .registry_name
                .as_deref()
                .and_then(|name| receipt_counter.get(name))
                == Some(&0)
    };
    let mut nodes = graph
        .nodes
        .iter()
        .filter(|node| !observed_zero(node))
        .collect::<Vec<_>>();
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
    output.push_str(
        "%% verdicts: ran (green) was observed; not-run (dimmed) would have been recorded and was not; unknown (dashed) cannot be told from this run\n",
    );
    output.push_str(&format!("%% rule: {VERDICT_RULE}\n"));
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
                edge.verdict,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut link_verdicts = BTreeMap::<Verdict, Vec<usize>>::new();
    let mut link = 0usize;
    for edge in &graph.edges {
        let Some(from) = first_id.get(edge.from.as_str()) else {
            continue;
        };
        let Some(to) = first_id.get(edge.to.as_str()) else {
            continue;
        };
        let index = link;
        link += 1;
        output.push_str(&format!(
            "  {from} -->|\"{} [{}]\"| {to}\n",
            escape(&edge.kind),
            escape(&edge.provenance)
        ));
        let verdict = edge_status
            .get(&(
                edge.kind.as_str(),
                edge.from.as_str(),
                edge.to.as_str(),
                edge.detail.as_deref(),
                edge.order,
            ))
            .copied()
            .unwrap_or(Verdict::Unknown);
        link_verdicts.entry(verdict).or_default().push(index);
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
    output.push_str("  classDef ran fill:#e5f6e8,stroke:#2f6f3e,color:#17251b\n");
    output.push_str("  classDef notrun fill:#f1f1f1,stroke:#aaa,color:#999\n");
    output.push_str(
        "  classDef unknown fill:#fffdf5,stroke:#8a6d1f,stroke-width:2px,stroke-dasharray:6 3,color:#3b3218\n",
    );
    for (verdict, class) in [
        (Verdict::Ran, "ran"),
        (Verdict::NotRun, "notrun"),
        (Verdict::Unknown, "unknown"),
    ] {
        let members = nodes
            .iter()
            .filter(|node| {
                status
                    .get(&(node.kind.as_str(), node.id.as_str()))
                    .copied()
                    .unwrap_or(Verdict::Unknown)
                    == verdict
            })
            .map(|node| ids[&(node.kind.as_str(), node.id.as_str())].as_str())
            .collect::<Vec<_>>();
        if !members.is_empty() {
            output.push_str(&format!("  class {} {class}\n", members.join(",")));
        }
    }
    for (verdict, style) in [
        (Verdict::NotRun, "stroke:#bbb,color:#999,opacity:0.35"),
        (
            Verdict::Unknown,
            "stroke:#8a6d1f,color:#5c4a16,stroke-dasharray:6 3",
        ),
    ] {
        if let Some(links) = link_verdicts.get(&verdict) {
            output.push_str(&format!(
                "  linkStyle {} {style}\n",
                links
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(",")
            ));
        }
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

[[node]]
kind = "observation"
id = "CounterZero"
provenance = "table"
registry_name = "work.zero"
[node.anchor]
crate = "demo"
file = "measure.rs"
symbol = "Counter::Zero"

[[edge]]
kind = "measured-by"
from = "backend.unused"
to = "CounterZero"
provenance = "declared"

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
kind = "contains"
from = "proof"
to = "backend.unused"
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
            r#"{"format":"krust-counters","version":1,"counters":{"work.a":10,"work.b":3,"work.zero":0}}"#,
        )
        .unwrap();

        let (graph, join) = join_files(&root, &graph_path, &trace_path, &receipt).unwrap();
        assert_eq!(join.receipt.directory, "receipt");
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
        assert!(join.summary.not_run_backend_algorithms.is_empty());
        assert_eq!(join.summary.unknown_backend_algorithms, ["backend.unused"]);
        assert_eq!(
            (join.summary.ran_algorithms, join.summary.unknown_algorithms),
            (2, 1)
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
        assert!(overlay.contains(" unknown\n"), "{overlay}");
        assert!(!overlay.contains("CounterZero"), "{overlay}");
        assert!(!overlay.contains("receipt n: 0"), "{overlay}");
        // The one drawn edge without an observation is proof -> backend.unused, and it is
        // unknown rather than not-run because an entry may bypass the algorithm's span.
        let styled = overlay
            .lines()
            .filter_map(|line| line.strip_prefix("  linkStyle "))
            .collect::<Vec<_>>();
        assert_eq!(styled.len(), 1, "{overlay}");
        assert!(styled[0].contains("stroke-dasharray"), "{overlay}");
        assert!(!styled[0].split_whitespace().next().unwrap().contains(','));

        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn counts_a_recursive_invocation_once_in_totals() {
        let observations = parse_trace(&serde_json::json!([
            {"ph":"B","name":"phase","ts":0,"pid":1,"tid":1,"args":{"name":"proof"}},
            {"ph":"B","name":"algo","ts":0,"pid":1,"tid":1,"args":{"id":"backend.a"}},
            {"ph":"B","name":"algo","ts":10,"pid":1,"tid":1,"args":{"id":"backend.a"}},
            {"ph":"E","name":"algo","ts":20,"pid":1,"tid":1,"args":{"counters":{"c":3}}},
            {"ph":"E","name":"algo","ts":30,"pid":1,"tid":1,"args":{"counters":{"c":3}}},
            {"ph":"E","name":"phase","ts":30,"pid":1,"tid":1}
        ]))
        .unwrap();
        let a = &observations.algorithms["backend.a"];
        assert_eq!(a.count, 2);
        assert_eq!(a.total_micros, 30.0);
        assert_eq!(a.self_micros, 30.0);
        assert_eq!(a.counters["c"], 3);
        let contained = &observations.contains[&("proof".to_owned(), "backend.a".to_owned())];
        assert_eq!(contained.count, 2);
        assert_eq!(contained.total_micros, 30.0);
    }

    #[test]
    fn keys_phase_follows_by_parent_phase() {
        let observations = parse_trace(&serde_json::json!([
            {"ph":"B","name":"phase","ts":0,"pid":1,"tid":1,"args":{"name":"P"}},
            {"ph":"B","name":"phase","ts":0,"pid":1,"tid":1,"args":{"name":"a"}},
            {"ph":"E","name":"phase","ts":1,"pid":1,"tid":1},
            {"ph":"B","name":"phase","ts":1,"pid":1,"tid":1,"args":{"name":"b"}},
            {"ph":"E","name":"phase","ts":2,"pid":1,"tid":1},
            {"ph":"E","name":"phase","ts":2,"pid":1,"tid":1},
            {"ph":"B","name":"phase","ts":2,"pid":1,"tid":1,"args":{"name":"Q"}},
            {"ph":"B","name":"phase","ts":2,"pid":1,"tid":1,"args":{"name":"c"}},
            {"ph":"E","name":"phase","ts":3,"pid":1,"tid":1},
            {"ph":"B","name":"phase","ts":3,"pid":1,"tid":1,"args":{"name":"d"}},
            {"ph":"E","name":"phase","ts":4,"pid":1,"tid":1},
            {"ph":"E","name":"phase","ts":4,"pid":1,"tid":1}
        ]))
        .unwrap();
        let pairs = |from: &str, to: &str| (from.to_owned(), to.to_owned());
        assert_eq!(
            observations.follows,
            BTreeSet::from([pairs("P", "Q"), pairs("a", "b"), pairs("c", "d")])
        );
    }

    fn demo_receipt() -> Receipt {
        Receipt {
            directory: "evidence/demo".to_owned(),
            workload: "demo".to_owned(),
            claim: None,
            timestamp: None,
            krust_revision: None,
            binary_sha256: None,
            metadata_schema: "1".to_owned(),
            timings_schema: "1".to_owned(),
            current_timings_schema: 1,
            timings_partial: false,
            counter_schema: "1".to_owned(),
            current_counter_schema: 1,
            counters_partial: false,
            trace_schema: "chrome-trace-event-B/E".to_owned(),
            tools: Vec::new(),
            revisions: Vec::new(),
        }
    }

    /// One node or edge per verdict rule, joined to a trace, a counter dump, and a timings list.
    #[test]
    fn verdicts_follow_only_the_evidence_that_can_prove_them() {
        let algorithm = |id: &str, span: &str| {
            format!(
                "[[node]]\nkind = \"algorithm\"\nid = \"{id}\"\nprovenance = \"declared\"\narea = \"backend\"\nspan = \"{span}\"\n[node.anchor]\ncrate = \"demo\"\nfile = \"a.rs\"\nsymbol = \"{id}\"\n\n"
            )
        };
        let node = |kind: &str, id: &str, extra: &str| {
            format!(
                "[[node]]\nkind = \"{kind}\"\nid = \"{id}\"\nprovenance = \"table\"\n{extra}[node.anchor]\ncrate = \"demo\"\nfile = \"t.rs\"\nsymbol = \"{id}\"\n\n"
            )
        };
        let edge = |kind: &str, from: &str, to: &str| {
            format!(
                "[[edge]]\nkind = \"{kind}\"\nfrom = \"{from}\"\nto = \"{to}\"\nprovenance = \"declared\"\n\n"
            )
        };
        let mut source = String::new();
        source.push_str(&algorithm("t.spanned", "per call"));
        source.push_str(&algorithm("t.idle_span", "per problem"));
        source.push_str(&algorithm("t.exclusive", "none"));
        source.push_str(&algorithm("t.shared_a", "none"));
        source.push_str(&algorithm("t.shared_b", "none"));
        source.push_str(&algorithm("t.zero", "none"));
        source.push_str(&algorithm("t.invisible", "none"));
        source.push_str(&node("phase", "outer", ""));
        source.push_str(&node("phase", "inner", ""));
        source.push_str(&node("phase", "timed", ""));
        source.push_str(&node("phase", "skipped", ""));
        source.push_str(&node("observation", "Own", "registry_name = \"t.own\"\n"));
        source.push_str(&node(
            "observation",
            "Shared",
            "registry_name = \"t.shared\"\n",
        ));
        source.push_str(&node("observation", "Idle", "registry_name = \"t.idle\"\n"));
        source.push_str(&node(
            "observation",
            "Missing",
            "registry_name = \"t.missing\"\n",
        ));
        source.push_str(&node(
            "representation",
            "t::R [r]",
            "type_path = \"t::R\"\n",
        ));
        source.push_str(&edge("measured-by", "t.exclusive", "Own"));
        source.push_str(&edge("measured-by", "t.shared_a", "Shared"));
        source.push_str(&edge("measured-by", "t.shared_b", "Shared"));
        source.push_str(&edge("measured-by", "t.zero", "Idle"));
        source.push_str(&edge("measured-by", "t.spanned", "Shared"));
        source.push_str(&edge("contains", "outer", "t.spanned"));
        source.push_str(&edge("contains", "skipped", "t.idle_span"));
        source.push_str(&edge("contains", "timed", "t.idle_span"));
        source.push_str(&edge("follows", "outer", "timed"));
        source.push_str(&edge("follows", "timed", "skipped"));
        source.push_str(&edge("consumes", "t.spanned", "t::R [r]"));
        source.push_str(&edge("produces", "t.idle_span", "t::R [r]"));
        let mut graph: Graph = toml::from_str(&source).unwrap();
        graph.sort();
        // `t.spanned` runs inside `inner`, a phase nested in `outer`.
        let observations = parse_trace(&serde_json::json!([
            {"ph":"B","name":"phase","ts":0,"pid":1,"tid":1,"args":{"name":"outer"}},
            {"ph":"B","name":"phase","ts":0,"pid":1,"tid":1,"args":{"name":"inner"}},
            {"ph":"B","name":"algo","ts":1,"pid":1,"tid":1,"args":{"id":"t.spanned"}},
            {"ph":"E","name":"algo","ts":2,"pid":1,"tid":1,"args":{"counters":{"t.shared":2}}},
            {"ph":"E","name":"phase","ts":3,"pid":1,"tid":1},
            {"ph":"E","name":"phase","ts":3,"pid":1,"tid":1}
        ]))
        .unwrap();
        let join = project_with_timings(
            &graph,
            observations,
            demo_receipt(),
            BTreeMap::from([
                ("t.own".to_owned(), 4),
                ("t.shared".to_owned(), 9),
                ("t.idle".to_owned(), 0),
            ]),
            Some(BTreeSet::from([
                "outer".to_owned(),
                "inner".to_owned(),
                "timed".to_owned(),
            ])),
        );
        let node = |id: &str| {
            let node = join.nodes.iter().find(|node| node.id == id).unwrap();
            (node.verdict, node.evidence.as_str())
        };
        let edge = |kind: &str, from: &str, to: &str| {
            let edge = join
                .edges
                .iter()
                .find(|edge| edge.kind == kind && edge.from == from && edge.to == to)
                .unwrap();
            (edge.verdict, edge.evidence.as_str())
        };
        use Verdict::{NotRun, Ran, Unknown};
        assert_eq!(node("t.spanned"), (Ran, "span"));
        // A spanned algorithm whose span never opened: an entry may bypass the span.
        assert_eq!(node("t.idle_span"), (Unknown, "zero-span"));
        // A counter-only algorithm with a positive counter that only its card declares.
        assert_eq!(node("t.exclusive"), (Unknown, "counter-moved"));
        let exclusive = join
            .nodes
            .iter()
            .find(|node| node.id == "t.exclusive")
            .unwrap();
        assert!(
            exclusive
                .reason
                .contains("t.own = 4 (declared by this card alone)"),
            "{}",
            exclusive.reason
        );
        // A positive counter that three cards declare.
        assert_eq!(node("t.shared_a"), (Unknown, "counter-moved"));
        let shared = join
            .nodes
            .iter()
            .find(|node| node.id == "t.shared_b")
            .unwrap();
        assert!(
            shared.reason.contains("t.shared = 9 (declared by 3 cards)"),
            "{}",
            shared.reason
        );
        // A zero counter does not show that the algorithm did not run.
        assert_eq!(node("t.zero"), (Unknown, "counter-idle"));
        assert_eq!(node("t.invisible"), (Unknown, "unobservable"));

        assert_eq!(node("outer"), (Ran, "span"));
        assert_eq!(node("timed"), (Ran, "timings"));
        assert_eq!(node("skipped"), (NotRun, "absent"));
        assert_eq!(node("Own"), (Ran, "counter"));
        assert_eq!(node("Idle"), (NotRun, "counter-zero"));
        assert_eq!(node("Missing"), (Unknown, "counter-unrecorded"));
        assert_eq!(node("t::R [r]"), (Unknown, "unobserved"));

        assert_eq!(edge("contains", "outer", "t.spanned"), (Ran, "observed"));
        assert_eq!(
            edge("contains", "skipped", "t.idle_span"),
            (NotRun, "endpoint-not-run")
        );
        assert_eq!(
            edge("contains", "timed", "t.idle_span"),
            (Unknown, "unobserved")
        );
        assert_eq!(edge("follows", "outer", "timed"), (Unknown, "unobserved"));
        assert_eq!(
            edge("follows", "timed", "skipped"),
            (NotRun, "endpoint-not-run")
        );
        assert_eq!(
            edge("measured-by", "t.spanned", "Shared"),
            (Ran, "observed")
        );
        assert_eq!(
            edge("measured-by", "t.shared_a", "Shared"),
            (Unknown, "unobserved")
        );
        assert_eq!(
            edge("measured-by", "t.zero", "Idle"),
            (NotRun, "endpoint-not-run")
        );
        assert_eq!(
            edge("consumes", "t.spanned", "t::R [r]"),
            (Unknown, "unobserved")
        );
        assert_eq!(
            edge("produces", "t.idle_span", "t::R [r]"),
            (Unknown, "unobserved")
        );

        assert_eq!(join.summary.declared_algorithms, 7);
        assert_eq!(
            (
                join.summary.ran_algorithms,
                join.summary.not_run_algorithms,
                join.summary.unknown_algorithms
            ),
            (1, 0, 6)
        );
        assert!(join.summary.not_run_backend_algorithms.is_empty());
        assert_eq!(join.summary.unknown_backend_algorithms.len(), 6);
        assert_eq!(join.verdict_rule, VERDICT_RULE);

        // Without a timings list, a phase with no span is unknown rather than not-run.
        let without_timings = project(
            &graph,
            TraceObservations::default(),
            demo_receipt(),
            BTreeMap::new(),
        );
        let skipped = without_timings
            .nodes
            .iter()
            .find(|node| node.id == "skipped")
            .unwrap();
        assert_eq!(
            (skipped.verdict, skipped.evidence.as_str()),
            (Unknown, "unrecorded")
        );

        let overlay = render_run_overlay(&graph, &join);
        assert!(overlay.contains(VERDICT_RULE), "{overlay}");
        for class in ["ran", "notrun", "unknown"] {
            assert!(
                overlay.lines().any(
                    |line| line.starts_with("  class ") && line.ends_with(&format!(" {class}"))
                ),
                "{class}: {overlay}"
            );
        }
    }

    #[test]
    fn receipt_directory_is_never_absolute() {
        let root = fixture();
        let inside = root.join("draft/evidence/imp-prove/working-tree");
        fs::create_dir_all(&inside).unwrap();
        assert_eq!(
            receipt_directory(&root, &inside),
            "draft/evidence/imp-prove/working-tree"
        );
        let outside = fixture().join("imp-prove/working-tree");
        fs::create_dir_all(&outside).unwrap();
        assert_eq!(
            receipt_directory(&root.join("draft"), &outside),
            "imp-prove/working-tree"
        );
        fs::remove_dir_all(root).unwrap();
        fs::remove_dir_all(outside.parent().unwrap().parent().unwrap()).unwrap();
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
