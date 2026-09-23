//! Per-algorithm aggregation of algorithm and phase spans.
//!
//! One aggregator serves two producers: `algo-graph join` feeds it the begin and end events of a
//! Chrome trace written by `krust --trace`, and `krust --trace-aggregate` feeds it the same spans
//! in process and writes only the aggregate. Because both producers run this code, a join read
//! from either file applies the same aggregation rule, and a long run no longer has to write one
//! trace event per span.
//!
//! Spans are keyed by thread: a begin event pushes a frame on its thread's stack and an end event
//! pops it. An `algo` span carries an algorithm id and, on a `measure` build, the counter deltas
//! of its invocation; a `phase` span carries a phase name; any other span only keeps the nesting
//! balanced.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

/// The `schema` value of an aggregate document.
pub const TRACE_AGGREGATE_SCHEMA: &str = "krust-trace-aggregate/1";

/// Invocation count, durations in microseconds, and counter deltas of one algorithm or phase.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct Aggregate {
    pub count: u64,
    pub total_micros: f64,
    pub self_micros: f64,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub counters: BTreeMap<String, u64>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub self_counters: BTreeMap<String, u64>,
}

/// Everything the join reads from a run's spans.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct TraceAggregate {
    pub algorithms: BTreeMap<String, Aggregate>,
    pub phases: BTreeMap<String, Aggregate>,
    /// (parent algorithm, algorithm): invocations opened directly inside the parent.
    pub nests: BTreeMap<(String, String), u64>,
    /// (innermost phase, algorithm): the algorithm's invocations inside that phase.
    pub contains: BTreeMap<(String, String), Aggregate>,
    /// (phase, algorithm) for every algorithm span opened inside a phase span at any depth.
    pub within: BTreeSet<(String, String)>,
    /// (phase, phase): sibling phases in sequence under the same enclosing phase instance.
    pub follows: BTreeSet<(String, String)>,
}

/// What a begin event opens.
#[derive(Clone, Debug)]
pub enum SpanKind {
    Algorithm(String),
    Phase(String),
    Other,
}

#[derive(Clone, Debug)]
enum FrameKind {
    Algorithm {
        id: String,
        /// Stack position of the innermost enclosing phase frame when the span opened.
        phase: Option<usize>,
        child_micros: f64,
        /// Counter deltas of direct nested algorithm invocations, by interned counter.
        child_counters: Vec<(usize, u64)>,
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

/// Pair-keyed observations held as nested maps, so a hit needs no key allocation.
type Nested<V> = BTreeMap<String, BTreeMap<String, V>>;

/// Incremental aggregation of span begin and end events.
///
/// The frames below an open frame never change while it is open, so the innermost algorithm
/// and phase frames below it at its end are those it had at its begin.
#[derive(Debug, Default)]
pub struct SpanAggregator {
    algorithms: BTreeMap<String, Totals>,
    /// Counter names in first-seen order; the internal counter vectors index this list.
    counter_names: Vec<String>,
    counter_index: BTreeMap<String, usize>,
    phases: BTreeMap<String, Aggregate>,
    nests: Nested<u64>,
    contains: Nested<Aggregate>,
    within: BTreeMap<String, BTreeSet<String>>,
    stacks: BTreeMap<String, Vec<Frame>>,
    // Sibling phases are sequenced under their enclosing phase instance (None at top level).
    phase_sequences: BTreeMap<(String, Option<usize>), Vec<String>>,
}

fn innermost_algorithm(stack: &[Frame]) -> Option<usize> {
    stack
        .iter()
        .rposition(|frame| matches!(frame.kind, FrameKind::Algorithm { .. }))
}

fn innermost_phase(stack: &[Frame]) -> Option<usize> {
    stack
        .iter()
        .rposition(|frame| matches!(frame.kind, FrameKind::Phase { .. }))
}

fn phase_name(stack: &[Frame], position: Option<usize>) -> Option<&str> {
    position.and_then(|position| match &stack[position].kind {
        FrameKind::Phase { name, .. } => Some(name.as_str()),
        _ => None,
    })
}

fn entry<'a, V: Default>(map: &'a mut Nested<V>, outer: &str, inner: &str) -> &'a mut V {
    if !map.contains_key(outer) {
        map.insert(outer.to_owned(), BTreeMap::new());
    }
    let inner_map = map.get_mut(outer).expect("inserted above");
    if !inner_map.contains_key(inner) {
        inner_map.insert(inner.to_owned(), V::default());
    }
    inner_map.get_mut(inner).expect("inserted above")
}

fn aggregate<'a, V: Default>(map: &'a mut BTreeMap<String, V>, id: &str) -> &'a mut V {
    if !map.contains_key(id) {
        map.insert(id.to_owned(), V::default());
    }
    map.get_mut(id).expect("inserted above")
}

/// An algorithm's [`Aggregate`] with counters indexed by interned name; `None` marks a counter
/// that no invocation recorded, which the aggregate leaves out.
#[derive(Debug, Default)]
struct Totals {
    count: u64,
    total_micros: f64,
    self_micros: f64,
    counters: Vec<Option<u64>>,
    self_counters: Vec<Option<u64>>,
}

fn add_at(values: &mut Vec<Option<u64>>, counter: usize, addition: u64) -> Result<(), usize> {
    if values.len() <= counter {
        values.resize(counter + 1, None);
    }
    let value = values[counter].get_or_insert(0);
    *value = value.checked_add(addition).ok_or(counter)?;
    Ok(())
}

fn add_child(children: &mut Vec<(usize, u64)>, counter: usize, addition: u64) -> Result<(), usize> {
    match children.iter_mut().find(|(index, _)| *index == counter) {
        Some((_, value)) => *value = value.checked_add(addition).ok_or(counter)?,
        None => children.push((counter, addition)),
    }
    Ok(())
}

fn named_counters(names: &[String], values: &[Option<u64>]) -> BTreeMap<String, u64> {
    values
        .iter()
        .enumerate()
        .filter_map(|(index, value)| value.map(|value| (names[index].clone(), value)))
        .collect()
}

fn flatten<V: Clone>(map: &Nested<V>) -> BTreeMap<(String, String), V> {
    map.iter()
        .flat_map(|(outer, inner)| {
            inner
                .iter()
                .map(move |(key, value)| ((outer.clone(), key.clone()), value.clone()))
        })
        .collect()
}

impl SpanAggregator {
    /// Open a span named `name` on `thread` at `timestamp` microseconds; `index` names the event
    /// in error messages and identifies a phase instance, so it must be unique per event.
    pub fn begin(
        &mut self,
        index: usize,
        thread: &str,
        name: &str,
        kind: SpanKind,
        timestamp: f64,
    ) -> Result<(), String> {
        if !self.stacks.contains_key(thread) {
            self.stacks.insert(thread.to_owned(), Vec::new());
        }
        let stack = self.stacks.get_mut(thread).expect("inserted above");
        let frame_kind = match kind {
            SpanKind::Algorithm(id) => {
                if let Some(parent) = innermost_algorithm(stack)
                    && let FrameKind::Algorithm { id: parent, .. } = &stack[parent].kind
                {
                    let count = entry(&mut self.nests, parent, &id);
                    *count = count
                        .checked_add(1)
                        .ok_or_else(|| "observation count overflow".to_owned())?;
                }
                for frame in stack.iter() {
                    if let FrameKind::Phase { name, .. } = &frame.kind {
                        let ids = match self.within.get_mut(name) {
                            Some(ids) => ids,
                            None => self.within.entry(name.clone()).or_default(),
                        };
                        if !ids.contains(&id) {
                            ids.insert(id.clone());
                        }
                    }
                }
                FrameKind::Algorithm {
                    id,
                    phase: innermost_phase(stack),
                    child_micros: 0.0,
                    child_counters: Vec::new(),
                }
            }
            SpanKind::Phase(phase) => {
                let parent =
                    innermost_phase(stack).and_then(|position| match &stack[position].kind {
                        FrameKind::Phase { serial, .. } => Some(*serial),
                        _ => None,
                    });
                self.phase_sequences
                    .entry((thread.to_owned(), parent))
                    .or_default()
                    .push(phase.clone());
                FrameKind::Phase {
                    name: phase,
                    serial: index,
                }
            }
            SpanKind::Other => FrameKind::Other,
        };
        stack.push(Frame {
            name: name.to_owned(),
            started: timestamp,
            kind: frame_kind,
        });
        Ok(())
    }

    fn intern(&mut self, name: &str) -> usize {
        if let Some(index) = self.counter_index.get(name) {
            return *index;
        }
        self.counter_names.push(name.to_owned());
        self.counter_index
            .insert(name.to_owned(), self.counter_names.len() - 1);
        self.counter_names.len() - 1
    }

    /// Close the innermost open span on `thread`. `name`, when given, must be the open span's;
    /// `counters` are the invocation's counter deltas, each name once (empty for a phase or
    /// another span).
    pub fn end(
        &mut self,
        index: usize,
        thread: &str,
        name: Option<&str>,
        counters: &[(&str, u64)],
        timestamp: f64,
    ) -> Result<(), String> {
        let counters = counters
            .iter()
            .map(|(name, value)| (self.intern(name), *value))
            .collect::<Vec<_>>();
        let overflow =
            |names: &[String], counter: usize| format!("counter {} overflow", names[counter]);
        let frame = self
            .stacks
            .get_mut(thread)
            .and_then(Vec::pop)
            .ok_or_else(|| format!("end event {index} has no matching begin"))?;
        let stack = &mut self.stacks.get_mut(thread).expect("popped above")[..];
        if let Some(name) = name
            && !name.is_empty()
            && name != frame.name
        {
            return Err(format!(
                "end event {index} closes {name}, but {} is open",
                frame.name
            ));
        }
        let duration = timestamp - frame.started;
        if duration < 0.0 {
            return Err(format!("end event {index} precedes its begin event"));
        }
        match frame.kind {
            FrameKind::Algorithm {
                id,
                phase,
                child_micros,
                child_counters,
            } => {
                let phase = phase_name(stack, phase);
                // A recursive invocation lies inside an open invocation of the same id, whose
                // inclusive duration and counter delta already contain it.
                let mut recursive = false;
                let mut recursive_in_phase = false;
                for (position, open) in stack.iter().enumerate() {
                    if let FrameKind::Algorithm {
                        id: open_id,
                        phase: open_phase,
                        ..
                    } = &open.kind
                        && *open_id == id
                    {
                        recursive = true;
                        let open_phase = phase_name(&stack[..position], *open_phase);
                        recursive_in_phase |= open_phase == phase;
                    }
                }
                let totals = aggregate(&mut self.algorithms, &id);
                totals.count = totals
                    .count
                    .checked_add(1)
                    .ok_or_else(|| "algorithm count overflow".to_owned())?;
                if !recursive {
                    totals.total_micros += duration;
                    for &(counter, value) in &counters {
                        add_at(&mut totals.counters, counter, value)
                            .map_err(|counter| overflow(&self.counter_names, counter))?;
                    }
                }
                totals.self_micros += (duration - child_micros).max(0.0);
                for &(counter, value) in &counters {
                    let child = child_counters
                        .iter()
                        .find(|(index, _)| *index == counter)
                        .map_or(0, |(_, child)| *child);
                    add_at(
                        &mut totals.self_counters,
                        counter,
                        value.saturating_sub(child),
                    )
                    .map_err(|counter| overflow(&self.counter_names, counter))?;
                }
                if let Some(phase) = phase {
                    let contained = entry(&mut self.contains, phase, &id);
                    contained.count = contained
                        .count
                        .checked_add(1)
                        .ok_or_else(|| "containment count overflow".to_owned())?;
                    if !recursive_in_phase {
                        contained.total_micros += duration;
                    }
                    contained.self_micros += (duration - child_micros).max(0.0);
                }
                if let Some(parent) = innermost_algorithm(stack)
                    && let FrameKind::Algorithm {
                        child_micros,
                        child_counters,
                        ..
                    } = &mut stack[parent].kind
                {
                    *child_micros += duration;
                    for &(counter, value) in &counters {
                        add_child(child_counters, counter, value)
                            .map_err(|counter| overflow(&self.counter_names, counter))?;
                    }
                }
            }
            FrameKind::Phase { name, .. } => {
                let totals = aggregate(&mut self.phases, &name);
                totals.count = totals
                    .count
                    .checked_add(1)
                    .ok_or_else(|| "phase count overflow".to_owned())?;
                totals.total_micros += duration;
                totals.self_micros += duration;
            }
            FrameKind::Other => {}
        }
        Ok(())
    }

    /// The aggregate of a run whose spans are all closed.
    pub fn finish(self) -> Result<TraceAggregate, String> {
        if let Some((thread, stack)) = self.stacks.iter().find(|(_, stack)| !stack.is_empty()) {
            return Err(format!(
                "trace ends with {} open span(s) on thread {thread}",
                stack.len()
            ));
        }
        let mut follows = BTreeSet::new();
        for sequence in self.phase_sequences.values() {
            for pair in sequence.windows(2) {
                follows.insert((pair[0].clone(), pair[1].clone()));
            }
        }
        Ok(TraceAggregate {
            nests: flatten(&self.nests),
            contains: flatten(&self.contains),
            within: self
                .within
                .iter()
                .flat_map(|(phase, ids)| ids.iter().map(move |id| (phase.clone(), id.clone())))
                .collect(),
            algorithms: self
                .algorithms
                .into_iter()
                .map(|(id, totals)| {
                    let aggregate = Aggregate {
                        count: totals.count,
                        total_micros: totals.total_micros,
                        self_micros: totals.self_micros,
                        counters: named_counters(&self.counter_names, &totals.counters),
                        self_counters: named_counters(&self.counter_names, &totals.self_counters),
                    };
                    (id, aggregate)
                })
                .collect(),
            phases: self.phases,
            follows,
        })
    }
}

#[derive(Serialize, Deserialize)]
struct Named {
    id: String,
    #[serde(flatten)]
    aggregate: Aggregate,
}

#[derive(Serialize, Deserialize)]
struct Nest {
    parent: String,
    id: String,
    count: u64,
}

#[derive(Serialize, Deserialize)]
struct Contained {
    phase: String,
    id: String,
    #[serde(flatten)]
    aggregate: Aggregate,
}

#[derive(Serialize, Deserialize)]
struct Document {
    schema: String,
    aggregation: String,
    algorithms: Vec<Named>,
    phases: Vec<Named>,
    nests: Vec<Nest>,
    contains: Vec<Contained>,
    within: Vec<(String, String)>,
    follows: Vec<(String, String)>,
}

fn named(map: &BTreeMap<String, Aggregate>) -> Vec<Named> {
    map.iter()
        .map(|(id, aggregate)| Named {
            id: id.clone(),
            aggregate: aggregate.clone(),
        })
        .collect()
}

impl TraceAggregate {
    /// The aggregate as a JSON document whose `schema` is [`TRACE_AGGREGATE_SCHEMA`].
    /// `aggregation` states the rule that produced it, for a reader of the file.
    pub fn to_json(&self, aggregation: &str) -> serde_json::Value {
        let document = Document {
            schema: TRACE_AGGREGATE_SCHEMA.to_owned(),
            aggregation: aggregation.to_owned(),
            algorithms: named(&self.algorithms),
            phases: named(&self.phases),
            nests: self
                .nests
                .iter()
                .map(|((parent, id), count)| Nest {
                    parent: parent.clone(),
                    id: id.clone(),
                    count: *count,
                })
                .collect(),
            contains: self
                .contains
                .iter()
                .map(|((phase, id), aggregate)| Contained {
                    phase: phase.clone(),
                    id: id.clone(),
                    aggregate: aggregate.clone(),
                })
                .collect(),
            within: self.within.iter().cloned().collect(),
            follows: self.follows.iter().cloned().collect(),
        };
        serde_json::to_value(document).expect("an aggregate always serializes")
    }

    /// Read a document written by [`TraceAggregate::to_json`].
    pub fn from_json(document: &serde_json::Value) -> Result<Self, String> {
        let document = Document::deserialize(document).map_err(|error| error.to_string())?;
        if document.schema != TRACE_AGGREGATE_SCHEMA {
            return Err(format!(
                "trace aggregate schema is `{}`, expected `{TRACE_AGGREGATE_SCHEMA}`",
                document.schema
            ));
        }
        let by_id = |entries: Vec<Named>| {
            entries
                .into_iter()
                .map(|entry| (entry.id, entry.aggregate))
                .collect()
        };
        Ok(Self {
            algorithms: by_id(document.algorithms),
            phases: by_id(document.phases),
            nests: document
                .nests
                .into_iter()
                .map(|nest| ((nest.parent, nest.id), nest.count))
                .collect(),
            contains: document
                .contains
                .into_iter()
                .map(|entry| ((entry.phase, entry.id), entry.aggregate))
                .collect(),
            within: document.within.into_iter().collect(),
            follows: document.follows.into_iter().collect(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_through_json() {
        let mut aggregator = SpanAggregator::default();
        let counters = [("c", 2)];
        let none = [];
        aggregator
            .begin(0, "t", "phase", SpanKind::Phase("p".to_owned()), 0.0)
            .unwrap();
        aggregator
            .begin(1, "t", "algo", SpanKind::Algorithm("a".to_owned()), 1.0)
            .unwrap();
        aggregator
            .begin(2, "t", "algo", SpanKind::Algorithm("b".to_owned()), 2.0)
            .unwrap();
        aggregator
            .end(3, "t", Some("algo"), &counters, 3.0)
            .unwrap();
        aggregator
            .end(4, "t", Some("algo"), &counters, 5.0)
            .unwrap();
        aggregator.end(5, "t", Some("phase"), &none, 6.0).unwrap();
        aggregator
            .begin(6, "t", "phase", SpanKind::Phase("q".to_owned()), 6.0)
            .unwrap();
        aggregator.end(7, "t", None, &none, 7.0).unwrap();
        let aggregate = aggregator.finish().unwrap();
        assert_eq!(aggregate.algorithms["a"].self_micros, 3.0);
        assert_eq!(aggregate.algorithms["a"].self_counters["c"], 0);
        assert_eq!(aggregate.nests[&("a".to_owned(), "b".to_owned())], 1);
        assert!(
            aggregate
                .follows
                .contains(&("p".to_owned(), "q".to_owned()))
        );
        let document = aggregate.to_json("rule");
        assert_eq!(document["schema"], TRACE_AGGREGATE_SCHEMA);
        assert_eq!(TraceAggregate::from_json(&document).unwrap(), aggregate);
    }

    #[test]
    fn rejects_an_unclosed_span() {
        let mut aggregator = SpanAggregator::default();
        aggregator
            .begin(0, "t", "other", SpanKind::Other, 0.0)
            .unwrap();
        assert!(aggregator.finish().unwrap_err().contains("1 open span(s)"));
    }
}
