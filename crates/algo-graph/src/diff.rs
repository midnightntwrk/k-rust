//! Per-algorithm comparison of two sets of joins of one workload.
//!
//! Each side of a comparison is one or more joins of one workload, read as repeats.
//! Span counts and counters are deterministic for a deterministic workload, so their deltas are
//! exact; span times vary between runs, so a time delta is classified against the spread of the
//! repeats. [`DIFF_RULE`] states the rules, and every answer repeats it.

use std::{collections::BTreeSet, fmt, fs, path::Path};

use serde::Serialize;

use crate::{Error, JOIN_SCHEMA_VERSION, Join, query::Answer};

/// The rules by which [`diff`] reduces repeats and classifies deltas.
pub const DIFF_RULE: &str = "each side is one workload and its joins are repeats; a side's value of a quantity is the median over its repeats (the mean of the two middle values for an even number) with the min..max range, and an algorithm without a row in a join counts as zero spans, zero seconds, and zero counters there. Span counts and counters are deterministic: their delta is the after median minus the before median, exact when every repeat of each side agrees and marked varies otherwise. A time delta is unreplicated when either side has fewer than two joins, within noise when the before and after min..max ranges overlap, and faster or slower otherwise. Algorithm counters are the counters its card declares, measured inside its spans including nested spans (trace_total); receipt counters are process-wide totals. An algorithm is added when some after join declares it and no before join does, and removed conversely";

/// Read a join file, refusing any schema other than [`JOIN_SCHEMA_VERSION`].
///
/// Every error names `path` exactly once.
pub fn read_join_file(path: &Path) -> Result<Join, Error> {
    let at = |error: &dyn fmt::Display| Error::Invalid(format!("{}: {error}", path.display()));
    let source = fs::read_to_string(path).map_err(|error| at(&error))?;
    let table = toml::from_str::<toml::Table>(&source).map_err(|error| at(&error))?;
    let schema = table
        .get("schema_version")
        .and_then(toml::Value::as_integer);
    if schema != Some(i64::from(JOIN_SCHEMA_VERSION)) {
        return Err(at(&format!(
            "join schema {}, but this tool reads schema {JOIN_SCHEMA_VERSION}; rerun `algo-graph join`",
            schema.map_or_else(|| "absent".to_owned(), |schema| schema.to_string())
        )));
    }
    toml::Value::Table(table)
        .try_into()
        .map_err(|error| at(&error))
}

/// The median and range of one quantity over repeats.
#[derive(Clone, Copy, Debug, Default, PartialEq, Serialize)]
pub struct Spread {
    /// The middle value, or the mean of the two middle values for an even number of repeats.
    pub median: f64,
    pub min: f64,
    pub max: f64,
}

impl Spread {
    /// The spread of `values`; zero for an empty slice.
    pub fn of(values: &[f64]) -> Self {
        if values.is_empty() {
            return Self::default();
        }
        let mut sorted = values.to_vec();
        sorted.sort_by(f64::total_cmp);
        let middle = sorted.len() / 2;
        let median = if sorted.len() % 2 == 1 {
            sorted[middle]
        } else {
            (sorted[middle - 1] + sorted[middle]) / 2.0
        };
        Self {
            median,
            min: sorted[0],
            max: sorted[sorted.len() - 1],
        }
    }

    /// Every repeat has the same value.
    pub fn constant(&self) -> bool {
        self.min == self.max
    }

    /// The two closed ranges share a point.
    pub fn overlaps(&self, other: &Self) -> bool {
        self.min <= other.max && other.min <= self.max
    }
}

/// How a time delta compares with the spread of the repeats.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum TimeClass {
    /// A side has fewer than two joins, so its spread is unknown.
    Unreplicated,
    /// The before and after ranges overlap.
    WithinNoise,
    /// The after range lies entirely below the before range.
    Faster,
    /// The after range lies entirely above the before range.
    Slower,
}

impl TimeClass {
    /// Classify `after` against `before` by [`DIFF_RULE`].
    pub fn of(before: &Spread, after: &Spread, before_runs: usize, after_runs: usize) -> Self {
        if before_runs < 2 || after_runs < 2 {
            Self::Unreplicated
        } else if before.overlaps(after) {
            Self::WithinNoise
        } else if after.max < before.min {
            Self::Faster
        } else {
            Self::Slower
        }
    }

    /// The serialized name.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Unreplicated => "unreplicated",
            Self::WithinNoise => "within noise",
            Self::Faster => "faster",
            Self::Slower => "slower",
        }
    }
}

/// One deterministic quantity on both sides.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct CountDelta {
    pub name: String,
    pub before: Spread,
    pub after: Spread,
    /// After median minus before median.
    pub delta: f64,
    /// Every repeat of each side agrees, so `delta` is the exact change.
    pub exact: bool,
}

impl CountDelta {
    fn new(name: String, before: &[f64], after: &[f64]) -> Self {
        let before = Spread::of(before);
        let after = Spread::of(after);
        Self {
            name,
            delta: after.median - before.median,
            exact: before.constant() && after.constant(),
            before,
            after,
        }
    }

    fn changed(&self) -> bool {
        self.delta != 0.0 || !self.exact
    }
}

/// One timed quantity on both sides.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct TimeDelta {
    pub before: Spread,
    pub after: Spread,
    /// After median minus before median, in seconds.
    pub delta: f64,
    pub class: TimeClass,
}

impl TimeDelta {
    fn new(before: &[f64], after: &[f64]) -> Self {
        let class_before = Spread::of(before);
        let class_after = Spread::of(after);
        Self {
            delta: class_after.median - class_before.median,
            class: TimeClass::of(&class_before, &class_after, before.len(), after.len()),
            before: class_before,
            after: class_after,
        }
    }
}

/// One algorithm with a span on either side.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct AlgorithmDelta {
    pub id: String,
    pub count: CountDelta,
    pub self_seconds: TimeDelta,
    pub total_seconds: TimeDelta,
    pub verdict_before: String,
    pub verdict_after: String,
    /// The card's declared counters inside the algorithm's spans, nonzero on some side.
    #[serde(rename = "counter", skip_serializing_if = "Vec::is_empty")]
    pub counters: Vec<CountDelta>,
}

/// A deterministic quantity that changed, or whose repeats disagree.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct ChangedCount {
    /// `span` (an algorithm's span count), `algorithm-counter` (a declared counter inside its
    /// spans), or `receipt-counter` (a process-wide counter).
    pub kind: String,
    /// The algorithm id, or the counter name for a receipt counter.
    pub id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counter: Option<String>,
    pub before: Spread,
    pub after: Spread,
    pub delta: f64,
    pub exact: bool,
}

/// An algorithm whose verdict differs between the sides.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct VerdictChange {
    pub id: String,
    pub before: String,
    pub after: String,
}

/// The identity of one side.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct Side {
    pub workload: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub claim: Option<String>,
    pub runs: usize,
    /// Distinct krust revisions of the joins, abbreviated to 12 characters.
    pub revisions: Vec<String>,
    pub joins: Vec<String>,
}

/// The comparison of two sets of joins.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct DiffAnswer {
    pub rule: String,
    pub before: Side,
    pub after: Side,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<String>,
    pub added: Vec<String>,
    pub removed: Vec<String>,
    #[serde(rename = "changed_count")]
    pub changed_counts: Vec<ChangedCount>,
    #[serde(rename = "changed_verdict")]
    pub changed_verdicts: Vec<VerdictChange>,
    /// Algorithms with a span on either side, by decreasing absolute self-time delta.
    #[serde(rename = "algorithm")]
    pub algorithms: Vec<AlgorithmDelta>,
    /// Process-wide counters that are nonzero on either side.
    #[serde(rename = "receipt_counter")]
    pub receipt_counters: Vec<CountDelta>,
}

/// Compare `before` with `after`; each is a list of `(label, join)` repeats of one workload.
///
/// Fails when a side is empty or mixes workloads.
pub fn diff(before: &[(String, Join)], after: &[(String, Join)]) -> Result<DiffAnswer, Error> {
    let before_side = side("--before", before)?;
    let after_side = side("--after", after)?;
    let mut warnings = Vec::new();
    if before_side.workload != after_side.workload || before_side.claim != after_side.claim {
        warnings.push(format!(
            "the sides run different workloads ({} and {}), so their deltas compare different work",
            workload_text(&before_side),
            workload_text(&after_side)
        ));
    }
    for (flag, joins) in [("--before", before), ("--after", after)] {
        let graphs = joins
            .iter()
            .map(|(_, join)| declared(join))
            .collect::<BTreeSet<_>>();
        if graphs.len() > 1 {
            warnings.push(format!(
                "the {flag} joins declare different algorithm sets, so they were joined to different graphs"
            ));
        }
    }

    let declared_before = joins_declared(before);
    let declared_after = joins_declared(after);
    let added = declared_after
        .difference(&declared_before)
        .cloned()
        .collect();
    let removed = declared_before
        .difference(&declared_after)
        .cloned()
        .collect();

    let ids = before
        .iter()
        .chain(after)
        .flat_map(|(_, join)| join.algorithms.iter().map(|algorithm| algorithm.id.clone()))
        .chain(
            before
                .iter()
                .chain(after)
                .flat_map(|(_, join)| algorithm_nodes(join).map(|(id, _)| id.to_owned())),
        )
        .collect::<BTreeSet<_>>();

    let mut algorithms = Vec::new();
    let mut changed_counts = Vec::new();
    let mut changed_verdicts = Vec::new();
    for id in &ids {
        let verdict_before = verdict(before, id);
        let verdict_after = verdict(after, id);
        if verdict_before != verdict_after {
            changed_verdicts.push(VerdictChange {
                id: id.clone(),
                before: verdict_before.clone(),
                after: verdict_after.clone(),
            });
        }
        let count = CountDelta::new(
            "span count".to_owned(),
            &column(before, |join| {
                row(join, id).map_or(0.0, |row| row.count as f64)
            }),
            &column(after, |join| {
                row(join, id).map_or(0.0, |row| row.count as f64)
            }),
        );
        if count.before.max == 0.0 && count.after.max == 0.0 {
            continue;
        }
        let counter_names = before
            .iter()
            .chain(after)
            .filter_map(|(_, join)| row(join, id))
            .flat_map(|row| row.counters.iter())
            .filter(|counter| counter.declared)
            .map(|counter| counter.name.clone())
            .collect::<BTreeSet<_>>();
        let counters = counter_names
            .into_iter()
            .map(|name| {
                let value = |join: &Join| {
                    row(join, id)
                        .and_then(|row| row.counters.iter().find(|counter| counter.name == name))
                        .and_then(|counter| counter.trace_total)
                        .unwrap_or(0) as f64
                };
                CountDelta::new(name.clone(), &column(before, value), &column(after, value))
            })
            .filter(|counter| counter.before.max > 0.0 || counter.after.max > 0.0)
            .collect::<Vec<_>>();
        if count.changed() {
            changed_counts.push(changed("span", id, None, &count));
        }
        for counter in counters.iter().filter(|counter| counter.changed()) {
            changed_counts.push(changed(
                "algorithm-counter",
                id,
                Some(&counter.name),
                counter,
            ));
        }
        let seconds = |select: fn(&crate::AlgorithmRun) -> f64| {
            TimeDelta::new(
                &column(before, |join| row(join, id).map_or(0.0, select)),
                &column(after, |join| row(join, id).map_or(0.0, select)),
            )
        };
        algorithms.push(AlgorithmDelta {
            id: id.clone(),
            count,
            self_seconds: seconds(|row| row.self_seconds),
            total_seconds: seconds(|row| row.total_seconds),
            verdict_before,
            verdict_after,
            counters,
        });
    }
    algorithms.sort_by(|left, right| {
        right
            .self_seconds
            .delta
            .abs()
            .total_cmp(&left.self_seconds.delta.abs())
            .then_with(|| left.id.cmp(&right.id))
    });

    let counter_names = before
        .iter()
        .chain(after)
        .flat_map(|(_, join)| join.receipt_counters.iter().map(|counter| &counter.name))
        .collect::<BTreeSet<_>>();
    let receipt_counters = counter_names
        .into_iter()
        .map(|name| {
            let value = |join: &Join| {
                join.receipt_counters
                    .iter()
                    .find(|counter| &counter.name == name)
                    .map_or(0.0, |counter| counter.value as f64)
            };
            CountDelta::new(name.clone(), &column(before, value), &column(after, value))
        })
        .filter(|counter| counter.before.max > 0.0 || counter.after.max > 0.0)
        .collect::<Vec<_>>();
    for counter in receipt_counters.iter().filter(|counter| counter.changed()) {
        changed_counts.push(changed("receipt-counter", &counter.name, None, counter));
    }

    Ok(DiffAnswer {
        rule: DIFF_RULE.to_owned(),
        before: before_side,
        after: after_side,
        warnings,
        added,
        removed,
        changed_counts,
        changed_verdicts,
        algorithms,
        receipt_counters,
    })
}

fn side(flag: &str, joins: &[(String, Join)]) -> Result<Side, Error> {
    let Some((_, first)) = joins.first() else {
        return Err(Error::Invalid(format!("{flag} names no join")));
    };
    let identity = |join: &Join| (join.receipt.workload.clone(), join.receipt.claim.clone());
    if let Some((label, other)) = joins
        .iter()
        .find(|(_, join)| identity(join) != identity(first))
    {
        return Err(Error::Invalid(format!(
            "{flag} mixes workloads: {} is {}, but {} is {}; the joins of one side must be repeats of one workload",
            joins[0].0,
            workload_of(first),
            label,
            workload_of(other)
        )));
    }
    Ok(Side {
        workload: first.receipt.workload.clone(),
        claim: first.receipt.claim.clone(),
        runs: joins.len(),
        revisions: joins
            .iter()
            .map(|(_, join)| {
                join.receipt.krust_revision.as_deref().map_or_else(
                    || "unknown".to_owned(),
                    |revision| revision[..revision.len().min(12)].to_owned(),
                )
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect(),
        joins: joins.iter().map(|(label, _)| label.clone()).collect(),
    })
}

fn workload_of(join: &Join) -> String {
    match &join.receipt.claim {
        Some(claim) => format!("{} claim {claim}", join.receipt.workload),
        None => join.receipt.workload.clone(),
    }
}

fn workload_text(side: &Side) -> String {
    match &side.claim {
        Some(claim) => format!("{} claim {claim}", side.workload),
        None => side.workload.clone(),
    }
}

fn declared(join: &Join) -> BTreeSet<String> {
    join.algorithms
        .iter()
        .filter(|algorithm| algorithm.declared)
        .map(|algorithm| algorithm.id.clone())
        .collect()
}

fn joins_declared(joins: &[(String, Join)]) -> BTreeSet<String> {
    joins.iter().flat_map(|(_, join)| declared(join)).collect()
}

fn row<'a>(join: &'a Join, id: &str) -> Option<&'a crate::AlgorithmRun> {
    join.algorithms.iter().find(|algorithm| algorithm.id == id)
}

fn column(joins: &[(String, Join)], value: impl Fn(&Join) -> f64) -> Vec<f64> {
    joins.iter().map(|(_, join)| value(join)).collect()
}

fn algorithm_nodes(join: &Join) -> impl Iterator<Item = (&str, &str)> {
    join.nodes
        .iter()
        .filter(|node| node.kind == "algorithm")
        .map(|node| (node.id.as_str(), node.verdict.as_str()))
}

/// The verdict the joins of one side give `id`: one verdict, `mixed a/b` when repeats disagree,
/// or `absent` when no join has a node for it.
fn verdict(joins: &[(String, Join)], id: &str) -> String {
    let verdicts = joins
        .iter()
        .map(|(_, join)| {
            algorithm_nodes(join)
                .find(|(node, _)| *node == id)
                .map_or("absent", |(_, verdict)| verdict)
        })
        .collect::<BTreeSet<_>>();
    if verdicts.len() == 1 {
        verdicts.into_iter().next().unwrap_or("absent").to_owned()
    } else {
        format!(
            "mixed {}",
            verdicts.into_iter().collect::<Vec<_>>().join("/")
        )
    }
}

fn changed(kind: &str, id: &str, counter: Option<&str>, delta: &CountDelta) -> ChangedCount {
    ChangedCount {
        kind: kind.to_owned(),
        id: id.to_owned(),
        counter: counter.map(ToOwned::to_owned),
        before: delta.before,
        after: delta.after,
        delta: delta.delta,
        exact: delta.exact,
    }
}

/// An integer-valued spread: `v`, or `median (min..max)` when repeats disagree.
pub(crate) fn count_text(spread: &Spread) -> String {
    if spread.constant() {
        number(spread.median)
    } else {
        format!(
            "{} ({}..{})",
            number(spread.median),
            number(spread.min),
            number(spread.max)
        )
    }
}

/// A seconds spread: `s`, or `median (min..max)` when repeats disagree.
pub(crate) fn seconds_text(spread: &Spread) -> String {
    if spread.constant() {
        format!("{:.6}", spread.median)
    } else {
        format!(
            "{:.6} ({:.6}..{:.6})",
            spread.median, spread.min, spread.max
        )
    }
}

/// An integer without a fraction, else one decimal.
pub(crate) fn number(value: f64) -> String {
    if value.fract() == 0.0 {
        format!("{value:.0}")
    } else {
        format!("{value:.1}")
    }
}

fn signed(value: f64) -> String {
    if value.fract() == 0.0 {
        format!("{value:+.0}")
    } else {
        format!("{value:+.1}")
    }
}

fn count_delta_text(before: &Spread, after: &Spread, delta: f64, exact: bool) -> String {
    format!(
        "{} -> {} ({}{})",
        count_text(before),
        count_text(after),
        signed(delta),
        if exact { "" } else { ", varies" }
    )
}

fn time_text(delta: &TimeDelta) -> String {
    format!(
        "{} -> {} ({:+.6}, {})",
        seconds_text(&delta.before),
        seconds_text(&delta.after),
        delta.delta,
        delta.class.as_str()
    )
}

fn side_text(side: &Side) -> String {
    format!(
        "{} ({} join{}, krust {})",
        workload_text(side),
        side.runs,
        if side.runs == 1 { "" } else { "s" },
        side.revisions.join(", ")
    )
}

fn list_text(values: &[String]) -> String {
    if values.is_empty() {
        "none".to_owned()
    } else {
        values.join(", ")
    }
}

impl Answer for DiffAnswer {
    fn text(&self) -> String {
        let mut out = String::new();
        let mut line = |text: String| {
            out.push_str(&text);
            out.push('\n');
        };
        line(format!(
            "diff: before {} -> after {}",
            side_text(&self.before),
            side_text(&self.after)
        ));
        line(format!("rule: {}.", self.rule));
        for warning in &self.warnings {
            line(format!("warning: {warning}"));
        }
        line(format!("added algorithms: {}", list_text(&self.added)));
        line(format!("removed algorithms: {}", list_text(&self.removed)));
        line(format!(
            "changed counts ({}; deterministic, exact unless marked varies):",
            self.changed_counts.len()
        ));
        for change in &self.changed_counts {
            let subject = match &change.counter {
                Some(counter) => format!("{} {counter}", change.id),
                None => change.id.clone(),
            };
            line(format!(
                "  {} {subject}: {}",
                change.kind,
                count_delta_text(&change.before, &change.after, change.delta, change.exact)
            ));
        }
        line(format!(
            "changed verdicts ({}):",
            self.changed_verdicts.len()
        ));
        for change in &self.changed_verdicts {
            line(format!(
                "  {}: {} -> {}",
                change.id, change.before, change.after
            ));
        }
        line(format!(
            "algorithms with spans ({}), by absolute self-time delta; seconds are median (min..max):",
            self.algorithms.len()
        ));
        for algorithm in &self.algorithms {
            let verdict = if algorithm.verdict_before == algorithm.verdict_after {
                algorithm.verdict_after.clone()
            } else {
                format!(
                    "{} -> {}",
                    algorithm.verdict_before, algorithm.verdict_after
                )
            };
            line(format!(
                "  {}  spans {}  self {}  total {}  verdict {verdict}",
                algorithm.id,
                count_delta_text(
                    &algorithm.count.before,
                    &algorithm.count.after,
                    algorithm.count.delta,
                    algorithm.count.exact
                ),
                time_text(&algorithm.self_seconds),
                time_text(&algorithm.total_seconds),
            ));
            if !algorithm.counters.is_empty() {
                line(format!(
                    "    declared counters in spans: {}",
                    algorithm
                        .counters
                        .iter()
                        .map(|counter| format!(
                            "{} {}",
                            counter.name,
                            count_delta_text(
                                &counter.before,
                                &counter.after,
                                counter.delta,
                                counter.exact
                            )
                        ))
                        .collect::<Vec<_>>()
                        .join("; ")
                ));
            }
        }
        line(format!(
            "receipt counters nonzero on either side ({}):",
            self.receipt_counters.len()
        ));
        for counter in &self.receipt_counters {
            line(format!(
                "  {}: {}",
                counter.name,
                count_delta_text(
                    &counter.before,
                    &counter.after,
                    counter.delta,
                    counter.exact
                )
            ));
        }
        out
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::{
        AGGREGATION_RULE, AlgorithmCounter, AlgorithmRun, NodeRun, Receipt, ReceiptCounter,
        Summary, VERDICT_RULE, Verdict,
    };

    /// A join of `workload` at `revision` with the given algorithm rows and receipt counters.
    pub(crate) fn join(
        workload: &str,
        revision: &str,
        algorithms: Vec<AlgorithmRun>,
        counters: &[(&str, u64)],
    ) -> Join {
        let nodes = algorithms
            .iter()
            .filter(|algorithm| algorithm.declared)
            .map(|algorithm| NodeRun {
                kind: "algorithm".to_owned(),
                id: algorithm.id.clone(),
                verdict: if algorithm.count > 0 {
                    Verdict::Ran
                } else {
                    Verdict::Unknown
                },
                evidence: "span".to_owned(),
                reason: String::new(),
            })
            .collect();
        Join {
            schema_version: JOIN_SCHEMA_VERSION,
            aggregation_rule: AGGREGATION_RULE.to_owned(),
            verdict_rule: VERDICT_RULE.to_owned(),
            receipt: Receipt {
                directory: format!("receipts/{workload}"),
                workload: workload.to_owned(),
                claim: None,
                timestamp: None,
                krust_revision: Some(revision.to_owned()),
                binary_sha256: None,
                metadata_schema: "1".to_owned(),
                timings_schema: "1".to_owned(),
                current_timings_schema: 1,
                timings_partial: false,
                counter_schema: "10".to_owned(),
                current_counter_schema: 10,
                counters_partial: false,
                trace_schema: "chrome-trace-event-B/E".to_owned(),
                tools: Vec::new(),
                revisions: Vec::new(),
                coverage: None,
            },
            summary: Summary {
                largest_self_time_algorithm: None,
                largest_self_seconds: 0.0,
                declared_algorithms: algorithms.len(),
                ran_algorithms: 0,
                not_run_algorithms: 0,
                unknown_algorithms: 0,
                not_run_backend_algorithms: Vec::new(),
                unknown_backend_algorithms: Vec::new(),
                span_bypasses: Vec::new(),
            },
            algorithms,
            phases: Vec::new(),
            observed_nests: Vec::new(),
            observed_contains: Vec::new(),
            receipt_counters: counters
                .iter()
                .map(|(name, value)| ReceiptCounter {
                    name: (*name).to_owned(),
                    value: *value,
                    declared_in_graph: true,
                })
                .collect(),
            nodes,
            edges: Vec::new(),
        }
    }

    /// A declared algorithm row with declared counters as `(name, trace_total, trace_self)`.
    pub(crate) fn run(
        id: &str,
        count: u64,
        self_seconds: f64,
        total_seconds: f64,
        counters: &[(&str, u64, u64)],
    ) -> AlgorithmRun {
        AlgorithmRun {
            id: id.to_owned(),
            declared: true,
            area: None,
            span_policy: Some("per call".to_owned()),
            count,
            total_seconds,
            self_seconds,
            cost: Vec::new(),
            counters: counters
                .iter()
                .map(|(name, total, own)| AlgorithmCounter {
                    name: (*name).to_owned(),
                    observation: None,
                    declared: true,
                    trace_total: Some(*total),
                    trace_self: Some(*own),
                    receipt_total: Some(*total),
                })
                .collect(),
        }
    }

    fn labelled(joins: Vec<Join>) -> Vec<(String, Join)> {
        joins
            .into_iter()
            .enumerate()
            .map(|(index, join)| (format!("rep-{}", index + 1), join))
            .collect()
    }

    fn find<'a>(answer: &'a DiffAnswer, id: &str) -> &'a AlgorithmDelta {
        answer
            .algorithms
            .iter()
            .find(|algorithm| algorithm.id == id)
            .expect("algorithm row")
    }

    #[test]
    fn spread_takes_the_median_and_range() {
        let odd = Spread::of(&[3.0, 1.0, 2.0]);
        assert_eq!((odd.median, odd.min, odd.max), (2.0, 1.0, 3.0));
        let even = Spread::of(&[4.0, 1.0, 2.0, 10.0]);
        assert_eq!((even.median, even.min, even.max), (3.0, 1.0, 10.0));
        assert!(Spread::of(&[5.0, 5.0]).constant());
        assert!(!even.constant());
        assert_eq!(Spread::of(&[]), Spread::default());
    }

    #[test]
    fn time_deltas_are_classified_against_the_ranges() {
        let slow = Spread::of(&[1.0, 1.1, 1.2]);
        let overlapping = Spread::of(&[1.15, 1.3, 1.4]);
        let fast = Spread::of(&[0.5, 0.6, 0.7]);
        assert_eq!(
            TimeClass::of(&slow, &overlapping, 3, 3),
            TimeClass::WithinNoise
        );
        assert_eq!(TimeClass::of(&slow, &fast, 3, 3), TimeClass::Faster);
        assert_eq!(TimeClass::of(&fast, &slow, 3, 3), TimeClass::Slower);
        assert_eq!(TimeClass::of(&slow, &fast, 1, 3), TimeClass::Unreplicated);
        assert_eq!(TimeClass::of(&slow, &fast, 3, 1), TimeClass::Unreplicated);
    }

    #[test]
    fn diff_reports_exact_counts_noise_and_graph_changes() {
        let before = labelled(vec![
            join(
                "w",
                "aaaa",
                vec![
                    run("a.hot", 10, 1.0, 2.0, &[("a.pairs", 100, 40)]),
                    run("a.steady", 4, 0.5, 0.5, &[]),
                    run("a.gone", 1, 0.1, 0.1, &[]),
                ],
                &[("a.pairs", 100), ("a.idle", 0)],
            ),
            join(
                "w",
                "aaaa",
                vec![
                    run("a.hot", 10, 1.2, 2.2, &[("a.pairs", 100, 40)]),
                    run("a.steady", 4, 0.6, 0.6, &[]),
                    run("a.gone", 1, 0.1, 0.1, &[]),
                ],
                &[("a.pairs", 100), ("a.idle", 0)],
            ),
        ]);
        let after = labelled(vec![
            join(
                "w",
                "bbbb",
                vec![
                    run("a.hot", 6, 0.4, 1.0, &[("a.pairs", 60, 20)]),
                    run("a.steady", 4, 0.55, 0.55, &[]),
                    run("a.new", 2, 0.2, 0.2, &[]),
                ],
                &[("a.pairs", 60), ("a.idle", 0)],
            ),
            join(
                "w",
                "bbbb",
                vec![
                    run("a.hot", 6, 0.5, 1.1, &[("a.pairs", 60, 20)]),
                    run("a.steady", 4, 0.65, 0.65, &[]),
                    run("a.new", 2, 0.2, 0.2, &[]),
                ],
                &[("a.pairs", 60), ("a.idle", 0)],
            ),
        ]);
        let answer = diff(&before, &after).expect("diff");
        assert_eq!(answer.added, ["a.new"]);
        assert_eq!(answer.removed, ["a.gone"]);
        assert!(answer.warnings.is_empty());

        let hot = find(&answer, "a.hot");
        assert_eq!(hot.count.delta, -4.0);
        assert!(hot.count.exact);
        assert!((hot.self_seconds.before.median - 1.1).abs() < 1e-12);
        assert_eq!(hot.self_seconds.class, TimeClass::Faster);
        assert_eq!(hot.counters[0].delta, -40.0);
        let steady = find(&answer, "a.steady");
        assert_eq!(steady.count.delta, 0.0);
        assert_eq!(steady.self_seconds.class, TimeClass::WithinNoise);
        assert_eq!(
            answer.algorithms[0].id, "a.hot",
            "largest |self delta| first"
        );

        let changes = answer
            .changed_counts
            .iter()
            .map(|change| (change.kind.as_str(), change.id.as_str(), change.delta))
            .collect::<Vec<_>>();
        assert!(changes.contains(&("span", "a.hot", -4.0)));
        assert!(changes.contains(&("span", "a.gone", -1.0)));
        assert!(changes.contains(&("span", "a.new", 2.0)));
        assert!(changes.contains(&("algorithm-counter", "a.hot", -40.0)));
        assert!(changes.contains(&("receipt-counter", "a.pairs", -40.0)));
        assert!(!changes.iter().any(|(_, id, _)| *id == "a.steady"));
        assert_eq!(
            answer
                .receipt_counters
                .iter()
                .map(|counter| counter.name.as_str())
                .collect::<Vec<_>>(),
            ["a.pairs"],
            "counters zero on both sides are omitted"
        );
        assert!(
            answer
                .changed_verdicts
                .iter()
                .any(|change| change.id == "a.gone" && change.after == "absent")
        );

        let text = answer.text();
        assert!(text.contains("span a.hot: 10 -> 6 (-4)"), "{text}");
        assert!(text.contains("within noise"), "{text}");
        answer.toml().expect("toml");
    }

    #[test]
    fn one_join_per_side_is_unreplicated_and_varying_counts_are_marked() {
        let before = labelled(vec![join("w", "a", vec![run("x", 3, 1.0, 1.0, &[])], &[])]);
        let after = labelled(vec![join("w", "b", vec![run("x", 3, 9.0, 9.0, &[])], &[])]);
        let answer = diff(&before, &after).expect("diff");
        let row = find(&answer, "x");
        assert_eq!(row.self_seconds.class, TimeClass::Unreplicated);
        assert_eq!(row.total_seconds.class, TimeClass::Unreplicated);
        assert!(answer.changed_counts.is_empty());

        let varying = labelled(vec![
            join("w", "b", vec![run("x", 3, 1.0, 1.0, &[])], &[]),
            join("w", "b", vec![run("x", 4, 1.0, 1.0, &[])], &[]),
        ]);
        let answer = diff(&before, &varying).expect("diff");
        let change = &answer.changed_counts[0];
        assert_eq!((change.kind.as_str(), change.exact), ("span", false));
        assert!(answer.text().contains("varies"));
    }

    #[test]
    fn diff_refuses_mixed_sides_and_other_schemas() {
        let mixed = labelled(vec![
            join("w", "a", Vec::new(), &[]),
            join("v", "a", Vec::new(), &[]),
        ]);
        let error = diff(&mixed, &mixed).expect_err("mixed workloads");
        assert!(error.to_string().contains("mixes workloads"), "{error}");

        let directory = std::env::temp_dir().join(format!("algo-diff-{}", std::process::id()));
        fs::create_dir_all(&directory).expect("temporary directory");
        let path = directory.join("old.toml");
        fs::write(&path, "schema_version = 1\n").expect("write");
        let error = read_join_file(&path).expect_err("schema 1").to_string();
        assert_eq!(error.matches(&path.display().to_string()).count(), 1);
        assert!(error.contains("join schema 1"), "{error}");
        let path = directory.join("current.toml");
        fs::write(
            &path,
            crate::canonical_join_toml(&join("w", "a", vec![run("x", 1, 0.1, 0.1, &[])], &[]))
                .expect("serialize"),
        )
        .expect("write");
        assert_eq!(read_join_file(&path).expect("read").algorithms.len(), 1);
        fs::remove_dir_all(&directory).expect("clean up");
    }
}
