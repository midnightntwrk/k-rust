//! The cost atlas: where each workload's measured time goes by algorithm, and how each
//! algorithm's work grows along a parameter ladder.
//!
//! The atlas reads an `atlas.toml` index of receipts (schema [`INDEX_SCHEMA_VERSION`]) and the
//! joins it names. Every number follows from the joins and the index's whole-run measurements by
//! the rules [`SHARE_RULE`], [`AMDAHL_RULE`], [`CUT_RULE`], [`SLOPE_RULE`], [`RUN_GROWTH_RULE`],
//! and [`STALENESS_RULE`], which the rendered atlas repeats in its header.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{self, Write as _},
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use serde::{Deserialize, Deserializer, Serialize};

use crate::{
    Cost, Error, Graph, Join,
    diff::{Spread, number, read_join_file},
    profile::{NO_ALGORITHM, SampledProfile, read_profile},
};

/// The schema of the `atlas.toml` receipt index this module reads.
pub const INDEX_SCHEMA_VERSION: u32 = 1;

/// The schema of the atlas TOML this module writes.
pub const ATLAS_SCHEMA_VERSION: u32 = 1;

/// How an algorithm's share of a workload is computed.
pub const SHARE_RULE: &str = "an algorithm's share of a run is its self seconds divided by the run's span seconds, the sum of self seconds over every algorithm of the join. Because self time subtracts the directly nested algorithm spans, that sum is the time inside outermost algorithm spans, summed over threads. The denominator is span time, not wall time, because both come from the same spans on the same clock, while wall time also holds process start, unspanned work, and trace writing that no algorithm row can claim. A workload's share is the median of its per-run shares";

/// How the Amdahl ceiling is computed from a share.
pub const AMDAHL_RULE: &str = "the ceiling of an algorithm is 1 / (1 - share): the factor by which the workload's span time would shrink if the algorithm's self time were zero and nothing else changed, unbounded at share 1. On one thread span time is at most wall time, so the ceiling also bounds the wall-time speedup, which is 1 / (1 - share x span/wall)";

/// Which algorithms a workload lists.
pub const CUT_RULE: &str = "a workload lists its algorithms by decreasing share until the listed shares reach 90 % of span time, then every further algorithm whose share exceeds 1 %; the others are counted in the workload table. A workload is its receipts without a parameter, or, for a ladder, its receipts at the largest parameter";

/// How a growth exponent is fitted along a ladder.
pub const SLOPE_RULE: &str = "for each ladder, each algorithm whose median span count is positive at two or more parameter values is fitted by ordinary least squares of ln(value) on ln(param), over the parameter values where the value's median over repeats is positive, for its span count, its self seconds, and each counter its card declares, measured inside its spans including nested spans (trace_total). The slope is the growth exponent, points is the number of parameter values fitted, R2 is 1 - residual / total sum of squares (absent when every fitted value is equal), and a fit from fewer than three points is marked *. The card's cost bounds and variable are printed beside the fit, not parsed. In the markdown, the per-call slope is the self-seconds slope minus the span-count slope, the growth of one invocation's own time; rows are sorted by self-seconds slope, and an algorithm whose span-count, self-seconds and counter slopes are all below 0.2 in magnitude (or absent) is listed on one Flat line instead of a row";

/// A ladder whose peak-RSS slope exceeds this is marked by [`RUN_GROWTH_RULE`].
pub const MEMORY_MARK_SLOPE: f64 = 1.5;

/// How a ladder's whole-run growth is fitted and when a ladder is marked.
pub const RUN_GROWTH_RULE: &str = "for each ladder, the wall seconds, peak RSS and stdout bytes of each receipt's untraced measured run (the index's wall_seconds, peak_rss_kib and stdout_bytes) are taken as the median over the repeats that record them at each parameter value, and fitted against the parameter over the values where that median is positive: by the least squares of the Slope rule, with the same points, R2 and * marks, and by the top slope, ln(v2 / v1) / ln(p2 / p1) between the two largest such parameter values p1 < p2. They measure the whole process, not an algorithm, so no card bound is printed beside them and no algorithm row carries a space bound. A measurement that is a fixed baseline b (the binary, the loaded definition) plus a growing part c p^k has every such slope between 0 and k, lowered most where b dominates, which is at the smallest parameter values; the top slope is the least lowered. A ladder is marked when the peak-RSS slope or top slope exceeds 1.5: the rule is meant for ladders whose parameter grows the input at most linearly, as every ladder of scripts/algo-workloads.toml does, so a marked ladder's memory grows superlinearly in its input. A stdout slope close to the peak-RSS slope points at output-driven memory (a result that is built or held whole before it is written); a stdout slope well below it points at the algorithms";

/// How a workload's observed nesting outline is built.
pub const NESTING_RULE: &str = "each workload's outline is the nesting observed on its run, not a declared relation: a child under a parent means the child's span opened while the parent's span was open on the same thread (the join's observed_nest edges), and algorithms without spans do not appear. With repeats, the edges are the first repeat's, and the outline says whether every repeat has the same edges. Roots are algorithms with a positive span count and no observed parent other than themselves; algorithms reachable only through a cycle are added as roots. Children are ordered by decreasing median total-seconds share of span time; a line reads `id - nested N x - total X % - self Y %`, with the span count in place of the nest count for a root. Nesting of an algorithm inside itself is a `(recursive, N x)` note, not a child. An algorithm with several parents is shown in full under the parent with the largest nest count and as `= id` under the others; `^ id (cycle)` marks a child that is already an ancestor on the path. Children and roots below 0.5 % total share are folded into a `+k more (Z %)` line with their summed total share";

/// When a row is stale.
pub const STALENESS_RULE: &str = "every row is measured at the index commit. `atlas --check` reports an algorithm stale when `git diff --name-only <commit> -- <files>` in the checkout names one of the files of its anchor and sites in the graph beside a receipt's join, which is the graph at the receipt commit, and a listed uncarded function of a profile stale when that diff names its own file; it exits 1 when a listed row is stale. A change outside those files, such as in a callee or in a representation the algorithm reads, is not detected";

/// How sampled shares enter the atlas.
pub const SAMPLED_RULE: &str = "a receipt with a profile (`algo-receipt.sh --profile`) adds the CPU samples of one untraced `samply` run of the same command, attributed to algorithms by `algo-graph profile` (its ownership rule is in each profile.toml): sampled self % is the share of the run's samples whose innermost card-owned frame is the algorithm's, sampled total % the share with any frame it owns. Sampled shares divide by all samples of the process (CPU time on every thread), traced shares by span time, so they differ by the work outside spans as well as by tracing overhead. A workload uses the profile of its first profiled receipt at its parameter. The uncarded table lists workspace functions no card site contains: self % has the function as the innermost workspace frame, inclusive % has it anywhere inside the innermost card-owned frame, and under names the algorithm owning that frame (`(truncated stack)` when the unwinder stopped before reaching an owned frame, on recursion deeper than samply's stack copy). It lists up to 10 functions whose inclusive or self share reaches 1 %. A ladder's sampled table gives the inclusive share of the top uncarded functions at each profiled parameter";

/// The `atlas.toml` index of receipts.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct AtlasIndex {
    pub schema: u32,
    /// The full commit at which every receipt was recorded.
    pub commit: String,
    #[serde(rename = "receipt", default)]
    pub receipts: Vec<IndexReceipt>,
}

/// One receipt of the index.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct IndexReceipt {
    pub workload: String,
    /// `kcompile`, `kprove`, or `krun`.
    pub command: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub param_name: Option<String>,
    #[serde(
        default,
        deserialize_with = "optional_number",
        skip_serializing_if = "Option::is_none"
    )]
    pub param: Option<f64>,
    /// 1-based repeat index.
    #[serde(default = "first_repeat")]
    pub repeat: u32,
    /// The join, relative to the index file.
    pub join: String,
    #[serde(
        default,
        deserialize_with = "optional_number",
        skip_serializing_if = "Option::is_none"
    )]
    pub wall_seconds: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub peak_rss_kib: Option<u64>,
    /// The size of the measured run's standard output.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stdout_bytes: Option<u64>,
    /// The profile.toml of a sampled run, relative to the index file.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub profile: Option<String>,
}

fn first_repeat() -> u32 {
    1
}

/// A TOML integer or float as `f64`.
fn optional_number<'de, D: Deserializer<'de>>(deserializer: D) -> Result<Option<f64>, D::Error> {
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum Number {
        Integer(i64),
        Float(f64),
    }
    Ok(
        Option::<Number>::deserialize(deserializer)?.map(|number| match number {
            Number::Integer(value) => value as f64,
            Number::Float(value) => value,
        }),
    )
}

/// One index receipt with its join and the graph beside the join, when there is one.
#[derive(Clone, Debug)]
pub struct LoadedReceipt {
    pub entry: IndexReceipt,
    pub join_path: PathBuf,
    pub join: Join,
    /// `graph.toml` in the join's directory: the graph at the receipt commit.
    pub graph: Option<Graph>,
    /// The sampled profile the entry names.
    pub profile: Option<SampledProfile>,
}

/// Read an index and every join it names. Errors name the file they concern.
pub fn read_atlas_index(path: &Path) -> Result<(AtlasIndex, Vec<LoadedReceipt>), Error> {
    let at = |error: &dyn fmt::Display| Error::Invalid(format!("{}: {error}", path.display()));
    let source = fs::read_to_string(path).map_err(|error| at(&error))?;
    let table = toml::from_str::<toml::Table>(&source).map_err(|error| at(&error))?;
    let schema = table.get("schema").and_then(toml::Value::as_integer);
    if schema != Some(i64::from(INDEX_SCHEMA_VERSION)) {
        return Err(at(&format!(
            "index schema {}, but this tool reads schema {INDEX_SCHEMA_VERSION}",
            schema.map_or_else(|| "absent".to_owned(), |schema| schema.to_string())
        )));
    }
    let index: AtlasIndex = toml::Value::Table(table)
        .try_into()
        .map_err(|error| at(&error))?;
    let base = path.parent().unwrap_or_else(|| Path::new("."));
    let receipts = index
        .receipts
        .iter()
        .map(|entry| {
            let join_path = base.join(&entry.join);
            let join = read_join_file(&join_path)?;
            let graph_path = join_path
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .join("graph.toml");
            let graph = if graph_path.exists() {
                let source = fs::read_to_string(&graph_path).map_err(|error| {
                    Error::Invalid(format!("{}: {error}", graph_path.display()))
                })?;
                let mut graph: Graph = toml::from_str(&source).map_err(|error| {
                    Error::Invalid(format!("{}: {error}", graph_path.display()))
                })?;
                graph.sort();
                Some(graph)
            } else {
                None
            };
            let profile = entry
                .profile
                .as_ref()
                .map(|profile| read_profile(&base.join(profile)))
                .transpose()?;
            Ok(LoadedReceipt {
                entry: entry.clone(),
                join_path,
                join,
                graph,
                profile,
            })
        })
        .collect::<Result<Vec<_>, Error>>()?;
    Ok((index, receipts))
}

/// The rules the atlas repeats.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct Rules {
    pub share: String,
    pub amdahl: String,
    pub cut: String,
    pub slope: String,
    pub run_growth: String,
    pub staleness: String,
    pub nesting: String,
    pub sampled: String,
}

impl Rules {
    fn current() -> Self {
        Self {
            share: SHARE_RULE.to_owned(),
            amdahl: AMDAHL_RULE.to_owned(),
            cut: CUT_RULE.to_owned(),
            slope: SLOPE_RULE.to_owned(),
            run_growth: RUN_GROWTH_RULE.to_owned(),
            staleness: STALENESS_RULE.to_owned(),
            nesting: NESTING_RULE.to_owned(),
            sampled: SAMPLED_RULE.to_owned(),
        }
    }
}

/// The cost atlas of one index.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct Atlas {
    pub schema: u32,
    pub commit: String,
    /// The command that regenerates the atlas.
    pub regenerate: String,
    pub rules: Rules,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<String>,
    #[serde(rename = "workload")]
    pub workloads: Vec<WorkloadCost>,
    /// The workloads of the share matrix, in the order of every row's `shares`.
    pub matrix_columns: Vec<String>,
    #[serde(rename = "matrix_row")]
    pub matrix: Vec<MatrixRow>,
    #[serde(rename = "ladder")]
    pub ladders: Vec<Ladder>,
}

/// Where one workload's span time goes.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct WorkloadCost {
    pub workload: String,
    pub command: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub param_name: Option<String>,
    /// The ladder parameter of the measured receipts: the largest one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub param: Option<f64>,
    pub runs: usize,
    /// Present when every run records it.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub wall_seconds: Option<Spread>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub peak_rss_kib: Option<Spread>,
    /// The sum of algorithm self seconds per run: the time inside outermost algorithm spans.
    pub span_seconds: Spread,
    /// Median span seconds over median wall seconds.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span_over_wall: Option<f64>,
    /// Algorithms with a span that the cut leaves out, and their summed median share.
    pub omitted_algorithms: usize,
    pub omitted_share: f64,
    #[serde(rename = "algorithm")]
    pub rows: Vec<ShareRow>,
    /// The observed nesting outline by [`NESTING_RULE`].
    pub nesting: Nesting,
    /// Sampled shares by [`SAMPLED_RULE`], when a receipt has a profile.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sampled: Option<SampledCost>,
    /// The median share of every algorithm with a span, for the matrix.
    #[serde(skip)]
    shares: BTreeMap<String, f64>,
}

/// One algorithm's share of one workload.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct ShareRow {
    pub id: String,
    pub commit: String,
    pub share: Spread,
    /// `1 / (1 - share median)`; absent when the share is 1, where it is unbounded.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ceiling: Option<f64>,
    pub self_seconds: Spread,
    pub span_count: Spread,
    /// Counters that moved in its spans outside nested algorithm spans (`trace_self`).
    #[serde(rename = "counter", skip_serializing_if = "Vec::is_empty")]
    pub counters: Vec<MovedCounter>,
    /// Sampled self and total share by [`SAMPLED_RULE`], when the workload has a profile.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sampled_self: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sampled_total: Option<f64>,
}

/// A workload's sampled shares.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct SampledCost {
    /// The profile.toml, relative to the index.
    pub profile: String,
    pub samples: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rate_hz: Option<f64>,
    pub owned_share: f64,
    pub uncarded_leaf_share: f64,
    pub outside_workspace_share: f64,
    pub truncated_share: f64,
    /// Samples of truncated stacks without an owned frame.
    pub truncated_unowned_share: f64,
    /// Algorithms with a sampled self share of at least 1 % that the traced table does not list.
    #[serde(rename = "unlisted")]
    pub unlisted: Vec<SampledShare>,
    #[serde(rename = "uncarded")]
    pub uncarded: Vec<UncardedRow>,
}

/// An algorithm's sampled shares.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct SampledShare {
    pub id: String,
    pub self_share: f64,
    pub total_share: f64,
}

/// One uncarded function of a workload.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct UncardedRow {
    /// `file::symbol`.
    pub function: String,
    pub self_share: f64,
    pub inclusive_share: f64,
    /// The algorithms its inclusive samples run under, with the share of them.
    pub under: String,
}

/// The rows the uncarded table of a workload lists at most.
const UNCARDED_ROWS: usize = 10;

/// The uncarded functions of one workload's profile by [`SAMPLED_RULE`].
fn uncarded_rows(profile: &SampledProfile) -> Vec<UncardedRow> {
    let leaf = profile
        .leaves
        .iter()
        .map(|row| (row.function.as_str(), row))
        .collect::<BTreeMap<_, _>>();
    let inclusive = profile
        .inclusive
        .iter()
        .map(|row| (row.function.as_str(), row))
        .collect::<BTreeMap<_, _>>();
    let mut rows = leaf
        .keys()
        .chain(inclusive.keys())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .map(|function| {
            let under = inclusive
                .get(function)
                .or_else(|| leaf.get(function))
                .map(|row| crate::profile::under_text(row))
                .unwrap_or_else(|| NO_ALGORITHM.to_owned());
            UncardedRow {
                function: (*function).to_owned(),
                self_share: profile.share(leaf.get(function).map_or(0, |row| row.samples)),
                inclusive_share: profile
                    .share(inclusive.get(function).map_or(0, |row| row.samples)),
                under,
            }
        })
        .filter(|row| row.self_share >= 0.01 || row.inclusive_share >= 0.01)
        .collect::<Vec<_>>();
    rows.sort_by(|left, right| {
        right
            .inclusive_share
            .total_cmp(&left.inclusive_share)
            .then_with(|| right.self_share.total_cmp(&left.self_share))
            .then_with(|| left.function.cmp(&right.function))
    });
    rows.truncate(UNCARDED_ROWS);
    rows
}

/// A workload's observed nesting outline.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct Nesting {
    /// The join whose `observed_nest` edges built the outline: the first repeat's.
    pub edges_from: String,
    /// Every measured repeat has the same `observed_nest` edges.
    pub repeats_agree: bool,
    /// The outline in reading order.
    #[serde(rename = "line")]
    pub lines: Vec<NestLine>,
}

/// One line of a nesting outline.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct NestLine {
    /// Indentation level; roots are at 0.
    pub depth: usize,
    /// `node` (shown in full), `ref` (shown in full under another parent), `cycle` (already an
    /// ancestor on this path), or `more` (folded children).
    pub kind: String,
    /// The algorithm id; empty for a `more` line.
    pub id: String,
    /// The nest count under its parent, the span count for a root, or the number of folded
    /// algorithms for a `more` line.
    pub count: u64,
    pub root: bool,
    /// Median total seconds over span seconds; summed over the folded algorithms of a `more` line.
    pub total_share: f64,
    /// Median self seconds over span seconds; zero for a `more` line.
    pub self_share: f64,
    /// How often its span opened inside its own open span.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub recursive: Option<u64>,
}

/// One counter an algorithm moved in its own code.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct MovedCounter {
    pub name: String,
    /// The algorithm's card declares the counter.
    pub declared: bool,
    /// Median over runs of the delta inside its spans outside nested algorithm spans.
    pub span_self: f64,
}

/// One algorithm's median share in every workload.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct MatrixRow {
    pub id: String,
    pub commit: String,
    /// Aligned with [`Atlas::matrix_columns`]; zero where it has no span.
    pub shares: Vec<f64>,
    pub max_share: f64,
    pub workloads_over_one_percent: usize,
}

/// A ladder row whose every slope is below this in magnitude does not grow with the parameter.
pub const FLAT_SLOPE: f64 = 0.2;

/// Growth fits along one ladder.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct Ladder {
    pub workload: String,
    pub param_name: String,
    pub params: Vec<f64>,
    /// The peak-RSS slope or top slope exceeds [`MEMORY_MARK_SLOPE`] ([`RUN_GROWTH_RULE`]).
    pub memory_marked: bool,
    /// Whole-run fits by [`RUN_GROWTH_RULE`].
    pub wall_seconds: RunFit,
    pub peak_rss_kib: RunFit,
    pub stdout_bytes: RunFit,
    /// The whole-run medians at each parameter value, aligned with `params`.
    #[serde(rename = "step")]
    pub steps: Vec<LadderStep>,
    #[serde(rename = "algorithm")]
    pub rows: Vec<LadderRow>,
    /// The parameters with a profile, for the `sampled` rows.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub sampled_params: Vec<f64>,
    /// Uncarded functions by [`SAMPLED_RULE`].
    #[serde(rename = "sampled", skip_serializing_if = "Vec::is_empty")]
    pub sampled: Vec<SampledLadderRow>,
}

/// The whole-run measurements at one parameter value of a ladder: each is the median over the
/// repeats that record it, absent when none does.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct LadderStep {
    pub param: f64,
    pub runs: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub wall_seconds: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub peak_rss_kib: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stdout_bytes: Option<f64>,
}

/// The growth of one whole-run measurement along a ladder by [`RUN_GROWTH_RULE`].
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct RunFit {
    /// The least-squares fit over every parameter value where the median is positive.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fit: Option<Fit>,
    /// The slope between the two largest parameter values where the median is positive.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub top_slope: Option<f64>,
    /// Those two parameter values, when there is a top slope.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub top_params: Vec<f64>,
}

impl RunFit {
    /// Fit `(param, value)` points in increasing parameter order.
    fn of(points: &[(f64, f64)]) -> Self {
        let positive = points
            .iter()
            .copied()
            .filter(|(param, value)| *param > 0.0 && *value > 0.0)
            .collect::<Vec<_>>();
        let top = positive
            .len()
            .checked_sub(2)
            .and_then(|start| fit_power_law(&positive[start..]));
        Self {
            fit: fit_power_law(&positive),
            top_slope: top.map(|top| top.slope),
            top_params: if top.is_some() {
                positive[positive.len() - 2..]
                    .iter()
                    .map(|(param, _)| *param)
                    .collect()
            } else {
                Vec::new()
            },
        }
    }

    /// Whether the fit or the top slope exceeds `threshold`.
    fn exceeds(&self, threshold: f64) -> bool {
        self.fit.is_some_and(|fit| fit.slope > threshold)
            || self.top_slope.is_some_and(|slope| slope > threshold)
    }
}

/// The whole-run steps of a ladder, the fits of each measurement, and the memory mark, by
/// [`RUN_GROWTH_RULE`].
fn run_growth(receipts: &[&LoadedReceipt]) -> (Vec<LadderStep>, [RunFit; 3], bool) {
    let mut by_param = BTreeMap::<u64, (f64, Vec<&IndexReceipt>)>::new();
    for receipt in receipts {
        if let Some(param) = receipt.entry.param {
            by_param
                .entry(param.to_bits())
                .or_insert_with(|| (param, Vec::new()))
                .1
                .push(&receipt.entry);
        }
    }
    let mut groups = by_param.into_values().collect::<Vec<_>>();
    groups.sort_by(|left, right| left.0.total_cmp(&right.0));
    let median = |entries: &[&IndexReceipt], value: fn(&IndexReceipt) -> Option<f64>| {
        let values = entries
            .iter()
            .filter_map(|entry| value(entry))
            .collect::<Vec<_>>();
        (!values.is_empty()).then(|| Spread::of(&values).median)
    };
    let steps = groups
        .iter()
        .map(|(param, entries)| LadderStep {
            param: *param,
            runs: entries.len(),
            wall_seconds: median(entries, |entry| entry.wall_seconds),
            peak_rss_kib: median(entries, |entry| entry.peak_rss_kib.map(|kib| kib as f64)),
            stdout_bytes: median(entries, |entry| {
                entry.stdout_bytes.map(|bytes| bytes as f64)
            }),
        })
        .collect::<Vec<_>>();
    let fit = |value: fn(&LadderStep) -> Option<f64>| {
        RunFit::of(
            &steps
                .iter()
                .filter_map(|step| Some((step.param, value(step)?)))
                .collect::<Vec<_>>(),
        )
    };
    let fits = [
        fit(|step| step.wall_seconds),
        fit(|step| step.peak_rss_kib),
        fit(|step| step.stdout_bytes),
    ];
    let marked = fits[1].exceeds(MEMORY_MARK_SLOPE);
    (steps, fits, marked)
}

/// One uncarded function's inclusive share at each profiled parameter of a ladder.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct SampledLadderRow {
    pub function: String,
    /// Aligned with [`Ladder::sampled_params`].
    pub inclusive_shares: Vec<f64>,
}

/// The uncarded functions a ladder follows per profiled parameter: the top ones at each.
const LADDER_SAMPLED_TOP: usize = 5;

fn sampled_ladder(receipts: &[&LoadedReceipt]) -> (Vec<f64>, Vec<SampledLadderRow>) {
    let mut by_param = BTreeMap::<u64, (f64, &SampledProfile)>::new();
    for receipt in receipts {
        if let (Some(param), Some(profile)) = (receipt.entry.param, receipt.profile.as_ref()) {
            by_param.entry(param.to_bits()).or_insert((param, profile));
        }
    }
    let mut steps = by_param.into_values().collect::<Vec<_>>();
    steps.sort_by(|left, right| left.0.total_cmp(&right.0));
    let functions = steps
        .iter()
        .flat_map(|(_, profile)| {
            profile
                .inclusive
                .iter()
                .filter(|row| profile.share(row.samples) >= 0.01)
                .take(LADDER_SAMPLED_TOP)
                .map(|row| row.function.clone())
        })
        .collect::<BTreeSet<_>>();
    let mut rows = functions
        .into_iter()
        .map(|function| SampledLadderRow {
            inclusive_shares: steps
                .iter()
                .map(|(_, profile)| {
                    profile.share(
                        profile
                            .inclusive
                            .iter()
                            .find(|row| row.function == function)
                            .map_or(0, |row| row.samples),
                    )
                })
                .collect(),
            function,
        })
        .collect::<Vec<_>>();
    rows.sort_by(|left, right| {
        right
            .inclusive_shares
            .last()
            .unwrap_or(&0.0)
            .total_cmp(left.inclusive_shares.last().unwrap_or(&0.0))
            .then_with(|| left.function.cmp(&right.function))
    });
    (steps.iter().map(|(param, _)| *param).collect(), rows)
}

/// The growth of one algorithm along a ladder.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct LadderRow {
    pub id: String,
    pub commit: String,
    /// Parameter values at which its median span count is positive.
    pub params_with_spans: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span_count: Option<Fit>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub self_seconds: Option<Fit>,
    #[serde(rename = "counter", skip_serializing_if = "Vec::is_empty")]
    pub counters: Vec<CounterFit>,
    pub cost: Vec<Cost>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub variable: Option<String>,
}

impl LadderRow {
    /// Whether no fitted quantity grows or shrinks with the parameter by `FLAT_SLOPE` or more.
    pub fn is_flat(&self) -> bool {
        [self.span_count.as_ref(), self.self_seconds.as_ref()]
            .into_iter()
            .chain(self.counters.iter().map(|counter| counter.fit.as_ref()))
            .all(|fit| fit.is_none_or(|fit| fit.slope.abs() < FLAT_SLOPE))
    }

    /// The growth exponent of one invocation's self time: self-seconds slope minus span-count
    /// slope.
    pub fn per_call_slope(&self) -> Option<f64> {
        Some(self.self_seconds.as_ref()?.slope - self.span_count.as_ref()?.slope)
    }
}

fn slope_of(fit: Option<&Fit>) -> f64 {
    fit.map_or(f64::NEG_INFINITY, |fit| fit.slope)
}

/// The fit of one declared counter.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct CounterFit {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fit: Option<Fit>,
}

/// A least-squares line through `(ln param, ln value)`.
#[derive(Clone, Copy, Debug, PartialEq, Serialize)]
pub struct Fit {
    pub slope: f64,
    pub points: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub r_squared: Option<f64>,
    pub fewer_than_three: bool,
}

/// Fit `ln(value)` against `ln(param)` over the points where both are positive.
///
/// Returns `None` with fewer than two such points or when they share one parameter value.
pub fn fit_power_law(points: &[(f64, f64)]) -> Option<Fit> {
    let logs = points
        .iter()
        .filter(|(param, value)| *param > 0.0 && *value > 0.0)
        .map(|(param, value)| (param.ln(), value.ln()))
        .collect::<Vec<_>>();
    if logs.len() < 2 {
        return None;
    }
    let count = logs.len() as f64;
    let mean_x = logs.iter().map(|(x, _)| x).sum::<f64>() / count;
    let mean_y = logs.iter().map(|(_, y)| y).sum::<f64>() / count;
    let sxx = logs.iter().map(|(x, _)| (x - mean_x).powi(2)).sum::<f64>();
    if sxx == 0.0 {
        return None;
    }
    let sxy = logs
        .iter()
        .map(|(x, y)| (x - mean_x) * (y - mean_y))
        .sum::<f64>();
    let slope = sxy / sxx;
    let intercept = mean_y - slope * mean_x;
    let total = logs.iter().map(|(_, y)| (y - mean_y).powi(2)).sum::<f64>();
    let residual = logs
        .iter()
        .map(|(x, y)| (y - intercept - slope * x).powi(2))
        .sum::<f64>();
    Some(Fit {
        slope,
        points: logs.len(),
        r_squared: (total > 0.0).then(|| 1.0 - residual / total),
        fewer_than_three: logs.len() < 3,
    })
}

/// The Amdahl ceiling `1 / (1 - share)`, `None` when unbounded.
pub fn amdahl_ceiling(share: f64) -> Option<f64> {
    (share < 1.0).then(|| 1.0 / (1.0 - share))
}

/// Per-run observations of one algorithm.
#[derive(Clone, Debug, Default)]
struct Observed {
    count: f64,
    self_seconds: f64,
    total_seconds: f64,
    /// Declared counters inside its spans, including nested spans.
    declared_total: BTreeMap<String, f64>,
    /// Every counter inside its spans outside nested spans, with whether the card declares it.
    own: BTreeMap<String, (bool, f64)>,
}

fn observe(join: &Join) -> BTreeMap<String, Observed> {
    join.algorithms
        .iter()
        .filter(|algorithm| algorithm.count > 0)
        .map(|algorithm| {
            let mut observed = Observed {
                count: algorithm.count as f64,
                self_seconds: algorithm.self_seconds,
                total_seconds: algorithm.total_seconds,
                ..Observed::default()
            };
            for counter in &algorithm.counters {
                if counter.declared {
                    observed.declared_total.insert(
                        counter.name.clone(),
                        counter.trace_total.unwrap_or(0) as f64,
                    );
                }
                observed.own.insert(
                    counter.name.clone(),
                    (counter.declared, counter.trace_self.unwrap_or(0) as f64),
                );
            }
            (algorithm.id.clone(), observed)
        })
        .collect()
}

fn span_seconds(observed: &BTreeMap<String, Observed>) -> f64 {
    observed
        .values()
        .map(|observed| observed.self_seconds)
        .sum()
}

fn short(commit: &str) -> &str {
    &commit[..commit.len().min(12)]
}

/// Build the atlas of `receipts`, which were read from `index`; `regenerate` is the command line
/// that rebuilds it.
pub fn atlas(index: &AtlasIndex, receipts: &[LoadedReceipt], regenerate: &str) -> Atlas {
    let mut warnings = Vec::new();
    for receipt in receipts {
        if let Some(revision) = &receipt.join.receipt.krust_revision
            && !(revision.starts_with(&index.commit) || index.commit.starts_with(revision))
        {
            warnings.push(format!(
                "{} was recorded at krust {}, not at the index commit {}",
                receipt.entry.join,
                short(revision),
                short(&index.commit)
            ));
        }
    }
    let mut by_workload = BTreeMap::<&str, Vec<&LoadedReceipt>>::new();
    for receipt in receipts {
        by_workload
            .entry(receipt.entry.workload.as_str())
            .or_default()
            .push(receipt);
    }

    let mut workloads = Vec::new();
    let mut ladders = Vec::new();
    for (name, group) in &by_workload {
        let largest = group
            .iter()
            .filter_map(|receipt| receipt.entry.param)
            .max_by(f64::total_cmp);
        let measured = group
            .iter()
            .copied()
            .filter(|receipt| receipt.entry.param == largest)
            .collect::<Vec<_>>();
        workloads.push(workload_cost(name, &measured, &index.commit));
        if largest.is_some() {
            let graph = group.iter().find_map(|receipt| receipt.graph.as_ref());
            ladders.push(ladder(name, group, graph, &index.commit));
        }
    }

    let matrix_columns = workloads
        .iter()
        .map(|workload| workload.workload.clone())
        .collect::<Vec<_>>();
    let listed = workloads
        .iter()
        .flat_map(|workload| workload.rows.iter().map(|row| row.id.clone()))
        .collect::<BTreeSet<_>>();
    let mut matrix = listed
        .into_iter()
        .map(|id| {
            let shares = workloads
                .iter()
                .map(|workload| workload.shares.get(&id).copied().unwrap_or(0.0))
                .collect::<Vec<_>>();
            MatrixRow {
                commit: index.commit.clone(),
                max_share: shares.iter().copied().fold(0.0, f64::max),
                workloads_over_one_percent: shares.iter().filter(|share| **share > 0.01).count(),
                shares,
                id,
            }
        })
        .collect::<Vec<_>>();
    matrix.sort_by(|left, right| {
        right
            .workloads_over_one_percent
            .cmp(&left.workloads_over_one_percent)
            .then_with(|| right.max_share.total_cmp(&left.max_share))
            .then_with(|| left.id.cmp(&right.id))
    });

    Atlas {
        schema: ATLAS_SCHEMA_VERSION,
        commit: index.commit.clone(),
        regenerate: regenerate.to_owned(),
        rules: Rules::current(),
        warnings,
        workloads,
        matrix_columns,
        matrix,
        ladders,
    }
}

fn workload_cost(name: &str, receipts: &[&LoadedReceipt], commit: &str) -> WorkloadCost {
    let runs = receipts
        .iter()
        .map(|receipt| observe(&receipt.join))
        .collect::<Vec<_>>();
    let totals = runs.iter().map(span_seconds).collect::<Vec<_>>();
    let ids = runs
        .iter()
        .flat_map(|run| run.keys().cloned())
        .collect::<BTreeSet<_>>();
    let mut rows = ids
        .into_iter()
        .map(|id| {
            let column = |value: &dyn Fn(&Observed) -> f64| {
                runs.iter()
                    .map(|run| run.get(&id).map_or(0.0, value))
                    .collect::<Vec<_>>()
            };
            let shares = runs
                .iter()
                .zip(&totals)
                .map(|(run, total)| {
                    let own = run.get(&id).map_or(0.0, |observed| observed.self_seconds);
                    if *total > 0.0 { own / total } else { 0.0 }
                })
                .collect::<Vec<_>>();
            let share = Spread::of(&shares);
            let names = runs
                .iter()
                .filter_map(|run| run.get(&id))
                .flat_map(|observed| observed.own.iter())
                .map(|(name, (declared, _))| (name.clone(), *declared))
                .collect::<BTreeMap<_, _>>();
            let counters = names
                .into_iter()
                .map(|(name, declared)| MovedCounter {
                    span_self: Spread::of(&column(&|observed| {
                        observed.own.get(&name).map_or(0.0, |(_, value)| *value)
                    }))
                    .median,
                    name,
                    declared,
                })
                .filter(|counter| counter.span_self > 0.0)
                .collect();
            ShareRow {
                commit: commit.to_owned(),
                ceiling: amdahl_ceiling(share.median),
                share,
                self_seconds: Spread::of(&column(&|observed| observed.self_seconds)),
                span_count: Spread::of(&column(&|observed| observed.count)),
                counters,
                sampled_self: None,
                sampled_total: None,
                id,
            }
        })
        .collect::<Vec<_>>();
    rows.sort_by(|left, right| {
        right
            .share
            .median
            .total_cmp(&left.share.median)
            .then_with(|| left.id.cmp(&right.id))
    });
    let shares = rows
        .iter()
        .map(|row| (row.id.clone(), row.share.median))
        .collect::<BTreeMap<_, _>>();
    let mut covered = 0.0;
    let mut kept = Vec::new();
    let mut omitted_share = 0.0;
    let mut omitted_algorithms = 0;
    for row in rows {
        if covered < 0.9 || row.share.median > 0.01 {
            covered += row.share.median;
            kept.push(row);
        } else {
            omitted_share += row.share.median;
            omitted_algorithms += 1;
        }
    }
    let every = |value: fn(&IndexReceipt) -> Option<f64>| {
        receipts
            .iter()
            .map(|receipt| value(&receipt.entry))
            .collect::<Option<Vec<_>>>()
            .filter(|values| !values.is_empty())
            .map(|values| Spread::of(&values))
    };
    let wall_seconds = every(|entry| entry.wall_seconds);
    let span_seconds = Spread::of(&totals);
    let first = &receipts[0].entry;
    let profiled = receipts
        .iter()
        .find_map(|receipt| receipt.profile.as_ref().zip(receipt.entry.profile.as_ref()));
    let sampled = profiled.map(|(profile, path)| {
        let shares = profile
            .algorithms
            .iter()
            .map(|algorithm| {
                (
                    algorithm.id.as_str(),
                    (
                        profile.share(algorithm.self_samples),
                        profile.share(algorithm.total_samples),
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();
        for row in &mut kept {
            let (own, total) = shares.get(row.id.as_str()).copied().unwrap_or((0.0, 0.0));
            row.sampled_self = Some(own);
            row.sampled_total = Some(total);
        }
        let mut unlisted = shares
            .iter()
            .filter(|(id, (own, _))| *own >= 0.01 && !kept.iter().any(|row| row.id == **id))
            .map(|(id, (own, total))| SampledShare {
                id: (*id).to_owned(),
                self_share: *own,
                total_share: *total,
            })
            .collect::<Vec<_>>();
        unlisted.sort_by(|left, right| {
            right
                .self_share
                .total_cmp(&left.self_share)
                .then_with(|| left.id.cmp(&right.id))
        });
        SampledCost {
            profile: path.clone(),
            samples: profile.samples,
            rate_hz: profile
                .interval_ms
                .filter(|interval| *interval > 0.0)
                .map(|interval| 1000.0 / interval),
            owned_share: profile.share(profile.owned_samples),
            uncarded_leaf_share: profile.share(profile.uncarded_leaf_samples),
            outside_workspace_share: profile.share(profile.outside_workspace_samples),
            truncated_share: profile.share(profile.truncated_samples),
            truncated_unowned_share: profile.share(profile.truncated_unowned_samples),
            unlisted,
            uncarded: uncarded_rows(profile),
        }
    });
    WorkloadCost {
        workload: name.to_owned(),
        command: first.command.clone(),
        param_name: first.param_name.clone(),
        param: first.param,
        runs: receipts.len(),
        span_over_wall: wall_seconds
            .filter(|wall| wall.median > 0.0)
            .map(|wall| span_seconds.median / wall.median),
        wall_seconds,
        peak_rss_kib: every(|entry| entry.peak_rss_kib.map(|value| value as f64)),
        span_seconds,
        omitted_algorithms,
        omitted_share,
        rows: kept,
        nesting: nesting(receipts, &runs, &totals),
        sampled,
        shares,
    }
}

/// The share below which children and roots are folded into a `more` line.
const NESTING_FOLD: f64 = 0.005;

/// Build the observed nesting outline of one workload by [`NESTING_RULE`].
fn nesting(
    receipts: &[&LoadedReceipt],
    runs: &[BTreeMap<String, Observed>],
    totals: &[f64],
) -> Nesting {
    let share = |id: &str, value: fn(&Observed) -> f64| {
        Spread::of(
            &runs
                .iter()
                .zip(totals)
                .map(|(run, total)| {
                    let own = run.get(id).map_or(0.0, value);
                    if *total > 0.0 { own / total } else { 0.0 }
                })
                .collect::<Vec<_>>(),
        )
        .median
    };
    let positive = runs
        .iter()
        .flat_map(|run| run.keys().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter(|id| {
            Spread::of(
                &runs
                    .iter()
                    .map(|run| run.get(id).map_or(0.0, |observed| observed.count))
                    .collect::<Vec<_>>(),
            )
            .median
                > 0.0
        })
        .map(|id| {
            let observed = (
                share(&id, |observed| observed.total_seconds),
                share(&id, |observed| observed.self_seconds),
                Spread::of(
                    &runs
                        .iter()
                        .map(|run| run.get(&id).map_or(0.0, |observed| observed.count))
                        .collect::<Vec<_>>(),
                )
                .median as u64,
            );
            (id, observed)
        })
        .collect::<BTreeMap<_, _>>();
    let first = &receipts[0].join;
    let edges = |join: &Join| {
        let mut edges = join
            .observed_nests
            .iter()
            .map(|edge| (edge.from.clone(), edge.to.clone(), edge.count))
            .collect::<Vec<_>>();
        edges.sort();
        edges
    };
    let first_edges = edges(first);
    let repeats_agree = receipts[1..]
        .iter()
        .all(|receipt| edges(&receipt.join) == first_edges);

    let mut recursive = BTreeMap::<&str, u64>::new();
    let mut children = BTreeMap::<&str, Vec<(&str, u64)>>::new();
    let mut parents = BTreeMap::<&str, Vec<(&str, u64)>>::new();
    for (from, to, count) in &first_edges {
        if !positive.contains_key(from) || !positive.contains_key(to) {
            continue;
        }
        if from == to {
            recursive.insert(from, *count);
        } else {
            children.entry(from).or_default().push((to, *count));
            parents.entry(to).or_default().push((from, *count));
        }
    }
    let primary = parents
        .iter()
        .map(|(child, parents)| {
            let parent = parents
                .iter()
                .max_by(|left, right| left.1.cmp(&right.1).then_with(|| right.0.cmp(left.0)))
                .map(|(parent, _)| *parent);
            (*child, parent)
        })
        .collect::<BTreeMap<_, _>>();
    let by_total = |left: &(&str, u64), right: &(&str, u64)| {
        positive[right.0]
            .0
            .total_cmp(&positive[left.0].0)
            .then_with(|| left.0.cmp(right.0))
    };
    let mut roots = positive
        .keys()
        .map(String::as_str)
        .filter(|id| !parents.contains_key(id))
        .collect::<Vec<_>>();
    let mut reachable = BTreeSet::<&str>::new();
    let mut stack = roots.clone();
    while let Some(id) = stack.pop() {
        if reachable.insert(id) {
            stack.extend(
                children
                    .get(id)
                    .into_iter()
                    .flatten()
                    .map(|(child, _)| *child),
            );
        }
    }
    // An algorithm reachable only through a cycle has no root above it; each unreached cycle
    // contributes its first member by id, and the rest is reached from it.
    for id in positive.keys().map(String::as_str) {
        if !reachable.contains(id) {
            roots.push(id);
            let mut stack = vec![id];
            while let Some(id) = stack.pop() {
                if reachable.insert(id) {
                    stack.extend(
                        children
                            .get(id)
                            .into_iter()
                            .flatten()
                            .map(|(child, _)| *child),
                    );
                }
            }
        }
    }

    struct Outline<'a> {
        positive: &'a BTreeMap<String, (f64, f64, u64)>,
        children: &'a BTreeMap<&'a str, Vec<(&'a str, u64)>>,
        primary: &'a BTreeMap<&'a str, Option<&'a str>>,
        recursive: &'a BTreeMap<&'a str, u64>,
        lines: Vec<NestLine>,
    }
    impl<'a> Outline<'a> {
        fn line(&mut self, depth: usize, kind: &str, id: &str, count: u64, root: bool) {
            let (total_share, self_share, _) = self.positive[id];
            self.lines.push(NestLine {
                depth,
                kind: kind.to_owned(),
                id: id.to_owned(),
                count,
                root,
                total_share,
                self_share,
                recursive: (kind == "node")
                    .then(|| self.recursive.get(id).copied())
                    .flatten(),
            });
        }

        fn more(&mut self, depth: usize, folded: &[(&str, u64)]) {
            if folded.is_empty() {
                return;
            }
            self.lines.push(NestLine {
                depth,
                kind: "more".to_owned(),
                id: String::new(),
                count: folded.len() as u64,
                root: depth == 0,
                total_share: folded.iter().map(|(id, _)| self.positive[*id].0).sum(),
                self_share: 0.0,
                recursive: None,
            });
        }

        fn node(
            &mut self,
            id: &'a str,
            depth: usize,
            count: u64,
            root: bool,
            path: &mut Vec<&'a str>,
        ) {
            self.line(depth, "node", id, count, root);
            path.push(id);
            let mut kids = self.children.get(id).cloned().unwrap_or_default();
            kids.sort_by(|left, right| {
                self.positive[right.0]
                    .0
                    .total_cmp(&self.positive[left.0].0)
                    .then_with(|| left.0.cmp(right.0))
            });
            let (shown, folded): (Vec<_>, Vec<_>) = kids
                .into_iter()
                .partition(|(child, _)| self.positive[*child].0 >= NESTING_FOLD);
            for (child, nested) in shown {
                if path.contains(&child) {
                    self.line(depth + 1, "cycle", child, nested, false);
                } else if self.primary.get(child).copied().flatten() == Some(id) {
                    self.node(child, depth + 1, nested, false, path);
                } else {
                    self.line(depth + 1, "ref", child, nested, false);
                }
            }
            self.more(depth + 1, &folded);
            path.pop();
        }
    }

    let mut ordered = roots
        .into_iter()
        .map(|id| (id, positive[id].2))
        .collect::<Vec<_>>();
    ordered.sort_by(by_total);
    let (shown, folded): (Vec<_>, Vec<_>) = ordered
        .into_iter()
        .partition(|(id, _)| positive[*id].0 >= NESTING_FOLD);
    let mut outline = Outline {
        positive: &positive,
        children: &children,
        primary: &primary,
        recursive: &recursive,
        lines: Vec::new(),
    };
    for (root, spans) in shown {
        outline.node(root, 0, spans, true, &mut Vec::new());
    }
    outline.more(0, &folded);
    Nesting {
        edges_from: receipts[0].entry.join.clone(),
        repeats_agree,
        lines: outline.lines,
    }
}

fn ladder(name: &str, receipts: &[&LoadedReceipt], graph: Option<&Graph>, commit: &str) -> Ladder {
    let (sampled_params, sampled) = sampled_ladder(receipts);
    let (run_steps, [wall_seconds, peak_rss_kib, stdout_bytes], memory_marked) =
        run_growth(receipts);
    let mut by_param = BTreeMap::<u64, (f64, Vec<BTreeMap<String, Observed>>)>::new();
    for receipt in receipts {
        if let Some(param) = receipt.entry.param {
            by_param
                .entry(param.to_bits())
                .or_insert_with(|| (param, Vec::new()))
                .1
                .push(observe(&receipt.join));
        }
    }
    let mut steps = by_param.into_values().collect::<Vec<_>>();
    steps.sort_by(|left, right| left.0.total_cmp(&right.0));
    let median_at =
        |runs: &[BTreeMap<String, Observed>], id: &str, value: &dyn Fn(&Observed) -> f64| {
            Spread::of(
                &runs
                    .iter()
                    .map(|run| run.get(id).map_or(0.0, value))
                    .collect::<Vec<_>>(),
            )
            .median
        };
    let ids = steps
        .iter()
        .flat_map(|(_, runs)| runs.iter().flat_map(|run| run.keys().cloned()))
        .collect::<BTreeSet<_>>();
    let rows = ids
        .into_iter()
        .filter_map(|id| {
            let series = |value: &dyn Fn(&Observed) -> f64| {
                steps
                    .iter()
                    .map(|(param, runs)| (*param, median_at(runs, &id, value)))
                    .collect::<Vec<_>>()
            };
            let counts = series(&|observed| observed.count);
            let params_with_spans = counts.iter().filter(|(_, count)| *count > 0.0).count();
            if params_with_spans < 2 {
                return None;
            }
            let declared = steps
                .iter()
                .flat_map(|(_, runs)| runs.iter())
                .filter_map(|run| run.get(&id))
                .flat_map(|observed| observed.declared_total.keys().cloned())
                .collect::<BTreeSet<_>>();
            let node = graph.and_then(|graph| {
                graph
                    .nodes
                    .iter()
                    .find(|node| node.kind == "algorithm" && node.id == id)
            });
            let join_cost = || {
                receipts
                    .iter()
                    .flat_map(|receipt| receipt.join.algorithms.iter())
                    .find(|algorithm| algorithm.id == id)
                    .map(|algorithm| algorithm.cost.clone())
                    .unwrap_or_default()
            };
            Some(LadderRow {
                commit: commit.to_owned(),
                params_with_spans,
                span_count: fit_power_law(&counts),
                self_seconds: fit_power_law(&series(&|observed| observed.self_seconds)),
                counters: declared
                    .into_iter()
                    .map(|counter| CounterFit {
                        fit: fit_power_law(&series(&|observed| {
                            observed
                                .declared_total
                                .get(&counter)
                                .copied()
                                .unwrap_or(0.0)
                        })),
                        name: counter,
                    })
                    .collect(),
                cost: node.map_or_else(join_cost, |node| node.cost.clone()),
                variable: node.and_then(|node| node.variable.clone()),
                id,
            })
        })
        .collect();
    Ladder {
        workload: name.to_owned(),
        param_name: receipts
            .iter()
            .find_map(|receipt| receipt.entry.param_name.clone())
            .unwrap_or_else(|| "param".to_owned()),
        params: steps.iter().map(|(param, _)| *param).collect(),
        memory_marked,
        wall_seconds,
        peak_rss_kib,
        stdout_bytes,
        steps: run_steps,
        rows,
        sampled_params,
        sampled,
    }
}

impl Atlas {
    /// Every algorithm id that a table of the atlas lists.
    pub fn listed_ids(&self) -> BTreeSet<String> {
        self.workloads
            .iter()
            .flat_map(|workload| workload.rows.iter().map(|row| row.id.clone()))
            .chain(self.matrix.iter().map(|row| row.id.clone()))
            .chain(
                self.ladders
                    .iter()
                    .flat_map(|ladder| ladder.rows.iter().map(|row| row.id.clone())),
            )
            .collect()
    }

    /// Every uncarded function (`file::symbol`) that a sampled table of the atlas lists.
    pub fn listed_code(&self) -> BTreeSet<String> {
        self.workloads
            .iter()
            .filter_map(|workload| workload.sampled.as_ref())
            .flat_map(|sampled| sampled.uncarded.iter().map(|row| row.function.clone()))
            .chain(
                self.ladders
                    .iter()
                    .flat_map(|ladder| ladder.sampled.iter().map(|row| row.function.clone())),
            )
            .collect()
    }

    /// The atlas as TOML.
    pub fn toml(&self) -> Result<String, Error> {
        let mut output = toml::to_string_pretty(self)?;
        if !output.ends_with('\n') {
            output.push('\n');
        }
        Ok(output)
    }

    /// The atlas as compact Markdown for agents.
    pub fn markdown(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "# Cost atlas at {}", short(&self.commit));
        let _ = writeln!(out);
        let _ = writeln!(
            out,
            "Regenerate with `{}`; every row is measured at commit `{}`.",
            self.regenerate, self.commit
        );
        let _ = writeln!(out);
        for (label, rule) in [
            ("Share", &self.rules.share),
            ("Ceiling", &self.rules.amdahl),
            ("Cut", &self.rules.cut),
            ("Slope", &self.rules.slope),
            ("Run growth", &self.rules.run_growth),
            ("Staleness", &self.rules.staleness),
            ("Nesting", &self.rules.nesting),
            ("Sampled", &self.rules.sampled),
        ] {
            let _ = writeln!(out, "- {label}: {rule}.");
        }
        for warning in &self.warnings {
            let _ = writeln!(out, "- Warning: {warning}.");
        }
        let _ = writeln!(out);
        let _ = writeln!(out, "## Workloads");
        let _ = writeln!(out);
        let _ = writeln!(
            out,
            "| workload | command | param | runs | wall s | span s | span/wall | peak RSS MiB | listed | omitted (share %) |"
        );
        let _ = writeln!(out, "|---|---|---|--:|--:|--:|--:|--:|--:|--:|");
        for workload in &self.workloads {
            let _ = writeln!(
                out,
                "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} ({:.1}) |",
                workload.workload,
                workload.command,
                param_text(workload),
                workload.runs,
                workload
                    .wall_seconds
                    .map_or_else(|| "-".to_owned(), |wall| significant(wall.median)),
                significant(workload.span_seconds.median),
                workload
                    .span_over_wall
                    .map_or_else(|| "-".to_owned(), |ratio| format!("{ratio:.2}")),
                workload.peak_rss_kib.map_or_else(
                    || "-".to_owned(),
                    |rss| format!("{:.0}", rss.median / 1024.0)
                ),
                workload.rows.len(),
                workload.omitted_algorithms,
                100.0 * workload.omitted_share
            );
        }
        for workload in &self.workloads {
            let _ = writeln!(out);
            let _ = match workload.param {
                Some(_) => writeln!(out, "## {} {}", workload.workload, param_text(workload)),
                None => writeln!(out, "## {}", workload.workload),
            };
            let _ = writeln!(out);
            let sampled = workload.sampled.as_ref();
            let _ = writeln!(
                out,
                "| algorithm | share % |{} ceiling | self s | spans | counters moved in own code (? = not declared by its card) |",
                if sampled.is_some() {
                    " sampled self % | sampled total % |"
                } else {
                    ""
                }
            );
            let _ = writeln!(
                out,
                "|---|--:|{}--:|--:|--:|---|",
                if sampled.is_some() { "--:|--:|" } else { "" }
            );
            let percent = |share: Option<f64>| {
                share.map_or_else(String::new, |share| format!(" {:.1} |", 100.0 * share))
            };
            for row in &workload.rows {
                let _ = writeln!(
                    out,
                    "| {} | {:.1} |{}{} {} | {} | {} | {} |",
                    row.id,
                    100.0 * row.share.median,
                    percent(row.sampled_self),
                    percent(row.sampled_total),
                    row.ceiling
                        .map_or_else(|| "unbounded".to_owned(), |ceiling| format!("{ceiling:.2}")),
                    significant(row.self_seconds.median),
                    number(row.span_count.median),
                    if row.counters.is_empty() {
                        "-".to_owned()
                    } else {
                        row.counters
                            .iter()
                            .map(|counter| {
                                format!(
                                    "{}{}={}",
                                    counter.name,
                                    if counter.declared { "" } else { "?" },
                                    number(counter.span_self)
                                )
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    }
                );
            }
            if let Some(sampled) = sampled {
                for row in &sampled.unlisted {
                    let _ = writeln!(
                        out,
                        "| {} | - | {:.1} | {:.1} | - | - | - | not listed by traced share |",
                        row.id,
                        100.0 * row.self_share,
                        100.0 * row.total_share
                    );
                }
                let _ = writeln!(out);
                let _ = writeln!(
                    out,
                    "Sampled: {} samples{} of `{}`, untraced; owned by an algorithm {:.1} %, uncarded leaf {:.1} %, outside the workspace {:.1} %, truncated stacks {:.1} % ({:.1} % without an owned frame). Uncarded hot code:",
                    sampled.samples,
                    sampled
                        .rate_hz
                        .map(|rate| format!(" at {rate:.0} Hz"))
                        .unwrap_or_default(),
                    sampled.profile,
                    100.0 * sampled.owned_share,
                    100.0 * sampled.uncarded_leaf_share,
                    100.0 * sampled.outside_workspace_share,
                    100.0 * sampled.truncated_share,
                    100.0 * sampled.truncated_unowned_share
                );
                let _ = writeln!(out);
                let _ = writeln!(out, "| uncarded function | self % | inclusive % | under |");
                let _ = writeln!(out, "|---|--:|--:|---|");
                for row in &sampled.uncarded {
                    let _ = writeln!(
                        out,
                        "| {} | {:.1} | {:.1} | {} |",
                        cell(&row.function),
                        100.0 * row.self_share,
                        100.0 * row.inclusive_share,
                        cell(&row.under)
                    );
                }
            }
            let _ = writeln!(out);
            let _ = writeln!(
                out,
                "Observed nesting on this run only, not a declared relation (child span opened inside the parent's open span on one thread; algorithms without spans are absent). Edges of {}{}:",
                workload.nesting.edges_from,
                match (workload.runs, workload.nesting.repeats_agree) {
                    (1, _) => String::new(),
                    (runs, true) => format!(", the first of {runs} repeats, which agree"),
                    (runs, false) => format!(", the first of {runs} repeats, which differ"),
                }
            );
            let _ = writeln!(out);
            let _ = writeln!(out, "```text");
            for line in &workload.nesting.lines {
                let _ = writeln!(out, "{}{}", "  ".repeat(line.depth), nest_text(line));
            }
            let _ = writeln!(out, "```");
        }
        let _ = writeln!(out);
        let _ = writeln!(
            out,
            "## Share matrix (median share % of each workload's span time; . = no span)"
        );
        let _ = writeln!(out);
        let _ = writeln!(
            out,
            "| algorithm | max % | workloads >1 % | {} |",
            self.matrix_columns.join(" | ")
        );
        let _ = writeln!(
            out,
            "|---|--:|--:|{}",
            "--:|".repeat(self.matrix_columns.len())
        );
        for row in &self.matrix {
            let _ = writeln!(
                out,
                "| {} | {:.1} | {} | {} |",
                row.id,
                100.0 * row.max_share,
                row.workloads_over_one_percent,
                row.shares
                    .iter()
                    .map(|share| if *share > 0.0 {
                        format!("{:.1}", 100.0 * share)
                    } else {
                        ".".to_owned()
                    })
                    .collect::<Vec<_>>()
                    .join(" | ")
            );
        }
        for ladder in &self.ladders {
            let _ = writeln!(out);
            let _ = writeln!(
                out,
                "## Ladder {} ({} = {})",
                ladder.workload,
                ladder.param_name,
                ladder
                    .params
                    .iter()
                    .map(|param| number(*param))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            ladder_run_growth(&mut out, ladder);
            let (flat, mut growing): (Vec<&LadderRow>, Vec<&LadderRow>) =
                ladder.rows.iter().partition(|row| row.is_flat());
            growing.sort_by(|left, right| {
                slope_of(right.self_seconds.as_ref())
                    .total_cmp(&slope_of(left.self_seconds.as_ref()))
                    .then_with(|| left.id.cmp(&right.id))
            });
            let _ = writeln!(out);
            let _ = writeln!(
                out,
                "| algorithm | spans slope (points, R2) | self s slope | per-call slope | declared counter slopes | card bounds | variable |"
            );
            let _ = writeln!(out, "|---|---|---|--:|---|---|---|");
            for row in growing {
                let _ = writeln!(
                    out,
                    "| {} | {} | {} | {} | {} | {} | {} |",
                    row.id,
                    fit_text(row.span_count.as_ref()),
                    fit_text(row.self_seconds.as_ref()),
                    row.per_call_slope()
                        .map_or_else(|| "-".to_owned(), |slope| format!("{slope:.2}")),
                    if row.counters.is_empty() {
                        "-".to_owned()
                    } else {
                        row.counters
                            .iter()
                            .map(|counter| {
                                format!("{} {}", counter.name, fit_text(counter.fit.as_ref()))
                            })
                            .collect::<Vec<_>>()
                            .join("; ")
                    },
                    cell(
                        &row.cost
                            .iter()
                            .map(|cost| format!("{}: {}", cost.mode, cost.bound))
                            .collect::<Vec<_>>()
                            .join("; ")
                    ),
                    cell(row.variable.as_deref().unwrap_or("-")),
                );
            }
            if !flat.is_empty() {
                let _ = writeln!(out);
                let _ = writeln!(
                    out,
                    "Flat ({} algorithms, every slope below {FLAT_SLOPE} in magnitude): {}",
                    flat.len(),
                    flat.iter()
                        .map(|row| row.id.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
            if !ladder.sampled.is_empty() {
                let _ = writeln!(out);
                let _ = writeln!(
                    out,
                    "Sampled uncarded code, inclusive % by {}:",
                    ladder.param_name
                );
                let _ = writeln!(out);
                let _ = writeln!(
                    out,
                    "| uncarded function | {} |",
                    ladder
                        .sampled_params
                        .iter()
                        .map(|param| number(*param))
                        .collect::<Vec<_>>()
                        .join(" | ")
                );
                let _ = writeln!(out, "|---|{}", "--:|".repeat(ladder.sampled_params.len()));
                for row in &ladder.sampled {
                    let _ = writeln!(
                        out,
                        "| {} | {} |",
                        cell(&row.function),
                        row.inclusive_shares
                            .iter()
                            .map(|share| format!("{:.1}", 100.0 * share))
                            .collect::<Vec<_>>()
                            .join(" | ")
                    );
                }
            }
        }
        out
    }
}

/// The whole-run table of a ladder, its fits, and the memory mark by [`RUN_GROWTH_RULE`].
fn ladder_run_growth(out: &mut String, ladder: &Ladder) {
    let optional = |value: Option<f64>, text: &dyn Fn(f64) -> String| {
        value.map_or_else(|| "-".to_owned(), text)
    };
    let _ = writeln!(out);
    let _ = writeln!(
        out,
        "Whole run (the untraced measured run of each receipt; medians over repeats):"
    );
    let _ = writeln!(out);
    let _ = writeln!(
        out,
        "| {} | runs | wall s | peak RSS MiB | stdout MB |",
        ladder.param_name
    );
    let _ = writeln!(out, "|--:|--:|--:|--:|--:|");
    for step in &ladder.steps {
        let _ = writeln!(
            out,
            "| {} | {} | {} | {} | {} |",
            number(step.param),
            step.runs,
            optional(step.wall_seconds, &significant),
            optional(step.peak_rss_kib, &|kib| format!("{:.0}", kib / 1024.0)),
            optional(step.stdout_bytes, &|bytes| significant(bytes / 1e6)),
        );
    }
    let _ = writeln!(
        out,
        "| slope (points, R2) | | {} | {} | {} |",
        fit_text(ladder.wall_seconds.fit.as_ref()),
        fit_text(ladder.peak_rss_kib.fit.as_ref()),
        fit_text(ladder.stdout_bytes.fit.as_ref())
    );
    let top = |fit: &RunFit| match (fit.top_slope, fit.top_params.as_slice()) {
        (Some(slope), [from, to]) => format!("{slope:.2} ({}..{})", number(*from), number(*to)),
        _ => "-".to_owned(),
    };
    let _ = writeln!(
        out,
        "| top slope (between) | | {} | {} | {} |",
        top(&ladder.wall_seconds),
        top(&ladder.peak_rss_kib),
        top(&ladder.stdout_bytes)
    );
    if ladder.memory_marked {
        // A fit and a top slope exist together: both need two positive parameter values.
        let exponent = |fit: &RunFit| match (fit.fit, fit.top_slope) {
            (Some(all), Some(top)) => format!(
                "{name}^{:.2} (fit), {name}^{top:.2} (top)",
                all.slope,
                name = ladder.param_name
            ),
            _ => "not fitted".to_owned(),
        };
        let _ = writeln!(out);
        let _ = writeln!(
            out,
            "**Marked: peak RSS grows as {}, above {}^{MEMORY_MARK_SLOPE}; stdout grows as {}.**",
            exponent(&ladder.peak_rss_kib),
            ladder.param_name,
            exponent(&ladder.stdout_bytes)
        );
    }
}

fn nest_text(line: &NestLine) -> String {
    let percent = |share: f64| format!("{:.1} %", 100.0 * share);
    match line.kind.as_str() {
        "more" => format!("+{} more ({})", line.count, percent(line.total_share)),
        "ref" => format!("= {} (nested {}\u{d7})", line.id, line.count),
        "cycle" => format!("^ {} (cycle, nested {}\u{d7})", line.id, line.count),
        _ => format!(
            "{} \u{2014} {} {}\u{d7} \u{2014} total {} \u{2014} self {}{}",
            line.id,
            if line.root { "spans" } else { "nested" },
            line.count,
            percent(line.total_share),
            percent(line.self_share),
            line.recursive
                .map(|count| format!(" (recursive, {count}\u{d7})"))
                .unwrap_or_default()
        ),
    }
}

fn param_text(workload: &WorkloadCost) -> String {
    match (&workload.param_name, workload.param) {
        (Some(name), Some(param)) => format!("{name}={}", number(param)),
        (None, Some(param)) => number(param),
        _ => "-".to_owned(),
    }
}

/// Four significant digits, without exponent.
fn significant(value: f64) -> String {
    if value == 0.0 || !value.is_finite() {
        return format!("{value}");
    }
    let decimals = (3 - value.abs().log10().floor() as i32).clamp(0, 9) as usize;
    format!("{value:.decimals$}")
}

fn fit_text(fit: Option<&Fit>) -> String {
    match fit {
        None => "-".to_owned(),
        Some(fit) => format!(
            "{:.2} ({}{}, {})",
            fit.slope,
            fit.points,
            if fit.fewer_than_three { "*" } else { "" },
            fit.r_squared
                .map_or_else(|| "-".to_owned(), |r_squared| format!("{r_squared:.3}"))
        ),
    }
}

fn cell(text: &str) -> String {
    text.replace('|', "\\|").replace('\n', " ")
}

/// Algorithms whose site files changed since the index commit.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct Staleness {
    pub commit: String,
    pub rule: String,
    /// Listed algorithms found in the graph and checked.
    pub checked: usize,
    #[serde(rename = "stale")]
    pub stale: Vec<StaleAlgorithm>,
    /// Listed algorithms without a node in the graph at the receipt commit; not checked.
    pub not_in_graph: Vec<String>,
}

/// One stale algorithm and its changed files.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct StaleAlgorithm {
    pub id: String,
    pub files: Vec<String>,
}

/// Check `ids` and the uncarded functions `code` (`file::symbol`) against the working tree at
/// `root` by [`STALENESS_RULE`], taking site files from `graph`, the graph at `commit`.
pub fn check_staleness(
    root: &Path,
    commit: &str,
    graph: &Graph,
    ids: &BTreeSet<String>,
    code: &BTreeSet<String>,
) -> Result<Staleness, Error> {
    let mut files_of = BTreeMap::<&str, BTreeSet<&str>>::new();
    for function in code {
        let file = function
            .split_once("::")
            .map_or(function.as_str(), |(file, _)| file);
        files_of.insert(function, BTreeSet::from([file]));
    }
    let mut not_in_graph = Vec::new();
    for id in ids {
        match graph
            .nodes
            .iter()
            .find(|node| node.kind == "algorithm" && &node.id == id)
        {
            Some(node) => {
                files_of.insert(
                    id,
                    std::iter::once(node.anchor.file.as_str())
                        .chain(node.sites.iter().map(|site| site.file.as_str()))
                        .collect(),
                );
            }
            None => not_in_graph.push(id.clone()),
        }
    }
    let files = files_of
        .values()
        .flatten()
        .copied()
        .collect::<BTreeSet<_>>();
    let changed = if files.is_empty() {
        BTreeSet::new()
    } else {
        let output = Command::new("git")
            .arg("-C")
            .arg(root)
            .args(["diff", "--name-only", commit, "--"])
            .args(&files)
            .output()?;
        if !output.status.success() {
            return Err(Error::Invalid(format!(
                "git diff --name-only {commit} in {} failed: {}",
                root.display(),
                String::from_utf8_lossy(&output.stderr).trim()
            )));
        }
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .map(ToOwned::to_owned)
            .collect::<BTreeSet<_>>()
    };
    let stale = files_of
        .iter()
        .filter_map(|(id, files)| {
            let touched = files
                .iter()
                .filter(|file| changed.contains(**file))
                .map(|file| (*file).to_owned())
                .collect::<Vec<_>>();
            (!touched.is_empty()).then(|| StaleAlgorithm {
                id: (*id).to_owned(),
                files: touched,
            })
        })
        .collect();
    Ok(Staleness {
        commit: commit.to_owned(),
        rule: STALENESS_RULE.to_owned(),
        checked: files_of.len(),
        stale,
        not_in_graph,
    })
}

impl Staleness {
    /// One line per stale algorithm after a summary line.
    pub fn text(&self) -> String {
        let mut out = format!(
            "atlas check at {}: {} of {} listed algorithms and uncarded functions stale. Rule: {}.\n",
            short(&self.commit),
            self.stale.len(),
            self.checked,
            self.rule
        );
        for stale in &self.stale {
            let _ = writeln!(out, "stale {}: {}", stale.id, stale.files.join(", "));
        }
        if !self.not_in_graph.is_empty() {
            let _ = writeln!(
                out,
                "not in the graph at the receipt commit, so not checked: {}",
                self.not_in_graph.join(", ")
            );
        }
        out
    }
}

/// The graph at the receipt commit: the first `graph.toml` beside a join of the index.
pub fn receipt_graph<'a>(
    index_path: &Path,
    receipts: &'a [LoadedReceipt],
) -> Result<&'a Graph, Error> {
    receipts
        .iter()
        .find_map(|receipt| receipt.graph.as_ref())
        .ok_or_else(|| {
            Error::Invalid(format!(
                "{}: no join of the index has a graph.toml beside it, and the site files must come from the graph at the receipt commit",
                index_path.display()
            ))
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Anchor, Node,
        diff::tests::{join, run},
    };

    fn receipt(
        workload: &str,
        param: Option<f64>,
        repeat: u32,
        join: Join,
        wall: f64,
    ) -> LoadedReceipt {
        LoadedReceipt {
            entry: IndexReceipt {
                workload: workload.to_owned(),
                command: "krun".to_owned(),
                param_name: param.map(|_| "n".to_owned()),
                param,
                repeat,
                join: format!("{workload}/rep-{repeat}/join.toml"),
                wall_seconds: Some(wall),
                peak_rss_kib: Some(2048),
                stdout_bytes: None,
                profile: None,
            },
            join_path: PathBuf::from("join.toml"),
            join,
            graph: None,
            profile: None,
        }
    }

    /// A profile of `samples` samples: `alg` owns `owned` of them, and `walk` is an uncarded
    /// function with `walk` inclusive samples under it, `walk / 2` as the leaf.
    fn sampled(samples: u64, owned: u64, walk: u64) -> SampledProfile {
        use crate::profile::{SampledAlgorithm, UncardedFunction, Under};
        let row = |samples: u64| UncardedFunction {
            function: "crates/x/src/w.rs::walk".to_owned(),
            samples,
            under: vec![Under {
                id: "b".to_owned(),
                samples,
            }],
        };
        SampledProfile {
            schema: crate::profile::PROFILE_SCHEMA_VERSION,
            rule: String::new(),
            stacks: None,
            interval_ms: Some(1.0),
            samples,
            truncated_samples: 0,
            owned_samples: owned,
            uncarded_leaf_samples: walk / 2,
            outside_workspace_samples: samples - owned,
            tied_samples: 0,
            truncated_unowned_samples: 0,
            algorithms: vec![
                SampledAlgorithm {
                    id: "b".to_owned(),
                    self_samples: owned,
                    total_samples: owned,
                },
                SampledAlgorithm {
                    id: "unspanned".to_owned(),
                    self_samples: samples / 10,
                    total_samples: samples / 10,
                },
            ],
            leaves: vec![row(walk / 2)],
            inclusive: vec![row(walk)],
        }
    }

    #[test]
    fn a_profile_adds_sampled_shares_and_uncarded_code() {
        let at = |count, seconds| {
            join(
                "w",
                "c0ffee",
                vec![run("b", count, seconds, seconds, &[])],
                &[],
            )
        };
        let mut small = receipt("w", Some(10.0), 1, at(10, 1.0), 1.0);
        let mut large = receipt("w", Some(100.0), 1, at(100, 4.0), 4.0);
        small.entry.profile = Some("w/10/rep-1/profile.toml".to_owned());
        small.profile = Some(sampled(1000, 800, 100));
        large.entry.profile = Some("w/100/rep-1/profile.toml".to_owned());
        large.profile = Some(sampled(1000, 900, 400));
        let receipts = [small, large];
        let atlas = atlas(&index(&receipts), &receipts, "algo-graph atlas");
        let workload = &atlas.workloads[0];
        assert_eq!(workload.rows[0].sampled_self, Some(0.9));
        let sampled = workload.sampled.as_ref().expect("sampled");
        assert_eq!(sampled.profile, "w/100/rep-1/profile.toml");
        assert_eq!(
            sampled
                .unlisted
                .iter()
                .map(|row| row.id.as_str())
                .collect::<Vec<_>>(),
            ["unspanned"]
        );
        assert_eq!(
            sampled.uncarded,
            [UncardedRow {
                function: "crates/x/src/w.rs::walk".to_owned(),
                self_share: 0.2,
                inclusive_share: 0.4,
                under: "b".to_owned(),
            }]
        );
        let ladder = &atlas.ladders[0];
        assert_eq!(ladder.sampled_params, [10.0, 100.0]);
        assert_eq!(ladder.sampled[0].inclusive_shares, [0.1, 0.4]);
        assert_eq!(
            atlas.listed_code(),
            BTreeSet::from(["crates/x/src/w.rs::walk".to_owned()])
        );
        let markdown = atlas.markdown();
        assert!(
            markdown.contains("| b | 100.0 | 90.0 | 90.0 |"),
            "{markdown}"
        );
        assert!(
            markdown.contains("| unspanned | - | 10.0 | 10.0 |"),
            "{markdown}"
        );
        assert!(
            markdown.contains("| crates/x/src/w.rs::walk | 20.0 | 40.0 | b |"),
            "{markdown}"
        );
        assert!(
            markdown.contains("| crates/x/src/w.rs::walk | 10.0 | 40.0 |"),
            "{markdown}"
        );
    }

    fn index(receipts: &[LoadedReceipt]) -> AtlasIndex {
        AtlasIndex {
            schema: INDEX_SCHEMA_VERSION,
            commit: "c0ffee".to_owned(),
            receipts: receipts
                .iter()
                .map(|receipt| receipt.entry.clone())
                .collect(),
        }
    }

    #[test]
    fn ceiling_is_one_over_the_remaining_share() {
        assert_eq!(amdahl_ceiling(0.0), Some(1.0));
        assert_eq!(amdahl_ceiling(0.5), Some(2.0));
        assert_eq!(amdahl_ceiling(0.75), Some(4.0));
        assert_eq!(amdahl_ceiling(1.0), None);
    }

    #[test]
    fn exact_power_laws_recover_their_exponents() {
        let linear = [(10.0, 30.0), (100.0, 300.0), (1000.0, 3000.0)];
        let fit = fit_power_law(&linear).expect("fit");
        assert!((fit.slope - 1.0).abs() < 1e-12, "{fit:?}");
        assert!((fit.r_squared.expect("r2") - 1.0).abs() < 1e-12);
        assert_eq!((fit.points, fit.fewer_than_three), (3, false));

        let quadratic = [(2.0, 20.0), (4.0, 80.0), (8.0, 320.0), (16.0, 1280.0)];
        let fit = fit_power_law(&quadratic).expect("fit");
        assert!((fit.slope - 2.0).abs() < 1e-12, "{fit:?}");
        assert_eq!(fit.points, 4);

        let two = [(10.0, 5.0), (100.0, 500.0), (1000.0, 0.0)];
        let fit = fit_power_law(&two).expect("fit");
        assert!((fit.slope - 2.0).abs() < 1e-12);
        assert_eq!((fit.points, fit.fewer_than_three), (2, true));

        assert_eq!(fit_power_law(&[(10.0, 5.0)]), None);
        assert_eq!(fit_power_law(&[(10.0, 5.0), (10.0, 6.0)]), None);
        let flat = fit_power_law(&[(1.0, 7.0), (2.0, 7.0), (4.0, 7.0)]).expect("fit");
        assert_eq!((flat.slope, flat.r_squared), (0.0, None));
    }

    #[test]
    fn workloads_list_shares_with_ceilings_up_to_the_cut() {
        // Span time 10 s: shares 60 %, 25 %, 8 %, 5 %, 1.5 %, 0.5 %.
        let rows = |scale: f64| {
            vec![
                run("a.big", 3, 6.0 * scale, 6.0, &[("a.pairs", 30, 12)]),
                run("a.mid", 5, 2.5 * scale, 2.5, &[]),
                run("a.small", 7, 0.8 * scale, 0.8, &[]),
                run("a.tail", 1, 0.5 * scale, 0.5, &[]),
                run("a.over", 1, 0.15 * scale, 0.15, &[]),
                run("a.under", 1, 0.05 * scale, 0.05, &[]),
                run("a.idle", 0, 0.0, 0.0, &[]),
            ]
        };
        let receipts = vec![
            receipt("w", None, 1, join("w", "c0ffee", rows(1.0), &[]), 20.0),
            receipt("w", None, 2, join("w", "c0ffee", rows(1.0), &[]), 22.0),
            receipt(
                "v",
                None,
                1,
                join("v", "c0ffee", vec![run("a.mid", 1, 1.0, 1.0, &[])], &[]),
                1.0,
            ),
        ];
        let atlas = atlas(
            &index(&receipts),
            &receipts,
            "algo-graph atlas --index atlas.toml",
        );
        assert!(atlas.warnings.is_empty(), "{:?}", atlas.warnings);
        let w = atlas
            .workloads
            .iter()
            .find(|workload| workload.workload == "w")
            .expect("w");
        assert_eq!(w.runs, 2);
        assert!((w.span_seconds.median - 10.0).abs() < 1e-9);
        assert_eq!(w.wall_seconds.map(|wall| wall.median), Some(21.0));
        let ids = w.rows.iter().map(|row| row.id.as_str()).collect::<Vec<_>>();
        assert_eq!(
            ids,
            ["a.big", "a.mid", "a.small", "a.tail", "a.over"],
            "90 % is reached with a.small, then every share above 1 %"
        );
        assert_eq!(w.omitted_algorithms, 1);
        assert!((w.omitted_share - 0.005).abs() < 1e-12);
        let big = &w.rows[0];
        assert!((big.share.median - 0.6).abs() < 1e-12);
        assert!((big.ceiling.expect("bounded") - 2.5).abs() < 1e-9);
        assert_eq!(big.counters[0].name, "a.pairs");
        assert_eq!(big.counters[0].span_self, 12.0);
        assert_eq!(big.commit, "c0ffee");

        assert_eq!(atlas.matrix_columns, ["v", "w"]);
        let mid = atlas
            .matrix
            .iter()
            .find(|row| row.id == "a.mid")
            .expect("row");
        assert_eq!(mid.workloads_over_one_percent, 2);
        assert_eq!(
            atlas.matrix[0].id, "a.mid",
            "present everywhere sorts first"
        );
        assert!((mid.shares[0] - 1.0).abs() < 1e-12);

        let markdown = atlas.markdown();
        assert!(markdown.contains("| a.big | 60.0 | 2.50 |"), "{markdown}");
        assert!(
            markdown.contains("| a.mid | 100.0 | unbounded |"),
            "{markdown}"
        );
        atlas.toml().expect("toml");
    }

    #[test]
    fn nesting_outlines_roots_recursion_shared_children_cycles_and_folds() {
        // Span time 10 s (the sum of self seconds).
        let rows = vec![
            run("n.root", 1, 1.0, 10.0, &[]),
            run("n.a", 5, 2.0, 6.0, &[]),
            run("n.b", 3, 2.47, 3.0, &[]),
            run("n.c", 14, 4.0, 4.0, &[]),
            run("n.d", 1, 0.03, 0.03, &[]),
            run("n.e", 1, 0.0, 0.0, &[]),
            run("n.f", 1, 0.3, 0.5, &[]),
            run("n.g", 1, 0.2, 0.2, &[]),
            run("n.idle", 0, 0.0, 0.0, &[]),
        ];
        let mut joined = join("w", "c0ffee", rows, &[]);
        joined.observed_nests = [
            ("n.root", "n.a", 5),
            ("n.root", "n.b", 3),
            ("n.a", "n.a", 2),
            ("n.a", "n.c", 10),
            ("n.b", "n.c", 4),
            ("n.b", "n.d", 1),
            ("n.f", "n.g", 1),
            ("n.g", "n.f", 1),
            ("n.root", "n.idle", 1),
        ]
        .into_iter()
        .map(|(from, to, count)| crate::ObservedEdge {
            from: from.to_owned(),
            to: to.to_owned(),
            count,
        })
        .collect();
        let mut second = joined.clone();
        second.observed_nests.pop();
        let receipts = vec![
            receipt("w", None, 1, joined.clone(), 12.0),
            receipt("w", None, 2, joined, 12.0),
        ];
        let atlas = atlas(&index(&receipts), &receipts, "regenerate");
        let nesting = &atlas.workloads[0].nesting;
        assert!(nesting.repeats_agree);
        let shape = nesting
            .lines
            .iter()
            .map(|line| (line.depth, line.kind.as_str(), line.id.as_str(), line.count))
            .collect::<Vec<_>>();
        assert_eq!(
            shape,
            [
                (0, "node", "n.root", 1),
                (1, "node", "n.a", 5),
                (2, "node", "n.c", 10),
                (1, "node", "n.b", 3),
                (2, "ref", "n.c", 4),
                (2, "more", "", 1),
                (0, "node", "n.f", 1),
                (1, "node", "n.g", 1),
                (2, "cycle", "n.f", 1),
                (0, "more", "", 1),
            ]
        );
        assert_eq!(nesting.lines[1].recursive, Some(2));
        assert!((nesting.lines[1].total_share - 0.6).abs() < 1e-12);
        assert!((nesting.lines[5].total_share - 0.003).abs() < 1e-12);
        let markdown = atlas.markdown();
        assert!(
            markdown.contains("  n.a \u{2014} nested 5\u{d7} \u{2014} total 60.0 % \u{2014} self 20.0 % (recursive, 2\u{d7})"),
            "{markdown}"
        );
        assert!(
            markdown.contains("    = n.c (nested 4\u{d7})"),
            "{markdown}"
        );
        assert!(markdown.contains("    +1 more (0.3 %)"), "{markdown}");
        assert!(
            markdown.contains("the first of 2 repeats, which agree"),
            "{markdown}"
        );
        assert!(
            atlas
                .toml()
                .expect("toml")
                .contains("[[workload.nesting.line]]")
        );

        let differing = vec![
            receipt("w", None, 1, second.clone(), 1.0),
            receipt(
                "w",
                None,
                2,
                {
                    let mut other = second;
                    other.observed_nests.clear();
                    other
                },
                1.0,
            ),
        ];
        let atlas = super::atlas(&index(&differing), &differing, "regenerate");
        assert!(!atlas.workloads[0].nesting.repeats_agree);
    }

    #[test]
    fn ladders_fit_each_algorithm_and_mark_short_fits() {
        let at = |n: f64, repeat: u32| {
            let rows = vec![
                run(
                    "a.linear",
                    n as u64,
                    n / 1000.0,
                    n / 1000.0,
                    &[("a.steps", 3 * n as u64, 0)],
                ),
                run(
                    "a.square",
                    (n * n) as u64,
                    n * n / 1000.0,
                    n * n / 1000.0,
                    &[],
                ),
                run(
                    "a.late",
                    if n >= 100.0 { n as u64 } else { 0 },
                    n / 1000.0,
                    n / 1000.0,
                    &[],
                ),
                run("a.once", u64::from(n == 1000.0), 0.001, 0.001, &[]),
            ];
            receipt("sum", Some(n), repeat, join("sum", "c0ffee", rows, &[]), n)
        };
        let receipts = vec![at(10.0, 1), at(100.0, 1), at(1000.0, 1), at(1000.0, 2)];
        let atlas = atlas(&index(&receipts), &receipts, "regenerate");
        let workload = &atlas.workloads[0];
        assert_eq!((workload.param, workload.runs), (Some(1000.0), 2));
        let ladder = &atlas.ladders[0];
        assert_eq!(ladder.params, [10.0, 100.0, 1000.0]);
        let row = |id: &str| ladder.rows.iter().find(|row| row.id == id);
        let linear = row("a.linear").expect("linear");
        assert!((linear.span_count.expect("fit").slope - 1.0).abs() < 1e-9);
        assert!((linear.counters[0].fit.expect("fit").slope - 1.0).abs() < 1e-9);
        let square = row("a.square").expect("square");
        assert!((square.span_count.expect("fit").slope - 2.0).abs() < 1e-9);
        assert!((square.self_seconds.expect("fit").slope - 2.0).abs() < 1e-9);
        let late = row("a.late").expect("late");
        assert_eq!(late.params_with_spans, 2);
        assert!(late.span_count.expect("fit").fewer_than_three);
        assert!(
            row("a.once").is_none(),
            "one parameter value is not a ladder row"
        );
        assert!(atlas.markdown().contains("(2*, "));
    }

    #[test]
    fn ladder_markdown_folds_flat_rows_and_prints_per_call_growth() {
        let at = |n: f64| {
            let rows = vec![
                run("a.flat", 5, 0.01, 0.01, &[]),
                run("a.linear", n as u64, n / 1000.0, n / 1000.0, &[]),
                // one call per step whose own time grows with n: per-call slope 1
                run("a.per_call", n as u64, n * n / 1e6, n * n / 1e6, &[]),
            ];
            receipt("sum", Some(n), 1, join("sum", "c0ffee", rows, &[]), n)
        };
        let receipts = vec![at(10.0), at(100.0), at(1000.0)];
        let atlas = atlas(&index(&receipts), &receipts, "regenerate");
        let ladder = &atlas.ladders[0];
        let row = |id: &str| ladder.rows.iter().find(|row| row.id == id).expect(id);
        assert!(row("a.flat").is_flat());
        assert!(!row("a.linear").is_flat());
        assert!((row("a.linear").per_call_slope().expect("slope")).abs() < 1e-9);
        assert!((row("a.per_call").per_call_slope().expect("slope") - 1.0).abs() < 1e-9);
        let markdown = atlas.markdown();
        let markdown = &markdown[markdown.find("## Ladder").expect("ladder section")..];
        assert!(
            markdown.contains("Flat (1 algorithms, every slope below 0.2 in magnitude): a.flat")
        );
        assert!(!markdown.contains("| a.flat |"));
        let per_call = markdown.find("| a.per_call |").expect("per-call row");
        let linear = markdown.find("| a.linear |").expect("linear row");
        assert!(per_call < linear, "rows sort by self-seconds slope");
    }

    #[test]
    fn ladders_fit_whole_run_growth_and_mark_superlinear_memory() {
        let at = |workload: &str, n: f64, repeat: u32, rss: Option<f64>, stdout: Option<f64>| {
            let rows = vec![run("a.linear", n as u64, n / 1000.0, n / 1000.0, &[])];
            let mut receipt = receipt(
                workload,
                Some(n),
                repeat,
                join(workload, "c0ffee", rows, &[]),
                n / 100.0,
            );
            receipt.entry.peak_rss_kib = rss.map(|kib| kib as u64);
            receipt.entry.stdout_bytes = stdout.map(|bytes| bytes as u64);
            receipt
        };
        // "grow": peak RSS 4 n^2 KiB and stdout n^3 bytes; the second repeat at n = 100 has no
        // RSS, so that step's median is the first repeat's alone. "flat": RSS linear, no stdout.
        // "baseline": a fixed 100000 KiB plus n^2.5 KiB, which holds the least-squares slope
        // over n = 10..300 near 0.79 while the top slope (100..300) is about 1.93.
        let baseline = |n: f64| Some(100_000.0 + n.powf(2.5));
        let receipts = vec![
            at("grow", 10.0, 1, Some(400.0), Some(1e3)),
            at("grow", 100.0, 1, Some(40_000.0), Some(1e6)),
            at("grow", 100.0, 2, None, Some(1e6)),
            at("grow", 1000.0, 1, Some(4_000_000.0), Some(1e9)),
            at("flat", 10.0, 1, Some(10_240.0), None),
            at("flat", 100.0, 1, Some(102_400.0), None),
            at("flat", 1000.0, 1, Some(1_024_000.0), None),
            at("baseline", 10.0, 1, baseline(10.0), Some(1.0)),
            at("baseline", 30.0, 1, baseline(30.0), Some(1.0)),
            at("baseline", 100.0, 1, baseline(100.0), Some(1.0)),
            at("baseline", 300.0, 1, baseline(300.0), Some(1.0)),
        ];
        let atlas = atlas(&index(&receipts), &receipts, "regenerate");
        let ladder = |name: &str| {
            atlas
                .ladders
                .iter()
                .find(|ladder| ladder.workload == name)
                .expect(name)
        };
        let grow = ladder("grow");
        assert_eq!(grow.steps[1].runs, 2);
        assert_eq!(grow.steps[1].peak_rss_kib, Some(40_000.0));
        let slope = |fit: &RunFit| fit.fit.expect("fit").slope;
        let top = |fit: &RunFit| fit.top_slope.expect("top slope");
        assert!((slope(&grow.wall_seconds) - 1.0).abs() < 1e-9);
        assert!((slope(&grow.peak_rss_kib) - 2.0).abs() < 1e-9);
        assert!((top(&grow.peak_rss_kib) - 2.0).abs() < 1e-9);
        assert_eq!(grow.peak_rss_kib.top_params, [100.0, 1000.0]);
        assert!((slope(&grow.stdout_bytes) - 3.0).abs() < 1e-9);
        assert_eq!(grow.peak_rss_kib.fit.expect("fit").points, 3);
        assert!(grow.memory_marked);

        let flat = ladder("flat");
        assert!((slope(&flat.peak_rss_kib) - 1.0).abs() < 1e-9);
        assert_eq!(flat.stdout_bytes.fit, None);
        assert_eq!(flat.stdout_bytes.top_slope, None);
        assert!(!flat.memory_marked, "linear memory is not marked");

        let baseline = ladder("baseline");
        assert!(slope(&baseline.peak_rss_kib) < 0.8, "{baseline:?}");
        assert!(top(&baseline.peak_rss_kib) > 1.9, "{baseline:?}");
        assert!(baseline.memory_marked, "the top slope marks it");
        assert_eq!(slope(&baseline.stdout_bytes), 0.0);

        // A slope at the threshold (truncated to whole KiB, so just below it) is not marked, and
        // a ladder without peak RSS has no fit to mark.
        let two = vec![
            at("edge", 10.0, 1, Some(100.0), None),
            at(
                "edge",
                100.0,
                1,
                Some(100.0 * 10f64.powf(MEMORY_MARK_SLOPE)),
                None,
            ),
            at("none", 10.0, 1, None, None),
            at("none", 100.0, 1, None, None),
        ];
        let edges = super::atlas(&index(&two), &two, "regenerate");
        assert!(edges.ladders.iter().all(|ladder| !ladder.memory_marked));
        assert!(
            edges.ladders[0]
                .peak_rss_kib
                .fit
                .expect("fit")
                .fewer_than_three
        );
        assert_eq!(edges.ladders[1].peak_rss_kib.fit, None);

        assert!(RUN_GROWTH_RULE.contains(&format!("exceeds {MEMORY_MARK_SLOPE}")));
        let markdown = atlas.markdown();
        assert!(
            markdown.contains("- Run growth: for each ladder"),
            "{markdown}"
        );
        let section = |name: &str| {
            let start = markdown
                .find(&format!("## Ladder {name} "))
                .expect("ladder section");
            let rest = &markdown[start + 1..];
            &markdown[start..start + 1 + rest.find("\n## ").unwrap_or(rest.len())]
        };
        let grow = section("grow");
        assert!(
            grow.contains("| 1000 | 1 | 10.00 | 3906 | 1000 |"),
            "{grow}"
        );
        assert!(
            grow.contains(
                "| slope (points, R2) | | 1.00 (3, 1.000) | 2.00 (3, 1.000) | 3.00 (3, 1.000) |"
            ),
            "{grow}"
        );
        assert!(
            grow.contains(
                "| top slope (between) | | 1.00 (100..1000) | 2.00 (100..1000) | 3.00 (100..1000) |"
            ),
            "{grow}"
        );
        assert!(
            grow.contains(
                "**Marked: peak RSS grows as n^2.00 (fit), n^2.00 (top), above n^1.5; stdout grows as n^3.00 (fit), n^3.00 (top).**"
            ),
            "{grow}"
        );
        let flat = section("flat");
        assert!(flat.contains("| 10 | 1 | 0.1000 | 10 | - |"), "{flat}");
        assert!(!flat.contains("Marked"), "{flat}");
        let baseline = section("baseline");
        assert!(
            baseline.contains("**Marked: peak RSS grows as n^0.79 (fit), n^1.93 (top)"),
            "{baseline}"
        );
        let toml = atlas.toml().expect("toml");
        assert!(toml.contains("memory_marked = true"), "{toml}");
        assert!(toml.contains("[[ladder.step]]"), "{toml}");
        assert!(toml.contains("[ladder.peak_rss_kib.fit]"), "{toml}");
        assert!(toml.contains("top_slope = "), "{toml}");
    }

    #[test]
    fn staleness_names_algorithms_whose_site_files_changed() {
        let directory = std::env::temp_dir().join(format!("algo-atlas-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(directory.join("src")).expect("directory");
        let git = |args: &[&str]| {
            let status = Command::new("git")
                .arg("-C")
                .arg(&directory)
                .args([
                    "-c",
                    "user.name=test",
                    "-c",
                    "user.email=test@example.invalid",
                    "-c",
                    "commit.gpgsign=false",
                ])
                .args(args)
                .output()
                .expect("git");
            assert!(status.status.success(), "{status:?}");
            String::from_utf8(status.stdout).expect("utf-8")
        };
        git(&["init", "-q"]);
        fs::write(directory.join("src/a.rs"), "fn a() {}\n").expect("write");
        fs::write(directory.join("src/b.rs"), "fn b() {}\n").expect("write");
        fs::write(directory.join("src/c.rs"), "fn c() {}\n").expect("write");
        git(&["add", "."]);
        git(&["commit", "-q", "-m", "base"]);
        let commit = git(&["rev-parse", "HEAD"]).trim().to_owned();
        fs::write(directory.join("src/b.rs"), "fn b() { changed() }\n").expect("write");

        let anchor = |file: &str| Anchor {
            crate_name: "x".to_owned(),
            file: file.to_owned(),
            symbol: "f".to_owned(),
        };
        let node = |id: &str, files: &[&str]| Node {
            kind: "algorithm".to_owned(),
            id: id.to_owned(),
            provenance: "declared".to_owned(),
            anchor: anchor(files[0]),
            area: None,
            name: None,
            sites: files.iter().map(|file| anchor(file)).collect(),
            cost: Vec::new(),
            variable: None,
            invariant: None,
            no_counter: None,
            span: None,
            table: None,
            call: None,
            behavior: None,
            generating_passes: Vec::new(),
            type_path: None,
            role: None,
            registry_name: None,
            sequence: None,
            lean: Vec::new(),
        };
        let graph = Graph {
            nodes: vec![
                node("x.a", &["src/a.rs"]),
                node("x.ab", &["src/a.rs", "src/b.rs"]),
                node("x.c", &["src/c.rs"]),
            ],
            edges: Vec::new(),
        };
        let ids = ["x.a", "x.ab", "x.missing"]
            .into_iter()
            .map(ToOwned::to_owned)
            .collect();
        let code = BTreeSet::new();
        let staleness = check_staleness(&directory, &commit, &graph, &ids, &code).expect("check");
        assert_eq!(staleness.checked, 2);
        assert_eq!(
            staleness.stale,
            [StaleAlgorithm {
                id: "x.ab".to_owned(),
                files: vec!["src/b.rs".to_owned()],
            }]
        );
        assert_eq!(staleness.not_in_graph, ["x.missing"]);
        assert!(staleness.text().contains("stale x.ab: src/b.rs"));

        let clean = ["x.a", "x.c"].into_iter().map(ToOwned::to_owned).collect();
        assert!(
            check_staleness(&directory, &commit, &graph, &clean, &code)
                .expect("check")
                .stale
                .is_empty()
        );
        assert!(check_staleness(&directory, "0000000", &graph, &clean, &code).is_err());
        let functions = ["src/b.rs::b", "src/c.rs::c"]
            .into_iter()
            .map(ToOwned::to_owned)
            .collect();
        let staleness =
            check_staleness(&directory, &commit, &graph, &clean, &functions).expect("check");
        assert_eq!(
            staleness.stale,
            [StaleAlgorithm {
                id: "src/b.rs::b".to_owned(),
                files: vec!["src/b.rs".to_owned()],
            }]
        );
        fs::remove_dir_all(&directory).expect("clean up");
    }

    #[test]
    fn index_reader_resolves_joins_and_refuses_other_schemas() {
        let directory =
            std::env::temp_dir().join(format!("algo-atlas-index-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(directory.join("w/base/rep-1")).expect("directory");
        fs::write(
            directory.join("w/base/rep-1/join.toml"),
            crate::canonical_join_toml(&join(
                "w",
                "c0ffee",
                vec![run("a.x", 1, 1.0, 1.0, &[])],
                &[],
            ))
            .expect("join"),
        )
        .expect("write");
        let path = directory.join("atlas.toml");
        fs::write(
            &path,
            "schema = 1\ncommit = \"c0ffee\"\n[[receipt]]\nworkload = \"w\"\ncommand = \"krun\"\nparam_name = \"n\"\nparam = 3\nrepeat = 1\njoin = \"w/base/rep-1/join.toml\"\nwall_seconds = 5\npeak_rss_kib = 10\n",
        )
        .expect("write");
        let (index, receipts) = read_atlas_index(&path).expect("read");
        assert_eq!(index.receipts[0].param, Some(3.0));
        assert_eq!(receipts[0].entry.wall_seconds, Some(5.0));
        assert!(receipts[0].graph.is_none());
        assert!(receipt_graph(&path, &receipts).is_err());

        fs::write(&path, "schema = 2\ncommit = \"c0ffee\"\n").expect("write");
        let error = read_atlas_index(&path).expect_err("schema 2").to_string();
        assert!(error.contains("index schema 2"), "{error}");
        fs::remove_dir_all(&directory).expect("clean up");
    }
}
