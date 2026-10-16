//! The fixed-format Markdown report of `kbench compare`.
//!
//! The layout is part of the interface, as for `kbench report`: the same sections, columns, row
//! order (the registry's), and number formats every time, so two reports compare line by line.

use std::collections::BTreeSet;
use std::fmt::Write;

use crate::compare::{Comparison, PointComparison, WorkloadComparison};
use crate::report::{growth, mib, seconds};
use crate::results::Samples;
use crate::stats::{
    Interval, MIN_PAIRS, MetricComparison, Verdict, compare_metric, judge_pooled, paired_ratios,
};

const MIB: f64 = 1_048_576.0;
/// Below this base CPU time a point is dominated by process start and is left out of the noise
/// band summary (its verdicts still count).
const NOISE_FLOOR_SECONDS: f64 = 0.2;

#[allow(clippy::cast_precision_loss)]
fn peaks(samples: &Samples) -> Vec<f64> {
    samples.peak_bytes.iter().map(|b| *b as f64).collect()
}

/// A better or worse verdict on a time whose change is under `min_seconds` is within noise:
/// a few milliseconds of process start and exit are not a change of the program's cost.
fn with_time_floor(
    mut metric: MetricComparison,
    base_seconds: Option<f64>,
    min_seconds: f64,
) -> MetricComparison {
    let change = match (metric.ratio, base_seconds) {
        (Some(ratio), Some(base)) => (ratio - 1.0).abs() * base,
        _ => return metric,
    };
    if matches!(metric.verdict, Verdict::Better | Verdict::Worse) && change < min_seconds {
        metric.verdict = Verdict::WithinNoise;
    }
    metric
}

/// The three metrics of a point, in report order: CPU, wall, peak.
pub fn metrics(point: &PointComparison, comparison: &Comparison) -> [MetricComparison; 3] {
    let compare =
        |a: &[f64], b: &[f64]| compare_metric(a, b, comparison.level, comparison.min_effect);
    let time = |a: &[f64], b: &[f64]| {
        let metric = compare(a, b);
        with_time_floor(metric, metric.base, comparison.min_seconds)
    };
    [
        time(&point.base.cpu_seconds, &point.candidate.cpu_seconds),
        time(&point.base.wall_seconds, &point.candidate.wall_seconds),
        compare(&peaks(&point.base), &peaks(&point.candidate)),
    ]
}

/// The timed runs of the selected workloads: one number, or the most common and the others.
fn runs_summary(comparison: &Comparison) -> String {
    let mut counts: std::collections::BTreeMap<u32, usize> = std::collections::BTreeMap::new();
    for workload in comparison.workload.iter().filter(|w| w.status != "skipped") {
        let runs = if workload.runs == 0 {
            comparison.runs
        } else {
            workload.runs
        };
        *counts.entry(runs).or_default() += 1;
    }
    let mut entries: Vec<(u32, usize)> = counts.into_iter().collect();
    entries.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    match entries.split_first() {
        None => comparison.runs.to_string(),
        Some(((runs, _), [])) => runs.to_string(),
        Some(((runs, _), rest)) => format!(
            "{runs} ({})",
            rest.iter()
                .map(|(r, n)| format!("{r} for {n} workload{}", if *n == 1 { "" } else { "s" }))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

/// The points a workload's pooled CPU verdict uses: the completed points with at least
/// `MIN_PAIRS` pairs (a point of one or two runs says nothing about noise) whose base CPU is
/// at least `NOISE_FLOOR_SECONDS`, or all such points when none reaches it.
fn pooled_points(workload: &WorkloadComparison) -> Vec<&PointComparison> {
    let completed: Vec<&PointComparison> = workload
        .point
        .iter()
        .filter(|p| ok(p))
        .filter(|p| paired_ratios(&p.base.cpu_seconds, &p.candidate.cpu_seconds).len() >= MIN_PAIRS)
        .collect();
    let above: Vec<&PointComparison> = completed
        .iter()
        .copied()
        .filter(|p| p.base.cpu().is_some_and(|c| c >= NOISE_FLOOR_SECONDS))
        .collect();
    if above.is_empty() { completed } else { above }
}

/// The number of CPU pairs `pooled_cpu` pools.
fn pooled_pairs(workload: &WorkloadComparison) -> usize {
    pooled_points(workload)
        .iter()
        .map(|p| paired_ratios(&p.base.cpu_seconds, &p.candidate.cpu_seconds).len())
        .sum()
}

/// The workload-level CPU verdict: the paired CPU ratios of `pooled_points`, pooled.
pub fn pooled_cpu(workload: &WorkloadComparison, comparison: &Comparison) -> MetricComparison {
    let pooled = pooled_points(workload);
    let ratios: Vec<f64> = pooled
        .iter()
        .flat_map(|p| paired_ratios(&p.base.cpu_seconds, &p.candidate.cpu_seconds))
        .collect();
    let typical = crate::results::median(
        &pooled
            .iter()
            .filter_map(|p| p.base.cpu())
            .collect::<Vec<f64>>(),
    );
    with_time_floor(
        judge_pooled(&ratios, comparison.level, comparison.min_effect),
        typical,
        comparison.min_seconds,
    )
}

fn ok(point: &PointComparison) -> bool {
    point.base_status == "ok" && point.candidate_status == "ok"
}

/// The point a summary row shows: the largest one both binaries completed.
fn headline(workload: &WorkloadComparison) -> Option<&PointComparison> {
    workload.point.iter().rev().find(|p| ok(p))
}

fn point_label(workload: &WorkloadComparison, point: &PointComparison) -> String {
    match point.param {
        None => "—".to_owned(),
        Some(value) => format!(
            "{} = {value}",
            workload.ladder_param.as_deref().unwrap_or("n")
        ),
    }
}

fn ratio(value: Option<f64>) -> String {
    value.map_or_else(|| "—".to_owned(), |r| format!("{r:.3}"))
}

fn interval(value: Option<&Interval>) -> String {
    value.map_or_else(
        || "—".to_owned(),
        |i| format!("{:.3} … {:.3}", i.low, i.high),
    )
}

fn percent(value: f64) -> String {
    format!("{:.1} %", value * 100.0)
}

fn exponent(value: Option<f64>) -> String {
    value.map_or_else(|| "—".to_owned(), |v| format!("{v:.2}"))
}

fn count(value: Option<u64>) -> String {
    value.map_or_else(|| "—".to_owned(), |v| v.to_string())
}

#[allow(clippy::cast_precision_loss)]
fn per(numerator: Option<f64>, denominator: Option<u64>, scale: f64) -> Option<f64> {
    match (numerator, denominator) {
        (Some(n), Some(d)) if d > 0 => Some(n * scale / d as f64),
        _ => None,
    }
}

fn decimal(value: Option<f64>) -> String {
    match value {
        None => "—".to_owned(),
        Some(v) if v >= 100.0 => format!("{v:.0}"),
        Some(v) if v >= 10.0 => format!("{v:.1}"),
        Some(v) => format!("{v:.2}"),
    }
}

#[allow(clippy::cast_precision_loss)]
fn growth_of(workload: &WorkloadComparison, candidate: bool) -> (Option<f64>, Option<f64>) {
    let side = |p: &PointComparison| {
        if candidate {
            p.candidate.clone()
        } else {
            p.base.clone()
        }
    };
    let points: Vec<(f64, Samples)> = workload
        .point
        .iter()
        .filter(|p| ok(p))
        .filter_map(|p| Some((p.param? as f64, side(p))))
        .collect();
    let cpu: Vec<(f64, f64)> = points
        .iter()
        .filter_map(|(x, s)| Some((*x, s.cpu()?)))
        .collect();
    let peak: Vec<(f64, f64)> = points
        .iter()
        .filter_map(|(x, s)| Some((*x, s.peak()?)))
        .collect();
    (growth(&cpu, 0.05), growth(&peak, 64.0 * MIB))
}

/// Counters that vary slightly between runs of the same binary, and the relative difference
/// below which a difference is not reported. Two copies of one binary differed by at most
/// 6e-5 in `allocation.count` and 3.5e-5 in `allocation.bytes` over 70 points on 2026-10-16;
/// every other counter was identical.
const VARYING_COUNTERS: &[(&str, f64)] = &[("allocation.count", 1e-3), ("allocation.bytes", 1e-3)];

/// Whether two values of a counter differ beyond its run-to-run variation.
fn counter_differs(name: &str, a: Option<u64>, b: Option<u64>) -> bool {
    let (a, b) = (a.unwrap_or(0), b.unwrap_or(0));
    if a == b {
        return false;
    }
    match VARYING_COUNTERS
        .iter()
        .find(|(counter, _)| *counter == name)
    {
        #[allow(clippy::cast_precision_loss)]
        Some((_, tolerance)) => (a.abs_diff(b) as f64) > tolerance * (a.max(b) as f64),
        None => true,
    }
}

/// The unit of the cost per step: `rewrite.steps` where the run counts them, otherwise
/// `rewrite.rules_applied`; `None` when neither side counted either.
fn cost_unit(point: &PointComparison) -> Option<(&'static str, Option<u64>, Option<u64>)> {
    ["rewrite.steps", "rewrite.rules_applied"]
        .into_iter()
        .map(|name| {
            (
                name,
                point.base_counters.get(name).copied(),
                point.candidate_counters.get(name).copied(),
            )
        })
        .find(|(_, a, b)| a.unwrap_or(0) > 0 || b.unwrap_or(0) > 0)
        .map(|(name, a, b)| {
            let unit = if name == "rewrite.steps" {
                "steps"
            } else {
                "rules applied"
            };
            (unit, a, b)
        })
}

/// Counters of a point that differ between the binaries beyond their run-to-run variation.
fn counter_differences(point: &PointComparison) -> Vec<(String, Option<u64>, Option<u64>)> {
    let names: BTreeSet<&String> = point
        .base_counters
        .keys()
        .chain(point.candidate_counters.keys())
        .collect();
    names
        .into_iter()
        .filter_map(|name| {
            let a = point.base_counters.get(name).copied();
            let b = point.candidate_counters.get(name).copied();
            counter_differs(name, a, b).then(|| (name.clone(), a, b))
        })
        .collect()
}

fn change(a: Option<u64>, b: Option<u64>) -> String {
    match (a, b) {
        (Some(a), Some(b)) if a > 0 => {
            #[allow(clippy::cast_precision_loss)]
            let change = (b as f64 - a as f64) / a as f64 * 100.0;
            format!("{change:+.1} %")
        }
        _ => "new".to_owned(),
    }
}

struct Tally {
    better: usize,
    worse: usize,
    noise: usize,
    unknown: usize,
}

impl Tally {
    fn line(&self, name: &str, points: usize) -> String {
        format!(
            "- {name}: {} better, {} worse, {} within noise, {} without a verdict (of {points} points).",
            self.better, self.worse, self.noise, self.unknown
        )
    }
}

#[allow(clippy::too_many_lines)]
pub fn render(comparison: &Comparison) -> String {
    let mut out = String::new();
    let selected: Vec<&WorkloadComparison> = comparison
        .workload
        .iter()
        .filter(|w| w.status != "skipped")
        .collect();
    let counters = comparison.counters_base.is_some();

    let _ = writeln!(out, "# krust comparison report\n");
    let _ = writeln!(out, "| | |\n|:--|:--|");
    let _ = writeln!(
        out,
        "| Comparison | `{}`, {} → {} |",
        comparison.compare_id, comparison.started_at, comparison.finished_at
    );
    let _ = writeln!(
        out,
        "| Selection | {}; {} |",
        comparison.selection.join(", "),
        if comparison.full_ladders {
            "full ladders"
        } else {
            "ladders capped by the set's `ladder_max`"
        }
    );
    for (label, binary) in [
        ("Base (A)", &comparison.base),
        ("Candidate (B)", &comparison.candidate),
    ] {
        let _ = writeln!(
            out,
            "| {label} | `{}`, sha256 `{}`{} |",
            binary.path,
            &binary.sha256[..binary.sha256.len().min(16)],
            if binary.measure {
                ", measure build"
            } else {
                ""
            }
        );
    }
    match (&comparison.counters_base, &comparison.counters_candidate) {
        (Some(a), Some(b)) => {
            let _ = writeln!(
                out,
                "| Counters | one separate `KRUST_COUNTERS` run per binary and point: base `{}`, candidate `{}` |",
                a.path, b.path
            );
        }
        _ => {
            let _ = writeln!(out, "| Counters | not collected |");
        }
    }
    let _ = writeln!(
        out,
        "| Registry | commit `{}` |",
        &comparison.commit[..comparison.commit.len().min(12)]
    );
    let _ = writeln!(
        out,
        "| Host | {}, {} CPUs, load {} → {} |",
        comparison.host.hostname,
        comparison.host.cpus,
        comparison.host.load_before,
        comparison.host.load_after
    );
    let _ = writeln!(out, "| Method | {} |", comparison.method);
    let _ = writeln!(
        out,
        "| Statistics | {} timed runs per binary and point, interleaved A B, B A, …; B/A is the ratio of the medians; the interval is the sign-test interval of the median of the paired ratios B/A (at least {:.0} % coverage where the run count allows); better or worse needs the whole interval on one side of 1, B/A beyond ±{:.0} %, and for CPU and wall a change of at least {} s |",
        runs_summary(comparison),
        comparison.level * 100.0,
        comparison.min_effect * 100.0,
        comparison.min_seconds
    );
    let _ = writeln!(out);
    let _ = writeln!(
        out,
        "CPU (user + system time of the whole process tree, the primary metric) and wall are medians in seconds; peak is the median peak memory of the whole process tree in MiB.\n\
         For every metric lower is better: B/A below 1 means the candidate is cheaper.\n"
    );

    // Verdict.
    let points: Vec<(&WorkloadComparison, &PointComparison)> = selected
        .iter()
        .flat_map(|w| w.point.iter().filter(|p| ok(p)).map(move |p| (*w, p)))
        .collect();
    let mut tallies: Vec<Tally> = (0..3)
        .map(|_| Tally {
            better: 0,
            worse: 0,
            noise: 0,
            unknown: 0,
        })
        .collect();
    for (_, point) in &points {
        for (tally, metric) in tallies.iter_mut().zip(metrics(point, comparison)) {
            match metric.verdict {
                Verdict::Better => tally.better += 1,
                Verdict::Worse => tally.worse += 1,
                Verdict::WithinNoise => tally.noise += 1,
                Verdict::Unknown => tally.unknown += 1,
            }
        }
    }
    let _ = writeln!(out, "## Verdict\n");
    let mismatched: Vec<&str> = selected
        .iter()
        .filter(|w| w.point.iter().any(|p| p.output == "differs"))
        .map(|w| w.id.as_str())
        .collect();
    let ignored: Vec<&str> = selected
        .iter()
        .filter(|w| w.ignored_output.is_some())
        .map(|w| w.id.as_str())
        .collect();
    if mismatched.is_empty() {
        let _ = writeln!(
            out,
            "- Output: identical on every timed run of every point{}.",
            if ignored.is_empty() {
                String::new()
            } else {
                format!(
                    " (parts that vary between runs are left out on {}; see Notes)",
                    ignored.join(", ")
                )
            }
        );
    } else {
        let _ = writeln!(
            out,
            "- **Output: DIFFERS** on {}: the candidate changes behaviour.",
            mismatched
                .iter()
                .map(|id| format!("`{id}`"))
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    let failed: Vec<&WorkloadComparison> = selected
        .iter()
        .copied()
        .filter(|w| w.status == "failed" || w.status == "error")
        .collect();
    if failed.is_empty() {
        let _ = writeln!(out, "- Checks: every run passed its workload's check.");
    } else {
        let _ = writeln!(
            out,
            "- **Checks: {} workload(s) FAILED** (see Failures).",
            failed.len()
        );
    }
    let mut workload_tally = Tally {
        better: 0,
        worse: 0,
        noise: 0,
        unknown: 0,
    };
    let judged: Vec<&&WorkloadComparison> =
        selected.iter().filter(|w| headline(w).is_some()).collect();
    for workload in &judged {
        match pooled_cpu(workload, comparison).verdict {
            Verdict::Better => workload_tally.better += 1,
            Verdict::Worse => workload_tally.worse += 1,
            Verdict::WithinNoise => workload_tally.noise += 1,
            Verdict::Unknown => workload_tally.unknown += 1,
        }
    }
    let _ = writeln!(
        out,
        "- CPU per workload (pooled over its points): {} better, {} worse, {} within noise, {} without a verdict (of {} workloads).",
        workload_tally.better,
        workload_tally.worse,
        workload_tally.noise,
        workload_tally.unknown,
        judged.len()
    );
    for (tally, name) in tallies.iter().zip(["CPU", "Wall", "Peak"]) {
        let _ = writeln!(
            out,
            "{}",
            tally.line(&format!("{name} per point"), points.len())
        );
    }
    if counters {
        let differing: usize = points
            .iter()
            .map(|(_, p)| counter_differences(p).len())
            .sum();
        if differing == 0 {
            let _ = writeln!(
                out,
                "- Counters: every counter is identical at every point."
            );
        } else {
            let _ = writeln!(
                out,
                "- **Counters: {differing} counter values differ** (see Counter differences): each is a change in the work done, expected or not."
            );
        }
    }
    let _ = writeln!(
        out,
        "- Exit status: {}.\n",
        if comparison.passed() {
            "0 (outputs identical, checks passed)"
        } else {
            "1 (a mismatch or a failure)"
        }
    );

    // Summary.
    let _ = writeln!(out, "## Summary\n");
    let _ = writeln!(
        out,
        "One row per workload. Pooled: the paired CPU ratios of all its points with a base CPU of at least {NOISE_FLOOR_SECONDS} s (all points when none is), their median, interval, and verdict: the workload's CPU verdict.\n\
         The other columns are at the largest point both binaries completed.\n"
    );
    let _ = writeln!(
        out,
        "| Workload | Pairs | Pooled CPU B/A | Pooled interval | Pooled CPU | Point | CPU A | CPU B | CPU B/A | CPU | Wall B/A | Wall | Peak A | Peak B | Peak B/A | Peak | Output |"
    );
    let _ = writeln!(
        out,
        "|:--|--:|--:|:--|:--|:--|--:|--:|--:|:--|--:|:--|--:|--:|--:|:--|:--|"
    );
    for workload in &selected {
        let Some(point) = headline(workload) else {
            let _ = writeln!(
                out,
                "| `{}` | — | — | — | — | — | — | — | — | — | — | — | — | — | — | — | {} |",
                workload.id, workload.status
            );
            continue;
        };
        let [cpu, wall, peak] = metrics(point, comparison);
        let pooled = pooled_cpu(workload, comparison);
        let _ = writeln!(
            out,
            "| `{}` | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
            workload.id,
            pooled_pairs(workload),
            ratio(pooled.ratio),
            interval(pooled.interval.as_ref()),
            pooled.verdict.label(),
            point_label(workload, point),
            seconds(cpu.base),
            seconds(cpu.candidate),
            ratio(cpu.ratio),
            cpu.verdict.label(),
            ratio(wall.ratio),
            wall.verdict.label(),
            mib(peak.base),
            mib(peak.candidate),
            ratio(peak.ratio),
            peak.verdict.label(),
            point.output
        );
    }
    let _ = writeln!(out);

    // Ladders.
    let ladders: Vec<&&WorkloadComparison> = selected
        .iter()
        .filter(|w| w.ladder_param.is_some())
        .collect();
    if !ladders.is_empty() {
        let _ = writeln!(out, "## Ladders\n");
        let _ = writeln!(
            out,
            "Growth exponent: the least-squares slope of log(CPU) over log(size) for the largest four sizes of at least 0.05 s (1 is linear, 2 quadratic); for peak memory, sizes of at least 64 MiB.\n"
        );
        let _ = writeln!(
            out,
            "| Workload | Values run | Registry values | CPU growth A | CPU growth B | Peak growth A | Peak growth B | Ended |"
        );
        let _ = writeln!(out, "|:--|:--|:--|--:|--:|--:|--:|:--|");
        for workload in ladders {
            let run: Vec<String> = workload
                .point
                .iter()
                .filter_map(|p| p.param.map(|v| v.to_string()))
                .collect();
            let registry: Vec<String> = workload.ladder_values.iter().map(i64::to_string).collect();
            let (cpu_a, peak_a) = growth_of(workload, false);
            let (cpu_b, peak_b) = growth_of(workload, true);
            let ended = if let Some(stopped) = &workload.stopped {
                stopped.clone()
            } else if workload.status == "failed" {
                "a run failed (see Failures)".to_owned()
            } else if let Some(cap) = workload.ladder_cap {
                format!("set cap {cap}")
            } else {
                "all values".to_owned()
            };
            let _ = writeln!(
                out,
                "| `{}` ({}) | {} | {} | {} | {} | {} | {} | {ended} |",
                workload.id,
                workload.ladder_param.as_deref().unwrap_or("n"),
                run.join(" / "),
                registry.join(" / "),
                exponent(cpu_a),
                exponent(cpu_b),
                exponent(peak_a),
                exponent(peak_b),
            );
        }
        let _ = writeln!(out);
    }

    // Every point.
    let _ = writeln!(out, "## Every point\n");
    let _ = writeln!(
        out,
        "| Workload | Point | CPU A | CPU B | CPU B/A | CPU interval | CPU | Wall A | Wall B | Wall B/A | Wall interval | Wall | Peak A | Peak B | Peak B/A | Peak interval | Peak | Output |"
    );
    let _ = writeln!(
        out,
        "|:--|:--|--:|--:|--:|:--|:--|--:|--:|--:|:--|:--|--:|--:|--:|:--|:--|:--|"
    );
    for workload in &selected {
        for point in &workload.point {
            if !ok(point) {
                let _ = writeln!(
                    out,
                    "| `{}` | {} | FAILED | | | | | | | | | | | | | | | {} |",
                    workload.id,
                    point_label(workload, point),
                    point.output
                );
                continue;
            }
            let [cpu, wall, peak] = metrics(point, comparison);
            let _ = writeln!(
                out,
                "| `{}` | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
                workload.id,
                point_label(workload, point),
                seconds(cpu.base),
                seconds(cpu.candidate),
                ratio(cpu.ratio),
                interval(cpu.interval.as_ref()),
                cpu.verdict.label(),
                seconds(wall.base),
                seconds(wall.candidate),
                ratio(wall.ratio),
                interval(wall.interval.as_ref()),
                wall.verdict.label(),
                mib(peak.base),
                mib(peak.candidate),
                ratio(peak.ratio),
                interval(peak.interval.as_ref()),
                peak.verdict.label(),
                point.output
            );
        }
    }
    let _ = writeln!(out);

    // Noise band.
    let _ = writeln!(out, "## Noise band\n");
    let _ = writeln!(
        out,
        "Per workload, over its points whose base CPU is at least {NOISE_FLOOR_SECONDS} s: the widest interval half-width of each metric, and the largest deviation of a single pair's CPU ratio from the median paired ratio.\n\
         A change larger than the half-width plus the {:.0} % minimum moves the whole interval past 1 and gets a verdict; for two identical binaries every verdict should be within noise.\n",
        comparison.min_effect * 100.0
    );
    let _ = writeln!(
        out,
        "| Workload | Points | CPU half-width | Wall half-width | Peak half-width | Largest CPU pair deviation |"
    );
    let _ = writeln!(out, "|:--|--:|--:|--:|--:|--:|");
    for workload in &selected {
        let noisy: Vec<&PointComparison> = workload
            .point
            .iter()
            .filter(|p| ok(p) && p.base.cpu().is_some_and(|c| c >= NOISE_FLOOR_SECONDS))
            .collect();
        if noisy.is_empty() {
            let _ = writeln!(out, "| `{}` | 0 | — | — | — | — |", workload.id);
            continue;
        }
        let mut widest = [None::<f64>; 3];
        let mut deviation = None::<f64>;
        for point in &noisy {
            for (slot, metric) in widest.iter_mut().zip(metrics(point, comparison)) {
                if let Some(i) = metric.interval {
                    *slot = Some(slot.map_or(i.half_width(), |w: f64| w.max(i.half_width())));
                }
            }
            let ratios = paired_ratios(&point.base.cpu_seconds, &point.candidate.cpu_seconds);
            if let Some(center) = crate::results::median(&ratios) {
                for r in ratios {
                    let d = (r - center).abs();
                    deviation = Some(deviation.map_or(d, |x: f64| x.max(d)));
                }
            }
        }
        let cell = |v: Option<f64>| v.map_or_else(|| "—".to_owned(), percent);
        let _ = writeln!(
            out,
            "| `{}` | {} | {} | {} | {} | {} |",
            workload.id,
            noisy.len(),
            cell(widest[0]),
            cell(widest[1]),
            cell(widest[2]),
            cell(deviation)
        );
    }
    let _ = writeln!(out);

    if counters {
        let _ = writeln!(out, "## Cost per step\n");
        let _ = writeln!(
            out,
            "The unit is `rewrite.steps`, the states the execution loop visited (one rewrite step each; merged arrivals included, `execution.states_merged` of them), or, where the run takes no such step (a `--search` run's breadth-first search counts no visited states), `rewrite.rules_applied`, the successors that rule applications produced.\n\
             CPU per unit divides the median timed CPU by the count; allocations per unit divide `allocation.count`.\n"
        );
        let _ = writeln!(
            out,
            "| Workload | Point | Unit | Count A | Count B | Merged A | Merged B | µs CPU per unit A | µs CPU per unit B | B/A | Allocations per unit A | Allocations per unit B |"
        );
        let _ = writeln!(out, "|:--|:--|:--|--:|--:|--:|--:|--:|--:|--:|--:|--:|");
        for workload in &selected {
            for point in workload.point.iter().filter(|p| ok(p)) {
                let Some((unit, units_a, units_b)) = cost_unit(point) else {
                    continue;
                };
                let merged_a = point.base_counters.get("execution.states_merged").copied();
                let merged_b = point
                    .candidate_counters
                    .get("execution.states_merged")
                    .copied();
                let per_unit_a = per(point.base.cpu(), units_a, 1e6);
                let per_unit_b = per(point.candidate.cpu(), units_b, 1e6);
                #[allow(clippy::cast_precision_loss)]
                let allocations = |counters: &std::collections::BTreeMap<String, u64>,
                                   units: Option<u64>| {
                    per(
                        counters.get("allocation.count").map(|v| *v as f64),
                        units,
                        1.0,
                    )
                };
                let per_unit_ratio = match (per_unit_a, per_unit_b) {
                    (Some(a), Some(b)) if a > 0.0 => Some(b / a),
                    _ => None,
                };
                let _ = writeln!(
                    out,
                    "| `{}` | {} | {unit} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
                    workload.id,
                    point_label(workload, point),
                    count(units_a),
                    count(units_b),
                    count(merged_a),
                    count(merged_b),
                    decimal(per_unit_a),
                    decimal(per_unit_b),
                    ratio(per_unit_ratio),
                    decimal(allocations(&point.base_counters, units_a)),
                    decimal(allocations(&point.candidate_counters, units_b)),
                );
            }
        }
        let _ = writeln!(out);

        let _ = writeln!(out, "## Counter differences\n");
        let _ = writeln!(
            out,
            "Every counter whose values differ at a point; `allocation.count` and `allocation.bytes` vary by up to 6e-5 between runs of the same binary, so their differences below 0.1 % are not listed.\n"
        );
        let rows: Vec<String> = selected
            .iter()
            .flat_map(|w| {
                w.point.iter().filter(|p| ok(p)).flat_map(move |p| {
                    counter_differences(p).into_iter().map(move |(name, a, b)| {
                        format!(
                            "| `{}` | {} | `{name}` | {} | {} | {} |",
                            w.id,
                            point_label(w, p),
                            count(a),
                            count(b),
                            change(a, b)
                        )
                    })
                })
            })
            .collect();
        if rows.is_empty() {
            let _ = writeln!(out, "None: every counter is identical at every point.\n");
        } else {
            let _ = writeln!(out, "| Workload | Point | Counter | A | B | Change |");
            let _ = writeln!(out, "|:--|:--|:--|--:|--:|--:|");
            for row in rows {
                let _ = writeln!(out, "{row}");
            }
            let _ = writeln!(out);
        }

        let _ = writeln!(out, "## Counters at the summary point\n");
        let _ = writeln!(
            out,
            "Every counter that is not zero on either side; ≠ marks a difference, ≈ a difference within the counter's run-to-run variation.\n"
        );
        for workload in &selected {
            let Some(point) = headline(workload) else {
                continue;
            };
            if point.base_counters.is_empty() && point.candidate_counters.is_empty() {
                continue;
            }
            let _ = writeln!(
                out,
                "### `{}` ({})\n",
                workload.id,
                point_label(workload, point)
            );
            let _ = writeln!(out, "| Counter | A | B | |");
            let _ = writeln!(out, "|:--|--:|--:|:-:|");
            let names: BTreeSet<&String> = point
                .base_counters
                .keys()
                .chain(point.candidate_counters.keys())
                .collect();
            for name in names {
                let a = point.base_counters.get(name).copied();
                let b = point.candidate_counters.get(name).copied();
                if a.unwrap_or(0) == 0 && b.unwrap_or(0) == 0 {
                    continue;
                }
                let mark = if counter_differs(name, a, b) {
                    "≠"
                } else if a != b {
                    "≈"
                } else {
                    ""
                };
                let _ = writeln!(out, "| `{name}` | {} | {} | {mark} |", count(a), count(b));
            }
            let _ = writeln!(out);
        }
    }

    if !failed.is_empty() || !mismatched.is_empty() {
        let _ = writeln!(out, "## Failures\n");
        let mut index = 0;
        for workload in &selected {
            if workload.status == "ok" {
                continue;
            }
            index += 1;
            let _ = writeln!(
                out,
                "{index}. `{}` ({}): {}",
                workload.id,
                workload.status,
                workload.detail.as_deref().unwrap_or("")
            );
        }
        let _ = writeln!(out);
    }

    let _ = writeln!(out, "## Notes\n");
    let mut notes = 0;
    for workload in &comparison.workload {
        if workload.status == "skipped" {
            notes += 1;
            let _ = writeln!(
                out,
                "- `{}` not compared: {}.",
                workload.id,
                workload.detail.as_deref().unwrap_or("skipped")
            );
        }
        if let Some(ignored) = &workload.ignored_output {
            notes += 1;
            let _ = writeln!(out, "- `{}`: {ignored}", workload.id);
        }
    }
    if notes == 0 {
        let _ = writeln!(out, "None.");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compare::{Binary, COMPARE_SCHEMA};
    use crate::results::Host;

    fn binary(path: &str) -> Binary {
        Binary {
            path: path.to_owned(),
            sha256: "ab".repeat(32),
            prepared: String::new(),
            measure: false,
        }
    }

    fn samples(cpu: &[f64]) -> Samples {
        Samples {
            wall_seconds: cpu.to_vec(),
            cpu_seconds: cpu.to_vec(),
            peak_bytes: vec![100 << 20; cpu.len()],
        }
    }

    fn comparison(candidate_scale: f64, output: &str) -> Comparison {
        let base = [1.0, 1.01, 0.99, 1.0, 1.02];
        let candidate: Vec<f64> = base.iter().map(|v| v * candidate_scale).collect();
        Comparison {
            schema: COMPARE_SCHEMA.to_owned(),
            compare_id: "test".to_owned(),
            started_at: String::new(),
            finished_at: String::new(),
            selection: vec!["set:test".to_owned()],
            runs: 5,
            min_effect: 0.03,
            min_seconds: 0.02,
            level: 0.9,
            full_ladders: false,
            commit: "0123456789abcdef".to_owned(),
            base: binary("/a/krust"),
            candidate: binary("/b/krust"),
            counters_base: None,
            counters_candidate: None,
            method: String::new(),
            host: Host::default(),
            workload: vec![WorkloadComparison {
                id: "imp/x".to_owned(),
                semantics: "imp".to_owned(),
                operation: "execute".to_owned(),
                title: String::new(),
                runs: 5,
                status: if output == "differs" {
                    "mismatch"
                } else {
                    "ok"
                }
                .to_owned(),
                detail: None,
                ladder_param: None,
                ladder_values: Vec::new(),
                ladder_cap: None,
                stopped: None,
                ignored_output: None,
                point: vec![PointComparison {
                    param: None,
                    base_status: "ok".to_owned(),
                    candidate_status: "ok".to_owned(),
                    output: output.to_owned(),
                    base: samples(&base),
                    candidate: samples(&candidate),
                    ..PointComparison::default()
                }],
            }],
        }
    }

    #[test]
    fn identical_runs_render_within_noise_and_a_slowdown_worse() {
        let same = render(&comparison(1.0, "identical"));
        assert!(same.contains("- CPU per point: 0 better, 0 worse, 1 within noise"));
        assert!(same.contains(
            "- CPU per workload (pooled over its points): 0 better, 0 worse, 1 within noise"
        ));
        assert!(same.contains("- Output: identical"));
        assert!(same.contains("Exit status: 0"));
        let slower = render(&comparison(1.1, "identical"));
        assert!(slower.contains("- CPU per point: 0 better, 1 worse, 0 within noise"));
        assert!(slower.contains("(pooled over its points): 0 better, 1 worse"));
        assert!(slower.contains("| 1.100 |"));
    }

    #[test]
    fn a_change_of_a_few_milliseconds_is_within_noise() {
        let mut short = comparison(1.1, "identical");
        let point = &mut short.workload[0].point[0];
        for samples in [&mut point.base, &mut point.candidate] {
            for value in samples
                .cpu_seconds
                .iter_mut()
                .chain(&mut samples.wall_seconds)
            {
                *value *= 0.05;
            }
        }
        // 10 % of 50 ms is 5 ms, under the 20 ms floor.
        assert!(render(&short).contains("- CPU per point: 0 better, 0 worse, 1 within noise"));
    }

    #[test]
    fn single_runs_give_no_pooled_verdict() {
        let mut once = comparison(1.5, "identical");
        once.truncate_runs(1);
        let text = render(&once);
        assert!(text.contains(
            "(pooled over its points): 0 better, 0 worse, 0 within noise, 1 without a verdict"
        ));
    }

    #[test]
    fn a_mismatch_is_reported_prominently() {
        let text = render(&comparison(1.0, "differs"));
        assert!(text.contains("**Output: DIFFERS** on `imp/x`"));
        assert!(text.contains("Exit status: 1"));
        assert!(text.contains("## Failures"));
    }

    #[test]
    fn allocation_counters_tolerate_run_to_run_variation() {
        assert!(!counter_differs(
            "allocation.count",
            Some(1_000_000),
            Some(1_000_050)
        ));
        assert!(counter_differs(
            "allocation.count",
            Some(1_000_000),
            Some(1_002_000)
        ));
        assert!(counter_differs(
            "rewrite.steps",
            Some(1_000_000),
            Some(1_000_001)
        ));
        assert!(!counter_differs("rewrite.steps", Some(5), Some(5)));
        assert!(counter_differs("rewrite.steps", None, Some(1)));
    }

    #[test]
    fn search_runs_cost_per_applied_rule() {
        let mut point = PointComparison::default();
        point
            .base_counters
            .insert("rewrite.rules_applied".to_owned(), 10);
        point
            .candidate_counters
            .insert("rewrite.rules_applied".to_owned(), 10);
        assert_eq!(cost_unit(&point).unwrap().0, "rules applied");
        point.base_counters.insert("rewrite.steps".to_owned(), 7);
        assert_eq!(cost_unit(&point), Some(("steps", Some(7), None)));
        assert!(cost_unit(&PointComparison::default()).is_none());
    }

    #[test]
    fn the_report_survives_a_toml_round_trip() {
        let original = comparison(1.1, "identical");
        let text = toml::to_string(&original).unwrap();
        let back: Comparison = toml::from_str(&text).unwrap();
        assert_eq!(render(&original), render(&back));
    }
}
