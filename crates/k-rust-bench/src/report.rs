//! The fixed-format Markdown report of a run.
//!
//! The layout is part of the interface: the same sections, columns, row order, and number
//! formats every time, so two reports compare line by line.
//! Every registered workload has a row, including those the run did not select.

use std::collections::BTreeMap;
use std::fmt::Write;

use crate::registry::{OPERATIONS, SEMANTICS};
use crate::results::{Point, Run, Samples, WorkloadResult};

const MIB: f64 = 1_048_576.0;

fn semantics_label(semantics: &str) -> &str {
    match semantics {
        "imp" => "IMP",
        "fun" => "FUN",
        "simple" => "SIMPLE",
        "kool" => "KOOL",
        "lambda" => "LAMBDA",
        "toy" => "Small definitions and synthetic stress",
        "kevm" => "KEVM",
        "kwasm" => "KWASM",
        "kmir" => "KMIR",
        "krs" => "KRS",
        other => other,
    }
}

pub fn seconds(value: Option<f64>) -> String {
    match value {
        None => "—".to_owned(),
        Some(v) if v >= 100.0 => format!("{v:.0}"),
        Some(v) if v >= 10.0 => format!("{v:.1}"),
        Some(v) if v >= 1.0 => format!("{v:.2}"),
        Some(v) => format!("{v:.3}"),
    }
}

pub fn mib(bytes: Option<f64>) -> String {
    match bytes {
        None => "—".to_owned(),
        Some(b) => {
            let m = b / MIB;
            if m >= 100.0 {
                format!("{m:.0}")
            } else {
                format!("{m:.1}")
            }
        }
    }
}

fn ratio(value: Option<f64>) -> String {
    match value {
        None => "—".to_owned(),
        Some(r) if r >= 100.0 => format!("{r:.0}×"),
        Some(r) if r >= 1.0 => format!("{r:.1}×"),
        Some(r) => format!("{r:.2}×"),
    }
}

/// Change from `base` to `now` in percent, with a mark beyond ±10 %.
fn delta(now: Option<f64>, base: Option<f64>) -> String {
    match (now, base) {
        (Some(now), Some(base)) if base > 0.0 => {
            let change = (now - base) / base * 100.0;
            let mark = if change > 10.0 {
                " ▲"
            } else if change < -10.0 {
                " ▼"
            } else {
                ""
            };
            let sign = if change >= 0.0 { "+" } else { "−" };
            format!("{sign}{:.0}%{mark}", change.abs())
        }
        _ => "—".to_owned(),
    }
}

fn divide(a: Option<f64>, b: Option<f64>) -> Option<f64> {
    match (a, b) {
        (Some(a), Some(b)) if b > 0.0 => Some(a / b),
        _ => None,
    }
}

/// The figures a table row shows: the samples of a plain workload, or of a ladder's largest
/// value that krust completed and, when the reference has ladder figures, the reference
/// completed too, so the row compares the same size; otherwise krust's largest completed value.
fn headline(
    samples: Option<&Samples>,
    points: &[Point],
    reference: &[Point],
) -> Option<(Samples, Option<i64>)> {
    if let Some(samples) = samples {
        return Some((samples.clone(), None));
    }
    let completed = |p: &&Point| p.status == "ok";
    points
        .iter()
        .rev()
        .filter(completed)
        .find(|p| {
            reference
                .iter()
                .any(|r| r.param == p.param && r.status == "ok")
        })
        .or_else(|| points.iter().rev().find(completed))
        .map(|p| (p.samples.clone(), Some(p.param)))
}

/// A short label for a failed ladder size (the full text stays in `results.toml`).
fn short_failure(status: &str) -> String {
    if status.starts_with("not run") {
        return "not run".to_owned();
    }
    let label = if status.contains("OutOfMemoryError") {
        "out of heap"
    } else if status.contains("StackOverflowError") || status.contains("stack overflow") {
        "stack overflow"
    } else if status.contains("Segmentation") || status.contains("exit status 139") {
        "crash"
    } else if status.starts_with("timeout") {
        "timeout"
    } else if status.starts_with("out of memory") {
        "out of memory"
    } else {
        return format!("✗ {}", status.split(" (stderr").next().unwrap_or(status));
    };
    format!("✗ {label}")
}

fn reference_point(result: &WorkloadResult, param: Option<i64>) -> Option<Samples> {
    match param {
        None => result.reference.samples.clone(),
        Some(param) => result
            .reference
            .points
            .iter()
            .find(|p| p.param == param && p.status == "ok")
            .map(|p| p.samples.clone()),
    }
}

fn reference_cell(result: &WorkloadResult) -> Option<String> {
    let reference = &result.reference;
    match reference.status.as_str() {
        "cached" => None,
        "unsupported" => Some(format!(
            "n/a: {}",
            reference.reason.as_deref().unwrap_or("unsupported")
        )),
        "untested" => Some("not paired yet".to_owned()),
        "missing" => Some("not measured yet".to_owned()),
        "stale" => Some("stale: command changed".to_owned()),
        "failed" => Some(format!(
            "reference failed: {}",
            reference.note.as_deref().unwrap_or("unknown")
        )),
        other => Some(other.to_owned()),
    }
}

/// Least-squares slope of log(y) over log(x) for the last points with y ≥ `floor`.
pub fn growth(points: &[(f64, f64)], floor: f64) -> Option<f64> {
    let usable: Vec<(f64, f64)> = points
        .iter()
        .filter(|(x, y)| *x > 0.0 && *y >= floor)
        .map(|(x, y)| (x.ln(), y.ln()))
        .collect();
    let usable = &usable[usable.len().saturating_sub(4)..];
    if usable.len() < 2 {
        return None;
    }
    #[allow(clippy::cast_precision_loss)]
    let n = usable.len() as f64;
    let mean_x = usable.iter().map(|p| p.0).sum::<f64>() / n;
    let mean_y = usable.iter().map(|p| p.1).sum::<f64>() / n;
    let sxx: f64 = usable.iter().map(|p| (p.0 - mean_x).powi(2)).sum();
    let sxy: f64 = usable.iter().map(|p| (p.0 - mean_x) * (p.1 - mean_y)).sum();
    (sxx > 0.0).then(|| sxy / sxx)
}

#[allow(clippy::cast_precision_loss)]
fn ladder_growth(points: &[Point]) -> (Option<f64>, Option<f64>) {
    let ok: Vec<&Point> = points.iter().filter(|p| p.status == "ok").collect();
    let wall: Vec<(f64, f64)> = ok
        .iter()
        .filter_map(|p| Some((p.param as f64, p.samples.wall()?)))
        .collect();
    let peak: Vec<(f64, f64)> = ok
        .iter()
        .filter_map(|p| Some((p.param as f64, p.samples.peak()?)))
        .collect();
    (growth(&wall, 0.05), growth(&peak, 64.0 * MIB))
}

fn exponent(value: Option<f64>) -> String {
    value.map_or_else(|| "—".to_owned(), |v| format!("{v:.2}"))
}

pub fn render(run: &Run, baseline: Option<&Run>) -> String {
    let mut out = String::new();
    let base: BTreeMap<&str, &WorkloadResult> = baseline
        .map(|b| b.workload.iter().map(|w| (w.id.as_str(), w)).collect())
        .unwrap_or_default();

    let _ = writeln!(out, "# krust benchmark report\n");
    let _ = writeln!(out, "| | |\n|:--|:--|");
    let _ = writeln!(
        out,
        "| Run | `{}`, tier **{}**, {} → {} |",
        run.run_id, run.tier, run.started_at, run.finished_at
    );
    let _ = writeln!(
        out,
        "| krust | commit `{}`{}, binary sha256 `{}` |",
        &run.commit[..run.commit.len().min(12)],
        if run.dirty { " (modified)" } else { "" },
        &run.krust_sha256[..run.krust_sha256.len().min(16)]
    );
    let _ = writeln!(
        out,
        "| Reference | K {} from `benchmarks/reference.toml` (cached; a run never re-measures it), `K_OPTS={}` |",
        run.reference_k_version, run.reference_k_opts
    );
    match baseline {
        Some(b) => {
            let _ = writeln!(
                out,
                "| Baseline | `{}`, tier {}, commit `{}` |",
                b.run_id,
                b.tier,
                &b.commit[..b.commit.len().min(12)]
            );
        }
        None => {
            let _ = writeln!(out, "| Baseline | none |");
        }
    }
    let _ = writeln!(
        out,
        "| Host | {}, {} CPUs, {:.0} GiB, kernel {}, load {} → {} |",
        run.host.hostname,
        run.host.cpus,
        run.host.memory_bytes as f64 / (MIB * 1024.0),
        run.host.kernel,
        run.host.load_before,
        run.host.load_after
    );
    let _ = writeln!(out, "| Method | {} |", run.memory_method);
    if !run.filter.is_empty() {
        let _ = writeln!(out, "| Filter | {} |", run.filter.join(", "));
    }
    let _ = writeln!(out);
    let _ = writeln!(
        out,
        "Wall and CPU are medians in seconds; CPU is user + system time of the whole process tree.\n\
         Peak is the median peak memory of the whole process tree in MiB.\n\
         Speedup is reference wall / krust wall (above 1× krust is faster); memory ratio is krust peak / reference peak (below 1× krust uses less).\n\
         Δ compares krust with the baseline run (▲ more than 10 % higher, ▼ more than 10 % lower).\n\
         A ladder row shows its largest completed size; the ladder table below has every size.\n"
    );

    // Coverage grid.
    let _ = writeln!(out, "## Coverage\n");
    let _ = write!(out, "| Semantics |");
    for operation in OPERATIONS {
        let _ = write!(out, " {operation} |");
    }
    let _ = write!(out, "\n|:--|");
    for _ in OPERATIONS {
        let _ = write!(out, ":-:|");
    }
    let _ = writeln!(out);
    for semantics in SEMANTICS {
        let rows: Vec<&WorkloadResult> = run
            .workload
            .iter()
            .filter(|w| w.semantics == *semantics)
            .collect();
        if rows.is_empty() {
            continue;
        }
        let _ = write!(out, "| {} |", semantics_label(semantics));
        for operation in OPERATIONS {
            let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
            for row in rows.iter().filter(|w| w.operation == *operation) {
                let symbol = match row.reference.status.as_str() {
                    "cached" => "●",
                    "missing" | "stale" | "failed" => "◐",
                    "unsupported" => "○",
                    _ => "?",
                };
                *counts.entry(symbol).or_default() += 1;
            }
            let gap = run
                .gap
                .iter()
                .any(|g| g.semantics == *semantics && g.operation == *operation);
            if counts.is_empty() && gap {
                let _ = write!(out, " ✗ |");
            } else if counts.is_empty() {
                let _ = write!(out, " — |");
            } else {
                let cell: Vec<String> = ["●", "◐", "○", "?"]
                    .iter()
                    .filter_map(|s| counts.get(s).map(|n| format!("{s}{n}")))
                    .collect();
                let _ = write!(out, " {} |", cell.join(" "));
            }
        }
        let _ = writeln!(out);
    }
    let _ = writeln!(
        out,
        "\n● paired with a cached reference measurement · ◐ paired, reference not measured yet (or stale or failed) · \
         ○ krust only: reference K cannot run it (reason in the table) · ? reference pairing not written yet · \
         ✗ no workload on either side (see Gaps) · — no workload.\n\
         The number is the count of workloads.\n"
    );

    // One table per semantics.
    let mut failures = Vec::new();
    for semantics in SEMANTICS {
        let rows: Vec<&WorkloadResult> = run
            .workload
            .iter()
            .filter(|w| w.semantics == *semantics)
            .collect();
        if rows.is_empty() {
            continue;
        }
        let _ = writeln!(out, "## {}\n", semantics_label(semantics));
        let _ = writeln!(
            out,
            "| Workload | Operation | krust wall | krust CPU | krust peak | ref wall | ref CPU | ref peak | Speedup | Memory ratio | Δ wall | Δ peak |"
        );
        let _ = writeln!(out, "|:--|:--|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|");
        for row in rows {
            let name = format!("{} (`{}`)", row.title, row.id);
            let figures = headline(row.krust.as_ref(), &row.points, &row.reference.points);
            let size = figures
                .as_ref()
                .and_then(|(_, param)| *param)
                .map(|p| format!(", {}={p}", row.ladder_param.as_deref().unwrap_or("n")))
                .unwrap_or_default();
            let krust_cells = match (&row.status[..], &figures) {
                ("skipped", _) => [
                    format!("not run ({} tier)", row.tier),
                    String::new(),
                    String::new(),
                ],
                ("ok", Some((samples, _))) => [
                    format!("{}{size}", seconds(samples.wall())),
                    seconds(samples.cpu()),
                    mib(samples.peak()),
                ],
                (_, partial) => {
                    failures.push((row.id.clone(), row.detail.clone().unwrap_or_default()));
                    let marker = format!("FAILED [{}]", failures.len());
                    match partial {
                        Some((samples, _)) if !row.points.is_empty() => [
                            format!("{}{size}; {marker}", seconds(samples.wall())),
                            seconds(samples.cpu()),
                            mib(samples.peak()),
                        ],
                        _ => [marker, String::new(), String::new()],
                    }
                }
            };
            let param = figures.as_ref().and_then(|(_, p)| *p);
            let reference = reference_point(row, param);
            let (ref_cells, speedup, memory) = match reference_cell(row) {
                Some(text) => (
                    [text, String::new(), String::new()],
                    "—".to_owned(),
                    "—".to_owned(),
                ),
                None => match &reference {
                    Some(r) => {
                        let krust = figures.as_ref().map(|(s, _)| s);
                        (
                            [seconds(r.wall()), seconds(r.cpu()), mib(r.peak())],
                            ratio(divide(r.wall(), krust.and_then(Samples::wall))),
                            ratio(divide(krust.and_then(Samples::peak), r.peak())),
                        )
                    }
                    None => (
                        [
                            format!(
                                "no reference at {}",
                                param.map_or(String::new(), |p| p.to_string())
                            ),
                            String::new(),
                            String::new(),
                        ],
                        "—".to_owned(),
                        "—".to_owned(),
                    ),
                },
            };
            let (delta_wall, delta_peak) = match (figures.as_ref(), base.get(row.id.as_str())) {
                (Some((samples, param)), Some(previous)) => {
                    let previous_figures = match param {
                        None => previous.krust.clone(),
                        Some(param) => previous
                            .points
                            .iter()
                            .find(|p| p.param == *param && p.status == "ok")
                            .map(|p| p.samples.clone()),
                    };
                    match previous_figures {
                        Some(prev) => (
                            delta(samples.wall(), prev.wall()),
                            delta(samples.peak(), prev.peak()),
                        ),
                        None => ("—".to_owned(), "—".to_owned()),
                    }
                }
                _ => ("—".to_owned(), "—".to_owned()),
            };
            let _ = writeln!(
                out,
                "| {name} | {} | {} | {} | {} | {} | {} | {} | {speedup} | {memory} | {delta_wall} | {delta_peak} |",
                row.operation,
                krust_cells[0],
                krust_cells[1],
                krust_cells[2],
                ref_cells[0],
                ref_cells[1],
                ref_cells[2],
            );
        }
        let _ = writeln!(out);
    }

    // Ladders.
    let ladders: Vec<&WorkloadResult> = run
        .workload
        .iter()
        .filter(|w| !w.points.is_empty() || !w.reference.points.is_empty())
        .collect();
    if !ladders.is_empty() {
        let _ = writeln!(out, "## Scaling ladders\n");
        let _ = writeln!(
            out,
            "Growth exponent: the least-squares slope of log(wall) over log(size) for the largest four sizes of at least 0.05 s \
             (1 is linear, 2 quadratic); for peak memory, sizes of at least 64 MiB.\n"
        );
        let _ = writeln!(
            out,
            "| Workload | Sizes | krust wall per size | krust peak per size | Wall growth | Peak growth | ref wall per size | ref wall growth |"
        );
        let _ = writeln!(out, "|:--|:--|:--|:--|--:|--:|:--|--:|");
        for row in ladders {
            let sizes: Vec<String> = row.points.iter().map(|p| p.param.to_string()).collect();
            let walls: Vec<String> = row
                .points
                .iter()
                .map(|p| {
                    if p.status == "ok" {
                        seconds(p.samples.wall())
                    } else {
                        short_failure(&p.status)
                    }
                })
                .collect();
            let peaks: Vec<String> = row.points.iter().map(|p| mib(p.samples.peak())).collect();
            let (wall_growth, peak_growth) = ladder_growth(&row.points);
            let reference_walls: Vec<String> = row
                .reference
                .points
                .iter()
                .map(|p| {
                    format!(
                        "{}: {}",
                        p.param,
                        if p.status == "ok" {
                            seconds(p.samples.wall())
                        } else {
                            short_failure(&p.status)
                        }
                    )
                })
                .collect();
            let (reference_growth, _) = ladder_growth(&row.reference.points);
            let _ = writeln!(
                out,
                "| `{}` ({}) | {} | {} | {} | {} | {} | {} | {} |",
                row.id,
                row.ladder_param.as_deref().unwrap_or("n"),
                sizes.join(" / "),
                walls.join(" / "),
                peaks.join(" / "),
                exponent(wall_growth),
                exponent(peak_growth),
                if reference_walls.is_empty() {
                    reference_cell(row).unwrap_or_else(|| "—".to_owned())
                } else {
                    reference_walls.join(" / ")
                },
                exponent(reference_growth),
            );
        }
        let _ = writeln!(out);
    }

    if !run.gap.is_empty() {
        let _ = writeln!(out, "## Gaps\n");
        let mut gaps: Vec<_> = run.gap.iter().collect();
        gaps.sort_by_key(|g| {
            (
                SEMANTICS.iter().position(|s| *s == g.semantics),
                OPERATIONS.iter().position(|o| *o == g.operation),
            )
        });
        for gap in gaps {
            let _ = writeln!(
                out,
                "- {} {} (`{}`): {}",
                semantics_label(&gap.semantics),
                gap.operation,
                gap.reason,
                gap.note.trim()
            );
        }
        let _ = writeln!(out);
    }

    if !failures.is_empty() {
        let _ = writeln!(out, "## Failures\n");
        for (index, (id, detail)) in failures.iter().enumerate() {
            let _ = writeln!(out, "{}. `{id}`: {detail}", index + 1);
        }
        let _ = writeln!(out);
    }

    let _ = writeln!(out, "## Reference reasons\n");
    let _ = writeln!(
        out,
        "- `no-counterpart`: reference K has no comparable operation (for example krust's separate load or spec-compile).\n\
         - `missing-hook`: the reference backend lacks a hook the program needs.\n\
         - `ref-fails`: the reference reports an error on this input.\n\
         - `ref-timeout`: the reference does not finish within the workload's limits.\n\
         - `no-claims`: the semantics has no proof claims to prove.\n"
    );
    let notes: Vec<&WorkloadResult> = run
        .workload
        .iter()
        .filter(|w| w.reference.note.is_some() && w.reference.status != "failed")
        .collect();
    if !notes.is_empty() {
        let _ = writeln!(out, "Notes on the reference side:\n");
        for row in notes {
            let _ = writeln!(
                out,
                "- `{}`: {}",
                row.id,
                row.reference.note.as_deref().unwrap_or_default().trim()
            );
        }
        let _ = writeln!(out);
    }

    let _ = writeln!(out, "## What each workload measures\n");
    for row in &run.workload {
        let origin = row
            .origin
            .as_deref()
            .map(|o| format!(" Origin: {}.", o.trim().trim_end_matches('.')))
            .unwrap_or_default();
        let _ = writeln!(
            out,
            "- `{}` ({}, {}): {}{origin}",
            row.id,
            row.operation,
            row.tier,
            row.stresses.trim()
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn growth_of_a_quadratic_ladder_is_two() {
        let points: Vec<(f64, f64)> = [10.0, 100.0, 1000.0]
            .iter()
            .map(|x| (*x, x * x * 1e-4))
            .collect();
        let slope = growth(&points, 0.0).unwrap();
        assert!((slope - 2.0).abs() < 1e-9);
    }

    #[test]
    fn formats_are_fixed() {
        assert_eq!(seconds(Some(0.3411)), "0.341");
        assert_eq!(seconds(Some(46.06)), "46.1");
        assert_eq!(ratio(Some(10.61)), "10.6×");
        assert_eq!(ratio(Some(0.0397)), "0.04×");
        assert_eq!(delta(Some(1.2), Some(1.0)), "+20% ▲");
    }
}
