//! `kbench compare`: runs the krust side of the selected workloads with two binaries,
//! interleaved, checks that both produce the same output, and records the samples for the
//! comparison report (`compare_report.rs`). Reference K is never run.

use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::Read;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::measure::counter_files;
use crate::registry::{Engine, Ladder, Workload};
use crate::results::{Host, Samples};
use crate::runner::{Environment, PointRun, Runner};

pub const COMPARE_SCHEMA: &str = "kbench-compare/1";

/// Default timed runs per binary and point.
pub const DEFAULT_RUNS: u32 = 5;
/// Default minimum relevant change, as a fraction (3 %).
pub const DEFAULT_MIN_EFFECT: f64 = 0.03;
/// The marker a `measure` build of krust carries: the format name of its `KRUST_COUNTERS` dump.
const MEASURE_MARKER: &[u8] = b"krust-counters";
/// Outputs up to this size are normalized before hashing; larger ones are hashed as they are.
const NORMALIZE_LIMIT: u64 = 512 << 20;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Binary {
    pub path: String,
    pub sha256: String,
    pub prepared: String,
    /// Built with the `measure` feature (writes `KRUST_COUNTERS`).
    pub measure: bool,
}

/// One point (a plain workload, or one ladder value) measured with both binaries.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct PointComparison {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub param: Option<i64>,
    /// `ok`, or the side's first failure.
    pub base_status: String,
    pub candidate_status: String,
    /// `identical`, `differs`, `ignored` (the workload opts out), or `unchecked` (a side failed
    /// before both produced output).
    pub output: String,
    pub base: Samples,
    pub candidate: Samples,
    /// The first 16 hex digits of the SHA-256 of each timed run's normalized output.
    pub base_digests: Vec<String>,
    pub candidate_digests: Vec<String>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub base_counters: BTreeMap<String, u64>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub candidate_counters: BTreeMap<String, u64>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WorkloadComparison {
    pub id: String,
    pub semantics: String,
    pub operation: String,
    pub title: String,
    /// `ok`, `failed` (a run failed or its check did not pass), `mismatch` (the outputs
    /// differ), `error` (setup), or `skipped`.
    pub status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ladder_param: Option<String>,
    /// The registry's ladder values.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub ladder_values: Vec<i64>,
    /// The set's compare cap (`ladder_max`), when one applied.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ladder_cap: Option<i64>,
    /// Why the ladder ended before its last selected value.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stopped: Option<String>,
    /// The registry's `[workload.compare]` opt-out: what the output digest leaves out, and why.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ignored_output: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub point: Vec<PointComparison>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Comparison {
    pub schema: String,
    pub compare_id: String,
    pub started_at: String,
    pub finished_at: String,
    /// The selection as given: `set:NAME` and `only:PATTERN` entries.
    pub selection: Vec<String>,
    pub runs: u32,
    pub min_effect: f64,
    pub level: f64,
    pub full_ladders: bool,
    /// The k-rust checkout whose registry was used.
    pub commit: String,
    pub base: Binary,
    pub candidate: Binary,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub counters_base: Option<Binary>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub counters_candidate: Option<Binary>,
    pub method: String,
    pub host: Host,
    pub workload: Vec<WorkloadComparison>,
}

impl Comparison {
    pub fn load(path: &Path) -> Result<Comparison, String> {
        let text = fs::read_to_string(path)
            .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
        let comparison: Comparison =
            toml::from_str(&text).map_err(|error| format!("{}: {error}", path.display()))?;
        if comparison.schema != COMPARE_SCHEMA {
            return Err(format!(
                "{}: unsupported schema {}",
                path.display(),
                comparison.schema
            ));
        }
        Ok(comparison)
    }

    pub fn save(&self, path: &Path) -> Result<(), String> {
        let text = toml::to_string(self).map_err(|error| error.to_string())?;
        fs::write(path, text).map_err(|error| format!("cannot write {}: {error}", path.display()))
    }

    /// Keeps the first `runs` timed runs of each side of every point.
    pub fn truncate_runs(&mut self, runs: usize) {
        self.runs = self.runs.min(u32::try_from(runs).unwrap_or(u32::MAX));
        for workload in &mut self.workload {
            for point in &mut workload.point {
                for samples in [&mut point.base, &mut point.candidate] {
                    samples.wall_seconds.truncate(runs);
                    samples.cpu_seconds.truncate(runs);
                    samples.peak_bytes.truncate(runs);
                }
                point.base_digests.truncate(runs);
                point.candidate_digests.truncate(runs);
            }
        }
    }

    /// Whether every selected workload ran, passed its check, and gave identical output.
    pub fn passed(&self) -> bool {
        self.workload
            .iter()
            .all(|w| w.status == "ok" || w.status == "skipped")
    }
}

/// Whether a krust binary was built with the `measure` feature.
pub fn is_measure_build(path: &Path) -> Result<bool, String> {
    let mut file =
        File::open(path).map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let mut chunk = vec![0u8; 1 << 20];
    let mut window: Vec<u8> = Vec::new();
    loop {
        let read = file.read(&mut chunk).map_err(|e| e.to_string())?;
        if read == 0 {
            return Ok(false);
        }
        window.extend_from_slice(&chunk[..read]);
        if window
            .windows(MEASURE_MARKER.len())
            .any(|w| w == MEASURE_MARKER)
        {
            return Ok(true);
        }
        let keep = MEASURE_MARKER.len() - 1;
        window.drain(..window.len().saturating_sub(keep));
    }
}

pub fn binary(environment: &Environment) -> Result<Binary, String> {
    Ok(Binary {
        path: environment.krust.display().to_string(),
        sha256: environment.krust_sha256.clone(),
        prepared: environment.prepared_krust.display().to_string(),
        measure: is_measure_build(&environment.krust)?,
    })
}

/// The ladder values a compare runs: every value up to the cap, or all with `full`.
pub fn ladder_values(ladder: &Ladder, cap: Option<i64>, full: bool) -> Vec<i64> {
    ladder
        .values
        .iter()
        .copied()
        .filter(|value| full || cap.is_none_or(|cap| *value <= cap))
        .collect()
}

/// Why a ladder stops after a value, if either side's median wall exceeded `stop_seconds`:
/// both sides then stop, so they are compared on the same values.
pub fn stop_reason(
    param: &str,
    value: i64,
    base_wall: Option<f64>,
    candidate_wall: Option<f64>,
    stop_seconds: f64,
) -> Option<String> {
    let slow: Vec<String> = [("base", base_wall), ("candidate", candidate_wall)]
        .into_iter()
        .filter_map(|(side, wall)| {
            wall.filter(|w| *w > stop_seconds)
                .map(|w| format!("{side} {w:.1} s"))
        })
        .collect();
    (!slow.is_empty()).then(|| {
        format!(
            "stopped after {param} = {value}: median wall above stop_seconds = {stop_seconds} ({}); larger values not run for either binary",
            slow.join(", ")
        )
    })
}

/// Whether the measured side runs the krust binary under comparison.
pub fn runs_krust(workload: &Workload) -> bool {
    match workload.krust.engine.unwrap_or(Engine::Krust) {
        Engine::Krust => true,
        Engine::Reference => false,
        Engine::Command => workload
            .krust
            .invocations()
            .iter()
            .flatten()
            .any(|arg| arg.contains("${krust}")),
    }
}

/// SHA-256 (first 16 hex digits) of a run's output: its standard output, then each file its
/// check names, with each binary's own paths (its prepared root and its path) replaced by
/// placeholders so that the two binaries' outputs compare.
pub fn output_digest(
    stdout: Option<&Path>,
    files: &[PathBuf],
    replacements: &[(String, &str)],
) -> Result<String, String> {
    let mut hasher = Sha256::new();
    let mut add = |label: &str, path: &Path| -> Result<(), String> {
        hasher.update(label.as_bytes());
        hasher.update([0]);
        let length = fs::metadata(path).map(|m| m.len()).unwrap_or(0);
        if length <= NORMALIZE_LIMIT {
            let bytes = fs::read(path).unwrap_or_default();
            let mut text = bytes;
            for (from, to) in replacements {
                if !from.is_empty() {
                    text = replace_bytes(&text, from.as_bytes(), to.as_bytes());
                }
            }
            hasher.update(&text);
        } else {
            let mut file = File::open(path)
                .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
            let mut chunk = vec![0u8; 1 << 20];
            loop {
                let read = file.read(&mut chunk).map_err(|e| e.to_string())?;
                if read == 0 {
                    break;
                }
                hasher.update(&chunk[..read]);
            }
        }
        hasher.update([0]);
        Ok(())
    };
    if let Some(stdout) = stdout {
        add("stdout", stdout)?;
    }
    for (index, file) in files.iter().enumerate() {
        add(&format!("file {index}"), file)?;
    }
    let digest = hasher.finalize();
    Ok(digest[..8].iter().fold(String::new(), |mut out, b| {
        use std::fmt::Write;
        let _ = write!(out, "{b:02x}");
        out
    }))
}

fn replace_bytes(text: &[u8], from: &[u8], to: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(text.len());
    let mut index = 0;
    while index < text.len() {
        if text[index..].starts_with(from) {
            out.extend_from_slice(to);
            index += from.len();
        } else {
            out.push(text[index]);
            index += 1;
        }
    }
    out
}

/// Reads and sums the `KRUST_COUNTERS` files of one run's steps.
pub fn read_counters(files: &[PathBuf]) -> Result<BTreeMap<String, u64>, String> {
    let mut total: BTreeMap<String, u64> = BTreeMap::new();
    let mut found = false;
    for path in files {
        let Ok(text) = fs::read_to_string(path) else {
            continue;
        };
        found = true;
        let document: serde_json::Value =
            serde_json::from_str(&text).map_err(|error| format!("{}: {error}", path.display()))?;
        let counters = document
            .get("counters")
            .and_then(serde_json::Value::as_object)
            .ok_or_else(|| format!("{}: no counters object", path.display()))?;
        for (name, value) in counters {
            let value = value
                .as_u64()
                .ok_or_else(|| format!("{}: counter {name} is not an integer", path.display()))?;
            *total.entry(name.clone()).or_default() += value;
        }
    }
    if found {
        Ok(total)
    } else {
        Err("no KRUST_COUNTERS file was written (is the binary a measure build?)".to_owned())
    }
}

/// The counters of the base and the candidate run.
type CounterPair = (BTreeMap<String, u64>, BTreeMap<String, u64>);

/// The two runners of a side pair: timed runs, and counter runs (possibly other binaries).
pub struct Sides<'a> {
    pub base: Runner<'a>,
    pub candidate: Runner<'a>,
    pub counters: Option<(Runner<'a>, Runner<'a>)>,
}

pub struct Options {
    pub runs: u32,
    pub full_ladders: bool,
}

fn sanitize(id: &str) -> String {
    id.replace('/', "__")
}

/// The base and candidate invocations of one point. Both use the same `${run}` and `${input}`
/// paths, so outputs that mention them still compare.
struct Pair {
    base: PointRun,
    candidate: PointRun,
}

fn replacements(environment: &Environment) -> Vec<(String, &'static str)> {
    vec![
        (
            environment.prepared_krust.display().to_string(),
            "${prepared}",
        ),
        (environment.krust.display().to_string(), "${krust}"),
    ]
}

/// The parts of a run's output that are compared: standard output and the check files, less
/// what the workload's `[workload.compare]` opts out of.
fn compared_output(point: &PointRun, workload: &Workload) -> (Option<PathBuf>, Vec<PathBuf>) {
    let opt_out = workload.compare.as_ref();
    let stdout = point
        .invocation
        .stdout
        .clone()
        .filter(|_| !opt_out.is_some_and(|o| o.ignore_stdout));
    let files = point
        .check
        .files
        .iter()
        .filter(|file| !opt_out.is_some_and(|o| o.ignore_files.contains(file)))
        .filter_map(|file| point.vars.expand(file).ok())
        .map(PathBuf::from)
        .collect();
    (stdout, files)
}

#[allow(clippy::too_many_arguments)]
fn point_pair(
    base: &Runner,
    candidate: &Runner,
    workload: &Workload,
    directory: &Path,
    run_dir: &Path,
    point_vars: &[(String, String)],
    params: &BTreeMap<String, i64>,
    label: &str,
) -> Result<Pair, String> {
    let make = |runner: &Runner, side_label: &str| -> Result<PointRun, String> {
        let engine = workload.krust.engine.unwrap_or(Engine::Krust);
        let mut vars = runner.side_vars(engine, run_dir);
        for (name, value) in point_vars {
            vars.set(name, value.clone());
        }
        let side_directory = directory.join(format!("{label}{side_label}"));
        fs::create_dir_all(&side_directory).map_err(|e| e.to_string())?;
        runner.point_run(
            workload,
            &workload.krust,
            engine,
            &vars,
            &side_directory,
            params,
            true,
        )
    };
    Ok(Pair {
        base: make(base, "base")?,
        candidate: make(candidate, "candidate")?,
    })
}

/// Measures one workload with both binaries.
pub fn compare_workload(
    sides: &mut Sides,
    workload: &Workload,
    cap: Option<i64>,
    options: &Options,
    work: &Path,
) -> WorkloadComparison {
    let mut result = WorkloadComparison {
        id: workload.id.clone(),
        semantics: workload.semantics.clone(),
        operation: workload.operation.clone(),
        title: workload.title.clone(),
        status: "ok".to_owned(),
        detail: None,
        ladder_param: workload.ladder.as_ref().map(|l| l.param.clone()),
        ladder_values: workload
            .ladder
            .as_ref()
            .map(|l| l.values.clone())
            .unwrap_or_default(),
        ladder_cap: if options.full_ladders { None } else { cap },
        stopped: None,
        ignored_output: workload.compare.as_ref().map(|opt_out| {
            let mut parts = Vec::new();
            if opt_out.ignore_stdout {
                parts.push("standard output".to_owned());
            }
            parts.extend(opt_out.ignore_files.iter().map(|f| format!("`{f}`")));
            format!(
                "{} not compared: {}",
                parts.join(", "),
                opt_out.reason.trim()
            )
        }),
        point: Vec::new(),
    };
    if !runs_krust(workload) {
        result.status = "skipped".to_owned();
        result.detail =
            Some("its measured command does not run the krust binary under comparison".to_owned());
        return result;
    }
    if let Err(error) = sides.base.check_pins(workload) {
        result.status = "error".to_owned();
        result.detail = Some(error);
        return result;
    }
    if let Err(error) = compare_points(sides, workload, cap, options, work, &mut result) {
        result.status = "error".to_owned();
        result.detail = Some(error);
    }
    result
}

fn compare_points(
    sides: &mut Sides,
    workload: &Workload,
    cap: Option<i64>,
    options: &Options,
    work: &Path,
    result: &mut WorkloadComparison,
) -> Result<(), String> {
    let directory = work.join(sanitize(&workload.id));
    fs::create_dir_all(&directory).map_err(|e| e.to_string())?;
    let run_dir = directory.join("run");
    let engine = workload.krust.engine.unwrap_or(Engine::Krust);
    let values: Vec<Option<i64>> = match &workload.ladder {
        None => vec![None],
        Some(ladder) => ladder_values(ladder, cap, options.full_ladders)
            .into_iter()
            .map(Some)
            .collect(),
    };
    for value in values {
        let mut point_vars: Vec<(String, String)> = Vec::new();
        let mut params = BTreeMap::new();
        let mut label = String::new();
        if let (Some(ladder), Some(value)) = (&workload.ladder, value) {
            let input = directory.join(format!("input-{value}"));
            let mut vars = sides.base.side_vars(engine, &run_dir);
            vars.set(&ladder.param, value.to_string());
            vars.set("input", input.display().to_string());
            sides.base.write_ladder_input(ladder, &vars, &input)?;
            point_vars.push((ladder.param.clone(), value.to_string()));
            point_vars.push(("input".to_owned(), input.display().to_string()));
            params.insert(ladder.param.clone(), value);
            label = format!("{value}-");
            eprintln!("  {} = {value}", ladder.param);
        }
        sides
            .base
            .prepare_side(&workload.krust, engine, &point_vars)?;
        sides
            .candidate
            .prepare_side(&workload.krust, engine, &point_vars)?;
        let pair = point_pair(
            &sides.base,
            &sides.candidate,
            workload,
            &directory,
            &run_dir,
            &point_vars,
            &params,
            &label,
        )?;
        let mut point = PointComparison {
            param: value,
            base_status: "ok".to_owned(),
            candidate_status: "ok".to_owned(),
            ..PointComparison::default()
        };
        let base_replacements = replacements(sides.base.environment);
        let candidate_replacements = replacements(sides.candidate.environment);
        let warmup = if value.is_none() {
            workload.warmup()
        } else {
            0
        };
        let mut failed = false;
        'runs: for index in 0..warmup + options.runs {
            // A B, then B A: alternating the order cancels a steady drift in host load.
            let order: [bool; 2] = if index % 2 == 0 {
                [false, true]
            } else {
                [true, false]
            };
            for is_candidate in order {
                let (runner, run, replacements) = if is_candidate {
                    (
                        &mut sides.candidate,
                        &pair.candidate,
                        &candidate_replacements,
                    )
                } else {
                    (&mut sides.base, &pair.base, &base_replacements)
                };
                let (sample, verdict) = runner.run_point(run)?;
                if let Err(failure) = verdict {
                    if is_candidate {
                        point.candidate_status = failure;
                    } else {
                        point.base_status = failure;
                    }
                    failed = true;
                    break 'runs;
                }
                if index < warmup {
                    continue;
                }
                let (stdout, files) = compared_output(run, workload);
                let digest = output_digest(stdout.as_deref(), &files, replacements)?;
                if is_candidate {
                    point.candidate.push(&sample);
                    point.candidate_digests.push(digest);
                } else {
                    point.base.push(&sample);
                    point.base_digests.push(digest);
                }
            }
        }
        point.output =
            if failed {
                "unchecked".to_owned()
            } else if workload.compare.as_ref().is_some_and(|o| {
                o.ignore_stdout && o.ignore_files.len() == pair.base.check.files.len()
            }) {
                "ignored".to_owned()
            } else if point
                .base_digests
                .iter()
                .chain(&point.candidate_digests)
                .all(|d| Some(d) == point.base_digests.first())
            {
                "identical".to_owned()
            } else {
                "differs".to_owned()
            };
        if !failed && let Some((base_counter, candidate_counter)) = &mut sides.counters {
            let counted = count_pair(
                base_counter,
                candidate_counter,
                workload,
                &directory,
                &run_dir,
                &point_vars,
                &params,
                &label,
            );
            match counted {
                Ok((base, candidate)) => {
                    point.base_counters = base;
                    point.candidate_counters = candidate;
                }
                Err(error) => {
                    result.status = "failed".to_owned();
                    result.detail = Some(format!("counter run: {error}"));
                    failed = true;
                }
            }
        }
        pair.base.clean_up();
        pair.candidate.clean_up();
        let summary = summarize(&point);
        eprintln!("    {summary}");
        let differs = point.output == "differs";
        let walls = (point.base.wall(), point.candidate.wall());
        result.point.push(point);
        if failed {
            if result.status == "ok" {
                result.status = "failed".to_owned();
                let last = result.point.last().expect("pushed");
                let side = if last.base_status == "ok" {
                    format!("candidate: {}", last.candidate_status)
                } else {
                    format!("base: {}", last.base_status)
                };
                result.detail = Some(match value {
                    Some(v) => format!(
                        "{} = {v}: {side}",
                        workload.ladder.as_ref().map_or("n", |l| l.param.as_str())
                    ),
                    None => side,
                });
            }
            break;
        }
        if differs && result.status == "ok" {
            result.status = "mismatch".to_owned();
            result.detail = Some(match value {
                Some(v) => format!(
                    "{} = {v}: the base and candidate outputs differ",
                    workload.ladder.as_ref().map_or("n", |l| l.param.as_str())
                ),
                None => "the base and candidate outputs differ".to_owned(),
            });
        }
        if let (Some(ladder), Some(value)) = (&workload.ladder, value)
            && let Some(reason) = stop_reason(
                &ladder.param,
                value,
                walls.0,
                walls.1,
                ladder.stop_seconds.unwrap_or(120.0),
            )
        {
            result.stopped = Some(reason);
            break;
        }
    }
    Ok(())
}

fn summarize(point: &PointComparison) -> String {
    if point.base_status != "ok" || point.candidate_status != "ok" {
        return format!(
            "FAILED: base {}, candidate {}",
            point.base_status, point.candidate_status
        );
    }
    let cpu = |s: &Samples| s.cpu().map_or("—".to_owned(), |v| format!("{v:.3}"));
    format!(
        "CPU base {} s, candidate {} s; output {}",
        cpu(&point.base),
        cpu(&point.candidate),
        point.output
    )
}

#[allow(clippy::too_many_arguments)]
fn count_pair<'a>(
    base: &mut Runner<'a>,
    candidate: &mut Runner<'a>,
    workload: &Workload,
    directory: &Path,
    run_dir: &Path,
    point_vars: &[(String, String)],
    params: &BTreeMap<String, i64>,
    label: &str,
) -> Result<CounterPair, String> {
    let engine = workload.krust.engine.unwrap_or(Engine::Krust);
    base.prepare_side(&workload.krust, engine, point_vars)?;
    candidate.prepare_side(&workload.krust, engine, point_vars)?;
    let label = format!("{label}counters-");
    let mut pair = point_pair(
        base, candidate, workload, directory, run_dir, point_vars, params, &label,
    )?;
    let mut counted = Vec::new();
    for (runner, run, side) in [
        (base, &mut pair.base, "base"),
        (candidate, &mut pair.candidate, "candidate"),
    ] {
        let prefix = run.invocation.stderr.with_file_name("counters");
        let files = counter_files(&prefix, run.invocation.steps.len());
        for file in &files {
            let _ = fs::remove_file(file);
        }
        run.invocation.counters = Some(prefix);
        let (_, verdict) = runner.run_point(run)?;
        verdict.map_err(|failure| format!("{side}: {failure}"))?;
        counted.push(read_counters(&files).map_err(|error| format!("{side}: {error}"))?);
        run.clean_up();
    }
    let candidate_counters = counted.pop().expect("two sides");
    let base_counters = counted.pop().expect("two sides");
    Ok((base_counters, candidate_counters))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ladder(values: &[i64]) -> Ladder {
        Ladder {
            param: "n".to_owned(),
            values: values.to_vec(),
            stop_seconds: None,
            input: Some(String::new()),
            generator: None,
        }
    }

    #[test]
    fn a_cap_truncates_the_ladder_unless_full_ladders() {
        let ladder = ladder(&[125, 250, 500, 1000, 2000]);
        assert_eq!(
            ladder_values(&ladder, Some(1000), false),
            vec![125, 250, 500, 1000]
        );
        assert_eq!(ladder_values(&ladder, Some(1000), true).len(), 5);
        assert_eq!(ladder_values(&ladder, None, false).len(), 5);
    }

    #[test]
    fn either_side_above_stop_seconds_stops_both() {
        assert!(stop_reason("n", 500, Some(10.0), Some(130.0), 120.0).is_some());
        assert!(stop_reason("n", 500, Some(130.0), Some(10.0), 120.0).is_some());
        let reason = stop_reason("n", 500, Some(121.0), Some(10.0), 120.0).unwrap();
        assert!(reason.contains("base 121.0 s") && reason.contains("n = 500"));
        assert!(stop_reason("n", 500, Some(10.0), Some(119.0), 120.0).is_none());
        assert!(stop_reason("n", 500, None, None, 120.0).is_none());
    }

    #[test]
    fn digests_ignore_each_binarys_own_paths() {
        let dir = std::env::temp_dir().join(format!("kbench-compare-{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let a = dir.join("a");
        let b = dir.join("b");
        fs::write(&a, "result in /p/krust-aaaa/def\n").unwrap();
        fs::write(&b, "result in /p/krust-bbbb/def\n").unwrap();
        let da = output_digest(
            Some(&a),
            &[],
            &[("/p/krust-aaaa".to_owned(), "${prepared}")],
        )
        .unwrap();
        let db = output_digest(
            Some(&b),
            &[],
            &[("/p/krust-bbbb".to_owned(), "${prepared}")],
        )
        .unwrap();
        assert_eq!(da, db);
        let raw = output_digest(Some(&b), &[], &[]).unwrap();
        assert_ne!(da, raw);
        // A check file is part of the output.
        let with_file = output_digest(Some(&a), std::slice::from_ref(&b), &[]).unwrap();
        assert_ne!(with_file, output_digest(Some(&a), &[], &[]).unwrap());
        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn counters_of_several_steps_add_up() {
        let dir = std::env::temp_dir().join(format!("kbench-counters-{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let files = counter_files(&dir.join("counters"), 3);
        let document = |steps: u64| {
            format!(
                "{{\n  \"format\": \"krust-counters\",\n  \"version\": 19,\n  \"counters\": {{\n    \"rewrite.steps\": {steps},\n    \"allocation.count\": 7\n  }}\n}}\n"
            )
        };
        fs::write(&files[0], document(5)).unwrap();
        fs::write(&files[2], document(6)).unwrap();
        let total = read_counters(&files).unwrap();
        assert_eq!(total["rewrite.steps"], 11);
        assert_eq!(total["allocation.count"], 14);
        fs::remove_dir_all(&dir).unwrap();
        assert!(read_counters(&files).is_err());
    }

    #[test]
    fn the_measure_marker_is_found_across_chunks() {
        let dir = std::env::temp_dir().join(format!("kbench-marker-{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let path = dir.join("bin");
        let mut bytes = vec![0u8; (1 << 20) - 5];
        bytes.extend_from_slice(b"krust-counters");
        fs::write(&path, &bytes).unwrap();
        assert!(is_measure_build(&path).unwrap());
        fs::write(&path, vec![0u8; 3 << 20]).unwrap();
        assert!(!is_measure_build(&path).unwrap());
        fs::remove_dir_all(&dir).unwrap();
    }
}
