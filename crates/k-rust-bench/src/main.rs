//! `kbench`: runs the krust benchmark registry (`benchmarks/registry/`) and renders the
//! fixed-format report against cached reference K measurements (`benchmarks/reference.toml`).
//! See `benchmarks/README.md`.

mod check;
mod expand;
mod measure;
mod registry;
mod report;
mod results;
mod runner;

use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::{SystemTime, UNIX_EPOCH};

use clap::{Parser, Subcommand};

use crate::registry::{Engine, ReferenceStatus, Registry, Tier, Workload};
use crate::results::{
    Host, Measurement, Point, RESULTS_SCHEMA, ReferenceCache, ReferenceResult, Run, WorkloadResult,
};
use crate::runner::{Environment, REFERENCE_K_OPTS, Runner, git, reference_key};

#[derive(Parser)]
#[command(
    name = "kbench",
    about = "Benchmark krust against cached reference K measurements"
)]
struct Cli {
    /// The k-rust checkout (default: the checkout containing the current directory).
    #[arg(long, global = true)]
    workspace: Option<PathBuf>,
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// List the registered workloads.
    List {
        #[arg(long, default_value = "heavy")]
        tier: String,
    },
    /// Check the registry and the reference cache.
    Validate,
    /// Measure krust on the selected workloads and print the report.
    Run {
        /// quick, standard (quick + standard), or heavy (everything).
        #[arg(long, default_value = "standard")]
        tier: String,
        /// Only workloads whose id starts with one of these prefixes (`*` matches anything).
        #[arg(long)]
        only: Vec<String>,
        /// The krust binary (default: target/release/krust, or KRUST_BIN).
        #[arg(long)]
        krust: Option<PathBuf>,
        /// The run directory (default: target/kbench/runs/<run id>).
        #[arg(long)]
        output: Option<PathBuf>,
        /// Where results and reports are kept (default: <main checkout>/draft-personal/benchmarks).
        #[arg(long)]
        history: Option<PathBuf>,
        /// Do not copy the results into the history directory.
        #[arg(long)]
        no_history: bool,
        /// Compare with this results.toml instead of the latest history run.
        #[arg(long)]
        baseline: Option<PathBuf>,
        /// Print the resolved commands without running anything.
        #[arg(long)]
        dry_run: bool,
        /// Measure without a delegated cgroup scope (peak memory unknown).
        #[arg(long)]
        no_cgroup: bool,
    },
    /// Measure reference K once for paired workloads that have no cached measurement.
    Reference {
        #[arg(long, default_value = "standard")]
        tier: String,
        #[arg(long)]
        only: Vec<String>,
        /// Re-measure even when a measurement with the same key is cached.
        #[arg(long)]
        force: bool,
        #[arg(long)]
        dry_run: bool,
        #[arg(long)]
        no_cgroup: bool,
    },
    /// Print the reference cache key of a paired workload.
    Key { id: String },
    /// Render the report of a results.toml.
    Report {
        results: PathBuf,
        #[arg(long)]
        baseline: Option<PathBuf>,
    },
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match execute(cli) {
        Ok(code) => code,
        Err(error) => {
            eprintln!("kbench: {error}");
            ExitCode::from(2)
        }
    }
}

fn workspace_root(explicit: Option<PathBuf>) -> Result<PathBuf, String> {
    if let Some(path) = explicit {
        return Ok(path);
    }
    let current = std::env::current_dir().map_err(|e| e.to_string())?;
    git(&current, &["rev-parse", "--show-toplevel"])
        .map(PathBuf::from)
        .ok_or_else(|| "not inside a git checkout; pass --workspace".to_owned())
}

fn parse_tier(text: &str) -> Result<Tier, String> {
    Tier::parse(text).ok_or_else(|| format!("unknown tier {text} (quick, standard, heavy)"))
}

fn selected(workload: &Workload, tier: Tier, only: &[String]) -> bool {
    workload.tier <= tier
        && (only.is_empty() || only.iter().any(|pattern| matches(pattern, &workload.id)))
}

/// A prefix match where `*` matches any run of characters.
fn matches(pattern: &str, id: &str) -> bool {
    fn go(pattern: &[u8], text: &[u8]) -> bool {
        match pattern.split_first() {
            None => true,
            Some((b'*', rest)) => (0..=text.len()).any(|i| go(rest, &text[i..])),
            Some((c, rest)) => text
                .split_first()
                .is_some_and(|(t, tail)| t == c && go(rest, tail)),
        }
    }
    go(pattern.as_bytes(), id.as_bytes())
}

/// Re-runs this command inside a delegated user systemd scope so runs can be measured as
/// cgroups; returns `None` when that is not possible (the caller then measures with rusage).
fn reexec_in_scope() -> Option<ExitCode> {
    if std::env::var_os(measure::SCOPE_ENV).is_some() || !measure::scope_available() {
        return None;
    }
    let exe = std::env::current_exe().ok()?;
    let mut command = Command::new("systemd-run");
    command.args(["--user", "--scope", "--quiet", "-p", "Delegate=yes"]);
    for property in measure::inherited_scope_properties() {
        command.args(["-p", &property]);
    }
    command
        .arg("--")
        .arg(exe)
        .args(std::env::args_os().skip(1))
        .env(measure::SCOPE_ENV, "1");
    let status = command.status().ok()?;
    Some(ExitCode::from(
        u8::try_from(status.code().unwrap_or(2)).unwrap_or(2),
    ))
}

pub fn utc_now() -> (String, String) {
    let seconds = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_secs());
    let days = i64::try_from(seconds / 86_400).unwrap_or(0);
    let rem = seconds % 86_400;
    // Civil date from days since 1970-01-01 (Howard Hinnant's algorithm).
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = yoe + era * 400 + i64::from(month <= 2);
    let (h, m, s) = (rem / 3600, rem % 3600 / 60, rem % 60);
    (
        format!("{year:04}-{month:02}-{day:02}T{h:02}:{m:02}:{s:02}Z"),
        format!("{year:04}{month:02}{day:02}T{h:02}{m:02}{s:02}Z"),
    )
}

fn read_trimmed(path: &str) -> String {
    std::fs::read_to_string(path)
        .map(|s| s.trim().to_owned())
        .unwrap_or_default()
}

fn load_average() -> String {
    read_trimmed("/proc/loadavg")
        .split_whitespace()
        .take(3)
        .collect::<Vec<_>>()
        .join(" ")
}

fn host() -> Host {
    let memory_kib = read_trimmed("/proc/meminfo")
        .lines()
        .find_map(|line| line.strip_prefix("MemTotal:"))
        .and_then(|rest| rest.split_whitespace().next()?.parse::<u64>().ok())
        .unwrap_or(0);
    Host {
        hostname: read_trimmed("/proc/sys/kernel/hostname"),
        kernel: read_trimmed("/proc/sys/kernel/osrelease"),
        cpus: std::thread::available_parallelism().map_or(0, std::num::NonZero::get),
        memory_bytes: memory_kib * 1024,
        load_before: load_average(),
        load_after: String::new(),
    }
}

fn history_root(workspace: &Path) -> PathBuf {
    let common = git(
        workspace,
        &["rev-parse", "--path-format=absolute", "--git-common-dir"],
    );
    let main = common
        .as_deref()
        .map(Path::new)
        .and_then(Path::parent)
        .map_or_else(|| workspace.to_path_buf(), Path::to_path_buf);
    main.join("draft-personal/benchmarks")
}

/// The latest history run other than `current`, preferring one of the same tier.
fn latest_baseline(history: &Path, current: &str, tier: &str) -> Option<Run> {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(history)
        .ok()?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.join("results.toml").exists())
        .filter(|path| path.file_name().is_some_and(|name| name != current))
        .collect();
    entries.sort();
    let runs: Vec<Run> = entries
        .iter()
        .rev()
        .filter_map(|path| Run::load(&path.join("results.toml")).ok())
        .collect();
    runs.iter()
        .find(|run| run.tier == tier && run.filter.is_empty())
        .or_else(|| runs.first())
        .cloned()
}

/// The reference side of a workload's result, from the cache.
fn reference_result(
    environment: &Environment,
    registry: &Registry,
    cache: &ReferenceCache,
    workload: &Workload,
) -> ReferenceResult {
    let Some(reference) = &workload.reference else {
        return ReferenceResult {
            status: "untested".to_owned(),
            ..ReferenceResult::default()
        };
    };
    let mut result = ReferenceResult {
        status: String::new(),
        reason: reference.reason.clone(),
        note: reference.note.clone(),
        backend: reference.backend.clone(),
        ..ReferenceResult::default()
    };
    match reference.status {
        ReferenceStatus::Unsupported => result.status = "unsupported".to_owned(),
        ReferenceStatus::Untested => result.status = "untested".to_owned(),
        ReferenceStatus::Paired => {
            let key = match reference_key(environment, registry, workload, &reference.side()) {
                Ok(key) => key,
                Err(error) => {
                    result.status = "failed".to_owned();
                    result.note = Some(error);
                    return result;
                }
            };
            let params: Vec<Option<i64>> = match &workload.ladder {
                None => vec![None],
                Some(ladder) => ladder.values.iter().copied().map(Some).collect(),
            };
            let found: Vec<&Measurement> = params
                .iter()
                .filter_map(|p| cache.find(&workload.id, *p))
                .collect();
            if found.is_empty() {
                result.status = "missing".to_owned();
            } else if found.iter().any(|m| m.key != key) {
                result.status = "stale".to_owned();
            } else if workload.ladder.is_none() && found[0].outcome != "ok" {
                result.status = "failed".to_owned();
                result.note = Some(found[0].outcome.clone());
                result.measured_at = Some(found[0].measured_at.clone());
            } else {
                result.status = "cached".to_owned();
                result.measured_at = Some(found[0].measured_at.clone());
                if workload.ladder.is_none() {
                    result.samples = Some(found[0].samples.clone());
                } else {
                    result.points = found
                        .iter()
                        .map(|m| Point {
                            param: m.param.unwrap_or_default(),
                            status: m.outcome.clone(),
                            samples: m.samples.clone(),
                        })
                        .collect();
                }
            }
        }
    }
    result
}

fn skeleton(workload: &Workload, status: &str, reference: ReferenceResult) -> WorkloadResult {
    WorkloadResult {
        id: workload.id.clone(),
        semantics: workload.semantics.clone(),
        operation: workload.operation.clone(),
        title: workload.title.clone(),
        stresses: workload.stresses.clone(),
        tier: workload.tier.name().to_owned(),
        origin: workload.origin.clone(),
        status: status.to_owned(),
        detail: None,
        ladder_param: workload.ladder.as_ref().map(|l| l.param.clone()),
        krust: None,
        points: Vec::new(),
        reference,
    }
}

fn execute(cli: Cli) -> Result<ExitCode, String> {
    let workspace = workspace_root(cli.workspace)?;
    let registry_dir = workspace.join("benchmarks/registry");
    let cache_path = workspace.join("benchmarks/reference.toml");
    match cli.command {
        Commands::List { tier } => {
            let tier = parse_tier(&tier)?;
            let registry = Registry::load(&registry_dir)?;
            for workload in registry.workloads.iter().filter(|w| w.tier <= tier) {
                let reference =
                    workload
                        .reference
                        .as_ref()
                        .map_or("—".to_owned(), |r| match r.status {
                            ReferenceStatus::Paired => "paired".to_owned(),
                            ReferenceStatus::Unsupported => {
                                format!("unsupported: {}", r.reason.as_deref().unwrap_or(""))
                            }
                            ReferenceStatus::Untested => "untested".to_owned(),
                        });
                println!(
                    "{:<44} {:<9} {:<13} {:<26} {}",
                    workload.id, workload.tier, workload.operation, reference, workload.title
                );
            }
            Ok(ExitCode::SUCCESS)
        }
        Commands::Validate => {
            let registry = Registry::load(&registry_dir)?;
            let cache = ReferenceCache::load(&cache_path)?;
            let environment = Environment::discover(&workspace, None)?;
            let mut problems = 0;
            for measurement in &cache.measurement {
                match registry
                    .workloads
                    .iter()
                    .find(|w| w.id == measurement.workload)
                {
                    None => {
                        println!("cache entry for unknown workload {}", measurement.workload);
                        problems += 1;
                    }
                    Some(workload) => {
                        let current = workload
                            .reference
                            .as_ref()
                            .filter(|r| r.status == ReferenceStatus::Paired)
                            .map(|r| reference_key(&environment, &registry, workload, &r.side()));
                        if !matches!(current, Some(Ok(ref key)) if *key == measurement.key) {
                            println!(
                                "stale cache entry for {} (its command, options, or pins changed)",
                                measurement.workload
                            );
                            problems += 1;
                        }
                    }
                }
            }
            let count = |status: ReferenceStatus| {
                registry
                    .workloads
                    .iter()
                    .filter(|w| w.reference.as_ref().is_some_and(|r| r.status == status))
                    .count()
            };
            println!(
                "{} workloads ({} paired, {} unsupported, {} untested), {} prepare steps, {} cached reference measurements",
                registry.workloads.len(),
                count(ReferenceStatus::Paired),
                count(ReferenceStatus::Unsupported),
                count(ReferenceStatus::Untested),
                registry.prepare.len(),
                cache.measurement.len()
            );
            Ok(if problems == 0 {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            })
        }
        Commands::Key { id } => {
            let registry = Registry::load(&registry_dir)?;
            let environment = Environment::discover(&workspace, None)?;
            let workload = registry
                .workloads
                .iter()
                .find(|w| w.id == id)
                .ok_or_else(|| format!("no workload {id}"))?;
            let reference = workload
                .reference
                .as_ref()
                .filter(|r| r.status == ReferenceStatus::Paired)
                .ok_or_else(|| format!("{id} is not paired with reference K"))?;
            println!(
                "{}",
                reference_key(&environment, &registry, workload, &reference.side())?
            );
            Ok(ExitCode::SUCCESS)
        }
        Commands::Report { results, baseline } => {
            let run = Run::load(&results)?;
            let baseline = baseline.map(|path| Run::load(&path)).transpose()?;
            print!("{}", report::render(&run, baseline.as_ref()));
            Ok(ExitCode::SUCCESS)
        }
        Commands::Run {
            tier,
            only,
            krust,
            output,
            history,
            no_history,
            baseline,
            dry_run,
            no_cgroup,
        } => {
            let tier = parse_tier(&tier)?;
            if !dry_run
                && !no_cgroup
                && let Some(code) = reexec_in_scope()
            {
                return Ok(code);
            }
            let registry = Registry::load(&registry_dir)?;
            let cache = ReferenceCache::load(&cache_path)?;
            let environment = Environment::discover(&workspace, krust)?;
            if !dry_run && !environment.krust.exists() {
                return Err(format!(
                    "{} does not exist; build it with `cargo build --release -p k-rust --bin krust` (benchmarks/README.md)",
                    environment.krust.display()
                ));
            }
            let commit = git(&workspace, &["rev-parse", "HEAD"]).unwrap_or_default();
            let dirty = git(
                &workspace,
                &["status", "--porcelain", "--untracked-files=no"],
            )
            .is_some_and(|s| !s.is_empty());
            let (started_at, stamp) = utc_now();
            let run_id = format!(
                "{stamp}-{}{}",
                &commit[..commit.len().min(8)],
                if dirty { "-dirty" } else { "" }
            );
            let work = output.unwrap_or_else(|| workspace.join("target/kbench/runs").join(&run_id));
            std::fs::create_dir_all(&work).map_err(|e| e.to_string())?;
            let mut runner = Runner::new(&environment, &registry, work.clone());
            if dry_run {
                for workload in registry
                    .workloads
                    .iter()
                    .filter(|w| selected(w, tier, &only))
                {
                    println!("[{}]", workload.id);
                    for line in runner.describe(
                        workload,
                        &workload.krust,
                        workload.krust.engine.unwrap_or(Engine::Krust),
                    )? {
                        println!("  krust: {line}");
                    }
                }
                return Ok(ExitCode::SUCCESS);
            }
            if no_cgroup {
                eprintln!("kbench: measuring without a cgroup scope; peak memory is unknown");
            }
            let mut run = Run {
                schema: RESULTS_SCHEMA.to_owned(),
                run_id: run_id.clone(),
                started_at,
                finished_at: String::new(),
                tier: tier.name().to_owned(),
                filter: only.clone(),
                commit,
                dirty,
                krust_path: environment.krust.display().to_string(),
                krust_sha256: environment.krust_sha256.clone(),
                memory_method: runner.meter.method_description().to_owned(),
                reference_k_version: environment.k_version.clone(),
                reference_k_opts: REFERENCE_K_OPTS.to_owned(),
                host: host(),
                gap: registry
                    .gaps
                    .iter()
                    .map(|g| results::Gap {
                        semantics: g.semantics.clone(),
                        operation: g.operation.clone(),
                        reason: g.reason.clone(),
                        note: g.note.clone(),
                    })
                    .collect(),
                workload: Vec::new(),
            };
            let mut failed = 0;
            for workload in &registry.workloads {
                let reference = reference_result(&environment, &registry, &cache, workload);
                if !selected(workload, tier, &only) {
                    run.workload.push(skeleton(workload, "skipped", reference));
                    continue;
                }
                eprintln!("[{}] {}", workload.id, workload.title);
                let mut result = skeleton(workload, "ok", reference);
                if let Err(error) = runner.check_pins(workload) {
                    result.status = "error".to_owned();
                    result.detail = Some(error);
                } else {
                    let engine = workload.krust.engine.unwrap_or(Engine::Krust);
                    let measured = runner.measure(workload, &workload.krust, engine, "krust");
                    if measured.status != "ok" {
                        result.status = "failed".to_owned();
                        result.detail = Some(measured.status.clone());
                    }
                    result.krust = measured.samples;
                    result.points = measured.points;
                }
                if result.status != "ok" {
                    failed += 1;
                    eprintln!(
                        "  {}: {}",
                        result.status,
                        result.detail.as_deref().unwrap_or("")
                    );
                } else if let Some((samples, _)) = result.krust.as_ref().map(|s| (s, ())) {
                    eprintln!(
                        "  wall {} s, peak {} MiB",
                        report::seconds(samples.wall()),
                        report::mib(samples.peak())
                    );
                }
                run.workload.push(result);
                run.save(&work.join("results.toml"))?;
            }
            let (finished_at, _) = utc_now();
            run.finished_at = finished_at;
            run.host.load_after = load_average();
            run.save(&work.join("results.toml"))?;
            let history = history.unwrap_or_else(|| history_root(&workspace));
            let baseline = match baseline {
                Some(path) => Some(Run::load(&path)?),
                None => latest_baseline(&history, &run_id, tier.name()),
            };
            let text = report::render(&run, baseline.as_ref());
            std::fs::write(work.join("report.md"), &text).map_err(|e| e.to_string())?;
            if !no_history {
                let target = history.join(&run_id);
                std::fs::create_dir_all(&target).map_err(|e| e.to_string())?;
                std::fs::copy(work.join("results.toml"), target.join("results.toml"))
                    .map_err(|e| e.to_string())?;
                std::fs::write(target.join("report.md"), &text).map_err(|e| e.to_string())?;
                eprintln!("kbench: history {}", target.display());
            }
            print!("{text}");
            eprintln!("kbench: results {}", work.join("results.toml").display());
            Ok(if failed == 0 {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            })
        }
        Commands::Reference {
            tier,
            only,
            force,
            dry_run,
            no_cgroup,
        } => {
            let tier = parse_tier(&tier)?;
            if !dry_run
                && !no_cgroup
                && let Some(code) = reexec_in_scope()
            {
                return Ok(code);
            }
            let registry = Registry::load(&registry_dir)?;
            let mut cache = ReferenceCache::load(&cache_path)?;
            let environment = Environment::discover(&workspace, None)?;
            let (_, stamp) = utc_now();
            let work = workspace.join("target/kbench/reference").join(&stamp);
            std::fs::create_dir_all(&work).map_err(|e| e.to_string())?;
            let mut runner = Runner::new(&environment, &registry, work);
            for workload in registry
                .workloads
                .iter()
                .filter(|w| selected(w, tier, &only))
            {
                let Some(reference) = workload
                    .reference
                    .as_ref()
                    .filter(|r| r.status == ReferenceStatus::Paired)
                else {
                    continue;
                };
                let side = reference.side();
                let key = reference_key(&environment, &registry, workload, &side)?;
                let params: Vec<Option<i64>> = match &workload.ladder {
                    None => vec![None],
                    Some(ladder) => ladder.values.iter().copied().map(Some).collect(),
                };
                let cached = params
                    .iter()
                    .all(|p| cache.find(&workload.id, *p).is_some_and(|m| m.key == key));
                if cached && !force {
                    continue;
                }
                if dry_run {
                    println!("[{}] would measure reference:", workload.id);
                    for line in runner.describe(workload, &side, Engine::Reference)? {
                        println!("  reference: {line}");
                    }
                    continue;
                }
                if let Err(error) = runner.check_pins(workload) {
                    eprintln!("[{}] skipped: {error}", workload.id);
                    continue;
                }
                eprintln!("[{}] measuring reference K once", workload.id);
                let measured = runner.measure(workload, &side, Engine::Reference, "reference");
                let (measured_at, _) = utc_now();
                let entry =
                    |param: Option<i64>, outcome: String, samples: results::Samples| Measurement {
                        workload: workload.id.clone(),
                        param,
                        key: key.clone(),
                        k_version: environment.k_version.clone(),
                        k_opts: REFERENCE_K_OPTS.to_owned(),
                        measured_at: measured_at.clone(),
                        source: format!("kbench {}", env!("CARGO_PKG_VERSION")),
                        host: read_trimmed("/proc/sys/kernel/hostname"),
                        method: runner.meter.method_description().to_owned(),
                        outcome,
                        samples,
                    };
                if measured.status.starts_with("error:") {
                    eprintln!("  not recorded: {}", measured.status);
                    continue;
                }
                if workload.ladder.is_none() {
                    cache.upsert(entry(
                        None,
                        measured.status.clone(),
                        measured.samples.unwrap_or_default(),
                    ));
                } else {
                    let measured_params: Vec<i64> =
                        measured.points.iter().map(|p| p.param).collect();
                    for point in measured.points {
                        cache.upsert(entry(Some(point.param), point.status, point.samples));
                    }
                    // Sizes after a stop are recorded as not run, so they are not retried.
                    for param in params
                        .iter()
                        .flatten()
                        .filter(|p| !measured_params.contains(p))
                    {
                        cache.upsert(entry(
                            Some(*param),
                            "not run: the ladder stopped at a smaller size".to_owned(),
                            results::Samples::default(),
                        ));
                    }
                }
                eprintln!("  {}", measured.status);
                cache.save(&cache_path)?;
            }
            Ok(ExitCode::SUCCESS)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn patterns_match_prefixes_and_stars() {
        assert!(matches("imp/", "imp/compile"));
        assert!(matches("*/compile", "kevm/compile"));
        assert!(!matches("kevm/", "imp/compile"));
    }

    #[test]
    fn utc_dates_are_civil() {
        let (iso, stamp) = utc_now();
        assert_eq!(iso.len(), 20);
        assert_eq!(stamp.len(), 16);
    }
}
