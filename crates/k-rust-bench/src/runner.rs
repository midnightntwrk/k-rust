//! Prepares and measures workloads, for krust (`kbench run`) and once for reference K
//! (`kbench reference`).

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use sha2::{Digest, Sha256};

use crate::check;
use crate::expand::Vars;
use crate::measure::{Invocation, Meter, Outcome, Sample};
use crate::registry::{Engine, Prepare, Registry, Side, Workload};
use crate::results::{Point, Samples};

pub const REFERENCE_K_OPTS: &str = "-Xmx4096m -Xss4m -Dscala.concurrent.context.numThreads=1 -Dscala.concurrent.context.maxThreads=1";
const GIB: u64 = 1 << 30;
const PREPARE_MEMORY_GIB: u64 = 32;
/// Standard output larger than this is deleted once its check has passed.
const KEEP_STDOUT_BYTES: u64 = 64 << 20;

/// Variables to set and variables to remove in an engine's environment.
type EngineEnv = (Vec<(String, String)>, Vec<String>);

/// Checkout roots, tools, and pins of this workspace.
pub struct Environment {
    pub workspace: PathBuf,
    pub roots: BTreeMap<&'static str, PathBuf>,
    pub kbin: PathBuf,
    pub krust: PathBuf,
    pub krust_sha256: String,
    pub k_version: String,
    /// `[reference.*]` revisions of `scripts/reference-differential.toml`.
    pub pins: BTreeMap<String, String>,
    pub prepared_krust: PathBuf,
    pub prepared_reference: PathBuf,
}

fn env_path(name: &str, default: PathBuf) -> PathBuf {
    std::env::var_os(name).map_or(default, PathBuf::from)
}

pub fn sha256_file(path: &Path) -> Result<String, String> {
    let bytes =
        fs::read(path).map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    Ok(hex(&Sha256::digest(&bytes)))
}

fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write;
    bytes.iter().fold(String::new(), |mut out, b| {
        let _ = write!(out, "{b:02x}");
        out
    })
}

pub fn git(directory: &Path, args: &[&str]) -> Option<String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(directory)
        .args(args)
        .env_remove("GIT_DIR")
        .env_remove("GIT_WORK_TREE")
        .output()
        .ok()?;
    output
        .status
        .success()
        .then(|| String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

impl Environment {
    pub fn discover(workspace: &Path, krust: Option<PathBuf>) -> Result<Environment, String> {
        let workspace = workspace.to_path_buf();
        let k = env_path("K_CHECKOUT", workspace.join("k"));
        let mut roots = BTreeMap::new();
        roots.insert("k", k.clone());
        roots.insert(
            "imp",
            env_path("IMP_SEMANTICS_CHECKOUT", workspace.join("imp-semantics")),
        );
        roots.insert(
            "wasm",
            env_path("WASM_SEMANTICS_CHECKOUT", workspace.join("wasm-semantics")),
        );
        roots.insert(
            "evm",
            env_path("EVM_SEMANTICS_CHECKOUT", workspace.join("evm-semantics")),
        );
        roots.insert(
            "mir",
            env_path("MIR_SEMANTICS_CHECKOUT", workspace.join("mir-semantics")),
        );
        roots.insert(
            "evm-equivalence",
            env_path(
                "EVM_EQUIVALENCE_CHECKOUT",
                workspace.join("evm-equivalence"),
            ),
        );
        let kbin = match std::env::var_os("K_KOMPILE") {
            Some(kompile) => PathBuf::from(kompile)
                .parent()
                .map(Path::to_path_buf)
                .ok_or("K_KOMPILE has no directory")?,
            None => k.join("result/bin"),
        };
        let krust =
            krust.unwrap_or_else(|| env_path("KRUST_BIN", workspace.join("target/release/krust")));
        let krust_sha256 = if krust.exists() {
            sha256_file(&krust)?
        } else {
            String::from("missing")
        };
        let manifest_path = workspace.join("scripts/reference-differential.toml");
        let manifest: toml::Value = toml::from_str(
            &fs::read_to_string(&manifest_path)
                .map_err(|error| format!("cannot read {}: {error}", manifest_path.display()))?,
        )
        .map_err(|error| format!("{}: {error}", manifest_path.display()))?;
        let mut pins = BTreeMap::new();
        let mut k_version = String::from("unknown");
        if let Some(reference) = manifest.get("reference").and_then(toml::Value::as_table) {
            for (name, table) in reference {
                if let Some(revision) = table.get("revision").and_then(toml::Value::as_str) {
                    pins.insert(name.clone(), revision.to_owned());
                }
                if name == "k"
                    && let Some(version) = table.get("version").and_then(toml::Value::as_str)
                {
                    version.clone_into(&mut k_version);
                }
            }
        }
        let prepared = workspace.join("target/kbench/prepared");
        Ok(Environment {
            prepared_krust: prepared.join(format!(
                "krust-{}",
                &krust_sha256[..krust_sha256.len().min(16)]
            )),
            prepared_reference: prepared.join(format!("reference-{k_version}")),
            workspace,
            roots,
            kbin,
            krust,
            krust_sha256,
            k_version,
            pins,
        })
    }

    pub fn base_vars(&self) -> Vars {
        let mut vars = Vars::default();
        vars.set("workspace", self.workspace.display().to_string());
        for (name, path) in &self.roots {
            vars.set(name, path.display().to_string());
        }
        vars.set(
            "builtin",
            self.roots["k"]
                .join("k-distribution/include/kframework/builtin")
                .display()
                .to_string(),
        );
        vars.set(
            "programs",
            self.workspace
                .join("benchmarks/programs")
                .display()
                .to_string(),
        );
        vars.set("kbin", self.kbin.display().to_string());
        vars.set("krust", self.krust.display().to_string());
        vars
    }

    fn pin_checkout(&self, pin: &str) -> PathBuf {
        match pin {
            "kevm" => self.roots["evm"].clone(),
            "kevm-plugin" => self.roots["evm"].join("kevm-pyk/src/kevm_pyk/kproj/plugin"),
            other => self
                .roots
                .get(other)
                .cloned()
                .unwrap_or_else(|| self.workspace.join(other)),
        }
    }

    /// `Err` names the first checkout that is not at its pinned revision or has modifications.
    pub fn check_pin(&self, pin: &str) -> Result<(), String> {
        let expected = self
            .pins
            .get(pin)
            .ok_or_else(|| format!("no [reference.{pin}] revision in the manifest"))?;
        let checkout = self.pin_checkout(pin);
        let actual = git(&checkout, &["rev-parse", "HEAD"])
            .ok_or_else(|| format!("{pin} checkout is missing: {}", checkout.display()))?;
        if &actual != expected {
            return Err(format!(
                "{pin} checkout {} is at {actual}, pinned {expected}",
                checkout.display()
            ));
        }
        if git(&checkout, &["status", "--short", "--untracked-files=no"])
            .is_some_and(|status| !status.is_empty())
        {
            return Err(format!(
                "{pin} checkout {} has modifications",
                checkout.display()
            ));
        }
        Ok(())
    }

    fn prepared_root(&self, engine: Engine) -> &Path {
        match engine {
            Engine::Reference => &self.prepared_reference,
            Engine::Krust | Engine::Command => &self.prepared_krust,
        }
    }

    /// The program and arguments of one registry argv for an engine.
    fn command_line(&self, engine: Engine, argv: Vec<String>) -> Vec<String> {
        match engine {
            Engine::Krust => {
                let mut line = vec![self.krust.display().to_string()];
                line.extend(argv);
                line
            }
            Engine::Reference => {
                let mut line = argv;
                if !line[0].contains('/') {
                    line[0] = self.kbin.join(&line[0]).display().to_string();
                }
                line
            }
            Engine::Command => argv,
        }
    }

    fn engine_env(
        engine: Engine,
        extra: &BTreeMap<String, String>,
        vars: &Vars,
    ) -> Result<EngineEnv, String> {
        let mut env = Vec::new();
        let mut remove = Vec::new();
        if engine == Engine::Reference {
            env.push(("K_OPTS".to_owned(), REFERENCE_K_OPTS.to_owned()));
            remove.push("GHCRTS".to_owned());
        }
        for (name, value) in extra {
            env.push((name.clone(), vars.expand(value)?));
        }
        Ok((env, remove))
    }
}

/// The reference cache key of a paired workload's reference side.
pub fn reference_key(
    environment: &Environment,
    registry: &Registry,
    workload: &Workload,
    side: &Side,
) -> Result<String, String> {
    let mut text = String::from("kbench-reference-key/1\n");
    let mut push = |label: &str, value: &str| {
        text.push_str(label);
        text.push('\x1f');
        text.push_str(value);
        text.push('\n');
    };
    for step in side.invocations() {
        push("argv", &step.join("\x1e"));
    }
    push("stdin", side.stdin.as_deref().unwrap_or("/dev/null"));
    for (name, value) in &side.env {
        push("env", &format!("{name}={value}"));
    }
    for step in registry.prepare_order(&side.prepare)? {
        push("prepare", &step.name);
        push("prepare-engine", &format!("{:?}", step.engine));
        push("prepare-argv", &step.argv.join("\x1e"));
        for (name, value) in &step.env {
            push("prepare-env", &format!("{name}={value}"));
        }
    }
    if let Some(ladder) = &workload.ladder {
        push("ladder-input", ladder.input.as_deref().unwrap_or(""));
        push(
            "ladder-generator",
            &ladder
                .generator
                .as_ref()
                .map(|g| g.join("\x1e"))
                .unwrap_or_default(),
        );
    }
    push("k-opts", REFERENCE_K_OPTS);
    push("k-version", &environment.k_version);
    let pins: BTreeSet<&str> = workload
        .pins
        .iter()
        .map(String::as_str)
        .chain(std::iter::once("k"))
        .collect();
    for pin in pins {
        push(
            "pin",
            &format!(
                "{pin}={}",
                environment.pins.get(pin).map_or("", String::as_str)
            ),
        );
    }
    Ok(hex(&Sha256::digest(text.as_bytes())))
}

/// The measurement of one side: samples of a plain workload, or ladder points.
pub struct SideResult {
    /// `ok`, or the first failure.
    pub status: String,
    pub samples: Option<Samples>,
    pub points: Vec<Point>,
}

pub struct Runner<'a> {
    pub environment: &'a Environment,
    pub registry: &'a Registry,
    pub meter: Meter,
    pub work: PathBuf,
    prepared: BTreeMap<String, Result<(), String>>,
    pins: BTreeMap<String, Result<(), String>>,
}

fn sanitize(id: &str) -> String {
    id.replace('/', "__")
}

fn exit_code(outcome: Outcome) -> Option<i32> {
    match outcome {
        Outcome::Ok => Some(0),
        Outcome::Exit(code) => Some(code),
        _ => None,
    }
}

impl<'a> Runner<'a> {
    pub fn new(environment: &'a Environment, registry: &'a Registry, work: PathBuf) -> Runner<'a> {
        Runner {
            environment,
            registry,
            meter: Meter::new(),
            work,
            prepared: BTreeMap::new(),
            pins: BTreeMap::new(),
        }
    }

    pub fn check_pins(&mut self, workload: &Workload) -> Result<(), String> {
        for pin in workload
            .pins
            .iter()
            .map(String::as_str)
            .chain(std::iter::once("k"))
        {
            let result = self
                .pins
                .entry(pin.to_owned())
                .or_insert_with(|| self.environment.check_pin(pin))
                .clone();
            result?;
        }
        Ok(())
    }

    /// Runs a prepare step unless its `creates` file exists; `point` binds a ladder value's
    /// parameter and `${input}`, so a step can depend on them.
    fn ensure_prepared(
        &mut self,
        step: &Prepare,
        side_engine: Engine,
        point: &[(String, String)],
    ) -> Result<(), String> {
        let engine_root = match step.engine {
            Engine::Command => self.environment.prepared_root(side_engine),
            engine => self.environment.prepared_root(engine),
        }
        .to_path_buf();
        let mut vars = self.environment.base_vars();
        vars.set("prepared", engine_root.display().to_string());
        for (name, value) in point {
            vars.set(name, value.clone());
        }
        let creates = PathBuf::from(vars.expand(&step.creates)?);
        let memo = format!("{}\u{1f}{}", step.name, creates.display());
        if let Some(result) = self.prepared.get(&memo) {
            return result.clone();
        }
        let result = self.run_prepare(step, &engine_root, &vars, &creates);
        self.prepared.insert(memo, result.clone());
        result
    }

    fn run_prepare(
        &mut self,
        step: &Prepare,
        engine_root: &Path,
        vars: &Vars,
        creates: &Path,
    ) -> Result<(), String> {
        if creates.exists() {
            return Ok(());
        }
        let logs = self.work.join("prepare");
        fs::create_dir_all(&logs).map_err(|e| e.to_string())?;
        fs::create_dir_all(engine_root).map_err(|e| e.to_string())?;
        let argv = vars.expand_all(&step.argv)?;
        let (env, env_remove) = Environment::engine_env(step.engine, &step.env, vars)?;
        eprintln!("[prepare] {}", step.name);
        let invocation = Invocation {
            steps: vec![self.environment.command_line(step.engine, argv)],
            env,
            env_remove,
            stdin: PathBuf::from("/dev/null"),
            stdout: Some(logs.join(format!("{}.out", step.name))),
            stderr: logs.join(format!("{}.err", step.name)),
            cwd: self.environment.workspace.clone(),
            timeout: Duration::from_secs(step.timeout_seconds.unwrap_or(3600)),
            memory_max_bytes: PREPARE_MEMORY_GIB * GIB,
        };
        let sample = self.meter.run(&invocation).map_err(|e| e.to_string())?;
        if sample.outcome != Outcome::Ok || !creates.exists() {
            return Err(format!(
                "prepare step {} failed ({}; {} not created); log {}",
                step.name,
                sample.outcome.describe(),
                creates.display(),
                invocation.stderr.display()
            ));
        }
        Ok(())
    }

    /// Prints the expanded commands of one side without running anything.
    pub fn describe(
        &self,
        workload: &Workload,
        side: &Side,
        engine: Engine,
    ) -> Result<Vec<String>, String> {
        let mut vars = self.environment.base_vars();
        vars.set(
            "prepared",
            self.environment.prepared_root(engine).display().to_string(),
        );
        vars.set(
            "run",
            self.work
                .join(sanitize(&workload.id))
                .join("run")
                .display()
                .to_string(),
        );
        vars.set("input", "<input>");
        if let Some(ladder) = &workload.ladder {
            vars.set(&ladder.param, ladder.values[0].to_string());
        }
        vars.set("expect", "<expect>");
        let mut lines = Vec::new();
        for step in self.registry.prepare_order(&side.prepare)? {
            let mut step_vars = vars.clone();
            let root = match step.engine {
                Engine::Command => self.environment.prepared_root(engine),
                other => self.environment.prepared_root(other),
            };
            step_vars.set("prepared", root.display().to_string());
            lines.push(format!(
                "prepare {}: {}",
                step.name,
                self.environment
                    .command_line(step.engine, step_vars.expand_all(&step.argv)?)
                    .join(" ")
            ));
        }
        for step in side.invocations() {
            lines.push(
                self.environment
                    .command_line(engine, vars.expand_all(&step)?)
                    .join(" "),
            );
        }
        Ok(lines)
    }

    /// Prepares and measures one side of a workload.
    pub fn measure(
        &mut self,
        workload: &Workload,
        side: &Side,
        engine: Engine,
        label: &str,
    ) -> SideResult {
        match self.measure_inner(workload, side, engine, label) {
            Ok(result) => result,
            Err(error) => SideResult {
                status: format!("error: {error}"),
                samples: None,
                points: Vec::new(),
            },
        }
    }

    fn measure_inner(
        &mut self,
        workload: &Workload,
        side: &Side,
        engine: Engine,
        label: &str,
    ) -> Result<SideResult, String> {
        let steps = self.registry.prepare_order(&side.prepare)?;
        if workload.ladder.is_none() {
            for step in &steps {
                self.ensure_prepared(step, engine, &[])?;
            }
        }
        let directory = self.work.join(sanitize(&workload.id)).join(label);
        fs::create_dir_all(&directory).map_err(|e| e.to_string())?;
        let mut vars = self.environment.base_vars();
        vars.set(
            "prepared",
            self.environment.prepared_root(engine).display().to_string(),
        );
        let run_dir = directory.join("run");
        vars.set("run", run_dir.display().to_string());
        let Some(ladder) = &workload.ladder else {
            let (status, samples) = self.repeat(
                workload,
                side,
                engine,
                &vars,
                &directory,
                &BTreeMap::new(),
                workload.warmup(),
                workload.runs(),
            )?;
            return Ok(SideResult {
                status,
                samples: Some(samples),
                points: Vec::new(),
            });
        };
        let stop = ladder.stop_seconds.unwrap_or(120.0);
        let mut points = Vec::new();
        let mut status = String::from("ok");
        for &value in &ladder.values {
            let mut point_vars = vars.clone();
            point_vars.set(&ladder.param, value.to_string());
            let input = directory.join(format!("input-{value}"));
            point_vars.set("input", input.display().to_string());
            let text = match (&ladder.input, &ladder.generator) {
                (Some(template), _) => point_vars.expand(template)?,
                (None, Some(generator)) => {
                    let argv = point_vars.expand_all(generator)?;
                    let output = Command::new(&argv[0])
                        .args(&argv[1..])
                        .current_dir(&self.environment.workspace)
                        .output()
                        .map_err(|error| format!("generator {}: {error}", argv[0]))?;
                    if !output.status.success() {
                        return Err(format!(
                            "generator {} failed: {}",
                            argv.join(" "),
                            String::from_utf8_lossy(&output.stderr)
                        ));
                    }
                    String::from_utf8(output.stdout).map_err(|e| e.to_string())?
                }
                (None, None) => unreachable!("validated"),
            };
            fs::write(&input, text).map_err(|e| e.to_string())?;
            let point = [
                (ladder.param.clone(), value.to_string()),
                ("input".to_owned(), input.display().to_string()),
            ];
            for step in &steps {
                self.ensure_prepared(step, engine, &point)?;
            }
            let params = BTreeMap::from([(ladder.param.clone(), value)]);
            let (point_status, samples) = self.repeat(
                workload,
                side,
                engine,
                &point_vars,
                &directory,
                &params,
                0,
                workload.runs(),
            )?;
            let slow = samples.wall().is_some_and(|wall| wall > stop);
            let failed = point_status != "ok";
            points.push(Point {
                param: value,
                status: point_status.clone(),
                samples,
            });
            if failed {
                status = format!("{}={value}: {point_status}", ladder.param);
                break;
            }
            if slow {
                break;
            }
        }
        Ok(SideResult {
            status,
            samples: None,
            points,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn repeat(
        &mut self,
        workload: &Workload,
        side: &Side,
        engine: Engine,
        vars: &Vars,
        directory: &Path,
        params: &BTreeMap<String, i64>,
        warmup: u32,
        runs: u32,
    ) -> Result<(String, Samples), String> {
        let mut vars = vars.clone();
        check::bind_expect(&side.check, &mut vars, params)?;
        let run_dir = PathBuf::from(vars.get("run").unwrap_or_default());
        let stdout = side.check.reads_stdout().then(|| directory.join("stdout"));
        let stderr = directory.join("stderr");
        let stdin = match &side.stdin {
            Some(path) => PathBuf::from(vars.expand(path)?),
            None => PathBuf::from("/dev/null"),
        };
        let steps = side
            .invocations()
            .into_iter()
            .map(|argv| {
                Ok(self
                    .environment
                    .command_line(engine, vars.expand_all(&argv)?))
            })
            .collect::<Result<Vec<_>, String>>()?;
        let (env, env_remove) = Environment::engine_env(engine, &side.env, &vars)?;
        let invocation = Invocation {
            steps,
            env,
            env_remove,
            stdin,
            stdout: stdout.clone(),
            stderr: stderr.clone(),
            cwd: self.environment.workspace.clone(),
            timeout: Duration::from_secs(workload.timeout_seconds()),
            memory_max_bytes: workload.memory_gib() * GIB,
        };
        let mut samples = Samples::default();
        for index in 0..warmup + runs {
            if run_dir.exists() {
                fs::remove_dir_all(&run_dir).map_err(|e| e.to_string())?;
            }
            fs::create_dir_all(&run_dir).map_err(|e| e.to_string())?;
            let sample: Sample = self.meter.run(&invocation).map_err(|e| e.to_string())?;
            let verdict = match exit_code(sample.outcome) {
                None => Err(sample.outcome.describe()),
                Some(code) => check::verify(&side.check, &vars, code, stdout.as_deref())
                    .map_err(|error| format!("check: {error}")),
            };
            if let Err(failure) = verdict {
                let tail = crate::measure::tail(&stderr, 400);
                let tail = tail.trim();
                let detail = if tail.is_empty() {
                    failure
                } else {
                    format!("{failure} (stderr: …{})", tail.replace('\n', " ⏎ "))
                };
                return Ok((detail, samples));
            }
            if index >= warmup {
                samples.wall_seconds.push(sample.wall_seconds);
                if let Some(cpu) = sample.cpu_seconds {
                    samples.cpu_seconds.push(cpu);
                }
                if let Some(peak) = sample.peak_bytes {
                    samples.peak_bytes.push(peak);
                }
            }
        }
        if let Some(path) = &stdout
            && fs::metadata(path).is_ok_and(|m| m.len() > KEEP_STDOUT_BYTES)
        {
            let _ = fs::remove_file(path);
        }
        if run_dir.exists() {
            let _ = fs::remove_dir_all(&run_dir);
        }
        Ok((String::from("ok"), samples))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The reference runtime options are part of a cached measurement's key, so the reference
    /// always runs with `REFERENCE_K_OPTS` and without `GHCRTS`, whatever the caller exports.
    #[test]
    fn the_reference_runs_with_its_own_runtime_options_not_the_callers() {
        let (env, remove) =
            Environment::engine_env(Engine::Reference, &BTreeMap::new(), &Vars::default()).unwrap();
        assert_eq!(
            env,
            vec![("K_OPTS".to_owned(), REFERENCE_K_OPTS.to_owned())]
        );
        assert_eq!(remove, vec!["GHCRTS".to_owned()]);
        let (env, remove) =
            Environment::engine_env(Engine::Krust, &BTreeMap::new(), &Vars::default()).unwrap();
        assert!(env.is_empty() && remove.is_empty());
    }
}
