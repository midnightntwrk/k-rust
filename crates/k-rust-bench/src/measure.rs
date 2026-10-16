//! Runs one invocation and measures its wall time, CPU time, and whole-tree peak memory.
//!
//! With the cgroup method, `kbench` runs inside a delegated user systemd scope.
//! The scope holds a `supervisor` cgroup for `kbench` itself and one fresh cgroup per run.
//! Before a run starts, `kbench` moves itself into the run's cgroup, outside the timed region,
//! so every process the run forks starts there and no process changes cgroup while it is timed.
//! The run's figures are the cgroup's `memory.peak` (every process of the tree that is resident
//! at the same time, summed) and its `cpu.stat` user and system time.
//! The cgroup's `memory.max` is the workload's memory limit, so a run that exceeds it is killed
//! and reported as out of memory instead of disturbing the host.
//!
//! Without a delegated scope (an `agent-N` sandbox, for example) the rusage method records wall
//! time and the CPU time of reaped children; peak memory is then unknown.

use std::fs::{self, File};
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

pub const SCOPE_ENV: &str = "KBENCH_IN_SCOPE";

pub const CGROUP_METHOD: &str = "cgroup v2: a fresh cgroup per run holds the whole process tree; peak is its memory.peak, CPU is its cpu.stat user + system time";
pub const RUSAGE_METHOD: &str =
    "rusage: wall time and the CPU time of reaped children; peak memory unknown";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Ok,
    Exit(i32),
    Signal,
    Timeout,
    OutOfMemory,
    SpawnFailed,
}

impl Outcome {
    pub fn describe(self) -> String {
        match self {
            Outcome::Ok => "ok".to_owned(),
            Outcome::Exit(code) => format!("exit {code}"),
            Outcome::Signal => "killed by a signal".to_owned(),
            Outcome::Timeout => "timeout".to_owned(),
            Outcome::OutOfMemory => "out of memory".to_owned(),
            Outcome::SpawnFailed => "could not start".to_owned(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Sample {
    pub wall_seconds: f64,
    pub cpu_seconds: Option<f64>,
    pub peak_bytes: Option<u64>,
    pub outcome: Outcome,
}

pub struct Invocation {
    pub steps: Vec<Vec<String>>,
    pub env: Vec<(String, String)>,
    pub env_remove: Vec<String>,
    pub stdin: PathBuf,
    pub stdout: Option<PathBuf>,
    pub stderr: PathBuf,
    pub cwd: PathBuf,
    pub timeout: Duration,
    pub memory_max_bytes: u64,
}

enum Method {
    Cgroup { scope: PathBuf, next: u64 },
    Rusage { clock_ticks: f64 },
}

pub struct Meter {
    method: Method,
}

fn current_cgroup() -> Option<PathBuf> {
    let text = fs::read_to_string("/proc/self/cgroup").ok()?;
    let path = text.lines().find_map(|line| line.strip_prefix("0::"))?;
    Some(Path::new("/sys/fs/cgroup").join(path.trim_start_matches('/')))
}

/// The tightest memory limits of the current cgroup and its ancestors, as systemd properties,
/// so a run started inside a memory-limited scope stays inside that limit.
pub fn inherited_scope_properties() -> Vec<String> {
    let Some(current) = current_cgroup() else {
        return Vec::new();
    };
    let mut properties = Vec::new();
    for (file, property) in [
        ("memory.max", "MemoryMax"),
        ("memory.high", "MemoryHigh"),
        ("memory.swap.max", "MemorySwapMax"),
    ] {
        let mut tightest: Option<u64> = None;
        let mut directory = current.as_path();
        while directory.starts_with("/sys/fs/cgroup/") {
            if let Ok(text) = fs::read_to_string(directory.join(file))
                && let Ok(value) = text.trim().parse::<u64>()
            {
                tightest = Some(tightest.map_or(value, |t| t.min(value)));
            }
            match directory.parent() {
                Some(parent) => directory = parent,
                None => break,
            }
        }
        if let Some(limit) = tightest {
            properties.push(format!("{property}={limit}"));
        }
    }
    properties
}

/// Whether a delegated user scope can be created here.
pub fn scope_available() -> bool {
    Command::new("systemd-run")
        .args([
            "--user",
            "--scope",
            "--quiet",
            "-p",
            "Delegate=yes",
            "--",
            "true",
        ])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
}

fn clock_ticks() -> f64 {
    Command::new("getconf")
        .arg("CLK_TCK")
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .and_then(|text| text.trim().parse().ok())
        .unwrap_or(100.0)
}

/// CPU seconds of this process's reaped children (`cutime + cstime` of `/proc/self/stat`).
fn children_cpu_seconds(clock_ticks: f64) -> Option<f64> {
    let text = fs::read_to_string("/proc/self/stat").ok()?;
    let after = &text[text.rfind(')')? + 1..];
    let fields: Vec<&str> = after.split_whitespace().collect();
    // Field 3 (state) is the first after the command name; cutime is field 16, cstime 17.
    let cutime: f64 = fields.get(13)?.parse().ok()?;
    let cstime: f64 = fields.get(14)?.parse().ok()?;
    Some((cutime + cstime) / clock_ticks)
}

fn write(path: &Path, value: &str) -> io::Result<()> {
    fs::write(path, value)
}

fn read_key(path: &Path, key: &str) -> Option<u64> {
    let text = fs::read_to_string(path).ok()?;
    text.lines().find_map(|line| {
        let (name, value) = line.split_once(' ')?;
        (name == key).then(|| value.trim().parse().ok())?
    })
}

impl Meter {
    /// The cgroup method when this process runs in a delegated scope (`SCOPE_ENV` set by the
    /// re-exec in `main`), otherwise the rusage method.
    pub fn new() -> Meter {
        if std::env::var_os(SCOPE_ENV).is_some()
            && let Some(scope) = current_cgroup()
            && Meter::enter_scope(&scope).is_ok()
        {
            return Meter {
                method: Method::Cgroup { scope, next: 0 },
            };
        }
        Meter {
            method: Method::Rusage {
                clock_ticks: clock_ticks(),
            },
        }
    }

    fn enter_scope(scope: &Path) -> io::Result<()> {
        let supervisor = scope.join("supervisor");
        if !supervisor.exists() {
            fs::create_dir(&supervisor)?;
        }
        write(
            &supervisor.join("cgroup.procs"),
            &std::process::id().to_string(),
        )?;
        write(&scope.join("cgroup.subtree_control"), "+memory")?;
        Ok(())
    }

    pub fn method_description(&self) -> &'static str {
        match self.method {
            Method::Cgroup { .. } => CGROUP_METHOD,
            Method::Rusage { .. } => RUSAGE_METHOD,
        }
    }

    pub fn run(&mut self, invocation: &Invocation) -> io::Result<Sample> {
        match &mut self.method {
            Method::Cgroup { scope, next } => {
                *next += 1;
                let scope = scope.clone();
                let run = scope.join(format!("run-{next}"));
                fs::create_dir(&run)?;
                // A limit the kernel refuses (no swap controller, for example) is not fatal.
                let _ = write(
                    &run.join("memory.max"),
                    &invocation.memory_max_bytes.to_string(),
                );
                let _ = write(&run.join("memory.swap.max"), "0");
                let pid = std::process::id().to_string();
                write(&run.join("cgroup.procs"), &pid)?;
                let timed = execute(invocation);
                write(&scope.join("supervisor").join("cgroup.procs"), &pid)?;
                let (wall, mut outcome) = timed?;
                // Processes a run leaves behind (daemons) end with it.
                let _ = write(&run.join("cgroup.kill"), "1");
                let deadline = Instant::now() + Duration::from_secs(10);
                while read_key(&run.join("cgroup.events"), "populated") != Some(0)
                    && Instant::now() < deadline
                {
                    std::thread::sleep(Duration::from_millis(20));
                }
                let peak = fs::read_to_string(run.join("memory.peak"))
                    .ok()
                    .and_then(|text| text.trim().parse().ok());
                let user = read_key(&run.join("cpu.stat"), "user_usec");
                let system = read_key(&run.join("cpu.stat"), "system_usec");
                if read_key(&run.join("memory.events"), "oom_kill").unwrap_or(0) > 0
                    && outcome != Outcome::Ok
                {
                    outcome = Outcome::OutOfMemory;
                }
                let _ = fs::remove_dir(&run);
                Ok(Sample {
                    wall_seconds: wall,
                    #[allow(clippy::cast_precision_loss)]
                    cpu_seconds: user.zip(system).map(|(u, s)| (u + s) as f64 / 1e6),
                    peak_bytes: peak,
                    outcome,
                })
            }
            Method::Rusage { clock_ticks } => {
                let before = children_cpu_seconds(*clock_ticks);
                let (wall, outcome) = execute(invocation)?;
                let after = children_cpu_seconds(*clock_ticks);
                Ok(Sample {
                    wall_seconds: wall,
                    cpu_seconds: before.zip(after).map(|(b, a)| a - b),
                    peak_bytes: None,
                    outcome,
                })
            }
        }
    }
}

/// Runs the steps in order and returns the wall time from the first start to the last exit.
fn execute(invocation: &Invocation) -> io::Result<(f64, Outcome)> {
    use std::os::unix::process::{CommandExt, ExitStatusExt};

    let stdout = match &invocation.stdout {
        Some(path) => Some(File::create(path)?),
        None => None,
    };
    let stderr = File::create(&invocation.stderr)?;
    let started = Instant::now();
    let deadline = started + invocation.timeout;
    for step in &invocation.steps {
        let mut command = Command::new(&step[0]);
        command
            .args(&step[1..])
            .current_dir(&invocation.cwd)
            .stdin(File::open(&invocation.stdin)?)
            .stderr(stderr.try_clone()?)
            .process_group(0);
        match &stdout {
            Some(file) => command.stdout(file.try_clone()?),
            None => command.stdout(Stdio::null()),
        };
        for name in &invocation.env_remove {
            command.env_remove(name);
        }
        for (name, value) in &invocation.env {
            command.env(name, value);
        }
        let mut child = match command.spawn() {
            Ok(child) => child,
            Err(error) => {
                use std::io::Write;
                let mut log = stderr.try_clone()?;
                let _ = writeln!(log, "kbench: cannot start {}: {error}", step[0]);
                return Ok((started.elapsed().as_secs_f64(), Outcome::SpawnFailed));
            }
        };
        let pgid = child.id();
        let (done, waiting) = mpsc::channel::<()>();
        let remaining = deadline.saturating_duration_since(Instant::now());
        let watchdog = std::thread::spawn(move || {
            if waiting.recv_timeout(remaining).is_err() {
                // The whole process group: a JVM or a shell wrapper has children.
                let _ = Command::new("kill")
                    .args(["-KILL", "--", &format!("-{pgid}")])
                    .stdout(Stdio::null())
                    .stderr(Stdio::null())
                    .status();
                true
            } else {
                false
            }
        });
        let status = child.wait()?;
        let _ = done.send(());
        let timed_out = watchdog.join().unwrap_or(false);
        if timed_out {
            return Ok((started.elapsed().as_secs_f64(), Outcome::Timeout));
        }
        if !status.success() {
            let outcome = match (status.code(), status.signal()) {
                (Some(code), _) => Outcome::Exit(code),
                (None, _) => Outcome::Signal,
            };
            return Ok((started.elapsed().as_secs_f64(), outcome));
        }
    }
    Ok((started.elapsed().as_secs_f64(), Outcome::Ok))
}

/// Reads at most `limit` bytes of the end of a file, for failure messages.
pub fn tail(path: &Path, limit: u64) -> String {
    use std::io::{Seek, SeekFrom};
    let Ok(mut file) = File::open(path) else {
        return String::new();
    };
    let length = file.metadata().map(|m| m.len()).unwrap_or(0);
    let _ = file.seek(SeekFrom::Start(length.saturating_sub(limit)));
    let mut bytes = Vec::new();
    let _ = file.read_to_end(&mut bytes);
    String::from_utf8_lossy(&bytes).into_owned()
}
