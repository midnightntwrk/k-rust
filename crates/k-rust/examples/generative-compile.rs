//! Replay harness of the opt-in generative compile test (`scripts/generative-compile.sh`).
//!
//! The feature `generative-harness` gates this example, so ordinary builds, `cargo test` and
//! `cargo clippy --all-targets` never compile it. Build it with
//! `cargo build --release -p k-rust --features generative-harness --example generative-compile`.
//!
//! ```text
//! generative-compile run CORPUS_DIR OUT.tsv [--jobs J] [--timeout SECS] [--fresh]
//! generative-compile case FILE.k [--fresh]
//! generative-compile worker [--fresh]
//! ```
//!
//! Every case is one K definition whose main module is `MAIN`. The oracle accepts two outcomes:
//! loading or compiling fails with an ordinary error, or compilation succeeds and the emitted
//! `definition.kore` parses and internalizes in the Rust backend. A panic, a process crash, a
//! timeout, or a KORE parse or backend failure after a successful compilation is a violation.
//! Whether an ordinary error is the right answer for that input is decided afterwards by
//! `scripts/generative/triage.py`.
//!
//! `run` writes one TSV row per case (`file outcome location first_line ms wall_ms`). It keeps
//! `--jobs` persistent `worker` processes, each under a 6 GiB address-space limit. A worker loads
//! the implicit prelude (`kast.md`, `domains.md`) once, then compiles each case against that
//! prepared base, so loading a case parses only its own module's rules. A worker that panics is
//! replaced after reporting the panic, so no later case runs in a process whose state a panic
//! interrupted. A worker that crashes (for example on a stack overflow) or exceeds `--timeout` on
//! a case is killed and replaced; that case is recorded as `crash` or `timeout`.
//!
//! The prepared base parses the prelude's rules once, without any case's syntax in scope. A
//! defect in which a case's productions change how a builtin module's rules parse is therefore
//! visible only with `--fresh`, which loads the prelude again with every case.
//!
//! `case` compiles one file in this process and prints the result line, with the full error on
//! standard error; `scripts/generative/reduce.py` calls it once per candidate.

use std::{
    any::Any,
    collections::{BTreeMap, VecDeque},
    env, fs,
    io::{self, BufRead, BufReader, Read, Write},
    panic::{self, AssertUnwindSafe},
    path::{Path, PathBuf},
    process::{Child, ChildStdin, Command, ExitStatus, Stdio},
    sync::{
        Arc, Mutex,
        mpsc::{self, Receiver, RecvTimeoutError},
    },
    thread::{self, JoinHandle},
    time::{Duration, Instant},
};

use k_rust::{
    builtin::embedded,
    definition::json::ProvenanceDefinition,
    diagnostic::{Diagnostic, Severity},
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::parser::parse_definition,
    outer::{
        LoadError, LoadOptions, LoadedDefinition, ResolvedSource, load_with_options,
        load_with_prepared_base,
    },
};
use k_rust_backend::definition::BackendDefinition;

/// Address-space limit of one worker process, in KiB, so that a runaway case aborts its worker
/// instead of exhausting a shared host.
const WORKER_ADDRESS_SPACE_KIB: u64 = 6 * 1024 * 1024;
/// How long a worker may take to load the prelude before it reports ready.
const WORKER_STARTUP: Duration = Duration::from_secs(120);
/// Name of the empty module that anchors the prelude load; it is dropped from the base.
const BASE_ANCHOR_MODULE: &str = "GENERATIVE-COMPILE-BASE";

/// One case's verdict as the worker reports it.
struct Outcome {
    class: &'static str,
    located: bool,
    message: String,
}

impl Outcome {
    fn new(class: &'static str, located: bool, message: String) -> Self {
        Self {
            class,
            located,
            message,
        }
    }
}

fn load_options(with_prelude: bool) -> LoadOptions {
    LoadOptions {
        implicit_sources: if with_prelude {
            vec![embedded("prelude.md").expect("the prelude is embedded")]
        } else {
            Vec::new()
        },
        excluded_module_attributes: vec![
            CompilationBackend::Rust.excluded_module_attribute().into(),
        ],
        ..LoadOptions::default()
    }
}

fn builtin_resolver(_: &str, required: &str) -> Result<ResolvedSource, String> {
    embedded(required).ok_or_else(|| format!("unexpected require {required}"))
}

/// How a worker loads each case: against the prelude it loaded once, or with a fresh prelude.
enum Loader {
    Prepared(Box<ProvenanceDefinition>),
    Fresh,
}

impl Loader {
    fn new(fresh: bool) -> Self {
        if fresh {
            return Self::Fresh;
        }
        // The prelude's modules, with their rules parsed, loaded once around an empty anchor
        // module that is then removed, so the base holds exactly what the prelude contributes.
        let anchor = ResolvedSource::new(
            "generative-compile-base".to_owned(),
            format!("module {BASE_ANCHOR_MODULE}\nendmodule\n"),
        );
        let loaded = load_with_options(
            anchor,
            BASE_ANCHOR_MODULE,
            &mut builtin_resolver,
            &load_options(true),
        )
        .unwrap_or_else(|error| panic!("the prelude does not load: {error}"));
        let mut definition = loaded.definition().clone();
        definition
            .modules
            .retain(|module| module.name != BASE_ANCHOR_MODULE);
        Self::Prepared(Box::new(ProvenanceDefinition {
            definition,
            source_table: loaded.source_table().clone(),
        }))
    }

    fn load(&self, entry: ResolvedSource) -> Result<LoadedDefinition, LoadError> {
        match self {
            Self::Prepared(base) => load_with_prepared_base(
                entry,
                "MAIN",
                &mut builtin_resolver,
                &load_options(false),
                base,
                &[],
                &[],
            ),
            Self::Fresh => {
                load_with_options(entry, "MAIN", &mut builtin_resolver, &load_options(true))
            }
        }
    }
}

/// The message and location of the last panic, recorded by the hook installed in [`quiet_panics`].
static LAST_PANIC: Mutex<Option<String>> = Mutex::new(None);

/// Replace the default panic report on standard error by a record that [`panic_text`] reads.
fn quiet_panics() {
    panic::set_hook(Box::new(|info| {
        let location = info
            .location()
            .map(|location| format!("{}:{}: ", location.file(), location.line()))
            .unwrap_or_default();
        let text = format!("{location}{}", payload_text(info.payload()));
        if let Ok(mut last) = LAST_PANIC.lock() {
            *last = Some(text);
        }
    }));
}

fn payload_text(payload: &(dyn Any + Send)) -> String {
    if let Some(text) = payload.downcast_ref::<&str>() {
        (*text).to_owned()
    } else if let Some(text) = payload.downcast_ref::<String>() {
        text.clone()
    } else {
        "<non-string panic>".into()
    }
}

fn panic_text(payload: &(dyn Any + Send)) -> String {
    LAST_PANIC
        .lock()
        .ok()
        .and_then(|mut last| last.take())
        .unwrap_or_else(|| payload_text(payload))
}

/// Whether an error without structured diagnostics carries a source position: its rendering
/// names a line and column, or its structure holds a location.
fn has_position(display: &str, debug: &str) -> bool {
    let position = regex::Regex::new(r"\d+:\d+|\.(k|md):\d+").expect("valid regex");
    position.is_match(display)
        || debug.contains("line:")
        || debug.contains("Location")
        || debug.contains("location: Some")
}

/// A diagnostic's message on one line, so that its hint reaches the result row.
fn one_line(message: &str) -> String {
    message.lines().map(str::trim).collect::<Vec<_>>().join(" ")
}

fn first_error(diagnostics: &[Diagnostic]) -> Option<&Diagnostic> {
    diagnostics
        .iter()
        .find(|diagnostic| diagnostic.severity == Severity::Error)
}

fn load_error_outcome(error: &LoadError) -> Outcome {
    let debug = format!("{error:?}");
    let variant = debug
        .split(|c: char| !c.is_alphanumeric())
        .next()
        .unwrap_or("");
    let class = match error {
        LoadError::Parse { .. } | LoadError::Markdown { .. } => "parse_error",
        _ => "load_error",
    };
    if let LoadError::SourceDiagnostics(diagnostics) = error
        && let Some(diagnostic) = first_error(diagnostics)
    {
        return Outcome::new(
            class,
            diagnostic.location.is_some(),
            format!("[{variant}] {}", one_line(&diagnostic.message)),
        );
    }
    let display = error.to_string();
    Outcome::new(
        class,
        has_position(&display, &debug),
        format!("[{variant}] {display}"),
    )
}

fn run_case(loader: &Loader, name: String, text: String) -> Outcome {
    let loaded = panic::catch_unwind(AssertUnwindSafe(|| {
        loader.load(ResolvedSource::new(name, text))
    }));
    let loaded = match loaded {
        Err(payload) => return Outcome::new("panic_load", false, panic_text(&*payload)),
        Ok(Err(error)) => return load_error_outcome(&error),
        Ok(Ok(loaded)) => loaded,
    };
    let compiled = panic::catch_unwind(AssertUnwindSafe(|| {
        compile_loaded_definition(&loaded, CompileOptions::default())
    }));
    let compiled = match compiled {
        Err(payload) => return Outcome::new("panic_compile", false, panic_text(&*payload)),
        Ok(Err(error)) => {
            if let Some(diagnostic) = first_error(&error.diagnostics) {
                return Outcome::new(
                    "compile_error",
                    diagnostic.location.is_some(),
                    format!("[{}] {}", error.stage, one_line(&diagnostic.message)),
                );
            }
            let display = error.to_string();
            let located = has_position(&display, &format!("{error:?}"));
            return Outcome::new("compile_error", located, display);
        }
        Ok(Ok(compiled)) => compiled,
    };
    let checked = panic::catch_unwind(AssertUnwindSafe(|| {
        let kore = parse_definition(&compiled.definition_kore)
            .map_err(|error| ("kore_parse_error", error.to_string()))?;
        BackendDefinition::internalize(&kore, "MAIN")
            .map(|_| ())
            .map_err(|error| ("backend_error", error.to_string()))
    }));
    match checked {
        Err(payload) => Outcome::new("panic_backend", false, panic_text(&*payload)),
        Ok(Err((class, message))) => Outcome::new(class, false, message),
        Ok(Ok(())) => Outcome::new("pass", false, String::new()),
    }
}

fn first_line(text: &str) -> String {
    let line = text
        .lines()
        .find(|line| !line.trim().is_empty())
        .unwrap_or("");
    line.replace('\t', " ").chars().take(400).collect()
}

/// Compile the case at `path` and render its result line (without a trailing newline).
fn result_line(loader: &Loader, path: &Path, full_message: bool) -> String {
    let started = Instant::now();
    let outcome = match fs::read_to_string(path) {
        Ok(text) => {
            let name = path
                .file_name()
                .map_or_else(String::new, |name| name.to_string_lossy().into_owned());
            run_case(loader, name, text)
        }
        Err(error) => Outcome::new("harness_error", false, error.to_string()),
    };
    let ms = started.elapsed().as_secs_f64() * 1000.0;
    if full_message && !outcome.message.is_empty() {
        eprintln!("{}", outcome.message);
    }
    format!(
        "RESULT\t{}\t{}\t{ms:.1}\t{}",
        outcome.class,
        if outcome.located { "loc" } else { "noloc" },
        first_line(&outcome.message)
    )
}

fn case_mode(path: &Path, fresh: bool) {
    quiet_panics();
    let loader = Loader::new(fresh);
    println!("{}", result_line(&loader, path, true));
}

/// Read case paths from standard input and answer each with one result line. The worker exits
/// after reporting a panic, since the interrupted computation may have left shared state behind.
fn worker_mode(fresh: bool) -> io::Result<()> {
    quiet_panics();
    let loader = Loader::new(fresh);
    let mut stdout = io::stdout().lock();
    writeln!(stdout, "READY")?;
    stdout.flush()?;
    for path in io::stdin().lock().lines() {
        let line = result_line(&loader, Path::new(&path?), false);
        writeln!(stdout, "{line}")?;
        stdout.flush()?;
        if line.starts_with("RESULT\tpanic_") {
            break;
        }
    }
    Ok(())
}

struct Row {
    file: String,
    class: String,
    location: String,
    message: String,
    ms: f64,
    wall_ms: f64,
}

/// A live worker process and the threads that read its output.
struct Worker {
    child: Child,
    stdin: ChildStdin,
    lines: Receiver<String>,
    stderr_tail: Arc<Mutex<VecDeque<String>>>,
    stderr_reader: Option<JoinHandle<()>>,
}

impl Worker {
    fn spawn(exe: &Path, fresh: bool) -> io::Result<Self> {
        let mut command = Command::new("sh");
        command
            .arg("-c")
            .arg(format!(
                "ulimit -c 0; ulimit -v {WORKER_ADDRESS_SPACE_KIB}; exec \"$0\" worker \"$@\""
            ))
            .arg(exe);
        if fresh {
            command.arg("--fresh");
        }
        let mut child = command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        let stdin = child.stdin.take().expect("piped stdin");
        let stdout = child.stdout.take().expect("piped stdout");
        let mut stderr = child.stderr.take().expect("piped stderr");
        let (sender, lines) = mpsc::channel();
        thread::spawn(move || {
            for line in BufReader::new(stdout).lines() {
                let Ok(line) = line else { break };
                if sender.send(line).is_err() {
                    break;
                }
            }
        });
        let stderr_tail = Arc::new(Mutex::new(VecDeque::new()));
        let tail = Arc::clone(&stderr_tail);
        let stderr_reader = thread::spawn(move || {
            let mut bytes = Vec::new();
            let _ = stderr.read_to_end(&mut bytes);
            let mut tail = tail.lock().expect("stderr tail");
            for line in String::from_utf8_lossy(&bytes).lines() {
                if !line.trim().is_empty() {
                    tail.push_back(line.to_owned());
                    if tail.len() > 8 {
                        tail.pop_front();
                    }
                }
            }
        });
        let mut worker = Self {
            child,
            stdin,
            lines,
            stderr_tail,
            stderr_reader: Some(stderr_reader),
        };
        match worker.lines.recv_timeout(WORKER_STARTUP) {
            Ok(line) if line == "READY" => Ok(worker),
            other => {
                let (status, stderr) = worker.stop();
                Err(io::Error::other(format!(
                    "worker did not start ({other:?}, {status:?}): {stderr}"
                )))
            }
        }
    }

    /// Kill the process if it still runs, wait for it, and return its status with the last line
    /// it wrote to standard error.
    fn stop(&mut self) -> (Option<ExitStatus>, String) {
        let _ = self.child.kill();
        let status = self.child.wait().ok();
        if let Some(reader) = self.stderr_reader.take() {
            let _ = reader.join();
        }
        let last = self
            .stderr_tail
            .lock()
            .ok()
            .and_then(|tail| tail.back().cloned())
            .unwrap_or_default();
        (status, last)
    }
}

impl Drop for Worker {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Runs cases on one worker, replacing it whenever it panics, crashes, or times out.
struct Supervisor {
    exe: PathBuf,
    fresh: bool,
    timeout: Duration,
    worker: Option<Worker>,
}

impl Supervisor {
    fn run(&mut self, path: &Path) -> Row {
        let file = path
            .file_name()
            .map_or_else(String::new, |name| name.to_string_lossy().into_owned());
        let row = |class: &str, message: String, wall_ms: f64| Row {
            file: file.clone(),
            class: class.into(),
            location: "noloc".into(),
            message,
            ms: wall_ms,
            wall_ms,
        };
        let mut worker = match self.worker.take() {
            Some(worker) => worker,
            None => match Worker::spawn(&self.exe, self.fresh) {
                Ok(worker) => worker,
                Err(error) => return row("harness_error", first_line(&error.to_string()), 0.0),
            },
        };
        let started = Instant::now();
        let sent = writeln!(worker.stdin, "{}", path.display()).and_then(|()| worker.stdin.flush());
        let received = match sent {
            Ok(()) => worker.lines.recv_timeout(self.timeout),
            Err(_) => Err(RecvTimeoutError::Disconnected),
        };
        let wall_ms = started.elapsed().as_secs_f64() * 1000.0;
        match received {
            Ok(line) => {
                let fields: Vec<&str> = line.splitn(5, '\t').collect();
                if fields.len() < 5 || fields[0] != "RESULT" {
                    worker.stop();
                    return row("harness_error", first_line(&line), wall_ms);
                }
                if !fields[1].starts_with("panic_") {
                    self.worker = Some(worker);
                }
                Row {
                    file,
                    class: fields[1].into(),
                    location: fields[2].into(),
                    ms: fields[3].parse().unwrap_or(f64::NAN),
                    message: fields[4].into(),
                    wall_ms,
                }
            }
            Err(RecvTimeoutError::Timeout) => {
                worker.stop();
                row(
                    "timeout",
                    format!("exceeded {}s", self.timeout.as_secs_f64()),
                    wall_ms,
                )
            }
            Err(RecvTimeoutError::Disconnected) => {
                let (status, last) = worker.stop();
                let status = status.map_or_else(|| "unknown status".into(), |s| s.to_string());
                row("crash", first_line(&format!("{status}: {last}")), wall_ms)
            }
        }
    }
}

struct RunOptions {
    corpus: PathBuf,
    out: PathBuf,
    jobs: usize,
    timeout: Duration,
    fresh: bool,
}

fn percentile(sorted: &[f64], fraction: f64) -> f64 {
    if sorted.is_empty() {
        return f64::NAN;
    }
    let index = ((sorted.len() - 1) as f64 * fraction).round() as usize;
    sorted[index]
}

fn run_mode(options: RunOptions) -> io::Result<()> {
    let exe = env::current_exe()?;
    let mut files: Vec<PathBuf> = fs::read_dir(&options.corpus)?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|extension| extension == "k"))
        .collect();
    files.sort();
    let total = files.len();
    let queue = Arc::new(Mutex::new(
        files.into_iter().enumerate().rev().collect::<Vec<_>>(),
    ));
    let rows = Arc::new(Mutex::new(Vec::<(usize, Row)>::with_capacity(total)));
    let started = Instant::now();
    let threads: Vec<_> = (0..options.jobs.max(1))
        .map(|_| {
            let queue = Arc::clone(&queue);
            let rows = Arc::clone(&rows);
            let mut supervisor = Supervisor {
                exe: exe.clone(),
                fresh: options.fresh,
                timeout: options.timeout,
                worker: None,
            };
            thread::spawn(move || {
                loop {
                    let Some((index, path)) = queue.lock().expect("queue").pop() else {
                        break;
                    };
                    let row = supervisor.run(&path);
                    let mut rows = rows.lock().expect("rows");
                    rows.push((index, row));
                    if rows.len().is_multiple_of(250) {
                        eprintln!("{}/{total} cases", rows.len());
                    }
                }
            })
        })
        .collect();
    for thread in threads {
        thread.join().expect("replay thread");
    }
    let wall = started.elapsed().as_secs_f64();
    let mut rows = Arc::try_unwrap(rows)
        .ok()
        .expect("all replay threads joined")
        .into_inner()
        .expect("rows");
    rows.sort_by_key(|(index, _)| *index);
    let mut out = io::BufWriter::new(fs::File::create(&options.out)?);
    writeln!(out, "file\toutcome\tlocation\tfirst_line\tms\twall_ms")?;
    let mut counts = BTreeMap::<&str, usize>::new();
    let mut times = Vec::with_capacity(rows.len());
    for (_, row) in &rows {
        *counts.entry(row.class.as_str()).or_default() += 1;
        times.push(row.wall_ms);
        writeln!(
            out,
            "{}\t{}\t{}\t{}\t{:.1}\t{:.1}",
            row.file, row.class, row.location, row.message, row.ms, row.wall_ms
        )?;
    }
    out.flush()?;
    times.sort_by(f64::total_cmp);
    eprintln!(
        "{total} cases in {wall:.1}s with {} jobs; per case median {:.0} ms, p95 {:.0} ms",
        options.jobs,
        percentile(&times, 0.5),
        percentile(&times, 0.95)
    );
    for (class, count) in counts {
        eprintln!("  {class}: {count}");
    }
    Ok(())
}

fn usage() -> ! {
    eprintln!(
        "usage: generative-compile run CORPUS_DIR OUT.tsv [--jobs J] [--timeout SECS] [--fresh]\n\
         \x20      generative-compile case FILE.k [--fresh]\n\
         \x20      generative-compile worker [--fresh]"
    );
    std::process::exit(2)
}

fn main() -> io::Result<()> {
    let mut args = env::args().skip(1);
    let mode = args.next().unwrap_or_else(|| usage());
    let mut positional = Vec::new();
    let mut jobs = 8;
    let mut timeout = Duration::from_secs(10);
    let mut fresh = false;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--fresh" => fresh = true,
            "--jobs" => {
                jobs = args
                    .next()
                    .and_then(|value| value.parse().ok())
                    .unwrap_or_else(|| usage());
            }
            "--timeout" => {
                timeout = args
                    .next()
                    .and_then(|value| value.parse().ok())
                    .map(Duration::from_secs_f64)
                    .unwrap_or_else(|| usage());
            }
            _ if arg.starts_with("--") => usage(),
            _ => positional.push(arg),
        }
    }
    match (mode.as_str(), positional.as_slice()) {
        ("run", [corpus, out]) => run_mode(RunOptions {
            corpus: corpus.into(),
            out: out.into(),
            jobs,
            timeout,
            fresh,
        }),
        ("case", [path]) => {
            case_mode(Path::new(path), fresh);
            Ok(())
        }
        ("worker", []) => worker_mode(fresh),
        _ => usage(),
    }
}
