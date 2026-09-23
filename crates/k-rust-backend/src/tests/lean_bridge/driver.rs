//! The generic driver of the Lean model conformance bridge.
//!
//! A check names a model of `lean/KRustBridge/Dispatch.lean`, a proptest strategy, an encoder
//! from a case to the model's input JSON, and the Rust answer as JSON in the shape the model
//! prints. Every case goes through one `krust-bridge` process as one request line,
//! `{"id": n, "model": m, "input": x}`; the answers come back in input order as
//! `{"id": n, "output": y}` and are compared with the Rust answers as JSON values. A divergence
//! is shrunk with proptest's `simplify`/`complicate` loop, one process per candidate, and the
//! smallest diverging case is reported.
//!
//! Environment: `K_RUST_LEAN_BRIDGE=1` runs the checks (unset, empty or `0` skips them, any other
//! value is an error); `K_RUST_LEAN_BRIDGE_CASES` sets the number of cases (default 4096); `LAKE`
//! names the `lake` executable (default `lake`, as in `scripts/lean-check.sh`).

use std::{
    io::{BufRead, BufReader, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::OnceLock,
    time::Instant,
};

use proptest::{
    strategy::{Strategy, ValueTree},
    test_runner::{Config, RngAlgorithm, TestRng, TestRunner},
};
use serde_json::{Value, json};

const DEFAULT_CASES: usize = 4096;
const SHRINK_STEPS: usize = 2048;

fn enabled() -> bool {
    match std::env::var("K_RUST_LEAN_BRIDGE") {
        Err(std::env::VarError::NotPresent) => false,
        Ok(value) if value.is_empty() || value == "0" => false,
        Ok(value) if value == "1" => true,
        other => panic!("K_RUST_LEAN_BRIDGE must be unset, 0 or 1, not {other:?}"),
    }
}

fn cases() -> usize {
    std::env::var("K_RUST_LEAN_BRIDGE_CASES").map_or(DEFAULT_CASES, |cases| {
        cases
            .parse()
            .expect("K_RUST_LEAN_BRIDGE_CASES is a case count")
    })
}

fn lean_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean")
}

/// `lake build krust-bridge` once per test process, so that an edit of a model is picked up, and
/// the path of the built executable.
fn executable() -> &'static Path {
    static EXECUTABLE: OnceLock<PathBuf> = OnceLock::new();
    EXECUTABLE.get_or_init(|| {
        let lake = std::env::var("LAKE").unwrap_or_else(|_| "lake".to_owned());
        let dir = lean_dir();
        let started = Instant::now();
        let status = Command::new(&lake)
            .args(["build", "krust-bridge"])
            .current_dir(&dir)
            .status()
            .unwrap_or_else(|error| {
                panic!("K_RUST_LEAN_BRIDGE=1 but `{lake}` could not be started: {error}")
            });
        assert!(
            status.success(),
            "`{lake} build krust-bridge` failed in {}",
            dir.display()
        );
        eprintln!(
            "lean bridge: lake build krust-bridge {:?}",
            started.elapsed()
        );
        dir.join(".lake/build/bin/krust-bridge")
    })
}

/// Send every input as one request through a single process and return the outputs in order.
fn run(model: &str, inputs: &[Value]) -> Vec<Value> {
    let mut child = Command::new(executable())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("the krust-bridge executable should start");
    let mut stdin = child.stdin.take().expect("piped stdin");
    let requests = inputs
        .iter()
        .enumerate()
        .map(|(id, input)| json!({ "id": id, "model": model, "input": input }).to_string() + "\n")
        .collect::<String>();
    // A writer thread, so that a full stdout pipe cannot deadlock against a full stdin pipe.
    let writer = std::thread::spawn(move || {
        stdin
            .write_all(requests.as_bytes())
            .expect("krust-bridge should read its input");
    });
    let outputs = BufReader::new(child.stdout.take().expect("piped stdout"))
        .lines()
        .enumerate()
        .map(|(id, line)| {
            let line = line.expect("krust-bridge output is UTF-8");
            let mut answer: Value =
                serde_json::from_str(&line).expect("krust-bridge output is JSON");
            assert_eq!(answer["id"], json!(id), "answers come back in input order");
            assert!(
                answer.get("error").is_none(),
                "model {model} rejected case {id}: {answer}"
            );
            answer
                .get_mut("output")
                .map(Value::take)
                .unwrap_or_else(|| panic!("model {model}: answer without output: {line}"))
        })
        .collect::<Vec<_>>();
    writer.join().expect("writer thread");
    assert!(child.wait().expect("krust-bridge exit").success());
    assert_eq!(outputs.len(), inputs.len(), "one answer per case");
    outputs
}

/// Check the Lean model `model` against `rust` on `cases()` values of `strategy`.
///
/// Returns the Rust answers, so that a caller can check that the generator reached the cases it
/// is meant to reach, or `None` when the bridge is switched off.
pub(super) fn check<S>(
    model: &str,
    strategy: S,
    encode: impl Fn(&S::Value) -> Value,
    rust: impl Fn(&S::Value) -> Value,
) -> Option<Vec<Value>>
where
    S: Strategy,
{
    if !enabled() {
        eprintln!(
            "skipped: set K_RUST_LEAN_BRIDGE=1 to run the Lean model {model} against the Rust"
        );
        return None;
    }
    let cases = cases();
    executable();

    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    let started = Instant::now();
    let mut trees = (0..cases)
        .map(|_| strategy.new_tree(&mut runner).expect("a case"))
        .collect::<Vec<_>>();
    let values = trees.iter().map(ValueTree::current).collect::<Vec<_>>();
    let inputs = values.iter().map(&encode).collect::<Vec<_>>();
    let expected = values.iter().map(&rust).collect::<Vec<_>>();
    let rust_side = started.elapsed();

    let started = Instant::now();
    let outputs = run(model, &inputs);
    let lean_side = started.elapsed();

    if let Some(id) = (0..cases).find(|&id| outputs[id] != expected[id]) {
        let diverges = |value: &S::Value| run(model, &[encode(value)]).remove(0) != rust(value);
        let started = Instant::now();
        let tree = &mut trees[id];
        let mut smallest = tree.current();
        let mut steps = 0;
        if tree.simplify() {
            while steps < SHRINK_STEPS {
                steps += 1;
                let candidate = tree.current();
                if diverges(&candidate) {
                    smallest = candidate;
                    if !tree.simplify() {
                        break;
                    }
                } else if !tree.complicate() {
                    break;
                }
            }
        }
        let input = encode(&smallest);
        let lean = run(model, std::slice::from_ref(&input)).remove(0);
        panic!(
            "model {model}: case {id} of {cases} diverges; shrunk in {steps} steps ({:?}) to\n\
             input: {input}\nlean:  {lean}\nrust:  {}",
            started.elapsed(),
            rust(&smallest)
        );
    }
    eprintln!(
        "lean bridge: model {model}, {cases} cases agree; rust generate+answer {rust_side:?}, \
         lean batch {lean_side:?}"
    );
    Some(expected)
}
