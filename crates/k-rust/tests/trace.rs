#![cfg(feature = "cli")]

use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

use serde_json::Value;

fn fixture() -> (PathBuf, PathBuf) {
    static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
    let nonce = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
    let root = std::env::temp_dir().join(format!("k-rust-trace-{}-{nonce}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let definition = root.join("definition.k");
    fs::write(
        &definition,
        r#"
module MAIN
  imports INT
  syntax Input ::= Int | "twice" "(" Int ")" [macro]
  rule twice(I) => I +Int I
  configuration <k> $PGM:Input </k>
endmodule
"#,
    )
    .unwrap();
    (root, definition)
}

fn run(command: &mut Command) -> Output {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

fn read_trace(path: &Path) -> Vec<Value> {
    serde_json::from_str(&fs::read_to_string(path).unwrap()).unwrap()
}

fn algorithm_ids(events: &[Value]) -> Vec<&str> {
    events
        .iter()
        .filter(|event| event["ph"] == "B" && event["name"] == "algo")
        .filter_map(|event| event["args"]["id"].as_str())
        .collect()
}

fn assert_trace_contract(events: &[Value]) -> Vec<String> {
    assert!(events.iter().any(|event| {
        event["ph"] == "i"
            && event["args"]["aggregation_rule"]
                == "per algorithm id: invocation count, total and self duration; counter deltas summed across invocations"
    }));

    let mut stacks = BTreeMap::<u64, Vec<String>>::new();
    let mut phase_names = Vec::new();
    let mut algorithm_count = 0;
    let mut algorithm_with_work = 0;
    for event in events {
        let Some(thread) = event["tid"].as_u64() else {
            continue;
        };
        let Some(kind) = event["ph"].as_str() else {
            continue;
        };
        let Some(name) = event["name"].as_str() else {
            continue;
        };
        let stack = stacks.entry(thread).or_default();
        match kind {
            "B" => {
                if name == "phase" {
                    phase_names.push(event["args"]["name"].as_str().unwrap().to_owned());
                } else if name == "algo" {
                    algorithm_count += 1;
                    assert!(
                        event["args"]["id"].as_str().unwrap().contains('.'),
                        "{event}"
                    );
                    assert!(stack.iter().any(|ancestor| ancestor == "phase"), "{event}");
                }
                stack.push(name.to_owned());
            }
            "E" => {
                assert_eq!(stack.pop().as_deref(), Some(name), "{event}");
                if name == "algo" {
                    let counters: Value =
                        serde_json::from_str(event["args"]["counters"].as_str().unwrap()).unwrap();
                    let counters = counters.as_object().unwrap();
                    assert!(counters.values().all(Value::is_u64), "{event}");
                    algorithm_with_work += usize::from(!counters.is_empty());
                }
            }
            _ => {}
        }
    }
    assert!(stacks.values().all(Vec::is_empty), "{stacks:?}");
    assert!(algorithm_count > 0);
    assert!(algorithm_with_work > 0);
    phase_names
}

fn normalize_timing_bytes(path: &Path) -> String {
    let contents = fs::read_to_string(path).unwrap();
    serde_json::from_str::<Value>(&contents).unwrap();
    // Independent wall-clock observations necessarily differ. Everything but those observations,
    // including field order and phase order, must remain byte-equivalent after normalization.
    contents
        .lines()
        .map(|line| {
            let trimmed = line.trim_start();
            let Some(after_quote) = trimmed.strip_prefix('"') else {
                return line.to_owned();
            };
            let Some(name_end) = after_quote.find('"') else {
                return line.to_owned();
            };
            let name = &after_quote[..name_end];
            if name != "seconds" && !name.ends_with("_seconds") {
                return line.to_owned();
            }
            let value_start = line.find(": ").unwrap() + 2;
            format!(
                "{}0{}",
                &line[..value_start],
                if trimmed.ends_with(',') { "," } else { "" }
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn assert_timing_contract_equal(left: &Path, right: &Path) {
    assert_eq!(normalize_timing_bytes(left), normalize_timing_bytes(right));
}

#[test]
fn krun_trace_nests_algorithms_under_named_phases() {
    let (root, definition) = fixture();
    let timings = root.join("timings.json");
    let trace = root.join("trace.json");
    let output = run(Command::new(env!("CARGO_BIN_EXE_krust")).args([
        "krun",
        definition.to_str().unwrap(),
        "--main-module",
        "MAIN",
        "--sort",
        "Input",
        "--expression",
        "twice(21)",
        "--depth",
        "1",
        "--timings",
        timings.to_str().unwrap(),
        "--trace",
        trace.to_str().unwrap(),
    ]));
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains(r#"\dv{SortInt{}}("42")"#)
    );

    let events = read_trace(&trace);
    let ids = algorithm_ids(&events);
    assert!(ids.contains(&"parser.grammar.build"), "{ids:?}");
    assert!(ids.contains(&"parser.earley.recognize"), "{ids:?}");
    let phases = assert_trace_contract(&events);
    assert_eq!(
        &phases[phases.len() - 5..],
        [
            "program_parse",
            "config_vars_parse",
            "internalize",
            "execute",
            "output",
        ]
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn kprove_trace_preserves_timings_and_counters() {
    let (root, definition) = fixture();
    fs::write(
        &definition,
        r#"
module MAIN
  syntax State ::= "a" [symbol(a)] | "b" [symbol(b)] | "c" [symbol(c)]
  configuration <k> $PGM:State </k>
  rule <k> a => b </k>
  claim <k> a => b #Or c </k> [label(reaches-b-or-c)]
endmodule
"#,
    )
    .unwrap();
    let compiled = root.join("compiled");
    run(Command::new(env!("CARGO_BIN_EXE_krust")).args([
        "kcompile",
        definition.to_str().unwrap(),
        "--main-module",
        "MAIN",
        "--output-directory",
        compiled.to_str().unwrap(),
        "--for-proving",
    ]));

    let baseline_timings = root.join("baseline-timings.json");
    let baseline_counters = root.join("baseline-counters.json");
    let baseline = run(Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--claim",
            "reaches-b-or-c",
            "--depth",
            "10",
            "--timings",
            baseline_timings.to_str().unwrap(),
        ])
        .env("KRUST_COUNTERS", &baseline_counters));

    let traced_timings = root.join("traced-timings.json");
    let traced_counters = root.join("traced-counters.json");
    let trace = root.join("trace.json");
    let traced = run(Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kprove",
            "--compiled-definition",
            compiled.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--claim",
            "reaches-b-or-c",
            "--depth",
            "10",
            "--timings",
            traced_timings.to_str().unwrap(),
            "--trace",
            trace.to_str().unwrap(),
        ])
        .env("KRUST_COUNTERS", &traced_counters));
    assert_eq!(traced.stdout, baseline.stdout);
    assert_eq!(traced.stderr, baseline.stderr);
    assert_eq!(
        fs::read(&traced_counters).unwrap(),
        fs::read(&baseline_counters).unwrap()
    );
    assert_timing_contract_equal(&traced_timings, &baseline_timings);

    let phases = assert_trace_contract(&read_trace(&trace));
    assert_eq!(phases, ["input", "internalize", "proof_setup", "proof"]);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn an_uncreatable_trace_path_is_a_cli_error() {
    let (root, definition) = fixture();
    let output = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            definition.to_str().unwrap(),
            "--main-module",
            "MAIN",
            "--sort",
            "Input",
            "--expression",
            "0",
            "--trace",
            root.join("missing/trace.json").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(!output.status.success());
    assert!(stderr.contains("could not create trace file"), "{stderr}");
    assert!(!stderr.contains("panicked"), "{stderr}");
    fs::remove_dir_all(root).unwrap();
}
