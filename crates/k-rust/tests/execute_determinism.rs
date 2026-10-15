//! An execution request on equal inputs gives an equal `ExecutionResult` on a fresh `Backend` and
//! on one that ran other requests before, in any process and on any thread
//! (`docs/compatibility.md`, "Determinism and concurrency").
//!
//! The fixture explores several paths: three rules match the initial `go`, later rules write a
//! `Map` with a fresh value and update a counter cell; a second program evaluates a strict
//! operator over integers. Every result is compared as its serialized JSON text, for strategy
//! `all`, in path-set and state-set modality, through `execute` and `execute_observed`. The
//! cross-process test detects a dependence on the hash seed or on addresses only with some
//! probability (two processes and this one may agree by chance), so one passing run is evidence,
//! not proof.

use std::{
    path::{Path, PathBuf},
    process::Command,
    sync::OnceLock,
};

use indoc::indoc;
use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionStrategy, ObservedRequest,
        ResultModalityOutput,
    },
    builtin::embedded,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ProgramGrammar,
        compile_loaded_definition,
    },
    kore::ast::Pattern,
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};

const DEFINITION: &str = indoc! {r#"
    module ND-SYNTAX
      imports INT-SYNTAX
      syntax Pgm ::= "go" | Exp
      syntax Exp ::= Int | Exp "+" Exp [left, strict]
    endmodule

    module ND
      imports ND-SYNTAX
      imports INT
      imports MAP
      syntax KItem ::= a(Int) | b(Int) | c(Int)
      syntax KResult ::= Int
      configuration <k> $PGM:Pgm </k> <m> .Map </m> <n> 0 </n>
      rule <k> go => a(1) </k>
      rule <k> go => a(2) </k>
      rule <k> go => b(3) </k>
      rule <k> a(I) => b(I +Int 10) </k> <m> M => M[I <- !N:Int] </m>
      rule <k> a(I) => c(I) </k> <n> N => N +Int I </n>
      rule <k> b(I) => c(I *Int 2) </k> <m> M => M[I <- I] </m>
      rule I1:Int + I2:Int => I1 +Int I2
    endmodule
"#};

const MAIN: &str = "ND";

/// The compiled definition's KORE and the initial states of the two programs, `go` and a sum.
struct Compiled {
    kore: String,
    states: Vec<Pattern>,
}

/// The fixture compiled once per process, with the embedded prelude, for the Rust backend.
fn compiled() -> &'static Compiled {
    static COMPILED: OnceLock<Compiled> = OnceLock::new();
    COMPILED.get_or_init(|| {
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let (loaded, syntax) = load_for_compilation(
            ResolvedSource::new("nd.k", DEFINITION),
            MAIN,
            Some("ND-SYNTAX"),
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![
                    embedded("prelude.md").expect("the embedded prelude exists"),
                ],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust.excluded_module_attribute().into(),
                ],
                ..LoadOptions::default()
            },
        )
        .expect("the fixture loads");
        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
            .expect("the fixture compiles");
        let grammar = ProgramGrammar::new(loaded.definition()).expect("the program grammar builds");
        let states = ["go", "1 + 2 + 3"]
            .into_iter()
            .map(|program| {
                let mut assembler = ConfigurationAssembler::new(
                    &grammar,
                    MAIN,
                    syntax.clone(),
                    &artifacts.configuration_variables,
                );
                assembler
                    .program(&Sort::new("Pgm"), program)
                    .expect("the program parses");
                assembler
                    .finish()
                    .expect("the initial configuration assembles")
            })
            .collect();
        Compiled {
            kore: artifacts.definition_kore,
            states,
        }
    })
}

fn backend() -> Backend {
    Backend::new(&compiled().kore, MAIN, BackendOptions::default()).expect("the backend loads")
}

/// The serialized results of every request of the contract on `backend`, in a fixed order:
/// each program, in path-set and state-set modality, through `execute` and through
/// `execute_observed` with every rule observed.
fn results(backend: &mut Backend) -> Vec<String> {
    let mut results = Vec::new();
    for state in &compiled().states {
        for modality in [
            ResultModalityOutput::PathSet,
            ResultModalityOutput::StateSet,
        ] {
            let request = || ExecuteRequest {
                strategy: ExecutionStrategy::All,
                result_modality: modality,
                ..ExecuteRequest::new(state.clone())
            };
            let executed = backend.execute(request()).expect("the request executes");
            let observed = backend
                .execute_observed(ObservedRequest {
                    request: request(),
                    rules: None,
                })
                .expect("the observed request executes");
            for result in [executed, observed] {
                results.push(serde_json::to_string(&result).expect("the result serializes"));
            }
        }
    }
    results
}

/// A request outside the contract's list, run between two rounds on a reused backend: any
/// history it leaves in the backend would show in the next round.
fn another_request(backend: &mut Backend) {
    backend
        .execute(ExecuteRequest {
            strategy: ExecutionStrategy::Any,
            max_depth: Some(1),
            ..ExecuteRequest::new(compiled().states[0].clone())
        })
        .expect("the other request executes");
}

#[test]
fn execute_results_are_equal_across_runs_and_backends() {
    let expected = results(&mut backend());
    // The fixture explores several paths, so the comparison is not of a single leaf.
    let leaves = serde_json::from_str::<serde_json::Value>(&expected[0])
        .expect("the result is JSON")["leaves"]
        .as_array()
        .map_or(0, Vec::len);
    assert!(
        leaves > 1,
        "the path-set result of `go` has {leaves} leaves"
    );
    for round in 0..3 {
        assert!(
            results(&mut backend()) == expected,
            "fresh backend {round} gave other results"
        );
    }
    let mut reused = backend();
    for round in 0..3 {
        assert!(
            results(&mut reused) == expected,
            "round {round} on a reused backend gave other results"
        );
        another_request(&mut reused);
    }
}

#[test]
fn execute_results_are_equal_across_threads() {
    let expected = results(&mut backend());
    let threads = std::thread::scope(|scope| {
        let runs = (0..4)
            .map(|_| scope.spawn(|| results(&mut backend())))
            .collect::<Vec<_>>();
        runs.into_iter()
            .map(|run| run.join().expect("a thread does not panic"))
            .collect::<Vec<_>>()
    });
    for (thread, results) in threads.iter().enumerate() {
        assert!(*results == expected, "thread {thread} gave other results");
    }
}

/// The variable naming the file a child process writes its results to; the child does nothing
/// without it.
const CHILD_FILE: &str = "K_RUST_TEST_EXECUTE_DETERMINISM_FILE";

/// The results as one text, one serialized result per line.
fn results_text(backend: &mut Backend) -> String {
    results(backend).join("\n")
}

/// The work of a child process of [`execute_results_are_identical_across_processes`]: writes the
/// results of a fresh backend. It does nothing unless that test runs it.
#[test]
fn execute_determinism_child() {
    let Some(file) = std::env::var_os(CHILD_FILE) else {
        return;
    };
    std::fs::write(Path::new(&file), results_text(&mut backend()))
        .expect("the child writes its results");
}

/// Two child processes of this test binary, whose hash seeds and address layouts differ, write
/// byte for byte the results this process computes.
#[test]
fn execute_results_are_identical_across_processes() {
    /// Removes the children's directory however the test ends.
    struct Remove(PathBuf);
    impl Drop for Remove {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let root =
        std::env::temp_dir().join(format!("k-rust-execute-determinism-{}", std::process::id()));
    std::fs::create_dir_all(&root).expect("the children's directory is created");
    let _remove = Remove(root.clone());
    let expected = results_text(&mut backend());
    for child in ["first", "second"] {
        let file = root.join(child);
        let output = Command::new(std::env::current_exe().expect("the test binary is known"))
            .args(["--exact", "execute_determinism_child", "--nocapture"])
            .args(["--test-threads", "1"])
            .env(CHILD_FILE, &file)
            .output()
            .expect("the test binary re-runs itself");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success() && stdout.contains("1 passed"),
            "the {child} child failed ({}):\n{stdout}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
        let written = std::fs::read_to_string(&file).expect("the child wrote its results");
        assert!(
            written == expected,
            "the {child} child wrote other bytes than this process computes"
        );
    }
}
