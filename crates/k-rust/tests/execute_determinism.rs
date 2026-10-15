//! An execution request on equal inputs gives an equal `ExecutionResult` on a fresh `Backend` and
//! on one that ran other requests before, in any process and on any thread
//! (`docs/compatibility.md`, "Determinism and concurrency").
//!
//! The fixture explores several paths: three rules match the initial `go`, later rules write a
//! `Map` with a fresh value and update a counter cell; `conv` has two paths that end in one
//! configuration, so the state-set result merges them; a sum evaluates a strict operator over
//! integers; and a symbolic integer branches on its sign, which the Z3 build decides with the
//! solver and the portable build leaves undecided. Every result is compared as its serialized
//! JSON text, for strategy `all`, in path-set and state-set modality, through `execute`,
//! `execute_observed` and `execute_observed_to_writer`. The cross-process test detects a
//! dependence on the hash seed or on addresses only with some probability (two processes and
//! this one may agree by chance), so one passing run is evidence, not proof.

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
    kore::{ast::Pattern, parser::parse_pattern, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};

const DEFINITION: &str = indoc! {r#"
    module ND-SYNTAX
      imports INT-SYNTAX
      syntax Pgm ::= "go" | "conv" | Exp
      syntax Exp ::= Int | Exp "+" Exp [left, strict]
    endmodule

    module ND
      imports ND-SYNTAX
      imports INT
      imports MAP
      syntax KItem ::= a(Int) | b(Int) | c(Int) | "left" | "right" | "done" | "pos" | "nonpos"
      syntax KResult ::= Int
      configuration <k> $PGM:Pgm </k> <m> .Map </m> <n> 0 </n>
      rule <k> go => a(1) </k>
      rule <k> go => a(2) </k>
      rule <k> go => b(3) </k>
      rule <k> a(I) => b(I +Int 10) </k> <m> M => M[I <- !N:Int] </m>
      rule <k> a(I) => c(I) </k> <n> N => N +Int I </n>
      rule <k> b(I) => c(I *Int 2) </k> <m> M => M[I <- I] </m>
      rule <k> conv => left </k>
      rule <k> conv => right </k>
      rule <k> left => done </k>
      rule <k> right => done </k>
      rule I1:Int + I2:Int => I1 +Int I2
      rule <k> I:Int => pos </k> requires I >Int 0
      rule <k> I:Int => nonpos </k> requires I <=Int 0
    endmodule
"#};

const MAIN: &str = "ND";

/// The compiled definition's KORE and the initial states of the programs: `go`, `conv`, a sum,
/// and a symbolic integer.
struct Compiled {
    kore: String,
    states: Vec<Pattern>,
}

/// Index of `go` and of `conv` in [`Compiled::states`].
const GO: usize = 0;
const CONV: usize = 1;

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
        let state = |program: &str| {
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
        };
        let mut states = ["go", "conv", "1 + 2 + 3"].map(state).to_vec();
        // The symbolic state: the program `7` with its integer replaced by a variable.
        let literal = Printer::compact().print_pattern(&state("7"));
        let symbolic = literal.replace(r#"\dv{SortInt{}}("7")"#, "VarX:SortInt{}");
        assert_ne!(symbolic, literal, "the program's integer is a domain value");
        states.push(parse_pattern(&symbolic).expect("the symbolic state parses"));
        Compiled {
            kore: artifacts.definition_kore,
            states,
        }
    })
}

fn backend() -> Backend {
    Backend::new(&compiled().kore, MAIN, BackendOptions::default()).expect("the backend loads")
}

/// How a request is made.
#[derive(Clone, Copy)]
enum Entry {
    Execute,
    Observed,
    Writer,
}

/// One request of the contract: a program, a modality, an entry point and a work budget.
#[derive(Clone, Copy)]
struct Request {
    state: usize,
    modality: ResultModalityOutput,
    entry: Entry,
    max_work: Option<u64>,
}

/// The work budget of the budgeted requests: below the count of `go`'s run, so they end with a
/// `work-bound` leaf.
const BUDGET: u64 = 4;

/// Every request of the contract, in a fixed order.
fn requests() -> Vec<Request> {
    let mut requests = Vec::new();
    for state in 0..compiled().states.len() {
        for modality in [
            ResultModalityOutput::PathSet,
            ResultModalityOutput::StateSet,
        ] {
            for entry in [Entry::Execute, Entry::Observed, Entry::Writer] {
                requests.push(Request {
                    state,
                    modality,
                    entry,
                    max_work: None,
                });
                // A run the work budget stops is covered by the contract too.
                if state == GO {
                    requests.push(Request {
                        state,
                        modality,
                        entry,
                        max_work: Some(BUDGET),
                    });
                }
            }
        }
    }
    requests
}

/// The serialized result of `request` on `backend`.
fn run(backend: &mut Backend, request: Request) -> String {
    let execute = ExecuteRequest {
        strategy: ExecutionStrategy::All,
        result_modality: request.modality,
        max_work: request.max_work,
        ..ExecuteRequest::new(compiled().states[request.state].clone())
    };
    let observed = ObservedRequest {
        request: execute.clone(),
        rules: None,
    };
    let serialized = match request.entry {
        Entry::Execute => serde_json::to_string(&backend.execute(execute).expect("it executes")),
        Entry::Observed => serde_json::to_string(
            &backend
                .execute_observed(observed)
                .expect("it executes observed"),
        ),
        Entry::Writer => {
            let mut written = Vec::new();
            backend
                .execute_observed_to_writer(observed, &mut written)
                .expect("it writes");
            return String::from_utf8(written).expect("the written result is UTF-8");
        }
    };
    serialized.expect("the result serializes")
}

/// The results of every request in order on one backend.
fn results(backend: &mut Backend) -> Vec<String> {
    requests()
        .into_iter()
        .map(|request| run(backend, request))
        .collect()
}

/// The result of every request, each on a backend of its own that ran nothing before.
fn fresh_results() -> Vec<String> {
    requests()
        .into_iter()
        .map(|request| run(&mut backend(), request))
        .collect()
}

/// A request outside the contract's list, run between two rounds on a reused backend: any
/// history it leaves in the backend would show in the next round.
fn another_request(backend: &mut Backend) {
    backend
        .execute(ExecuteRequest {
            strategy: ExecutionStrategy::Any,
            max_depth: Some(1),
            ..ExecuteRequest::new(compiled().states[GO].clone())
        })
        .expect("the other request executes");
}

/// The number of leaves of the result of `state` in `modality`, run on a fresh backend.
fn leaves(state: usize, modality: ResultModalityOutput) -> usize {
    let text = run(
        &mut backend(),
        Request {
            state,
            modality,
            entry: Entry::Execute,
            max_work: None,
        },
    );
    serde_json::from_str::<serde_json::Value>(&text).expect("the result is JSON")["leaves"]
        .as_array()
        .map_or(0, Vec::len)
}

/// Each request on a fresh backend gives the result it gives in every round on one reused
/// backend, with another request between rounds.
#[test]
fn execute_results_are_equal_across_runs_and_backends() {
    // The fixture explores several paths, and `conv`'s converge, so state-set merges them.
    let go = leaves(GO, ResultModalityOutput::PathSet);
    assert!(go > 1, "the path-set result of `go` has {go} leaves");
    let (paths, states) = (
        leaves(CONV, ResultModalityOutput::PathSet),
        leaves(CONV, ResultModalityOutput::StateSet),
    );
    assert!(
        states < paths,
        "`conv`: {states} state-set leaves against {paths} path-set leaves"
    );
    // The budgeted requests stop: `work` is the budget and the last leaf is `work-bound`.
    let budgeted = run(
        &mut backend(),
        Request {
            state: GO,
            modality: ResultModalityOutput::PathSet,
            entry: Entry::Execute,
            max_work: Some(BUDGET),
        },
    );
    let budgeted =
        serde_json::from_str::<serde_json::Value>(&budgeted).expect("the result is JSON");
    assert_eq!(budgeted["work"], BUDGET);
    let last = budgeted["leaves"]
        .as_array()
        .and_then(|leaves| leaves.last());
    assert_eq!(
        last.map(|leaf| &leaf["reason"]),
        Some(&serde_json::json!("work-bound"))
    );
    let expected = fresh_results();
    let mut reused = backend();
    for round in 0..3 {
        for (index, (result, fresh)) in results(&mut reused).iter().zip(&expected).enumerate() {
            assert!(
                result == fresh,
                "round {round}, request {index}: a reused backend gave another result than a fresh one"
            );
        }
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
