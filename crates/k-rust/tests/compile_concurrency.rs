//! A loaded definition can be relinked and compiled from several threads at once, and each
//! concurrent call returns what the same call returns alone (`docs/compatibility.md`,
//! "Determinism and concurrency", Concurrency).
//!
//! The concurrent comparison catches shared mutable state on the compile path only when a race
//! happens to show in a run, so a passing run is evidence, not proof; new statics on the path
//! still need review. Run it with the default (`cli`) features too, which add MPFR's Float
//! folding (`folded_floats_compile_concurrently_as_alone`); `concurrent_compiles_stress` repeats
//! the concurrent comparison and is ignored by default.

use std::sync::{Arc, Barrier};

use indoc::indoc;
use k_rust::{
    backend::Backend,
    builtin::embedded,
    definition::Definition,
    kompile::{
        CompilationBackend, CompileError, CompileOptions, CompiledKoreArtifacts,
        compile_loaded_definition,
    },
    outer::{LoadError, LoadOptions, LoadedDefinition, ResolvedSource, load_with_options},
};

/// A small language: strict operators, a configuration with a `Map` cell, functions, and an
/// `owise` rule.
const CALC: &str = indoc! {r#"
    module CALC-SYNTAX
      imports INT-SYNTAX
      imports ID-SYNTAX
      syntax Exp ::= Int | Id
                   | Exp "+" Exp [left, strict]
                   | Exp "*" Exp [left, strict]
                   | "let" Id "=" Exp "in" Exp [strict(2)]
    endmodule

    module CALC
      imports CALC-SYNTAX
      imports DOMAINS
      syntax KResult ::= Int
      configuration <T> <k> $PGM:Exp </k> <env> .Map </env> </T>
      rule I1:Int + I2:Int => I1 +Int I2
      rule I1:Int * I2:Int => I1 *Int I2
      rule <k> X:Id => I ...</k> <env>... X |-> I ...</env>
      rule <k> let X = I:Int in E => E ...</k> <env> M => M[X <- I] </env>
      syntax Int ::= double(Int) [function]
      rule double(I) => I *Int 2
      syntax Bool ::= small(Int) [function]
      rule small(I) => true requires I <Int 10
      rule small(_) => false [owise]
    endmodule
"#};

/// One-rule mutants of [`CALC`]: each replaces one rule's right-hand side.
const MUTATIONS: [(&str, &str); 4] = [
    ("I1 +Int I2", "I1 -Int I2"),
    ("I1 *Int I2", "I1 +Int I2"),
    ("I *Int 2", "I *Int 3"),
    ("=> true requires", "=> false requires"),
];

/// A mutant that loads and fails to compile: a strict production whose result sort has no sort
/// predicate, which heating and cooling need.
const FAILING_MUTATION: (&str, &str) = (
    "  syntax Int ::= double(Int) [function]",
    "  syntax 8\n  syntax Exp ::= bad(Exp) [strict, result(8)]\n  syntax Int ::= double(Int) [function]",
);

fn load(text: &str) -> LoadedDefinition {
    let prelude = embedded("prelude.md").expect("the embedded prelude exists");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
        ResolvedSource::new("calc.k", text),
        "CALC",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .expect("the definition loads")
}

/// The definition of [`CALC`] with `from` replaced by `to` once, as a host's edit of the
/// baseline's `Definition` would give it.
fn mutant(from: &str, to: &str) -> Definition {
    let text = CALC.replacen(from, to, 1);
    assert_ne!(text, CALC, "the mutation site {from:?} exists");
    load(&text).definition().clone()
}

/// `mutant` relinked against `baseline` and compiled.
fn relink_and_compile(
    baseline: &LoadedDefinition,
    mutant: &Definition,
) -> Result<CompiledKoreArtifacts, CompileError> {
    let relinked = baseline
        .with_definition(mutant.clone())
        .expect("the mutant relinks");
    compile_loaded_definition(&relinked, CompileOptions::default())
}

#[test]
fn compile_inputs_and_outputs_are_send_and_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    fn assert_send<T: Send>() {}
    assert_send_sync::<LoadedDefinition>();
    assert_send_sync::<Definition>();
    assert_send_sync::<CompileOptions>();
    assert_send_sync::<CompiledKoreArtifacts>();
    assert_send::<CompileError>();
    assert_send::<LoadError>();
    assert_send::<Backend>();
}

/// Eight threads share one baseline, and each relinks and compiles every mutant, in an order of
/// its own; every result equals the sequential compile of that mutant.
#[test]
fn concurrent_relinks_and_compiles_of_one_baseline_return_the_sequential_artifacts() {
    let baseline = Arc::new(load(CALC));
    let mutants = MUTATIONS
        .iter()
        .map(|(from, to)| mutant(from, to))
        .collect::<Vec<_>>();
    let sequential = mutants
        .iter()
        .map(|mutant| relink_and_compile(&baseline, mutant).expect("the mutant compiles"))
        .collect::<Vec<_>>();
    std::thread::scope(|scope| {
        let threads = (0..8)
            .map(|thread| {
                let baseline = Arc::clone(&baseline);
                let mutants = &mutants;
                scope.spawn(move || {
                    let mut order = (0..mutants.len())
                        .map(|index| (index + thread) % mutants.len())
                        .collect::<Vec<_>>();
                    if thread % 2 == 1 {
                        order.reverse();
                    }
                    order
                        .into_iter()
                        .map(|index| {
                            let artifacts = relink_and_compile(&baseline, &mutants[index])
                                .expect("the mutant compiles");
                            (index, artifacts)
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect::<Vec<_>>();
        for (thread, handle) in threads.into_iter().enumerate() {
            for (index, artifacts) in handle.join().expect("a thread does not panic") {
                assert!(
                    artifacts == sequential[index],
                    "thread {thread}: mutant {index} compiled other artifacts"
                );
            }
        }
    });
}

/// A mutant that relinks and fails to compile fails with an equal error on four threads at once
/// and alone.
#[test]
fn a_failing_compile_fails_identically_on_every_thread() {
    let baseline = Arc::new(load(CALC));
    let failing = mutant(FAILING_MUTATION.0, FAILING_MUTATION.1);
    let sequential =
        relink_and_compile(&baseline, &failing).expect_err("the failing mutant does not compile");
    assert_eq!(
        sequential.stage, "resolve heat/cool attributes",
        "{sequential}"
    );
    std::thread::scope(|scope| {
        let threads = (0..4)
            .map(|_| {
                let baseline = Arc::clone(&baseline);
                let failing = &failing;
                scope.spawn(move || relink_and_compile(&baseline, failing))
            })
            .collect::<Vec<_>>();
        for (thread, handle) in threads.into_iter().enumerate() {
            let error = handle
                .join()
                .expect("a thread does not panic")
                .expect_err("the failing mutant does not compile");
            assert!(error == sequential, "thread {thread} failed differently");
        }
    });
}

/// Eight threads compile one shared baseline and one shared relinked mutant at once, before any
/// compile has filled the lazy tables they share, and every result equals the compile of a fresh
/// load.
#[test]
fn concurrent_compiles_of_one_shared_loaded_definition_return_the_fresh_artifacts() {
    let mutation = mutant(MUTATIONS[0].0, MUTATIONS[0].1);
    let fresh_baseline =
        compile_loaded_definition(&load(CALC), CompileOptions::default()).expect("it compiles");
    let fresh_mutant = relink_and_compile(&load(CALC), &mutation).expect("it compiles");
    let baseline = Arc::new(load(CALC));
    let relinked = Arc::new(
        baseline
            .with_definition(mutation)
            .expect("the mutant relinks"),
    );
    let start = Barrier::new(8);
    std::thread::scope(|scope| {
        let threads = (0..8)
            .map(|thread| {
                let (baseline, relinked, start) = (&baseline, &relinked, &start);
                scope.spawn(move || {
                    start.wait();
                    let (first, second): (&LoadedDefinition, &LoadedDefinition) = if thread % 2 == 0
                    {
                        (baseline, relinked)
                    } else {
                        (relinked, baseline)
                    };
                    let compile = |loaded: &LoadedDefinition| {
                        compile_loaded_definition(loaded, CompileOptions::default())
                            .expect("it compiles")
                    };
                    let (first, second) = (compile(first), compile(second));
                    if thread % 2 == 0 {
                        (first, second)
                    } else {
                        (second, first)
                    }
                })
            })
            .collect::<Vec<_>>();
        for (thread, handle) in threads.into_iter().enumerate() {
            let (baseline, mutant) = handle.join().expect("a thread does not panic");
            assert!(
                baseline == fresh_baseline,
                "thread {thread}: the shared baseline compiled otherwise"
            );
            assert!(
                mutant == fresh_mutant,
                "thread {thread}: the shared mutant compiled otherwise"
            );
        }
    });
}

/// The concurrent comparison repeated `K_RUST_COMPILE_CONCURRENCY_ROUNDS` times (20 by default):
/// each round, eight threads relink and compile every mutant and compile the shared baseline.
#[test]
#[ignore = "a stress run of several minutes; run it explicitly"]
fn concurrent_compiles_stress() {
    let rounds = std::env::var("K_RUST_COMPILE_CONCURRENCY_ROUNDS")
        .ok()
        .and_then(|rounds| rounds.parse::<usize>().ok())
        .unwrap_or(20);
    let mutants = MUTATIONS
        .iter()
        .map(|(from, to)| mutant(from, to))
        .collect::<Vec<_>>();
    let fresh = mutants
        .iter()
        .map(|mutant| relink_and_compile(&load(CALC), mutant).expect("the mutant compiles"))
        .collect::<Vec<_>>();
    let fresh_baseline =
        compile_loaded_definition(&load(CALC), CompileOptions::default()).expect("it compiles");
    for round in 0..rounds {
        let baseline = Arc::new(load(CALC));
        std::thread::scope(|scope| {
            let threads = (0..8)
                .map(|_| {
                    let (baseline, mutants) = (&baseline, &mutants);
                    scope.spawn(move || {
                        let compiled = mutants
                            .iter()
                            .map(|mutant| {
                                relink_and_compile(baseline, mutant).expect("the mutant compiles")
                            })
                            .collect::<Vec<_>>();
                        let own = compile_loaded_definition(baseline, CompileOptions::default())
                            .expect("it compiles");
                        (compiled, own)
                    })
                })
                .collect::<Vec<_>>();
            for (thread, handle) in threads.into_iter().enumerate() {
                let (compiled, own) = handle.join().expect("a thread does not panic");
                assert!(
                    compiled == fresh,
                    "round {round}, thread {thread}: a mutant compiled otherwise"
                );
                assert!(
                    own == fresh_baseline,
                    "round {round}, thread {thread}: the baseline compiled otherwise"
                );
            }
        });
    }
}

/// Every build folds `Float` constants through the backend: four threads compiling one shared
/// definition whose rules fold `Float` arithmetic give the artifacts of a compile of a fresh load.
/// The folded text is the backend's canonical text, which reads no locale.
#[test]
fn folded_floats_compile_concurrently_as_alone() {
    const FLOATS: &str = indoc! {r#"
        module FLOATS
          imports DOMAINS
          imports FLOAT
          syntax Float ::= sum() [function] | third() [function]
          rule sum() => 1.5 +Float 1.25
          rule third() => 1.0 /Float 3.0
        endmodule
    "#};
    let load_floats = || {
        let prelude = embedded("prelude.md").expect("the embedded prelude exists");
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        load_with_options(
            ResolvedSource::new("floats.k", FLOATS),
            "FLOATS",
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![prelude],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust.excluded_module_attribute().into(),
                ],
                ..LoadOptions::default()
            },
        )
        .expect("the definition loads")
    };
    let fresh =
        compile_loaded_definition(&load_floats(), CompileOptions::default()).expect("it compiles");
    assert!(
        fresh.definition_kore.contains("2.7500000000000000e+00"),
        "the sum is folded"
    );
    let shared = load_floats();
    std::thread::scope(|scope| {
        let threads = (0..4)
            .map(|_| {
                scope.spawn(|| {
                    compile_loaded_definition(&shared, CompileOptions::default())
                        .expect("it compiles")
                })
            })
            .collect::<Vec<_>>();
        for (thread, handle) in threads.into_iter().enumerate() {
            let artifacts = handle.join().expect("a thread does not panic");
            assert!(artifacts == fresh, "thread {thread} folded otherwise");
        }
    });
}
