//! A loaded definition can be relinked and compiled from several threads at once, and each
//! concurrent call returns what the same call returns alone (`docs/compatibility.md`,
//! "Determinism and concurrency", Concurrency).
//!
//! The concurrent comparison catches shared mutable state on the compile path only when a race
//! happens to show in a run, so a passing run is evidence, not proof; new statics on the path
//! still need review.

use std::sync::Arc;

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
