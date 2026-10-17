//! The work budget's prefix contract through the facade (`docs/compatibility.md`, "Work budget"):
//! every leaf finished before the `work-bound` leaf is a leaf of every run of the same request
//! with a larger budget or none, at the same position. Under `path-set` it is the same leaf in
//! every field; under `state-set` it is the same leaf but for its diagnostics, which are among
//! the larger run's. A budget of at least the unbounded run's `work` gives the unbounded result.
//!
//! The fixture is a run in which two paths reach one configuration (`d(4)`) at different depths,
//! so that under `maxDepth` 4 one path ends `stuck` and the other at the depth bound, and the
//! `state-set` merge absorbs the later leaf into the earlier one.

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionResult, HaltReasonOutput,
        ResultModalityOutput,
    },
    builtin::embedded,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ProgramGrammar,
        compile_loaded_definition,
    },
    kore::{ast::Pattern, codec, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use serde_json::Value;

const MODALITIES: [ResultModalityOutput; 2] = [
    ResultModalityOutput::PathSet,
    ResultModalityOutput::StateSet,
];

/// The absorb shape: `s(3)` steps to `a(4)`, which steps to `b(4)` and to `c(4)`; `b(4)` reaches
/// `d(4)` in one step and `c(4)` in two, through `e(4)`. `{A_RULES}` is replaced by the two rules
/// of `a`, in the order a variant declares them.
const ABSORB: &str = r#"
module ABSORB
  imports INT
  syntax Pgm ::= s(Int) | a(Int) | b(Int) | c(Int) | d(Int) | e(Int)
  rule s(N) => a(N +Int 1)
  {A_RULES}
  rule b(K) => d(K)
  rule c(K) => e(K)
  rule e(K) => d(K)
endmodule
"#;

/// A ground stuck configuration that applies a partial function no equation evaluates there:
/// `g(0)` is left as it is, since `g`'s one equation requires a positive argument.
const PARTIAL: &str = r#"
module PARTIAL
  imports INT
  syntax Pgm ::= s(Int) | done(Int)
  syntax Int ::= g(Int) [function]
  rule g(X) => 1 requires X >Int 0
  rule s(N) => done(g(N))
endmodule
"#;

/// Compile `source` (main and syntax module `main`) for the Rust backend with the prelude, and
/// assemble the initial configuration whose `$PGM` is `program` at sort `Pgm`.
fn compile(source: &str, main: &str, program: &str) -> (String, Pattern) {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("test.k", source),
        main,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap();
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let frontend = loaded.into_definition();
    let grammar = ProgramGrammar::new(&frontend).unwrap();
    let mut assembler =
        ConfigurationAssembler::new(&grammar, main, main, &artifacts.configuration_variables);
    assembler.program(&Sort::new("Pgm"), program).unwrap();
    (artifacts.definition_kore, assembler.finish().unwrap())
}

fn run(
    backend: &mut Backend,
    initial: &Pattern,
    modality: ResultModalityOutput,
    max_depth: Option<u64>,
    max_work: Option<u64>,
) -> ExecutionResult {
    backend
        .execute(ExecuteRequest {
            max_depth,
            max_work,
            result_modality: modality,
            ..ExecuteRequest::new(initial.clone())
        })
        .unwrap()
}

/// A leaf as JSON, and the same leaf without its diagnostics.
fn leaf_values(leaf: &k_rust::backend::ExecutionLeaf) -> (Value, Value) {
    let full = serde_json::to_value(leaf).unwrap();
    let mut stripped = leaf.clone();
    stripped.diagnostics.clear();
    (full, serde_json::to_value(stripped).unwrap())
}

fn diagnostics(leaf: &k_rust::backend::ExecutionLeaf) -> Vec<Value> {
    leaf.diagnostics
        .iter()
        .map(|diagnostic| serde_json::to_value(diagnostic).unwrap())
        .collect()
}

/// Run the request at every budget from 0 to the unbounded run's `work` + 1 and check the prefix
/// contract against the unbounded result, which it returns.
fn assert_prefix_contract(
    name: &str,
    backend: &mut Backend,
    initial: &Pattern,
    modality: ResultModalityOutput,
    max_depth: Option<u64>,
) -> ExecutionResult {
    let context = format!("{name}, {modality:?}, maxDepth {max_depth:?}");
    let unbounded = run(backend, initial, modality, max_depth, None);
    assert!(
        unbounded
            .leaves
            .iter()
            .all(|leaf| leaf.reason != HaltReasonOutput::WorkBound),
        "{context}: {unbounded:#?}"
    );
    let work = unbounded.work;
    for budget in 0..=work + 1 {
        let bounded = run(backend, initial, modality, max_depth, Some(budget));
        let context = format!("{context}, maxWork {budget}");
        if budget >= work {
            assert_eq!(
                serde_json::to_value(&bounded).unwrap(),
                serde_json::to_value(&unbounded).unwrap(),
                "{context}: a budget of at least `work` changes nothing"
            );
            continue;
        }
        assert_eq!(bounded.work, budget, "{context}");
        let (last, before) = bounded.leaves.split_last().expect("a work-bound leaf");
        assert_eq!(last.reason, HaltReasonOutput::WorkBound, "{context}");
        assert!(
            before
                .iter()
                .all(|leaf| leaf.reason != HaltReasonOutput::WorkBound),
            "{context}: one work-bound leaf, the last"
        );
        assert!(before.len() <= unbounded.leaves.len(), "{context}");
        for (position, (leaf, larger)) in before.iter().zip(&unbounded.leaves).enumerate() {
            let (leaf_full, leaf_stripped) = leaf_values(leaf);
            let (larger_full, larger_stripped) = leaf_values(larger);
            match modality {
                ResultModalityOutput::PathSet => {
                    assert_eq!(leaf_full, larger_full, "{context}, leaf {position}");
                }
                ResultModalityOutput::StateSet => {
                    assert_eq!(leaf_stripped, larger_stripped, "{context}, leaf {position}");
                    let larger_diagnostics = diagnostics(larger);
                    for diagnostic in diagnostics(leaf) {
                        assert!(
                            larger_diagnostics.contains(&diagnostic),
                            "{context}, leaf {position}: {diagnostic} is not among {larger_diagnostics:?}"
                        );
                    }
                }
            }
        }
    }
    unbounded
}

fn reasons(result: &ExecutionResult) -> Vec<HaltReasonOutput> {
    result.leaves.iter().map(|leaf| leaf.reason).collect()
}

/// The absorb shape, with `a`'s two rules in either order, in both modalities, with and without
/// a depth bound: the leaves before the `work-bound` leaf are the first leaves of the unbounded
/// run at every budget. Under `maxDepth` 4 the path-set result holds a finished `depth-bound`
/// leaf, so a bound leaf finished before the stop is covered too.
#[test]
fn the_leaves_before_a_work_bound_leaf_are_a_prefix_of_every_larger_budget_result() {
    for (variant, a_rules) in [
        ("b first", "rule a(K) => b(K)\n  rule a(K) => c(K)"),
        ("c first", "rule a(K) => c(K)\n  rule a(K) => b(K)"),
    ] {
        let (kore, initial) = compile(&ABSORB.replace("{A_RULES}", a_rules), "ABSORB", "s(3)");
        let mut backend = Backend::new(&kore, "ABSORB", BackendOptions::default()).unwrap();
        for modality in MODALITIES {
            for max_depth in [Some(4), None] {
                let unbounded =
                    assert_prefix_contract(variant, &mut backend, &initial, modality, max_depth);
                if modality == ResultModalityOutput::PathSet && max_depth.is_some() {
                    let reasons = reasons(&unbounded);
                    assert!(
                        reasons.contains(&HaltReasonOutput::Stuck)
                            && reasons.contains(&HaltReasonOutput::DepthBound),
                        "{variant}: {reasons:?}"
                    );
                }
            }
        }
    }
}

/// The documented counter-case: `s(0)` reaches a ground `stuck` leaf `done(g(0))` without
/// constraint and without diagnostics (beside the `trivial` leaf of the step's instances where
/// `g(0)` is undefined), in every budget at least the run's `work` and as a prefix at every
/// smaller one. It is a reached configuration to which no rule applies, but not a final
/// configuration of the request: its term applies the partial function `g`, which no equation
/// evaluates at `0`, so it may denote no value. Only a stuck term of constructors and domain
/// values is a final configuration.
#[test]
fn a_clean_stuck_leaf_that_applies_a_function_is_not_a_final_configuration() {
    let (kore, initial) = compile(PARTIAL, "PARTIAL", "s(0)");
    let mut backend = Backend::new(&kore, "PARTIAL", BackendOptions::default()).unwrap();
    for modality in MODALITIES {
        let unbounded = assert_prefix_contract("partial", &mut backend, &initial, modality, None);
        let [leaf] = unbounded
            .leaves
            .iter()
            .filter(|leaf| leaf.reason == HaltReasonOutput::Stuck)
            .collect::<Vec<_>>()[..]
        else {
            panic!("{modality:?}: one stuck leaf expected: {unbounded:#?}");
        };
        assert_eq!(leaf.depth, 1, "{modality:?}");
        assert!(leaf.diagnostics.is_empty(), "{modality:?}: {leaf:#?}");
        let state = codec::from_value(&leaf.state).unwrap();
        let text = Printer::compact().print_pattern(&state);
        assert!(
            !matches!(state, Pattern::And { .. }),
            "{modality:?}: the leaf carries no constraint: {text}"
        );
        assert!(
            text.contains(
                r#"Lblg'LParUndsRParUnds'PARTIAL'Unds'Int'Unds'Int{}(\dv{SortInt{}}("0"))"#
            ) && text.contains("Lbldone'"),
            "{modality:?}: {text}"
        );
    }
}
