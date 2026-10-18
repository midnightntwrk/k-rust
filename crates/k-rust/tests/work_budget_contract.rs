//! The work budget's prefix contract through the facade (`docs/compatibility.md`, "Work budget"):
//! every leaf finished before the `work-bound` leaf is a leaf of every run of the same request
//! with a larger budget or none, at the same position. Under `path-set` it is the same leaf in
//! every field but its path facts; under `state-set` it is the same leaf but for its
//! diagnostics, which are among the larger run's. A budget of at least the unbounded run's
//! `work` gives the unbounded result but for the leaves' diagnostics, which gain the run's
//! path facts (its implementation-chosen marks and the contradicted claims it observed).
//!
//! The fixture is a run in which two paths reach one configuration (`d(4)`) at different depths,
//! so that under `maxDepth` 4 one path ends `stuck` and the other at the depth bound, and the
//! `state-set` merge absorbs the later leaf into the earlier one. The same fixture pins the
//! completeness of such a `state-set` result (`docs/compatibility.md`, "Search results"): an
//! earlier `stuck` leaf stands for a later bound leaf of its configuration, whatever the
//! console's availability on either path. A second fixture has paths that meet path facts.

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionResult, HaltReasonOutput,
        ObservedRequest, ResultModalityOutput,
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

/// The request options a sweep varies besides the modality and the budget.
#[derive(Clone, Copy, Debug, Default)]
struct Shape {
    max_depth: Option<u64>,
    max_breadth: Option<usize>,
    /// Run through `execute_observed` with every rule observed.
    observed: bool,
}

fn run(
    backend: &mut Backend,
    initial: &Pattern,
    modality: ResultModalityOutput,
    max_depth: Option<u64>,
    max_work: Option<u64>,
) -> ExecutionResult {
    let shape = Shape {
        max_depth,
        ..Shape::default()
    };
    run_shaped(backend, initial, modality, shape, max_work)
}

fn run_shaped(
    backend: &mut Backend,
    initial: &Pattern,
    modality: ResultModalityOutput,
    shape: Shape,
    max_work: Option<u64>,
) -> ExecutionResult {
    let request = ExecuteRequest {
        max_depth: shape.max_depth,
        max_breadth: shape.max_breadth,
        max_work,
        result_modality: modality,
        ..ExecuteRequest::new(initial.clone())
    };
    if shape.observed {
        backend
            .execute_observed(ObservedRequest {
                request,
                rules: None,
            })
            .unwrap()
    } else {
        backend.execute(request).unwrap()
    }
}

/// A leaf as JSON without its diagnostics.
fn stripped(leaf: &k_rust::backend::ExecutionLeaf) -> Value {
    let mut stripped = leaf.clone();
    stripped.diagnostics.clear();
    serde_json::to_value(stripped).unwrap()
}

/// Whether a diagnostic is a path fact: a mark of an open value or a contradicted-claim record,
/// which a run with a work or breadth bound puts on every leaf.
fn is_path_fact(diagnostic: &Value) -> bool {
    diagnostic["kind"] == "implementation-chosen-value"
        || diagnostic["kind"] == "contradicted-claim"
}

/// A leaf's diagnostics, split into those that are not path facts and the path facts.
fn diagnostics(leaf: &k_rust::backend::ExecutionLeaf) -> (Vec<Value>, Vec<Value>) {
    leaf.diagnostics
        .iter()
        .map(|diagnostic| serde_json::to_value(diagnostic).unwrap())
        .partition(|diagnostic| !is_path_fact(diagnostic))
}

/// The path facts a run noted, as the diagnostics a leaf carries them as: its marks and the
/// contradicted claims it observed (not those of its definition's load, which no leaf carries).
fn run_path_facts(result: &ExecutionResult) -> Vec<Value> {
    let result = serde_json::to_value(result).unwrap();
    let marks = result["implementationChosenValues"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|mark| {
            let mut diagnostic = mark.clone();
            diagnostic["kind"] = "implementation-chosen-value".into();
            diagnostic
        });
    let records = result["contradictedClaims"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|record| record["observedIn"] == "run")
        .map(|record| {
            let mut diagnostic = record.clone();
            diagnostic["kind"] = "contradicted-claim".into();
            diagnostic
        });
    marks.chain(records).collect()
}

/// The result without its leaves' diagnostics.
fn without_diagnostics(result: &ExecutionResult) -> Value {
    let mut result = result.clone();
    for leaf in &mut result.leaves {
        leaf.diagnostics.clear();
    }
    serde_json::to_value(result).unwrap()
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
    let shape = Shape {
        max_depth,
        ..Shape::default()
    };
    assert_shaped_prefix_contract(name, backend, initial, modality, shape)
}

/// [`assert_prefix_contract`] for a request of the given shape. Under `path-set` the leaves are
/// compared in every field but their path facts, which includes an observed run's branch
/// identities and observations.
///
/// A budget of at least `work` gives the unbounded result in every field but the leaves'
/// diagnostics, and each leaf's diagnostics are the unbounded leaf's with every path fact of the
/// run added: in a run with a bound set, whether the bound fires rests on the exploration of
/// every path. A leaf finished before the stop carries the path facts the run noted so far, which
/// are among the larger run's.
fn assert_shaped_prefix_contract(
    name: &str,
    backend: &mut Backend,
    initial: &Pattern,
    modality: ResultModalityOutput,
    shape: Shape,
) -> ExecutionResult {
    let context = format!("{name}, {modality:?}, {shape:?}");
    let unbounded = run_shaped(backend, initial, modality, shape, None);
    assert!(
        unbounded
            .leaves
            .iter()
            .all(|leaf| leaf.reason != HaltReasonOutput::WorkBound),
        "{context}: {unbounded:#?}"
    );
    let run_facts = run_path_facts(&unbounded);
    let work = unbounded.work;
    for budget in 0..=work + 1 {
        let bounded = run_shaped(backend, initial, modality, shape, Some(budget));
        let context = format!("{context}, maxWork {budget}");
        if budget >= work {
            assert_eq!(
                without_diagnostics(&bounded),
                without_diagnostics(&unbounded),
                "{context}: a budget of at least `work` changes no configuration, halt, order or count"
            );
            for (position, (leaf, unbounded_leaf)) in
                bounded.leaves.iter().zip(&unbounded.leaves).enumerate()
            {
                let mut expected = serde_json::to_value(&unbounded_leaf.diagnostics)
                    .unwrap()
                    .as_array()
                    .unwrap()
                    .clone();
                for fact in &run_facts {
                    if !expected.contains(fact) {
                        expected.push(fact.clone());
                    }
                }
                let actual = serde_json::to_value(&leaf.diagnostics).unwrap();
                let actual = actual.as_array().unwrap();
                assert!(
                    actual.len() == expected.len()
                        && expected
                            .iter()
                            .all(|diagnostic| actual.contains(diagnostic)),
                    "{context}, leaf {position}: the diagnostics gain the run's path facts: {actual:?} against {expected:?}"
                );
            }
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
            assert_eq!(
                stripped(leaf),
                stripped(larger),
                "{context}, leaf {position}"
            );
            let (leaf_other, leaf_facts) = diagnostics(leaf);
            let (larger_other, larger_facts) = diagnostics(larger);
            match modality {
                ResultModalityOutput::PathSet => {
                    assert_eq!(leaf_other, larger_other, "{context}, leaf {position}");
                }
                ResultModalityOutput::StateSet => {
                    for diagnostic in &leaf_other {
                        assert!(
                            larger_other.contains(diagnostic),
                            "{context}, leaf {position}: {diagnostic} is not among {larger_other:?}"
                        );
                    }
                }
            }
            for fact in &leaf_facts {
                assert!(
                    larger_facts.contains(fact) || run_facts.contains(fact),
                    "{context}, leaf {position}: {fact} is no path fact of the larger run"
                );
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
/// leaf, so a bound leaf finished before the stop is covered too, and with `b` first the
/// state-set result merged it (it has fewer leaves). Under `maxDepth` 4 the sweep also runs with
/// `maxBreadth` 1, whose drain ends the run in `breadth-bound` leaves, and 2, which the run never
/// exceeds, and observed, with every rule's transitions in the leaves.
#[test]
fn the_leaves_before_a_work_bound_leaf_are_a_prefix_of_every_larger_budget_result() {
    let depth_four = Shape {
        max_depth: Some(4),
        ..Shape::default()
    };
    let shapes = [
        depth_four,
        Shape::default(),
        Shape {
            max_breadth: Some(1),
            ..depth_four
        },
        Shape {
            max_breadth: Some(2),
            ..depth_four
        },
        Shape {
            observed: true,
            ..depth_four
        },
    ];
    for (variant, a_rules) in [
        ("b first", "rule a(K) => b(K)\n  rule a(K) => c(K)"),
        ("c first", "rule a(K) => c(K)\n  rule a(K) => b(K)"),
    ] {
        let (kore, initial) = compile(&ABSORB.replace("{A_RULES}", a_rules), "ABSORB", "s(3)");
        let mut backend = Backend::new(&kore, "ABSORB", BackendOptions::default()).unwrap();
        for shape in shapes {
            let [path_set, state_set] = MODALITIES.map(|modality| {
                assert_shaped_prefix_contract(variant, &mut backend, &initial, modality, shape)
            });
            let path_reasons = reasons(&path_set);
            if let Some(breadth) = shape.max_breadth {
                // The run's worklist holds at most two states (`a(4)`'s two successors), so only a
                // bound of 1 drains it; a bound of 2 is never exceeded.
                assert_eq!(
                    path_reasons.contains(&HaltReasonOutput::BreadthBound),
                    breadth == 1,
                    "{variant}, maxBreadth {breadth}: {path_reasons:?}"
                );
            } else if shape.max_depth.is_some() {
                assert!(
                    path_reasons.contains(&HaltReasonOutput::Stuck)
                        && path_reasons.contains(&HaltReasonOutput::DepthBound),
                    "{variant}: {path_reasons:?}"
                );
                if variant == "b first" {
                    assert!(
                        state_set.leaves.len() < path_set.leaves.len(),
                        "{variant}, {shape:?}: the state set merged the bound leaf"
                    );
                }
            }
            if shape.observed {
                assert!(
                    path_set
                        .leaves
                        .iter()
                        .all(|leaf| !leaf.observations.is_empty()),
                    "{variant}: observed leaves carry their transitions"
                );
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

/// A leaf as the absorb tests read it: halt reason, depth and the compact KORE of its state.
fn shape(result: &ExecutionResult) -> Vec<(HaltReasonOutput, u64, String)> {
    result
        .leaves
        .iter()
        .map(|leaf| {
            let state = codec::from_value(&leaf.state).unwrap();
            (
                leaf.reason,
                leaf.depth,
                Printer::compact().print_pattern(&state),
            )
        })
        .collect()
}

/// An earlier `stuck` leaf absorbs a later bound leaf of its configuration, so the `state-set`
/// result is complete where the `path-set` result of the same bounds is not
/// (`docs/compatibility.md`, "Search results"). Under `maxDepth` 4, `d(4)` is stuck at depth 3
/// through `b` and at the depth bound at depth 4 through `c` and `e`: the path set holds both,
/// the state set only the stuck leaf, and both runs visit 7 states and expand 6 (the bound state
/// is visited, not stepped). With `a`'s rule to `c` declared first the bound leaf comes first and
/// is kept beside the stuck one. Without a depth bound each state set is one stuck `d(4)`.
#[test]
fn a_stuck_leaf_absorbs_a_later_bound_leaf_and_the_state_set_is_complete() {
    for (variant, a_rules) in [
        ("b first", "rule a(K) => b(K)\n  rule a(K) => c(K)"),
        ("c first", "rule a(K) => c(K)\n  rule a(K) => b(K)"),
    ] {
        let (kore, initial) = compile(&ABSORB.replace("{A_RULES}", a_rules), "ABSORB", "s(3)");
        let mut backend = Backend::new(&kore, "ABSORB", BackendOptions::default()).unwrap();
        let path_set = run(
            &mut backend,
            &initial,
            ResultModalityOutput::PathSet,
            Some(4),
            None,
        );
        let state_set = run(
            &mut backend,
            &initial,
            ResultModalityOutput::StateSet,
            Some(4),
            None,
        );
        let path_shape = shape(&path_set);
        assert!(
            path_shape
                .iter()
                .all(|(_, _, state)| state == &path_shape[0].2),
            "{variant}: every leaf is d(4): {path_shape:#?}"
        );
        assert!(
            path_shape[0].2.contains("Lbld'"),
            "{variant}: {path_shape:#?}"
        );
        let reasons = |result: &ExecutionResult| {
            shape(result)
                .into_iter()
                .map(|(reason, depth, _)| (reason, depth))
                .collect::<Vec<_>>()
        };
        let stuck = (HaltReasonOutput::Stuck, 3);
        let bound = (HaltReasonOutput::DepthBound, 4);
        let (expected_path, expected_state) = match variant {
            "b first" => (vec![stuck, bound], vec![stuck]),
            _ => (vec![bound, stuck], vec![bound, stuck]),
        };
        assert_eq!(reasons(&path_set), expected_path, "{variant}");
        assert_eq!(reasons(&state_set), expected_state, "{variant}");
        for result in [&path_set, &state_set] {
            assert_eq!((result.work, result.expanded), (7, 6), "{variant}");
        }

        // Without a depth bound both paths end stuck in `d(4)`; the state set keeps the first.
        let first_depth = if variant == "b first" { 3 } else { 4 };
        for modality in MODALITIES {
            let unbounded = run(&mut backend, &initial, modality, None, None);
            let expected = match modality {
                ResultModalityOutput::PathSet => vec![
                    (HaltReasonOutput::Stuck, first_depth),
                    (HaltReasonOutput::Stuck, 7 - first_depth),
                ],
                ResultModalityOutput::StateSet => vec![(HaltReasonOutput::Stuck, first_depth)],
            };
            assert_eq!(reasons(&unbounded), expected, "{variant}, {modality:?}");
            assert!(
                shape(&unbounded)
                    .iter()
                    .all(|(_, _, state)| state == &path_shape[0].2),
                "{variant}, {modality:?}"
            );
        }
    }
}

/// The console fixture: from `go`, one path passes through `sym(?X)`, a state with a variable,
/// so the console is off on it from there on, and reaches `fin` at depth 2; the other stays
/// ground, with the console on, and reaches `fin` at depth 3 through `gnd()` and `gnd2()`.
/// `{FIN_RULES}` is replaced by the rules of `fin`.
const CONSOLE: &str = r#"
module CONSOLE
  imports INT
  imports K-IO
  syntax Pgm ::= "go" | sym(Int) | gnd() | gnd2() | "fin" | out(IOInt)
  rule go => sym(?_X:Int)
  rule go => gnd()
  rule sym(_) => fin
  rule gnd() => gnd2()
  rule gnd2() => fin
  {FIN_RULES}
endmodule
"#;

/// The console fixture with `fin_rules`, run on the backend with the console on and `input` as
/// its standard input (the facade's `ExecuteRequest` has no console input).
fn console_runs(
    fin_rules: &str,
    input: &[u8],
    max_depth: u64,
) -> [k_rust_backend::rewrite::ExecutionResult; 2] {
    use k_rust_backend::{
        definition::BackendDefinition,
        rewrite::{ExecutionOptions, execute_with_io_state},
        search::ResultModality,
        transition::ExecutionIoState,
    };
    let (kore, initial) = compile(&CONSOLE.replace("{FIN_RULES}", fin_rules), "CONSOLE", "go");
    let syntax = k_rust::kore::parser::parse_definition(&kore).unwrap();
    let definition = BackendDefinition::internalize(&syntax, "CONSOLE").unwrap();
    let initial = definition
        .admit_unverified(&initial, &[])
        .internalize_pattern()
        .unwrap();
    [ResultModality::PathSet, ResultModality::StateSet].map(|result_modality| {
        execute_with_io_state(
            &definition,
            initial.clone(),
            ExecutionOptions {
                result_modality,
                max_depth,
                ..ExecutionOptions::default()
            },
            ExecutionIoState::new(input.to_vec()),
        )
    })
}

/// Console availability is not part of a final leaf's identity, and it does not change a stuck
/// verdict. With no rule for `fin`, both paths end `stuck` in `fin` in the path set, and the
/// state set holds one `stuck` leaf `fin`, the first path's (the console-off one).
///
/// The companion fixture shows that the first path does run with the console off, and that a
/// step that reaches a console hook there ends as a `simplification-failure` leaf, not `stuck`:
/// with `fin => out(#getc(0))` and input `a`, the console-off `fin` is the unsupported-hook
/// failure of `IO.getc`, and the ground path's `fin` steps to a `stuck` `out(97)` that consumed
/// one byte. Under `maxDepth` 3 the ground path's `fin` is a `depth-bound` leaf instead.
#[test]
fn a_stuck_leaf_reached_with_the_console_off_absorbs_one_reached_with_it_on() {
    use k_rust_backend::{
        rewrite::{ExecutionLeaf, HaltReason},
        simplify::SimplificationError,
    };
    let read = |leaf: &ExecutionLeaf| (leaf.halt_reason.clone(), leaf.depth, leaf.pattern.clone());

    let [path_set, state_set] = console_runs("", b"", u64::MAX);
    let [first, second] = path_set.leaves.as_slice() else {
        panic!("two path-set leaves expected: {:#?}", path_set.leaves);
    };
    assert_eq!(first.halt_reason, HaltReason::Stuck, "{first:#?}");
    assert_eq!(second.halt_reason, HaltReason::Stuck, "{second:#?}");
    assert_eq!(first.pattern, second.pattern);
    assert_eq!(
        (first.depth, second.depth),
        (2, 3),
        "the path through the symbolic state comes first"
    );
    assert_eq!(first.io.observable(), second.io.observable());
    let [merged] = state_set.leaves.as_slice() else {
        panic!("one state-set leaf expected: {:#?}", state_set.leaves);
    };
    assert_eq!(read(merged), read(first));

    let unsupported_getc = |leaf: &ExecutionLeaf| {
        matches!(
            &leaf.halt_reason,
            HaltReason::Simplification(SimplificationError::UnsupportedHook { hook, .. })
                if hook == "IO.getc"
        )
    };
    let getc = "rule fin => out(#getc(0))";
    let [path_set, _] = console_runs(getc, b"a", u64::MAX);
    let [off, on] = path_set.leaves.as_slice() else {
        panic!("two path-set leaves expected: {:#?}", path_set.leaves);
    };
    assert!(unsupported_getc(off), "console off at fin: {off:#?}");
    assert_eq!(off.depth, 2);
    assert_eq!(off.io.observable().consumed, 0);
    assert_eq!(on.halt_reason, HaltReason::Stuck, "{on:#?}");
    assert_eq!(on.depth, 4);
    assert_eq!(on.io.observable().consumed, 1);
    assert!(
        format!("{:?}", on.pattern).contains("\"97\""),
        "the ground path read `a`: {:?}",
        on.pattern
    );

    let [path_set, _] = console_runs(getc, b"a", 3);
    let [off, on] = path_set.leaves.as_slice() else {
        panic!("two path-set leaves expected: {:#?}", path_set.leaves);
    };
    assert!(unsupported_getc(off), "{off:#?}");
    assert_eq!(off.depth, 2);
    assert_eq!(
        (on.halt_reason.clone(), on.depth),
        (HaltReason::DepthBound, 3)
    );
}

/// Two paths of `g2(0)` reach `val(2)`: the `ga` path's `fe(0)` meets a contradicted `total`
/// claim (`td(0)` is bottom), the `gc` path reads the order of a two-key listing (whose size is the same in every order), and the `gb`
/// path meets neither. Without a budget each `path-set` leaf carries its own path's facts only.
/// With a budget set, whether it fires rests on every path, so every leaf carries every path fact
/// of the run, at a budget well above `work` too; the leaves are otherwise those of the unbounded
/// run, in both modalities, at every budget.
#[test]
fn a_budget_puts_the_run_s_path_facts_on_every_leaf_and_changes_nothing_else() {
    const FACTS: &str = r#"
module FACTS
  imports INT
  imports MAP
  imports LIST
  syntax Pgm ::= g2(Int) | ga(Int) | gb(Int) | gc(Int) | val(Int)
  syntax Int ::= td(Int) [function, total]
               | fe(Int) [function, total]
  rule [tdeq]: td(I) => 10 /Int (I +Int 0)
  rule [fe1]:  fe(I) => 1 requires td(I) >Int 0
  rule [fe2]:  fe(_) => 2 [owise]
  rule [g2a]:  g2(X) => ga(X)
  rule [g2b]:  g2(X) => gb(X)
  rule [g2c]:  g2(X) => gc(X)
  rule [gar]:  ga(X) => val(fe(X))
  rule [gbr]:  gb(_) => val(2)
  rule [gcr]:  gc(X) => val(size(keys_list(X |-> 0 (X +Int 1) |-> 0)))
endmodule
"#;
    let (kore, initial) = compile(FACTS, "FACTS", "g2(0)");
    let mut backend = Backend::new(&kore, "FACTS", BackendOptions::default()).unwrap();
    let kinds = |leaf: &k_rust::backend::ExecutionLeaf| {
        let (_, facts) = diagnostics(leaf);
        let mut kinds = facts
            .iter()
            .map(|fact| fact["kind"].as_str().unwrap().to_owned())
            .collect::<Vec<_>>();
        kinds.sort();
        kinds
    };
    let both = ["contradicted-claim", "implementation-chosen-value"];
    for modality in MODALITIES {
        let unbounded = assert_prefix_contract("facts", &mut backend, &initial, modality, None);
        let facts = run_path_facts(&unbounded);
        assert_eq!(facts.len(), 2, "{modality:?}: {unbounded:#?}");
        if modality == ResultModalityOutput::PathSet {
            let mut per_leaf = unbounded.leaves.iter().map(kinds).collect::<Vec<_>>();
            per_leaf.sort();
            assert_eq!(
                per_leaf,
                [
                    vec![],
                    vec!["contradicted-claim".to_owned()],
                    vec!["implementation-chosen-value".to_owned()],
                ],
                "{unbounded:#?}"
            );
        }
        let generous = run(&mut backend, &initial, modality, None, Some(100));
        assert_eq!(
            without_diagnostics(&generous),
            without_diagnostics(&unbounded),
            "{modality:?}"
        );
        assert!(
            generous.leaves.iter().all(|leaf| kinds(leaf) == both),
            "{modality:?}: {generous:#?}"
        );
    }
}
