//! The execution work budget (`ExecutionOptions::max_work`): the states a run visits across all
//! its paths, a deterministic stop reported as one `WorkBound` leaf.

use std::{collections::BTreeMap, fmt::Write};

use k_rust_backend::{
    definition::BackendDefinition,
    rewrite::{ExecutionLeaf, ExecutionOptions, ExecutionResult, HaltReason, Pattern, execute},
    search::ResultModality,
    transition::ConsoleObservation,
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::internal_term;

const MODALITIES: [ResultModality; 2] = [ResultModality::PathSet, ResultModality::StateSet];

fn options(result_modality: ResultModality, max_work: Option<u64>) -> ExecutionOptions {
    ExecutionOptions {
        result_modality,
        max_work,
        ..ExecutionOptions::default()
    }
}

/// A leaf as the stop point's determinism is stated: by state, depth, halt reason, effects and
/// console, not by diagnostics, which a state-set merge unions and a larger budget can add to.
fn reading(
    leaf: &ExecutionLeaf,
) -> (
    Pattern,
    u64,
    HaltReason,
    Vec<k_rust_backend::builtin::BuiltinEffect>,
    ConsoleObservation,
) {
    (
        leaf.pattern.clone(),
        leaf.depth,
        leaf.halt_reason.clone(),
        leaf.effects.clone(),
        leaf.io.observable(),
    )
}

fn work_bound_leaves(result: &ExecutionResult) -> usize {
    result
        .leaves
        .iter()
        .filter(|leaf| leaf.halt_reason == HaltReason::WorkBound)
        .count()
}

/// The comb: `fork(N, A)` steps to `fork(N - 1, A)` and to `fork(N, A + 1)` while `N > 0`, and
/// `fork(0, A)` to `done(A)`. From `fork(1, 0)` one path never ends and every other one ends in
/// a `done` leaf, so the run has no end and finished leaves accumulate along it.
fn comb() -> BackendDefinition {
    let rule = |label: &str, left: &str, right: &str, requires: &str| {
        let requires = if requires.is_empty() {
            r"\top{SortS{}}()".to_owned()
        } else {
            format!(
                r#"\equals{{SortBool{{}}, SortS{{}}}}({requires}, \dv{{SortBool{{}}}}("true"))"#
            )
        };
        format!(
            r#"
            axiom{{}} \rewrites{{SortS{{}}}}(
                \and{{SortS{{}}}}({left}, {requires}),
                \and{{SortS{{}}}}({right}, \top{{SortS{{}}}}())
            ) [label{{}}("{label}")]"#
        )
    };
    let n = "N:SortInt{}";
    let a = "A:SortInt{}";
    let zero = r#"\dv{SortInt{}}("0")"#;
    let one = r#"\dv{SortInt{}}("1")"#;
    let source = format!(
        r#"[]
        module MAIN
            hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            sort SortS{{}} []
            hooked-symbol plus{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.add"), smt-hook{{}}("+")]
            hooked-symbol minus{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.sub"), smt-hook{{}}("-")]
            hooked-symbol gtInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.gt"), smt-hook{{}}(">")]
            symbol fork{{}}(SortInt{{}}, SortInt{{}}) : SortS{{}}
                [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol done{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            {down}
            {up}
            {end}
        endmodule []"#,
        down = rule(
            "down",
            &format!("fork{{}}({n}, {a})"),
            &format!("fork{{}}(minus{{}}({n}, {one}), {a})"),
            &format!("gtInt{{}}({n}, {zero})"),
        ),
        up = rule(
            "up",
            &format!("fork{{}}({n}, {a})"),
            &format!("fork{{}}({n}, plus{{}}({a}, {one}))"),
            &format!("gtInt{{}}({n}, {zero})"),
        ),
        end = rule(
            "end",
            &format!("fork{{}}({zero}, {a})"),
            &format!("done{{}}({a})"),
            "",
        ),
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn pattern(definition: &BackendDefinition, source: &str) -> Pattern {
    Pattern {
        term: internal_term(definition, source),
        constraints: Vec::new(),
    }
}

/// A definition over wrapped string states with the rewrite rules `edges` (from, to).
fn graph(edges: &[(String, String)]) -> BackendDefinition {
    let mut axioms = String::new();
    let mut counts = BTreeMap::<&str, usize>::new();
    for (from, to) in edges {
        let edge = counts.entry(from).or_default();
        write!(
            axioms,
            r#"axiom{{}} \rewrites{{SortS{{}}}}(
                \and{{SortS{{}}}}(wrap{{}}(\dv{{SortS{{}}}}("{from}")), \top{{SortS{{}}}}()),
                wrap{{}}(\dv{{SortS{{}}}}("{to}"))
            ) [label{{}}("{from}-{edge}")]
            "#
        )
        .unwrap();
        *edge += 1;
    }
    let source = format!(
        r#"[]
            module MAIN
                sort SortS{{}} [hasDomainValues{{}}()]
                symbol wrap{{}}(SortS{{}}) : SortS{{}}
                    [function{{}}(), total{{}}(), injective{{}}(), no-evaluators{{}}()]
                {axioms}
            endmodule []"#
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn node(definition: &BackendDefinition, name: &str) -> Pattern {
    pattern(
        definition,
        &format!(r#"wrap{{}}(\dv{{SortS{{}}}}("{name}"))"#),
    )
}

/// Test 1: on a run without end, every budget stops the run at the same state: one `WorkBound`
/// leaf, last, after exactly `k` states, and the leaves before it are the first leaves of the
/// same request with a larger budget; the same budget gives identical results.
#[test]
fn a_work_budget_stops_a_branching_run_at_the_same_state() {
    let definition = comb();
    let initial = pattern(
        &definition,
        r#"fork{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("0"))"#,
    );
    for modality in MODALITIES {
        for k in 1..=40 {
            let bounded = execute(&definition, initial.clone(), options(modality, Some(k)));
            assert_eq!(bounded.work, k, "{modality:?} k = {k}");
            assert_eq!(work_bound_leaves(&bounded), 1, "{modality:?} k = {k}");
            let (last, before) = bounded.leaves.split_last().expect("a leaf");
            assert_eq!(
                last.halt_reason,
                HaltReason::WorkBound,
                "{modality:?} k = {k}"
            );

            let larger = execute(
                &definition,
                initial.clone(),
                options(modality, Some(k + 1000)),
            );
            assert_eq!(larger.work, k + 1000);
            assert!(larger.leaves.len() > before.len());
            assert_eq!(
                before.iter().map(reading).collect::<Vec<_>>(),
                larger.leaves[..before.len()]
                    .iter()
                    .map(reading)
                    .collect::<Vec<_>>(),
                "{modality:?} k = {k}"
            );

            let again = execute(&definition, initial.clone(), options(modality, Some(k)));
            assert_eq!(again, bounded, "{modality:?} k = {k}");
        }
    }
}

/// The edges of `levels` chained diamonds, each with two routes to the next one and one stuck
/// side node (as `explore_all_covers_the_distinct_final_states_of_generated_reachability_graphs`).
fn diamonds(levels: usize) -> Vec<(String, String)> {
    let mut edges = Vec::new();
    for level in 0..levels {
        let start = format!("start-{level}");
        let left = format!("left-{level}");
        let right = format!("right-{level}");
        let next = format!("start-{}", level + 1);
        let side = format!("side-{level}");
        edges.push((start.clone(), left.clone()));
        edges.push((start, right.clone()));
        edges.push((left.clone(), next.clone()));
        edges.push((left, side.clone()));
        edges.push((right.clone(), next));
        edges.push((right, side));
    }
    edges
}

/// Test 2: a budget of at least the unbounded run's count changes nothing.
#[test]
fn a_work_budget_at_least_the_run_count_changes_nothing() {
    for levels in 1..=4 {
        let definition = graph(&diamonds(levels));
        let initial = node(&definition, "start-0");
        for modality in MODALITIES {
            let unbounded = execute(&definition, initial.clone(), options(modality, None));
            let work = unbounded.work;
            assert!(work > 0);
            assert_eq!(work_bound_leaves(&unbounded), 0);
            for budget in [work, work + 1] {
                let bounded = execute(
                    &definition,
                    initial.clone(),
                    options(modality, Some(budget)),
                );
                assert_eq!(
                    bounded, unbounded,
                    "{levels} levels, {modality:?}, {budget}"
                );
            }
            let short = execute(
                &definition,
                initial.clone(),
                options(modality, Some(work - 1)),
            );
            assert_eq!(short.work, work - 1);
            assert_eq!(
                work_bound_leaves(&short),
                1,
                "{levels} levels, {modality:?}"
            );
        }
    }
}

/// Test 3: the `WorkBound` leaf stands for the states the run dropped, so a state-set result
/// keeps it beside an earlier leaf of the same configuration. Two routes converge on the stuck
/// `d`: the states taken are `a`, `b`, `d` (stuck), `c`, and the budget of four stops the run on
/// the second arrival at `d`.
#[test]
fn a_work_bound_leaf_survives_the_state_set_merge() {
    let edges = [("a", "b"), ("a", "c"), ("b", "d"), ("c", "d")]
        .map(|(from, to)| (from.to_owned(), to.to_owned()));
    let definition = graph(&edges);
    let initial = node(&definition, "a");
    let unbounded = execute(
        &definition,
        initial.clone(),
        options(ResultModality::StateSet, None),
    );
    assert_eq!(unbounded.work, 5);
    assert_eq!(unbounded.leaves.len(), 1, "the two stuck `d` leaves merge");

    let result = execute(
        &definition,
        initial,
        options(ResultModality::StateSet, Some(4)),
    );
    assert_eq!(result.work, 4);
    let halts = result
        .leaves
        .iter()
        .map(|leaf| leaf.halt_reason.clone())
        .collect::<Vec<_>>();
    assert_eq!(halts, vec![HaltReason::Stuck, HaltReason::WorkBound]);
    assert_eq!(result.leaves[0].pattern, result.leaves[1].pattern);
}

/// Test 3, against a terminal-rule leaf: `b` reaches `d` by a terminal rule, so the first `d` is
/// a terminal leaf, which says its configuration is final; the budget stops the run on the
/// second arrival at `d`, and neither leaf absorbs the other.
#[test]
fn a_work_bound_leaf_and_a_terminal_leaf_of_one_configuration_are_both_kept() {
    let edges = [("a", "b"), ("a", "c"), ("b", "d"), ("c", "d")]
        .map(|(from, to)| (from.to_owned(), to.to_owned()));
    let definition = graph(&edges);
    let initial = node(&definition, "a");
    let terminal = |max_work| ExecutionOptions {
        terminal_rules: ["b-0".to_owned()].into(),
        ..options(ResultModality::StateSet, max_work)
    };
    let unbounded = execute(&definition, initial.clone(), terminal(None));
    let halts = |result: &ExecutionResult| {
        result
            .leaves
            .iter()
            .map(|leaf| leaf.halt_reason.clone())
            .collect::<Vec<_>>()
    };
    let terminal_halt = HaltReason::TerminalRule {
        rule: "b-0".to_owned(),
    };
    // The stuck second arrival at `d` is final in its own right, so the terminal leaf absorbs it.
    assert_eq!(halts(&unbounded), vec![terminal_halt.clone()]);

    let result = execute(&definition, initial, terminal(Some(unbounded.work - 1)));
    assert_eq!(halts(&result), vec![terminal_halt, HaltReason::WorkBound]);
    assert_eq!(result.leaves[0].pattern, result.leaves[1].pattern);
}

/// A run with `max_breadth = Some(0)` visits no state.
#[test]
fn a_run_bounded_to_no_breadth_visits_no_state() {
    let definition = graph(&diamonds(1));
    let result = execute(
        &definition,
        node(&definition, "start-0"),
        ExecutionOptions {
            max_breadth: Some(0),
            max_work: Some(1),
            ..ExecutionOptions::default()
        },
    );
    assert_eq!(result.work, 0);
    assert_eq!(result.leaves[0].halt_reason, HaltReason::BreadthBound);
}

/// `expanded` under `path-set`: no state is merged, so the visited states that are not expanded
/// are those that ended without a step. On the comb with a depth bound, the `done` leaves are
/// stuck after a step (expanded) and the state at the bound ends without one.
#[test]
fn a_path_set_run_expands_every_visited_state_but_those_ended_without_a_step() {
    let definition = comb();
    let initial = pattern(
        &definition,
        r#"fork{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("0"))"#,
    );
    for max_depth in [1, 2, 5, 10] {
        let result = execute(
            &definition,
            initial.clone(),
            ExecutionOptions {
                max_depth,
                ..options(ResultModality::PathSet, None)
            },
        );
        let unstepped = result
            .leaves
            .iter()
            .filter(|leaf| leaf.halt_reason == HaltReason::DepthBound)
            .count() as u64;
        assert!(unstepped > 0, "max_depth {max_depth}");
        assert_eq!(
            result.expanded,
            result.work - unstepped,
            "max_depth {max_depth}"
        );
    }
    // Without a bound on the diamonds every leaf is stuck after its step, so every visited
    // state is expanded.
    for levels in 1..=4 {
        let definition = graph(&diamonds(levels));
        let result = execute(
            &definition,
            node(&definition, "start-0"),
            options(ResultModality::PathSet, None),
        );
        assert_eq!(result.expanded, result.work, "{levels} levels");
    }
}

/// `expanded` under `state-set` with merges: each distinct (depth, state) is expanded once, and
/// every other visit is an arrival merged into it, which counts in `work` only.
#[test]
fn a_state_set_run_expands_each_distinct_state_of_a_depth_once() {
    for levels in 1..=4 {
        let edges = diamonds(levels);
        let definition = graph(&edges);
        let result = execute(
            &definition,
            node(&definition, "start-0"),
            options(ResultModality::StateSet, None),
        );
        // The oracle: the distinct (depth, node) pairs reachable from `start-0`, each expanded
        // once, and one visit for the initial state and for every successor of an expanded one.
        let successors = |from: &str| {
            edges
                .iter()
                .filter(|(source, _)| source == from)
                .map(|(_, to)| to.clone())
                .collect::<Vec<_>>()
        };
        let mut level = vec!["start-0".to_owned()];
        let (mut distinct, mut visits) = (0u64, 1u64);
        while !level.is_empty() {
            distinct += level.len() as u64;
            let mut next = std::collections::BTreeSet::new();
            for state in &level {
                let targets = successors(state);
                visits += targets.len() as u64;
                next.extend(targets);
            }
            level = next.into_iter().collect();
        }
        assert_eq!(result.expanded, distinct, "{levels} levels");
        assert_eq!(result.work, visits, "{levels} levels");
        assert!(
            result.expanded < result.work,
            "{levels} levels: merges happened"
        );

        let path_set = execute(
            &definition,
            node(&definition, "start-0"),
            options(ResultModality::PathSet, None),
        );
        assert!(result.expanded <= path_set.expanded);
    }
}

/// `expanded` at a work-bound stop: the state the budget stops at is neither visited nor
/// expanded, and on the comb every visited state is stepped.
#[test]
fn the_state_a_work_budget_stops_at_is_not_expanded() {
    let definition = comb();
    let initial = pattern(
        &definition,
        r#"fork{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("0"))"#,
    );
    for modality in MODALITIES {
        for k in [1, 2, 7, 30] {
            let result = execute(&definition, initial.clone(), options(modality, Some(k)));
            assert_eq!(work_bound_leaves(&result), 1);
            assert_eq!(result.work, k, "{modality:?} k = {k}");
            assert_eq!(result.expanded, k, "{modality:?} k = {k}");
        }
        let result = execute(&definition, initial.clone(), options(modality, Some(0)));
        assert_eq!((result.work, result.expanded), (0, 0), "{modality:?}");
    }
}
