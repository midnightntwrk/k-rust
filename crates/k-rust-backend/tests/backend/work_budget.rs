//! The execution work budget (`ExecutionOptions::max_work`): the states a run visits across all
//! its paths, a deterministic stop reported as one `WorkBound` leaf.

use std::{collections::BTreeMap, fmt::Write};

use k_rust_backend::{
    definition::BackendDefinition,
    rewrite::{
        ExecutionLeaf, ExecutionOptions, ExecutionResult, HaltReason, Pattern, execute,
        execute_with_solver,
    },
    rule::Predicate,
    search::ResultModality,
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    stop::Stoppable,
    substitution::Substitution,
    transition::ConsoleObservation,
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

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
    // Without a bound on the diamonds every path ends stuck after its step, so the oracle is the
    // graph's: every node of every path from `start-0` is visited and stepped once per path, so
    // `work` and `expanded` are both the number of path prefixes.
    for levels in 1..=4 {
        let edges = diamonds(levels);
        let definition = graph(&edges);
        let result = execute(
            &definition,
            node(&definition, "start-0"),
            options(ResultModality::PathSet, None),
        );
        let mut prefixes = 0u64;
        let mut stack = vec!["start-0".to_owned()];
        while let Some(state) = stack.pop() {
            prefixes += 1;
            stack.extend(
                edges
                    .iter()
                    .filter(|(source, _)| *source == state)
                    .map(|(_, to)| to.clone()),
            );
        }
        assert_eq!(result.work, prefixes, "{levels} levels");
        assert_eq!(result.expanded, prefixes, "{levels} levels");
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

/// A solver that finds every constraint satisfiable and decides no implication, so that a
/// symbolic condition splits a step into a branch and its remainder in every build.
struct Undecided;

impl SmtSolver for Undecided {
    fn is_sat(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        Ok(Ok(Satisfiability::Sat))
    }

    fn check_predicates(
        &self,
        _known: &[Predicate],
        _substitution: &Substitution,
        _checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        Ok(Ok(Validity::Contingent))
    }
}

fn definition(source: &str) -> BackendDefinition {
    let syntax = parse_definition(source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

/// A remainder is visited but takes no step of its own: its parent's step decided it. From
/// `f(X)`, the one rule `f(N) => g() requires N > 0` yields the successor `g()` where `X > 0`
/// and the remainder `f(X)` where `X <= 0`. The states visited are `f(X)`, `g()` and the
/// remainder; the first two are stepped (`g()` answers stuck), the remainder is not.
#[test]
fn a_remainder_is_visited_but_not_expanded() {
    let definition = definition(
        r#"[]
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            sort SortS{} []
            hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
            symbol f{}(SortInt{}) : SortS{} [constructor{}()]
            symbol g{}() : SortS{} [constructor{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    f{}(N:SortInt{}),
                    \equals{SortBool{}, SortS{}}(
                        gtInt{}(N:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    )
                ),
                \and{SortS{}}(g{}(), \top{SortS{}}())
            ) [label{}("positive")]
        endmodule []"#,
    );
    let initial = pattern(&definition, "f{}(X:SortInt{})");
    for modality in MODALITIES {
        let result = execute_with_solver(
            &definition,
            initial.clone(),
            options(modality, None),
            &Undecided,
        );
        let leaves = result
            .leaves
            .iter()
            .map(|leaf| (leaf.depth, leaf.halt_reason.clone()))
            .collect::<Vec<_>>();
        assert_eq!(
            leaves,
            [(1, HaltReason::Stuck), (0, HaltReason::Stuck)],
            "{modality:?}"
        );
        assert_eq!((result.work, result.expanded), (3, 2), "{modality:?}");
    }
}

/// `b` rewrites to `d`; both carry `N == 0` and `N =/= 0`, a contradiction that only the input
/// substitution exposes. From `b`, the depth-0 state is stepped from its unsimplified pattern
/// and its successor `d` is shown vacuous by its constraint simplification, before its step:
/// two states visited, one expanded. From `d`, the depth-0 state is stepped the same way, no
/// rule applies, and it is reported vacuous: the one state visited is expanded.
#[test]
fn a_vacuous_successor_is_not_expanded_and_a_deferred_initial_vacuity_is() {
    let definition = definition(
        r#"[]
        module MAIN
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            sort SortState{} []
            symbol b{}() : SortState{} [constructor{}()]
            symbol d{}() : SortState{} [constructor{}()]
            hooked-symbol intEq{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), hook{}("INT.eq")]
            hooked-symbol intNe{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), hook{}("INT.ne")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(b{}(), \top{SortState{}}()),
                d{}()
            ) [label{}("step")]
        endmodule []"#,
    );
    let initial = |state: &str| {
        let syntax = parse_pattern(&format!(
            r#"\and{{SortState{{}}}}(
                {state}{{}}(),
                \and{{SortState{{}}}}(
                    \equals{{SortBool{{}}, SortState{{}}}}(
                        intEq{{}}(N:SortInt{{}}, \dv{{SortInt{{}}}}("0")),
                        \dv{{SortBool{{}}}}("true")
                    ),
                    \equals{{SortBool{{}}, SortState{{}}}}(
                        intNe{{}}(N:SortInt{{}}, \dv{{SortInt{{}}}}("0")),
                        \dv{{SortBool{{}}}}("true")
                    )
                )
            )"#
        ))
        .expect("pattern should parse");
        definition
            .admit_unverified(&syntax, &[])
            .internalize_pattern()
            .expect("pattern should internalize")
    };
    let vacuous = |result: &ExecutionResult, depth: u64| {
        matches!(
            result.leaves.as_slice(),
            [ExecutionLeaf {
                depth: leaf_depth,
                halt_reason: HaltReason::Vacuous { depth: halt_depth, .. },
                ..
            }] if *leaf_depth == depth && *halt_depth == depth
        )
    };
    for modality in MODALITIES {
        let rewritten = execute(&definition, initial("b"), options(modality, None));
        assert!(vacuous(&rewritten, 1), "{modality:?}: {rewritten:#?}");
        assert_eq!((rewritten.work, rewritten.expanded), (2, 1), "{modality:?}");

        let stuck = execute(&definition, initial("d"), options(modality, None));
        assert!(vacuous(&stuck, 0), "{modality:?}: {stuck:#?}");
        assert_eq!((stuck.work, stuck.expanded), (1, 1), "{modality:?}");
    }
}

/// Every answer of the step is an expansion, a guard's answer included. From `initial()`, one
/// rule rewrites to `wrap(R)`:
/// - `R = \bottom`: the step answers `trivial`, and its one state is expanded;
/// - `R = dead("x")`, `dead` partial with an equation to `\bottom`: the step decides the
///   right-hand side's definedness itself and answers `trivial`, so the undefined successor is
///   never a state of its own: one state visited, one expanded;
/// - `R = dead("x")`, `dead` total: no term is undefined, so the successor is a state whose term
///   simplification takes it to `\bottom`; the step's first guard answers it `vacuous` without
///   matching a rule, and it is expanded: two states visited, two expanded.
#[test]
fn every_answer_of_the_step_is_an_expansion_a_guard_answer_included() {
    let shell = |symbols: &str, axioms: &str| {
        definition(&format!(
            r#"[]
            module MAIN
                sort SortS{{}} [hasDomainValues{{}}()]
                sort SortK{{}} []
                symbol initial{{}}() : SortK{{}} [constructor{{}}()]
                symbol wrap{{}}(SortS{{}}) : SortK{{}} [constructor{{}}()]
                {symbols}
                {axioms}
            endmodule []"#
        ))
    };
    let bottom_equation = r#"
        axiom{R} \implies{R}(
            \top{R}(),
            \equals{SortS{}, R}(dead{}(X:SortS{}), \and{SortS{}}(X:SortS{}, \bottom{SortS{}}()))
        ) [label{}("dead"), simplification{}()]"#;
    let to_dead = r#"
        axiom{} \rewrites{SortK{}}(
            \and{SortK{}}(initial{}(), \top{SortK{}}()),
            wrap{}(dead{}(\dv{SortS{}}("x")))
        ) [label{}("go")]"#;
    let cases = [
        // The rule's right-hand side is `\bottom`: the step answers `trivial`.
        (
            shell(
                "",
                r#"
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(initial{}(), \top{SortK{}}()),
                    wrap{}(\bottom{SortS{}}())
                ) [label{}("go")]"#,
            ),
            "trivial",
            0,
            (1, 1),
        ),
        // `dead` is partial: the step shows its right-hand side undefined.
        (
            shell(
                "symbol dead{}(SortS{}) : SortS{} [function{}()]",
                &format!("{bottom_equation}{to_dead}"),
            ),
            "trivial",
            0,
            (1, 1),
        ),
        // `dead` is total: no term is undefined, and the step's guard answers.
        (
            shell(
                "symbol dead{}(SortS{}) : SortS{} [function{}(), total{}()]",
                &format!("{bottom_equation}{to_dead}"),
            ),
            "vacuous",
            1,
            (2, 2),
        ),
    ];
    for (definition, halt, depth, counts) in cases {
        for modality in MODALITIES {
            let result = execute(
                &definition,
                pattern(&definition, "initial{}()"),
                options(modality, None),
            );
            let [leaf] = result.leaves.as_slice() else {
                panic!("{halt}, {modality:?}: {result:#?}");
            };
            let reported = match leaf.halt_reason {
                HaltReason::Trivial { .. } => "trivial",
                HaltReason::Vacuous { .. } => "vacuous",
                _ => "other",
            };
            assert_eq!((reported, leaf.depth), (halt, depth), "{result:#?}");
            assert_eq!(
                (result.work, result.expanded),
                counts,
                "{halt}, {modality:?}: {result:#?}"
            );
        }
    }
}

/// A breadth drain ends the pending states as `BreadthBound` leaves without visiting them. On
/// the diamonds, depth first, each expansion takes one pending state and pushes two, so after
/// `k` expansions `k + 1` states are pending; a bound of `b` is first exceeded after `b`
/// expansions, and the `b + 1` pending states are drained.
#[test]
fn a_breadth_drain_neither_visits_nor_expands_the_drained_states() {
    let definition = graph(&diamonds(3));
    for modality in MODALITIES {
        for breadth in 1..=4 {
            let result = execute(
                &definition,
                node(&definition, "start-0"),
                ExecutionOptions {
                    max_breadth: Some(breadth),
                    ..options(modality, None)
                },
            );
            let drained = result
                .leaves
                .iter()
                .filter(|leaf| leaf.halt_reason == HaltReason::BreadthBound)
                .count();
            assert_eq!(drained, breadth + 1, "{modality:?} {breadth}");
            assert_eq!(result.leaves.len(), drained, "{modality:?} {breadth}");
            let expanded = breadth as u64;
            assert_eq!(
                (result.work, result.expanded),
                (expanded, expanded),
                "{modality:?} {breadth}"
            );
        }
    }
}
