//! Public contracts of `k_rust_backend::search`: the diagnostics of search result entries, and
//! the identity of results, which a state-set execution shares.

use k_rust_backend::{
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic},
    rewrite::{ExecutionOptions, Pattern, TraceKind, execute},
    rule::Predicate,
    search::{
        IncompleteSearch, PathWitness, SearchOptions, SearchState, SearchType, search_graph,
        search_graph_disjunction_with_solver_and_observer, search_paths, search_paths_with_solver,
        search_pattern, search_pattern_paths,
    },
    simplify::BudgetSubject,
    smt::NoSolver,
    term::TermKind,
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::{
    ceil_div_definition, condition_exhausted, internal_term, rule, search_definition,
};

/// `start => held(g(a))`, and `start => b` when `branching`.
fn growing_definition(branching: bool) -> BackendDefinition {
    let mut rules = rule("to-g", "start{}()", "held{}(g{}(a{}()))");
    if branching {
        rules.push_str(&rule("to-b", "start{}()", "b{}()"));
    }
    search_definition(&rules)
}

fn start(definition: &BackendDefinition) -> Pattern {
    Pattern {
        term: internal_term(definition, "start{}()"),
        constraints: Vec::new(),
    }
}

fn options(search_type: SearchType) -> SearchOptions {
    SearchOptions {
        search_type,
        max_simplification_iterations: 3,
        ..SearchOptions::default()
    }
}

fn term_exhausted(limit: usize) -> BackendDiagnostic {
    BackendDiagnostic::SimplificationBudgetExhausted {
        limit,
        subject: BudgetSubject::Term,
    }
}

fn head(pattern: &Pattern) -> &str {
    match pattern.term.kind() {
        TermKind::Application { symbol, .. } => symbol.name.as_ref(),
        term => panic!("expected an application, found {term:?}"),
    }
}

fn state_headed<'a>(states: &'a [SearchState], name: &str) -> &'a SearchState {
    states
        .iter()
        .find(|state| head(&state.pattern) == name)
        .unwrap_or_else(|| panic!("no state headed by {name}: {states:?}"))
}

fn witness_headed<'a>(witnesses: &'a [PathWitness], name: &str) -> &'a PathWitness {
    witnesses
        .iter()
        .find(|witness| head(&witness.pattern) == name)
        .unwrap_or_else(|| panic!("no witness headed by {name}: {witnesses:?}"))
}

/// The rewrite rule the path of `trace` took last.
fn last_rule(trace: &[k_rust_backend::rewrite::TraceEntry]) -> &str {
    trace
        .iter()
        .rev()
        .find(|entry| entry.kind == TraceKind::Rewrite)
        .map(|entry| entry.unique_id.as_str())
        .expect("the path took a rewrite rule")
}

/// A pattern `X:SortS{}` constrained by `symbol(X) == ok`.
fn target_where(definition: &BackendDefinition, symbol: &str) -> Pattern {
    Pattern {
        term: internal_term(definition, "X:SortS{}"),
        constraints: vec![Predicate::Equals(
            internal_term(definition, &format!("{symbol}{{}}(X:SortS{{}})")),
            internal_term(definition, "ok{}()"),
        )],
    }
}

/// A Final search whose only result exhausted the budget returns that state with the
/// exhaustion, with no collector around the call, and reports no incompleteness: exhaustion
/// loses no successor.
#[test]
fn a_final_state_carries_the_budget_exhaustion_of_its_path() {
    let definition = growing_definition(false);

    let result = search_graph(&definition, start(&definition), options(SearchType::Final));

    let [state] = result.states.as_slice() else {
        panic!("expected one final state, found {:?}", result.states);
    };
    assert_eq!(head(&state.pattern), "held");
    assert_eq!(state.diagnostics, [term_exhausted(3)]);
    assert_eq!(result.incomplete, []);
}

/// Only the state whose path reached the exhausting equation carries its diagnostic.
#[test]
fn state_search_attributes_a_diagnostic_to_the_branch_that_emitted_it_only() {
    let definition = growing_definition(true);

    let result = search_graph(&definition, start(&definition), options(SearchType::Final));

    assert_eq!(result.states.len(), 2, "{:?}", result.states);
    assert_eq!(
        state_headed(&result.states, "held").diagnostics,
        [term_exhausted(3)]
    );
    assert_eq!(state_headed(&result.states, "b").diagnostics, []);
    assert_eq!(result.incomplete, []);
}

/// Each path witness carries its own path's diagnostics.
#[test]
fn path_search_attributes_a_diagnostic_to_the_witness_that_emitted_it_only() {
    let definition = growing_definition(true);

    let result = search_paths(&definition, start(&definition), options(SearchType::Final));

    assert_eq!(result.witnesses.len(), 2, "{:?}", result.witnesses);
    assert_eq!(
        witness_headed(&result.witnesses, "held").diagnostics,
        [term_exhausted(3)]
    );
    assert_eq!(witness_headed(&result.witnesses, "b").diagnostics, []);
    assert_eq!(result.incomplete, []);
}

/// A caller collecting around a search, as a same-thread adapter does, receives every
/// diagnostic in emission order under the collection's rules, although the search now collects
/// per unit of work inside. The expected lists are the ones these collections returned before
/// search collected per state (8377a862): for the growing branches, one exhaustion for each
/// simplification of the `g` state (its term simplification and its externalisation as a
/// result); for the pattern searches, `norm-c`'s exhaustion on the path to `c`, then the
/// match conditions' `check-ok` (or `stall-ok`) exhaustion, recorded once per rule and limit.
#[test]
fn a_collector_around_search_sees_every_diagnostic_of_every_path() {
    let definition = growing_definition(true);

    let (states, collected_states) = diagnostic::collect(|| {
        search_graph(&definition, start(&definition), options(SearchType::Final))
    });
    let (paths, collected_paths) = diagnostic::collect(|| {
        search_paths(&definition, start(&definition), options(SearchType::Final))
    });

    let growing = [term_exhausted(3), term_exhausted(3)];
    assert_eq!(collected_states, growing);
    assert_eq!(collected_paths, growing);
    assert_eq!(
        state_headed(&states.states, "held").diagnostics,
        [term_exhausted(3)]
    );
    assert_eq!(
        witness_headed(&paths.witnesses, "held").diagnostics,
        [term_exhausted(3)]
    );

    let definition = normalizing_definition();
    for (symbol, rule_id) in [("check", "check-ok"), ("stall", "stall-ok")] {
        let target = target_where(&definition, symbol);
        let (_, collected_states) = diagnostic::collect(|| {
            search_pattern(
                &definition,
                start(&definition),
                &target,
                options(SearchType::Final),
            )
        });
        let (_, collected_paths) = diagnostic::collect(|| {
            search_pattern_paths(
                &definition,
                start(&definition),
                &target,
                options(SearchType::Final),
            )
        });
        let expected = [
            condition_exhausted(&definition, "norm-c", 3),
            condition_exhausted(&definition, rule_id, 3),
        ]
        .concat();
        assert_eq!(collected_states, expected, "{symbol}");
        assert_eq!(collected_paths, expected, "{symbol}");
    }
}

/// Two paths reach `c` at depth 1: `to-c` directly, `to-norm` through `norm(a)`, whose
/// simplification to `c` exhausts the budget on `norm-c`'s condition. State-set search keeps one
/// of the converging states: whichever it keeps reports the diagnostics of the path its trace
/// records, and the dropped duplicate takes its own with it; a collector around the search still
/// receives them.
#[test]
fn a_deduplicated_state_keeps_the_diagnostics_of_its_recorded_path() {
    for rules in [["to-c", "to-norm"], ["to-norm", "to-c"]] {
        let definition = search_definition(
            &rules
                .iter()
                .map(|label| match *label {
                    "to-c" => rule("to-c", "start{}()", "c{}()"),
                    _ => rule("to-norm", "start{}()", "norm{}(a{}())"),
                })
                .collect::<String>(),
        );

        let (result, collected) = diagnostic::collect(|| {
            search_graph(&definition, start(&definition), options(SearchType::Final))
        });

        let [state] = result.states.as_slice() else {
            panic!("expected one deduplicated state, found {:?}", result.states);
        };
        assert_eq!(head(&state.pattern), "c");
        match last_rule(&state.trace) {
            "to-c" => assert_eq!(state.diagnostics, [], "{rules:?}"),
            "to-norm" => assert_eq!(
                state.diagnostics,
                condition_exhausted(&definition, "norm-c", 3),
                "{rules:?}"
            ),
            other => panic!("unexpected rule {other}"),
        }
        assert_eq!(
            collected,
            condition_exhausted(&definition, "norm-c", 3),
            "{rules:?}"
        );
    }
}

/// `start => b` and `start => norm(b)`: the second path reaches `c` through `norm-c`, whose
/// condition exhausts the budget when the state is simplified.
fn normalizing_definition() -> BackendDefinition {
    search_definition(
        &[
            rule("to-b", "start{}()", "b{}()"),
            rule("to-norm", "start{}()", "norm{}(b{}())"),
        ]
        .concat(),
    )
}

/// Matching a state against a target whose condition exhausts the budget (`check-ok`) records
/// the exhaustion on the match, not on the state or witness it matched, which keeps its own
/// path's list (`norm-c` on the path to `c`).
#[test]
fn a_match_records_its_own_diagnostics_apart_from_its_state() {
    let definition = normalizing_definition();
    let target = target_where(&definition, "check");

    let states = search_pattern(
        &definition,
        start(&definition),
        &target,
        options(SearchType::Final),
    );
    let paths = search_pattern_paths(
        &definition,
        start(&definition),
        &target,
        options(SearchType::Final),
    );

    assert_eq!(states.incomplete, []);
    assert_eq!(states.matches.len(), 2, "{:?}", states.matches);
    for found in &states.matches {
        let path = match head(&found.state.pattern) {
            "b" => Vec::new(),
            "c" => condition_exhausted(&definition, "norm-c", 3).to_vec(),
            other => panic!("unexpected match on {other}"),
        };
        assert_eq!(found.state.diagnostics, path);
        assert_eq!(
            found.diagnostics,
            condition_exhausted(&definition, "check-ok", 3)
        );
    }

    assert_eq!(paths.incomplete, []);
    assert_eq!(paths.matches.len(), 2, "{:?}", paths.matches);
    for found in &paths.matches {
        let path = match head(&found.witness.pattern) {
            "b" => Vec::new(),
            "c" => condition_exhausted(&definition, "norm-c", 3).to_vec(),
            other => panic!("unexpected match on {other}"),
        };
        assert_eq!(found.witness.diagnostics, path);
        assert_eq!(
            found.diagnostics,
            condition_exhausted(&definition, "check-ok", 3)
        );
    }
}

/// A match left undecided (`stall-ok`'s condition exhausts the budget and stays open) is
/// reported as an incomplete entry, which has no match entry: its state carries the path's
/// diagnostics followed by those of the undecided match, each distinct diagnostic once.
#[test]
fn an_undecided_match_reports_its_diagnostics_on_the_incomplete_entry() {
    let definition = normalizing_definition();
    let target = target_where(&definition, "stall");

    let states = search_pattern(
        &definition,
        start(&definition),
        &target,
        options(SearchType::Final),
    );
    let paths = search_pattern_paths(
        &definition,
        start(&definition),
        &target,
        options(SearchType::Final),
    );

    let [stall_predicates, stall_rule] = condition_exhausted(&definition, "stall-ok", 3);
    let [_, norm_rule] = condition_exhausted(&definition, "norm-c", 3);
    for (matches, incomplete) in [
        (states.matches.len(), &states.incomplete),
        (paths.matches.len(), &paths.incomplete),
    ] {
        assert_eq!(matches, 0);
        assert_eq!(incomplete.len(), 2, "{incomplete:?}");
        for entry in incomplete {
            let (IncompleteSearch::Smt { state, .. } | IncompleteSearch::Match { state, .. }) =
                entry
            else {
                panic!("expected an undecided match, found {entry:?}");
            };
            let expected = match head(&state.pattern) {
                "b" => vec![stall_predicates.clone(), stall_rule.clone()],
                "c" => vec![
                    stall_predicates.clone(),
                    norm_rule.clone(),
                    stall_rule.clone(),
                ],
                other => panic!("unexpected undecided match on {other}"),
            };
            assert_eq!(state.diagnostics, expected);
        }
    }
}

/// `start => b requires g(a) == g(a)` and `start => c`: deciding `to-b`'s condition exhausts
/// the budget in the rewrite step. The step attributes that work to the candidate it produced,
/// so only the path through `to-b` carries it, in state-set and path search alike.
#[test]
fn a_step_candidates_work_is_on_that_candidates_path_only() {
    let definition = search_definition(
        &[
            r#"
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        start{}(),
                        \equals{SortS{}, SortS{}}(g{}(a{}()), g{}(a{}()))
                    ),
                    \and{SortS{}}(b{}(), \top{SortS{}}())
                ) [label{}("to-b")]"#
                .to_owned(),
            rule("to-c", "start{}()", "c{}()"),
        ]
        .concat(),
    );

    let states = search_graph(&definition, start(&definition), options(SearchType::Final));
    let paths = search_paths(&definition, start(&definition), options(SearchType::Final));

    assert_eq!(states.states.len(), 2, "{:?}", states.states);
    let condition = [BackendDiagnostic::SimplificationBudgetExhausted {
        limit: 3,
        subject: BudgetSubject::Predicates,
    }];
    assert_eq!(state_headed(&states.states, "b").diagnostics, condition);
    assert_eq!(state_headed(&states.states, "c").diagnostics, []);
    assert_eq!(witness_headed(&paths.witnesses, "b").diagnostics, condition);
    assert_eq!(witness_headed(&paths.witnesses, "c").diagnostics, []);
}

/// An incomplete entry reports its state with the diagnostics of that state's path.
#[test]
fn an_incomplete_entry_carries_its_states_path_diagnostics() {
    let definition = growing_definition(false);

    let result = search_graph(
        &definition,
        start(&definition),
        SearchOptions {
            max_depth: 1,
            ..options(SearchType::Star)
        },
    );

    assert_eq!(
        state_headed(&result.states, "held").diagnostics,
        [term_exhausted(3)]
    );
    let [IncompleteSearch::DepthBound(bounded)] = result.incomplete.as_slice() else {
        panic!(
            "expected one depth-bound entry, found {:?}",
            result.incomplete
        );
    };
    assert_eq!(head(&bounded.pattern), "held");
    assert_eq!(bounded.diagnostics, [term_exhausted(3)]);
}

/// `pair(X, X /Int 0)` denotes `⌈X /Int 0⌉ ∧ pair(X, X /Int 0)`, and the ceil axiom makes
/// `⌈X /Int 0⌉` the false `0 =/=Int 0`: the initial state has no instance, so it is neither a
/// result nor explored, and the one result the bound admits is `pair(1, 2)`. A path search from
/// it has no witness.
#[test]
fn an_initial_state_empty_by_its_term_definedness_is_no_result() {
    let definition = ceil_div_definition();
    let state = |term: &str| Pattern {
        term: internal_term(&definition, term),
        constraints: Vec::new(),
    };
    let empty = r#"pair{}(X:SortInt{}, divInt{}(X:SortInt{}, \dv{SortInt{}}("0")))"#;
    let defined = state(r#"pair{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("2"))"#);

    let result = search_graph_disjunction_with_solver_and_observer(
        &definition,
        vec![state(empty), defined.clone()],
        SearchOptions {
            search_type: SearchType::Star,
            max_results: Some(1),
            ..SearchOptions::default()
        },
        &NoSolver,
        |_| {},
    );
    let patterns = result
        .states
        .iter()
        .map(|state| &state.pattern)
        .collect::<Vec<_>>();
    assert_eq!(patterns, [&defined]);

    let paths = search_paths_with_solver(
        &definition,
        state(empty),
        SearchOptions {
            search_type: SearchType::Star,
            ..SearchOptions::default()
        },
        &NoSolver,
    );
    assert!(paths.witnesses.is_empty(), "{:#?}", paths.witnesses);
}

/// A rewrite rule `left => \exists Y. held(Y)` labelled `label`.
fn existential_rule(label: &str, left: &str) -> String {
    existential_rule_into(label, left, "held")
}

/// A rewrite rule `left => \exists Y. head(Y)` labelled `label`.
fn existential_rule_into(label: &str, left: &str, head: &str) -> String {
    format!(
        r#"
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}({left}, \top{{SortS{{}}}}()),
                    \exists{{SortS{{}}}}(Y:SortS{{}}, {head}{{}}(Y:SortS{{}}))
                ) [label{{}}("{label}")]"#
    )
}

/// Every step of `held(X) => \exists Y. held(Y)` from `held(c)` reaches `held(Y')` for a new
/// variable `Y'`, which denotes the configurations `held(Y)` denotes: the second step closes a
/// cycle, so the path search ends exhausted with the witnesses `held(c)` and `held(Y)`, well
/// inside the depth bound, although the request's counter names each step's variable apart.
/// A few states of a few nodes each: kilobytes, well under a second.
#[test]
fn a_path_through_a_right_hand_side_existential_ends_at_its_cycle() {
    let definition = search_definition(&existential_rule("again", "held{}(X:SortS{})"));
    let initial = Pattern {
        term: internal_term(&definition, "held{}(c{}())"),
        constraints: Vec::new(),
    };
    let result = search_paths(
        &definition,
        initial,
        SearchOptions {
            max_depth: 30,
            ..options(SearchType::Star)
        },
    );
    assert!(
        matches!(result.end, k_rust_backend::search::SearchEnd::Exhausted(_)),
        "{:?}",
        result.end
    );
    assert!(result.incomplete.is_empty(), "{:?}", result.incomplete);
    let depths = result
        .witnesses
        .iter()
        .map(|witness| witness.depth)
        .collect::<Vec<_>>();
    assert_eq!(depths, [0, 1], "{:?}", result.witnesses);
}

/// `start => l`, `start => r`, and both `l` and `r` rewrite to `\exists Y. held(Y)`: the two
/// branches reach `held(Y0)` and `held(Y1)` for two new variables, one state up to their names,
/// so the state search reports it once. A chain of n such diamonds therefore has n + 1 final
/// states at most, not 2^n. Kilobytes, well under a second.
#[test]
fn a_state_search_merges_branches_that_introduce_their_own_variables() {
    let rules = [
        rule("to-a", "start{}()", "a{}()"),
        rule("to-b", "start{}()", "b{}()"),
        existential_rule("a-held", "a{}()"),
        existential_rule("b-held", "b{}()"),
    ]
    .concat();
    let definition = search_definition(&rules);
    let result = search_graph(&definition, start(&definition), options(SearchType::Final));
    let [state] = result.states.as_slice() else {
        panic!("expected one merged final state, found {:?}", result.states);
    };
    assert_eq!(head(&state.pattern), "held");
    assert_eq!(state.depth, 2);
}

/// A variable of the initial pattern is a name of the request, shared by every state, so a
/// state that holds it is not merged with one that holds a variable a rewrite introduced:
/// from `held(X)`, `held(Z) => held(Z)` and `held(Z) => \exists Y. held(Y)` reach two
/// different states at depth 1. Kilobytes, well under a second.
#[test]
fn a_state_search_keeps_a_request_variable_apart_from_an_introduced_one() {
    let rules = [
        rule("same", "held{}(Z:SortS{})", "held{}(Z:SortS{})"),
        existential_rule("other", "held{}(Z:SortS{})"),
    ]
    .concat();
    let definition = search_definition(&rules);
    let request = internal_term(&definition, "X:SortS{}");
    let initial = Pattern {
        term: internal_term(&definition, "held{}(X:SortS{})"),
        constraints: Vec::new(),
    };
    let result = search_graph(
        &definition,
        initial,
        SearchOptions {
            max_depth: 1,
            ..options(SearchType::Star)
        },
    );
    // Both states sit at the depth bound; merging them would list one.
    let at_bound = result
        .incomplete
        .iter()
        .filter_map(|entry| match entry {
            IncompleteSearch::DepthBound(state) => Some(state),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(at_bound.len(), 2, "{at_bound:?}");
    let TermKind::Variable(request) = request.kind() else {
        panic!("a variable");
    };
    assert_eq!(
        at_bound
            .iter()
            .filter(|state| state.pattern.term.attributes().variables.contains(request))
            .count(),
        1,
        "{at_bound:?}"
    );
}

/// The definition of the solution tests: constructors `s`, `d(SortS)`, `e`, `g`, `h`, `h2`, `k`
/// and the rules
///
/// ```text
/// s => \exists Y. d(Y)    d(Y) => e    e => g    g => \exists Y. d(Y)
/// e => h                  h => h2      h2 => d(k)
/// ```
///
/// From `s`, the states `d(Y)` for a new `Y` arise at depths 1 and 4 (the second through
/// `e => g => d(Y')`), and `d(k)` at depth 5.
fn solution_definition() -> BackendDefinition {
    let rules = [
        existential_rule_into("s-d", "s{}()", "d"),
        rule("d-e", "d{}(Y:SortS{})", "e{}()"),
        rule("e-g", "e{}()", "g{}()"),
        existential_rule_into("g-d", "g{}()", "d"),
        rule("e-h", "e{}()", "h{}()"),
        rule("h-h2", "h{}()", "h2{}()"),
        rule("h2-d", "h2{}()", "d{}(k{}())"),
    ]
    .concat();
    let source = format!(
        r#"[]
            module MAIN
                sort SortS{{}} []
                symbol s{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol d{{}}(SortS{{}}) : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol e{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol g{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol h{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol h2{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol k{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                {rules}
            endmodule []"#
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

/// The solutions of a pattern search for `d(V)` from `s`, each as the printed value of `V`
/// with the variables the request does not name shown as `?`.
fn solutions(definition: &BackendDefinition, max_results: Option<usize>) -> Vec<String> {
    let target = Pattern {
        term: internal_term(definition, "d{}(VarV:SortS{})"),
        constraints: Vec::new(),
    };
    let result = search_pattern(
        definition,
        Pattern {
            term: internal_term(definition, "s{}()"),
            constraints: Vec::new(),
        },
        &target,
        SearchOptions {
            max_depth: 7,
            max_results,
            ..options(SearchType::Star)
        },
    );
    // Only the depth bound leaves work behind.
    assert!(
        result
            .incomplete
            .iter()
            .all(|entry| matches!(entry, IncompleteSearch::DepthBound(_))),
        "{:?}",
        result.incomplete
    );
    result
        .matches
        .iter()
        .map(|found| {
            let [(variable, value)] = found.substitution.iter().collect::<Vec<_>>()[..] else {
                panic!("one binding: {:?}", found.substitution);
            };
            assert_eq!(variable.name.as_ref(), "VarV");
            match value.kind() {
                TermKind::Variable(_) => "?".to_owned(),
                TermKind::Application { symbol, .. } => symbol.name.to_string(),
                other => panic!("unexpected value {other:?}"),
            }
        })
        .collect()
}

/// `V = Y` for a variable `Y` the rewrite introduced is one solution, whichever name the
/// request's counter gave `Y`: the copy of `d(Y)` reached again at depth 4 is not a second
/// solution, so it takes no result slot from `V = k`, and an unbounded search lists it once.
/// A few states of a few nodes each: kilobytes, well under a second.
#[test]
fn a_solution_reached_again_under_another_name_is_one_solution() {
    let definition = solution_definition();
    assert_eq!(solutions(&definition, Some(2)), ["?", "k"]);
    assert_eq!(solutions(&definition, None), ["?", "k"]);
}

/// A state search reports a state once whatever names its introduced variables have: from
/// `start`, `start => held(a)` and `held(X) => \exists Y. held(Y)` reach `held(Y)` for a new
/// `Y` at every depth after the first, which is one state. A few states of a few nodes each:
/// kilobytes, well under a second.
#[test]
fn a_state_search_reports_a_state_reached_again_under_another_name_once() {
    let rules = [
        rule("to-held", "start{}()", "held{}(a{}())"),
        existential_rule("again", "held{}(X:SortS{})"),
    ]
    .concat();
    let definition = search_definition(&rules);
    let result = search_graph(
        &definition,
        start(&definition),
        SearchOptions {
            max_depth: 6,
            ..options(SearchType::Star)
        },
    );
    let depths = result
        .states
        .iter()
        .map(|state| state.depth)
        .collect::<Vec<_>>();
    assert_eq!(depths, [0, 1, 2], "{:?}", result.states);
}

/// A state-set execution reports two branches that end in one state up to the names of the
/// variables each introduced as one leaf: `start => a`, `start => b`, and both `a` and `b`
/// rewrite to `\exists Y. held(Y)`. Kilobytes, well under a second.
#[test]
fn a_state_set_execution_merges_leaves_equal_up_to_introduced_names() {
    let rules = [
        rule("to-a", "start{}()", "a{}()"),
        rule("to-b", "start{}()", "b{}()"),
        existential_rule("a-held", "a{}()"),
        existential_rule("b-held", "b{}()"),
    ]
    .concat();
    let definition = search_definition(&rules);
    let result = execute(
        &definition,
        start(&definition),
        ExecutionOptions {
            max_depth: 4,
            ..ExecutionOptions::default()
        },
    );
    let [leaf] = result.leaves.as_slice() else {
        panic!("expected one merged leaf, found {:?}", result.leaves);
    };
    assert_eq!(head(&leaf.pattern), "held");
}
