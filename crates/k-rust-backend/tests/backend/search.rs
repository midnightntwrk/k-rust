//! Public contracts of `k_rust_backend::search`: the diagnostics of search result entries.

use k_rust_backend::{
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic},
    rewrite::{Pattern, TraceKind},
    rule::Predicate,
    search::{
        IncompleteSearch, PathWitness, SearchOptions, SearchState, SearchType, search_graph,
        search_paths, search_pattern, search_pattern_paths,
    },
    simplify::BudgetSubject,
    term::TermKind,
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::internal_term;

/// A definition over constructors `start`, `a`, `b`, `c`, `ok` with:
/// - `g(X) = g(g(X))`, a simplification equation under which simplifying any `g` application
///   exhausts every budget;
/// - `check(X) = ok requires g(X) == g(X)` (`check-ok`) and `norm(X) = c requires g(X) == g(X)`
///   (`norm-c`): simplifying the condition exhausts the budget, and the unsimplified condition
///   still holds, so the equation applies and the application reports the exhaustion;
/// - `stall(X) = ok requires g(X) == a` (`stall-ok`): the condition exhausts the budget and its
///   unsimplified form is undecided, so `stall(X)` stays unevaluated;
/// - the rewrite rules `rules`.
fn search_definition(rules: &str) -> BackendDefinition {
    let conditional = |symbol: &str, result: &str, right: &str, label: &str| {
        format!(
            r#"
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \equals{{SortS{{}}, R}}(g{{}}(X:SortS{{}}), {right}),
                        \and{{R}}(\in{{SortS{{}}, R}}(X0:SortS{{}}, X:SortS{{}}), \top{{R}}())
                    ),
                    \equals{{SortS{{}}, R}}(
                        {symbol}{{}}(X0:SortS{{}}),
                        \and{{SortS{{}}}}({result}{{}}(), \top{{SortS{{}}}}())
                    )
                ) [label{{}}("{label}")]"#
        )
    };
    let source = format!(
        r#"[]
            module MAIN
                sort SortS{{}} []
                symbol start{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol a{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol b{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol c{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol ok{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol held{{}}(SortS{{}}) : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol g{{}}(SortS{{}}) : SortS{{}} [function{{}}(), functional{{}}()]
                symbol check{{}}(SortS{{}}) : SortS{{}} [function{{}}()]
                symbol norm{{}}(SortS{{}}) : SortS{{}} [function{{}}()]
                symbol stall{{}}(SortS{{}}) : SortS{{}} [function{{}}()]
                axiom{{R}} \implies{{R}}(
                    \top{{R}}(),
                    \equals{{SortS{{}}, R}}(
                        g{{}}(X:SortS{{}}),
                        \and{{SortS{{}}}}(g{{}}(g{{}}(X:SortS{{}})), \top{{SortS{{}}}}())
                    )
                ) [label{{}}("grow"), simplification{{}}()]
                {check}
                {norm}
                {stall}
                {rules}
            endmodule []"#,
        check = conditional("check", "ok", "g{}(X:SortS{})", "check-ok"),
        norm = conditional("norm", "c", "g{}(X:SortS{})", "norm-c"),
        stall = conditional("stall", "ok", "a{}()", "stall-ok"),
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn rule(label: &str, left: &str, right: &str) -> String {
    format!(
        r#"
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}({left}, \top{{SortS{{}}}}()),
                    \and{{SortS{{}}}}({right}, \top{{SortS{{}}}}())
                ) [label{{}}("{label}")]"#
    )
}

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

fn condition_exhausted(rule_id: &str, limit: usize) -> [BackendDiagnostic; 2] {
    [
        BackendDiagnostic::SimplificationBudgetExhausted {
            limit,
            subject: BudgetSubject::Predicates,
        },
        BackendDiagnostic::RuleConditionUnsimplified {
            rule_id: rule_id.to_owned(),
            limit,
        },
    ]
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
            condition_exhausted("norm-c", 3),
            condition_exhausted(rule_id, 3),
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
                condition_exhausted("norm-c", 3),
                "{rules:?}"
            ),
            other => panic!("unexpected rule {other}"),
        }
        assert_eq!(collected, condition_exhausted("norm-c", 3), "{rules:?}");
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
            "c" => condition_exhausted("norm-c", 3).to_vec(),
            other => panic!("unexpected match on {other}"),
        };
        assert_eq!(found.state.diagnostics, path);
        assert_eq!(found.diagnostics, condition_exhausted("check-ok", 3));
    }

    assert_eq!(paths.incomplete, []);
    assert_eq!(paths.matches.len(), 2, "{:?}", paths.matches);
    for found in &paths.matches {
        let path = match head(&found.witness.pattern) {
            "b" => Vec::new(),
            "c" => condition_exhausted("norm-c", 3).to_vec(),
            other => panic!("unexpected match on {other}"),
        };
        assert_eq!(found.witness.diagnostics, path);
        assert_eq!(found.diagnostics, condition_exhausted("check-ok", 3));
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

    let [stall_predicates, stall_rule] = condition_exhausted("stall-ok", 3);
    let [_, norm_rule] = condition_exhausted("norm-c", 3);
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
