//! A request that executes and then matches a target is one request: the variables the execution
//! mints are apart from every name of the target too. The target below spells `Ex-hX-b0`, the
//! spelling of the first mint of the rule variable `X`, at sort `SortT`, while the rule mints `X`
//! at sort `SortS`. If the execution's counter did not skip the target's spellings, the match
//! would report two distinct variables under one name, at two sorts.
//!
//! The target's names are its spellings as received: an alias that drops an argument removes the
//! argument's variables from the internalized target, yet the client wrote them, so no mint takes
//! their spelling either.
//!
//! A search without a target pattern matches a target the facade makes itself, one variable
//! spelled like the reference's `VarResult`. That variable is part of the request, so it is
//! named apart from every variable of the initial states.

use std::collections::BTreeSet;

use k_rust::backend::{
    Backend, BackendOptions,
    execution::{BackendRunOptions, SearchRunOptions},
    search::BackendMatchTarget,
};
use k_rust_backend::{fresh::RequestNames, rewrite::ExecutionMode, search::SearchType};
use k_rust_kore::kore::{
    ast::Pattern as KorePattern,
    parser::{parse_definition, parse_pattern},
    printer::Printer,
};

const DEFINITION: &str = r#"[]
module TEST
  sort SortS{} []
  sort SortT{} []
  sort SortState{} []
  symbol a{}() : SortS{} [constructor{}(), functional{}()]
  symbol t{}() : SortT{} [constructor{}(), functional{}()]
  symbol start{}() : SortState{} [constructor{}(), functional{}()]
  symbol pair{}(SortS{}, SortT{}) : SortState{} [constructor{}(), functional{}()]
  alias ignore{}(SortT{}) : SortT{} where ignore{}(V:SortT{}) := t{}() []
  axiom{} \rewrites{SortState{}}(
    \and{SortState{}}(start{}(), \top{SortState{}}()),
    \and{SortState{}}(pair{}(X:SortS{}, t{}()), \top{SortState{}}())
  ) [label{}("mint")]
endmodule []"#;

/// The printed response of `start()` run one step and matched against `target`, by execution then
/// match, or by search (which already reserved the target's names).
fn matched(target: &str, searching: bool) -> String {
    let mut backend = Backend::from_definition(
        parse_definition(DEFINITION).unwrap(),
        "TEST",
        BackendOptions::default(),
    )
    .unwrap();
    let definition = backend.select_definition(None).unwrap();
    let read = |source: &str| {
        let syntax = parse_pattern(source).unwrap();
        let pattern = definition
            .verify_standalone_pattern(&syntax, &[])
            .and_then(|admitted| admitted.internalize_pattern())
            .unwrap();
        (pattern, RequestNames::of_received(&[&syntax]))
    };
    let (initial, _) = read("start{}()");
    let (target, request_names) = read(target);
    let result = backend
        .run_cli(
            None,
            vec![initial],
            BackendRunOptions {
                depth: 1,
                max_simplification_iterations: 1000,
                breadth_limit: None,
                execute_to_branch: false,
                cut_point_rules: BTreeSet::new(),
                terminal_rules: BTreeSet::new(),
                strategy: ExecutionMode::All,
                search: searching.then_some(SearchRunOptions {
                    search_type: SearchType::One,
                    pattern: None,
                    bound: None,
                }),
                match_target: Some(BackendMatchTarget {
                    pattern: target,
                    generated_anonymous_variables: BTreeSet::new(),
                    request_names,
                }),
                function_symbols: BTreeSet::new(),
                stop_leaves: None,
                step_timeout: None,
                moving_average_timeout: false,
                capture_stdout: false,
                execution_input: None,
            },
        )
        .unwrap();
    Printer::compact().print_pattern(&result.pattern.to_pattern())
}

#[test]
fn execution_then_match_mints_apart_from_the_target() {
    for searching in [false, true] {
        let printed = matched("pair{}(Y:SortS{}, Ex-hX-b0:SortT{})", searching);
        let parsed = parse_pattern(&printed).unwrap();
        let mut backend =
            Backend::new(DEFINITION, "TEST", BackendOptions::default()).expect("definition");
        let _ = backend
            .select_definition(None)
            .unwrap()
            .verify_standalone_pattern(&parsed, &[])
            .unwrap_or_else(|error| {
                panic!("search {searching}: {printed} names two variables alike: {error}")
            });
        assert!(
            !printed.contains("Ex-hX-b0:SortS{}"),
            "search {searching}: the mint took the target's name: {printed}"
        );
    }
}

/// A target that wraps `Ex-hX-b0` in an alias that ignores its argument internalizes to a pattern
/// without it, but the client wrote it: the execution's or search's mint for `X` is still not
/// spelled `Ex-hX-b0`.
#[test]
fn mints_avoid_the_spellings_an_alias_drops_from_the_target() {
    for searching in [false, true] {
        let printed = matched("pair{}(Y:SortS{}, ignore{}(Ex-hX-b0:SortT{}))", searching);
        assert!(
            printed.contains("Ex-hX-b"),
            "search {searching}: the target should match a mint: {printed}"
        );
        assert!(
            !printed.contains("Ex-hX-b0"),
            "search {searching}: the mint took a spelling of the target: {printed}"
        );
    }
}

const SEARCH_DEFINITION: &str = r#"[]
module TEST
  sort SortS{} []
  sort SortT{} []
  sort SortState{} []
  symbol a{}() : SortS{} [constructor{}(), functional{}()]
  symbol t{}() : SortT{} [constructor{}(), functional{}()]
  symbol start{}(SortS{}) : SortState{} [constructor{}(), functional{}()]
  symbol pair{}(SortS{}, SortT{}) : SortState{} [constructor{}(), functional{}()]
  axiom{} \rewrites{SortState{}}(
    \and{SortState{}}(start{}(X:SortS{}), \top{SortState{}}()),
    \and{SortState{}}(pair{}(X:SortS{}, Y:SortT{}), \top{SortState{}}())
  ) [label{}("mint")]
endmodule []"#;

/// The answers of a one-step search of `initial` with no target pattern: the name of every
/// variable the response binds, and every bound value as printed. The response is a disjunction
/// of `\equals(target, value)`; it must be a pattern of the definition (no name at two sorts).
fn default_target_answers(
    initial: &str,
    search_type: SearchType,
) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut backend = Backend::from_definition(
        parse_definition(SEARCH_DEFINITION).unwrap(),
        "TEST",
        BackendOptions::default(),
    )
    .unwrap();
    let definition = backend.select_definition(None).unwrap();
    let initial_syntax = parse_pattern(initial).unwrap();
    let initial_pattern = definition
        .verify_standalone_pattern(&initial_syntax, &[])
        .and_then(|admitted| admitted.internalize_pattern())
        .unwrap();
    let result = backend
        .run_cli(
            None,
            vec![initial_pattern],
            BackendRunOptions {
                depth: 1,
                max_simplification_iterations: 1000,
                breadth_limit: None,
                execute_to_branch: false,
                cut_point_rules: BTreeSet::new(),
                terminal_rules: BTreeSet::new(),
                strategy: ExecutionMode::All,
                search: Some(SearchRunOptions {
                    search_type,
                    pattern: None,
                    bound: None,
                }),
                match_target: None,
                function_symbols: BTreeSet::new(),
                stop_leaves: None,
                step_timeout: None,
                moving_average_timeout: false,
                capture_stdout: false,
                execution_input: None,
            },
        )
        .unwrap();
    let response = result.pattern.to_pattern();
    let printed = Printer::compact().print_pattern(&response);
    let mut verifier =
        Backend::new(SEARCH_DEFINITION, "TEST", BackendOptions::default()).expect("definition");
    let _ = verifier
        .select_definition(None)
        .unwrap()
        .verify_standalone_pattern(&parse_pattern(&printed).unwrap(), &[])
        .unwrap_or_else(|error| {
            panic!("{search_type:?} from {initial}: {printed} names two variables alike: {error}")
        });
    let disjuncts = match &response {
        KorePattern::Or { arguments, .. } => arguments.iter().collect::<Vec<_>>(),
        other => vec![other],
    };
    let mut targets = BTreeSet::new();
    let mut values = BTreeSet::new();
    for disjunct in disjuncts {
        let KorePattern::Equals { left, right, .. } = disjunct else {
            panic!("{search_type:?} from {initial}: an answer is not a binding: {printed}");
        };
        let KorePattern::Variable(target) = left.as_ref() else {
            panic!("{search_type:?} from {initial}: an answer binds no variable: {printed}");
        };
        targets.insert(target.name.clone());
        values.insert(Printer::compact().print_pattern(right));
    }
    (targets, values)
}

#[test]
fn a_default_search_target_is_named_apart_from_the_request() {
    for search_type in [SearchType::Star, SearchType::Final] {
        // The target keeps the reference's spelling when no request variable has it.
        let (control_targets, other_sort_control) =
            default_target_answers("start{}(Q:SortS{})", search_type);
        assert_eq!(
            control_targets,
            BTreeSet::from(["VarResult".to_owned()]),
            "{search_type:?}"
        );

        // A request variable `VarResult` at another sort: the same answers, with the target
        // named apart (before, one printed name stood for both variables at two sorts).
        let (targets, other_sort) =
            default_target_answers("start{}(VarResult:SortS{})", search_type);
        assert_eq!(targets.len(), 1, "{search_type:?}: {targets:?}");
        assert!(
            !targets.contains("VarResult"),
            "{search_type:?}: the target took a request variable's name"
        );
        let expected = other_sort_control
            .iter()
            .map(|value| value.replace("Q:SortS{}", "VarResult:SortS{}"))
            .collect::<BTreeSet<_>>();
        assert_eq!(other_sort, expected, "{search_type:?}");

        // A request variable `VarResult` at the target's sort, constrained in the path condition:
        // the same answers as when it is spelled `W` (before, the target was identified with it,
        // and the search lost `pair(Q, _)` and reported the non-final `start(a())` as final).
        let same_sort = |name: &str| {
            default_target_answers(
                &format!(
                    "\\and{{SortState{{}}}}(start{{}}(Q:SortS{{}}), \\equals{{SortState{{}}, SortState{{}}}}({name}:SortState{{}}, start{{}}(a{{}}())))"
                ),
                search_type,
            )
        };
        let (control_targets, control) = same_sort("W");
        assert_eq!(
            control_targets,
            BTreeSet::from(["VarResult".to_owned()]),
            "{search_type:?}"
        );
        let (targets, answers) = same_sort("VarResult");
        assert_eq!(answers, control, "{search_type:?}");
        assert_eq!(targets.len(), 1, "{search_type:?}: {targets:?}");
        assert!(
            !targets.contains("VarResult"),
            "{search_type:?}: the target took a request variable's name"
        );
    }
}
