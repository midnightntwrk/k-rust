//! A search without a target pattern matches a target the facade makes itself, one variable
//! spelled like the reference's `VarResult`. That variable is part of the request, so it is
//! named apart from every variable of the initial states.

use std::collections::BTreeSet;

use k_rust::backend::{
    Backend, BackendOptions,
    execution::{BackendRunOptions, SearchRunOptions},
};
use k_rust_backend::{rewrite::ExecutionMode, search::SearchType};
use k_rust_kore::kore::{
    ast::Pattern as KorePattern,
    parser::{parse_definition, parse_pattern},
    printer::Printer,
};

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
