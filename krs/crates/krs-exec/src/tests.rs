use std::collections::BTreeMap;

use k_rust::{
    backend::{
        Backend, BackendOptions, EffectOutput, ExecuteRequest, ExecutionStrategy, HaltReasonOutput,
    },
    kast::Sort as KastSort,
    kore::parser::parse_pattern,
    names::BuiltinSort,
};

use super::{
    ConfigVariable, ExecError, Halt, SearchMode, SearchOptions, config_variables, log_lines,
    result_sort_hooks, search_backend, term,
};

/// A raw KORE definition with one initial state and two rules leaving it.
fn branching_backend() -> Backend {
    let definition = r#"[]
        module MAIN
            sort SortState{} []
            symbol initial{}() : SortState{} [constructor{}()]
            symbol left{}() : SortState{} [constructor{}()]
            symbol right{}() : SortState{} [constructor{}()]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(initial{}(), \top{SortState{}}()), left{}()
            ) [label{}("left")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(initial{}(), \top{SortState{}}()), right{}()
            ) [label{}("right")]
        endmodule []"#;
    Backend::new(definition, "MAIN", BackendOptions::default()).unwrap()
}

#[test]
fn search_returns_both_final_states() {
    let mut backend = branching_backend();
    let hooks = result_sort_hooks(&mut backend).unwrap();
    let response = search_backend(
        &mut backend,
        parse_pattern("initial{}()").unwrap(),
        SearchOptions::default(),
    )
    .unwrap();
    assert!(response.incomplete.is_empty());
    let mut states = response
        .states
        .iter()
        .map(|state| term(&state.state, &hooks).unwrap().kore().to_string())
        .collect::<Vec<_>>();
    states.sort();
    assert_eq!(states, ["left{}()", "right{}()"]);
}

#[test]
fn search_bounds_solutions_and_depth() {
    let mut backend = branching_backend();
    for (max_solutions, count) in [(Some(0), 0), (Some(1), 1), (None, 2)] {
        let response = search_backend(
            &mut backend,
            parse_pattern("initial{}()").unwrap(),
            SearchOptions {
                max_solutions,
                ..SearchOptions::default()
            },
        )
        .unwrap();
        assert_eq!(response.states.len(), count, "{max_solutions:?}");
    }
    let one_step = search_backend(
        &mut backend,
        parse_pattern("initial{}()").unwrap(),
        SearchOptions {
            mode: SearchMode::OneStep,
            ..SearchOptions::default()
        },
    )
    .unwrap();
    assert_eq!(one_step.states.len(), 2);
    let depth_zero = search_backend(
        &mut backend,
        parse_pattern("initial{}()").unwrap(),
        SearchOptions {
            mode: SearchMode::All,
            depth: Some(0),
            ..SearchOptions::default()
        },
    )
    .unwrap();
    assert_eq!(depth_zero.states.len(), 1);
    assert_eq!(
        term(
            &depth_zero.states[0].state,
            &result_sort_hooks(&mut backend).unwrap()
        )
        .unwrap()
        .kore()
        .to_string(),
        "initial{}()"
    );
}

#[test]
fn strategy_any_follows_one_path_and_depth_zero_stays_put() {
    let mut backend = branching_backend();
    let mut request = ExecuteRequest::new(parse_pattern("initial{}()").unwrap());
    request.strategy = ExecutionStrategy::Any;
    let result = backend.execute(request).unwrap();
    assert_eq!(result.leaves.len(), 1);
    assert_eq!(result.leaves[0].depth, 1);
    assert_eq!(Halt::from_backend(result.leaves[0].reason), Halt::Stuck);

    let mut request = ExecuteRequest::new(parse_pattern("initial{}()").unwrap());
    request.strategy = ExecutionStrategy::Any;
    request.max_depth = Some(0);
    let result = backend.execute(request).unwrap();
    assert_eq!(result.leaves.len(), 1);
    assert_eq!(
        Halt::from_backend(result.leaves[0].reason),
        Halt::DepthBound
    );
    assert_eq!(
        term(
            &result.leaves[0].state,
            &result_sort_hooks(&mut backend).unwrap()
        )
        .unwrap()
        .kore()
        .to_string(),
        "initial{}()"
    );
}

/// A result's domain values are rendered by their sorts' hooks in the definition: a Bytes value
/// is a byte string, whether or not its bytes are UTF-8, and a String value is quoted.
#[test]
fn results_render_domain_values_with_the_definitions_sort_hooks() {
    let definition = r#"[]
        module MAIN
            hooked-sort SortBytes{} [hook{}("BYTES.Bytes"), hasDomainValues{}()]
            hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
            sort SortState{} []
            symbol initial{}() : SortState{} [constructor{}()]
            symbol done{}(SortBytes{}, SortString{}) : SortState{} [constructor{}()]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(initial{}(), \top{SortState{}}()),
                done{}(\dv{SortBytes{}}("\x80\xff"), \dv{SortString{}}("a"))
            ) [label{}("done")]
        endmodule []"#;
    let mut backend = Backend::new(definition, "MAIN", BackendOptions::default()).unwrap();
    let hooks = result_sort_hooks(&mut backend).unwrap();
    let result = backend
        .execute(ExecuteRequest::new(parse_pattern("initial{}()").unwrap()))
        .unwrap();
    let state = term(&result.leaves[0].state, &hooks).unwrap();
    assert_eq!(
        k_rust::kast::printer::Printer::new().print_term(state.kast()),
        r#"done(#token("b\"\\x80\\xff\"","Bytes"),#token("\"a\"","String"))"#
    );
}

#[test]
fn halt_reasons_split_into_complete_and_inconclusive() {
    for reason in HaltReasonOutput::ALL {
        let halt = Halt::from_backend(reason);
        let complete = matches!(
            reason,
            HaltReasonOutput::Stuck
                | HaltReasonOutput::DepthBound
                | HaltReasonOutput::Trivial
                | HaltReasonOutput::Vacuous
        );
        assert_eq!(halt.is_complete(), complete, "{reason:?}");
    }
    assert_eq!(
        Halt::from_backend(HaltReasonOutput::Trivial).as_str(),
        "undefined"
    );
    assert_eq!(
        serde_json::to_value(Halt::DepthBound).unwrap(),
        serde_json::json!("depth-bound")
    );
}

#[test]
fn configuration_variables_list_the_program_first_with_snake_parameters() {
    let declared = BTreeMap::from([
        ("ENV".to_owned(), KastSort::builtin(BuiltinSort::Map)),
        ("PGM".to_owned(), KastSort::new("Pgm")),
        ("COUNTER".to_owned(), KastSort::builtin(BuiltinSort::Int)),
    ]);
    let variables = config_variables(&declared);
    assert_eq!(
        variables
            .iter()
            .map(|variable| (
                variable.name.as_str(),
                variable.parameter.as_str(),
                variable.is_main
            ))
            .collect::<Vec<_>>(),
        [
            ("PGM", "pgm", true),
            ("COUNTER", "counter", false),
            ("ENV", "env", false)
        ]
    );
    assert_eq!(variables[2].to_string(), "$ENV (init parameter env): Map");
}

#[test]
fn unknown_variable_errors_list_every_variable() {
    let variables = vec![
        ConfigVariable {
            name: "PGM".to_owned(),
            parameter: "pgm".to_owned(),
            sort: "Pgm".to_owned(),
            is_main: true,
        },
        ConfigVariable {
            name: "ENV".to_owned(),
            parameter: "env".to_owned(),
            sort: "Map".to_owned(),
            is_main: false,
        },
    ];
    let error = ExecError::UnknownVariable {
        name: "store".to_owned(),
        variables,
    };
    assert_eq!(
        error.to_string(),
        "unknown configuration variable `store`; the definition declares:\n  $PGM (init parameter pgm): Pgm\n  $ENV (init parameter env): Map"
    );
}

#[test]
fn terms_serialize_as_the_kast_json_envelope() {
    let value = term(
        &serde_json::to_value(
            serde_json::from_str::<serde_json::Value>(
                &k_rust::kore::json::to_string(&parse_pattern("left{}()").unwrap()).unwrap(),
            )
            .unwrap(),
        )
        .unwrap(),
        &std::collections::HashMap::new(),
    )
    .unwrap();
    let json = serde_json::to_value(&value).unwrap();
    assert_eq!(json["format"], "KAST");
    assert!(json["term"].is_object(), "{json}");
}

#[test]
fn k_head_prints_the_first_item_or_reports_an_empty_cell() {
    use k_rust::kast::Term as KastTerm;
    let configuration = |content| {
        super::Term::new(
            parse_pattern("dotk{}()").unwrap(),
            KastTerm::apply(
                "<generatedTop>",
                vec![KastTerm::apply("<k>", vec![content])],
            ),
        )
    };
    let head = configuration(KastTerm::Sequence(vec![KastTerm::apply("bar", vec![])])).k_head();
    assert!(
        matches!(&head, Some(Some(text)) if text.starts_with("bar")),
        "{head:?}"
    );
    assert_eq!(
        configuration(KastTerm::Sequence(Vec::new())).k_head(),
        Some(None)
    );
    assert_eq!(
        super::Term::new(
            parse_pattern("dotk{}()").unwrap(),
            KastTerm::apply("other", vec![])
        )
        .k_head(),
        None
    );
}

#[test]
fn parse_positions_name_the_line_and_column() {
    assert_eq!(
        super::located("prog.imp", "int x;\nfooo", Some(10)),
        "prog.imp:2:4"
    );
    assert_eq!(super::located("prog.imp", "foo", None), "prog.imp");
    assert_eq!(super::located("prog.imp", "foo", Some(99)), "prog.imp");
}

#[test]
fn log_lines_keep_each_user_log_message_in_order() {
    let effects = ["first", "second"].map(|message| EffectOutput::UserLog {
        message: message.into(),
    });
    assert_eq!(log_lines(&effects), ["first", "second"]);
    assert!(log_lines(&[]).is_empty());
}
