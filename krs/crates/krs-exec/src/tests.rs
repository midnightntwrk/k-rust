use std::collections::BTreeMap;

use k_rust::{
    backend::{
        Backend, BackendOptions, EffectOutput, ExecuteRequest, ExecutionStrategy, HaltReasonOutput,
        KoreExecutionLeaf,
    },
    kast::Sort as KastSort,
    kore::parser::parse_pattern,
    names::BuiltinSort,
};

use super::{
    ConfigVariable, ExecError, Halt, OnePath, PathError, RunOptions, SearchMode, SearchOptions,
    StopIds, check_final_state, config_variables, cut_point_candidate, log_lines, one_path,
    read_proposal, result_sort_hooks, run_request, search_backend, term, valueless,
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
        .map(|state| {
            term(state.state.clone(), &hooks)
                .unwrap()
                .kore()
                .to_string()
        })
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
            depth_zero.states[0].state.clone(),
            &result_sort_hooks(&mut backend).unwrap()
        )
        .unwrap()
        .kore()
        .to_string(),
        "initial{}()"
    );
}

/// `KRS_CHECK_ENDS`'s check: a state reported stuck where no rule applies passes (`left`, an end
/// of the branching run); one a rule leaves (`initial`, the start the rules rewrite) fails,
/// naming the steps taken from it.
#[test]
fn a_stuck_end_holds_only_where_no_rule_applies() {
    let mut backend = branching_backend();
    let mut request = ExecuteRequest::new(parse_pattern("initial{}()").unwrap());
    request.strategy = ExecutionStrategy::Any;
    let end = one_path(
        backend.execute_kore(request).unwrap().leaves,
        &Named::default(),
    )
    .unwrap()
    .leaf;
    assert_eq!(end.reason, HaltReasonOutput::Stuck);
    check_final_state(
        &mut backend,
        &Named::default(),
        &end.state,
        "the run ended stuck",
    )
    .unwrap();

    let mut request = ExecuteRequest::new(parse_pattern("initial{}()").unwrap());
    request.max_depth = Some(0);
    let start = one_path(
        backend.execute_kore(request).unwrap().leaves,
        &Named::default(),
    )
    .unwrap()
    .leaf;
    let reported = KoreExecutionLeaf {
        reason: HaltReasonOutput::Stuck,
        ..start
    };
    let Err(ExecError::Result(message)) = check_final_state(
        &mut backend,
        &Named::default(),
        &reported.state,
        "the run ended stuck",
    ) else {
        panic!("a state two rules leave is no stuck end");
    };
    assert!(
        message.starts_with("KRS_CHECK_ENDS: the run ended stuck at a state")
            && message.contains("after 1 step(s)"),
        "{message}"
    );
}

/// A run asks the backend for its trace only when it reports one: k-rust keeps a trace entry
/// for every rewrite and simplification of the path unless asked not to (CF-32).
#[test]
fn a_run_requests_the_backend_trace_only_when_it_reports_one() {
    let state = parse_pattern("initial{}()").unwrap();
    let untraced = run_request(&state, &RunOptions::default(), &StopIds::default());
    assert!(!untraced.trace);
    assert!(matches!(untraced.strategy, ExecutionStrategy::Any));
    let traced = run_request(
        &state,
        &RunOptions {
            trace: true,
            depth: Some(3),
            ..RunOptions::default()
        },
        &StopIds::default(),
    );
    assert!(traced.trace);
    assert_eq!(traced.max_depth, Some(3));
    let mut backend = branching_backend();
    let leaves = backend.execute_kore(untraced).unwrap().leaves;
    assert!(leaves.iter().all(|leaf| leaf.trace.is_empty()));
    let leaves = backend.execute_kore(traced).unwrap().leaves;
    assert!(leaves.iter().any(|leaf| !leaf.trace.is_empty()));
}

/// A raw KORE definition of one path, `a => b => c`, by the rules `ab` and `bc`; an axiom without
/// `UNIQUE_ID` is identified by its label.
fn linear_backend() -> Backend {
    let definition = r#"[]
        module MAIN
            sort SortState{} []
            symbol a{}() : SortState{} [constructor{}()]
            symbol b{}() : SortState{} [constructor{}()]
            symbol c{}() : SortState{} [constructor{}()]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(a{}(), \top{SortState{}}()), b{}()
            ) [label{}("ab")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(b{}(), \top{SortState{}}()), c{}()
            ) [label{}("bc")]
        endmodule []"#;
    Backend::new(definition, "MAIN", BackendOptions::default()).unwrap()
}

/// The backend's stop rules as a run asks for them (CF-22): a stop before `bc` ends at `b`, the
/// state `bc` would rewrite, after one step, and proposes `c`, the successor a later run goes on
/// from; a stop after `ab` ends at `b` after one step, the step by `ab` counted.
#[test]
fn stop_rules_end_a_run_before_or_after_the_rule_s_step() {
    let state = parse_pattern("a{}()").unwrap();
    let mut backend = linear_backend();
    let before = StopIds {
        before: vec!["bc".to_owned()],
        after: Vec::new(),
        ..StopIds::default()
    };
    let leaves = backend
        .execute_kore(run_request(&state, &RunOptions::default(), &before))
        .unwrap()
        .leaves;
    let [leaf] = leaves.as_slice() else {
        panic!("{leaves:?}")
    };
    assert_eq!(leaf.reason, HaltReasonOutput::CutPoint);
    assert_eq!(Halt::from_backend(leaf.reason), Halt::Stopped);
    assert_eq!(leaf.depth, 1);
    assert_eq!(pattern_text(&leaf.state), "b{}()");
    assert_eq!(proposed(leaf), "c{}()");
    assert_eq!(leaf.candidates.as_ref().unwrap()[0].unique_id, "bc");

    let after = StopIds {
        before: Vec::new(),
        after: vec!["ab".to_owned()],
        ..StopIds::default()
    };
    let leaves = backend
        .execute_kore(run_request(&state, &RunOptions::default(), &after))
        .unwrap()
        .leaves;
    let [leaf] = leaves.as_slice() else {
        panic!("{leaves:?}")
    };
    assert_eq!(leaf.reason, HaltReasonOutput::Terminal);
    assert_eq!(leaf.depth, 1);
    assert_eq!(pattern_text(&leaf.state), "b{}()");
    // A stop before the first step a run takes ends it where it starts.
    let first = StopIds {
        before: vec!["ab".to_owned()],
        after: Vec::new(),
        ..StopIds::default()
    };
    let leaves = backend
        .execute_kore(run_request(&state, &RunOptions::default(), &first))
        .unwrap()
        .leaves;
    assert_eq!(leaves[0].reason, HaltReasonOutput::CutPoint);
    assert_eq!(leaves[0].depth, 0);
    assert_eq!(proposed(&leaves[0]), "b{}()");
}

fn proposed(leaf: &KoreExecutionLeaf) -> String {
    cut_point_candidate(leaf).unwrap().state.to_string()
}

fn pattern_text(state: &k_rust::kore::ast::Pattern) -> String {
    state.to_string()
}

#[test]
fn strategy_any_follows_one_path_and_depth_zero_stays_put() {
    let mut backend = branching_backend();
    let mut request = ExecuteRequest::new(parse_pattern("initial{}()").unwrap());
    request.strategy = ExecutionStrategy::Any;
    let result = backend.execute_kore(request).unwrap();
    assert_eq!(result.leaves.len(), 1);
    assert_eq!(result.leaves[0].depth, 1);
    assert_eq!(Halt::from_backend(result.leaves[0].reason), Halt::Stuck);

    let mut request = ExecuteRequest::new(parse_pattern("initial{}()").unwrap());
    request.strategy = ExecutionStrategy::Any;
    request.max_depth = Some(0);
    let result = backend.execute_kore(request).unwrap();
    assert_eq!(result.leaves.len(), 1);
    assert_eq!(
        Halt::from_backend(result.leaves[0].reason),
        Halt::DepthBound
    );
    assert_eq!(
        term(
            result.leaves[0].state.clone(),
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
        .execute_kore(ExecuteRequest::new(parse_pattern("initial{}()").unwrap()))
        .unwrap();
    let state = term(result.leaves[0].state.clone(), &hooks).unwrap();
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
                | HaltReasonOutput::CutPoint
                | HaltReasonOutput::Terminal
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
fn configuration_variables_list_the_main_parameter_first_with_its_rust_names() {
    let declared = BTreeMap::from([
        ("ENV".to_owned(), KastSort::builtin(BuiltinSort::Map)),
        ("PGM".to_owned(), KastSort::new("Pgm")),
        ("COUNTER".to_owned(), KastSort::builtin(BuiltinSort::Int)),
        ("ENTRY".to_owned(), KastSort::new("Op")),
        ("STDIN".to_owned(), KastSort::builtin(BuiltinSort::String)),
    ]);
    let parameter = |name: &str, variable: &str, main: bool| crate::Parameter {
        name: name.to_owned(),
        variable: variable.to_owned(),
        ty: crate::InputType::untyped(),
        main,
    };
    // The main parameter is the IR's, whatever its K name, and a parameter's name is its Rust
    // binding, not a case of its K name.
    let parameters = [
        parameter("env", "ENV", false),
        parameter("pgm", "PGM", false),
        parameter("count", "COUNTER", false),
        parameter("entry", "ENTRY", true),
    ];
    let variables = config_variables(&declared, &parameters);
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
            ("ENTRY", "entry", true),
            ("COUNTER", "count", false),
            ("ENV", "env", false),
            ("PGM", "pgm", false),
            ("STDIN", "stdin", false)
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
        parse_pattern("left{}()").unwrap(),
        &std::collections::HashMap::new(),
    )
    .unwrap();
    let json = serde_json::to_value(&value).unwrap();
    assert_eq!(json["format"], "KAST");
    assert!(json["term"].is_object(), "{json}");
}

#[test]
fn the_computation_head_prints_the_first_item_or_reports_an_empty_cell() {
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
    let head = configuration(KastTerm::Sequence(vec![KastTerm::apply("bar", vec![])]))
        .computation_head("k");
    assert!(
        matches!(&head, Some(Some(text)) if text.starts_with("bar")),
        "{head:?}"
    );
    assert_eq!(
        configuration(KastTerm::Sequence(Vec::new())).computation_head("k"),
        Some(None)
    );
    assert_eq!(
        super::Term::new(
            parse_pattern("dotk{}()").unwrap(),
            KastTerm::apply("other", vec![])
        )
        .computation_head("k"),
        None
    );
}

#[test]
fn the_computation_head_kore_is_the_first_item_of_the_flattened_sequence() {
    use k_rust::kast::Term as KastTerm;
    let head = |content: &str| {
        let state = super::Term::new(
            parse_pattern(&format!(
                "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}({content}))"
            ))
            .unwrap(),
            KastTerm::Sequence(Vec::new()),
        );
        state
            .computation_head_kore("k")
            .map(|item| item.map(ToString::to_string))
    };
    let wrap = r#"inj{SortObject{}, SortKItem{}}(Lblwrap{}(Lblbar{}(), \dv{SortInt{}}("3")))"#;
    assert_eq!(
        head(&format!("kseq{{}}({wrap}, dotk{{}}())")),
        Some(Some(parse_pattern(wrap).unwrap().to_string()))
    );
    assert_eq!(
        head(&format!(
            "append{{}}(dotk{{}}(), kseq{{}}({wrap}, Rest:SortK{{}}))"
        )),
        Some(Some(parse_pattern(wrap).unwrap().to_string()))
    );
    assert_eq!(
        head("Rest:SortK{}"),
        Some(Some(parse_pattern("Rest:SortK{}").unwrap().to_string()))
    );
    assert_eq!(head("dotk{}()"), Some(None));
    assert_eq!(
        super::Term::new(
            parse_pattern("dotk{}()").unwrap(),
            KastTerm::Sequence(Vec::new())
        )
        .computation_head_kore("k"),
        None
    );
    // The main cell is read by its name, whatever it is: `<prog>` holds the computation and no
    // `<k>` exists.
    let prog = super::Term::new(
        parse_pattern(&format!(
            "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'prog'-GT-'{{}}(kseq{{}}({wrap}, dotk{{}}())))"
        ))
        .unwrap(),
        KastTerm::Sequence(Vec::new()),
    );
    assert_eq!(
        prog.computation_head_kore("prog")
            .map(|item| item.map(ToString::to_string)),
        Some(Some(parse_pattern(wrap).unwrap().to_string()))
    );
    assert_eq!(prog.computation_head_kore("k"), None);
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

/// A variable's text that neither grammar of the reading rule parses is reported with both
/// failures, located where the text stops being readable under the rule: `word0` at `Word` is the
/// `Word` `word` and then a stray `0` under the syntax module's grammar, while the main module's
/// scanner reads `word` as a `Name` and fails at its start.
#[test]
fn a_variable_neither_grammar_reads_reports_both_failures_at_the_later_one() {
    use k_rust::{
        builtin::embedded,
        kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
        outer::{LoadOptions, ResolvedSource, load_with_options},
    };

    use super::configuration::{AssemblyError, Binding, Configuration};

    let source = r#"
module TOKENS-SYNTAX
  syntax Word ::= r"w[a-z]*" [token]
  syntax Pgm ::= "run" [symbol(run)]
endmodule
module TOKENS
  imports TOKENS-SYNTAX
  imports BASIC-K
  syntax Name ::= r"wor[a-z]*" [token, prec(2)]
  configuration <k> $PGM:Pgm </k> <w> $W:Word </w>
endmodule
"#;
    let mut resolver =
        |_: &str, path: &str| embedded(path).ok_or_else(|| format!("missing builtin {path}"));
    let loaded = load_with_options(
        ResolvedSource::new("tokens.k", source),
        "TOKENS",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap();
    let compiled = compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend: CompilationBackend::Rust,
            ..CompileOptions::default()
        },
    )
    .unwrap();
    let mut configuration =
        Configuration::new(&loaded.into_definition(), compiled.configuration_variables).unwrap();
    let variables = BTreeMap::from([("W".to_owned(), Binding::Text("word0".to_owned()))]);
    let Err(AssemblyError::Configuration(error)) =
        configuration.assemble_pattern(Some(&Binding::Text("run".to_owned())), &variables, None)
    else {
        panic!("`word0` at Word should not parse");
    };
    let sources = BTreeMap::from([(
        "W".to_owned(),
        super::Source {
            label: "w.txt".to_owned(),
            text: Some("word0".to_owned()),
        },
    )]);
    let ExecError::Parse {
        input,
        sort,
        message,
    } = super::configuration_error(&error, &sources, &[])
    else {
        panic!("{error}");
    };
    assert_eq!(
        (input.as_str(), sort.as_str()),
        ("w.txt:1:5", "Word"),
        "{message}"
    );
    assert!(
        message.starts_with("syntax module attempt: ")
            && message.contains("TOKENS-SYNTAX")
            && message.contains("; main module attempt: "),
        "{message}"
    );
}

#[test]
fn log_lines_keep_each_user_log_message_in_order() {
    let effects = ["first", "second"].map(|message| EffectOutput::UserLog {
        message: message.into(),
    });
    assert_eq!(log_lines(&effects), ["first", "second"]);
    assert!(log_lines(&[]).is_empty());
}

/// A raw KORE definition whose one rule rewrites to an application of a partial function with
/// no equations, so the backend splits on whether the result is defined.
fn partial_backend() -> Backend {
    let definition = r#"[]
        module MAIN
            sort SortState{} []
            symbol initial{}() : SortState{} [constructor{}()]
            symbol wrap{}(SortState{}) : SortState{} [constructor{}()]
            symbol undef{}() : SortState{} [function{}()]
            symbol empty{}() : SortState{} [constructor{}()]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(initial{}(), \top{SortState{}}()), wrap{}(undef{}())
            ) [label{}("wrap")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(empty{}(), \top{SortState{}}()), \bottom{SortState{}}()
            ) [label{}("empty")]
        endmodule []"#;
    Backend::new(definition, "MAIN", BackendOptions::default()).unwrap()
}

fn leaves(
    backend: &mut Backend,
    state: &str,
    strategy: ExecutionStrategy,
) -> Vec<KoreExecutionLeaf> {
    let mut request = ExecuteRequest::new(parse_pattern(state).unwrap());
    request.strategy = strategy;
    backend.execute_kore(request).unwrap().leaves
}

#[test]
fn a_run_follows_the_defined_leaf_of_a_definedness_split() {
    let mut backend = partial_backend();
    let hooks = result_sort_hooks(&mut backend).unwrap();
    let split = leaves(&mut backend, "initial{}()", ExecutionStrategy::Any);
    let mut reasons = split.iter().map(|leaf| leaf.reason).collect::<Vec<_>>();
    reasons.sort_by_key(|reason| format!("{reason:?}"));
    assert_eq!(
        reasons,
        [HaltReasonOutput::Stuck, HaltReasonOutput::Trivial]
    );

    let path = one_path(split.clone(), &Named::default()).unwrap();
    assert_eq!(Halt::from_backend(path.leaf.reason), Halt::Stuck);
    assert_eq!(path.leaf.depth, 1);
    assert_eq!(
        term(path.leaf.state.clone(), &hooks)
            .unwrap()
            .kore()
            .to_string(),
        "wrap{}(undef{}())"
    );
    assert!(path.valueless.is_empty());

    // `undef` is partial and has no equation, so `undef()` has no value, and neither has the
    // state that holds it: the run is undefined there, and names the term.
    let path = one_path(split, &Named::partial(&["undef"])).unwrap();
    assert_eq!(Halt::from_backend(path.leaf.reason), Halt::Undefined);
    assert_eq!(path.leaf.depth, 1);
    assert_eq!(path.valueless, [pattern("undef{}()")]);
}

/// `partial_backend`'s `wrap` rule, declared to preserve definedness: the backend takes its
/// successor `wrap(undef())` as defined, so it does not split on `undef()`'s definedness.
fn preserving_backend() -> Backend {
    let definition = r#"[]
        module MAIN
            sort SortState{} []
            symbol initial{}() : SortState{} [constructor{}()]
            symbol wrap{}(SortState{}) : SortState{} [constructor{}()]
            symbol undef{}() : SortState{} [function{}()]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(initial{}(), \top{SortState{}}()), wrap{}(undef{}())
            ) [label{}("wrap"), preserves-definedness{}()]
        endmodule []"#;
    Backend::new(definition, "MAIN", BackendOptions::default()).unwrap()
}

/// A stop before a rule proposes the rule's successor, which is read as a run's end is (CF-22).
/// `wrap`'s successor holds `undef()`, which has no value where `undef` is partial and has no
/// equation. Where the backend split the step on `undef()`'s definedness, the stopped leaf's
/// condition reads it and the leaf is already undefined; where it did not (`wrap` preserves
/// definedness), the proposal's reading finds the term: the step reaches no state, and the run
/// ends undefined where it would have stopped, after no step. Where `undef` may have a value,
/// the stop stands and proposes the successor.
#[test]
fn a_stop_before_a_rule_whose_successor_has_no_value_is_an_undefined_step() {
    let stops = StopIds {
        before: vec!["wrap".to_owned()],
        after: Vec::new(),
        ..StopIds::default()
    };
    let start = pattern("initial{}()");
    let partial = Named::partial(&["undef"]);
    let stopped = |backend: &mut Backend, heads: &Named| {
        let leaves = backend
            .execute_kore(run_request(&start, &RunOptions::default(), &stops))
            .unwrap()
            .leaves;
        one_path(leaves, heads).unwrap()
    };

    let split = stopped(&mut partial_backend(), &partial);
    assert!(split.held);
    assert_eq!(Halt::from_backend(split.leaf.reason), Halt::Undefined);
    assert_eq!(split.leaf.depth, 0);

    let mut backend = preserving_backend();
    let path = stopped(&mut backend, &partial);
    assert!(!path.held);
    assert_eq!(path.leaf.reason, HaltReasonOutput::CutPoint);
    let (leaf, proposed) = read_proposal(path.leaf, &partial).unwrap();
    assert_eq!(Halt::from_backend(leaf.reason), Halt::Undefined);
    assert_eq!(leaf.depth, 0);
    assert_eq!(pattern_text(&leaf.state), "initial{}()");
    assert_eq!(proposed.err().unwrap(), [pattern("undef{}()")]);

    let path = stopped(&mut backend, &Named::default());
    let (leaf, proposed) = read_proposal(path.leaf, &Named::default()).unwrap();
    assert_eq!(Halt::from_backend(leaf.reason), Halt::Stopped);
    assert_eq!(pattern_text(&leaf.state), "initial{}()");
    let proposed = proposed.ok().unwrap();
    assert_eq!(proposed.rule_id, "wrap");
    assert_eq!(proposed.successor.to_string(), "wrap{}(undef{}())");
}

#[test]
fn a_run_is_undefined_only_when_every_leaf_is() {
    let mut backend = partial_backend();
    let leaf = one_path(
        leaves(&mut backend, "empty{}()", ExecutionStrategy::Any),
        &Named::default(),
    )
    .unwrap()
    .leaf;
    assert_eq!(Halt::from_backend(leaf.reason), Halt::Undefined);

    // Two leaves under no condition break a run's contract: the internal error stays.
    let mut backend = branching_backend();
    let error = one_path(
        leaves(&mut backend, "initial{}()", ExecutionStrategy::All),
        &Named::default(),
    );
    assert!(matches!(error, Err(PathError::Several(2))), "{error:?}");
}

#[test]
fn proof_reports_keep_empty_success_and_render_its_contradiction_terms_as_kast() {
    use k_rust::{
        builtin::embedded,
        definition::CheckMode,
        kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
        outer::{LoadOptions, ResolvedSource, load_with_options},
    };
    let source = r"
module EMPTY-EVIDENCE
  imports INT
  syntax Int ::= bad(Int) [function, total]
  configuration <k> $PGM:K </k> <n> 0 </n>
  rule [bad-equation]: bad(X:Int) => X /Int 0
endmodule
module EMPTY-EVIDENCE-SPEC
  imports EMPTY-EVIDENCE
  claim [empty]: <k> .K </k> <n> bad(0) => 0 </n>
endmodule
";
    let mut resolver =
        |_: &str, path: &str| embedded(path).ok_or_else(|| format!("missing builtin {path}"));
    let loaded = load_with_options(
        ResolvedSource::new("empty.k", source),
        "EMPTY-EVIDENCE-SPEC",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            configuration_module: Some("EMPTY-EVIDENCE".into()),
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap();
    let compiled = compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend: CompilationBackend::Rust,
            default_claims_to_all_path: true,
            check_mode: CheckMode::Proof {
                definition_module: "EMPTY-EVIDENCE".into(),
            },
            ..CompileOptions::default()
        },
    )
    .unwrap();
    let mut backend = Backend::new(
        &compiled.definition_kore,
        "EMPTY-EVIDENCE-SPEC",
        BackendOptions::default(),
    )
    .unwrap();
    let hooks = result_sort_hooks(&mut backend).unwrap();
    let claim = super::ClaimInfo {
        label: "EMPTY-EVIDENCE-SPEC.empty".into(),
        module: "EMPTY-EVIDENCE-SPEC".into(),
        modality: super::Modality::AllPath,
        origin: None,
        trusted: false,
        backend_label: "EMPTY-EVIDENCE-SPEC.empty".into(),
    };
    // A claim timeout of zero cancels the proof before it starts: the claim times out, with no
    // leaves, and the backend proves it as before afterwards (the token was the proof's own).
    let cancelled = super::prove_claim(
        &mut backend,
        &hooks,
        &claim,
        None,
        Some(std::time::Duration::ZERO),
    )
    .unwrap();
    assert_eq!(cancelled.verdict, super::Verdict::Timeout);
    assert!(cancelled.leaves.is_empty());
    let reports = [super::prove_claim(&mut backend, &hooks, &claim, None, None).unwrap()];
    assert_eq!(reports[0].verdict, super::Verdict::Proven);
    // A wall the proof does not reach changes nothing.
    let walled = super::prove_claim(
        &mut backend,
        &hooks,
        &claim,
        None,
        Some(std::time::Duration::from_secs(600)),
    )
    .unwrap();
    assert_eq!(walled.verdict, super::Verdict::Proven);
    assert!(reports[0].trusted_claims.is_empty());
    assert!(reports[0].leaves[0].vacuous);
    assert!(!reports[0].leaves[0].certified);
    let json = serde_json::to_value(&reports[0]).unwrap();
    assert_eq!(
        json["leaves"][0]["contradicted_total"]["application"]["format"],
        "KAST"
    );
    assert_eq!(
        json["leaves"][0]["contradicted_total"]["undefined"]["format"],
        "KAST"
    );
}

/// Heads named by hand: the partial functions defined by their equations alone, and the data.
#[derive(Default)]
struct Named {
    partial: Vec<&'static str>,
}

impl Named {
    fn partial(partial: &[&'static str]) -> Self {
        Self {
            partial: partial.to_vec(),
        }
    }
}

impl valueless::Heads for Named {
    fn is_equational_partial(&self, symbol: &str) -> bool {
        self.partial.contains(&symbol)
    }

    fn is_data(&self, symbol: &str) -> bool {
        matches!(
            symbol,
            "inj" | "flag" | "done" | "test" | "acc" | "state" | "go"
        )
    }
}

fn pattern(text: &str) -> k_rust::kore::ast::Pattern {
    parse_pattern(text).unwrap()
}

/// A defined leaf at `depth` holding `state`, from a run of the partial backend.
fn leaf(state: &str, depth: u64) -> KoreExecutionLeaf {
    let mut backend = partial_backend();
    let mut leaf = leaves(&mut backend, "initial{}()", ExecutionStrategy::Any)
        .into_iter()
        .find(|leaf| leaf.reason == HaltReasonOutput::Stuck)
        .expect("a stuck leaf");
    leaf.state = pattern(state);
    leaf.depth = depth;
    leaf.trace.clear();
    leaf
}

fn state(path: &OnePath) -> String {
    path.leaf.state.to_string()
}

const F_TRUE: &str = r#"f{}(\dv{SortBool{}}("true"))"#;

/// The two leaves the backend returns where a rule's condition reads `f(true)`, the application
/// of a partial function defined by its equations alone, none of which applies at `true`
/// (finding NT-37-2): the rule applied where `f(true)` is defined and `true`, and the state left
/// where it is not `true`.
fn split_over(term: &str, held: &str) -> Vec<KoreExecutionLeaf> {
    vec![
        leaf(
            &format!(
                r#"\and{{SortState{{}}}}(done{{}}(), \ceil{{SortBool{{}}, SortState{{}}}}({term}), \equals{{SortBool{{}}, SortState{{}}}}(\dv{{SortBool{{}}}}("true"), {term}))"#
            ),
            1,
        ),
        leaf(
            &format!(
                r#"\and{{SortState{{}}}}({held}, \not{{SortState{{}}}}(\equals{{SortBool{{}}, SortState{{}}}}(\dv{{SortBool{{}}}}("true"), {term})))"#
            ),
            0,
        ),
    ]
}

/// A condition over a term with no value does not hold: the leaf where it holds is no state, and
/// the state the other leaf is holds the term, so it has none; the run is undefined there, with
/// any number of leaves (finding NT-42-2: one leaf).
#[test]
fn a_state_holding_a_term_with_no_value_has_none() {
    let heads = Named::partial(&["f"]);
    let held = format!("flag{{}}({F_TRUE})");
    let path = one_path(split_over(F_TRUE, &held), &heads).unwrap();
    assert_eq!(Halt::from_backend(path.leaf.reason), Halt::Undefined);
    assert_eq!(path.leaf.depth, 0);
    assert_eq!(path.valueless, [pattern(F_TRUE)]);
    // The condition the reading decided holds: the state is its configuration.
    assert_eq!(state(&path), held);

    let path = one_path(vec![leaf(&held, 0)], &heads).unwrap();
    assert_eq!(Halt::from_backend(path.leaf.reason), Halt::Undefined);
    assert_eq!(path.valueless, [pattern(F_TRUE)]);

    // A state whose condition gives the term a value is no state: alone, the run is undefined.
    let applied = split_over(F_TRUE, &held).remove(0);
    let path = one_path(vec![applied], &heads).unwrap();
    assert_eq!(Halt::from_backend(path.leaf.reason), Halt::Undefined);
    assert_eq!(path.valueless, [pattern(F_TRUE)]);
}

/// Where the condition built the term with no value and the state does not hold it, the rule
/// whose condition read it did not apply: the run ends as the other leaf does, naming the term.
#[test]
fn a_condition_over_a_term_with_no_value_does_not_hold() {
    let heads = Named::partial(&["f"]);
    let path = one_path(split_over(F_TRUE, "go{}()"), &heads).unwrap();
    assert_eq!(Halt::from_backend(path.leaf.reason), Halt::Stuck);
    assert_eq!(path.leaf.depth, 0);
    assert_eq!(path.valueless, [pattern(F_TRUE)]);
    assert_eq!(state(&path), "go{}()");
}

/// A term the backend left unevaluated that may have a value is no witness: a symbolic value
/// (an existential's `?V`), or a function that is not partial (`total`) or is hooked. A split
/// over it is the definition's, and the run names it rather than choosing a state.
#[test]
fn a_split_over_a_term_that_may_have_a_value_is_undecided() {
    let symbolic = r"VarV:SortInt{}";
    for (term, heads) in [
        (symbolic, Named::partial(&["f"])),
        (r#"opaque{}(\dv{SortInt{}}("1"))"#, Named::partial(&["f"])),
        // `f` applied to a symbolic argument: its equations' matching is not decided.
        (r"f{}(VarV:SortInt{})", Named::partial(&["f"])),
    ] {
        let held = format!("test{{}}({term})");
        let Err(PathError::Undecided { states, over }) = one_path(split_over(term, &held), &heads)
        else {
            panic!("a split over `{term}` is no one path");
        };
        assert_eq!(states, 2);
        assert_eq!(over, [pattern(term)]);
    }
    let error = one_path(split_over(symbolic, "test{}()"), &Named::default());
    assert!(matches!(error, Err(PathError::Undecided { .. })));
}

/// Where the leaves that are no state leave one whose condition the reading does not decide,
/// that leaf is the path, and its state keeps its condition.
#[test]
fn a_kept_leaf_keeps_the_condition_the_reading_does_not_decide() {
    let heads = Named::partial(&["f"]);
    let mut leaves = split_over(F_TRUE, "go{}()");
    let open = format!(
        r#"\and{{SortState{{}}}}(go{{}}(), \not{{SortState{{}}}}(\equals{{SortBool{{}}, SortState{{}}}}(\dv{{SortBool{{}}}}("true"), {F_TRUE})), \equals{{SortInt{{}}, SortState{{}}}}(VarV:SortInt{{}}, \dv{{SortInt{{}}}}("1")))"#
    );
    leaves[1] = leaf(&open, 0);
    let path = one_path(leaves, &heads).unwrap();
    assert_eq!(Halt::from_backend(path.leaf.reason), Halt::Stuck);
    assert_eq!(state(&path), pattern(&open).to_string());
    assert_eq!(path.valueless, [pattern(F_TRUE)]);

    // One leaf whose condition reads a term with a value the backend left (`#Ceil(b ; c)` under
    // a withdrawn equation head) is printed as it is.
    let residual =
        r"\and{SortState{}}(go{}(), \ceil{SortState{}, SortState{}}(seq{}(go{}(), go{}())))";
    let path = one_path(vec![leaf(residual, 1)], &heads).unwrap();
    assert_eq!(Halt::from_backend(path.leaf.reason), Halt::Stuck);
    assert_eq!(state(&path), pattern(residual).to_string());
    assert!(path.valueless.is_empty());
}

/// The backend states a projection's definedness as `#Exists V . {t #Equals V}`, a predicate: a
/// term with no value has no value `V` is equal to, so the condition does not hold where `t`
/// holds one, and the state is its configuration. Read so, the state's configuration is read
/// too, so a term with no value beside a projection whose operand may have one (`opaque(1)`) is
/// found there (`prj(noval(red))`, `duo(prj(opq(1)), size(red))`, `alias_clauses`).
#[test]
fn a_projection_s_definedness_is_a_condition_read_as_any_other() {
    let heads = Named::partial(&["f"]);
    let defined = |term: &str| {
        format!(
            r"\exists{{SortState{{}}}}(VarK:SortInt{{}}, \equals{{SortInt{{}}, SortState{{}}}}({term}, VarK:SortInt{{}}))"
        )
    };
    let projected = format!("test{{}}(project{{}}({F_TRUE}))");
    let path = one_path(
        vec![leaf(
            &format!(r"\and{{SortState{{}}}}({projected}, {})", defined(F_TRUE)),
            0,
        )],
        &heads,
    )
    .unwrap();
    assert_eq!(Halt::from_backend(path.leaf.reason), Halt::Undefined);
    assert_eq!(path.valueless, [pattern(F_TRUE)]);
    assert_eq!(state(&path), projected);

    let opaque = r#"opaque{}(\dv{SortInt{}}("1"))"#;
    let beside = format!(
        r"\and{{SortState{{}}}}(test{{}}(project{{}}({opaque}), {F_TRUE}), {})",
        defined(opaque)
    );
    let path = one_path(vec![leaf(&beside, 0)], &heads).unwrap();
    assert_eq!(Halt::from_backend(path.leaf.reason), Halt::Undefined);
    assert_eq!(path.valueless, [pattern(F_TRUE)]);

    // Alone, the projection of a term that may have a value is a state, its condition printed.
    let open = format!(
        r"\and{{SortState{{}}}}(test{{}}(project{{}}({opaque})), {})",
        defined(opaque)
    );
    let path = one_path(vec![leaf(&open, 0)], &heads).unwrap();
    assert_eq!(Halt::from_backend(path.leaf.reason), Halt::Stuck);
    assert_eq!(state(&path), pattern(&open).to_string());
    assert!(path.valueless.is_empty());
    // Two such leaves are undecided over the operand, not over the bound `V`.
    let Err(PathError::Undecided { over, .. }) = one_path(
        vec![leaf(&open, 0), leaf(&open.replace("test{}(", "go{}("), 0)],
        &heads,
    ) else {
        panic!("two leaves over `opaque(1)` are no one path");
    };
    assert_eq!(over, [pattern(opaque)]);
}

/// The entries of the deep states below: a log of a million entries, which a state holds as a
/// chain one level per entry.
const LOG_ENTRIES: usize = 1_000_000;

/// Run `work` on a thread of 8 MiB, a main thread's default on Linux: a walk that recursed once
/// per level of a state overflowed it at a few thousand levels.
fn on_an_8_mib_thread(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(work)
        .expect("the worker spawns")
        .join()
        .expect("the worker finishes");
}

/// Heads of a state that logs `acc` entries in a builtin list: the list's symbols and `acc`
/// build values, and `f` is a partial function defined by its equations alone.
struct LogHeads;

impl valueless::Heads for LogHeads {
    fn is_equational_partial(&self, symbol: &str) -> bool {
        symbol == "f"
    }

    fn is_data(&self, symbol: &str) -> bool {
        matches!(
            symbol,
            "Lbl'Unds'List'Unds'" | "LblListItem" | "Lbl'Stop'List" | "acc" | "state"
        )
    }
}

fn apply(name: &str, arguments: Vec<k_rust::kore::ast::Pattern>) -> k_rust::kore::ast::Pattern {
    k_rust::kore::ast::Pattern::Application {
        symbol: k_rust::kore::ast::Symbol {
            name: name.to_owned(),
            sort_parameters: Vec::new(),
        },
        arguments,
    }
}

/// How a log's `_List_` chain nests: each entry concatenated after the entries before it (`Left`),
/// as a step that appends to a log builds it, or before the entries after it (`Right`).
#[derive(Clone, Copy, Debug)]
enum Nesting {
    Left,
    Right,
}

/// `state(log)`, `log` a `_List_` chain of [`LOG_ENTRIES`] `acc` entries nested as `nesting`
/// says, over `first`, the chain's innermost part.
fn logged(first: k_rust::kore::ast::Pattern, nesting: Nesting) -> k_rust::kore::ast::Pattern {
    let mut log = first;
    for entry in 0..LOG_ENTRIES {
        let value = k_rust::kore::ast::Pattern::DomainValue {
            sort: k_rust::kore::ast::Sort::Application {
                name: "SortInt".to_owned(),
                arguments: Vec::new(),
            },
            value: k_rust::kore::ast::KoreString::from_bytes(entry.to_string().into_bytes()),
        };
        let item = apply("LblListItem", vec![apply("acc", vec![value])]);
        let arguments = match nesting {
            Nesting::Left => vec![log, item],
            Nesting::Right => vec![item, log],
        };
        log = apply("Lbl'Unds'List'Unds'", arguments);
    }
    apply("state", vec![log])
}

fn state_sort() -> k_rust::kore::ast::Sort {
    k_rust::kore::ast::Sort::Application {
        name: "SortState".to_owned(),
        arguments: Vec::new(),
    }
}

/// A state that holds a million-entry log, nested either way, is read on an 8 MiB thread: whether
/// it is a value, the witnesses it holds, whether it holds a variable, and a `#Ceil` of it.
#[test]
fn a_million_entry_log_is_read_for_witnesses_on_an_8_mib_thread() {
    on_an_8_mib_thread(|| {
        for nesting in [Nesting::Left, Nesting::Right] {
            let heads = LogHeads;
            let empty = logged(apply("Lbl'Stop'List", Vec::new()), nesting);
            assert!(valueless::is_value(&empty, &heads));
            assert!(!valueless::is_symbolic(&empty));
            let mut held = Vec::new();
            valueless::witnesses(&empty, &heads, &mut held);
            assert!(held.is_empty());
            let ceil = k_rust::kore::ast::Pattern::Ceil {
                operand_sort: Box::new(state_sort()),
                result_sort: state_sort(),
                argument: Box::new(empty),
            };
            let mut read = Vec::new();
            assert_eq!(
                valueless::read(&[&ceil], &heads, &mut read),
                valueless::Reading::Holds
            );
            drop(ceil);

            // The witness is the log's innermost part, a million levels down.
            let witness = pattern(F_TRUE);
            let over_witness = logged(witness.clone(), nesting);
            assert!(!valueless::is_value(&over_witness, &heads));
            let mut held = Vec::new();
            valueless::witnesses(&over_witness, &heads, &mut held);
            assert_eq!(held, [&witness]);
            let ceil = k_rust::kore::ast::Pattern::Ceil {
                operand_sort: Box::new(state_sort()),
                result_sort: state_sort(),
                argument: Box::new(over_witness),
            };
            let mut read = Vec::new();
            assert_eq!(
                valueless::read(&[&ceil], &heads, &mut read),
                valueless::Reading::Fails
            );
            assert_eq!(read, [&witness]);
            drop(ceil);

            // A variable a million levels down is found, and a quantifier's own variable there is
            // not the run's.
            let variable = k_rust::kore::ast::Variable {
                kind: k_rust::kore::ast::VariableKind::Element,
                name: "VarV".to_owned(),
                sort: state_sort(),
            };
            let over_variable = logged(
                k_rust::kore::ast::Pattern::Variable(variable.clone()),
                nesting,
            );
            assert!(valueless::is_symbolic(&over_variable));
            let bound = k_rust::kore::ast::Pattern::Exists {
                sort: state_sort(),
                variable: Box::new(variable.clone()),
                body: Box::new(k_rust::kore::ast::Pattern::Equals {
                    operand_sort: Box::new(state_sort()),
                    result_sort: state_sort(),
                    left: Box::new(k_rust::kore::ast::Pattern::Variable(variable)),
                    right: Box::new(over_variable),
                }),
            };
            let mut read = Vec::new();
            assert_eq!(
                valueless::read(&[&bound], &heads, &mut read),
                valueless::Reading::Open { over: vec![&bound] }
            );
            assert!(read.is_empty());
        }
    });
}

/// A state whose path condition is a million conjuncts, nested one `#And` per conjunct, splits
/// on an 8 MiB thread into its configuration and its conjuncts in order.
#[test]
fn a_million_nested_conjuncts_split_on_an_8_mib_thread() {
    on_an_8_mib_thread(|| {
        let configuration = apply("go", Vec::new());
        let conjunct = |index: usize| k_rust::kore::ast::Pattern::Equals {
            operand_sort: Box::new(state_sort()),
            result_sort: state_sort(),
            left: Box::new(apply("acc", vec![apply(&format!("c{index}"), Vec::new())])),
            right: Box::new(apply("acc", vec![apply(&format!("c{index}"), Vec::new())])),
        };
        let mut condition = conjunct(LOG_ENTRIES - 1);
        for index in (0..LOG_ENTRIES - 1).rev() {
            condition = k_rust::kore::ast::Pattern::And {
                sort: state_sort(),
                arguments: vec![conjunct(index), condition],
            };
        }
        let state = k_rust::kore::ast::Pattern::And {
            sort: state_sort(),
            arguments: vec![configuration.clone(), condition],
        };
        let split = valueless::split(&state);
        assert_eq!(split.configuration, Some(&configuration));
        assert_eq!(split.predicates.len(), LOG_ENTRIES);
        for index in [0, 1, LOG_ENTRIES - 1] {
            assert_eq!(
                split.predicates[index],
                &conjunct(index),
                "conjunct {index}"
            );
        }
    });
}

/// A timeout replaces an undecided or bounded part of a claim, never a refutation: a
/// counterexample or a failure refutes the claim whatever the parts not yet proven give.
#[test]
fn a_timeout_is_weaker_than_an_undecided_part_and_stronger_than_a_refutation() {
    use super::Verdict::{
        BreadthBound, DepthBound, Disproved, Failed, Indeterminate, Proven, Timeout,
    };
    for refuted in [Disproved, Failed] {
        assert_eq!(refuted.weakest(Timeout), refuted);
        assert_eq!(Timeout.weakest(refuted), refuted);
    }
    for open in [Indeterminate, DepthBound, BreadthBound, Proven] {
        assert_eq!(open.weakest(Timeout), Timeout);
        assert_eq!(Timeout.weakest(open), Timeout);
    }
    assert_eq!(Timeout.as_str(), "timeout");
    assert_eq!(serde_json::to_value(Timeout).unwrap(), "timeout");
}
