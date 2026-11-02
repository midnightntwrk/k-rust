use std::collections::BTreeMap;

use k_rust::{
    backend::{
        Backend, BackendOptions, EffectOutput, ExecuteRequest, ExecutionLeaf, ExecutionStrategy,
        HaltReasonOutput,
    },
    kast::Sort as KastSort,
    kore::parser::parse_pattern,
    names::BuiltinSort,
};

use super::{
    ConfigVariable, ExecError, Halt, OnePath, PathError, SearchMode, SearchOptions,
    check_final_state, config_variables, log_lines, one_path, result_sort_hooks, search_backend,
    term, valueless,
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

/// `KRS_CHECK_ENDS`'s check: a state reported stuck where no rule applies passes (`left`, an end
/// of the branching run); one a rule leaves (`initial`, the start the rules rewrite) fails,
/// naming the steps taken from it.
#[test]
fn a_stuck_end_holds_only_where_no_rule_applies() {
    let mut backend = branching_backend();
    let mut request = ExecuteRequest::new(parse_pattern("initial{}()").unwrap());
    request.strategy = ExecutionStrategy::Any;
    let end = one_path(backend.execute(request).unwrap().leaves).unwrap();
    assert_eq!(end.reason, HaltReasonOutput::Stuck);
    check_final_state(&mut backend, &end.state, "the run ended stuck").unwrap();

    let mut request = ExecuteRequest::new(parse_pattern("initial{}()").unwrap());
    request.max_depth = Some(0);
    let start = one_path(backend.execute(request).unwrap().leaves).unwrap();
    let reported = ExecutionLeaf {
        reason: HaltReasonOutput::Stuck,
        ..start
    };
    let Err(ExecError::Result(message)) =
        check_final_state(&mut backend, &reported.state, "the run ended stuck")
    else {
        panic!("a state two rules leave is no stuck end");
    };
    assert!(
        message.starts_with("KRS_CHECK_ENDS: the run ended stuck at a state")
            && message.contains("after 1 step(s)"),
        "{message}"
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

fn leaves(backend: &mut Backend, state: &str, strategy: ExecutionStrategy) -> Vec<ExecutionLeaf> {
    let mut request = ExecuteRequest::new(parse_pattern(state).unwrap());
    request.strategy = strategy;
    backend.execute(request).unwrap().leaves
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
        term(&path.leaf.state, &hooks).unwrap().kore().to_string(),
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
    let claims = vec![super::ClaimInfo {
        label: "EMPTY-EVIDENCE-SPEC.empty".into(),
        module: "EMPTY-EVIDENCE-SPEC".into(),
        modality: super::Modality::AllPath,
        origin: None,
        trusted: false,
        backend_label: "EMPTY-EVIDENCE-SPEC.empty".into(),
    }];
    let reports = super::prove_claims(
        &mut backend,
        &hooks,
        &claims,
        &super::ProveOptions::default(),
    )
    .unwrap();
    assert_eq!(reports[0].verdict, super::Verdict::Proven);
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
fn leaf(state: &str, depth: u64) -> ExecutionLeaf {
    let mut backend = partial_backend();
    let mut leaf = leaves(&mut backend, "initial{}()", ExecutionStrategy::Any)
        .into_iter()
        .find(|leaf| leaf.reason == HaltReasonOutput::Stuck)
        .expect("a stuck leaf");
    leaf.state = k_rust::kore::json::to_value(&pattern(state)).unwrap();
    leaf.depth = depth;
    leaf.trace.clear();
    leaf
}

fn state(path: &OnePath) -> String {
    super::kore_pattern(&path.leaf.state).unwrap().to_string()
}

const F_TRUE: &str = r#"f{}(\dv{SortBool{}}("true"))"#;

/// The two leaves the backend returns where a rule's condition reads `f(true)`, the application
/// of a partial function defined by its equations alone, none of which applies at `true`
/// (finding NT-37-2): the rule applied where `f(true)` is defined and `true`, and the state left
/// where it is not `true`.
fn split_over(term: &str, held: &str) -> Vec<ExecutionLeaf> {
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
/// found there (`prj(noval(red))`, `duo(prj(opq(1)), size(red))`, alias_clauses).
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
