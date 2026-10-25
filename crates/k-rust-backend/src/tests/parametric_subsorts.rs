//! A declared subsort relates whole closed sorts, without covariance of their arguments.

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::{BackendDefinition, DefinitionError},
    matching::{
        InjectionEquality, MatchMode, MatchResult, SortError, SortGraph, UndecidedReason,
        match_injection_equality, match_terms_in_definition,
    },
    term::{Name, Sort, Term, Variable},
};

fn subsort_axiom(sub: &str, sup: &str) -> String {
    format!(
        r#"axiom{{R}} \exists{{R}}(Value:{sup},
            \equals{{{sup}, R}}(Value:{sup}, inj{{{sub}, {sup}}}(From:{sub})))
            [subsort{{{sub}, {sup}}}()]"#,
    )
}

fn load(source: &str) -> BackendDefinition {
    BackendDefinition::internalize(
        &parse_definition(source).expect("definition should parse"),
        "MAIN",
    )
    .expect("definition should load")
}

fn definition() -> BackendDefinition {
    let pairs = [
        ("SortMInt{Sort8{}}", "SortKResult{}"),
        ("SortKResult{}", "SortKItem{}"),
        ("SortMInt{Sort8{}}", "SortKItem{}"),
        ("SortMInt{Sort16{}}", "SortKItem{}"),
        ("SortMInt{Sort16{}}", "SortWide{}"),
        ("SortWide{}", "SortKItem{}"),
        ("SortFoo{}", "SortBar{}"),
        ("SortFoo{}", "SortKItem{}"),
        ("SortBar{}", "SortKItem{}"),
        ("SortMInt{SortFoo{}}", "SortKItem{}"),
        ("SortMInt{SortBar{}}", "SortKItem{}"),
    ];
    let axioms = pairs
        .iter()
        .map(|(sub, sup)| subsort_axiom(sub, sup))
        .collect::<Vec<_>>()
        .join("\n");
    load(&format!(
        r#"[] module MAIN
            sort SortKItem{{}} []
            sort SortKResult{{}} []
            sort SortWide{{}} []
            sort SortFoo{{}} []
            sort SortBar{{}} []
            sort Sort8{{}} []
            sort Sort16{{}} []
            hooked-sort SortMInt{{S}} [hasDomainValues{{}}(), hook{{}}("MINT.MInt")]
            symbol inj{{From, To}}(From) : To [sortInjection{{}}()]
            symbol mk{{}}() : SortMInt{{Sort8{{}}}} [function{{}}(), total{{}}()]
            {axioms}
        endmodule []"#,
    ))
}

fn mint(argument: &str) -> Sort {
    Sort::application("SortMInt", vec![Sort::simple(argument)])
}

fn checked_term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
        .expect("checked term should internalize")
}

#[test]
fn a_declared_instance_subsorts_hold_across_arities() {
    let definition = definition();
    for (sub, sup) in [
        (mint("Sort8"), Sort::simple("SortKResult")),
        (mint("Sort8"), Sort::simple("SortKItem")),
        (mint("Sort16"), Sort::simple("SortWide")),
    ] {
        assert_eq!(definition.sort_graph().check_subsort(&sub, &sup), Ok(true));
    }
}

#[test]
fn b_instance_axioms_do_not_relate_other_instances_or_reverse_the_order() {
    let definition = definition();
    for (sub, sup) in [
        (mint("Sort16"), Sort::simple("SortKResult")),
        (Sort::simple("SortKResult"), mint("Sort8")),
        (mint("Sort8"), mint("Sort16")),
        (Sort::simple("SortWide"), Sort::simple("SortKResult")),
    ] {
        assert_eq!(definition.sort_graph().check_subsort(&sub, &sup), Ok(false));
    }
}

#[test]
fn c_sort_arguments_do_not_induce_covariance_or_overlap() {
    let definition = definition();
    let (left, right) = (mint("SortFoo"), mint("SortBar"));
    assert_eq!(
        definition.sort_graph().check_subsort(&left, &right),
        Ok(false)
    );
    assert_eq!(
        definition.sort_graph().known_overlap(&left, &right),
        Some(false)
    );
}

#[test]
fn d_overlap_requires_a_common_closed_subsort() {
    let definition = definition();
    let result = Sort::simple("SortKResult");
    assert_eq!(
        definition
            .sort_graph()
            .known_overlap(&result, &Sort::simple("SortWide")),
        Some(false),
    );
    assert_eq!(
        definition
            .sort_graph()
            .known_overlap(&Sort::simple("SortKItem"), &result),
        Some(true),
    );
    assert_eq!(
        definition
            .sort_graph()
            .known_overlap(&mint("Sort8"), &result),
        Some(true)
    );
}

#[test]
fn e_schematic_instances_report_variables_unless_every_instance_is_unrelated() {
    let definition = definition();
    let schematic = Sort::application("SortMInt", vec![Sort::variable("W")]);
    assert_eq!(
        definition
            .sort_graph()
            .check_subsort(&schematic, &Sort::simple("SortKItem")),
        Err(SortError::FoundSortVariable("W".into())),
    );
    assert_eq!(
        definition
            .sort_graph()
            .check_subsort(&schematic, &Sort::simple("SortFoo")),
        Ok(false),
    );
    assert_eq!(
        definition
            .sort_graph()
            .check_subsort(&mint("Sort8"), &schematic),
        Err(SortError::FoundSortVariable("W".into())),
    );
    assert_eq!(
        SortError::FoundSortVariable("W".into()).to_string(),
        "whether one sort is a subsort of another depends on the sort variable W"
    );
    let undeclared = definition
        .sort_graph()
        .check_subsort(&schematic, &Sort::simple("SortUndeclared"))
        .unwrap_err();
    assert_eq!(
        undeclared.to_string(),
        "the sort SortUndeclared{} is not declared"
    );
}

#[test]
fn f_checked_injections_use_only_the_declared_closed_order() {
    let definition = definition();
    let accepted =
        parse_pattern(r#"inj{SortMInt{Sort8{}}, SortKResult{}}(\dv{SortMInt{Sort8{}}}("5p8"))"#)
            .unwrap();
    assert!(definition.internalize_term(&accepted, &[]).is_ok());
    for source in [
        r#"inj{SortMInt{Sort16{}}, SortKResult{}}(\dv{SortMInt{Sort16{}}}("5p16"))"#,
        "inj{SortMInt{SortFoo{}}, SortMInt{SortBar{}}}(X:SortMInt{SortFoo{}})",
    ] {
        assert!(
            matches!(
                definition.internalize_term(&parse_pattern(source).unwrap(), &[]),
                Err(DefinitionError::NotSubsort { .. }),
            ),
            "{source}"
        );
    }
}

#[test]
fn g_injection_matching_binds_declared_instances_and_refutes_covariance() {
    let definition = definition();
    let pattern = checked_term(
        &definition,
        "inj{SortKResult{}, SortKItem{}}(V:SortKResult{})",
    );
    let subject = checked_term(
        &definition,
        r#"inj{SortMInt{Sort8{}}, SortKItem{}}(\dv{SortMInt{Sort8{}}}("5p8"))"#,
    );
    let result = match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject);
    let MatchResult::Success(substitution) = result else {
        panic!("a declared instance must match its supersort: {result:?}");
    };
    let expected = checked_term(
        &definition,
        r#"inj{SortMInt{Sort8{}}, SortKResult{}}(\dv{SortMInt{Sort8{}}}("5p8"))"#,
    );
    assert_eq!(substitution.len(), 1);
    assert_eq!(
        substitution.get(&Variable::new("V", Sort::simple("SortKResult"))),
        Some(&expected)
    );

    let pattern = checked_term(
        &definition,
        "inj{SortMInt{SortBar{}}, SortKItem{}}(X:SortMInt{SortBar{}})",
    );
    let subject = checked_term(
        &definition,
        "inj{SortMInt{SortFoo{}}, SortKItem{}}(Y:SortMInt{SortFoo{}})",
    );
    assert!(matches!(
        match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject),
        MatchResult::Failed(_),
    ));
}

const PARAMETRIC_LIST: &str = r#"[]
module MAIN
  sort SortElement{} [hasDomainValues{}()]
  sort SortA{} []
  hooked-sort SortL{S}
    [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
  hooked-symbol listUnit{}() : SortL{SortA{}} [function{}(), total{}(), hook{}("LIST.unit")]
  hooked-symbol listItem{}(SortElement{}) : SortL{SortA{}} [function{}(), total{}(), hook{}("LIST.element")]
  hooked-symbol listConcat{}(SortL{SortA{}}, SortL{SortA{}}) : SortL{SortA{}} [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
  symbol keep{}(SortL{SortA{}}) : SortElement{} [function{}(), total{}(), no-evaluators{}()]
endmodule []
"#;

#[test]
fn h_parametric_collection_sorts_are_rejected_at_load() {
    let syntax = parse_definition(PARAMETRIC_LIST).unwrap();
    let result = BackendDefinition::internalize(&syntax, "MAIN");
    let Err(DefinitionError::MalformedCollection(message)) = result else {
        panic!("a collection declaration with parameters must fail at load: {result:?}");
    };
    assert!(message.contains("SortL"), "{message}");
}

#[test]
fn i_all_subsets_of_closed_sort_axioms_match_a_naive_closure_oracle() {
    let names = [
        "SortA{}",
        "SortB{}",
        "SortC{}",
        "SortS{SortA{}}",
        "SortS{SortB{}}",
        "SortS{SortC{}}",
    ];
    let sorts = [
        Sort::simple("SortA"),
        Sort::simple("SortB"),
        Sort::simple("SortC"),
        Sort::application("SortS", vec![Sort::simple("SortA")]),
        Sort::application("SortS", vec![Sort::simple("SortB")]),
        Sort::application("SortS", vec![Sort::simple("SortC")]),
    ];
    let candidates = [
        (0, 1),
        (1, 2),
        (3, 0),
        (4, 1),
        (3, 5),
        (5, 2),
        (0, 5),
        (4, 0),
    ];
    for subset in 0..256 {
        let mut below = [[false; 6]; 6];
        for (index, row) in below.iter_mut().enumerate() {
            row[index] = true;
        }
        let mut axioms = String::new();
        for (index, &(sub, sup)) in candidates.iter().enumerate() {
            if subset & (1 << index) != 0 {
                below[sub][sup] = true;
                axioms.push_str(&subsort_axiom(names[sub], names[sup]));
                axioms.push('\n');
            }
        }
        for middle in 0..6 {
            for sub in 0..6 {
                for sup in 0..6 {
                    below[sub][sup] |= below[sub][middle] && below[middle][sup];
                }
            }
        }
        let definition = load(&format!(
            r#"[] module MAIN
                sort SortA{{}} []
                sort SortB{{}} []
                sort SortC{{}} []
                sort SortS{{X}} []
                symbol inj{{From, To}}(From) : To [sortInjection{{}}()]
                {axioms}
            endmodule []"#,
        ));
        for (left, left_sort) in sorts.iter().enumerate() {
            for (right, right_sort) in sorts.iter().enumerate() {
                assert_eq!(
                    definition.sort_graph().check_subsort(left_sort, right_sort),
                    Ok(below[left][right]),
                    "subset {subset:#010b}: {} <= {}",
                    names[left],
                    names[right],
                );
                let overlap = (0..6).any(|sub| below[sub][left] && below[sub][right]);
                assert_eq!(
                    definition.sort_graph().known_overlap(left_sort, right_sort),
                    Some(overlap),
                    "subset {subset:#010b}: overlap of {} and {}",
                    names[left],
                    names[right],
                );
            }
        }
    }
}

#[test]
fn j_total_builders_inhabit_closed_instances_and_their_supersorts() {
    let definition = definition();
    assert!(definition.sort_is_inhabited(&mint("Sort8")));
    assert!(definition.sort_is_inhabited(&Sort::simple("SortKResult")));
    assert!(!definition.sort_is_inhabited(&mint("Sort16")));
}

fn schematic_mint() -> Sort {
    Sort::application("SortMInt", vec![Sort::variable("W")])
}

/// A sort-parametric pattern stands for each of its closed instances: `inj{SortMInt{W},
/// SortKItem}(X)` matches an injection from `SortMInt{Sort8}` at `W = Sort8`, and `X:SortMInt{W}`
/// matches a value of `SortMInt{Sort8}` there. The matcher binds no sort variable, so it leaves
/// both undecided in every mode, and mints no refutation from them.
#[test]
fn k_sort_variable_subsort_questions_leave_the_match_undecided() {
    let definition = definition();
    let schematic = schematic_mint();
    let operand = Term::variable(Variable::new("X", schematic));
    let injected = Term::injection(schematic, Sort::simple("SortKItem"), operand.clone());
    let subject = checked_term(
        &definition,
        r#"inj{SortMInt{Sort8{}}, SortKItem{}}(\dv{SortMInt{Sort8{}}}("5p8"))"#,
    );
    let value = checked_term(&definition, r#"\dv{SortMInt{Sort8{}}}("5p8")"#);
    let undecided = MatchResult::Undecided(UndecidedReason::Subsorting(
        SortError::FoundSortVariable("W".into()),
    ));
    for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
        let matched = match_terms_in_definition(mode, &definition, &injected, &subject);
        assert_eq!(matched, undecided, "{mode:?}");
        assert!(matched.refutation().is_none(), "{mode:?}");
        assert_eq!(
            match_terms_in_definition(mode, &definition, &operand, &value),
            undecided,
            "{mode:?}"
        );
    }
}

/// `inj{A,C}(a) = inj{B,C}(b)` is decided only from what the subsort order establishes. One
/// source below the other splits the equation, since `inj{A,C}(a) = inj{B,C}(inj{A,B}(a))`.
/// Two sources neither of which is below the other share only the injections of values of
/// common subsorts, which a constructor-like operand is not, so such an operand separates them,
/// and so does the absence of a common subsort. Without the order, or where the answer depends
/// on a sort variable, nothing is established.
#[test]
fn l_injection_equality_separates_only_established_incomparable_sources() {
    let (a, b, c) = (
        Sort::simple("SortA"),
        Sort::simple("SortB"),
        Sort::simple("SortC"),
    );
    let constructor_like = Term::raw_domain_value(a, "a");
    let x = Term::variable(Variable::new("X", b));
    let y = Term::variable(Variable::new("Y", a));
    let inject = |source: &Sort, operand: &Term| Term::injection(*source, c, operand.clone());
    let (left, symbolic_left, right) = (
        inject(&a, &constructor_like),
        inject(&a, &y),
        inject(&b, &x),
    );
    // Each sort with every sort below it.
    let graph = |pairs: Vec<(&str, Vec<&str>)>| {
        let mut graph = SortGraph::default();
        for (sup, subs) in pairs {
            graph.insert(sup, subs.into_iter().map(Name::from));
        }
        graph
    };

    assert_eq!(
        match_injection_equality(None, &left, &right),
        Some(InjectionEquality::Unknown),
        "no order: B may be above A"
    );

    let ordered = graph(vec![
        ("SortC", vec!["SortA", "SortB"]),
        ("SortB", vec!["SortA"]),
        ("SortA", vec![]),
    ]);
    assert_eq!(
        match_injection_equality(Some(&ordered), &left, &right),
        Some(InjectionEquality::Split(
            Term::injection(a, b, constructor_like.clone()),
            x.clone(),
        )),
    );

    let disjoint = graph(vec![
        ("SortC", vec!["SortA", "SortB"]),
        ("SortA", vec![]),
        ("SortB", vec![]),
    ]);
    for left in [&left, &symbolic_left] {
        assert_eq!(
            match_injection_equality(Some(&disjoint), left, &right),
            Some(InjectionEquality::Distinct),
            "{left:?}"
        );
    }

    let overlapping = graph(vec![
        ("SortC", vec!["SortA", "SortB", "SortD"]),
        ("SortA", vec!["SortD"]),
        ("SortB", vec!["SortD"]),
        ("SortD", vec![]),
    ]);
    assert_eq!(
        match_injection_equality(Some(&overlapping), &left, &right),
        Some(InjectionEquality::Distinct),
    );
    assert_eq!(
        match_injection_equality(Some(&overlapping), &symbolic_left, &right),
        Some(InjectionEquality::Unknown),
    );

    // `inj{SortMInt{W}, SortKItem}(X) = inj{SortMInt{Sort8}, SortKItem}(5p8)` holds at
    // `W = Sort8, X = 5p8`.
    let definition = definition();
    let schematic = schematic_mint();
    let open = Term::injection(
        schematic,
        Sort::simple("SortKItem"),
        Term::variable(Variable::new("X", schematic)),
    );
    let closed = checked_term(
        &definition,
        r#"inj{SortMInt{Sort8{}}, SortKItem{}}(\dv{SortMInt{Sort8{}}}("5p8"))"#,
    );
    assert_eq!(
        match_injection_equality(Some(definition.sort_graph()), &open, &closed),
        Some(InjectionEquality::Unknown),
    );
}
