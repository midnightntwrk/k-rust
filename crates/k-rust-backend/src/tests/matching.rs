//! Crate-internal contracts of `crate::matching` (`pub(crate)` entry points).

use std::{collections::BTreeSet, sync::Arc};

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use super::matching_oracle::{match_map_terms_all, match_set_terms_all};
use crate::{
    definition::BackendDefinition,
    matching::*,
    substitution::Substitution,
    term::{CollectionSymbols, MapDefinition, Name, Sort, Term, TermKind, Variable},
};

fn variable(name: &str, sort: Sort) -> Variable {
    Variable::new(name, sort)
}

fn var(name: &str, sort: Sort) -> Term {
    Term::variable(variable(name, sort))
}

fn domain_value(sort: Sort, value: &str) -> Term {
    Term::domain_value(sort, value)
}

fn collection_symbols(prefix: &str) -> CollectionSymbols {
    CollectionSymbols {
        unit: format!("{prefix}Unit").into(),
        element: format!("{prefix}Element").into(),
        concat: format!("{prefix}Concat").into(),
    }
}

fn map_definition() -> Arc<MapDefinition> {
    Arc::new(MapDefinition {
        symbols: collection_symbols("map"),
        key_sort: "MapKey".into(),
        value_sort: "MapValue".into(),
        map_sort: "MapSort".into(),
    })
}

fn collection_definition() -> BackendDefinition {
    let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortElement{} [hasDomainValues{}()]
                sort SortKey{} [hasDomainValues{}()]
                sort SortValue{} [hasDomainValues{}()]
                hooked-sort SortList{}
                    [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
                hooked-sort SortSet{}
                    [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
                hooked-symbol listItem{}(SortElement{}) : SortList{} [function{}(), total{}(), hook{}("LIST.element")]
                hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{} [function{}(), hook{}("LIST.concat"), assoc{}()]
                symbol opaqueList{}(SortElement{}) : SortList{} [function{}(), total{}()]
                hooked-symbol setUnit{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
                hooked-symbol setItem{}(SortElement{}) : SortSet{} [function{}(), total{}(), hook{}("SET.element")]
                hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{} [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
                hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol opaqueMap{}(SortElement{}) : SortMap{} [function{}(), total{}()]
                symbol opaqueSet{}(SortElement{}) : SortSet{} [function{}(), total{}()]
            endmodule []"#,
        )
        .expect("collection definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("collection definition should internalize")
}

fn internal_term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
        .expect("term should internalize")
}

fn solve_with_test_frames(
    definition: &BackendDefinition,
    pairs: &[(Term, Term)],
) -> Option<Vec<CollectionSolution>> {
    let mut counter = 0;
    let mut fresh_frame = |sort: &Sort| {
        let variable = Variable::new(format!("Ex#Frame!{counter}"), sort.clone());
        counter += 1;
        variable
    };
    let mut narrowing = Narrowing {
        fresh_frame: &mut fresh_frame,
    };
    solve_collection_pairs_in_definition(
        MatchMode::Rewrite,
        definition,
        Substitution::new(),
        pairs,
        Some(&mut narrowing),
    )
}

#[test]
fn symmetrically_unifies_a_closed_list_with_an_open_list() {
    let definition = collection_definition();
    let first = r#"\dv{SortElement{}}("first")"#;
    let second = r#"\dv{SortElement{}}("second")"#;
    let closed = internal_term(
        &definition,
        &format!("listConcat{{}}(listItem{{}}({first}), listItem{{}}({second}))"),
    );
    let open = internal_term(
        &definition,
        "listConcat{}(listItem{}(ELEMENT:SortElement{}), REST:SortList{})",
    );
    let expected_rest = internal_term(&definition, &format!("listItem{{}}({second})"));

    assert_eq!(
        solve_with_test_frames(&definition, &[(closed, open)]),
        Some(vec![CollectionSolution {
            substitution: Substitution::from([
                (
                    Variable::new("ELEMENT", Sort::simple("SortElement")),
                    internal_term(&definition, first),
                ),
                (
                    Variable::new("REST", Sort::simple("SortList")),
                    expected_rest,
                ),
            ]),
            constraints: Vec::new(),
            fresh: BTreeSet::new(),
        }])
    );
}

#[test]
fn symmetrically_enumerates_set_selections_from_a_closed_set() {
    let definition = collection_definition();
    let first = r#"\dv{SortElement{}}("first")"#;
    let second = r#"\dv{SortElement{}}("second")"#;
    let closed = internal_term(
        &definition,
        &format!("setConcat{{}}(setItem{{}}({first}), setItem{{}}({second}))"),
    );
    let open = internal_term(
        &definition,
        "setConcat{}(setItem{}(ELEMENT:SortElement{}), REST:SortSet{})",
    );
    let element = Variable::new("ELEMENT", Sort::simple("SortElement"));
    let rest = Variable::new("REST", Sort::simple("SortSet"));
    let mut expected = vec![
        CollectionSolution {
            substitution: Substitution::from([
                (element.clone(), internal_term(&definition, first)),
                (
                    rest.clone(),
                    internal_term(&definition, &format!("setItem{{}}({second})")),
                ),
            ]),
            constraints: Vec::new(),
            fresh: BTreeSet::new(),
        },
        CollectionSolution {
            substitution: Substitution::from([
                (element, internal_term(&definition, second)),
                (
                    rest,
                    internal_term(&definition, &format!("setItem{{}}({first})")),
                ),
            ]),
            constraints: Vec::new(),
            fresh: BTreeSet::new(),
        },
    ];
    expected.sort();

    assert_eq!(
        solve_with_test_frames(&definition, &[(closed, open)]),
        Some(expected)
    );
}

#[test]
fn symmetrically_enumerates_map_selections_from_a_closed_map() {
    let definition = collection_definition();
    let first_key = r#"\dv{SortKey{}}("first")"#;
    let first_value = r#"\dv{SortValue{}}("first-value")"#;
    let second_key = r#"\dv{SortKey{}}("second")"#;
    let second_value = r#"\dv{SortValue{}}("second-value")"#;
    let closed = internal_term(
        &definition,
        &format!(
            "mapConcat{{}}(mapItem{{}}({first_key}, {first_value}), mapItem{{}}({second_key}, {second_value}))"
        ),
    );
    let open = internal_term(
        &definition,
        "mapConcat{}(mapItem{}(KEY:SortKey{}, VALUE:SortValue{}), REST:SortMap{})",
    );
    let key = Variable::new("KEY", Sort::simple("SortKey"));
    let value = Variable::new("VALUE", Sort::simple("SortValue"));
    let rest = Variable::new("REST", Sort::simple("SortMap"));
    let mut expected = vec![
        CollectionSolution {
            substitution: Substitution::from([
                (key.clone(), internal_term(&definition, first_key)),
                (value.clone(), internal_term(&definition, first_value)),
                (
                    rest.clone(),
                    internal_term(
                        &definition,
                        &format!("mapItem{{}}({second_key}, {second_value})"),
                    ),
                ),
            ]),
            constraints: Vec::new(),
            fresh: BTreeSet::new(),
        },
        CollectionSolution {
            substitution: Substitution::from([
                (key, internal_term(&definition, second_key)),
                (value, internal_term(&definition, second_value)),
                (
                    rest,
                    internal_term(
                        &definition,
                        &format!("mapItem{{}}({first_key}, {first_value})"),
                    ),
                ),
            ]),
            constraints: Vec::new(),
            fresh: BTreeSet::new(),
        },
    ];
    expected.sort();

    assert_eq!(
        solve_with_test_frames(&definition, &[(closed, open)]),
        Some(expected)
    );
}

#[test]
fn cancels_common_opaque_set_chunks_before_solving_the_residual_frame() {
    let definition = collection_definition();
    let left = internal_term(
        &definition,
        "setConcat{}(setItem{}(X:SortElement{}), setConcat{}(U:SortSet{}, setConcat{}(V:SortSet{}, V:SortSet{})))",
    );
    let right = internal_term(
        &definition,
        "setConcat{}(setItem{}(Y:SortElement{}), setConcat{}(U:SortSet{}, setConcat{}(V:SortSet{}, setConcat{}(T:SortSet{}, U:SortSet{}))))",
    );

    assert_eq!(
        solve_with_test_frames(&definition, &[(left, right)]),
        Some(vec![CollectionSolution {
            substitution: Substitution::from([
                (
                    Variable::new("T", Sort::simple("SortSet")),
                    internal_term(&definition, "setUnit{}()"),
                ),
                (
                    Variable::new("X", Sort::simple("SortElement")),
                    internal_term(&definition, "Y:SortElement{}"),
                ),
            ]),
            constraints: Vec::new(),
            fresh: BTreeSet::new(),
        }])
    );
}

#[test]
fn cancels_common_opaque_map_chunks_before_solving_the_residual_frame() {
    let definition = collection_definition();
    let left = internal_term(
        &definition,
        "mapConcat{}(mapItem{}(K1:SortKey{}, V1:SortValue{}), mapConcat{}(U:SortMap{}, mapConcat{}(V:SortMap{}, V:SortMap{})))",
    );
    let right = internal_term(
        &definition,
        "mapConcat{}(mapItem{}(K2:SortKey{}, V2:SortValue{}), mapConcat{}(U:SortMap{}, mapConcat{}(V:SortMap{}, mapConcat{}(T:SortMap{}, U:SortMap{}))))",
    );

    assert_eq!(
        solve_with_test_frames(&definition, &[(left, right)]),
        Some(vec![CollectionSolution {
            substitution: Substitution::from([
                (
                    Variable::new("K1", Sort::simple("SortKey")),
                    internal_term(&definition, "K2:SortKey{}"),
                ),
                (
                    Variable::new("T", Sort::simple("SortMap")),
                    internal_term(&definition, "mapUnit{}()"),
                ),
                (
                    Variable::new("V1", Sort::simple("SortValue")),
                    internal_term(&definition, "V2:SortValue{}"),
                ),
            ]),
            constraints: Vec::new(),
            fresh: BTreeSet::new(),
        }])
    );
}

#[test]
fn carries_an_open_map_subject_frame_through_every_selection() {
    let definition = collection_definition();
    let first_key = r#"\dv{SortKey{}}("first")"#;
    let first_value = r#"\dv{SortValue{}}("first-value")"#;
    let second_key = r#"\dv{SortKey{}}("second")"#;
    let second_value = r#"\dv{SortValue{}}("second-value")"#;
    let pattern = internal_term(
        &definition,
        "mapConcat{}(mapItem{}(KEY:SortKey{}, VALUE:SortValue{}), REST:SortMap{})",
    );
    let subject = internal_term(
        &definition,
        &format!(
            "mapConcat{{}}(mapConcat{{}}(mapItem{{}}({first_key}, {first_value}), mapItem{{}}({second_key}, {second_value})), SUBJECTREST:SortMap{{}})"
        ),
    );

    let solutions = solve_with_test_frames(&definition, &[(pattern, subject)])
        .expect("the open Map selection should be decidable");
    assert_eq!(solutions.len(), 3);
    let subject_rest = Variable::new("SUBJECTREST", Sort::simple("SortMap"));
    let key = Variable::new("KEY", Sort::simple("SortKey"));
    let rest = Variable::new("REST", Sort::simple("SortMap"));
    let explicit = solutions
        .iter()
        .filter(|solution| solution.fresh.is_empty())
        .collect::<Vec<_>>();
    assert_eq!(explicit.len(), 2);
    assert_eq!(
        explicit
            .iter()
            .map(|solution| solution.substitution[&key].clone())
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([
            internal_term(&definition, first_key),
            internal_term(&definition, second_key),
        ])
    );
    assert!(explicit.iter().all(|solution| {
        solution.substitution[&rest]
            .attributes()
            .variables
            .contains(&subject_rest)
    }));
    assert!(solutions.iter().any(|solution| !solution.fresh.is_empty()));
}

#[test]
fn solves_the_frame_branch_for_a_symbolic_map_key() {
    let definition = collection_definition();
    let pattern = internal_term(
        &definition,
        "mapConcat{}(mapItem{}(KEY:SortKey{}, VALUE:SortValue{}), REST:SortMap{})",
    );
    let TermKind::Map {
        definition: map_definition,
        ..
    } = pattern.kind()
    else {
        unreachable!()
    };
    let map_definition = map_definition.clone();
    let subject = internal_term(
        &definition,
        r#"mapConcat{}(mapItem{}(\dv{SortKey{}}("first"), \dv{SortValue{}}("first-value")), mapConcat{}(mapItem{}(\dv{SortKey{}}("second"), \dv{SortValue{}}("second-value")), SUBJECTREST:SortMap{}))"#,
    );
    let fresh = Variable::new("Ex#Frame!0", Sort::simple("SortMap"));

    let solutions = solve_with_test_frames(&definition, &[(pattern, subject)])
        .expect("the supported map shape should be decidable");

    assert_eq!(solutions.len(), 3);
    let frame_solution = solutions
        .iter()
        .find(|solution| !solution.fresh.is_empty())
        .expect("one solution should assign the symbolic entry to the subject frame");
    assert_eq!(frame_solution.fresh, BTreeSet::from([fresh.clone()]));
    assert!(frame_solution.constraints.is_empty());
    assert_eq!(
        frame_solution.substitution,
        Substitution::from([
            (
                Variable::new("REST", Sort::simple("SortMap")),
                Term::map(
                    map_definition.clone(),
                    vec![
                        (
                            internal_term(&definition, r#"\dv{SortKey{}}("first")"#,),
                            internal_term(&definition, r#"\dv{SortValue{}}("first-value")"#,),
                        ),
                        (
                            internal_term(&definition, r#"\dv{SortKey{}}("second")"#,),
                            internal_term(&definition, r#"\dv{SortValue{}}("second-value")"#,),
                        ),
                    ],
                    Some(Term::variable(fresh.clone())),
                ),
            ),
            (
                Variable::new("SUBJECTREST", Sort::simple("SortMap")),
                Term::map(
                    map_definition,
                    vec![(
                        internal_term(&definition, "KEY:SortKey{}"),
                        internal_term(&definition, "VALUE:SortValue{}"),
                    )],
                    Some(Term::variable(fresh)),
                ),
            ),
        ])
    );
}

#[test]
fn solves_the_frame_branch_for_a_symbolic_set_element() {
    let definition = collection_definition();
    let pattern = internal_term(
        &definition,
        "setConcat{}(setItem{}(ELEMENT:SortElement{}), REST:SortSet{})",
    );
    let TermKind::Set {
        definition: set_definition,
        ..
    } = pattern.kind()
    else {
        unreachable!()
    };
    let set_definition = set_definition.clone();
    let subject = internal_term(
        &definition,
        r#"setConcat{}(setItem{}(\dv{SortElement{}}("first")), setConcat{}(setItem{}(\dv{SortElement{}}("second")), SUBJECTREST:SortSet{}))"#,
    );
    let fresh = Variable::new("Ex#Frame!0", Sort::simple("SortSet"));

    let solutions = solve_with_test_frames(&definition, &[(pattern, subject)])
        .expect("the supported set shape should be decidable");

    assert_eq!(solutions.len(), 3);
    let frame_solution = solutions
        .iter()
        .find(|solution| !solution.fresh.is_empty())
        .expect("one solution should assign the symbolic element to the subject frame");
    assert_eq!(frame_solution.fresh, BTreeSet::from([fresh.clone()]));
    assert!(frame_solution.constraints.is_empty());
    assert_eq!(
        frame_solution.substitution,
        Substitution::from([
            (
                Variable::new("REST", Sort::simple("SortSet")),
                Term::set(
                    set_definition.clone(),
                    vec![
                        internal_term(&definition, r#"\dv{SortElement{}}("first")"#,),
                        internal_term(&definition, r#"\dv{SortElement{}}("second")"#,),
                    ],
                    Some(Term::variable(fresh.clone())),
                ),
            ),
            (
                Variable::new("SUBJECTREST", Sort::simple("SortSet")),
                Term::set(
                    set_definition,
                    vec![internal_term(&definition, "ELEMENT:SortElement{}")],
                    Some(Term::variable(fresh)),
                ),
            ),
        ])
    );
}

#[test]
fn reports_indeterminate_for_an_opaque_function_frame() {
    let definition = collection_definition();
    let pattern = internal_term(
        &definition,
        "mapConcat{}(mapItem{}(KEY:SortKey{}, VALUE:SortValue{}), REST:SortMap{})",
    );
    let subject = internal_term(
        &definition,
        r#"mapConcat{}(mapItem{}(\dv{SortKey{}}("first"), \dv{SortValue{}}("first-value")), opaqueMap{}(Y:SortElement{}))"#,
    );

    assert!(
        solve_collection_pairs_in_definition(
            MatchMode::Rewrite,
            &definition,
            Substitution::new(),
            &[(pattern.clone(), subject.clone())],
            None,
        )
        .is_none()
    );
    assert!(solve_with_test_frames(&definition, &[(pattern, subject)]).is_none());
}

#[test]
fn narrows_a_symbolic_subject_key_against_a_concrete_pattern_key_with_a_frame() {
    let definition = collection_definition();
    let pattern = internal_term(
        &definition,
        r#"mapConcat{}(mapItem{}(\dv{SortKey{}}("wanted"), VALUE:SortValue{}), REST:SortMap{})"#,
    );
    let subject = internal_term(
        &definition,
        r#"mapConcat{}(mapItem{}(SUBJECTKEY:SortKey{}, \dv{SortValue{}}("selected")), SUBJECTREST:SortMap{})"#,
    );

    assert!(
        solve_collection_pairs_in_definition(
            MatchMode::Rewrite,
            &definition,
            Substitution::new(),
            &[(pattern.clone(), subject.clone())],
            None,
        )
        .is_none()
    );
    let solutions = solve_with_test_frames(&definition, &[(pattern, subject)])
        .expect("a variable subject key and frame are both narrowable");
    assert_eq!(solutions.len(), 2);
    let explicit_solution = solutions
        .iter()
        .find(|solution| {
            solution
                .substitution
                .contains_key(&Variable::new("SUBJECTKEY", Sort::simple("SortKey")))
        })
        .expect("one branch should select the explicit symbolic subject key");
    assert_eq!(
        explicit_solution
            .substitution
            .get(&Variable::new("SUBJECTKEY", Sort::simple("SortKey"))),
        Some(&internal_term(&definition, r#"\dv{SortKey{}}("wanted")"#,))
    );
    assert!(solutions.iter().any(|solution| !solution.fresh.is_empty()));
}

#[test]
fn keeps_evaluate_mode_one_directional() {
    let definition = collection_definition();
    let pattern = internal_term(
        &definition,
        "mapConcat{}(mapItem{}(KEY:SortKey{}, VALUE:SortValue{}), REST:SortMap{})",
    );
    let subject = internal_term(
        &definition,
        r#"mapConcat{}(mapItem{}(\dv{SortKey{}}("first"), \dv{SortValue{}}("first-value")), SUBJECTREST:SortMap{})"#,
    );

    assert!(
        match_collection_remainders_all_in_definition(
            MatchMode::Evaluate,
            &definition,
            Substitution::new(),
            &[(pattern, subject)],
        )
        .is_none()
    );
}

#[test]
fn solves_a_closed_map_pattern_into_a_variable_frame() {
    let definition = collection_definition();
    let first_key = r#"\dv{SortKey{}}("first")"#;
    let first_value = r#"\dv{SortValue{}}("first-value")"#;
    let second_key = r#"\dv{SortKey{}}("second")"#;
    let second_value = r#"\dv{SortValue{}}("second-value")"#;
    let closed_entry = internal_term(
        &definition,
        &format!("mapItem{{}}({first_key}, {first_value})"),
    );
    let matching_open = internal_term(
        &definition,
        &format!("mapConcat{{}}(mapItem{{}}({first_key}, {first_value}), FRAME:SortMap{{}})"),
    );
    assert_eq!(
        solve_with_test_frames(&definition, &[(closed_entry.clone(), matching_open)]),
        Some(vec![CollectionSolution {
            substitution: Substitution::from([(
                Variable::new("FRAME", Sort::simple("SortMap")),
                internal_term(&definition, "mapUnit{}()"),
            )]),
            constraints: Vec::new(),
            fresh: BTreeSet::new(),
        }])
    );

    let symbolic_entry = internal_term(&definition, "mapItem{}(KEY:SortKey{}, VALUE:SortValue{})");
    let bare_frame = internal_term(&definition, "FRAME:SortMap{}");
    assert_eq!(
        solve_with_test_frames(&definition, &[(symbolic_entry.clone(), bare_frame)]),
        Some(vec![CollectionSolution {
            substitution: Substitution::from([(
                Variable::new("FRAME", Sort::simple("SortMap")),
                symbolic_entry,
            )]),
            constraints: Vec::new(),
            fresh: BTreeSet::new(),
        }])
    );

    let extra_open = internal_term(
        &definition,
        &format!(
            "mapConcat{{}}(mapConcat{{}}(mapItem{{}}({first_key}, {first_value}), mapItem{{}}({second_key}, {second_value})), FRAME:SortMap{{}})"
        ),
    );
    assert_eq!(
        solve_with_test_frames(&definition, &[(closed_entry, extra_open)]),
        Some(Vec::new())
    );
}

#[test]
fn solves_a_closed_list_pattern_into_a_variable_frame() {
    let definition = collection_definition();
    let first = r#"\dv{SortElement{}}("first")"#;
    let second = r#"\dv{SortElement{}}("second")"#;
    let third = r#"\dv{SortElement{}}("third")"#;
    let closed_one = internal_term(&definition, &format!("listItem{{}}({first})"));
    let open_one = internal_term(
        &definition,
        &format!("listConcat{{}}(listItem{{}}({first}), FRAME:SortList{{}})"),
    );
    assert_eq!(
        solve_with_test_frames(&definition, &[(closed_one.clone(), open_one)]),
        Some(vec![CollectionSolution {
            substitution: Substitution::from([(
                Variable::new("FRAME", Sort::simple("SortList")),
                internal_term(&definition, "listUnit{}()"),
            )]),
            constraints: Vec::new(),
            fresh: BTreeSet::new(),
        }])
    );

    let closed_three = internal_term(
        &definition,
        &format!(
            "listConcat{{}}(listItem{{}}({first}), listConcat{{}}(listItem{{}}({second}), listItem{{}}({third})))"
        ),
    );
    let open_ends = internal_term(
        &definition,
        &format!(
            "listConcat{{}}(listItem{{}}({first}), listConcat{{}}(FRAME:SortList{{}}, listItem{{}}({third})))"
        ),
    );
    assert_eq!(
        solve_with_test_frames(&definition, &[(closed_three, open_ends)]),
        Some(vec![CollectionSolution {
            substitution: Substitution::from([(
                Variable::new("FRAME", Sort::simple("SortList")),
                internal_term(&definition, &format!("listItem{{}}({second})")),
            )]),
            constraints: Vec::new(),
            fresh: BTreeSet::new(),
        }])
    );

    let longer_open = internal_term(
        &definition,
        &format!(
            "listConcat{{}}(listItem{{}}({first}), listConcat{{}}(listItem{{}}({second}), FRAME:SortList{{}}))"
        ),
    );
    assert_eq!(
        solve_with_test_frames(&definition, &[(closed_one.clone(), longer_open)]),
        Some(Vec::new())
    );

    let opaque = internal_term(
        &definition,
        &format!("listConcat{{}}(listItem{{}}({first}), opaqueList{{}}(Y:SortElement{{}}))"),
    );
    assert!(solve_with_test_frames(&definition, &[(closed_one, opaque)]).is_none());
}

#[test]
fn solves_one_sided_residuals_between_variable_list_frames() {
    let definition = collection_definition();
    let first = r#"\dv{SortElement{}}("first")"#;
    let second = r#"\dv{SortElement{}}("second")"#;
    let third = r#"\dv{SortElement{}}("third")"#;
    let fourth = r#"\dv{SortElement{}}("fourth")"#;
    let longer_pattern = internal_term(
        &definition,
        &format!(
            "listConcat{{}}(listItem{{}}({first}), listConcat{{}}(listItem{{}}({second}), PATTERN:SortList{{}}))"
        ),
    );
    let shorter_subject = internal_term(
        &definition,
        &format!("listConcat{{}}(listItem{{}}({first}), SUBJECT:SortList{{}})"),
    );

    assert_eq!(
        solve_with_test_frames(&definition, &[(longer_pattern, shorter_subject)]),
        Some(vec![CollectionSolution {
            substitution: Substitution::from([(
                Variable::new("SUBJECT", Sort::simple("SortList")),
                internal_term(
                    &definition,
                    &format!("listConcat{{}}(listItem{{}}({second}), PATTERN:SortList{{}})"),
                ),
            )]),
            constraints: Vec::new(),
            fresh: BTreeSet::new(),
        }])
    );

    let opposing_pattern = internal_term(
        &definition,
        &format!(
            "listConcat{{}}(listItem{{}}({first}), listConcat{{}}(listItem{{}}({second}), listConcat{{}}(PATTERN:SortList{{}}, listItem{{}}({fourth}))))"
        ),
    );
    let opposing_subject = internal_term(
        &definition,
        &format!(
            "listConcat{{}}(listItem{{}}({first}), listConcat{{}}(SUBJECT:SortList{{}}, listConcat{{}}(listItem{{}}({third}), listItem{{}}({fourth}))))"
        ),
    );
    assert!(solve_with_test_frames(&definition, &[(opposing_pattern, opposing_subject)]).is_none());
}

#[test]
fn expands_closed_destination_maps_against_open_current_maps() {
    let definition = map_definition();
    let key = var("KEY", Sort::simple("MapKey"));
    let value = var("VALUE", Sort::simple("MapValue"));
    let rest = var("REST", Sort::simple("MapSort"));
    let first_key = domain_value(Sort::simple("MapKey"), "first");
    let first_value = domain_value(Sort::simple("MapValue"), "first-value");
    let second_key = domain_value(Sort::simple("MapKey"), "second");
    let second_value = domain_value(Sort::simple("MapValue"), "second-value");
    let destination = Term::map(
        definition.clone(),
        vec![
            (first_key.clone(), first_value.clone()),
            (second_key.clone(), second_value.clone()),
        ],
        None,
    );
    let current = Term::map(
        definition.clone(),
        vec![(key.clone(), value.clone())],
        Some(rest.clone()),
    );
    let first_remainder = Term::map(
        definition.clone(),
        vec![(second_key.clone(), second_value.clone())],
        None,
    );
    let second_remainder = Term::map(
        definition,
        vec![(first_key.clone(), first_value.clone())],
        None,
    );
    let mut expected = vec![
        vec![
            (key.clone(), first_key),
            (value.clone(), first_value),
            (rest.clone(), first_remainder),
        ],
        vec![
            (key, second_key),
            (value, second_value),
            (rest, second_remainder),
        ],
    ];
    expected.sort();

    assert_eq!(
        expand_closed_map_implication_remainders(&Substitution::new(), &[(destination, current)],),
        Some(expected),
    );
}

#[test]
fn carries_an_open_set_subject_frame_through_every_selection() {
    let definition = collection_definition();
    let first = r#"\dv{SortElement{}}("first")"#;
    let second = r#"\dv{SortElement{}}("second")"#;
    let pattern = internal_term(
        &definition,
        "setConcat{}(setItem{}(ELEMENT:SortElement{}), REST:SortSet{})",
    );
    let subject = internal_term(
        &definition,
        &format!(
            "setConcat{{}}(setConcat{{}}(setItem{{}}({first}), setItem{{}}({second})), SUBJECTREST:SortSet{{}})"
        ),
    );

    let solutions = solve_with_test_frames(&definition, &[(pattern, subject)])
        .expect("the open Set selection should be decidable");
    assert_eq!(solutions.len(), 3);
    let subject_rest = Variable::new("SUBJECTREST", Sort::simple("SortSet"));
    let element = Variable::new("ELEMENT", Sort::simple("SortElement"));
    let rest = Variable::new("REST", Sort::simple("SortSet"));
    let explicit = solutions
        .iter()
        .filter(|solution| solution.fresh.is_empty())
        .collect::<Vec<_>>();
    assert_eq!(explicit.len(), 2);
    assert_eq!(
        explicit
            .iter()
            .map(|solution| solution.substitution[&element].clone())
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([
            internal_term(&definition, first),
            internal_term(&definition, second),
        ])
    );
    assert!(explicit.iter().all(|solution| {
        solution.substitution[&rest]
            .attributes()
            .variables
            .contains(&subject_rest)
    }));
    assert!(solutions.iter().any(|solution| !solution.fresh.is_empty()));
}

fn set_definition() -> Arc<crate::term::SetDefinition> {
    Arc::new(crate::term::SetDefinition {
        symbols: collection_symbols("set"),
        element_sort: "SetElement".into(),
        list_sort: "SetSort".into(),
    })
}

fn sort_graph() -> SortGraph {
    let mut graph = SortGraph::default();
    graph.insert("SomeSort", [Name::from("ASubsort")]);
    graph.insert("ASubsort", []);
    for name in ["MapKey", "MapValue", "MapSort", "ListSort", "SetSort"] {
        graph.insert(name, []);
    }
    graph
}

#[test]
fn enumerates_every_symbolic_map_key_selection() {
    let definition = map_definition();
    let key_variable = variable("KEY", Sort::simple("MapKey"));
    let value_variable = variable("VALUE", Sort::simple("MapValue"));
    let rest_variable = variable("REST", Sort::simple("MapSort"));
    let first_key = domain_value(Sort::simple("MapKey"), "first");
    let first_value = domain_value(Sort::simple("MapValue"), "first-value");
    let second_key = domain_value(Sort::simple("MapKey"), "second");
    let second_value = domain_value(Sort::simple("MapValue"), "second-value");
    let pattern = Term::map(
        definition.clone(),
        vec![(
            Term::variable(key_variable.clone()),
            Term::variable(value_variable.clone()),
        )],
        Some(Term::variable(rest_variable.clone())),
    );
    let subject = Term::map(
        definition.clone(),
        vec![
            (first_key.clone(), first_value.clone()),
            (second_key.clone(), second_value.clone()),
        ],
        None,
    );

    assert_eq!(
        match_map_terms_all(
            MatchMode::Rewrite,
            &sort_graph(),
            &pattern,
            &subject,
            &Substitution::new(),
        ),
        Some(vec![
            Substitution::from([
                (key_variable.clone(), first_key.clone()),
                (
                    rest_variable.clone(),
                    Term::map(
                        definition.clone(),
                        vec![(second_key.clone(), second_value.clone())],
                        None,
                    ),
                ),
                (value_variable.clone(), first_value.clone()),
            ]),
            Substitution::from([
                (key_variable, second_key),
                (
                    rest_variable,
                    Term::map(definition, vec![(first_key, first_value)], None),
                ),
                (value_variable, second_value),
            ]),
        ])
    );
}

#[test]
fn enumerates_map_entry_permutations_without_splitting_values_from_keys() {
    let definition = map_definition();
    let first_key_variable = variable("KEY1", Sort::simple("MapKey"));
    let first_value_variable = variable("VALUE1", Sort::simple("MapValue"));
    let second_key_variable = variable("KEY2", Sort::simple("MapKey"));
    let second_value_variable = variable("VALUE2", Sort::simple("MapValue"));
    let first_key = domain_value(Sort::simple("MapKey"), "first");
    let first_value = domain_value(Sort::simple("MapValue"), "first-value");
    let second_key = domain_value(Sort::simple("MapKey"), "second");
    let second_value = domain_value(Sort::simple("MapValue"), "second-value");
    let pattern = Term::map(
        definition.clone(),
        vec![
            (
                Term::variable(first_key_variable.clone()),
                Term::variable(first_value_variable.clone()),
            ),
            (
                Term::variable(second_key_variable.clone()),
                Term::variable(second_value_variable.clone()),
            ),
        ],
        None,
    );
    let subject = Term::map(
        definition,
        vec![
            (first_key.clone(), first_value.clone()),
            (second_key.clone(), second_value.clone()),
        ],
        None,
    );

    assert_eq!(
        match_map_terms_all(
            MatchMode::Rewrite,
            &sort_graph(),
            &pattern,
            &subject,
            &Substitution::new(),
        ),
        Some(vec![
            Substitution::from([
                (first_key_variable.clone(), first_key.clone()),
                (first_value_variable.clone(), first_value.clone()),
                (second_key_variable.clone(), second_key.clone()),
                (second_value_variable.clone(), second_value.clone()),
            ]),
            Substitution::from([
                (first_key_variable, second_key),
                (first_value_variable, second_value),
                (second_key_variable, first_key),
                (second_value_variable, first_value),
            ]),
        ])
    );
}

#[test]
fn enumerates_every_symbolic_set_selection() {
    let definition = set_definition();
    let element_variable = variable("ELEMENT", Sort::simple("SetElement"));
    let rest_variable = variable("REST", Sort::simple("SetSort"));
    let first = domain_value(Sort::simple("SetElement"), "first");
    let second = domain_value(Sort::simple("SetElement"), "second");
    let pattern = Term::set(
        definition.clone(),
        vec![Term::variable(element_variable.clone())],
        Some(Term::variable(rest_variable.clone())),
    );
    let subject = Term::set(
        definition.clone(),
        vec![first.clone(), second.clone()],
        None,
    );

    assert_eq!(
        match_set_terms_all(
            MatchMode::Rewrite,
            &sort_graph(),
            &pattern,
            &subject,
            &Substitution::new(),
        ),
        Some(vec![
            Substitution::from([
                (element_variable.clone(), first.clone()),
                (
                    rest_variable.clone(),
                    Term::set(definition.clone(), vec![second.clone()], None),
                ),
            ]),
            Substitution::from([
                (element_variable, second),
                (rest_variable, Term::set(definition, vec![first], None)),
            ]),
        ])
    );
}

#[test]
fn enumerates_set_element_permutations_without_reuse() {
    let definition = set_definition();
    let first_variable = variable("FIRST", Sort::simple("SetElement"));
    let second_variable = variable("SECOND", Sort::simple("SetElement"));
    let first = domain_value(Sort::simple("SetElement"), "first");
    let second = domain_value(Sort::simple("SetElement"), "second");
    let pattern = Term::set(
        definition.clone(),
        vec![
            Term::variable(first_variable.clone()),
            Term::variable(second_variable.clone()),
        ],
        None,
    );
    let subject = Term::set(definition, vec![first.clone(), second.clone()], None);

    assert_eq!(
        match_set_terms_all(
            MatchMode::Rewrite,
            &sort_graph(),
            &pattern,
            &subject,
            &Substitution::new(),
        ),
        Some(vec![
            Substitution::from([
                (first_variable.clone(), first.clone()),
                (second_variable.clone(), second.clone()),
            ]),
            Substitution::from([(first_variable, second), (second_variable, first),]),
        ])
    );
}
