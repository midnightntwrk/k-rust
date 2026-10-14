//! Crate-internal contracts of `crate::matching` (`pub(crate)` entry points).

use std::{collections::BTreeSet, sync::Arc};

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use super::matching_oracle::{match_map_terms_all, match_set_terms_all};
use crate::{
    condition::MatchSolution,
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
    Term::raw_domain_value(sort, value)
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
        key_sort: Sort::simple("MapKey"),
        value_sort: Sort::simple("MapValue"),
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
                hooked-sort SortSetMap{}
                    [hook{}("MAP.Map"), unit{}(setMapUnit{}()), element{}(setMapItem{}()), concat{}(setMapConcat{}())]
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
                hooked-symbol setMapUnit{}() : SortSetMap{} [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol setMapItem{}(SortKey{}, SortSet{}) : SortSetMap{} [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol setMapConcat{}(SortSetMap{}, SortSetMap{}) : SortSetMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol nested{}(SortSet{}) : SortValue{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
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
fn a_collection_solution_states_an_element_equation_under_a_later_element_binding() {
    let syntax = parse_definition(
        r#"[]
        module MAIN
            sort SortElement{} [hasDomainValues{}()]
            sort SortWrapped{} []
            hooked-sort SortSet{}
                [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
            hooked-symbol setUnit{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
            hooked-symbol setItem{}(SortWrapped{}) : SortSet{} [function{}(), total{}(), hook{}("SET.element")]
            hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{} [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
            symbol p{}(SortElement{}) : SortWrapped{} [constructor{}(), injective{}()]
            symbol q{}(SortElement{}) : SortWrapped{} [constructor{}(), injective{}()]
            symbol g{}(SortElement{}) : SortElement{} [function{}()]
        endmodule []"#,
    )
    .expect("collection definition should parse");
    let definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("collection definition should internalize");
    let pattern = internal_term(
        &definition,
        "setConcat{}(setItem{}(p{}(g{}(X:SortElement{}))), setItem{}(q{}(X:SortElement{})))",
    );
    let subject = internal_term(
        &definition,
        r#"setConcat{}(setItem{}(p{}(\dv{SortElement{}}("e1"))), setItem{}(q{}(\dv{SortElement{}}("e2"))))"#,
    );
    let TermKind::Set { elements, .. } = pattern.kind() else {
        panic!("the pattern should internalize as a set");
    };
    assert_eq!(
        elements.first().expect("one element"),
        &internal_term(&definition, "p{}(g{}(X:SortElement{}))"),
        "the kept element equation must precede the binding of X",
    );

    let solutions = solve_with_test_frames(&definition, &[(pattern, subject)])
        .expect("both constructor elements should solve with narrowing");
    let [solution] = solutions.as_slice() else {
        panic!("distinct constructor heads should give exactly one solution");
    };
    assert_eq!(
        solution.matched.conditions(),
        vec![crate::rule::Predicate::Equals(
            internal_term(&definition, r#"g{}(\dv{SortElement{}}("e2"))"#),
            internal_term(&definition, r#"\dv{SortElement{}}("e1")"#),
        )],
    );
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
            matched: MatchSolution::new(Substitution::from([
                (
                    Variable::new("ELEMENT", Sort::simple("SortElement")),
                    internal_term(&definition, first),
                ),
                (
                    Variable::new("REST", Sort::simple("SortList")),
                    expected_rest,
                ),
            ])),
            fresh: BTreeSet::new(),
            bindings: Bindings::Forced,
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
            matched: MatchSolution::new(Substitution::from([
                (element.clone(), internal_term(&definition, first)),
                (
                    rest.clone(),
                    internal_term(&definition, &format!("setItem{{}}({second})")),
                ),
            ])),
            fresh: BTreeSet::new(),
            bindings: Bindings::Forced,
        },
        CollectionSolution {
            matched: MatchSolution::new(Substitution::from([
                (element, internal_term(&definition, second)),
                (
                    rest,
                    internal_term(&definition, &format!("setItem{{}}({first})")),
                ),
            ])),
            fresh: BTreeSet::new(),
            bindings: Bindings::Forced,
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
            matched: MatchSolution::new(Substitution::from([
                (key.clone(), internal_term(&definition, first_key)),
                (value.clone(), internal_term(&definition, first_value)),
                (
                    rest.clone(),
                    internal_term(
                        &definition,
                        &format!("mapItem{{}}({second_key}, {second_value})"),
                    ),
                ),
            ])),
            fresh: BTreeSet::new(),
            bindings: Bindings::Forced,
        },
        CollectionSolution {
            matched: MatchSolution::new(Substitution::from([
                (key, internal_term(&definition, second_key)),
                (value, internal_term(&definition, second_value)),
                (
                    rest,
                    internal_term(
                        &definition,
                        &format!("mapItem{{}}({first_key}, {first_value})"),
                    ),
                ),
            ])),
            fresh: BTreeSet::new(),
            bindings: Bindings::Forced,
        },
    ];
    expected.sort();

    assert_eq!(
        solve_with_test_frames(&definition, &[(closed, open)]),
        Some(expected)
    );
}

#[test]
fn nested_collection_remainder_is_solved_by_the_collection_solver() {
    let definition = collection_definition();
    let first = r#"\dv{SortElement{}}("first")"#;
    let second = r#"\dv{SortElement{}}("second")"#;
    let key = r#"\dv{SortKey{}}("key")"#;
    let pattern = internal_term(
        &definition,
        "mapItem{}(KEY:SortKey{}, nested{}(setConcat{}(setItem{}(ELEMENT:SortElement{}), REST:SortSet{})))",
    );
    let two = internal_term(
        &definition,
        &format!(
            "mapItem{{}}({key}, nested{{}}(setConcat{{}}(setItem{{}}({first}), setItem{{}}({second}))))"
        ),
    );
    let one = internal_term(
        &definition,
        &format!("mapItem{{}}({key}, nested{{}}(setItem{{}}({first})))"),
    );

    let two_solutions = solve_with_test_frames(&definition, &[(pattern.clone(), two)])
        .expect("the nested Set pair should be handled by the collection solver");
    assert_eq!(two_solutions.len(), 2, "{two_solutions:#?}");
    let one_solutions = solve_with_test_frames(&definition, &[(pattern, one)])
        .expect("the one-element nested Set pair should be decidable");
    assert_eq!(one_solutions.len(), 1, "{one_solutions:#?}");
}

/// A pattern binding with a variable key, `KEY |-> VALUE REST`, against a closed `n`-entry map
/// has one candidate per subject entry, and each candidate's frame, the binding of `REST`, is the
/// subject's tree without that entry: a removal, which summarizes only the entries of the nodes
/// it rebuilds on one path (at most `2B` of them, in a leaf and the sibling it may be merged
/// with), not the `n - 1` entries of a frame built anew.
#[test]
fn each_candidate_frame_of_a_symbolic_key_is_one_removal_from_the_subject() {
    const ENTRIES: usize = 1024;
    let definition = collection_definition();
    let one = internal_term(
        &definition,
        r#"mapItem{}(\dv{SortKey{}}("0"), \dv{SortValue{}}("0"))"#,
    );
    let TermKind::Map {
        definition: map, ..
    } = one.kind()
    else {
        panic!("a map item should internalize as a map");
    };
    let key =
        |index: usize| internal_term(&definition, &format!(r#"\dv{{SortKey{{}}}}("{index:05}")"#));
    let value =
        |index: usize| internal_term(&definition, &format!(r#"\dv{{SortValue{{}}}}("{index}")"#));
    let subject = Term::map(
        map.clone(),
        (0..ENTRIES)
            .map(|index| (key(index), value(index)))
            .collect(),
        None,
    );
    let pattern = internal_term(
        &definition,
        "mapConcat{}(mapItem{}(KEY:SortKey{}, VALUE:SortValue{}), REST:SortMap{})",
    );
    let mut solutions = None;
    let summarized = crate::term::items::entry_summaries_during(|| {
        solutions = solve_with_test_frames(&definition, &[(pattern, subject.clone())]);
    });
    let solutions = solutions.expect("a closed subject map is decided");
    assert_eq!(solutions.len(), ENTRIES);
    let bound = ENTRIES * 2 * crate::term::chunked::DEFAULT_BRANCHING;
    assert!(
        summarized <= bound,
        "{summarized} entry summaries for {ENTRIES} candidates, bound {bound}"
    );
    let TermKind::Map {
        entries: subject_entries,
        ..
    } = subject.kind()
    else {
        unreachable!()
    };
    let rest = Variable::new("REST", Sort::simple("SortMap"));
    let key_variable = Variable::new("KEY", Sort::simple("SortKey"));
    for solution in &solutions {
        let substitution = solution.matched.substitution();
        let bound_key = substitution.get(&key_variable).expect("KEY is bound");
        let index = subject_entries
            .search(bound_key)
            .expect("KEY is bound to a subject key");
        let expected = Term::map_of_items(map.clone(), subject_entries.remove_at(index).0, None);
        assert_eq!(
            substitution.get(&rest),
            Some(&expected),
            "KEY = {bound_key:?}"
        );
    }
}

#[test]
fn deferred_collection_pairs_are_solved_to_a_fixed_point() {
    let definition = collection_definition();
    let first = r#"\dv{SortElement{}}("first")"#;
    let second = r#"\dv{SortElement{}}("second")"#;
    let key = r#"\dv{SortKey{}}("key")"#;
    let concrete = internal_term(
        &definition,
        &format!("setConcat{{}}(setItem{{}}({first}), setItem{{}}({second}))"),
    );
    let rest = internal_term(&definition, "REST:SortSet{}");
    let binder_pattern = internal_term(
        &definition,
        &format!("setMapItem{{}}({key}, REST:SortSet{{}})"),
    );
    let binder_subject = internal_term(
        &definition,
        &format!(
            "setMapItem{{}}({key}, setConcat{{}}(setItem{{}}({first}), setItem{{}}({second})))"
        ),
    );
    let deferred = (rest, concrete);
    let binder = (binder_pattern, binder_subject);

    let forward = solve_with_test_frames(&definition, &[deferred.clone(), binder.clone()])
        .expect("the later Map pair should bind the earlier collection variable");
    let reverse = solve_with_test_frames(&definition, &[binder, deferred])
        .expect("mirroring the deferred pair order should stay decidable");
    assert_eq!(forward, reverse);
    assert_eq!(forward.len(), 1, "{forward:#?}");
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
            matched: MatchSolution::new(Substitution::from([
                (
                    Variable::new("T", Sort::simple("SortSet")),
                    internal_term(&definition, "setUnit{}()"),
                ),
                (
                    Variable::new("X", Sort::simple("SortElement")),
                    internal_term(&definition, "Y:SortElement{}"),
                ),
            ])),
            fresh: BTreeSet::new(),
            bindings: Bindings::Forced,
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
            matched: MatchSolution::new(Substitution::from([
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
            ])),
            fresh: BTreeSet::new(),
            bindings: Bindings::Forced,
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
            .map(|solution| solution.matched.substitution()[&key].clone())
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([
            internal_term(&definition, first_key),
            internal_term(&definition, second_key),
        ])
    );
    assert!(explicit.iter().all(|solution| {
        solution.matched.substitution()[&rest]
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
    assert!(frame_solution.matched.conditions().is_empty());
    assert_eq!(
        frame_solution.matched.substitution().clone(),
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
    assert!(frame_solution.matched.conditions().is_empty());
    assert_eq!(
        frame_solution.matched.substitution().clone(),
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
                .matched
                .substitution()
                .contains_key(&Variable::new("SUBJECTKEY", Sort::simple("SortKey")))
        })
        .expect("one branch should select the explicit symbolic subject key");
    assert_eq!(
        explicit_solution
            .matched
            .substitution()
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

    assert!(matches!(
        match_collection_remainders_all_in_definition(
            MatchMode::Evaluate,
            &definition,
            Substitution::new(),
            &[(pattern, subject)],
        ),
        CollectionMatches::Undecided
    ));
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
            matched: MatchSolution::new(Substitution::from([(
                Variable::new("FRAME", Sort::simple("SortMap")),
                internal_term(&definition, "mapUnit{}()"),
            )])),
            fresh: BTreeSet::new(),
            bindings: Bindings::Forced,
        }])
    );

    let symbolic_entry = internal_term(&definition, "mapItem{}(KEY:SortKey{}, VALUE:SortValue{})");
    let bare_frame = internal_term(&definition, "FRAME:SortMap{}");
    assert_eq!(
        solve_with_test_frames(&definition, &[(symbolic_entry.clone(), bare_frame)]),
        Some(vec![CollectionSolution {
            matched: MatchSolution::new(Substitution::from([(
                Variable::new("FRAME", Sort::simple("SortMap")),
                symbolic_entry,
            )])),
            fresh: BTreeSet::new(),
            bindings: Bindings::Forced,
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
            matched: MatchSolution::new(Substitution::from([(
                Variable::new("FRAME", Sort::simple("SortList")),
                internal_term(&definition, "listUnit{}()"),
            )])),
            fresh: BTreeSet::new(),
            bindings: Bindings::Forced,
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
            matched: MatchSolution::new(Substitution::from([(
                Variable::new("FRAME", Sort::simple("SortList")),
                internal_term(&definition, &format!("listItem{{}}({second})")),
            )])),
            fresh: BTreeSet::new(),
            bindings: Bindings::Forced,
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
            matched: MatchSolution::new(Substitution::from([(
                Variable::new("SUBJECT", Sort::simple("SortList")),
                internal_term(
                    &definition,
                    &format!("listConcat{{}}(listItem{{}}({second}), PATTERN:SortList{{}})"),
                ),
            )])),
            fresh: BTreeSet::new(),
            bindings: Bindings::Forced,
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
        expand_implication_remainders(
            &collection_definition(),
            &Substitution::new(),
            &[(destination, current)],
        ),
        Some(expected),
    );
}

/// The list of `collection_definition` concatenating `parts` in order (each a KORE list term, a
/// `listItem` or a list variable), `.List` for none.
fn concat_list(definition: &BackendDefinition, parts: &[&str]) -> Term {
    let source = parts
        .iter()
        .rev()
        .fold(None, |right: Option<String>, part| {
            Some(match right {
                None => (*part).to_owned(),
                Some(right) => format!("listConcat{{}}({part}, {right})"),
            })
        })
        .unwrap_or_else(|| "listUnit{}()".to_owned());
    internal_term(definition, &source)
}

fn list_element(name: &str) -> String {
    format!(r#"listItem{{}}(\dv{{SortElement{{}}}}("{name}"))"#)
}

fn element_value(name: &str) -> Term {
    domain_value(Sort::simple("SortElement"), name)
}

/// The expansion of the one remainder pair `(pattern, subject)`.
fn expand_list_pair(
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
) -> Option<Vec<Vec<(Term, Term)>>> {
    expand_implication_remainders(
        definition,
        &Substitution::new(),
        &[(pattern.clone(), subject.clone())],
    )
}

#[test]
fn an_item_between_two_list_parts_has_a_branch_for_each_position_of_a_closed_list() {
    let definition = collection_definition();
    let (a, b, c) = (list_element("a"), list_element("b"), list_element("c"));
    let pattern = concat_list(
        &definition,
        &[
            "A:SortList{}",
            "listItem{}(X:SortElement{})",
            "C:SortList{}",
        ],
    );
    let subject = concat_list(&definition, &[&a, &b, &c]);
    let list = |parts: &[&str]| concat_list(&definition, parts);
    let (first, x, last) = (
        var("A", Sort::simple("SortList")),
        var("X", Sort::simple("SortElement")),
        var("C", Sort::simple("SortList")),
    );
    let mut expected = vec![
        vec![
            (first.clone(), list(&[])),
            (x.clone(), element_value("a")),
            (last.clone(), list(&[&b, &c])),
        ],
        vec![
            (first.clone(), list(&[&a])),
            (x.clone(), element_value("b")),
            (last.clone(), list(&[&c])),
        ],
        vec![
            (first, list(&[&a, &b])),
            (x, element_value("c")),
            (last, list(&[])),
        ],
    ];
    expected.sort();
    assert_eq!(
        expand_list_pair(&definition, &pattern, &subject),
        Some(expected)
    );
}

#[test]
fn an_item_between_two_list_parts_keeps_only_the_positions_it_can_match() {
    let definition = collection_definition();
    let (a, b, c) = (list_element("a"), list_element("b"), list_element("c"));
    let pattern = concat_list(&definition, &["A:SortList{}", &b, "C:SortList{}"]);
    let subject = concat_list(&definition, &[&a, &b, &c]);
    assert_eq!(
        expand_list_pair(&definition, &pattern, &subject),
        Some(vec![vec![
            (
                var("A", Sort::simple("SortList")),
                concat_list(&definition, &[&a])
            ),
            (element_value("b"), element_value("b")),
            (
                var("C", Sort::simple("SortList")),
                concat_list(&definition, &[&c])
            ),
        ]])
    );
}

#[test]
fn an_item_between_two_list_parts_of_an_empty_list_has_no_branch() {
    let definition = collection_definition();
    let (a, b) = (list_element("a"), list_element("b"));
    let pattern = concat_list(&definition, &["A:SortList{}", &b, "C:SortList{}"]);
    assert_eq!(
        expand_list_pair(&definition, &pattern, &concat_list(&definition, &[])),
        Some(Vec::new())
    );
    let found = expand_list_pair(&definition, &pattern, &concat_list(&definition, &[&b]));
    assert_eq!(found.map(|branches| branches.len()), Some(1));
    assert_eq!(
        expand_list_pair(&definition, &pattern, &concat_list(&definition, &[&a])),
        Some(Vec::new())
    );
}

#[test]
fn two_items_between_list_parts_keep_their_order() {
    let definition = collection_definition();
    let (a, b, c) = (list_element("a"), list_element("b"), list_element("c"));
    let subject = concat_list(&definition, &[&a, &b, &c]);
    let pattern = concat_list(
        &definition,
        &["A:SortList{}", &a, "B:SortList{}", &c, "C:SortList{}"],
    );
    assert_eq!(
        expand_list_pair(&definition, &pattern, &subject),
        Some(vec![vec![
            (
                var("A", Sort::simple("SortList")),
                concat_list(&definition, &[])
            ),
            (element_value("a"), element_value("a")),
            (
                var("B", Sort::simple("SortList")),
                concat_list(&definition, &[&b])
            ),
            (element_value("c"), element_value("c")),
            (
                var("C", Sort::simple("SortList")),
                concat_list(&definition, &[])
            ),
        ]])
    );
    let swapped = concat_list(
        &definition,
        &["A:SortList{}", &c, "B:SortList{}", &a, "C:SortList{}"],
    );
    assert_eq!(
        expand_list_pair(&definition, &swapped, &subject),
        Some(Vec::new())
    );
}

#[test]
fn neighbouring_items_take_neighbouring_positions() {
    let definition = collection_definition();
    let (a, b, c) = (list_element("a"), list_element("b"), list_element("c"));
    let closed = concat_list(&definition, &[&a, &b, &c]);
    let neighbours = |first: &str, second: &str| {
        concat_list(
            &definition,
            &["A:SortList{}", first, second, "C:SortList{}"],
        )
    };
    let found = expand_list_pair(&definition, &neighbours(&b, &c), &closed);
    assert_eq!(found.map(|branches| branches.len()), Some(1));
    assert_eq!(
        expand_list_pair(&definition, &neighbours(&a, &c), &closed),
        Some(Vec::new())
    );
    // `a` and `b` are neighbours of the subject only when `L` is empty, which no position
    // states: the equation itself is the one branch.
    let open = concat_list(&definition, &[&a, "L:SortList{}", &b]);
    let pattern = neighbours(&a, &b);
    assert_eq!(
        expand_list_pair(&definition, &pattern, &open),
        Some(vec![vec![(pattern, open)]])
    );
}

#[test]
fn an_open_subject_keeps_the_whole_equation_as_a_branch() {
    let definition = collection_definition();
    let (a, b, c) = (list_element("a"), list_element("b"), list_element("c"));
    let rest = "L:SortList{}";
    let pattern = concat_list(
        &definition,
        &[
            "A:SortList{}",
            "listItem{}(X:SortElement{})",
            "C:SortList{}",
        ],
    );
    let subject = concat_list(&definition, &[&a, &b, rest, &c]);
    let list = |parts: &[&str]| concat_list(&definition, parts);
    let (first, x, last) = (
        var("A", Sort::simple("SortList")),
        var("X", Sort::simple("SortElement")),
        var("C", Sort::simple("SortList")),
    );
    let mut expected = vec![
        vec![
            (first.clone(), list(&[])),
            (x.clone(), element_value("a")),
            (last.clone(), list(&[&b, rest, &c])),
        ],
        vec![
            (first.clone(), list(&[&a])),
            (x.clone(), element_value("b")),
            (last.clone(), list(&[rest, &c])),
        ],
        vec![
            (first, list(&[&a, &b, rest])),
            (x, element_value("c")),
            (last, list(&[])),
        ],
        vec![(pattern.clone(), subject.clone())],
    ];
    expected.sort();
    assert_eq!(
        expand_list_pair(&definition, &pattern, &subject),
        Some(expected)
    );
}

#[test]
fn an_item_whose_match_is_left_open_keeps_its_position() {
    let definition = collection_definition();
    let (a, b) = (list_element("a"), list_element("b"));
    let pattern = concat_list(&definition, &["A:SortList{}", &a, "C:SortList{}"]);
    // `I` may be `a`, so its position is a branch whose item equation the implication decides;
    // `b` is not `a`, so its position is none.
    let subject = concat_list(&definition, &["listItem{}(I:SortElement{})", &b]);
    assert_eq!(
        expand_list_pair(&definition, &pattern, &subject),
        Some(vec![vec![
            (
                var("A", Sort::simple("SortList")),
                concat_list(&definition, &[])
            ),
            (element_value("a"), var("I", Sort::simple("SortElement"))),
            (
                var("C", Sort::simple("SortList")),
                concat_list(&definition, &[&b])
            ),
        ]])
    );
}

#[test]
fn a_list_pattern_without_an_item_or_with_one_part_is_not_expanded() {
    let definition = collection_definition();
    let (a, b) = (list_element("a"), list_element("b"));
    let subject = concat_list(&definition, &[&a, &b]);
    let parts_only = concat_list(&definition, &["A:SortList{}", "C:SortList{}"]);
    assert_eq!(expand_list_pair(&definition, &parts_only, &subject), None);
    let one_part = concat_list(&definition, &["A:SortList{}", &b]);
    assert_eq!(expand_list_pair(&definition, &one_part, &subject), None);
}

#[test]
fn list_positions_multiply_with_closed_map_selections() {
    let definition = collection_definition();
    let map = map_definition();
    let destination = Term::map(
        map.clone(),
        vec![
            (
                domain_value(Sort::simple("MapKey"), "first"),
                domain_value(Sort::simple("MapValue"), "first-value"),
            ),
            (
                domain_value(Sort::simple("MapKey"), "second"),
                domain_value(Sort::simple("MapValue"), "second-value"),
            ),
        ],
        None,
    );
    let current = Term::map(
        map,
        vec![(
            var("KEY", Sort::simple("MapKey")),
            var("VALUE", Sort::simple("MapValue")),
        )],
        Some(var("REST", Sort::simple("MapSort"))),
    );
    let pattern = concat_list(
        &definition,
        &[
            "A:SortList{}",
            "listItem{}(X:SortElement{})",
            "C:SortList{}",
        ],
    );
    let subject = concat_list(&definition, &[&list_element("a"), &list_element("b")]);
    let branches = expand_implication_remainders(
        &definition,
        &Substitution::new(),
        &[(destination, current), (pattern, subject)],
    )
    .expect("both pairs expand");
    assert_eq!(branches.len(), 4, "{branches:?}");
    let map_key = var("KEY", Sort::simple("MapKey"));
    let item = var("X", Sort::simple("SortElement"));
    for branch in &branches {
        assert!(
            branch.iter().any(|(left, _)| left == &map_key)
                && branch.iter().any(|(left, _)| left == &item),
            "{branch:?}"
        );
    }
}

/// A branch's runs are cuts of the subject's tree: the seek reads the items without summarizing
/// any, and a cut inside the tree summarizes only the items of the leaves it rebuilds (the two
/// halves of the leaf it divides and a neighbour one half may be merged with: at most `3B`),
/// whatever the list's length.
#[test]
fn the_parts_of_a_list_branch_are_cuts_of_the_subject_tree() {
    const ITEMS: usize = 4096;
    const FOUND: usize = 1234;
    let definition = collection_definition();
    let small = concat_list(&definition, &[&list_element("0")]);
    let TermKind::List {
        definition: list, ..
    } = small.kind()
    else {
        panic!("a list: {small:?}");
    };
    let item = |index: usize| element_value(&index.to_string());
    let subject = Term::list(list.clone(), (0..ITEMS).map(item).collect(), None);
    let pattern = concat_list(
        &definition,
        &[
            "A:SortList{}",
            &list_element(&FOUND.to_string()),
            "C:SortList{}",
        ],
    );
    let (heads, _) = list_parts(&subject);
    let mut branches = None;
    let summarized = crate::term::items::element_summaries_during(|| {
        branches = Some(expand_list_pair(&definition, &pattern, &subject));
    });
    let leaf = crate::term::chunked::DEFAULT_BRANCHING;
    assert!(
        summarized <= 2 * 3 * leaf,
        "{summarized} item summaries for two cuts"
    );
    assert_eq!(
        branches.flatten(),
        Some(vec![vec![
            (
                var("A", Sort::simple("SortList")),
                Term::list_of_items(list.clone(), heads.split_at(FOUND).0, None),
            ),
            (item(FOUND), item(FOUND)),
            (
                var("C", Sort::simple("SortList")),
                Term::list_of_items(list.clone(), heads.split_at(FOUND + 1).1, None),
            ),
        ]])
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
            .map(|solution| solution.matched.substitution()[&element].clone())
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([
            internal_term(&definition, first),
            internal_term(&definition, second),
        ])
    );
    assert!(explicit.iter().all(|solution| {
        solution.matched.substitution()[&rest]
            .attributes()
            .variables
            .contains(&subject_rest)
    }));
    assert!(solutions.iter().any(|solution| !solution.fresh.is_empty()));
}

fn set_definition() -> Arc<crate::term::SetDefinition> {
    Arc::new(crate::term::SetDefinition {
        symbols: collection_symbols("set"),
        element_sort: Sort::simple("SetElement"),
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

/// An `as` pattern `P #as A` is the conjunction `\and(P, A)`. Under an injection `inj{Exp,KItem}`
/// it matches a value `inj{Int,KItem}(v)` of a subsort, which equals `inj{Exp,KItem}(inj{Int,Exp}
/// (v))` by injection composition, so each conjunct matches `inj{Int,Exp}(v)`; it matches exactly
/// when the bare variable `inj{Exp,KItem}(X)` does.
#[test]
fn a_conjunction_under_an_injection_matches_a_value_of_a_subsort() {
    let definition = BackendDefinition::internalize(
        &parse_definition(
            r#"[]
            module MAIN
                sort SortKItem{} []
                sort SortExp{} []
                sort SortInt{} [hasDomainValues{}()]
                symbol inj{From, To}(From) : To [sortInjection{}()]
                axiom{R} \exists{R}(Value:SortExp{},
                    \equals{SortExp{}, R}(Value:SortExp{}, inj{SortInt{}, SortExp{}}(From:SortInt{})))
                    [subsort{SortInt{}, SortExp{}}()]
                axiom{R} \exists{R}(Value:SortKItem{},
                    \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortInt{}, SortKItem{}}(From:SortInt{})))
                    [subsort{SortInt{}, SortKItem{}}()]
                axiom{R} \exists{R}(Value:SortKItem{},
                    \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortExp{}, SortKItem{}}(From:SortExp{})))
                    [subsort{SortExp{}, SortKItem{}}()]
            endmodule []"#,
        )
        .unwrap(),
        "MAIN",
    )
    .unwrap();
    let subject = internal_term(
        &definition,
        r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("3"))"#,
    );
    let value = internal_term(
        &definition,
        r#"inj{SortInt{}, SortExp{}}(\dv{SortInt{}}("3"))"#,
    );
    let exp = Sort::simple("SortExp");
    for mode in [MatchMode::Rewrite, MatchMode::Evaluate] {
        let pattern = internal_term(
            &definition,
            r#"inj{SortExp{}, SortKItem{}}(\and{SortExp{}}(X:SortExp{}, Y:SortExp{}))"#,
        );
        let result = match_terms_in_definition(mode, &definition, &pattern, &subject);
        let MatchResult::Success(substitution) = result else {
            panic!("{mode:?}: {result:?}");
        };
        assert_eq!(
            substitution,
            Substitution::from([
                (variable("X", exp.clone()), value.clone()),
                (variable("Y", exp.clone()), value.clone()),
            ]),
            "{mode:?}"
        );
    }
}

/// A constructor-like pattern key that a map with constructor-like keys does not bind refutes the
/// match from the keys alone: no map of the subject's other entries, which the refutation does
/// not name, is built (no entry summarized), so the failure costs the search and not the size of
/// the subject.
#[test]
fn a_ground_key_missing_from_a_ground_map_fails_without_copying_its_other_entries() {
    const ENTRIES: u32 = 4096;
    let definition = map_definition();
    let key = |index: u32| domain_value(Sort::simple("MapKey"), &format!("{index:05}"));
    let subject = Term::map(
        definition.clone(),
        (1..=ENTRIES)
            .map(|index| (key(2 * index), domain_value(Sort::simple("MapValue"), "v")))
            .collect(),
        None,
    );
    for rest in [None, Some(var("REST", Sort::simple("MapSort")))] {
        let pattern = Term::map(
            definition.clone(),
            vec![(key(ENTRIES + 1), var("VALUE", Sort::simple("MapValue")))],
            rest,
        );
        for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
            let summarized = crate::term::items::entry_summaries_during(|| {
                assert_eq!(
                    match_terms(mode, &sort_graph(), &pattern, &subject),
                    MatchResult::Failed(FailReason::KeyNotFound(key(ENTRIES + 1))),
                    "{mode:?}"
                );
            });
            assert_eq!(
                summarized, 0,
                "{mode:?}: a map of the subject's other entries was built"
            );
        }
    }
}

/// A constructor-like pattern key that the subject does not bind syntactically is refuted only
/// when every subject key is constructor-like: a symbolic subject key may denote it, so the match
/// is not refuted, whatever the number of other ground keys beside it.
#[test]
fn a_ground_key_missing_beside_a_symbolic_subject_key_is_not_refuted() {
    let definition = map_definition();
    let key = |name: &str| domain_value(Sort::simple("MapKey"), name);
    let value = |name: &str| domain_value(Sort::simple("MapValue"), name);
    let subject = Term::map(
        definition.clone(),
        vec![
            (key("a"), value("1")),
            (var("K", Sort::simple("MapKey")), value("2")),
            (key("c"), value("3")),
        ],
        None,
    );
    for rest in [None, Some(var("REST", Sort::simple("MapSort")))] {
        let pattern = Term::map(
            definition.clone(),
            vec![(key("b"), var("VALUE", Sort::simple("MapValue")))],
            rest,
        );
        for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
            let result = match_terms(mode, &sort_graph(), &pattern, &subject);
            assert!(
                !matches!(result, MatchResult::Failed(_)),
                "{mode:?}: {result:?}"
            );
        }
    }
}

/// A ground pattern key that a subject with a map frame does not bind syntactically may be bound
/// in the frame (`FRAME := b |-> x` makes the subject an instance of the pattern), so the match is
/// not refuted.
#[test]
fn a_ground_key_missing_beside_a_subject_frame_is_not_refuted() {
    let definition = map_definition();
    let key = |name: &str| domain_value(Sort::simple("MapKey"), name);
    let subject = Term::map(
        definition.clone(),
        vec![(key("a"), domain_value(Sort::simple("MapValue"), "1"))],
        Some(var("FRAME", Sort::simple("MapSort"))),
    );
    for rest in [None, Some(var("REST", Sort::simple("MapSort")))] {
        let pattern = Term::map(
            definition.clone(),
            vec![(key("b"), var("VALUE", Sort::simple("MapValue")))],
            rest,
        );
        for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
            let result = match_terms(mode, &sort_graph(), &pattern, &subject);
            assert!(
                !matches!(result, MatchResult::Failed(_)),
                "{mode:?}: {result:?}"
            );
        }
    }
}

/// `n` ground elements of `set_definition`, `0 .. n` padded so that their order is the numbers'.
fn ground_set(n: usize) -> (Term, impl Fn(usize) -> Term) {
    let element = |index: usize| domain_value(Sort::simple("SetElement"), &format!("{index:05}"));
    let subject = Term::set(set_definition(), (0..n).map(element).collect(), None);
    (subject, element)
}

/// A pattern that names one element of an `n`-element subject set beside a rest variable binds
/// the rest to the subject's tree without that element: a removal, which summarizes only the
/// elements of the nodes it rebuilds on one path (at most `2B`, in a leaf and the sibling it may
/// be merged with), not the `n - 1` elements of a set built anew from a copy.
#[test]
fn matching_one_element_of_a_set_binds_the_rest_to_one_removal_from_the_subject() {
    const ELEMENTS: usize = 4096;
    let (subject, element) = ground_set(ELEMENTS);
    let TermKind::Set {
        elements: subject_elements,
        ..
    } = subject.kind()
    else {
        unreachable!()
    };
    let rest = variable("REST", Sort::simple("SetSort"));
    let bound = 2 * crate::term::chunked::DEFAULT_BRANCHING;
    for index in [0, ELEMENTS / 2, ELEMENTS - 1] {
        let pattern = Term::set(
            set_definition(),
            vec![element(index)],
            Some(Term::variable(rest.clone())),
        );
        let mut result = None;
        let summarized = crate::term::items::element_summaries_during(|| {
            result = Some(match_terms(
                MatchMode::Rewrite,
                &sort_graph(),
                &pattern,
                &subject,
            ));
        });
        assert!(
            summarized <= bound,
            "element {index}: {summarized} element summaries, bound {bound}"
        );
        let expected =
            Term::set_of_items(set_definition(), subject_elements.remove_at(index).0, None);
        assert_eq!(
            result,
            Some(MatchResult::Success(Substitution::from([(
                rest.clone(),
                expected
            )]))),
            "element {index}"
        );
    }
}

fn list_definition() -> Arc<crate::term::ListDefinition> {
    Arc::new(crate::term::ListDefinition {
        symbols: collection_symbols("list"),
        element_sort: Sort::simple("ListElement"),
        list_sort: "ListSort".into(),
    })
}

/// The heads (or tails) tree of a list term.
fn list_parts(
    list: &Term,
) -> (
    crate::term::Items<Term>,
    Option<(Term, crate::term::Items<Term>)>,
) {
    let TermKind::List { heads, rest, .. } = list.kind() else {
        panic!("a list: {list:?}");
    };
    (heads.clone(), rest.clone())
}

/// Patterns that name items at the ends of a long subject list beside a rest variable bind the
/// rest to the subject's trees cut where those items end: a cut summarizes only the items of the
/// leaves it rebuilds (a leaf and the neighbour it may be merged with, at most `2B`, per cut),
/// not the items of a list built anew from a copy. The subject may itself be open: the rest then
/// holds the subject's opaque middle between the cut heads and its tails.
#[test]
fn matching_items_at_the_ends_of_a_list_binds_the_rest_to_a_cut_of_the_subject() {
    const ITEMS: usize = 4096;
    let item = |index: usize| domain_value(Sort::simple("ListElement"), &index.to_string());
    let items = |range: std::ops::Range<usize>| range.map(item).collect::<Vec<_>>();
    let rest = variable("REST", Sort::simple("ListSort"));
    let first = variable("FIRST", Sort::simple("ListElement"));
    let last = variable("LAST", Sort::simple("ListElement"));
    let middle = var("MIDDLE", Sort::simple("ListSort"));
    let closed = Term::list(list_definition(), items(0..ITEMS), None);
    let open = Term::list(
        list_definition(),
        items(0..ITEMS),
        Some((middle.clone(), items(ITEMS..2 * ITEMS))),
    );
    let (heads, _) = list_parts(&closed);
    let pattern = |heads: Vec<Term>, tails: Vec<Term>| {
        Term::list(
            list_definition(),
            heads,
            Some((Term::variable(rest.clone()), tails)),
        )
    };
    let first_item = || vec![Term::variable(first.clone())];
    let last_item = || vec![Term::variable(last.clone())];
    let from_list = |heads, rest| Term::list_of_items(list_definition(), heads, rest);
    let (open_heads, open_rest) = list_parts(&open);
    let (_, open_tails) = open_rest.expect("an open list");
    let cases = [
        (
            "ListItem(FIRST) REST",
            pattern(first_item(), vec![]),
            &closed,
            1,
            vec![
                (first.clone(), item(0)),
                (rest.clone(), from_list(heads.split_at(1).1, None)),
            ],
        ),
        (
            "REST ListItem(LAST)",
            pattern(vec![], last_item()),
            &closed,
            1,
            vec![
                (last.clone(), item(ITEMS - 1)),
                (rest.clone(), from_list(heads.split_at(ITEMS - 1).0, None)),
            ],
        ),
        (
            "ListItem(FIRST) REST ListItem(LAST)",
            pattern(first_item(), last_item()),
            &closed,
            2,
            vec![
                (first.clone(), item(0)),
                (last.clone(), item(ITEMS - 1)),
                (
                    rest.clone(),
                    from_list(heads.split_at(1).1.split_at(ITEMS - 2).0, None),
                ),
            ],
        ),
        (
            "ListItem(FIRST) REST on an open subject",
            pattern(first_item(), vec![]),
            &open,
            1,
            vec![
                (first.clone(), item(0)),
                (
                    rest.clone(),
                    from_list(
                        open_heads.split_at(1).1,
                        Some((middle.clone(), open_tails.clone())),
                    ),
                ),
            ],
        ),
        (
            "REST ListItem(LAST) on an open subject",
            pattern(vec![], last_item()),
            &open,
            1,
            vec![
                (last.clone(), item(2 * ITEMS - 1)),
                (
                    rest.clone(),
                    from_list(
                        open_heads.clone(),
                        Some((middle.clone(), open_tails.split_at(ITEMS - 1).0)),
                    ),
                ),
            ],
        ),
    ];
    let leaf = crate::term::chunked::DEFAULT_BRANCHING;
    for (shape, pattern, subject, cuts, expected) in cases {
        let mut result = None;
        let summarized = crate::term::items::element_summaries_during(|| {
            result = Some(match_terms(
                MatchMode::Rewrite,
                &sort_graph(),
                &pattern,
                subject,
            ));
        });
        assert!(
            summarized <= cuts * 2 * leaf,
            "{shape}: {summarized} item summaries for {cuts} cuts"
        );
        assert_eq!(
            result,
            Some(MatchResult::Success(Substitution::from_iter(expected))),
            "{shape}"
        );
    }
}

/// The collection solver narrows a subject frame against a long closed pattern list to the
/// pattern's items between the subject's heads and tails, cut from the pattern's tree: at most
/// `2B` item summaries per cut, whatever the list's length.
#[test]
fn narrowing_a_list_frame_against_a_long_list_cuts_the_closed_side() {
    const ITEMS: usize = 4096;
    let definition = collection_definition();
    let small = internal_term(
        &definition,
        r#"listConcat{}(listItem{}(\dv{SortElement{}}("0")), listItem{}(\dv{SortElement{}}("1")))"#,
    );
    let TermKind::List {
        definition: list, ..
    } = small.kind()
    else {
        panic!("a list: {small:?}");
    };
    let item = |index: usize| domain_value(Sort::simple("SortElement"), &index.to_string());
    let pattern = Term::list(list.clone(), (0..ITEMS).map(item).collect(), None);
    let frame = variable("FRAME", Sort::simple("SortList"));
    let subject = Term::list(
        list.clone(),
        vec![item(0)],
        Some((Term::variable(frame.clone()), vec![item(ITEMS - 1)])),
    );
    let (heads, _) = list_parts(&pattern);
    let expected = Term::list_of_items(
        list.clone(),
        heads.split_at(1).1.split_at(ITEMS - 2).0,
        None,
    );
    let mut solutions = None;
    let summarized = crate::term::items::element_summaries_during(|| {
        solutions = Some(solve_with_test_frames(
            &definition,
            &[(pattern.clone(), subject.clone())],
        ));
    });
    let leaf = crate::term::chunked::DEFAULT_BRANCHING;
    assert!(
        summarized <= 2 * 2 * leaf,
        "{summarized} item summaries for two cuts"
    );
    let solutions = solutions
        .flatten()
        .expect("a subject frame against a closed list is narrowable");
    assert_eq!(solutions.len(), 1, "{solutions:?}");
    assert_eq!(
        solutions[0].matched.substitution().get(&frame),
        Some(&expected),
        "{solutions:?}"
    );
}

/// A constructor-like pattern element that a set of constructor-like elements does not hold
/// refutes the match from the elements' summary alone: no set of the subject's other elements is
/// built (no element summarized), so the failure costs the search and not the size of the
/// subject.
#[test]
fn a_ground_element_missing_from_a_ground_set_fails_without_copying_its_other_elements() {
    const ELEMENTS: usize = 4096;
    let (subject, element) = ground_set(ELEMENTS);
    for rest in [None, Some(var("REST", Sort::simple("SetSort")))] {
        let pattern = Term::set(set_definition(), vec![element(ELEMENTS + 1)], rest);
        for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
            let summarized = crate::term::items::element_summaries_during(|| {
                assert_eq!(
                    match_terms(mode, &sort_graph(), &pattern, &subject),
                    MatchResult::Failed(FailReason::KeyNotFound(element(ELEMENTS + 1))),
                    "{mode:?}"
                );
            });
            assert_eq!(
                summarized, 0,
                "{mode:?}: a set of the subject's other elements was built"
            );
        }
    }
}

/// A constructor-like pattern element that the subject does not hold syntactically is refuted
/// only when every subject element is constructor-like and the subject has no rest: a symbolic
/// subject element may denote it, and so may a subject rest.
#[test]
fn a_ground_element_missing_beside_a_symbolic_element_or_a_subject_rest_is_not_refuted() {
    let element = |name: &str| domain_value(Sort::simple("SetElement"), name);
    for (subject_elements, subject_rest) in [
        (
            vec![
                element("a"),
                var("E", Sort::simple("SetElement")),
                element("c"),
            ],
            None,
        ),
        (
            vec![element("a"), element("c")],
            Some(var("FRAME", Sort::simple("SetSort"))),
        ),
    ] {
        let subject = Term::set(set_definition(), subject_elements, subject_rest);
        for rest in [None, Some(var("REST", Sort::simple("SetSort")))] {
            let pattern = Term::set(set_definition(), vec![element("b")], rest);
            for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
                let result = match_terms(mode, &sort_graph(), &pattern, &subject);
                assert!(
                    !matches!(result, MatchResult::Failed(_)),
                    "{mode:?} on {subject:?}: {result:?}"
                );
            }
        }
    }
}

/// Each candidate the collection solver tries for a symbolic pattern element against an
/// `n`-element closed subject binds the pattern's rest to the subject's tree without that
/// element: one removal per candidate, which summarizes at most `2B` elements, not a copy of
/// the other `n - 1`.
#[test]
fn each_candidate_frame_of_a_symbolic_element_is_one_removal_from_the_subject() {
    const ELEMENTS: usize = 1024;
    let definition = collection_definition();
    let one = internal_term(&definition, r#"setItem{}(\dv{SortElement{}}("0"))"#);
    let TermKind::Set {
        definition: set, ..
    } = one.kind()
    else {
        panic!("a set item should internalize as a set");
    };
    let element = |index: usize| {
        internal_term(
            &definition,
            &format!(r#"\dv{{SortElement{{}}}}("{index:05}")"#),
        )
    };
    let subject = Term::set(set.clone(), (0..ELEMENTS).map(element).collect(), None);
    let pattern = internal_term(
        &definition,
        "setConcat{}(setItem{}(ELEMENT:SortElement{}), REST:SortSet{})",
    );
    let mut solutions = None;
    let summarized = crate::term::items::element_summaries_during(|| {
        solutions = solve_with_test_frames(&definition, &[(pattern, subject.clone())]);
    });
    let solutions = solutions.expect("a closed subject set is decided");
    assert_eq!(solutions.len(), ELEMENTS);
    let bound = ELEMENTS * 2 * crate::term::chunked::DEFAULT_BRANCHING;
    assert!(
        summarized <= bound,
        "{summarized} element summaries for {ELEMENTS} candidates, bound {bound}"
    );
    let TermKind::Set {
        elements: subject_elements,
        ..
    } = subject.kind()
    else {
        unreachable!()
    };
    let rest = Variable::new("REST", Sort::simple("SortSet"));
    let element_variable = Variable::new("ELEMENT", Sort::simple("SortElement"));
    for solution in &solutions {
        let substitution = solution.matched.substitution();
        let bound_element = substitution
            .get(&element_variable)
            .expect("ELEMENT is bound");
        let index = subject_elements
            .search(bound_element)
            .expect("ELEMENT is bound to a subject element");
        let expected = Term::set_of_items(set.clone(), subject_elements.remove_at(index).0, None);
        assert_eq!(
            substitution.get(&rest),
            Some(&expected),
            "ELEMENT = {bound_element:?}"
        );
    }
}

/// A set of the constructor terms `wrap(K)`, whose elements a pattern can alias, a constructor
/// pairing one with such a set, and a map between such terms, keyed like a `multiplicity="*"`
/// cell's instances by a part of their values, with a constructor pairing a key with such a map.
fn wrapped_collections_definition() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
        module MAIN
            sort SortKey{} [hasDomainValues{}()]
            sort SortWrapped{} []
            hooked-sort SortWrappedSet{}
                [hook{}("SET.Set"), unit{}(wrappedSetUnit{}()), element{}(wrappedSetItem{}()), concat{}(wrappedSetConcat{}())]
            hooked-symbol wrappedSetUnit{}() : SortWrappedSet{} [function{}(), total{}(), hook{}("SET.unit")]
            hooked-symbol wrappedSetItem{}(SortWrapped{}) : SortWrappedSet{} [function{}(), total{}(), hook{}("SET.element")]
            hooked-symbol wrappedSetConcat{}(SortWrappedSet{}, SortWrappedSet{}) : SortWrappedSet{} [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
            symbol wrap{}(SortKey{}) : SortWrapped{} [constructor{}(), functional{}()]
            symbol pairOf{}(SortWrapped{}, SortWrappedSet{}) : SortWrapped{} [constructor{}(), functional{}()]
            hooked-sort SortWrappedMap{}
                [hook{}("MAP.Map"), unit{}(wrappedMapUnit{}()), element{}(wrappedMapItem{}()), concat{}(wrappedMapConcat{}())]
            hooked-symbol wrappedMapUnit{}() : SortWrappedMap{} [function{}(), total{}(), hook{}("MAP.unit")]
            hooked-symbol wrappedMapItem{}(SortWrapped{}, SortWrapped{}) : SortWrappedMap{} [function{}(), total{}(), hook{}("MAP.element")]
            hooked-symbol wrappedMapConcat{}(SortWrappedMap{}, SortWrappedMap{}) : SortWrappedMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
            symbol keyedMap{}(SortKey{}, SortWrappedMap{}) : SortWrapped{} [constructor{}(), functional{}()]
        endmodule []"#,
    )
    .expect("wrapped collections definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("wrapped collections definition should internalize")
}

/// Whether `term` holds a conjunction of two terms anywhere.
fn holds_a_conjunction(term: &Term) -> bool {
    match term.kind() {
        TermKind::And(..) => true,
        TermKind::Application { arguments, .. } => arguments.iter().any(holds_a_conjunction),
        TermKind::Injection { term, .. } => holds_a_conjunction(term),
        TermKind::Set { elements, rest, .. } => {
            elements.iter().any(holds_a_conjunction)
                || rest.as_ref().is_some_and(holds_a_conjunction)
        }
        TermKind::Map { entries, rest, .. } => {
            entries
                .iter()
                .any(|(key, value)| holds_a_conjunction(key) || holds_a_conjunction(value))
                || rest.as_ref().is_some_and(holds_a_conjunction)
        }
        _ => false,
    }
}

/// An alias `P #as A` of a set element, `\and(P, A)`, is the element `P` matches with `A`
/// bound to it. Against several subject elements the set goes to the collection solver as the
/// set holding `P`, with `A` bound to `P`, so each solution binds `A` to the element `P` takes
/// there and no conjunction is left in the deferred pair for a condition to carry.
#[test]
fn an_aliased_set_element_among_several_binds_its_alias_to_each_element_its_pattern_takes() {
    let definition = wrapped_collections_definition();
    let pattern = internal_term(
        &definition,
        r#"wrappedSetConcat{}(wrappedSetItem{}(\and{SortWrapped{}}(wrap{}(K:SortKey{}), A:SortWrapped{})), REST:SortWrappedSet{})"#,
    );
    let subject = internal_term(
        &definition,
        r#"wrappedSetConcat{}(wrappedSetItem{}(wrap{}(\dv{SortKey{}}("1"))), wrappedSetConcat{}(wrappedSetItem{}(wrap{}(\dv{SortKey{}}("2"))), wrappedSetItem{}(wrap{}(\dv{SortKey{}}("3")))))"#,
    );
    let MatchResult::Indeterminate {
        substitution,
        remainder,
    } = match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject)
    else {
        panic!("a symbolic element among three is left to the collection solver");
    };
    assert!(
        remainder
            .iter()
            .all(|(pattern, _)| !holds_a_conjunction(pattern)),
        "{remainder:?}"
    );
    let solutions = solve_collection_pairs_in_definition(
        MatchMode::Rewrite,
        &definition,
        substitution,
        &remainder,
        None,
    )
    .expect("a closed subject set is decidable");
    let alias = variable("A", Sort::simple("SortWrapped"));
    let key = variable("K", Sort::simple("SortKey"));
    let aliased = internal_term(&definition, "wrap{}(K:SortKey{})");
    let mut taken = solutions
        .iter()
        .map(|solution| {
            let substitution = solution.matched.substitution();
            assert_eq!(
                substitution.get(&alias),
                Some(&crate::substitution::substitute(&aliased, substitution)),
                "{substitution:?}"
            );
            substitution[&key].clone()
        })
        .collect::<Vec<_>>();
    taken.sort();
    let keys = ["1", "2", "3"]
        .map(|key| internal_term(&definition, &format!(r#"\dv{{SortKey{{}}}}("{key}")"#)));
    assert_eq!(taken, keys);
}

/// When the alias's variable is bound before its set is matched, the element is that value,
/// which the aliased pattern must match: the set holding it is matched as one holding the
/// value, without a deferred conjunction.
#[test]
fn an_aliased_set_element_whose_alias_is_bound_is_the_bound_value() {
    let definition = wrapped_collections_definition();
    let pattern = internal_term(
        &definition,
        r#"pairOf{}(A:SortWrapped{}, wrappedSetConcat{}(wrappedSetItem{}(\and{SortWrapped{}}(wrap{}(K:SortKey{}), A:SortWrapped{})), REST:SortWrappedSet{}))"#,
    );
    let subject = |given: &str| {
        internal_term(
            &definition,
            &format!(
                r#"pairOf{{}}(wrap{{}}(\dv{{SortKey{{}}}}("{given}")), wrappedSetConcat{{}}(wrappedSetItem{{}}(wrap{{}}(\dv{{SortKey{{}}}}("1"))), wrappedSetConcat{{}}(wrappedSetItem{{}}(wrap{{}}(\dv{{SortKey{{}}}}("2"))), wrappedSetItem{{}}(wrap{{}}(\dv{{SortKey{{}}}}("3"))))))"#
            ),
        )
    };
    let MatchResult::Success(substitution) =
        match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject("2"))
    else {
        panic!("the bound value is found among the subject's elements");
    };
    assert_eq!(
        substitution.get(&variable("K", Sort::simple("SortKey"))),
        Some(&internal_term(&definition, r#"\dv{SortKey{}}("2")"#))
    );
    assert_eq!(
        substitution.get(&variable("REST", Sort::simple("SortWrappedSet"))),
        Some(&internal_term(
            &definition,
            r#"wrappedSetConcat{}(wrappedSetItem{}(wrap{}(\dv{SortKey{}}("1"))), wrappedSetItem{}(wrap{}(\dv{SortKey{}}("3"))))"#
        ))
    );
    assert!(matches!(
        match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject("4")),
        MatchResult::Failed(_)
    ));
}

/// The wrapped map `{wrap(1) |-> wrap-value(1), wrap(2) |-> ..., wrap(3) |-> ...}`, each value
/// built by `value` from its key's number, as a KORE pattern.
fn three_wrapped_entries(value: impl Fn(&str) -> String) -> String {
    let entry = |key: &str| {
        format!(
            r#"wrappedMapItem{{}}(wrap{{}}(\dv{{SortKey{{}}}}("{key}")), {})"#,
            value(key)
        )
    };
    format!(
        "wrappedMapConcat{{}}({}, wrappedMapConcat{{}}({}, {}))",
        entry("1"),
        entry("2"),
        entry("3")
    )
}

/// An aliased map key `\and(P, K)`, as a `multiplicity="*"` cell's key cell aliased in its
/// instance's pattern, is the key `P` matches with `K` bound to it: with `P` ground under the
/// substitution it is sought as `P` among the subject's keys, so the match succeeds with `K`
/// the key found, or fails when no key is `P`, with no pair left to the collection solver.
#[test]
fn an_aliased_map_key_is_sought_as_the_pattern_it_aliases() {
    let definition = wrapped_collections_definition();
    let pattern = internal_term(
        &definition,
        r#"keyedMap{}(I:SortKey{}, wrappedMapConcat{}(wrappedMapItem{}(\and{SortWrapped{}}(wrap{}(I:SortKey{}), K:SortWrapped{}), V:SortWrapped{}), REST:SortWrappedMap{}))"#,
    );
    let entries = three_wrapped_entries(|key| format!(r#"wrap{{}}(\dv{{SortKey{{}}}}("{key}0"))"#));
    let subject = |given: &str| {
        internal_term(
            &definition,
            &format!(r#"keyedMap{{}}(\dv{{SortKey{{}}}}("{given}"), {entries})"#),
        )
    };
    let MatchResult::Success(substitution) =
        match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject("2"))
    else {
        panic!("the aliased key is found among the subject's keys");
    };
    let wrapped = |key: &str| {
        internal_term(
            &definition,
            &format!(r#"wrap{{}}(\dv{{SortKey{{}}}}("{key}"))"#),
        )
    };
    let wrapped_sort = Sort::simple("SortWrapped");
    assert_eq!(
        substitution.get(&variable("K", wrapped_sort.clone())),
        Some(&wrapped("2"))
    );
    assert_eq!(
        substitution.get(&variable("V", wrapped_sort)),
        Some(&wrapped("20"))
    );
    assert_eq!(
        substitution.get(&variable("REST", Sort::simple("SortWrappedMap"))),
        Some(&internal_term(
            &definition,
            r#"wrappedMapConcat{}(wrappedMapItem{}(wrap{}(\dv{SortKey{}}("1")), wrap{}(\dv{SortKey{}}("10"))), wrappedMapItem{}(wrap{}(\dv{SortKey{}}("3")), wrap{}(\dv{SortKey{}}("30"))))"#
        ))
    );
    assert!(matches!(
        match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject("4")),
        MatchResult::Failed(_)
    ));
}

/// An aliased map key whose pattern is symbolic, `\and(wrap(I), K)`, with the same alias inside
/// the entry's aliased value, `\and(pairOf(\and(wrap(I), K), S), A)` (a `multiplicity="*"` cell
/// instance read through an alias, its key cell aliased inside it): against several entries the
/// map goes to the collection solver with each alias read as its pattern, its variable bound to
/// that pattern, so no conjunction is left for a condition to carry and each solution binds `K`
/// and `A` to the key and the value of the entry it takes.
#[test]
fn an_aliased_map_key_among_several_binds_its_aliases_to_each_entry_its_pattern_takes() {
    let definition = wrapped_collections_definition();
    let pattern = internal_term(
        &definition,
        r#"wrappedMapConcat{}(wrappedMapItem{}(\and{SortWrapped{}}(wrap{}(I:SortKey{}), K:SortWrapped{}), \and{SortWrapped{}}(pairOf{}(\and{SortWrapped{}}(wrap{}(I:SortKey{}), K:SortWrapped{}), S:SortWrappedSet{}), A:SortWrapped{})), REST:SortWrappedMap{})"#,
    );
    let subject = internal_term(
        &definition,
        &three_wrapped_entries(|key| {
            format!(r#"pairOf{{}}(wrap{{}}(\dv{{SortKey{{}}}}("{key}")), wrappedSetUnit{{}}())"#)
        }),
    );
    let MatchResult::Indeterminate {
        substitution,
        remainder,
    } = match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject)
    else {
        panic!("a symbolic key among three is left to the collection solver");
    };
    assert!(
        remainder
            .iter()
            .all(|(pattern, _)| !holds_a_conjunction(pattern)),
        "{remainder:?}"
    );
    let solutions = solve_collection_pairs_in_definition(
        MatchMode::Rewrite,
        &definition,
        substitution,
        &remainder,
        None,
    )
    .expect("a closed subject map is decidable");
    let wrapped_sort = Sort::simple("SortWrapped");
    let key_pattern = internal_term(&definition, "wrap{}(I:SortKey{})");
    let value_pattern = internal_term(
        &definition,
        "pairOf{}(wrap{}(I:SortKey{}), S:SortWrappedSet{})",
    );
    let mut taken = solutions
        .iter()
        .map(|solution| {
            let substitution = solution.matched.substitution();
            let instance = |term: &Term| crate::substitution::substitute(term, substitution);
            assert_eq!(
                substitution.get(&variable("K", wrapped_sort.clone())),
                Some(&instance(&key_pattern)),
                "{substitution:?}"
            );
            assert_eq!(
                substitution.get(&variable("A", wrapped_sort.clone())),
                Some(&instance(&value_pattern)),
                "{substitution:?}"
            );
            substitution[&variable("I", Sort::simple("SortKey"))].clone()
        })
        .collect::<Vec<_>>();
    taken.sort();
    let keys = ["1", "2", "3"]
        .map(|key| internal_term(&definition, &format!(r#"\dv{{SortKey{{}}}}("{key}")"#)));
    assert_eq!(taken, keys);
}

/// An alias inside an aliased set element, `\and(pairOf(\and(wrap(I), K), S), A)` (a
/// `multiplicity="*"` cell instance read through an alias, its key cell aliased inside it): against
/// several elements the set goes to the collection solver with each alias read as its pattern,
/// so neither the deferred set nor the value of `A` holds a conjunction, and each solution binds
/// `K` and `A` to the parts of the element it takes.
#[test]
fn an_alias_inside_an_aliased_set_element_is_read_as_its_pattern() {
    let definition = wrapped_collections_definition();
    let pattern = internal_term(
        &definition,
        r#"wrappedSetConcat{}(wrappedSetItem{}(\and{SortWrapped{}}(pairOf{}(\and{SortWrapped{}}(wrap{}(I:SortKey{}), K:SortWrapped{}), S:SortWrappedSet{}), A:SortWrapped{})), REST:SortWrappedSet{})"#,
    );
    let element = |key: &str| {
        format!(
            r#"wrappedSetItem{{}}(pairOf{{}}(wrap{{}}(\dv{{SortKey{{}}}}("{key}")), wrappedSetUnit{{}}()))"#
        )
    };
    let subject = internal_term(
        &definition,
        &format!(
            "wrappedSetConcat{{}}({}, wrappedSetConcat{{}}({}, {}))",
            element("1"),
            element("2"),
            element("3")
        ),
    );
    let MatchResult::Indeterminate {
        substitution,
        remainder,
    } = match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject)
    else {
        panic!("a symbolic element among three is left to the collection solver");
    };
    assert!(
        remainder
            .iter()
            .all(|(pattern, _)| !holds_a_conjunction(pattern)),
        "{remainder:?}"
    );
    let solutions = solve_collection_pairs_in_definition(
        MatchMode::Rewrite,
        &definition,
        substitution,
        &remainder,
        None,
    )
    .expect("a closed subject set is decidable");
    let wrapped_sort = Sort::simple("SortWrapped");
    let key_pattern = internal_term(&definition, "wrap{}(I:SortKey{})");
    let element_pattern = internal_term(
        &definition,
        "pairOf{}(wrap{}(I:SortKey{}), S:SortWrappedSet{})",
    );
    let mut taken = solutions
        .iter()
        .map(|solution| {
            let substitution = solution.matched.substitution();
            let instance = |term: &Term| crate::substitution::substitute(term, substitution);
            assert_eq!(
                substitution.get(&variable("K", wrapped_sort.clone())),
                Some(&instance(&key_pattern)),
                "{substitution:?}"
            );
            assert_eq!(
                substitution.get(&variable("A", wrapped_sort.clone())),
                Some(&instance(&element_pattern)),
                "{substitution:?}"
            );
            substitution[&variable("I", Sort::simple("SortKey"))].clone()
        })
        .collect::<Vec<_>>();
    taken.sort();
    let keys = ["1", "2", "3"]
        .map(|key| internal_term(&definition, &format!(r#"\dv{{SortKey{{}}}}("{key}")"#)));
    assert_eq!(taken, keys);
}

/// The set of `collection_definition` concatenating `parts` (each a KORE set term).
fn concat_set(definition: &BackendDefinition, parts: &[&str]) -> Term {
    let source = parts
        .iter()
        .rev()
        .fold(None, |right: Option<String>, part| {
            Some(match right {
                None => (*part).to_owned(),
                Some(right) => format!("setConcat{{}}({part}, {right})"),
            })
        })
        .unwrap_or_else(|| "setUnit{}()".to_owned());
    internal_term(definition, &source)
}

/// Set concatenation is associative and commutative with unit `.Set`, so free parts beside an
/// item are one part: the first keeps the place of all of them and the others are empty, in a
/// set and in a map alike.
#[test]
fn free_set_and_map_parts_merge_into_the_first() {
    let definition = collection_definition();
    let set = Sort::simple("SortSet");
    let b = r#"setItem{}(\dv{SortElement{}}("b"))"#;
    let pattern = concat_set(
        &definition,
        &["A:SortSet{}", b, "B:SortSet{}", "C:SortSet{}"],
    );
    let empty = concat_set(&definition, &[]);
    assert_eq!(
        merge_free_parts(&pattern, |_| true),
        Some((
            concat_set(&definition, &[b, "A:SortSet{}"]),
            vec![
                (variable("B", set.clone()), empty.clone()),
                (variable("C", set.clone()), empty.clone()),
            ],
        )),
    );
    // With no item, the merged parts leave the first part alone.
    let parts = concat_set(&definition, &["A:SortSet{}", "B:SortSet{}"]);
    assert_eq!(
        merge_free_parts(&parts, |_| true),
        Some((
            var("A", set.clone()),
            vec![(variable("B", set.clone()), empty)],
        )),
    );

    let map = Sort::simple("SortMap");
    let entry = r#"mapItem{}(\dv{SortKey{}}("k"), \dv{SortValue{}}("v"))"#;
    let pattern = internal_term(
        &definition,
        &format!("mapConcat{{}}(M:SortMap{{}}, mapConcat{{}}({entry}, N:SortMap{{}}))"),
    );
    assert_eq!(
        merge_free_parts(&pattern, |_| true),
        Some((
            internal_term(
                &definition,
                &format!("mapConcat{{}}({entry}, M:SortMap{{}})")
            ),
            vec![(
                variable("N", map),
                internal_term(&definition, "mapUnit{}()")
            )],
        )),
    );
}

/// A current set or map of items alone is defined on each instance, so its items are pairwise
/// distinct: a destination item is one of them, each placement is one branch of term equations,
/// and the destination's part holds the items no destination item took. A placement whose match
/// fails (`b` on `c`) has no branch; with two undecided current items there are two.
#[test]
fn a_destination_item_against_current_items_alone_has_a_branch_per_placement() {
    let definition = collection_definition();
    let set = Sort::simple("SortSet");
    let element = Sort::simple("SortElement");
    let b = r#"setItem{}(\dv{SortElement{}}("b"))"#;
    let c = r#"setItem{}(\dv{SortElement{}}("c"))"#;
    let pattern = concat_set(&definition, &[b, "A:SortSet{}"]);
    let a = var("A", set.clone());
    let x = var("X", element.clone());
    let y = var("Y", element.clone());

    // One undecided current item: the destination item is `X`.
    let subject = concat_set(&definition, &["setItem{}(X:SortElement{})", c]);
    assert_eq!(
        expand_implication_remainders(
            &definition,
            &Substitution::new(),
            &[(pattern.clone(), subject)],
        ),
        Some(vec![vec![
            (element_value("b"), x.clone()),
            (a.clone(), concat_set(&definition, &[c])),
        ]]),
    );

    // Two: `X` or `Y`, the other one left for the part.
    let subject = concat_set(
        &definition,
        &["setItem{}(X:SortElement{})", "setItem{}(Y:SortElement{})"],
    );
    let mut expected = vec![
        vec![
            (element_value("b"), x.clone()),
            (
                a.clone(),
                concat_set(&definition, &["setItem{}(Y:SortElement{})"]),
            ),
        ],
        vec![
            (element_value("b"), y.clone()),
            (
                a.clone(),
                concat_set(&definition, &["setItem{}(X:SortElement{})"]),
            ),
        ],
    ];
    expected.sort();
    assert_eq!(
        expand_implication_remainders(&definition, &Substitution::new(), &[(pattern, subject)]),
        Some(expected),
    );

    // A destination item identical to a current one is that one; without a part, no current
    // item may be left, so a closed destination with fewer items has no branch.
    let pattern = concat_set(&definition, &[b, "setItem{}(Z:SortElement{})"]);
    let subject = concat_set(&definition, &[b, "setItem{}(X:SortElement{})"]);
    assert_eq!(
        expand_implication_remainders(&definition, &Substitution::new(), &[(pattern, subject)]),
        Some(vec![vec![(var("Z", element.clone()), x.clone())]]),
    );
    let subject = concat_set(&definition, &["setItem{}(X:SortElement{})", c]);
    assert_eq!(
        expand_implication_remainders(
            &definition,
            &Substitution::new(),
            &[(concat_set(&definition, &[b]), subject)],
        ),
        Some(Vec::new()),
    );

    // A map entry: its key and its value.
    let pattern = internal_term(
        &definition,
        r#"mapConcat{}(mapItem{}(\dv{SortKey{}}("k"), \dv{SortValue{}}("v")), M:SortMap{})"#,
    );
    let subject = internal_term(&definition, "mapItem{}(K:SortKey{}, V:SortValue{})");
    assert_eq!(
        expand_implication_remainders(&definition, &Substitution::new(), &[(pattern, subject)]),
        Some(vec![vec![
            (
                domain_value(Sort::simple("SortKey"), "k"),
                var("K", Sort::simple("SortKey")),
            ),
            (
                domain_value(Sort::simple("SortValue"), "v"),
                var("V", Sort::simple("SortValue")),
            ),
            (
                var("M", Sort::simple("SortMap")),
                internal_term(&definition, "mapUnit{}()"),
            ),
        ]]),
    );
}

/// A part that the caller does not accept, that occurs twice, or that is no variable keeps its
/// place, and fewer than two free parts merge nothing.
#[test]
fn only_free_variable_parts_that_occur_once_merge() {
    let definition = collection_definition();
    let set = Sort::simple("SortSet");
    let b = r#"setItem{}(\dv{SortElement{}}("b"))"#;
    let empty = concat_set(&definition, &[]);
    let pattern = concat_set(
        &definition,
        &["A:SortSet{}", b, "B:SortSet{}", "C:SortSet{}"],
    );
    let c = variable("C", set.clone());
    assert_eq!(
        merge_free_parts(&pattern, |variable| variable != &c),
        Some((
            concat_set(&definition, &[b, "A:SortSet{}", "C:SortSet{}"]),
            vec![(variable("B", set.clone()), empty)],
        )),
    );
    let a = variable("A", set.clone());
    let only_a = |variable: &Variable| variable == &a;
    assert_eq!(merge_free_parts(&pattern, only_a), None);

    let repeated = concat_set(&definition, &["A:SortSet{}", "A:SortSet{}", b]);
    assert_eq!(merge_free_parts(&repeated, |_| true), None);
    let opaque = concat_set(
        &definition,
        &["A:SortSet{}", r#"opaqueSet{}(\dv{SortElement{}}("e"))"#, b],
    );
    assert_eq!(merge_free_parts(&opaque, |_| true), None);
    // A closed set has no part.
    assert_eq!(
        merge_free_parts(&concat_set(&definition, &[b]), |_| true),
        None
    );
}
