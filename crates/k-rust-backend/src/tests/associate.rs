//! `BackendDefinition::associate_collections`: the associated form of a request internalizes,
//! verifies and refuses as the nested form does, and its height does not grow with a
//! collection's length.

use k_rust_kore::kore::ast::{Pattern as KorePattern, Sort as KoreSort, Symbol};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::{BackendDefinition, DefinitionError, UnlicensedInjectionSite},
    rule::{Predicate, PredicateReading},
    term::Term,
};

fn collection_definition() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            sort SortOther{} []
            hooked-sort SortList{}
                [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
            hooked-sort SortSet{}
                [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
            hooked-sort SortMap{}
                [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
            hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
            hooked-symbol listItem{}(SortInt{}) : SortList{} [function{}(), total{}(), hook{}("LIST.element")]
            hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{} [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
            symbol opaqueList{}(SortInt{}) : SortList{} [function{}(), total{}()]
            hooked-symbol setUnit{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
            hooked-symbol setItem{}(SortInt{}) : SortSet{} [function{}(), total{}(), hook{}("SET.element")]
            hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{} [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
            symbol opaqueSet{}(SortInt{}) : SortSet{} [function{}(), total{}()]
            hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
            hooked-symbol mapItem{}(SortInt{}, SortInt{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.element")]
            hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
            symbol opaqueMap{}(SortInt{}) : SortMap{} [function{}(), total{}()]
            symbol other{}() : SortOther{} [constructor{}(), functional{}()]
            symbol pair{}(SortOther{}, SortOther{}) : SortOther{} [constructor{}(), functional{}()]
        endmodule []"#,
    )
    .expect("the collection definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the collection definition loads")
}

fn int(value: usize) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

fn item(value: usize) -> String {
    format!("listItem{{}}({})", int(value))
}

/// An element whose value is `X{value}`, with the predicate `X{value} = value` conjoined.
fn constrained_item(value: usize) -> String {
    format!(
        r"listItem{{}}(\and{{SortInt{{}}}}(X{value}:SortInt{{}}, \equals{{SortInt{{}}, SortInt{{}}}}(X{value}:SortInt{{}}, {})))",
        int(value)
    )
}

fn right(symbol: &str, parts: &[String]) -> String {
    let (last, init) = parts.split_last().expect("a spine has components");
    init.iter().rev().fold(last.clone(), |rest, part| {
        format!("{symbol}{{}}({part}, {rest})")
    })
}

fn left(symbol: &str, parts: &[String]) -> String {
    let (first, rest) = parts.split_first().expect("a spine has components");
    rest.iter().fold(first.clone(), |done, part| {
        format!("{symbol}{{}}({done}, {part})")
    })
}

fn items(count: usize) -> Vec<String> {
    (0..count).map(item).collect()
}

/// The term internalization builds, and the predicates it floats out of it, in order.
fn internalized(
    definition: &BackendDefinition,
    pattern: &KorePattern,
) -> (Result<Term, DefinitionError>, Vec<Predicate>) {
    let mut floated = Vec::new();
    let term = definition.internalize_term_collecting(
        pattern,
        &[],
        UnlicensedInjectionSite::Refuse,
        &mut floated,
        None,
        PredicateReading::Written,
    );
    (term, floated)
}

/// The verifier's verdict: its message on a failure (the location context of a failure inside
/// a spine names the associative application once instead of each nested application).
fn verified(definition: &BackendDefinition, pattern: &KorePattern) -> Result<(), String> {
    match definition.verify_standalone_pattern(pattern, &[]) {
        Ok(_) => Ok(()),
        Err(DefinitionError::Verification(error)) => Err(error.message),
        Err(other) => Err(other.to_string()),
    }
}

/// `source` has a spine to associate, and its associated form internalizes as it does (equal
/// terms or equal errors, the same floated predicates in the same order, the same constrained
/// pattern) and verifies as it does; `succeeds` says which of the two outcomes is expected.
fn assert_same_internalization(definition: &BackendDefinition, source: &str, succeeds: bool) {
    let nested = parse_pattern(source).expect("the case parses");
    let mut associated = nested.clone();
    definition.associate_collections(&mut associated);
    assert_ne!(
        associated, nested,
        "the case has a spine to associate: {source}"
    );
    assert_eq!(
        definition.associated_collections(&nested).as_ref(),
        &associated,
        "{source}"
    );
    assert!(matches!(
        definition.associated_collections(&associated),
        std::borrow::Cow::Borrowed(_)
    ));
    let expected = internalized(definition, &nested);
    assert_eq!(expected.0.is_ok(), succeeds, "{source}: {:?}", expected.0);
    assert_eq!(internalized(definition, &associated), expected, "{source}");
    assert_eq!(
        definition.internalize_pattern(&associated, &[]),
        definition.internalize_pattern(&nested, &[]),
        "{source}"
    );
    let verdict = verified(definition, &nested);
    assert_eq!(verdict.is_ok(), succeeds, "{source}: {verdict:?}");
    assert_eq!(verified(definition, &associated), verdict, "{source}");
}

#[test]
fn associated_right_left_and_mixed_spines_internalize_as_nested_ones() {
    let definition = collection_definition();
    for count in [3, 4, 7] {
        assert_same_internalization(&definition, &right("listConcat", &items(count)), true);
        assert_same_internalization(&definition, &left("listConcat", &items(count)), true);
    }
    let [a, b, c, d, e] = [0, 1, 2, 3, 4].map(item);
    for mixed in [
        format!("listConcat{{}}({a}, listConcat{{}}(listConcat{{}}({b}, {c}), {d}))"),
        format!("listConcat{{}}(listConcat{{}}({a}, {b}), listConcat{{}}({c}, {d}))"),
        format!(
            "listConcat{{}}(listConcat{{}}(listConcat{{}}({a}, {b}), {c}), listConcat{{}}({d}, {e}))"
        ),
        format!(
            "listConcat{{}}({a}, listConcat{{}}({}, {e}))",
            left("listConcat", &[b.clone(), c.clone(), d.clone()])
        ),
    ] {
        assert_same_internalization(&definition, &mixed, true);
    }
    let maps = (0..5)
        .map(|key| format!("mapItem{{}}({}, {})", int(key), int(key + 10)))
        .collect::<Vec<_>>();
    assert_same_internalization(&definition, &right("mapConcat", &maps), true);
    assert_same_internalization(&definition, &left("mapConcat", &maps), true);
    let sets = [0, 1, 2, 1, 3]
        .map(|value| format!("setItem{{}}({})", int(value)))
        .to_vec();
    assert_same_internalization(&definition, &right("setConcat", &sets), true);
    assert_same_internalization(&definition, &left("setConcat", &sets), true);
}

/// A concatenation symbol, an opaque rest of its collection and how it writes an element.
type Rest = (&'static str, String, fn(usize) -> String);

#[test]
fn associated_spines_with_opaque_rests_internalize_as_nested_ones() {
    let definition = collection_definition();
    let rests: [Rest; 4] = [
        ("listConcat", "L:SortList{}".to_owned(), item),
        ("listConcat", format!("opaqueList{{}}({})", int(9)), item),
        ("mapConcat", "M:SortMap{}".to_owned(), |key| {
            format!("mapItem{{}}({}, {})", int(key), int(key))
        }),
        ("setConcat", format!("opaqueSet{{}}({})", int(9)), |value| {
            format!("setItem{{}}({})", int(value))
        }),
    ];
    for (symbol, rest, element) in rests {
        for position in [0, 2, 4] {
            let mut parts = (0..4).map(element).collect::<Vec<_>>();
            parts.insert(position, rest.clone());
            assert_same_internalization(&definition, &right(symbol, &parts), true);
            assert_same_internalization(&definition, &left(symbol, &parts), true);
        }
    }
}

#[test]
fn associated_spines_float_the_predicates_of_their_elements_in_order() {
    let definition = collection_definition();
    let parts = (0..5).map(constrained_item).collect::<Vec<_>>();
    for source in [right("listConcat", &parts), left("listConcat", &parts)] {
        assert_same_internalization(&definition, &source, true);
        let pattern = parse_pattern(&source).expect("the case parses");
        let (_, floated) = internalized(&definition, &pattern);
        assert_eq!(floated.len(), 5, "{source}");
    }
}

#[test]
fn associated_spines_refuse_an_ill_sorted_element_as_nested_ones() {
    let definition = collection_definition();
    let ill_sorted = "listItem{}(other{}())".to_owned();
    let unknown = "nope{}()".to_owned();
    for position in [0, 2, 4] {
        let mut parts = items(5);
        parts[position] = ill_sorted.clone();
        if position < 4 {
            // A later argument that fails too: the first failure is the one reported.
            parts[4] = unknown.clone();
        }
        assert_same_internalization(&definition, &right("listConcat", &parts), false);
        assert_same_internalization(&definition, &left("listConcat", &parts), false);
    }
}

/// A left spine whose second component is a set: the nested form applies `listConcat` to the
/// first two components, and fails there, before it reads the unknown symbol of the last one;
/// the `\left-assoc` fold applies as it goes, and so fails at the same application.
#[test]
fn an_ill_sorted_fold_of_a_left_spine_is_refused_where_the_nested_form_refuses_it() {
    let definition = collection_definition();
    let parts = [
        item(0),
        format!("setItem{{}}({})", int(1)),
        item(2),
        "nope{}()".to_owned(),
    ];
    let source = left("listConcat", &parts);
    assert_same_internalization(&definition, &source, false);
    let pattern = parse_pattern(&source).expect("the case parses");
    let (term, _) = internalized(&definition, &pattern);
    assert!(
        matches!(
            term,
            Err(DefinitionError::IncorrectArgumentSort { index: 1, .. })
        ),
        "{term:?}"
    );
    assert_eq!(
        verified(&definition, &pattern),
        Err("Expecting sort SortList{} but got SortSet{}.".to_owned())
    );
    // A right spine internalizes every argument before any application, in both forms.
    let source = right("listConcat", &parts);
    assert_same_internalization(&definition, &source, false);
    let (term, _) = internalized(
        &definition,
        &parse_pattern(&source).expect("the case parses"),
    );
    assert!(
        matches!(term, Err(DefinitionError::UnknownSymbol(ref name)) if name == "nope"),
        "{term:?}"
    );
}

/// Only the concatenation symbols of builtin collections, with their declared sort arguments,
/// are associated.
#[test]
fn associate_collections_leaves_other_spines_as_they_are() {
    let definition = collection_definition();
    for source in [
        "pair{}(other{}(), pair{}(other{}(), pair{}(other{}(), other{}())))".to_owned(),
        right("listItem", &items(3)),
        right("listConcat", &items(2)),
    ] {
        let pattern = parse_pattern(&source).expect("the case parses");
        let mut associated = pattern.clone();
        definition.associate_collections(&mut associated);
        assert_eq!(associated, pattern, "{source}");
        assert!(matches!(
            definition.associated_collections(&pattern),
            std::borrow::Cow::Borrowed(_)
        ));
    }
}

fn apply(name: &str, arguments: Vec<KorePattern>) -> KorePattern {
    KorePattern::Application {
        symbol: Symbol {
            name: name.to_owned(),
            sort_parameters: Vec::new(),
        },
        arguments,
    }
}

/// A right-nested `listConcat` chain of `count` elements, built without parsing.
fn nested_list(count: usize) -> KorePattern {
    let element = |value: usize| {
        apply(
            "listItem",
            vec![KorePattern::DomainValue {
                sort: KoreSort::Application {
                    name: "SortInt".into(),
                    arguments: Vec::new(),
                },
                value: value.to_string().into(),
            }],
        )
    };
    let mut list = element(count - 1);
    for value in (0..count - 1).rev() {
        list = apply("listConcat", vec![element(value), list]);
    }
    list
}

/// A nested list one item longer than the deepest pattern the backend provides a stack for is
/// refused nested, and associated it is as deep as a three-item list: its depth does not grow
/// with its length.
#[test]
fn an_associated_list_is_as_deep_whatever_its_length() {
    let definition = collection_definition();
    let long = nested_list(crate::nesting::max_depth() + 1);
    assert!(definition.operation_depth(&[&long]) > crate::nesting::max_depth());
    let long = definition.associated_collections(&long);
    let short = nested_list(3);
    let short = definition.associated_collections(&short);
    assert_eq!(
        definition.operation_depth(&[&long]),
        definition.operation_depth(&[&short])
    );
    assert!(definition.operation_depth(&[&long]) < 8 + definition.operation_depth(&[]));
}

/// The full verification error of an ill-sorted element inside a spine: the two forms fail
/// with the same module, sentence and message, and differ only in the location context, where
/// the nested form names each application of the chain above the element and the associated
/// form names its associative application once.
#[test]
fn a_verification_failure_inside_an_associated_spine_names_the_application_once() {
    let definition = collection_definition();
    let failure = |pattern: &KorePattern| match definition.verify_standalone_pattern(pattern, &[]) {
        Err(DefinitionError::Verification(error)) => error,
        Err(other) => panic!("a verification failure: {other:?}"),
        Ok(_) => panic!("a verification failure"),
    };
    let concat = "symbol or alias 'listConcat'".to_owned();
    let element = "symbol or alias 'listItem'".to_owned();
    let mut parts = items(5);
    parts[2] = "listItem{}(other{}())".to_owned();
    // The element is the first argument of the third application of the right spine, and the
    // second argument of the third application of the left spine, counted from the root.
    for source in [right("listConcat", &parts), left("listConcat", &parts)] {
        let nested = parse_pattern(&source).expect("the case parses");
        let associated = definition.associated_collections(&nested).into_owned();
        let nested = failure(&nested);
        let associated = failure(&associated);
        assert_eq!(
            nested.context,
            [
                concat.clone(),
                concat.clone(),
                concat.clone(),
                element.clone()
            ],
            "{source}"
        );
        assert_eq!(
            associated.context,
            [concat.clone(), element.clone()],
            "{source}"
        );
        assert_eq!(
            associated.message, "Expecting sort SortInt{} but got SortOther{}.",
            "{source}"
        );
        assert_eq!(
            crate::verify::VerificationError {
                context: nested.context.clone(),
                ..associated
            },
            nested,
            "{source}"
        );
    }
}

/// `with_stack_for_associated` hands its work the associated form of each pattern, in the order
/// given, on a stack that holds the associated patterns: here a list longer than the backend's
/// deepest stack, which `with_stack_for` refuses as given, beside a constructor chain deep enough
/// that its stack is a segment of its own.
#[test]
fn with_stack_for_associated_hands_the_work_the_associated_patterns_on_their_stack() {
    let definition = collection_definition();
    let per_level = crate::nesting::stack_for_depth(1) - crate::nesting::stack_for_depth(0);
    let other = apply("other", Vec::new());
    let mut deep = other.clone();
    for _ in 0..(64 << 20) / per_level {
        deep = apply("pair", vec![other.clone(), deep]);
    }
    let long = nested_list(crate::nesting::max_depth() + 1);
    let short = parse_pattern(&right("listConcat", &items(3))).expect("the case parses");
    let patterns = [&short, &deep, &long];
    assert!(matches!(
        definition.with_stack_for(&patterns, || ()),
        Err(DefinitionError::InsufficientStack { .. })
    ));
    let expected = patterns.map(|pattern| definition.associated_collections(pattern));
    let expected = expected.iter().map(AsRef::as_ref).collect::<Vec<_>>();
    let need = crate::nesting::stack_for_depth(definition.operation_depth(&expected));
    definition
        .with_stack_for_associated(&patterns, |received| {
            assert_eq!(received, expected.as_slice());
            let remaining = crate::stop::remaining_stack().expect("the segment's bounds are known");
            // The frames between the segment's start and this closure take far less than 1 MiB.
            assert!(remaining + (1 << 20) >= need, "{remaining} of {need}");
        })
        .expect("the associated patterns are within the backend's stack");
}
