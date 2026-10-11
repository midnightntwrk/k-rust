//! A collection's element, key and value sorts may be closed instances of a parametric sort.
//!
//! A closed instance such as `SortMInt{Sort64{}}` denotes one sort, exactly as `SortInt{}` does:
//! every element of the collection has it, two elements are compared at it, and an element is
//! injected from it into a wider element sort along a declared subsort axiom. Nothing about a
//! collection depends on how its element sort's name is spelled, so a list, set and map over
//! `MInt{64}` load, and their hooks compute the values the sort's own constructors spell.
//!
//! The fixture declares the sort `MInt{64}`, whose values are domain values, a list, a set and a map over it,
//! hooked operations into and out of each, and a `KItem` list that `MInt{64}` is injected into.

use k_rust_backend::{
    definition::{BackendDefinition, DefinitionError},
    simplify::SimplificationOptions,
    term::{CollectionMetadata, Sort, Term},
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::{internal_term, unstopped};

const FIXTURE: &str = r#"[]
module MAIN
  sort SortKItem{} []
  sort Sort64{} []
  hooked-sort SortMInt{S} [hasDomainValues{}(), hook{}("MINT.MInt")]
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
  symbol inj{From, To}(From) : To [sortInjection{}()]
  axiom{R} \exists{R}(Value:SortKItem{},
      \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortMInt{Sort64{}}, SortKItem{}}(From:SortMInt{Sort64{}})))
      [subsort{SortMInt{Sort64{}}, SortKItem{}}()]

  hooked-sort SortWords{}
    [hook{}("LIST.List"), unit{}(dotWords{}()), element{}(wordItem{}()), concat{}(wordsConcat{}())]
  hooked-symbol dotWords{}() : SortWords{} [function{}(), total{}(), hook{}("LIST.unit")]
  hooked-symbol wordItem{}(SortMInt{Sort64{}}) : SortWords{}
    [function{}(), total{}(), hook{}("LIST.element")]
  hooked-symbol wordsConcat{}(SortWords{}, SortWords{}) : SortWords{}
    [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
  hooked-symbol wordsGet{}(SortWords{}, SortInt{}) : SortMInt{Sort64{}}
    [function{}(), hook{}("LIST.get")]
  hooked-symbol wordsSize{}(SortWords{}) : SortInt{} [function{}(), total{}(), hook{}("LIST.size")]

  hooked-sort SortWordSet{}
    [hook{}("SET.Set"), unit{}(dotWordSet{}()), element{}(wordSetItem{}()),
     concat{}(wordSetConcat{}())]
  hooked-symbol dotWordSet{}() : SortWordSet{} [function{}(), total{}(), hook{}("SET.unit")]
  hooked-symbol wordSetItem{}(SortMInt{Sort64{}}) : SortWordSet{}
    [function{}(), total{}(), hook{}("SET.element")]
  hooked-symbol wordSetConcat{}(SortWordSet{}, SortWordSet{}) : SortWordSet{}
    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
  hooked-symbol wordsToSet{}(SortWords{}) : SortWordSet{}
    [function{}(), total{}(), hook{}("SET.list2set")]
  hooked-symbol wordSetIn{}(SortMInt{Sort64{}}, SortWordSet{}) : SortBool{}
    [function{}(), total{}(), hook{}("SET.in")]

  hooked-sort SortWordMap{}
    [hook{}("MAP.Map"), unit{}(dotWordMap{}()), element{}(wordMapItem{}()),
     concat{}(wordMapConcat{}())]
  hooked-symbol dotWordMap{}() : SortWordMap{} [function{}(), total{}(), hook{}("MAP.unit")]
  hooked-symbol wordMapItem{}(SortMInt{Sort64{}}, SortMInt{Sort64{}}) : SortWordMap{}
    [function{}(), total{}(), hook{}("MAP.element")]
  hooked-symbol wordMapConcat{}(SortWordMap{}, SortWordMap{}) : SortWordMap{}
    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
  hooked-symbol wordMapLookup{}(SortWordMap{}, SortMInt{Sort64{}}) : SortMInt{Sort64{}}
    [function{}(), hook{}("MAP.lookup")]
  hooked-symbol wordMapKeys{}(SortWordMap{}) : SortWordSet{}
    [function{}(), total{}(), hook{}("MAP.keys")]

  hooked-sort SortList{}
    [hook{}("LIST.List"), unit{}(dotList{}()), element{}(listItem{}()), concat{}(listConcat{}())]
  hooked-symbol dotList{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
  hooked-symbol listItem{}(SortKItem{}) : SortList{}
    [function{}(), total{}(), hook{}("LIST.element")]
  hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{}
    [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
  hooked-symbol makeList{}(SortInt{}, SortMInt{Sort64{}}) : SortList{}
    [function{}(), hook{}("LIST.make")]
endmodule []"#;

const A: &str = r#"\dv{SortMInt{Sort64{}}}("1p64")"#;
const B: &str = r#"\dv{SortMInt{Sort64{}}}("2p64")"#;

fn definition() -> BackendDefinition {
    let syntax = parse_definition(FIXTURE).expect("parametric element fixture should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("a collection over a closed parametric instance should load")
}

fn word() -> Sort {
    Sort::application("SortMInt", vec![Sort::simple("Sort64")])
}

fn simplified(definition: &BackendDefinition, source: &str) -> Term {
    let term = internal_term(definition, source);
    unstopped::simplify(definition, &term, SimplificationOptions::default())
        .expect("a concrete hooked application should simplify")
        .term
}

/// `hooked` and `expected` simplify to one term of one sort.
fn assert_same_value(definition: &BackendDefinition, hooked: &str, expected: &str) {
    let hooked_value = simplified(definition, hooked);
    let expected_value = simplified(definition, expected);
    assert_eq!(hooked_value, expected_value, "{hooked} against {expected}");
    assert_eq!(hooked_value.sort(), expected_value.sort(), "{hooked}");
}

fn words(elements: &[&str]) -> String {
    elements
        .iter()
        .fold("dotWords{}()".to_owned(), |list, element| {
            format!("wordsConcat{{}}({list}, wordItem{{}}({element}))")
        })
}

fn word_set(elements: &[&str]) -> String {
    elements
        .iter()
        .fold("dotWordSet{}()".to_owned(), |set, element| {
            format!("wordSetConcat{{}}({set}, wordSetItem{{}}({element}))")
        })
}

fn word_map(entries: &[(&str, &str)]) -> String {
    entries
        .iter()
        .fold("dotWordMap{}()".to_owned(), |map, (key, value)| {
            format!("wordMapConcat{{}}({map}, wordMapItem{{}}({key}, {value}))")
        })
}

fn int(value: u32) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// Each collection's description holds the closed instance as its element (key, value) sort.
#[test]
fn collections_over_a_closed_parametric_instance_hold_it_as_their_element_sort() {
    let definition = definition();
    let collection = |symbol: &str| {
        definition
            .symbols()
            .get(symbol)
            .and_then(|symbol| symbol.attributes.collection.clone())
            .unwrap_or_else(|| panic!("{symbol} should carry its collection"))
    };
    let CollectionMetadata::List(list) = collection("wordItem") else {
        panic!("wordItem should be a list element symbol");
    };
    assert_eq!(list.element_sort, word());
    let CollectionMetadata::Set(set) = collection("wordSetItem") else {
        panic!("wordSetItem should be a set element symbol");
    };
    assert_eq!(set.element_sort, word());
    let CollectionMetadata::Map(map) = collection("wordMapItem") else {
        panic!("wordMapItem should be a map element symbol");
    };
    assert_eq!(
        (map.key_sort.clone(), map.value_sort.clone()),
        (word(), word())
    );
}

/// The list hooks read and count the elements of a list over `MInt{64}`.
#[test]
fn list_hooks_compute_over_a_closed_parametric_element_sort() {
    let definition = definition();
    let list = words(&[A, B]);
    assert_same_value(&definition, &format!("wordsGet{{}}({list}, {})", int(1)), B);
    assert_same_value(&definition, &format!("wordsSize{{}}({list})"), &int(2));
}

/// The set hooks build a set over `MInt{64}` from a list and decide membership in it; a repeated
/// element is held once.
#[test]
fn set_hooks_compute_over_a_closed_parametric_element_sort() {
    let definition = definition();
    let set = word_set(&[A, B]);
    assert_same_value(
        &definition,
        &format!("wordsToSet{{}}({})", words(&[B, A, B])),
        &set,
    );
    assert_same_value(
        &definition,
        &format!("wordSetIn{{}}({A}, {})", word_set(&[A])),
        r#"\dv{SortBool{}}("true")"#,
    );
    assert_same_value(
        &definition,
        &format!("wordSetIn{{}}({B}, {})", word_set(&[A])),
        r#"\dv{SortBool{}}("false")"#,
    );
}

/// The map hooks look up a key of a map keyed by `MInt{64}` and give its keys as a set of the
/// same element sort.
#[test]
fn map_hooks_compute_over_closed_parametric_key_and_value_sorts() {
    let definition = definition();
    let map = word_map(&[(A, B), (B, A)]);
    assert_same_value(&definition, &format!("wordMapLookup{{}}({map}, {A})"), B);
    assert_same_value(
        &definition,
        &format!("wordMapKeys{{}}({map})"),
        &word_set(&[A, B]),
    );
}

/// A hook whose result collection has a wider element sort injects each `MInt{64}` element
/// along the declared subsort axiom.
#[test]
fn an_element_of_a_closed_parametric_instance_is_injected_into_a_wider_element_sort() {
    let definition = definition();
    let injected = format!("inj{{SortMInt{{Sort64{{}}}}, SortKItem{{}}}}({A})");
    assert_same_value(
        &definition,
        &format!("makeList{{}}({}, {A})", int(2)),
        &format!("listConcat{{}}(listItem{{}}({injected}), listItem{{}}({injected}))"),
    );
}

/// An element sort with a sort variable names no one sort: the collection sort has no parameters
/// to instantiate the variable with, so the declaration is refused where it is loaded.
#[test]
fn an_element_sort_with_a_sort_variable_is_refused_at_load() {
    let source = r#"[]
module MAIN
  sort Sort64{} []
  hooked-sort SortMInt{S} [hasDomainValues{}(), hook{}("MINT.MInt")]
  hooked-sort SortWords{}
    [hook{}("LIST.List"), unit{}(dotWords{}()), element{}(wordItem{}()), concat{}(wordsConcat{}())]
  hooked-symbol dotWords{}() : SortWords{} [function{}(), total{}(), hook{}("LIST.unit")]
  hooked-symbol wordItem{S}(SortMInt{S}) : SortWords{}
    [function{}(), total{}(), hook{}("LIST.element")]
  hooked-symbol wordsConcat{}(SortWords{}, SortWords{}) : SortWords{}
    [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
endmodule []"#;
    let syntax = parse_definition(source).expect("the definition should parse");
    let result = BackendDefinition::internalize(&syntax, "MAIN");
    let Err(DefinitionError::MalformedCollection(message)) = result else {
        panic!("an element sort with a sort variable must fail at load: {result:?}");
    };
    assert!(
        message.contains("wordItem") && message.contains("sort variable"),
        "{message}"
    );
}
