//! A hooked function returns a value of its declared result sort.
//!
//! A collection sort (`hook(LIST.List)`, `hook(SET.Set)`, `hook(MAP.Map)`) names its own unit,
//! element and concatenation symbols, and a value of that sort is built from those symbols. A
//! hooked symbol whose result sort is such a sort denotes a value of that sort, whatever hook
//! computes it, so its evaluation must carry that sort: evaluation never changes the sort of the
//! term it evaluates. The second check is the same fact seen from the values: two spellings of
//! one collection value (a hook application and the value written with the sort's own
//! constructors) simplify to the same term.
//!
//! The fixture declares the builtin-named `SortList`, `SortSet` and `SortMap` next to user list,
//! set and map sorts with their own symbols, and hooked symbols into each of them whose arguments
//! are not of that collection sort (the hooks that introduce a collection value instead of
//! transforming one).
//!
//! A value of a collection sort holds elements of that sort's element sort, so a hook whose
//! result collection has a wider element sort than its element argument or argument collection
//! (`Val` into the builtin `KItem` collections) injects each element: the fixture's last three
//! hooked symbols are that case.

use k_rust_backend::{
    definition::BackendDefinition,
    simplify::SimplificationOptions,
    term::{CollectionMetadata, Sort, Term, TermKind},
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::{internal_term, unstopped};

const FIXTURE: &str = r#"[]
module MAIN
  sort SortK{} []
  sort SortKItem{} []
  sort SortVal{} []
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
  symbol inj{From, To}(From) : To [sortInjection{}()]
  symbol v{}() : SortVal{} [constructor{}(), functional{}(), injective{}(), total{}()]
  symbol w{}() : SortVal{} [constructor{}(), functional{}(), injective{}(), total{}()]
  axiom{R} \exists{R}(Value:SortKItem{},
      \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortVal{}, SortKItem{}}(From:SortVal{})))
      [subsort{SortVal{}, SortKItem{}}()]

  hooked-sort SortList{}
    [hook{}("LIST.List"), unit{}(Lbl'Stop'List{}()), element{}(LblListItem{}()),
     concat{}(Lbl'Unds'List'Unds'{}())]
  hooked-symbol Lbl'Stop'List{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
  hooked-symbol LblListItem{}(SortKItem{}) : SortList{}
    [function{}(), total{}(), hook{}("LIST.element")]
  hooked-symbol Lbl'Unds'List'Unds'{}(SortList{}, SortList{}) : SortList{}
    [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]

  hooked-sort SortSet{}
    [hook{}("SET.Set"), unit{}(Lbl'Stop'Set{}()), element{}(LblSetItem{}()),
     concat{}(Lbl'Unds'Set'Unds'{}())]
  hooked-symbol Lbl'Stop'Set{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
  hooked-symbol LblSetItem{}(SortKItem{}) : SortSet{}
    [function{}(), total{}(), hook{}("SET.element")]
  hooked-symbol Lbl'Unds'Set'Unds'{}(SortSet{}, SortSet{}) : SortSet{}
    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]

  hooked-sort SortMap{}
    [hook{}("MAP.Map"), unit{}(Lbl'Stop'Map{}()), element{}(Lbl'UndsPipe'-'-GT-Unds'{}()),
     concat{}(Lbl'Unds'Map'Unds'{}())]
  hooked-symbol Lbl'Stop'Map{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
  hooked-symbol Lbl'UndsPipe'-'-GT-Unds'{}(SortKItem{}, SortKItem{}) : SortMap{}
    [function{}(), total{}(), hook{}("MAP.element")]
  hooked-symbol Lbl'Unds'Map'Unds'{}(SortMap{}, SortMap{}) : SortMap{}
    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]

  hooked-sort SortVals{}
    [hook{}("LIST.List"), unit{}(dotVals{}()), element{}(valsItem{}()), concat{}(valsConcat{}())]
  hooked-symbol dotVals{}() : SortVals{} [function{}(), total{}(), hook{}("LIST.unit")]
  hooked-symbol valsItem{}(SortVal{}) : SortVals{} [function{}(), total{}(), hook{}("LIST.element")]
  hooked-symbol valsConcat{}(SortVals{}, SortVals{}) : SortVals{}
    [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]

  hooked-sort SortValSet{}
    [hook{}("SET.Set"), unit{}(dotValSet{}()), element{}(valSetItem{}()),
     concat{}(valSetConcat{}())]
  hooked-symbol dotValSet{}() : SortValSet{} [function{}(), total{}(), hook{}("SET.unit")]
  hooked-symbol valSetItem{}(SortVal{}) : SortValSet{}
    [function{}(), total{}(), hook{}("SET.element")]
  hooked-symbol valSetConcat{}(SortValSet{}, SortValSet{}) : SortValSet{}
    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]

  hooked-sort SortValMap{}
    [hook{}("MAP.Map"), unit{}(dotValMap{}()), element{}(valMapItem{}()),
     concat{}(valMapConcat{}())]
  hooked-symbol dotValMap{}() : SortValMap{} [function{}(), total{}(), hook{}("MAP.unit")]
  hooked-symbol valMapItem{}(SortVal{}, SortVal{}) : SortValMap{}
    [function{}(), total{}(), hook{}("MAP.element")]
  hooked-symbol valMapConcat{}(SortValMap{}, SortValMap{}) : SortValMap{}
    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]

  hooked-symbol makeList{}(SortInt{}, SortKItem{}) : SortList{}
    [function{}(), hook{}("LIST.make")]
  hooked-symbol makeVals{}(SortInt{}, SortVal{}) : SortVals{} [function{}(), hook{}("LIST.make")]
  hooked-symbol singletonVals{}(SortVal{}) : SortVals{}
    [function{}(), total{}(), hook{}("LIST.element")]
  hooked-symbol emptyVals{}() : SortVals{} [function{}(), total{}(), hook{}("LIST.unit")]
  hooked-symbol singletonValSet{}(SortVal{}) : SortValSet{}
    [function{}(), total{}(), hook{}("SET.element")]
  hooked-symbol emptyValSet{}() : SortValSet{} [function{}(), total{}(), hook{}("SET.unit")]
  hooked-symbol valsToSet{}(SortVals{}) : SortValSet{}
    [function{}(), total{}(), hook{}("SET.list2set")]
  hooked-symbol setToVals{}(SortValSet{}) : SortVals{}
    [function{}(), total{}(), hook{}("SET.set2list")]
  hooked-symbol singletonValMap{}(SortVal{}, SortVal{}) : SortValMap{}
    [function{}(), total{}(), hook{}("MAP.element")]
  hooked-symbol emptyValMap{}() : SortValMap{} [function{}(), total{}(), hook{}("MAP.unit")]
  hooked-symbol keysValMap{}(SortValMap{}) : SortValSet{} [function{}(), total{}(), hook{}("MAP.keys")]
  hooked-symbol keysListValMap{}(SortValMap{}) : SortVals{}
    [function{}(), total{}(), hook{}("MAP.keys_list")]
  hooked-symbol valuesValMap{}(SortValMap{}) : SortVals{}
    [function{}(), total{}(), hook{}("MAP.values")]

  hooked-symbol makeListOfVal{}(SortInt{}, SortVal{}) : SortList{}
    [function{}(), hook{}("LIST.make")]
  hooked-symbol keysValMapToSet{}(SortValMap{}) : SortSet{}
    [function{}(), total{}(), hook{}("MAP.keys")]
  hooked-symbol valsToKSet{}(SortVals{}) : SortSet{}
    [function{}(), total{}(), hook{}("SET.list2set")]
endmodule []"#;

fn definition() -> BackendDefinition {
    let syntax = parse_definition(FIXTURE).expect("hook result sort fixture should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("hook result sort fixture should internalize")
}

fn sort_name(sort: &Sort) -> &str {
    match sort {
        Sort::Application { name, arguments } if arguments.is_empty() => name,
        _ => panic!("the fixture declares only simple sorts, found {sort:?}"),
    }
}

/// The collection sort named `sort`, if the fixture declares one.
fn collection_of(definition: &BackendDefinition, sort: &str) -> Option<CollectionMetadata> {
    definition
        .symbols()
        .values()
        .filter_map(|symbol| symbol.attributes.collection.clone())
        .find(|collection| match collection {
            CollectionMetadata::Map(map) => &*map.map_sort == sort,
            CollectionMetadata::List(list) | CollectionMetadata::Set(list) => {
                &*list.list_sort == sort
            }
        })
}

/// A concrete KORE pattern of `sort`: `v` for an element, `2` for an integer, and for a
/// collection sort the value written with that sort's own element symbol.
fn sample(definition: &BackendDefinition, sort: &str) -> String {
    match sort {
        "SortVal" => "v{}()".into(),
        "SortKItem" => "inj{SortVal{}, SortKItem{}}(v{}())".into(),
        "SortInt" => r#"\dv{SortInt{}}("2")"#.into(),
        _ => {
            let (symbols, arguments) = match collection_of(definition, sort)
                .unwrap_or_else(|| panic!("no sample of {sort} in the fixture"))
            {
                CollectionMetadata::Map(map) => (
                    map.symbols.clone(),
                    vec![
                        sample(definition, &map.key_sort),
                        sample(definition, &map.value_sort),
                    ],
                ),
                CollectionMetadata::List(list) | CollectionMetadata::Set(list) => (
                    list.symbols.clone(),
                    vec![sample(definition, &list.element_sort)],
                ),
            };
            format!("{}{{}}({})", symbols.element, arguments.join(", "))
        }
    }
}

/// The sorts of the elements (keys and values for a map) of the collection value `value` that
/// are not the element sorts `collection` declares.
fn misplaced_elements(collection: &CollectionMetadata, value: &Term) -> Vec<String> {
    let elements: Vec<(&Term, &str)> = match (collection, value.kind()) {
        (CollectionMetadata::Map(map), TermKind::Map { entries, .. }) => entries
            .iter()
            .flat_map(|(key, value)| [(key, &*map.key_sort), (value, &*map.value_sort)])
            .collect(),
        (CollectionMetadata::List(list), TermKind::List { heads, .. }) => heads
            .iter()
            .map(|head| (head, &*list.element_sort))
            .collect(),
        (CollectionMetadata::Set(set), TermKind::Set { elements, .. }) => elements
            .iter()
            .map(|element| (element, &*set.element_sort))
            .collect(),
        _ => {
            return vec![format!(
                "not a collection value of the declared kind: {value:?}"
            )];
        }
    };
    elements
        .into_iter()
        .filter_map(|(element, declared)| {
            let actual = element.sort();
            (sort_name(&actual) != declared)
                .then(|| format!("{} where {declared} is declared", sort_name(&actual)))
        })
        .collect()
}

fn simplified(definition: &BackendDefinition, source: &str) -> Term {
    let term = internal_term(definition, source);
    unstopped::simplify(definition, &term, SimplificationOptions::default())
        .expect("a concrete hooked application should simplify")
        .term
}

/// Every hooked symbol of the fixture whose result sort is a collection sort, other than that
/// sort's own unit, element and concatenation, applied to concrete arguments, evaluates to a
/// value of its result sort.
#[test]
fn hooked_collection_results_keep_the_declared_result_sort() {
    let definition = definition();
    let mut checked = Vec::new();
    let mut wrong = Vec::new();
    for symbol in definition.symbols().values() {
        if symbol.attributes.hook.is_none() {
            continue;
        }
        let result_sort = sort_name(&symbol.result_sort);
        if symbol.attributes.collection.is_some()
            || collection_of(&definition, result_sort).is_none()
        {
            continue;
        }
        let arguments = symbol
            .argument_sorts
            .iter()
            .map(|sort| sample(&definition, sort_name(sort)))
            .collect::<Vec<_>>();
        let source = format!("{}{{}}({})", symbol.name, arguments.join(", "));
        let result = simplified(&definition, &source);
        // Only an evaluated application says something; an unevaluated one keeps its sort.
        if matches!(
            result.kind(),
            TermKind::Application { symbol: head, .. } if head.name == symbol.name
        ) {
            continue;
        }
        checked.push(symbol.name.clone());
        if result.sort() != symbol.result_sort {
            wrong.push(format!(
                "{source}: declared {}, evaluated to a value of {}",
                result_sort,
                sort_name(&result.sort())
            ));
            continue;
        }
        // A value of a collection sort holds elements of the sort's element sorts.
        let declared = collection_of(&definition, result_sort).expect("a collection sort");
        let misplaced = misplaced_elements(&declared, &result);
        if !misplaced.is_empty() {
            wrong.push(format!(
                "{source}: a value of {result_sort} holds elements of other sorts: {misplaced:?}"
            ));
        }
    }
    // The fixture declares 16 such symbols; each must have been evaluated for the check to say
    // anything about its hook.
    assert_eq!(
        checked.len(),
        16,
        "every hooked collection symbol of the fixture should evaluate, evaluated: {checked:?}"
    );
    assert!(
        wrong.is_empty(),
        "a hooked symbol evaluated to a value of another sort than it declares:\n{}",
        wrong.join("\n")
    );
}

/// A hook application and the same value written with the result sort's own symbols are two
/// spellings of one value, so they simplify to one term.
#[test]
fn a_hooked_collection_value_equals_its_constructor_spelling() {
    let definition = definition();
    let pairs = [
        (
            r#"makeVals{}(\dv{SortInt{}}("3"), v{}())"#,
            "valsConcat{}(valsItem{}(v{}()), valsConcat{}(valsItem{}(v{}()), valsItem{}(v{}())))",
        ),
        (
            r#"makeList{}(\dv{SortInt{}}("2"), inj{SortVal{}, SortKItem{}}(v{}()))"#,
            "Lbl'Unds'List'Unds'{}(LblListItem{}(inj{SortVal{}, SortKItem{}}(v{}())), \
             LblListItem{}(inj{SortVal{}, SortKItem{}}(v{}())))",
        ),
        ("singletonVals{}(v{}())", "valsItem{}(v{}())"),
        ("emptyVals{}()", "dotVals{}()"),
        ("singletonValSet{}(v{}())", "valSetItem{}(v{}())"),
        ("emptyValSet{}()", "dotValSet{}()"),
        ("valsToSet{}(valsItem{}(v{}()))", "valSetItem{}(v{}())"),
        ("setToVals{}(valSetItem{}(v{}()))", "valsItem{}(v{}())"),
        (
            "singletonValMap{}(v{}(), w{}())",
            "valMapItem{}(v{}(), w{}())",
        ),
        ("emptyValMap{}()", "dotValMap{}()"),
        (
            "keysValMap{}(valMapItem{}(v{}(), w{}()))",
            "valSetItem{}(v{}())",
        ),
        (
            "keysListValMap{}(valMapItem{}(v{}(), w{}()))",
            "valsItem{}(v{}())",
        ),
        (
            "valuesValMap{}(valMapItem{}(v{}(), w{}()))",
            "valsItem{}(w{}())",
        ),
    ];
    let differing = pairs
        .iter()
        .filter_map(|(hooked, written)| {
            let hooked_value = simplified(&definition, hooked);
            let written_value = simplified(&definition, written);
            (hooked_value != written_value).then(|| {
                format!(
                    "{hooked} => {}\n  {written} => {}",
                    sort_name(&hooked_value.sort()),
                    sort_name(&written_value.sort())
                )
            })
        })
        .collect::<Vec<_>>();
    assert!(
        differing.is_empty(),
        "two spellings of one collection value simplified apart (shown by sort):\n{}",
        differing.join("\n")
    );
}

/// A hook whose result collection has a wider element sort than its source (`Val` into the
/// builtin `KItem` collections) builds the value whose elements are the source's, injected: the
/// set of a `ValMap`'s keys, as a `Set`, is the set of those keys as `KItem`s.
#[test]
fn a_collection_hook_injects_elements_into_its_result_element_sort() {
    let definition = definition();
    let item = "inj{SortVal{}, SortKItem{}}(v{}())";
    let pairs = [
        (
            r#"makeListOfVal{}(\dv{SortInt{}}("2"), v{}())"#.to_owned(),
            format!("Lbl'Unds'List'Unds'{{}}(LblListItem{{}}({item}), LblListItem{{}}({item}))"),
        ),
        (
            "keysValMapToSet{}(valMapItem{}(v{}(), w{}()))".to_owned(),
            format!("LblSetItem{{}}({item})"),
        ),
        (
            "valsToKSet{}(valsItem{}(v{}()))".to_owned(),
            format!("LblSetItem{{}}({item})"),
        ),
    ];
    let differing = pairs
        .iter()
        .filter_map(|(hooked, written)| {
            let hooked_value = simplified(&definition, hooked);
            let written_value = simplified(&definition, written);
            (hooked_value != written_value).then(|| {
                let declared = collection_of(&definition, sort_name(&hooked_value.sort()))
                    .expect("a collection value");
                format!(
                    "{hooked}: {:?}",
                    misplaced_elements(&declared, &hooked_value)
                )
            })
        })
        .collect::<Vec<_>>();
    assert!(
        differing.is_empty(),
        "a hook built a collection whose elements are not of its element sort:\n{}",
        differing.join("\n")
    );
}
