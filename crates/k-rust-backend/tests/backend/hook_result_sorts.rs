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
                        sample(definition, sort_name(&map.key_sort)),
                        sample(definition, sort_name(&map.value_sort)),
                    ],
                ),
                CollectionMetadata::List(list) | CollectionMetadata::Set(list) => (
                    list.symbols.clone(),
                    vec![sample(definition, sort_name(&list.element_sort))],
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
            .flat_map(|(key, value)| {
                [
                    (key, sort_name(&map.key_sort)),
                    (value, sort_name(&map.value_sort)),
                ]
            })
            .collect(),
        (CollectionMetadata::List(list), TermKind::List { heads, .. }) => heads
            .iter()
            .map(|head| (head, sort_name(&list.element_sort)))
            .collect(),
        (CollectionMetadata::Set(set), TermKind::Set { elements, .. }) => elements
            .iter()
            .map(|element| (element, sort_name(&set.element_sort)))
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

/// The fixture with `declarations` added to its module.
fn with_declarations(declarations: &str) -> String {
    FIXTURE.replacen("endmodule []", &format!("{declarations}\nendmodule []"), 1)
}

/// A hooked collection symbol under whose declaration the hook gives no value of its result
/// sort (an element, or the elements of a collection argument, not of the result's element sort
/// or a subsort of it; a result sort that is no collection of the hook's kind; an element
/// returned that is not of the result sort or a subsort of it) denotes nothing the hook computes,
/// so the definition is rejected where the symbol is declared, before anything is evaluated.
#[test]
fn a_collection_hook_whose_declaration_gives_no_value_of_its_result_sort_is_rejected_at_load() {
    let cases = [
        (
            "makeBad{}(SortInt{}, SortInt{}) : SortVals{} [function{}(), hook{}(\"LIST.make\")]",
            "argument 2 of LIST.make, of sort SortInt, is an element of the result, but SortInt \
             is not SortVal",
        ),
        (
            "makeSet{}(SortInt{}, SortVal{}) : SortValSet{} [function{}(), hook{}(\"LIST.make\")]",
            "LIST.make gives a list, but the result sort SortValSet is no list sort",
        ),
        (
            "makeInt{}(SortInt{}, SortKItem{}) : SortInt{} [function{}(), hook{}(\"LIST.make\")]",
            "LIST.make gives a list, but the result sort SortInt is no list sort",
        ),
        (
            "makeThree{}(SortInt{}, SortVal{}, SortVal{}) : SortVals{} \
             [function{}(), hook{}(\"LIST.make\")]",
            "LIST.make takes 2 arguments, the symbol 3",
        ),
        (
            "listIntoVals{}(SortList{}, SortList{}) : SortVals{} \
             [function{}(), hook{}(\"LIST.concat\")]",
            "an element of argument 1 of LIST.concat, of sort SortKItem, is an element of the \
             result, but SortKItem is not SortVal",
        ),
        (
            "mapIntoVals{}(SortValMap{}, SortVals{}) : SortVals{} \
             [function{}(), hook{}(\"LIST.concat\")]",
            "argument 1 of LIST.concat, of sort SortValMap, is no list sort",
        ),
        (
            "listToValSet{}(SortList{}) : SortValSet{} [function{}(), hook{}(\"SET.list2set\")]",
            "an element of argument 1 of SET.list2set, of sort SortKItem",
        ),
        (
            "keysToValSet{}(SortMap{}) : SortValSet{} [function{}(), hook{}(\"MAP.keys\")]",
            "a key of argument 1 of MAP.keys, of sort SortKItem",
        ),
        (
            "updateValMap{}(SortValMap{}, SortKItem{}, SortVal{}) : SortValMap{} \
             [function{}(), hook{}(\"MAP.update\")]",
            "argument 2 of MAP.update, of sort SortKItem, is a key of the result",
        ),
        (
            "getVal{}(SortList{}, SortInt{}) : SortVal{} [function{}(), hook{}(\"LIST.get\")]",
            "an element of argument 1 of LIST.get, of sort SortKItem, is the result, but \
             SortKItem is not SortVal",
        ),
        (
            "getOfInt{}(SortInt{}, SortInt{}) : SortKItem{} [function{}(), hook{}(\"LIST.get\")]",
            "argument 1 of LIST.get, of sort SortInt, is no list sort",
        ),
        (
            "lookupVal{}(SortMap{}, SortKItem{}) : SortVal{} [function{}(), hook{}(\"MAP.lookup\")]",
            "a value of argument 1 of MAP.lookup, of sort SortKItem, is the result",
        ),
        (
            "lookupOrItem{}(SortValMap{}, SortVal{}, SortKItem{}) : SortVal{} \
             [function{}(), hook{}(\"MAP.lookupOrDefault\")]",
            "argument 3 of MAP.lookupOrDefault, of sort SortKItem, is a possible result",
        ),
        (
            "choiceInt{}(SortMap{}) : SortInt{} [function{}(), hook{}(\"MAP.choice\")]",
            "a key of argument 1 of MAP.choice, of sort SortKItem, is the result, but SortKItem \
             is not SortInt",
        ),
        (
            "choiceOfInt{}(SortInt{}) : SortKItem{} [function{}(), hook{}(\"MAP.choice\")]",
            "argument 1 of MAP.choice, of sort SortInt, is no map sort",
        ),
        (
            "differenceIntoValMap{}(SortMap{}, SortMap{}) : SortValMap{} \
             [function{}(), total{}(), hook{}(\"MAP.difference\")]",
            "a key of argument 1 of MAP.difference, of sort SortKItem, is a key of the result, \
             but SortKItem is not SortVal",
        ),
        (
            "differenceIntoVals{}(SortValMap{}, SortValMap{}) : SortVals{} \
             [function{}(), total{}(), hook{}(\"MAP.difference\")]",
            "MAP.difference gives a map, but the result sort SortVals is no map sort",
        ),
        (
            "differenceOfInt{}(SortValMap{}, SortInt{}) : SortValMap{} \
             [function{}(), total{}(), hook{}(\"MAP.difference\")]",
            "argument 2 of MAP.difference, of sort SortInt, is no map sort",
        ),
        (
            "differenceOfValMap{}(SortValSet{}, SortValMap{}) : SortValSet{} \
             [function{}(), total{}(), hook{}(\"SET.difference\")]",
            "argument 2 of SET.difference, of sort SortValMap, is no set sort",
        ),
        (
            "intersectionOfVals{}(SortValSet{}, SortVals{}) : SortValSet{} \
             [function{}(), total{}(), hook{}(\"SET.intersection\")]",
            "argument 2 of SET.intersection, of sort SortVals, is no set sort",
        ),
        (
            "removeAllOfInt{}(SortValMap{}, SortInt{}) : SortValMap{} \
             [function{}(), total{}(), hook{}(\"MAP.removeAll\")]",
            "argument 2 of MAP.removeAll, of sort SortInt, is no set sort",
        ),
        (
            "removeAllOfValMap{}(SortValMap{}, SortValMap{}) : SortValMap{} \
             [function{}(), total{}(), hook{}(\"MAP.removeAll\")]",
            "argument 2 of MAP.removeAll, of sort SortValMap, is no set sort",
        ),
        (
            "removeAllOfVals{}(SortValMap{}, SortVals{}) : SortValMap{} \
             [function{}(), total{}(), hook{}(\"MAP.removeAll\")]",
            "argument 2 of MAP.removeAll, of sort SortVals, is no set sort",
        ),
        (
            "choiceVal{}(SortSet{}) : SortVal{} [function{}(), hook{}(\"SET.choice\")]",
            "an element of argument 1 of SET.choice, of sort SortKItem, is the result, but \
             SortKItem is not SortVal",
        ),
        // The hooks that read collections into a `Bool` or an `Int` read the items of their
        // collection arguments, which only a collection of the hook's kind has, and give a value
        // of `SortBool` or `SortInt`.
        (
            "inOfInt{}(SortVal{}, SortInt{}) : SortBool{} \
             [function{}(), total{}(), hook{}(\"LIST.in\")]",
            "argument 2 of LIST.in, of sort SortInt, is no list sort",
        ),
        (
            "inValsAsInt{}(SortVal{}, SortVals{}) : SortInt{} \
             [function{}(), total{}(), hook{}(\"LIST.in\")]",
            "LIST.in gives a value of sort SortBool, but the result sort SortInt is not SortBool \
             or a sort above it",
        ),
        (
            "sizeOfValSet{}(SortValSet{}) : SortInt{} \
             [function{}(), total{}(), hook{}(\"LIST.size\")]",
            "argument 1 of LIST.size, of sort SortValSet, is no list sort",
        ),
        (
            "sizeValsAsBool{}(SortVals{}) : SortBool{} \
             [function{}(), total{}(), hook{}(\"LIST.size\")]",
            "LIST.size gives a value of sort SortInt, but the result sort SortBool is not SortInt \
             or a sort above it",
        ),
        (
            "inValSetOfVals{}(SortVal{}, SortVals{}) : SortBool{} \
             [function{}(), total{}(), hook{}(\"SET.in\")]",
            "argument 2 of SET.in, of sort SortVals, is no set sort",
        ),
        (
            "sizeSetOfValMap{}(SortValMap{}) : SortInt{} \
             [function{}(), total{}(), hook{}(\"SET.size\")]",
            "argument 1 of SET.size, of sort SortValMap, is no set sort",
        ),
        (
            "inclusionOfVals{}(SortValSet{}, SortVals{}) : SortBool{} \
             [function{}(), total{}(), hook{}(\"SET.inclusion\")]",
            "argument 2 of SET.inclusion, of sort SortVals, is no set sort",
        ),
        (
            "inclusionValSetAsVal{}(SortValSet{}, SortValSet{}) : SortVal{} \
             [function{}(), total{}(), hook{}(\"SET.inclusion\")]",
            "SET.inclusion gives a value of sort SortBool, but the result sort SortVal is not \
             SortBool or a sort above it",
        ),
        (
            "inKeysOfValSet{}(SortVal{}, SortValSet{}) : SortBool{} \
             [function{}(), total{}(), hook{}(\"MAP.in_keys\")]",
            "argument 2 of MAP.in_keys, of sort SortValSet, is no map sort",
        ),
        (
            "sizeMapOfInt{}(SortInt{}) : SortInt{} [function{}(), total{}(), hook{}(\"MAP.size\")]",
            "argument 1 of MAP.size, of sort SortInt, is no map sort",
        ),
        (
            "sizeValMapAsVal{}(SortValMap{}) : SortVal{} \
             [function{}(), total{}(), hook{}(\"MAP.size\")]",
            "MAP.size gives a value of sort SortInt, but the result sort SortVal is not SortInt \
             or a sort above it",
        ),
        (
            "inclusionOfValSetMap{}(SortValMap{}, SortValSet{}) : SortBool{} \
             [function{}(), total{}(), hook{}(\"MAP.inclusion\")]",
            "argument 2 of MAP.inclusion, of sort SortValSet, is no map sort",
        ),
        (
            "inclusionThreeMaps{}(SortValMap{}, SortValMap{}, SortValMap{}) : SortBool{} \
             [function{}(), total{}(), hook{}(\"MAP.inclusion\")]",
            "MAP.inclusion takes 2 arguments, the symbol 3",
        ),
    ];
    let unexpected = cases
        .iter()
        .filter_map(|(declaration, reason)| {
            let source = with_declarations(&format!("  hooked-symbol {declaration}"));
            let syntax = parse_definition(&source).expect("the declaration should parse");
            match BackendDefinition::internalize(&syntax, "MAIN") {
                Err(error) => {
                    let message = error.to_string();
                    (!message.contains("Malformed collection hook") || !message.contains(reason))
                        .then(|| format!("{declaration}: {message}"))
                }
                Ok(_) => Some(format!("{declaration}: loaded")),
            }
        })
        .collect::<Vec<_>>();
    assert!(
        unexpected.is_empty(),
        "an ill-fitting collection hook declaration was not rejected as expected:\n{}",
        unexpected.join("\n")
    );
}

/// The hooks that read collections into a `Bool` or an `Int` load where each collection argument
/// is a collection of the hook's kind, of any element sort, and the result is `SortBool` or
/// `SortInt`; the sort of the item whose membership is tested is not checked (an `Int` is no
/// `Val`, so it is in no set of `Val`). Their applications evaluate.
#[test]
fn a_collection_reading_hook_declared_on_collections_of_its_kind_loads_and_evaluates() {
    let source = with_declarations(
        r#"  hooked-symbol inVals{}(SortVal{}, SortVals{}) : SortBool{}
    [function{}(), total{}(), hook{}("LIST.in")]
  hooked-symbol inList{}(SortKItem{}, SortList{}) : SortBool{}
    [function{}(), total{}(), hook{}("LIST.in")]
  hooked-symbol sizeVals{}(SortVals{}) : SortInt{} [function{}(), total{}(), hook{}("LIST.size")]
  hooked-symbol inValSet{}(SortVal{}, SortValSet{}) : SortBool{}
    [function{}(), total{}(), hook{}("SET.in")]
  hooked-symbol inSetOfInt{}(SortInt{}, SortValSet{}) : SortBool{}
    [function{}(), total{}(), hook{}("SET.in")]
  hooked-symbol sizeValSet{}(SortValSet{}) : SortInt{}
    [function{}(), total{}(), hook{}("SET.size")]
  hooked-symbol inclusionValSet{}(SortValSet{}, SortValSet{}) : SortBool{}
    [function{}(), total{}(), hook{}("SET.inclusion")]
  hooked-symbol inKeysValMap{}(SortVal{}, SortValMap{}) : SortBool{}
    [function{}(), total{}(), hook{}("MAP.in_keys")]
  hooked-symbol sizeValMap{}(SortValMap{}) : SortInt{}
    [function{}(), total{}(), hook{}("MAP.size")]
  hooked-symbol inclusionValMap{}(SortValMap{}, SortValMap{}) : SortBool{}
    [function{}(), total{}(), hook{}("MAP.inclusion")]"#,
    );
    let syntax = parse_definition(&source).expect("the declarations should parse");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("the declarations should load");
    for (application, expected) in [
        (
            "inVals{}(v{}(), valsItem{}(v{}()))",
            r#"\dv{SortBool{}}("true")"#,
        ),
        ("sizeVals{}(valsItem{}(w{}()))", r#"\dv{SortInt{}}("1")"#),
        (
            "inValSet{}(w{}(), valSetItem{}(v{}()))",
            r#"\dv{SortBool{}}("false")"#,
        ),
        (
            "sizeValSet{}(valSetItem{}(v{}()))",
            r#"\dv{SortInt{}}("1")"#,
        ),
        (
            "inclusionValSet{}(dotValSet{}(), valSetItem{}(v{}()))",
            r#"\dv{SortBool{}}("true")"#,
        ),
        (
            "inKeysValMap{}(v{}(), valMapItem{}(v{}(), w{}()))",
            r#"\dv{SortBool{}}("true")"#,
        ),
        (
            "sizeValMap{}(valMapItem{}(v{}(), w{}()))",
            r#"\dv{SortInt{}}("1")"#,
        ),
        (
            "inclusionValMap{}(valMapItem{}(v{}(), w{}()), dotValMap{}())",
            r#"\dv{SortBool{}}("false")"#,
        ),
    ] {
        assert_eq!(
            simplified(&definition, application),
            simplified(&definition, expected),
            "{application}"
        );
    }
}

/// The rejection names where the symbol is written.
#[test]
fn an_ill_fitting_collection_hook_is_rejected_at_its_written_position() {
    let source = with_declarations(
        "  hooked-symbol makeBad{}(SortInt{}, SortInt{}) : SortVals{}\n    [function{}(), \
         hook{}(\"LIST.make\"),\n     org'Stop'kframework'Stop'attributes'Stop'Location{}(\"\
         Location(12,3,12,60)\"),\n     org'Stop'kframework'Stop'attributes'Stop'Source{}(\"\
         Source(/defs/vals.k)\")]",
    );
    let syntax = parse_definition(&source).expect("the declaration should parse");
    let Err(error) = BackendDefinition::internalize(&syntax, "MAIN") else {
        panic!("makeBad should be rejected at load");
    };
    let message = error.to_string();
    assert!(
        message.starts_with(
            "/defs/vals.k:12:3: Malformed collection hook: the hooked symbol \
                             makeBad denotes no value of its result sort:"
        ),
        "{message}"
    );
}

/// A hook that gives one element of a collection argument (`LIST.get`, `MAP.lookup`, or the
/// default of `MAP.lookupOrDefault`) gives a value of the symbol's result sort: the element
/// itself when its sort is that sort, its injection when it is a strict subsort.
#[test]
fn an_element_returning_hook_gives_a_value_of_its_result_sort() {
    let source = with_declarations(
        r#"  hooked-symbol getVal{}(SortVals{}, SortInt{}) : SortVal{} [function{}(), hook{}("LIST.get")]
  hooked-symbol getItem{}(SortVals{}, SortInt{}) : SortKItem{} [function{}(), hook{}("LIST.get")]
  hooked-symbol lookupItem{}(SortValMap{}, SortVal{}) : SortKItem{} [function{}(), hook{}("MAP.lookup")]
  hooked-symbol lookupOrItem{}(SortValMap{}, SortVal{}, SortVal{}) : SortKItem{}
    [function{}(), total{}(), hook{}("MAP.lookupOrDefault")]"#,
    );
    let syntax = parse_definition(&source).expect("the declarations should parse");
    let definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("element-returning hooks into the element sort or a supersort should load");
    let item = "inj{SortVal{}, SortKItem{}}(w{}())";
    let vals = "valsConcat{}(valsItem{}(v{}()), valsItem{}(w{}()))";
    let map = "valMapItem{}(v{}(), w{}())";
    let pairs = [
        (
            format!(r#"getVal{{}}({vals}, \dv{{SortInt{{}}}}("1"))"#),
            "w{}()".to_owned(),
        ),
        (
            format!(r#"getItem{{}}({vals}, \dv{{SortInt{{}}}}("1"))"#),
            item.to_owned(),
        ),
        (format!("lookupItem{{}}({map}, v{{}}())"), item.to_owned()),
        (
            format!("lookupOrItem{{}}({map}, w{{}}(), w{{}}())"),
            item.to_owned(),
        ),
        (
            format!("lookupOrItem{{}}({map}, v{{}}(), v{{}}())"),
            item.to_owned(),
        ),
    ];
    let differing = pairs
        .iter()
        .filter_map(|(hooked, expected)| {
            let value = simplified(&definition, hooked);
            let expected = internal_term(&definition, expected);
            (value != expected).then(|| format!("{hooked}: {value:?}"))
        })
        .collect::<Vec<_>>();
    assert!(
        differing.is_empty(),
        "an element-returning hook gave another value than its result sort's:\n{}",
        differing.join("\n")
    );
}

/// `choice` of a map gives a key and `choice` of a set an element, as a value of the symbol's
/// result sort: the key (element) itself when its sort is that sort, its injection when it is a
/// strict subsort. `choice` is declared at `KItem` in `domains.md`, above every key sort.
#[test]
fn choice_gives_its_one_key_or_element_as_a_value_of_its_result_sort() {
    let source = with_declarations(
        r#"  axiom{R} \exists{R}(Value:SortKItem{},
      \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortInt{}, SortKItem{}}(From:SortInt{})))
      [subsort{SortInt{}, SortKItem{}}()]
  hooked-sort SortIntMap{}
    [hook{}("MAP.Map"), unit{}(dotIntMap{}()), element{}(intMapItem{}()),
     concat{}(intMapConcat{}())]
  hooked-symbol dotIntMap{}() : SortIntMap{} [function{}(), total{}(), hook{}("MAP.unit")]
  hooked-symbol intMapItem{}(SortInt{}, SortVal{}) : SortIntMap{}
    [function{}(), total{}(), hook{}("MAP.element")]
  hooked-symbol intMapConcat{}(SortIntMap{}, SortIntMap{}) : SortIntMap{}
    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
  hooked-symbol choiceIntMap{}(SortIntMap{}) : SortKItem{} [function{}(), hook{}("MAP.choice")]
  hooked-symbol choiceValSet{}(SortValSet{}) : SortKItem{} [function{}(), hook{}("SET.choice")]
  hooked-symbol choiceValSetVal{}(SortValSet{}) : SortVal{} [function{}(), hook{}("SET.choice")]"#,
    );
    let syntax = parse_definition(&source).expect("the declarations should parse");
    let definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("choice into the key or element sort or a supersort should load");
    let pairs = [
        (
            r#"choiceIntMap{}(intMapItem{}(\dv{SortInt{}}("5"), v{}()))"#,
            r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("5"))"#,
        ),
        (
            "choiceValSet{}(valSetItem{}(w{}()))",
            "inj{SortVal{}, SortKItem{}}(w{}())",
        ),
        ("choiceValSetVal{}(valSetItem{}(w{}()))", "w{}()"),
    ];
    let differing = pairs
        .iter()
        .filter_map(|(hooked, expected)| {
            let value = simplified(&definition, hooked);
            let expected = internal_term(&definition, expected);
            (value != expected).then(|| format!("{hooked}: {value:?}"))
        })
        .collect::<Vec<_>>();
    assert!(
        differing.is_empty(),
        "choice gave another value than its result sort's:\n{}",
        differing.join("\n")
    );
}

/// `-Map` declared on a user map sort builds its result in that sort, and declared from a map of
/// `Val` into the builtin `KItem` map, in that map with the kept bindings injected. A binding the
/// other map holds with the same value is removed, and one it holds with another value is kept.
#[test]
fn map_difference_builds_the_value_of_its_declared_map_sort() {
    let source = with_declarations(
        r#"  hooked-symbol differenceValMap{}(SortValMap{}, SortValMap{}) : SortValMap{}
    [function{}(), total{}(), hook{}("MAP.difference")]
  hooked-symbol differenceValMapIntoMap{}(SortValMap{}, SortValMap{}) : SortMap{}
    [function{}(), total{}(), hook{}("MAP.difference")]"#,
    );
    let syntax = parse_definition(&source).expect("the declarations should parse");
    let definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("a difference into a map of the bindings' sorts or wider ones should load");
    let two = "valMapConcat{}(valMapItem{}(v{}(), w{}()), valMapItem{}(w{}(), w{}()))";
    let inj = |term: &str| format!("inj{{SortVal{{}}, SortKItem{{}}}}({term})");
    let pairs = [
        (
            format!("differenceValMap{{}}({two}, valMapItem{{}}(v{{}}(), w{{}}()))"),
            "valMapItem{}(w{}(), w{}())".to_owned(),
        ),
        (
            format!("differenceValMap{{}}({two}, valMapItem{{}}(v{{}}(), v{{}}()))"),
            two.to_owned(),
        ),
        (
            format!("differenceValMap{{}}({two}, {two})"),
            "dotValMap{}()".to_owned(),
        ),
        (
            format!("differenceValMapIntoMap{{}}({two}, valMapItem{{}}(v{{}}(), w{{}}()))"),
            format!(
                "Lbl'UndsPipe'-'-GT-Unds'{{}}({}, {})",
                inj("w{}()"),
                inj("w{}()")
            ),
        ),
        (
            format!("differenceValMapIntoMap{{}}({two}, dotValMap{{}}())"),
            format!(
                "Lbl'Unds'Map'Unds'{{}}(Lbl'UndsPipe'-'-GT-Unds'{{}}({}, {}), \
                 Lbl'UndsPipe'-'-GT-Unds'{{}}({}, {}))",
                inj("v{}()"),
                inj("w{}()"),
                inj("w{}()"),
                inj("w{}()")
            ),
        ),
    ];
    let differing = pairs
        .iter()
        .filter_map(|(hooked, expected)| {
            let value = simplified(&definition, hooked);
            let expected = simplified(&definition, expected);
            (value != expected || value.sort() != expected.sort()).then(|| {
                format!(
                    "{hooked} => {value:?} of {}, expected {}",
                    sort_name(&value.sort()),
                    sort_name(&expected.sort())
                )
            })
        })
        .collect::<Vec<_>>();
    assert!(
        differing.is_empty(),
        "-Map gave another value than its declared map sort's:\n{}",
        differing.join("\n")
    );
}
