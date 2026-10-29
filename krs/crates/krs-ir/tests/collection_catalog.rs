//! Map, List, and Set operation catalog facts that the facade, compiler, and adapter share.

use krs_ir::{
    BuiltinSort, CollectionApplication, FacadeMarker, ListOperation, MapOperation, SetOperation,
    TermMapOperation,
};

fn marker(module: &'static str, name: &'static str) -> FacadeMarker {
    FacadeMarker { module, name }
}

#[test]
fn term_map_operations_are_the_map_operations_with_facade_markers() {
    assert_eq!(
        MapOperation::ALL,
        [
            MapOperation::Item,
            MapOperation::Empty,
            MapOperation::Update,
            MapOperation::Get,
            MapOperation::InKeys,
            MapOperation::Remove,
            MapOperation::RemoveAll,
            MapOperation::Keys,
            MapOperation::KeysList,
            MapOperation::Values,
            MapOperation::Size,
            MapOperation::UpdateAll,
            MapOperation::GetOrDefault,
        ]
    );
    assert_eq!(
        TermMapOperation::ALL,
        [
            TermMapOperation::Empty,
            TermMapOperation::Update,
            TermMapOperation::Get,
            TermMapOperation::InKeys,
            TermMapOperation::Remove,
            TermMapOperation::RemoveAll,
            TermMapOperation::Keys,
            TermMapOperation::KeysList,
            TermMapOperation::Values,
            TermMapOperation::Size,
            TermMapOperation::UpdateAll,
            TermMapOperation::GetOrDefault,
        ]
    );
    for operation in MapOperation::ALL {
        let term = TermMapOperation::try_from(operation);
        assert_eq!(term.is_ok(), operation != MapOperation::Item, "{operation}");
        if let Ok(term) = term {
            assert_eq!(MapOperation::from(term), operation);
            assert_eq!(term.spec(), operation.spec());
        }
    }
}

#[test]
fn list_and_set_catalogs_list_every_operation_as_an_application_head() {
    assert_eq!(
        ListOperation::ALL,
        [
            ListOperation::Empty,
            ListOperation::Item,
            ListOperation::Concat,
            ListOperation::Get,
            ListOperation::Update,
            ListOperation::Size,
            ListOperation::Make,
            ListOperation::Range,
            ListOperation::UpdateAll,
            ListOperation::Contains,
        ]
    );
    assert_eq!(
        SetOperation::ALL,
        [
            SetOperation::Empty,
            SetOperation::Item,
            SetOperation::Concat,
            SetOperation::Union,
            SetOperation::Contains,
            SetOperation::Difference,
            SetOperation::Intersect,
            SetOperation::Size,
            SetOperation::IsSubset,
            SetOperation::ToList,
            SetOperation::FromList,
        ]
    );
}

#[test]
fn facade_markers_name_the_builtin_marker_types() {
    assert_eq!(
        TermMapOperation::ALL.map(TermMapOperation::facade_marker),
        [
            marker("map", "empty"),
            marker("map", "update"),
            marker("map", "get"),
            marker("map", "in_keys"),
            marker("map", "remove"),
            marker("map", "remove_all"),
            marker("map", "keys"),
            marker("map", "keys_list"),
            marker("map", "values"),
            marker("map", "size"),
            marker("map", "update_all"),
            marker("map", "get_or_default"),
        ]
    );
    assert_eq!(
        ListOperation::ALL.map(ListOperation::facade_marker),
        [
            marker("list", "empty"),
            marker("list", "item"),
            marker("list", "concat"),
            marker("list", "get"),
            marker("list", "update"),
            marker("list", "size"),
            marker("list", "make"),
            marker("list", "range"),
            marker("list", "update_all"),
            marker("list", "contains"),
        ]
    );
    assert_eq!(
        SetOperation::ALL.map(SetOperation::facade_marker),
        [
            marker("set", "empty"),
            marker("set", "item"),
            marker("set", "concat"),
            marker("set", "union"),
            marker("set", "contains"),
            marker("set", "difference"),
            marker("set", "intersect"),
            marker("set", "size"),
            marker("set", "is_subset"),
            marker("set", "to_list"),
            marker("set", "from_list"),
        ]
    );
}

#[test]
fn application_heads_expose_their_rows_through_the_shared_trait() {
    fn assert_rows<O: CollectionApplication + Copy>(operations: &[O], sort: BuiltinSort) {
        assert_eq!(O::SORT, sort);
        for operation in operations {
            assert!(!operation.spec().description.is_empty());
            assert!(operation.spec().k_hook.is_some());
            assert!(!operation.spec().k_module.is_empty());
            assert!(!operation.facade_marker().name.is_empty());
        }
    }
    assert_rows(&TermMapOperation::ALL, BuiltinSort::Map);
    assert_rows(&ListOperation::ALL, BuiltinSort::List);
    assert_rows(&SetOperation::ALL, BuiltinSort::Set);
    assert_eq!(MapOperation::CONCATENATION.k_label, "_Map_");
    assert_eq!(MapOperation::CONCATENATION.separator, " ");
}

#[test]
fn every_collection_method_reading_takes_its_receiver_where_its_row_says() {
    use krs_ir::{CollectionDomain, CollectionMethod, CollectionOperandSort};
    for method in CollectionMethod::ALL {
        let domains = method.domains();
        assert!(!domains.is_empty(), "{method:?} denotes nothing");
        for domain in domains {
            let reading = method.reading(domain).expect("a listed domain reads");
            let spec = reading.spec();
            assert_eq!(spec.arity(), method.arity(), "{method:?} in {domain:?}");
            assert_eq!(
                spec.operand_sorts.get(method.receiver()),
                Some(&CollectionOperandSort::Builtin(domain.sort())),
                "{method:?} in {domain:?}: the receiver is the collection"
            );
            assert_eq!(
                reading.facade_marker().module,
                match domain {
                    CollectionDomain::Map => "map",
                    CollectionDomain::List => "list",
                    CollectionDomain::Set => "set",
                },
                "{method:?} in {domain:?}"
            );
        }
        assert_eq!(
            method.facade_marker(),
            marker("__collection", method.rust_name())
        );
    }
}

#[test]
fn collection_methods_are_the_table_of_index_reads_and_methods() {
    use krs_ir::{CollectionDomain, CollectionMethod, CollectionReading};
    let table = CollectionMethod::ALL
        .into_iter()
        .map(|method| {
            let readings = CollectionDomain::ALL
                .into_iter()
                .filter_map(|domain| method.reading(domain))
                .map(|reading| {
                    let marker = reading.facade_marker();
                    format!("{}::{}", marker.module, marker.name)
                })
                .collect::<Vec<_>>();
            format!("{} {}", method.written(), readings.join(" "))
        })
        .collect::<Vec<_>>();
    assert_eq!(
        table,
        [
            "[..] map::get list::get",
            ".get_or(..) map::get_or_default",
            ".contains_key(..) map::in_keys",
            ".update(..) map::update list::update",
            ".without(..) map::remove",
            ".without_all(..) map::remove_all",
            ".extend(..) map::update_all",
            ".keys() map::keys",
            ".keys_list() map::keys_list",
            ".values() map::values",
            ".len() map::size list::size set::size",
            ".contains(..) list::contains set::contains",
            ".union(..) set::union",
            ".difference(..) set::difference",
            ".intersection(..) set::intersect",
            ".is_subset(..) set::is_subset",
            ".to_list() set::to_list",
        ]
    );
    assert_eq!(CollectionMethod::named("index"), None);
    assert_eq!(
        CollectionMethod::named("contains_key"),
        Some(CollectionMethod::ContainsKey)
    );
    assert_eq!(
        CollectionMethod::Index.reading(CollectionDomain::Map),
        Some(CollectionReading::Map(TermMapOperation::Get))
    );
}
