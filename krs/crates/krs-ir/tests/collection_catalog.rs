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
            MapOperation::Empty,
            MapOperation::Item,
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
        assert_eq!(
            term.is_ok(),
            !matches!(operation, MapOperation::Empty | MapOperation::Item),
            "{operation}"
        );
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
