use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    BuiltinOperation, DefinitionApplicationRef, DefinitionSortRef, DefinitionTerm, ListOperation,
    MapOperation, NodeOrigin, SetOperation,
};

use super::{EmitContext, term::render_term};

fn node(key: &str) -> NodeOrigin {
    krs_ir::testing::origin_in(
        key,
        krs_ir::testing::package("KRS-EMIT-TEST", "emit-test"),
        "src/lib.rs",
        krs_ir::testing::digest(),
        0,
        1,
    )
}

fn context() -> EmitContext<'static> {
    EmitContext {
        index: krs_ir::k_surface::DefinitionIndex::default(),
        non_associative_groups: BTreeSet::new(),
        repeated_ancestors: BTreeMap::new(),
    }
}

fn empty(key: &str) -> DefinitionTerm {
    DefinitionTerm::list(
        node(key),
        DefinitionSortRef::list(),
        ListOperation::Empty,
        vec![],
    )
}

fn int(key: &str, value: &str) -> DefinitionTerm {
    DefinitionTerm::token(node(key), DefinitionSortRef::int(), value).unwrap()
}

#[test]
fn builtin_list_operations_have_exact_canonical_k_source() {
    let terms = [
        (empty("list.empty"), ".List"),
        (
            DefinitionTerm::list(
                node("list.item"),
                DefinitionSortRef::list(),
                ListOperation::Item,
                vec![int("list.item.value", "1")],
            ),
            "ListItem(1)",
        ),
        (
            DefinitionTerm::list(
                node("list.concat"),
                DefinitionSortRef::list(),
                ListOperation::Concat,
                vec![
                    empty("list.concat.left"),
                    DefinitionTerm::list(
                        node("list.concat.right"),
                        DefinitionSortRef::list(),
                        ListOperation::Item,
                        vec![int("list.concat.value", "1")],
                    ),
                ],
            ),
            ".List ListItem(1)",
        ),
        (
            DefinitionTerm::list(
                node("list.get"),
                DefinitionSortRef::int(),
                ListOperation::Get,
                vec![empty("list.get.base"), int("list.get.index", "0")],
            ),
            "{.List [ 0 ]}:>Int",
        ),
        (
            DefinitionTerm::list(
                node("list.update"),
                DefinitionSortRef::list(),
                ListOperation::Update,
                vec![
                    empty("list.update.base"),
                    int("list.update.index", "0"),
                    int("list.update.value", "1"),
                ],
            ),
            ".List [ 0 <- 1 ]",
        ),
        (
            DefinitionTerm::list(
                node("list.size"),
                DefinitionSortRef::int(),
                ListOperation::Size,
                vec![empty("list.size.base")],
            ),
            "size(.List)",
        ),
        (
            DefinitionTerm::list(
                node("list.range"),
                DefinitionSortRef::list(),
                ListOperation::Range,
                vec![
                    empty("list.range.base"),
                    int("list.range.front", "1"),
                    int("list.range.back", "2"),
                ],
            ),
            "range(.List, 1, 2)",
        ),
        (
            DefinitionTerm::list(
                node("list.update-all"),
                DefinitionSortRef::list(),
                ListOperation::UpdateAll,
                vec![
                    empty("list.update-all.base"),
                    int("list.update-all.index", "1"),
                    empty("list.update-all.replacement"),
                ],
            ),
            "updateList(.List, 1, .List)",
        ),
    ];
    let context = context();
    for (term, expected) in terms {
        assert_eq!(render_term(&term, &context, false).unwrap().text, expected);
    }
}

#[test]
fn builtin_bytes_operations_have_exact_canonical_k_source() {
    let empty = || {
        DefinitionTerm::application(
            node("bytes.empty"),
            DefinitionSortRef::bytes(),
            DefinitionApplicationRef::Builtin(BuiltinOperation::BytesEmpty),
            vec![],
        )
    };
    let terms = [
        (empty(), ".Bytes"),
        (
            DefinitionTerm::application(
                node("bytes.update"),
                DefinitionSortRef::bytes(),
                DefinitionApplicationRef::Builtin(BuiltinOperation::BytesUpdate),
                vec![
                    empty(),
                    int("bytes.update.index", "0"),
                    int("bytes.update.value", "255"),
                ],
            ),
            "(.Bytes) [ 0 <- 255 ]",
        ),
        (
            DefinitionTerm::application(
                node("bytes.pad-right"),
                DefinitionSortRef::bytes(),
                DefinitionApplicationRef::Builtin(BuiltinOperation::BytesPadRight),
                vec![
                    empty(),
                    int("bytes.pad-right.length", "32"),
                    int("bytes.pad-right.value", "0"),
                ],
            ),
            "padRightBytes(.Bytes, 32, 0)",
        ),
        (
            DefinitionTerm::application(
                node("bytes.substring"),
                DefinitionSortRef::bytes(),
                DefinitionApplicationRef::Builtin(BuiltinOperation::BytesSubstring),
                vec![
                    empty(),
                    int("bytes.substring.start", "1"),
                    int("bytes.substring.end", "3"),
                ],
            ),
            "substrBytes(.Bytes, 1, 3)",
        ),
    ];
    let context = context();
    for (term, expected) in terms {
        assert_eq!(render_term(&term, &context, false).unwrap().text, expected);
    }
}

#[test]
fn builtin_map_lookup_and_set_operations_have_exact_canonical_k_source() {
    let map = || DefinitionTerm::map(node("map.empty"), MapOperation::Empty, vec![]);
    let set = || {
        DefinitionTerm::set(
            node("set.empty"),
            DefinitionSortRef::set(),
            SetOperation::Empty,
            vec![],
        )
    };
    let terms = [
        (
            DefinitionTerm::typed_map(
                node("map.get"),
                DefinitionSortRef::int(),
                MapOperation::Get,
                vec![map(), int("map.get.key", "1")],
            ),
            "{.Map [ 1 ]}:>Int",
        ),
        (
            DefinitionTerm::typed_map(
                node("map.in-keys"),
                DefinitionSortRef::bool(),
                MapOperation::InKeys,
                vec![int("map.in-keys.key", "1"), map()],
            ),
            "1 in_keys(.Map)",
        ),
        (set(), ".Set"),
        (
            DefinitionTerm::set(
                node("set.item"),
                DefinitionSortRef::set(),
                SetOperation::Item,
                vec![int("set.item.value", "1")],
            ),
            "SetItem(1)",
        ),
        (
            DefinitionTerm::set(
                node("set.concat"),
                DefinitionSortRef::set(),
                SetOperation::Concat,
                vec![set(), set()],
            ),
            ".Set .Set",
        ),
        (
            DefinitionTerm::set(
                node("set.union"),
                DefinitionSortRef::set(),
                SetOperation::Union,
                vec![set(), set()],
            ),
            ".Set |Set .Set",
        ),
        (
            DefinitionTerm::set(
                node("set.contains"),
                DefinitionSortRef::bool(),
                SetOperation::Contains,
                vec![int("set.contains.value", "1"), set()],
            ),
            "1 in .Set",
        ),
    ];
    let context = context();
    for (term, expected) in terms {
        assert_eq!(render_term(&term, &context, false).unwrap().text, expected);
    }
}
