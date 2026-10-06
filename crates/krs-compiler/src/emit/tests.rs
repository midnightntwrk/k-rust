use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{BuiltinOperation, NodeOrigin, NonEmpty};
use krs_ir_levels::{
    DefinitionApplicationRef, DefinitionSortRef, DefinitionTerm, ListOperands, MapEntry,
    MapOperands, SetOperands,
    k_surface::{SentenceVariables, VariableNaming},
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
        index: krs_ir_levels::k_surface::DefinitionIndex::default(),
        non_associative_groups: BTreeSet::new(),
        repeated_ancestors: BTreeMap::new(),
        naming: VariableNaming::default(),
    }
}

fn render(term: &DefinitionTerm, context: &EmitContext<'_>) -> String {
    render_term(term, context, &SentenceVariables::default(), false)
        .unwrap()
        .text
}

fn empty(key: &str) -> DefinitionTerm {
    DefinitionTerm::list(node(key), DefinitionSortRef::list(), ListOperands::Empty)
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
                ListOperands::Item {
                    element: int("list.item.value", "1"),
                },
            ),
            "ListItem(1)",
        ),
        (
            DefinitionTerm::list(
                node("list.concat"),
                DefinitionSortRef::list(),
                ListOperands::Concat {
                    left: empty("list.concat.left"),
                    right: DefinitionTerm::list(
                        node("list.concat.right"),
                        DefinitionSortRef::list(),
                        ListOperands::Item {
                            element: int("list.concat.value", "1"),
                        },
                    ),
                },
            ),
            ".List ListItem(1)",
        ),
        (
            DefinitionTerm::list(
                node("list.get"),
                DefinitionSortRef::int(),
                ListOperands::Get {
                    list: empty("list.get.base"),
                    index: int("list.get.index", "0"),
                },
            ),
            "{.List [ 0 ]}:>Int",
        ),
        (
            DefinitionTerm::list(
                node("list.update"),
                DefinitionSortRef::list(),
                ListOperands::Update {
                    list: empty("list.update.base"),
                    index: int("list.update.index", "0"),
                    value: int("list.update.value", "1"),
                },
            ),
            ".List [ 0 <- 1 ]",
        ),
        (
            DefinitionTerm::list(
                node("list.size"),
                DefinitionSortRef::int(),
                ListOperands::Size {
                    list: empty("list.size.base"),
                },
            ),
            "size(.List)",
        ),
        (
            DefinitionTerm::list(
                node("list.range"),
                DefinitionSortRef::list(),
                ListOperands::Range {
                    list: empty("list.range.base"),
                    from_front: int("list.range.front", "1"),
                    from_back: int("list.range.back", "2"),
                },
            ),
            "range(.List, 1, 2)",
        ),
        (
            DefinitionTerm::list(
                node("list.update-all"),
                DefinitionSortRef::list(),
                ListOperands::UpdateAll {
                    list: empty("list.update-all.base"),
                    index: int("list.update-all.index", "1"),
                    replacement: empty("list.update-all.replacement"),
                },
            ),
            "updateList(.List, 1, .List)",
        ),
    ];
    let context = context();
    for (term, expected) in terms {
        assert_eq!(render(&term, &context), expected);
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
        assert_eq!(render(&term, &context), expected);
    }
}

#[test]
fn builtin_map_lookup_and_set_operations_have_exact_canonical_k_source() {
    let map = || DefinitionTerm::map(node("map.empty"), MapOperands::Empty);
    let set = || {
        DefinitionTerm::set(
            node("set.empty"),
            DefinitionSortRef::set(),
            SetOperands::Empty,
        )
    };
    let terms = [
        (
            DefinitionTerm::typed_map(
                node("map.get"),
                DefinitionSortRef::int(),
                MapOperands::Get {
                    map: map(),
                    key: int("map.get.key", "1"),
                },
            ),
            "{.Map [ 1 ]}:>Int",
        ),
        (
            DefinitionTerm::typed_map(
                node("map.in-keys"),
                DefinitionSortRef::bool(),
                MapOperands::InKeys {
                    key: int("map.in-keys.key", "1"),
                    map: map(),
                },
            ),
            "1 in_keys(.Map)",
        ),
        (set(), ".Set"),
        (
            DefinitionTerm::set(
                node("set.item"),
                DefinitionSortRef::set(),
                SetOperands::Item {
                    element: int("set.item.value", "1"),
                },
            ),
            "SetItem(1)",
        ),
        (
            DefinitionTerm::set(
                node("set.concat"),
                DefinitionSortRef::set(),
                SetOperands::Concat {
                    left: set(),
                    right: set(),
                },
            ),
            ".Set .Set",
        ),
        (
            DefinitionTerm::set(
                node("set.union"),
                DefinitionSortRef::set(),
                SetOperands::Union {
                    left: set(),
                    right: set(),
                },
            ),
            ".Set |Set .Set",
        ),
        (
            DefinitionTerm::set(
                node("set.contains"),
                DefinitionSortRef::bool(),
                SetOperands::Contains {
                    element: int("set.contains.value", "1"),
                    set: set(),
                },
            ),
            "1 in .Set",
        ),
    ];
    let context = context();
    for (term, expected) in terms {
        assert_eq!(render(&term, &context), expected);
    }
}

#[test]
fn remaining_collection_operations_have_exact_canonical_k_source() {
    let map = || DefinitionTerm::map(node("map.empty"), MapOperands::Empty);
    let terms = [
        (map(), ".Map"),
        (
            DefinitionTerm::map(
                node("map.items"),
                MapOperands::Items(NonEmpty::new(
                    MapEntry {
                        key: int("map.items.first.key", "1"),
                        value: int("map.items.first.value", "2"),
                    },
                    vec![MapEntry {
                        key: int("map.items.second.key", "3"),
                        value: int("map.items.second.value", "4"),
                    }],
                )),
            ),
            "1 |-> 2 3 |-> 4",
        ),
        (
            DefinitionTerm::map(
                node("map.update"),
                MapOperands::Update {
                    map: map(),
                    key: int("map.update.key", "1"),
                    value: int("map.update.value", "2"),
                },
            ),
            ".Map [ 1 <- 2 ]",
        ),
        (
            DefinitionTerm::list(
                node("list.make"),
                DefinitionSortRef::list(),
                ListOperands::Make {
                    length: int("list.make.length", "3"),
                    value: int("list.make.value", "7"),
                },
            ),
            "makeList(3, 7)",
        ),
    ];
    let context = context();
    for (term, expected) in terms {
        assert_eq!(render(&term, &context), expected);
    }
}
