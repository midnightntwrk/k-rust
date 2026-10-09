use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{BuiltinOperation, BuiltinSort, NodeOrigin, NonEmpty};
use krs_ir_levels::{
    DefinitionApplicationRef, DefinitionSortRef, DefinitionTerm, ListOperands, MapEntry,
    MapOperands, SetOperands,
    k_surface::{SentenceVariables, VariableNaming},
};

use super::{EmitContext, quoted_kstring, quoted_outer, term::render_term, token::TokenLexicon};

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
        lexicon: TokenLexicon::default(),
        spec_identifiers: None,
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

fn float(key: &str, value: &str) -> DefinitionTerm {
    DefinitionTerm::token(
        node(key),
        DefinitionSortRef::Builtin(BuiltinSort::Float),
        value,
    )
    .unwrap()
}

#[test]
fn builtin_float_operations_have_exact_canonical_k_source() {
    let float_sort = || DefinitionSortRef::Builtin(BuiltinSort::Float);
    let apply = |key: &str, sort, operation, arguments| {
        DefinitionTerm::application(
            node(key),
            sort,
            DefinitionApplicationRef::Builtin(operation),
            arguments,
        )
    };
    let terms = [
        (
            apply(
                "float.add",
                float_sort(),
                BuiltinOperation::FloatAdd,
                vec![
                    float("float.add.left", "0.1f"),
                    float("float.add.right", "NaN"),
                ],
            ),
            "0.1f +Float NaN",
        ),
        (
            apply(
                "float.neg",
                float_sort(),
                BuiltinOperation::FloatNeg,
                vec![float("float.neg.operand", "-Infinity")],
            ),
            "--Float -Infinity",
        ),
        (
            apply(
                "float.root",
                float_sort(),
                BuiltinOperation::FloatRoot,
                vec![
                    float("float.root.base", "2.0"),
                    int("float.root.degree", "2"),
                ],
            ),
            "rootFloat(2.0, 2)",
        ),
        (
            apply(
                "float.from-int",
                float_sort(),
                BuiltinOperation::FloatFromInt,
                vec![
                    int("float.from-int.value", "7"),
                    int("float.from-int.precision", "53"),
                    int("float.from-int.exponent", "11"),
                ],
            ),
            "Int2Float(7, 53, 11)",
        ),
        (
            apply(
                "float.eq",
                DefinitionSortRef::Builtin(BuiltinSort::Bool),
                BuiltinOperation::FloatEqual,
                vec![
                    apply(
                        "float.eq.left",
                        float_sort(),
                        BuiltinOperation::FloatNeg,
                        vec![float("float.eq.zero", "0.0")],
                    ),
                    float("float.eq.right", "1.0p113x15"),
                ],
            ),
            "(--Float 0.0) ==Float 1.0p113x15",
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

#[test]
fn tokens_print_bare_only_when_k_lexes_them_back() {
    let context = context();
    for (sort, value, expected) in [
        (BuiltinSort::Int, "-7", "-7"),
        (BuiltinSort::Bool, "true", "true"),
        (BuiltinSort::Bytes, r#"b"\x00""#, r#"b"\x00""#),
        (BuiltinSort::String, r#""a\"b""#, r#""a\"b""#),
        (BuiltinSort::Float, "-0.0", "-0.0"),
        (BuiltinSort::Float, "NaNf", "NaNf"),
        (BuiltinSort::Float, "1.5F", r#"#token("1.5F","Float")"#),
        // `ID-SYNTAX` gives `Id` no rule-grammar lexical syntax, so no Id spelling is bare.
        (BuiltinSort::Id, "$x", r#"#token("$x","Id")"#),
        (BuiltinSort::Id, "x", r#"#token("x","Id")"#),
        (BuiltinSort::Int, "1_000", r#"#token("1_000","Int")"#),
        (
            BuiltinSort::String,
            "unquoted",
            r#"#token("unquoted","String")"#,
        ),
    ] {
        let term =
            DefinitionTerm::token(node("token"), DefinitionSortRef::Builtin(sort), value).unwrap();
        assert_eq!(render(&term, &context), expected, "{sort:?} {value:?}");
    }
    let unspellable = DefinitionTerm::token(
        node("token"),
        DefinitionSortRef::Builtin(BuiltinSort::Id),
        "line\nbreak",
    )
    .unwrap();
    assert!(render_term(&unspellable, &context, &SentenceVariables::default(), false).is_err());
}

#[test]
fn outer_syntax_literals_use_only_the_outer_lexer_escapes() {
    assert_eq!(quoted_outer("if"), r#""if""#);
    assert_eq!(quoted_outer("a\"b\\c"), r#""a\"b\\c""#);
    assert_eq!(quoted_outer("\n\r\t"), r#""\n\r\t""#);
    // Outer.jj reads any other character literally; `\u{..}` would not lex.
    assert_eq!(quoted_outer("\u{1b}[0m\u{7f}"), "\"\u{1b}[0m\u{7f}\"");
    assert_eq!(quoted_outer("é→"), "\"é→\"");
    assert_eq!(quoted_outer(r"[0-9]+\."), r#""[0-9]+\\.""#);
}

#[test]
fn cell_properties_use_kstring_escapes() {
    assert_eq!(quoted_kstring("red"), r#""red""#);
    assert_eq!(quoted_kstring("a\"b\\c"), r#""a\"b\\c""#);
    assert_eq!(quoted_kstring("\n\r\t\u{c}"), r#""\n\r\t\f""#);
    assert_eq!(
        quoted_kstring("\u{0}\u{1b}\u{7f}\u{9f}"),
        r#""\x00\x1B\x7F\x9F""#
    );
    assert_eq!(quoted_kstring("é→"), "\"é→\"");
}

#[test]
fn operator_shaped_collection_operands_are_parenthesized_where_k_could_misread_them() {
    let item = |key: &str, value: &str| {
        DefinitionTerm::set(
            node(key),
            DefinitionSortRef::set(),
            SetOperands::Item {
                element: int(&format!("{key}.value"), value),
            },
        )
    };
    let union = |key: &str, left: DefinitionTerm, right: DefinitionTerm| {
        DefinitionTerm::set(
            node(key),
            DefinitionSortRef::set(),
            SetOperands::Union { left, right },
        )
    };
    let map = || DefinitionTerm::map(node("map.empty"), MapOperands::Empty);
    let update = || {
        DefinitionTerm::map(
            node("map.update"),
            MapOperands::Update {
                map: map(),
                key: int("map.update.key", "1"),
                value: int("map.update.value", "2"),
            },
        )
    };
    let terms = [
        (
            DefinitionTerm::set(
                node("set.difference"),
                DefinitionSortRef::set(),
                SetOperands::Difference {
                    left: union("set.union", item("a", "1"), item("b", "2")),
                    right: item("c", "2"),
                },
            ),
            "(SetItem(1) |Set SetItem(2)) -Set SetItem(2)",
        ),
        (
            DefinitionTerm::set(
                node("set.contains"),
                DefinitionSortRef::bool(),
                SetOperands::Contains {
                    element: int("set.contains.element", "1"),
                    set: union("set.union", item("a", "1"), item("b", "2")),
                },
            ),
            "1 in (SetItem(1) |Set SetItem(2))",
        ),
        // `|Set` is left-associative, so a union in its own left operand needs no parentheses.
        (
            union(
                "set.outer",
                union("set.inner", item("a", "1"), item("b", "2")),
                item("c", "3"),
            ),
            "SetItem(1) |Set SetItem(2) |Set SetItem(3)",
        ),
        // A postfix update closes on the right, so a removal applies to it directly.
        (
            DefinitionTerm::map(
                node("map.remove"),
                MapOperands::Remove {
                    map: update(),
                    key: int("map.remove.key", "1"),
                },
            ),
            ".Map [ 1 <- 2 ] [ 1 <- undef ]",
        ),
        (
            DefinitionTerm::typed_map(
                node("map.get-or-default"),
                DefinitionSortRef::int(),
                MapOperands::GetOrDefault {
                    map: map(),
                    key: int("map.get-or-default.key", "1"),
                    default: int("map.get-or-default.default", "0"),
                },
            ),
            "{.Map [ 1 ] orDefault 0}:>Int",
        ),
    ];
    let context = context();
    for (term, expected) in terms {
        assert_eq!(render(&term, &context), expected);
    }
}

#[test]
fn generated_sort_operations_print_k_predicates_and_one_cast() {
    let context = context();
    let generated = |key: &str, sort, operation, argument| {
        DefinitionTerm::application(
            node(key),
            sort,
            DefinitionApplicationRef::Generated(operation),
            vec![argument],
        )
    };
    let predicate = generated(
        "is-int",
        DefinitionSortRef::Builtin(BuiltinSort::Bool),
        krs_ir::GeneratedOperation::SortPredicate(DefinitionSortRef::int()),
        int("is-int.operand", "1"),
    );
    assert_eq!(render(&predicate, &context), "isInt(1)");
    let projection = generated(
        "project-int",
        DefinitionSortRef::int(),
        krs_ir::GeneratedOperation::SortProjection(DefinitionSortRef::int()),
        int("project-int.operand", "1"),
    );
    assert_eq!(render(&projection, &context), "{1}:>Int");
    // A projected lookup under a projection keeps its KItem result and
    // contributes no cast of its own.
    let lookup = DefinitionTerm::list(
        node("lookup"),
        DefinitionSortRef::Builtin(BuiltinSort::KSequence),
        ListOperands::Get {
            list: empty("lookup.base"),
            index: int("lookup.index", "0"),
        },
    );
    let projected = generated(
        "project-lookup",
        DefinitionSortRef::int(),
        krs_ir::GeneratedOperation::SortProjection(DefinitionSortRef::int()),
        lookup,
    );
    assert_eq!(render(&projected, &context), "{.List [ 0 ]}:>Int");
}
