use k_rust::{
    backend::{Backend as NativeBackend, BackendOptions, ExecuteRequest},
    definition::{ProductionItem, Sentence},
    kast::Term,
    kore::parser::parse_pattern,
};
use krs_ir::{
    ApplicationRef, BuiltinOperation, CellAttribute, CellContentFrame, ClaimModality,
    ConfigurationRoot, FixedCell, FixedCellPattern, FixedConfiguration, FixedConfigurationPattern,
    FixedConfigurationVariable, FixedInitializerCell, FormatFragment, GroupAssociativity,
    GroupAssociativitySentence, HookOperation, ItemKind, ListOperation, MapOperation, ModuleId,
    NonEmpty, PrecedenceRelation, ProductionFieldId, ProductionFieldReference, ProductionGroupId,
    ProductionResultSort, SentenceKind, SetOperation, StableItemId, StrictnessKind,
};
use krs_ir_levels::{
    ContextAliasSentence, DefinitionClaim, DefinitionIr, DefinitionModule,
    DefinitionProductionAttribute, DefinitionRuleCondition, DefinitionScopedBinder,
    DefinitionSentence, DefinitionSortRef, DefinitionTerm, IrCondition, IrMlKind, IrMlPredicate,
    LabelId, LabelIdentity, ListOperands, MapEntry, MapOperands, ProductionGroupIdentity,
    ProductionItem as IrProductionItem, ProductionSentence, RuleSentence, SetOperands, SymbolId,
    SymbolKind,
    k_surface::{ImportPolicy, builtin_imports},
};

use super::{
    Adapter, AdapterError,
    sentence::{claim_modality_attribute, native_claim_counter, native_rule_label},
    term::TermContext,
};
use crate::{
    Backend, CompileOptions, NativeNodePlace, SentenceNodeRole, adapt_definition,
    compile_definition, prepare_definition,
    test_fixtures::{MODULE, node, semantic_id, smoke_definition, symbol},
};

#[test]
fn native_rule_labels_match_the_source_frontend_namespace_policy() {
    let label = |name: &str| LabelIdentity::new(LabelId::new("label").unwrap(), name).unwrap();
    assert_eq!(
        native_rule_label("SMOKE", &label("foo-to-bar")),
        "SMOKE.foo-to-bar"
    );
    assert_eq!(
        native_rule_label("SMOKE", &label("krsRule_725f2944b8a5a8eaf4b9fc6c")),
        "krsRule_725f2944b8a5a8eaf4b9fc6c"
    );
}

#[test]
fn native_claim_modalities_are_explicit() {
    assert_eq!(claim_modality_attribute(ClaimModality::OnePath), "one-path");
    assert_eq!(
        claim_modality_attribute(ClaimModality::AllPaths),
        "all-path"
    );
}

#[test]
fn typed_hooks_map_to_exact_native_frontend_attributes() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    for (index, operation) in HookOperation::ALL.into_iter().enumerate() {
        let expected = match operation {
            HookOperation::KryptoKeccak256Raw => "KRYPTO.keccak256raw",
            HookOperation::KryptoSha256Raw => "KRYPTO.sha256raw",
            HookOperation::KryptoRipemd160Raw => "KRYPTO.ripemd160raw",
            HookOperation::KryptoEcdsaRecover => "KRYPTO.ecdsaRecover",
            HookOperation::KryptoBn128Valid => "KRYPTO.bn128valid",
            HookOperation::KryptoBn128Add => "KRYPTO.bn128add",
            HookOperation::KryptoBn128Mul => "KRYPTO.bn128mul",
            HookOperation::KryptoBn128G2Valid => "KRYPTO.bn128g2valid",
            HookOperation::KryptoBn128Ate => "KRYPTO.bn128ate",
        };
        let point = DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap());
        let (result_sort, argument_sorts) =
            if let Some((result, arguments)) = operation.builtin_signature() {
                (
                    DefinitionSortRef::Builtin(result),
                    arguments
                        .iter()
                        .copied()
                        .map(DefinitionSortRef::Builtin)
                        .collect::<Vec<_>>(),
                )
            } else {
                match operation {
                    HookOperation::KryptoBn128Valid | HookOperation::KryptoBn128G2Valid => {
                        (DefinitionSortRef::bool(), vec![point])
                    }
                    HookOperation::KryptoBn128Add => (point.clone(), vec![point.clone(), point]),
                    HookOperation::KryptoBn128Mul => {
                        (point.clone(), vec![point, DefinitionSortRef::int()])
                    }
                    HookOperation::KryptoKeccak256Raw
                    | HookOperation::KryptoSha256Raw
                    | HookOperation::KryptoRipemd160Raw
                    | HookOperation::KryptoEcdsaRecover
                    | HookOperation::KryptoBn128Ate => unreachable!(),
                }
            };
        let items = argument_sorts
            .into_iter()
            .enumerate()
            .map(|(field, sort)| {
                IrProductionItem::non_terminal(
                    node(&format!("hook.{index}.field.{field}")),
                    ProductionFieldId::new(format!("field{field}")).unwrap(),
                    sort,
                )
            })
            .collect();
        let production = ProductionSentence::new(
            node(&format!("hook.{index}.production")),
            symbol(
                &format!("production.hook{index}"),
                &format!("Hook{index}"),
                SymbolKind::Production,
            ),
            result_sort,
            items,
            vec![
                DefinitionProductionAttribute::Function {
                    origin: node(&format!("hook.{index}.function")),
                },
                DefinitionProductionAttribute::Total {
                    origin: node(&format!("hook.{index}.total")),
                },
                DefinitionProductionAttribute::Hook {
                    origin: node(&format!("hook.{index}.attribute")),
                    operation,
                },
            ],
        )
        .unwrap();
        let native = adapter.production(&production, MODULE, index).unwrap();
        let Sentence::Production { attributes, .. } = native else {
            panic!("hooked function must remain a native production")
        };
        assert_eq!(attributes.get_str("hook"), Some(expected));
        assert_eq!(
            attributes.get_str("hook"),
            Some(operation.to_string().as_str())
        );
        assert!(attributes.get("function").is_some());
        assert!(attributes.get("total").is_some());
    }
}

#[test]
fn native_claim_counter_is_a_fresh_rhs_internal() {
    let counter = native_claim_counter(7);
    let mut variables = Vec::new();
    counter.visit_preorder(&mut |term| {
        if let Term::Variable { name, sort } = term {
            variables.push((name.clone(), sort.as_ref().map(|sort| sort.name.clone())));
        }
    });
    assert_eq!(
        variables,
        vec![
            ("_Krs_Counter7".to_owned(), Some("Int".to_owned())),
            ("?Krs_Counter7".to_owned(), Some("Int".to_owned())),
        ]
    );
}

fn context_alias_id() -> StableItemId {
    krs_ir::testing::item("contexts", "eval", ItemKind::ContextAlias)
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "Qualifies all structured builtin families in one definition."
)]
fn builtin_map_list_set_and_bytes_terms_map_structurally_and_infer_imports() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let int =
        |key, value| DefinitionTerm::token(node(key), DefinitionSortRef::int(), value).unwrap();
    let id = |key, value| DefinitionTerm::token(node(key), DefinitionSortRef::id(), value).unwrap();
    let addition = DefinitionTerm::application(
        node("schema9.term.add"),
        DefinitionSortRef::int(),
        ApplicationRef::Builtin(BuiltinOperation::IntAdd),
        vec![int("schema9.term.one", "1"), int("schema9.term.two", "2")],
    );
    let item = DefinitionTerm::map(
        node("schema9.term.map-item"),
        MapOperands::Items(NonEmpty::new(
            MapEntry {
                key: id("schema9.term.key-a", "a"),
                value: addition.clone(),
            },
            vec![MapEntry {
                key: id("schema9.term.key-b", "b"),
                value: int("schema9.term.three", "3"),
            }],
        )),
    );
    let update = DefinitionTerm::map(
        node("schema9.term.map-update"),
        MapOperands::Update {
            map: DefinitionTerm::map(node("schema9.term.empty-map"), MapOperands::Empty),
            key: id("schema9.term.update-key", "a"),
            value: int("schema9.term.update-value", "4"),
        },
    );

    let native_addition = adapter
        .term(&addition, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(matches!(&native_addition, Term::Apply { label, arguments }
        if label.name == "_+Int_" && arguments.len() == 2));
    let empty_bytes = DefinitionTerm::application(
        node("schema14.term.empty-bytes"),
        DefinitionSortRef::bytes(),
        ApplicationRef::Builtin(BuiltinOperation::BytesEmpty),
        vec![],
    );
    let native_empty_bytes = adapter
        .term(&empty_bytes, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(
        matches!(&native_empty_bytes, Term::Apply { label, arguments }
        if label.name == ".Bytes_BYTES-HOOKED_Bytes" && arguments.is_empty())
    );
    let bytes_update = DefinitionTerm::application(
        node("schema15.term.bytes-update"),
        DefinitionSortRef::bytes(),
        ApplicationRef::Builtin(BuiltinOperation::BytesUpdate),
        vec![
            empty_bytes.clone(),
            DefinitionTerm::token(
                node("schema15.term.bytes-update.index"),
                DefinitionSortRef::int(),
                "0",
            )
            .unwrap(),
            DefinitionTerm::token(
                node("schema15.term.bytes-update.value"),
                DefinitionSortRef::int(),
                "255",
            )
            .unwrap(),
        ],
    );
    let native_bytes_update = adapter
        .term(&bytes_update, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(
        matches!(&native_bytes_update, Term::Apply { label, arguments }
        if label.name == "_[_<-_]_BYTES-HOOKED_Bytes_Bytes_Int_Int" && arguments.len() == 3)
    );
    let bytes_pad_right = DefinitionTerm::application(
        node("schema15.term.bytes-pad-right"),
        DefinitionSortRef::bytes(),
        ApplicationRef::Builtin(BuiltinOperation::BytesPadRight),
        vec![
            empty_bytes,
            DefinitionTerm::token(
                node("schema15.term.bytes-pad-right.length"),
                DefinitionSortRef::int(),
                "32",
            )
            .unwrap(),
            DefinitionTerm::token(
                node("schema15.term.bytes-pad-right.value"),
                DefinitionSortRef::int(),
                "0",
            )
            .unwrap(),
        ],
    );
    let native_bytes_pad_right = adapter
        .term(&bytes_pad_right, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(
        matches!(&native_bytes_pad_right, Term::Apply { label, arguments }
        if label.name == "padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int" && arguments.len() == 3)
    );
    let bytes_substring = DefinitionTerm::application(
        node("schema26.term.bytes-substring"),
        DefinitionSortRef::bytes(),
        ApplicationRef::Builtin(BuiltinOperation::BytesSubstring),
        vec![
            DefinitionTerm::application(
                node("schema26.term.bytes-substring.value"),
                DefinitionSortRef::bytes(),
                ApplicationRef::Builtin(BuiltinOperation::BytesEmpty),
                vec![],
            ),
            int("schema26.term.bytes-substring.start", "1"),
            int("schema26.term.bytes-substring.end", "3"),
        ],
    );
    let native_bytes_substring = adapter
        .term(&bytes_substring, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(
        matches!(&native_bytes_substring, Term::Apply { label, arguments }
        if label.name == "substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int" && arguments.len() == 3)
    );
    let native_item = adapter
        .term(&item, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(matches!(&native_item, Term::Apply { label, arguments }
        if label.name == "_Map_"
            && matches!(arguments.as_slice(), [Term::Apply { label: left, .. }, Term::Apply { label: right, .. }]
                if left.name == "_|->_" && right.name == "_|->_")));
    let native_update = adapter
        .term(&update, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(matches!(&native_update, Term::Apply { label, arguments }
        if label.name == "Map:update"
            && matches!(arguments.first(), Some(Term::Apply { label, arguments })
                if label.name == ".Map" && arguments.is_empty())));
    let map_get = DefinitionTerm::typed_map(
        node("schema16.term.map-get"),
        DefinitionSortRef::int(),
        MapOperands::Get {
            map: DefinitionTerm::map(node("schema16.term.get-map"), MapOperands::Empty),
            key: id("schema16.term.get-key", "a"),
        },
    );
    let native_map_get = adapter
        .term(&map_get, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(matches!(&native_map_get, Term::Apply { label, arguments }
        if label.name == "project:Int"
            && matches!(arguments.as_slice(), [Term::Apply { label, arguments }]
                if label.name == "Map:lookup" && arguments.len() == 2)));
    let map_in_keys = DefinitionTerm::typed_map(
        node("schema16.term.map-in-keys"),
        DefinitionSortRef::bool(),
        MapOperands::InKeys {
            key: id("schema16.term.in-keys-key", "a"),
            map: DefinitionTerm::map(node("schema16.term.in-keys-map"), MapOperands::Empty),
        },
    );
    let native_map_in_keys = adapter
        .term(&map_in_keys, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(
        matches!(&native_map_in_keys, Term::Apply { label, arguments }
        if label.name == "_in_keys(_)_MAP_Bool_KItem_Map" && arguments.len() == 2)
    );

    let set_empty = DefinitionTerm::set(
        node("schema16.term.empty-set"),
        DefinitionSortRef::set(),
        SetOperands::Empty,
    );
    let set_item = DefinitionTerm::set(
        node("schema16.term.set-item"),
        DefinitionSortRef::set(),
        SetOperands::Item {
            element: int("schema16.term.set-value", "7"),
        },
    );
    let set_concat = DefinitionTerm::set(
        node("schema16.term.set-concat"),
        DefinitionSortRef::set(),
        SetOperands::Concat {
            left: set_item,
            right: set_empty,
        },
    );
    let set_contains = DefinitionTerm::set(
        node("schema16.term.set-contains"),
        DefinitionSortRef::bool(),
        SetOperands::Contains {
            element: int("schema16.term.set-member", "7"),
            set: set_concat,
        },
    );
    let native_set_contains = adapter
        .term(&set_contains, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(
        matches!(&native_set_contains, Term::Apply { label, arguments }
        if label.name == "Set:in"
            && matches!(arguments.get(1), Some(Term::Apply { label, .. }) if label.name == "_Set_"))
    );

    let list_empty = DefinitionTerm::list(
        node("schema11.term.empty-list"),
        DefinitionSortRef::list(),
        ListOperands::Empty,
    );
    let list_item = DefinitionTerm::list(
        node("schema11.term.list-item"),
        DefinitionSortRef::list(),
        ListOperands::Item {
            element: int("schema11.term.list-value", "7"),
        },
    );
    let list_concat = DefinitionTerm::list(
        node("schema11.term.list-concat"),
        DefinitionSortRef::list(),
        ListOperands::Concat {
            left: list_item.clone(),
            right: list_empty.clone(),
        },
    );
    let list_get = DefinitionTerm::list(
        node("schema11.term.list-get"),
        DefinitionSortRef::int(),
        ListOperands::Get {
            list: list_concat.clone(),
            index: int("schema11.term.list-index", "0"),
        },
    );
    let list_update = DefinitionTerm::list(
        node("schema11.term.list-update"),
        DefinitionSortRef::list(),
        ListOperands::Update {
            list: list_concat.clone(),
            index: int("schema11.term.list-update-index", "0"),
            value: int("schema11.term.list-update-value", "8"),
        },
    );
    let list_size = DefinitionTerm::list(
        node("schema11.term.list-size"),
        DefinitionSortRef::int(),
        ListOperands::Size { list: list_concat },
    );
    let list_make = DefinitionTerm::list(
        node("schema27.term.list-make"),
        DefinitionSortRef::list(),
        ListOperands::Make {
            length: int("schema27.term.list-make-length", "3"),
            value: int("schema27.term.list-make-value", "7"),
        },
    );
    let list_range = DefinitionTerm::list(
        node("schema25.term.list-range"),
        DefinitionSortRef::list(),
        ListOperands::Range {
            list: list_empty.clone(),
            from_front: int("schema25.term.list-range-front", "1"),
            from_back: int("schema25.term.list-range-back", "2"),
        },
    );
    let list_update_all = DefinitionTerm::list(
        node("schema25.term.list-update-all"),
        DefinitionSortRef::list(),
        ListOperands::UpdateAll {
            list: list_empty.clone(),
            index: int("schema25.term.list-update-all-index", "1"),
            replacement: list_empty,
        },
    );
    let native_list_get = adapter
        .term(&list_get, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(matches!(&native_list_get, Term::Apply { label, arguments }
        if label.name == "project:Int"
            && matches!(arguments.as_slice(), [Term::Apply { label, arguments }]
                if label.name == "List:get"
                    && matches!(arguments.first(), Some(Term::Apply { label, .. })
                        if label.name == "_List_"))));
    let native_list_update = adapter
        .term(&list_update, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(
        matches!(&native_list_update, Term::Apply { label, arguments }
        if label.name == "List:set" && arguments.len() == 3)
    );
    let native_list_size = adapter
        .term(&list_size, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(matches!(&native_list_size, Term::Apply { label, arguments }
        if label.name == "sizeList" && arguments.len() == 1));
    let native_list_make = adapter
        .term(&list_make, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(matches!(&native_list_make, Term::Apply { label, arguments }
        if label.name == "makeList(_,_)_LIST_List_Int_KItem" && arguments.len() == 2));
    let native_list_range = adapter
        .term(&list_range, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(
        matches!(&native_list_range, Term::Apply { label, arguments }
        if label.name == "List:range" && arguments.len() == 3)
    );
    let native_list_update_all = adapter
        .term(&list_update_all, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    assert!(
        matches!(&native_list_update_all, Term::Apply { label, arguments }
        if label.name == "updateList(_,_,_)_LIST_List_List_Int_List"
            && arguments.len() == 3)
    );

    let rewrite = DefinitionTerm::rewrite(
        node("schema9.term.map-rewrite"),
        DefinitionSortRef::map(),
        item,
        update,
    )
    .unwrap();
    let condition = DefinitionTerm::application(
        node("schema9.term.not"),
        DefinitionSortRef::bool(),
        ApplicationRef::Builtin(BuiltinOperation::BoolNot),
        vec![
            DefinitionTerm::token(node("schema9.term.true"), DefinitionSortRef::bool(), "true")
                .unwrap(),
        ],
    );
    let rule = RuleSentence::new(
        node("schema9.rule.map"),
        LabelIdentity::new(LabelId::new("schema9.rule.map").unwrap(), "schema9-map").unwrap(),
        SentenceKind::Transition,
        Vec::new(),
        rewrite,
    )
    .unwrap()
    .with_requires(Some(
        DefinitionRuleCondition::new(node("schema9.rule.map.requires"), condition).into(),
    ))
    .unwrap();
    let module = DefinitionModule::new(
        node("schema9.module.builtins"),
        ModuleId::new("SCHEMA9-BUILTINS").unwrap(),
        Vec::new(),
        Vec::new(),
        vec![DefinitionSentence::Rule(rule)],
    );
    assert_eq!(
        builtin_imports(&module, ImportPolicy::NativeFrontend),
        ["BOOL", "ID-SYNTAX", "INT", "MAP"].into_iter().collect()
    );
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One literal case per collection operation keeps the native labels an independent oracle."
)]
fn every_collection_operation_has_its_native_label() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let int = |key: &str, value: &str| {
        DefinitionTerm::token(node(key), DefinitionSortRef::int(), value).unwrap()
    };
    let map = |key: &str| DefinitionTerm::map(node(key), MapOperands::Empty);
    let list =
        |key: &str| DefinitionTerm::list(node(key), DefinitionSortRef::list(), ListOperands::Empty);
    let set =
        |key: &str| DefinitionTerm::set(node(key), DefinitionSortRef::set(), SetOperands::Empty);
    let cases = [
        (map("labels.map.empty"), ".Map", 0),
        (
            DefinitionTerm::map(
                node("labels.map.update"),
                MapOperands::Update {
                    map: map("labels.map.update.map"),
                    key: int("labels.map.update.key", "1"),
                    value: int("labels.map.update.value", "2"),
                },
            ),
            "Map:update",
            3,
        ),
        (
            DefinitionTerm::typed_map(
                node("labels.map.in-keys"),
                DefinitionSortRef::bool(),
                MapOperands::InKeys {
                    key: int("labels.map.in-keys.key", "1"),
                    map: map("labels.map.in-keys.map"),
                },
            ),
            "_in_keys(_)_MAP_Bool_KItem_Map",
            2,
        ),
        (list("labels.list.empty"), ".List", 0),
        (
            DefinitionTerm::list(
                node("labels.list.item"),
                DefinitionSortRef::list(),
                ListOperands::Item {
                    element: int("labels.list.item.element", "1"),
                },
            ),
            "ListItem",
            1,
        ),
        (
            DefinitionTerm::list(
                node("labels.list.concat"),
                DefinitionSortRef::list(),
                ListOperands::Concat {
                    left: list("labels.list.concat.left"),
                    right: list("labels.list.concat.right"),
                },
            ),
            "_List_",
            2,
        ),
        (
            DefinitionTerm::list(
                node("labels.list.update"),
                DefinitionSortRef::list(),
                ListOperands::Update {
                    list: list("labels.list.update.list"),
                    index: int("labels.list.update.index", "0"),
                    value: int("labels.list.update.value", "1"),
                },
            ),
            "List:set",
            3,
        ),
        (
            DefinitionTerm::list(
                node("labels.list.size"),
                DefinitionSortRef::int(),
                ListOperands::Size {
                    list: list("labels.list.size.list"),
                },
            ),
            "sizeList",
            1,
        ),
        (
            DefinitionTerm::list(
                node("labels.list.make"),
                DefinitionSortRef::list(),
                ListOperands::Make {
                    length: int("labels.list.make.length", "2"),
                    value: int("labels.list.make.value", "1"),
                },
            ),
            "makeList(_,_)_LIST_List_Int_KItem",
            2,
        ),
        (
            DefinitionTerm::list(
                node("labels.list.range"),
                DefinitionSortRef::list(),
                ListOperands::Range {
                    list: list("labels.list.range.list"),
                    from_front: int("labels.list.range.front", "0"),
                    from_back: int("labels.list.range.back", "0"),
                },
            ),
            "List:range",
            3,
        ),
        (
            DefinitionTerm::list(
                node("labels.list.update-all"),
                DefinitionSortRef::list(),
                ListOperands::UpdateAll {
                    list: list("labels.list.update-all.list"),
                    index: int("labels.list.update-all.index", "0"),
                    replacement: list("labels.list.update-all.replacement"),
                },
            ),
            "updateList(_,_,_)_LIST_List_List_Int_List",
            3,
        ),
        (set("labels.set.empty"), ".Set", 0),
        (
            DefinitionTerm::set(
                node("labels.set.item"),
                DefinitionSortRef::set(),
                SetOperands::Item {
                    element: int("labels.set.item.element", "1"),
                },
            ),
            "SetItem",
            1,
        ),
        (
            DefinitionTerm::set(
                node("labels.set.concat"),
                DefinitionSortRef::set(),
                SetOperands::Concat {
                    left: set("labels.set.concat.left"),
                    right: set("labels.set.concat.right"),
                },
            ),
            "_Set_",
            2,
        ),
        (
            DefinitionTerm::set(
                node("labels.set.union"),
                DefinitionSortRef::set(),
                SetOperands::Union {
                    left: set("labels.set.union.left"),
                    right: set("labels.set.union.right"),
                },
            ),
            "_|Set__SET_Set_Set_Set",
            2,
        ),
        (
            DefinitionTerm::set(
                node("labels.set.contains"),
                DefinitionSortRef::bool(),
                SetOperands::Contains {
                    element: int("labels.set.contains.element", "1"),
                    set: set("labels.set.contains.set"),
                },
            ),
            "Set:in",
            2,
        ),
    ];
    for (term, expected, arity) in cases {
        let native = adapter
            .term(&term, MODULE, 0, Vec::new(), TermContext::Normal)
            .unwrap();
        assert!(
            matches!(&native, Term::Apply { label, arguments }
                if label.name == expected && arguments.len() == arity),
            "{expected}"
        );
    }
}

#[test]
fn pinned_native_prelude_exposes_the_collection_labels_used_by_the_adapter() {
    let adapted = adapt_definition(&smoke_definition()).unwrap();
    let loaded = prepare_definition(adapted.definition, Backend::Llvm).unwrap();
    let labels = loaded
        .definition()
        .modules
        .iter()
        .flat_map(|module| module.local_sentences.iter())
        .filter_map(|sentence| match &**sentence {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.name.as_str()),
            _ => None,
        })
        .collect::<std::collections::BTreeSet<_>>();
    let catalog_labels = MapOperation::ALL
        .iter()
        .map(|operation| operation.spec().k_label)
        .chain(
            ListOperation::ALL
                .iter()
                .map(|operation| operation.spec().k_label),
        )
        .chain(
            SetOperation::ALL
                .iter()
                .map(|operation| operation.spec().k_label),
        )
        .chain([MapOperation::CONCATENATION.k_label]);
    for expected in catalog_labels {
        assert!(
            labels.contains(expected),
            "missing native prelude label {expected}"
        );
    }
    let update_all_labels = loaded
        .definition()
        .modules
        .iter()
        .flat_map(|module| module.local_sentences.iter())
        .filter_map(|sentence| match &**sentence {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if attributes.get_str("hook") == Some("LIST.updateAll") => Some(label.name.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        update_all_labels,
        ["updateList(_,_,_)_LIST_List_List_Int_List"]
    );
}

#[test]
fn pinned_native_prelude_evaluates_set_union() {
    let artifacts = compile_definition(&smoke_definition(), CompileOptions::default()).unwrap();
    let mut backend = NativeBackend::new(
        &artifacts.definition_kore,
        "SMOKE",
        BackendOptions::default(),
    )
    .unwrap();
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let item = |value: i32| {
        format!(
            "LblSetItem{{}}(inj{{SortInt{{}}, SortKItem{{}}}}(\\dv{{SortInt{{}}}}(\"{value}\")))"
        )
    };
    for (right, expected_items) in [(1, 1), (2, 2)] {
        let union = DefinitionTerm::set(
            node("set.union.execution"),
            DefinitionSortRef::set(),
            SetOperands::from_operands(
                SetOperation::Union,
                [1, right]
                    .into_iter()
                    .map(|value| {
                        DefinitionTerm::set(
                            node("set.item.execution"),
                            DefinitionSortRef::set(),
                            SetOperands::Item {
                                element: DefinitionTerm::token(
                                    node("set.value.execution"),
                                    DefinitionSortRef::int(),
                                    value.to_string(),
                                )
                                .unwrap(),
                            },
                        )
                    })
                    .collect(),
            )
            .unwrap(),
        );
        let lowered = adapter
            .term(&union, MODULE, 0, Vec::new(), TermContext::Normal)
            .unwrap();
        assert!(
            matches!(&lowered, Term::Apply { label, .. } if label.name == "_|Set__SET_Set_Set_Set")
        );
        let pattern = format!(
            "Lbl'UndsPipe'Set'UndsUnds'SET'Unds'Set'Unds'Set'Unds'Set{{}}({}, {})",
            item(1),
            item(right)
        );
        let result = backend
            .execute(ExecuteRequest::new(parse_pattern(&pattern).unwrap()))
            .unwrap();
        assert_eq!(result.leaves.len(), 1, "{result:#?}");
        let rendered = result.leaves[0].state.to_string();
        assert!(
            !rendered.contains("Pipe"),
            "union remained unevaluated: {rendered}"
        );
        assert_eq!(
            rendered.matches("LblSetItem").count(),
            expected_items,
            "{rendered}"
        );
    }
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "Checks grammar items, attributes, and groups in one complete definition."
)]
fn grammar_items_attributes_and_group_sentences_map_structurally() {
    let definition = smoke_definition();
    let application_group = ProductionGroupId::new("group.application").unwrap();
    let atom_group = ProductionGroupId::new("group.atom").unwrap();
    let empty_group = ProductionGroupId::new("group.empty").unwrap();
    let left = ProductionFieldId::new("left").unwrap();
    let right = ProductionFieldId::new("right").unwrap();
    let production = ProductionSentence::new(
        node("schema9.production.apply"),
        symbol(
            "schema9.production.apply",
            "applyTwice",
            SymbolKind::Production,
        ),
        DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
        vec![
            IrProductionItem::terminal(node("schema9.production.apply.open"), "twice(").unwrap(),
            IrProductionItem::non_terminal(
                node("schema9.production.apply.left"),
                left,
                DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
            ),
            IrProductionItem::terminal(node("schema9.production.apply.comma"), ",").unwrap(),
            IrProductionItem::non_terminal(
                node("schema9.production.apply.right"),
                right.clone(),
                DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
            ),
            IrProductionItem::terminal(node("schema9.production.apply.close"), ")").unwrap(),
        ],
        vec![
            DefinitionProductionAttribute::Group {
                origin: node("schema9.production.apply.group"),
                group: application_group.clone(),
            },
            DefinitionProductionAttribute::Format {
                origin: node("schema9.production.apply.format"),
                fragments: vec![
                    FormatFragment::Item(1),
                    FormatFragment::Item(2),
                    FormatFragment::Literal(" ".to_owned()),
                    FormatFragment::Item(4),
                    FormatFragment::Item(5),
                ],
            },
            DefinitionProductionAttribute::Strictness {
                origin: node("schema9.production.apply.strictness"),
                kind: StrictnessKind::SeqStrict,
                using: None,
                fields: vec![ProductionFieldReference::new(
                    node("schema9.production.apply.strict-field"),
                    right,
                )],
                result_sort: ProductionResultSort::new(
                    node("schema9.production.apply.result-sort"),
                    DefinitionSortRef::declared(SymbolId::new("sort.kresult").unwrap()),
                ),
            },
        ],
    )
    .unwrap();
    let atom = ProductionSentence::new(
        node("schema9.production.unit"),
        symbol(
            "schema9.production.unit",
            "unitValue",
            SymbolKind::Production,
        ),
        DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
        vec![IrProductionItem::terminal(node("schema9.production.unit.text"), "unit").unwrap()],
        vec![DefinitionProductionAttribute::Group {
            origin: node("schema9.production.unit.group"),
            group: atom_group.clone(),
        }],
    )
    .unwrap();
    let main = &definition.modules()[0];
    let main = DefinitionModule::new(
        main.origin().clone(),
        main.id().clone(),
        main.imports().iter().cloned().collect(),
        [
            (application_group.clone(), "application"),
            (atom_group.clone(), "atom"),
            (empty_group.clone(), "empty"),
        ]
        .into_iter()
        .map(|(id, name)| {
            ProductionGroupIdentity::new(node(&format!("schema9.group.{name}")), id, name).unwrap()
        })
        .collect(),
        main.sentences()
            .iter()
            .cloned()
            .chain([
                DefinitionSentence::Production(production.clone()),
                DefinitionSentence::Production(atom),
            ])
            .collect(),
    );
    let definition = DefinitionIr::new(
        definition.main_module().clone(),
        vec![main, definition.modules()[1].clone()],
    )
    .unwrap();
    let mut adapter = Adapter::new(&definition, true);
    let native = adapter.production(&production, MODULE, 0).unwrap();
    let Sentence::Production {
        label: Some(label),
        items,
        attributes,
        ..
    } = native
    else {
        panic!("grammar production must remain native")
    };
    assert_eq!(label.name, "applyTwice");
    // Non-terminals stay unnamed, as in the emitted K, so k-rust derives no
    // record production (`applyTwice(... left: L, right: R)`).
    assert!(matches!(
        items[1],
        ProductionItem::NonTerminal { name: None, .. }
    ));
    assert!(matches!(
        items[3],
        ProductionItem::NonTerminal { name: None, .. }
    ));
    assert_eq!(attributes.get_str("group"), Some("application"));
    assert_eq!(attributes.get_str("format"), Some("%1%2 %4%5"));
    assert_eq!(attributes.get_str("seqstrict"), Some("2"));
    assert_eq!(attributes.get_str("result"), Some("KResult"));

    let token_with = |precede_regex: Option<&str>| {
        ProductionSentence::new(
            node("schema9.production.integer-token"),
            symbol(
                "schema9.production.integer-token",
                "integerToken",
                SymbolKind::Production,
            ),
            DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
            vec![
                IrProductionItem::regex_terminal(
                    node("schema9.production.integer-token.regex"),
                    precede_regex.map(str::to_owned),
                    "[0-9]+",
                    None,
                )
                .unwrap(),
            ],
            vec![DefinitionProductionAttribute::Token {
                origin: node("schema9.production.integer-token.attribute"),
                lexical_precedence: Some(120),
            }],
        )
        .unwrap()
    };
    // k-rust reads a regex terminal as its regex alone, so a guard is refused, not dropped.
    assert!(matches!(
        adapter.production(&token_with(Some("[A-Za-z0-9_]")), MODULE, 1),
        Err(AdapterError::TokenRegexGuard { key })
            if key.as_str() == "schema9.production.integer-token.regex"
    ));
    let native_token = adapter.production(&token_with(None), MODULE, 1).unwrap();
    assert!(
        matches!(native_token, Sentence::Production { label: None, items, attributes, .. }
        if matches!(items.as_slice(), [ProductionItem::RegexTerminal { regex, .. }] if regex == "[0-9]+")
            && attributes.get("token").is_some()
            && attributes.get_str("prec") == Some("120"))
    );

    let precedence = DefinitionSentence::Precedence(
        PrecedenceRelation::new(
            node("schema9.precedence"),
            vec![atom_group.clone()],
            vec![application_group.clone()],
        )
        .unwrap(),
    );
    assert!(matches!(adapter.sentence(&precedence, MODULE, 2).unwrap(),
        Sentence::SyntaxPriority { priorities, .. }
            if priorities == vec![vec!["unitValue".to_owned()], vec!["applyTwice".to_owned()]]));
    let associativity = DefinitionSentence::Associativity(
        GroupAssociativitySentence::new(
            node("schema9.associativity"),
            GroupAssociativity::Left,
            vec![application_group],
        )
        .unwrap(),
    );
    assert!(
        matches!(adapter.sentence(&associativity, MODULE, 3).unwrap(),
        Sentence::SyntaxAssociativity { tags, .. } if tags == vec!["applyTwice"])
    );
    // K rejects a tag no production carries; so does the adapter.
    let empty = DefinitionSentence::Associativity(
        GroupAssociativitySentence::new(
            node("schema9.associativity.empty"),
            GroupAssociativity::NonAssociative,
            vec![empty_group],
        )
        .unwrap(),
    );
    assert!(matches!(
        adapter.sentence(&empty, MODULE, 4),
        Err(AdapterError::EmptyProductionGroup { group, .. }) if group == "empty"
    ));
}

#[test]
fn fixed_configuration_preserves_config_variables_and_cell_properties() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let cell = SymbolId::new("schema9.cell.k").unwrap();
    let program = semantic_id("program");
    let value_sort = DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap());
    let initializer = DefinitionTerm::k_sequence(
        node("schema9.configuration.initializer.sequence"),
        value_sort.clone(),
        vec![DefinitionTerm::variable(
            node("schema9.configuration.initializer.program"),
            value_sort.clone(),
            program.clone(),
        )],
    );
    let fixed = FixedConfiguration::new(
        node("schema9.configuration"),
        semantic_id("configuration.machine"),
        ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::leaf(
                node("schema9.configuration.cell.k"),
                cell.clone(),
                "k",
                vec![
                    CellAttribute::color(node("schema9.configuration.cell.k.color"), "yellow")
                        .unwrap(),
                ],
                DefinitionSortRef::k_sequence(),
            )
            .unwrap(),
        ],
        node("schema9.configuration.initializer"),
        semantic_id("initializer.machine"),
        vec![
            FixedConfigurationVariable::new(
                node("schema9.configuration.variable.program"),
                program,
                "PGM",
                value_sort,
                true,
            )
            .unwrap(),
        ],
        vec![FixedInitializerCell::term(
            node("schema9.configuration.initializer.cell.k"),
            cell,
            initializer,
        )],
    )
    .unwrap();
    let native = adapter.configuration(&fixed, MODULE, 0).unwrap();
    let Sentence::Configuration { body, .. } = native else {
        panic!("fixed configuration must remain native")
    };
    let mut saw_program = false;
    let mut saw_program_cast = false;
    let mut property_names = Vec::new();
    body.visit_preorder(&mut |term| {
        if matches!(term, Term::Apply { label, .. } if label.name == "#SemanticCastToValue") {
            saw_program_cast = true;
        }
        if let Term::Token { token, sort } = term {
            if token == "$PGM" && sort.name == "KConfigVar" {
                saw_program = true;
            }
            if sort.name == "#CellName" {
                property_names.push(token.clone());
            }
        }
    });
    assert!(
        saw_program,
        "configuration variables remain native KConfigVar tokens"
    );
    assert!(
        saw_program_cast,
        "configuration variables retain their authored term sort"
    );
    assert!(property_names.iter().any(|name| name == "color"));
    assert!(property_names.iter().any(|name| name == "maincell"));
    assert!(adapter.origins.iter().any(|mapping| {
        mapping.key.as_str() == "schema9.configuration.cell.k"
            && matches!(
                mapping.place,
                NativeNodePlace::Sentence {
                    role: SentenceNodeRole::ConfigurationCell,
                    ..
                }
            )
    }));
}

fn nested_cell_definition(parent: &SymbolId, left: &SymbolId, right: &SymbolId) -> DefinitionIr {
    let children = [(left.clone(), "left", "1"), (right.clone(), "right", "2")];
    let configuration = FixedConfiguration::new(
        node("schema26.configuration"),
        semantic_id("schema26.configuration"),
        ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::nested(
                node("schema26.cell.parent.declaration"),
                parent.clone(),
                "parent",
                Vec::new(),
                children
                    .iter()
                    .map(|(id, name, _)| {
                        FixedCell::leaf(
                            node(&format!("schema26.cell.{name}.declaration")),
                            id.clone(),
                            *name,
                            Vec::new(),
                            DefinitionSortRef::int(),
                        )
                        .unwrap()
                    })
                    .collect(),
            )
            .unwrap(),
        ],
        node("schema26.initializer"),
        semantic_id("schema26.initializer"),
        Vec::new(),
        vec![
            FixedInitializerCell::children(
                node("schema26.cell.parent.initializer"),
                parent.clone(),
                children
                    .iter()
                    .map(|(id, name, value)| {
                        FixedInitializerCell::term(
                            node(&format!("schema26.cell.{name}.initializer")),
                            id.clone(),
                            DefinitionTerm::token(
                                node(&format!("schema26.cell.{name}.initializer.body")),
                                DefinitionSortRef::int(),
                                *value,
                            )
                            .unwrap(),
                        )
                    })
                    .collect(),
            )
            .unwrap(),
        ],
    )
    .unwrap();
    let module_id = ModuleId::new(MODULE).unwrap();
    DefinitionIr::new(
        module_id.clone(),
        vec![DefinitionModule::new(
            node("schema26.module"),
            module_id,
            Vec::new(),
            Vec::new(),
            vec![DefinitionSentence::Configuration(configuration)],
        )],
    )
    .unwrap()
}

#[test]
fn complete_cell_terms_use_the_pinned_frontend_structured_shape() {
    fn cell_body<'a>(term: &'a Term, expected_label: &str) -> &'a Term {
        let Term::Apply { label, arguments } = term else {
            panic!("cell term must remain an application")
        };
        assert_eq!(label.name, expected_label);
        let [body] = arguments.as_slice() else {
            panic!("leaf cell must carry its complete structured body")
        };
        body
    }

    let parent = SymbolId::new("schema26.cell.parent").unwrap();
    let left = SymbolId::new("schema26.cell.left").unwrap();
    let right = SymbolId::new("schema26.cell.right").unwrap();
    let definition = nested_cell_definition(&parent, &left, &right);
    let mut adapter = Adapter::new(&definition, true);
    let leaf = |key: &str, cell: SymbolId, value: &str| {
        DefinitionTerm::cell(
            node(key),
            DefinitionSortRef::int(),
            cell,
            vec![
                DefinitionTerm::token(
                    node(&format!("{key}.body")),
                    DefinitionSortRef::int(),
                    value,
                )
                .unwrap(),
            ],
        )
    };
    let term = DefinitionTerm::cell(
        node("schema26.cell.parent.term"),
        DefinitionSortRef::int(),
        parent,
        vec![
            leaf("schema26.cell.left.term", left, "1"),
            leaf("schema26.cell.right.term", right, "2"),
        ],
    );
    let native = adapter
        .term(&term, MODULE, 0, Vec::new(), TermContext::Normal)
        .unwrap();
    let Term::Apply { label, arguments } = &native else {
        panic!("a multi-child parent must remain a complete application")
    };
    assert_eq!(label.name, "<parent>");
    let [left, right] = arguments.as_slice() else {
        panic!("the parent must retain both ordered children")
    };
    assert!(matches!(cell_body(left, "<left>"), Term::Token { token, .. } if token == "1"));
    assert!(matches!(cell_body(right, "<right>"), Term::Token { token, .. } if token == "2"));
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "Builds one claim with an ML precondition and a quantified postcondition."
)]
fn ml_predicates_are_plain_labels_without_sort_parameters() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let existential = semantic_id("r");
    let quantified = semantic_id("q");
    let body = DefinitionTerm::rewrite(
        node("kf039.claim.body"),
        DefinitionSortRef::int(),
        DefinitionTerm::token(node("kf039.claim.zero"), DefinitionSortRef::int(), "0").unwrap(),
        DefinitionTerm::variable(
            node("kf039.claim.r"),
            DefinitionSortRef::int(),
            existential.clone(),
        ),
    )
    .unwrap();
    let equals = |name: &str, left: DefinitionTerm, right: DefinitionTerm| {
        IrMlPredicate::new(
            node(name),
            IrMlKind::Equals {
                operand_sort: DefinitionSortRef::int(),
                left: Box::new(left),
                right: Box::new(right),
            },
        )
    };
    let zero =
        |name: &str| DefinitionTerm::token(node(name), DefinitionSortRef::int(), "0").unwrap();
    // requires #Not ( { 0 #Equals 0 } )
    let requires = IrMlPredicate::new(
        node("kf039.requires"),
        IrMlKind::Not {
            operand: Box::new(equals(
                "kf039.requires.eq",
                zero("kf039.z1"),
                zero("kf039.z2"),
            )),
        },
    );
    // ensures #Exists Q:Int . { ?R #Equals Q }
    let ensures = IrMlPredicate::new(
        node("kf039.ensures"),
        IrMlKind::Exists {
            binder: DefinitionScopedBinder::new(
                node("kf039.ensures.binder"),
                node("kf039.ensures.binder.name"),
                quantified.clone(),
                node("kf039.ensures.binder.sort"),
                DefinitionSortRef::int(),
            ),
            body: Box::new(equals(
                "kf039.ensures.eq",
                DefinitionTerm::variable(
                    node("kf039.ensures.r"),
                    DefinitionSortRef::int(),
                    existential.clone(),
                ),
                DefinitionTerm::variable(
                    node("kf039.ensures.q"),
                    DefinitionSortRef::int(),
                    quantified,
                ),
            )),
        },
    );
    let rule = RuleSentence::new(
        node("kf039.claim"),
        LabelIdentity::new(LabelId::new("kf039.claim").unwrap(), "kf039-claim").unwrap(),
        SentenceKind::Claim,
        Vec::new(),
        body,
    )
    .unwrap()
    .with_claim(Some(DefinitionClaim::new(
        node("kf039.claim.modality"),
        ClaimModality::AllPaths,
        None,
        Vec::new(),
    )))
    .with_existentials(vec![DefinitionScopedBinder::new(
        node("kf039.claim.existential"),
        node("kf039.claim.existential.name"),
        existential,
        node("kf039.claim.existential.sort"),
        DefinitionSortRef::int(),
    )])
    .with_requires(Some(IrCondition::Predicate(requires)))
    .unwrap()
    .with_ensures(Some(IrCondition::Predicate(ensures)));
    let Sentence::Claim {
        requires, ensures, ..
    } = adapter.rule(&rule, MODULE, 0).unwrap()
    else {
        panic!("claims must not be downgraded to rules")
    };
    let mut labels = Vec::new();
    for condition in [&requires, &ensures] {
        condition.visit_preorder(&mut |term| {
            if let Term::Apply { label, .. } = term {
                assert!(
                    label.parameters.is_empty(),
                    "{} carries sort parameters",
                    label.name
                );
                labels.push(label.name.clone());
            }
        });
    }
    assert_eq!(labels, ["#Not", "#Equals", "#Exists", "#Equals"]);
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "Checks related native claim and context forms with shared provenance fixtures."
)]
fn claims_and_context_aliases_preserve_native_forms_and_origin_roles() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let universal = semantic_id("_B__krs_0");
    let existential = semantic_id("n");
    let body = DefinitionTerm::rewrite(
        node("schema9.claim.body"),
        DefinitionSortRef::int(),
        DefinitionTerm::token(node("schema9.claim.zero"), DefinitionSortRef::int(), "0").unwrap(),
        DefinitionTerm::variable(
            node("schema9.claim.existential-use"),
            DefinitionSortRef::int(),
            existential.clone(),
        ),
    )
    .unwrap();
    let claim = DefinitionClaim::new(
        node("schema9.claim.modality"),
        ClaimModality::OnePath,
        Some(node("schema9.claim.circularity")),
        vec![DefinitionScopedBinder::new(
            node("schema9.claim.universal"),
            node("schema9.claim.universal.name"),
            universal.clone(),
            node("schema9.claim.universal.sort"),
            DefinitionSortRef::bool(),
        )],
    );
    let existentials = vec![DefinitionScopedBinder::new(
        node("schema9.claim.existential"),
        node("schema9.claim.existential.name"),
        existential.clone(),
        node("schema9.claim.existential.sort"),
        DefinitionSortRef::int(),
    )];
    let ensures = Some(DefinitionRuleCondition::new(
        node("schema9.claim.ensures"),
        DefinitionTerm::variable(
            node("schema9.claim.anonymous-use"),
            DefinitionSortRef::bool(),
            universal,
        ),
    ));
    let rule = RuleSentence::new(
        node("schema9.claim"),
        LabelIdentity::new(LabelId::new("schema9.claim").unwrap(), "schema9-claim").unwrap(),
        SentenceKind::Claim,
        Vec::new(),
        body,
    )
    .unwrap()
    .with_claim(Some(claim))
    .with_existentials(existentials)
    .with_ensures(ensures.map(Into::into));
    let native_claim = adapter.rule(&rule, MODULE, 0).unwrap();
    let Sentence::Claim {
        body,
        ensures,
        attributes,
        ..
    } = native_claim
    else {
        panic!("claims must not be downgraded to rules")
    };
    let mut variables = Vec::new();
    body.visit_preorder(&mut |term| {
        if let Term::Variable { name, .. } = term {
            variables.push(name.clone());
        }
    });
    ensures.visit_preorder(&mut |term| {
        if let Term::Variable { name, .. } = term {
            variables.push(name.clone());
        }
    });
    assert!(variables.contains(&"?N".to_owned()));
    assert!(variables.contains(&"_B".to_owned()));
    assert!(attributes.get("one-path").is_some());
    assert!(attributes.get("circularity").is_some());
    for role in [
        SentenceNodeRole::ClaimBinder(0),
        SentenceNodeRole::ClaimBinderName(0),
        SentenceNodeRole::ClaimBinderSort(0),
        SentenceNodeRole::ClaimBinder(1),
        SentenceNodeRole::ClaimModality,
        SentenceNodeRole::ClaimCircularity,
        SentenceNodeRole::Ensures,
    ] {
        assert!(adapter.origins.iter().any(|mapping| {
            matches!(&mapping.place, NativeNodePlace::Sentence { role: mapped_role, .. } if mapped_role == &role)
        }));
    }

    // A trusted claim carries the bare `trusted` attribute and maps its marker (KF-042).
    let trusted = DefinitionClaim::new(
        node("schema9.claim.modality"),
        ClaimModality::AllPaths,
        None,
        Vec::new(),
    )
    .with_trusted_origin(Some(node("schema9.claim.trusted")));
    let Sentence::Claim { attributes, .. } = adapter
        .rule(&rule.clone().with_claim(Some(trusted)), MODULE, 1)
        .unwrap()
    else {
        panic!("claims must not be downgraded to rules")
    };
    assert!(attributes.get("trusted").is_some());
    assert!(attributes.get("circularity").is_none());
    assert!(adapter.origins.iter().any(|mapping| {
        matches!(
            &mapping.place,
            NativeNodePlace::Sentence {
                role: SentenceNodeRole::ClaimTrusted,
                ..
            }
        )
    }));

    let here = semantic_id("here");
    let context = ContextAliasSentence::new(
        node("schema9.context"),
        context_alias_id(),
        node("schema9.context.name"),
        "schema9_eval".to_owned(),
        node("schema9.context.here"),
        here.clone(),
        Vec::new(),
        FixedConfigurationPattern::new(
            node("schema9.context.pattern"),
            semantic_id("configuration.machine"),
            vec![FixedCellPattern::new(
                node("schema9.context.cell.k"),
                SymbolId::new("cell.k").unwrap(),
                DefinitionTerm::variable(
                    node("schema9.context.here-use"),
                    DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
                    here,
                ),
                CellContentFrame::KSequenceTail {
                    origin: node("schema9.context.frame"),
                    binding: Some(semantic_id("tail")),
                },
            )],
            Vec::new(),
        )
        .unwrap(),
    );
    let native_context = adapter.context_alias(&context, MODULE, 1).unwrap();
    let Sentence::ContextAlias {
        body, attributes, ..
    } = native_context
    else {
        panic!("context aliases must remain native")
    };
    let mut saw_here = false;
    let mut saw_k_tail = false;
    body.visit_preorder(&mut |term| {
        if matches!(term, Term::Variable { name, .. } if name == "HERE") {
            saw_here = true;
        }
        if matches!(term, Term::Variable { name, sort: Some(sort) }
            if name == "Tail" && sort.name == "K")
        {
            saw_k_tail = true;
        }
    });
    assert!(saw_here);
    assert!(saw_k_tail);
    assert_eq!(attributes.get_str("label"), Some("schema9_eval"));
    assert!(attributes.get("cool-like").is_some());
    for role in [
        SentenceNodeRole::ContextAliasName,
        SentenceNodeRole::ContextAliasHere,
        SentenceNodeRole::ContextAliasCell(0),
        SentenceNodeRole::ContextAliasFrame(0),
    ] {
        assert!(adapter.origins.iter().any(|mapping| {
            matches!(&mapping.place, NativeNodePlace::Sentence { role: mapped_role, .. } if mapped_role == &role)
        }));
    }
}

#[test]
fn alias_clause_relies_on_aliased_production_propagation() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let body = DefinitionTerm::rewrite(
        node("schema9.alias.body"),
        DefinitionSortRef::int(),
        DefinitionTerm::token(node("schema9.alias.left"), DefinitionSortRef::int(), "0").unwrap(),
        DefinitionTerm::token(node("schema9.alias.right"), DefinitionSortRef::int(), "1").unwrap(),
    )
    .unwrap();
    let rule = RuleSentence::new(
        node("schema9.alias"),
        LabelIdentity::new(LabelId::new("schema9.alias").unwrap(), "schema9-alias").unwrap(),
        SentenceKind::Alias,
        Vec::new(),
        body,
    )
    .unwrap();
    let native = adapter.rule(&rule, MODULE, 0).unwrap();
    let Sentence::Rule { attributes, .. } = native else {
        panic!("static alias clauses remain ordinary native rules")
    };
    assert!(
        attributes.get("alias").is_none(),
        "the frontend propagates alias mode from the root production"
    );
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "Checks the complete structural adapter result from one smoke definition."
)]
fn definition_ir_maps_structurally_without_frontend_metadata() {
    let adapted = adapt_definition(&smoke_definition()).expect("the smoke IR must adapt");
    let native = adapted.definition();
    assert_eq!(native.main_module, "SMOKE");
    assert_eq!(native.modules.len(), 2);

    let main = native
        .modules
        .iter()
        .find(|module| module.name == "SMOKE")
        .unwrap();
    assert_eq!(main.imports.len(), 2);
    assert!(
        main.imports
            .iter()
            .any(|import| import.name == "MAP" && import.public)
    );
    assert!(
        main.imports
            .iter()
            .any(|import| import.name == "SMOKE-SYNTAX" && import.public)
    );
    assert_eq!(main.attributes.location(), None);

    let configuration = main
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Configuration { body, .. } => Some(body),
            _ => None,
        })
        .expect("configuration must remain structured");
    let Term::Apply { label, arguments } = configuration else {
        panic!("configuration must use the native structured cell form")
    };
    assert_eq!(label.name, "#configCell");
    assert!(matches!(
        arguments.as_slice(),
        [
            Term::Token { token: start, .. },
            Term::Apply { label: properties, .. },
            Term::Sequence(items),
            Term::Token { token: end, .. }
        ] if start == "k"
            && end == "k"
            && properties.name == "#cellPropertyList"
            && matches!(
                items.as_slice(),
                [Term::Apply { label, arguments }]
                    if label.name == "#SemanticCastToValue"
                        && matches!(arguments.as_slice(), [Term::Token { token, .. }] if token == "$PGM")
            )
    ));

    let rule = main
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Rule {
                body, attributes, ..
            } => Some((body, attributes)),
            _ => None,
        })
        .unwrap();
    assert_eq!(
        rule.1.get_str("label"),
        Some("SMOKE.ORG-EXAMPLE-SMOKE.rules.foo-to-bar")
    );
    assert!(matches!(
        rule.0,
        Term::Rewrite { left, right }
            if matches!(left.unannotated(), Term::Apply { label, .. } if label.name == "Lblfoo")
                && matches!(right.unannotated(), Term::Apply { label, .. } if label.name == "Lblbar")
    ));

    let syntax = native
        .modules
        .iter()
        .find(|module| module.name == "SMOKE-SYNTAX")
        .unwrap();
    let subsorts = syntax
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Production {
                label: None,
                sort,
                items,
                ..
            } => match items.as_slice() {
                [ProductionItem::NonTerminal { sort: child, .. }] => {
                    Some((child.name.as_str(), sort.name.as_str()))
                }
                _ => None,
            },
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(subsorts, vec![("KResult", "KItem"), ("Value", "KResult")]);

    let keys = adapted
        .origins()
        .iter()
        .map(|mapping| mapping.key.as_str())
        .collect::<Vec<_>>();
    for expected in [
        "def.module.main",
        "def.configuration",
        "def.cell.k",
        "def.initializer",
        "def.term.init.sequence",
        "def.term.init.program",
        "def.rule.foo-to-bar",
        "def.term.rule.rewrite",
        "def.term.rule.foo",
        "def.term.rule.bar",
    ] {
        assert!(
            keys.contains(&expected),
            "missing origin seam for {expected}"
        );
    }
    assert!(adapted.origins().iter().any(|mapping| {
        mapping.key.as_str() == "def.term.rule.bar"
            && matches!(&mapping.place, NativeNodePlace::Sentence { role: SentenceNodeRole::Term(path), .. } if path == &[1])
    }));
}

#[test]
fn transition_sentence_is_preserved_as_a_native_rule() {
    let adapted = adapt_definition(&smoke_definition()).expect("transitions adapt natively");
    assert!(adapted.definition().modules.iter().any(|module| {
        module
            .local_sentences
            .iter()
            .any(|sentence| matches!(**sentence, Sentence::Rule { .. }))
    }));
}

/// `concrete(x)`, bare `symbolic`, and `smt_lemma` become the native frontend's
/// `concrete = "X"`, `symbolic = ""`, and `smt-lemma = ""` (KF-043).
#[test]
fn match_restrictions_map_to_native_attributes_with_sentence_names() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let x = semantic_id("x");
    let variable =
        |name: &str| DefinitionTerm::variable(node(name), DefinitionSortRef::int(), x.clone());
    let body = DefinitionTerm::rewrite(
        node("restriction.body"),
        DefinitionSortRef::int(),
        variable("restriction.left"),
        variable("restriction.right"),
    )
    .unwrap();
    let rule = RuleSentence::new(
        node("restriction.rule"),
        LabelIdentity::new(LabelId::new("restriction.rule").unwrap(), "restricted").unwrap(),
        SentenceKind::Equation,
        Vec::new(),
        body,
    )
    .unwrap();
    let restricted = rule
        .clone()
        .with_restriction(Some(krs_ir_levels::IrMatchRestriction::new(
            Some(krs_ir_levels::IrRestriction::new(
                node("restriction.concrete"),
                vec![krs_ir_levels::IrRestrictionVariable::new(
                    node("restriction.concrete.x"),
                    x.clone(),
                )],
            )),
            Some(krs_ir_levels::IrRestriction::new(
                node("restriction.symbolic"),
                Vec::new(),
            )),
            Some(node("restriction.smt-lemma")),
        )));
    let Sentence::Rule {
        body, attributes, ..
    } = adapter.rule(&restricted, MODULE, 0).unwrap()
    else {
        panic!("an equation adapts to a native rule")
    };
    let mut names = Vec::new();
    body.visit_preorder(&mut |term| {
        if let Term::Variable { name, .. } = term {
            names.push(name.clone());
        }
    });
    assert_eq!(attributes.get_str("concrete"), Some(names[0].as_str()));
    assert_eq!(attributes.get_str("symbolic"), Some(""));
    assert_eq!(attributes.get_str("smt-lemma"), Some(""));

    let Sentence::Rule { attributes, .. } = adapter.rule(&rule, MODULE, 1).unwrap() else {
        panic!("an equation adapts to a native rule")
    };
    for key in ["concrete", "symbolic", "smt-lemma"] {
        assert!(attributes.get(key).is_none(), "{key}");
    }
}

/// `name @ pattern` adapts to the AST k-rust's parser builds for
/// `PATTERN #as Alias:Sort` (KF-029).
#[test]
fn pattern_aliases_adapt_to_native_as_terms() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let alias = semantic_id("p");
    let from = DefinitionTerm::pattern_as(
        node("as"),
        DefinitionSortRef::int(),
        alias.clone(),
        DefinitionTerm::variable(
            node("as.pattern"),
            DefinitionSortRef::int(),
            semantic_id("x"),
        ),
    );
    let to = DefinitionTerm::variable(node("as.use"), DefinitionSortRef::int(), alias);
    let rule = RuleSentence::new(
        node("as.rule"),
        LabelIdentity::new(LabelId::new("as.rule").unwrap(), "as-rule").unwrap(),
        SentenceKind::Equation,
        Vec::new(),
        DefinitionTerm::rewrite(node("as.body"), DefinitionSortRef::int(), from, to).unwrap(),
    )
    .unwrap();
    let Sentence::Rule { body, .. } = adapter.rule(&rule, MODULE, 0).unwrap() else {
        panic!("an equation adapts to a native rule")
    };
    let mut aliases = Vec::new();
    body.visit_preorder(&mut |term| {
        if let Term::As { pattern, alias } = term {
            aliases.push((pattern.as_ref().clone(), alias.as_ref().clone()));
        }
    });
    let [(pattern, alias)] = aliases.as_slice() else {
        panic!("one native #as term, found {aliases:?}")
    };
    assert!(matches!(pattern, Term::Variable { name, sort: Some(sort) }
        if name == "X" && sort.name == "Int"));
    assert!(matches!(alias, Term::Variable { name, sort: Some(sort) }
        if name == "P" && sort.name == "Int"));
}

/// `A | B | C` adapts to the AST k-rust's parser builds for `A #Or B #Or C`:
/// binary `#Or` nested to the left, with no label sort parameter (KF-030).
#[test]
fn or_patterns_adapt_to_left_nested_native_or() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let alternative = |name: &str| {
        DefinitionTerm::variable(node(name), DefinitionSortRef::int(), semantic_id("x"))
    };
    let from = DefinitionTerm::pattern_or(
        node("or"),
        DefinitionSortRef::int(),
        krs_ir::AtLeastTwo::new(
            alternative("or.0"),
            alternative("or.1"),
            vec![alternative("or.2")],
        ),
    );
    let to = DefinitionTerm::variable(node("or.use"), DefinitionSortRef::int(), semantic_id("x"));
    let rule = RuleSentence::new(
        node("or.rule"),
        LabelIdentity::new(LabelId::new("or.rule").unwrap(), "or-rule").unwrap(),
        SentenceKind::Equation,
        Vec::new(),
        DefinitionTerm::rewrite(node("or.body"), DefinitionSortRef::int(), from, to).unwrap(),
    )
    .unwrap();
    let Sentence::Rule { body, .. } = adapter.rule(&rule, MODULE, 0).unwrap() else {
        panic!("an equation adapts to a native rule")
    };
    let mut ors = Vec::new();
    body.visit_preorder(&mut |term| {
        if let Term::Apply { label, arguments } = term
            && label.name == "#Or"
        {
            assert!(label.parameters.is_empty(), "{label:?}");
            ors.push(arguments.clone());
        }
    });
    let [outer, inner] = ors.as_slice() else {
        panic!("two binary native #Or terms, found {ors:?}")
    };
    assert!(matches!(&outer[0], Term::Apply { label, .. } if label.name == "#Or"));
    assert!(matches!(&outer[1], Term::Variable { name, .. } if name == "X"));
    assert!(
        inner
            .iter()
            .all(|term| matches!(term, Term::Variable { name, .. } if name == "X"))
    );
}

/// `k::matches!(e, P)` adapts to the AST k-rust's parser builds for
/// `P :=K E`: `_:=K_` with the pattern first and no label sort parameter, so
/// k-rust's `resolve_fun` generates the lambda (KF-031).
#[test]
fn matches_adapt_to_native_k_equals_k_with_the_pattern_first() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let local = krs_ir::SemanticId::local("x", 1).unwrap();
    let pattern = DefinitionTerm::variable(
        node("matches.pattern"),
        DefinitionSortRef::int(),
        local.clone(),
    );
    let subject = DefinitionTerm::variable(
        node("matches.subject"),
        DefinitionSortRef::int(),
        semantic_id("x"),
    );
    let test = DefinitionTerm::matches(
        node("matches"),
        DefinitionSortRef::bool(),
        subject,
        pattern,
        vec![local],
    );
    let from = DefinitionTerm::variable(
        node("matches.from"),
        DefinitionSortRef::int(),
        semantic_id("x"),
    );
    let rule = RuleSentence::new(
        node("matches.rule"),
        LabelIdentity::new(LabelId::new("matches.rule").unwrap(), "matches-rule").unwrap(),
        SentenceKind::Equation,
        Vec::new(),
        DefinitionTerm::rewrite(node("matches.body"), DefinitionSortRef::int(), from, test)
            .unwrap(),
    )
    .unwrap();
    let Sentence::Rule { body, .. } = adapter.rule(&rule, MODULE, 0).unwrap() else {
        panic!("an equation adapts to a native rule")
    };
    let mut tests = Vec::new();
    body.visit_preorder(&mut |term| {
        if let Term::Apply { label, arguments } = term
            && label.name == "_:=K_"
        {
            assert!(label.parameters.is_empty(), "{label:?}");
            tests.push(arguments.clone());
        }
    });
    let [arguments] = tests.as_slice() else {
        panic!("one native `_:=K_` term, found {tests:?}")
    };
    let [pattern, subject] = arguments.as_slice() else {
        panic!("`_:=K_` is binary, found {arguments:?}")
    };
    // The local binder takes a name distinct from the rule's `x`.
    assert!(matches!(pattern, Term::Variable { name, .. } if name == "X_2"));
    assert!(matches!(subject, Term::Variable { name, .. } if name == "X"));
}

/// A `let` statement adapts to the AST k-rust's parser builds for
/// `#let P = A #in B`: `#let(P, A, B)` with no label sort parameter, the
/// argument order `resolve_fun` reads (KF-032).
#[test]
fn lets_adapt_to_native_let_with_pattern_value_body_order() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let local = krs_ir::SemanticId::local("x", 1).unwrap();
    let pattern =
        DefinitionTerm::variable(node("let.pattern"), DefinitionSortRef::int(), local.clone());
    let value = DefinitionTerm::variable(
        node("let.value"),
        DefinitionSortRef::int(),
        semantic_id("x"),
    );
    let body = DefinitionTerm::variable(node("let.body"), DefinitionSortRef::int(), local.clone());
    let binding = DefinitionTerm::let_binding(
        node("let"),
        DefinitionSortRef::int(),
        pattern,
        value,
        body,
        vec![local],
    );
    let from =
        DefinitionTerm::variable(node("let.from"), DefinitionSortRef::int(), semantic_id("x"));
    let rule = RuleSentence::new(
        node("let.rule"),
        LabelIdentity::new(LabelId::new("let.rule").unwrap(), "let-rule").unwrap(),
        SentenceKind::Equation,
        Vec::new(),
        DefinitionTerm::rewrite(
            node("let.body.rule"),
            DefinitionSortRef::int(),
            from,
            binding,
        )
        .unwrap(),
    )
    .unwrap();
    let Sentence::Rule { body, .. } = adapter.rule(&rule, MODULE, 0).unwrap() else {
        panic!("an equation adapts to a native rule")
    };
    let mut lets = Vec::new();
    body.visit_preorder(&mut |term| {
        if let Term::Apply { label, arguments } = term
            && label.name == "#let"
        {
            assert!(label.parameters.is_empty(), "{label:?}");
            lets.push(arguments.clone());
        }
    });
    let [arguments] = lets.as_slice() else {
        panic!("one native `#let` term, found {lets:?}")
    };
    let [pattern, value, body] = arguments.as_slice() else {
        panic!("`#let` is ternary, found {arguments:?}")
    };
    // The local binder takes a name distinct from the rule's `x`.
    assert!(matches!(pattern, Term::Variable { name, .. } if name == "X_2"));
    assert!(matches!(value, Term::Variable { name, .. } if name == "X"));
    assert!(matches!(body, Term::Variable { name, .. } if name == "X_2"));
}

/// An equation's function context adapts to k-rust's
/// `#withConfig(F => R, #cells(..))`, the structure its parser builds for
/// `[[ F => R ]] <cells>`; KRS adds no argument to the function (KF-025).
#[test]
fn function_contexts_adapt_to_native_with_config() {
    let definition = smoke_definition();
    let mut adapter = Adapter::new(&definition, true);
    let b = semantic_id("b");
    let body = DefinitionTerm::rewrite(
        node("context.body"),
        DefinitionSortRef::int(),
        DefinitionTerm::token(node("context.left"), DefinitionSortRef::int(), "0").unwrap(),
        DefinitionTerm::variable(node("context.right"), DefinitionSortRef::int(), b.clone()),
    )
    .unwrap();
    let rule = RuleSentence::new(
        node("context.rule"),
        LabelIdentity::new(LabelId::new("context.rule").unwrap(), "context").unwrap(),
        SentenceKind::Equation,
        Vec::new(),
        body,
    )
    .unwrap()
    .with_function_context(Some(krs_ir_levels::DefinitionFunctionContext::new(
        node("context.parameter"),
        FixedConfigurationPattern::new(
            node("context.cells"),
            semantic_id("configuration.machine"),
            vec![FixedCellPattern::new(
                node("context.cell.k"),
                SymbolId::new("cell.k").unwrap(),
                DefinitionTerm::variable(node("context.cell.read"), DefinitionSortRef::int(), b),
                CellContentFrame::KSequenceTail {
                    origin: node("context.frame"),
                    binding: None,
                },
            )],
            Vec::new(),
        )
        .unwrap(),
    )));
    let Sentence::Rule { body, .. } = adapter.rule(&rule, MODULE, 0).unwrap() else {
        panic!("an equation adapts to a native rule")
    };
    let Term::Apply {
        label, arguments, ..
    } = body.unannotated()
    else {
        panic!("a function context wraps the body: {body:?}")
    };
    assert_eq!(label.name, "#withConfig");
    assert_eq!(arguments.len(), 2);
    assert!(matches!(arguments[0].unannotated(), Term::Rewrite { .. }));
    assert!(matches!(
        arguments[1].unannotated(),
        Term::Apply { label, .. } if label.name == "#cells" || label.name == "<k>"
    ));
    for role in [
        SentenceNodeRole::FunctionContext,
        SentenceNodeRole::FunctionContextCell(0),
        SentenceNodeRole::FunctionContextFrame(0),
    ] {
        assert!(adapter.origins.iter().any(|mapping| {
            matches!(&mapping.place, NativeNodePlace::Sentence { role: mapped_role, .. } if mapped_role == &role)
        }));
    }
}
