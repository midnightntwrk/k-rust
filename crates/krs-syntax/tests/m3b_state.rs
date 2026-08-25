//! Schema-v3 fixed-state authoring parser freeze.

use krs_syntax::{
    ConfigurationCellContent, InitializerCellContent, KSequenceNotation, MapBody, ProvenanceRole,
    StateMacroRemainder, StateRuleReferenceKind, StateTerm, StructuredFormatFragment,
    SyntaxErrorKind, parse_cell_attribute_source, parse_cells_expression_source,
    parse_cells_pattern_source, parse_configuration_attribute_source,
    parse_configuration_declaration_source, parse_constructor_attribute_source,
    parse_initializer_function_source, parse_k_sequence_expression_source,
    parse_k_sequence_pattern_source, parse_map_expression_source, parse_map_pattern_source,
    parse_state_context_alias_item_source, parse_state_rule_item_source,
};

#[test]
fn generated_and_named_roots_and_cell_payloads_are_closed() {
    let generated = parse_configuration_attribute_source("").unwrap();
    assert!(generated.is_generated_top());
    assert!(generated.optional_root().is_none());
    assert!(generated.provenance().unwrap().is_empty());

    let named = parse_configuration_attribute_source(r#"root = "machine""#).unwrap();
    assert_eq!(named.optional_root().unwrap().value(), "machine");

    let cell = parse_cell_attribute_source(r#"color = "green", name = "currentFrame""#).unwrap();
    assert_eq!(cell.name().unwrap().value(), "currentFrame");
    assert_eq!(cell.color().unwrap().value(), "green");
    assert_eq!(
        cell.provenance()
            .unwrap()
            .iter()
            .map(krs_syntax::ProvenanceAnchor::role)
            .collect::<Vec<_>>(),
        [
            ProvenanceRole::ConfigurationCellName,
            ProvenanceRole::ConfigurationCellColor,
        ]
    );

    for source in [
        r#"color = "a", color = "b""#,
        r#"name = """#,
        r#"stream = "stdin""#,
        "color = green",
    ] {
        assert!(parse_cell_attribute_source(source).is_err(), "{source}");
    }
}

#[test]
fn multiple_fixed_and_nested_cells_preserve_order_types_metadata_and_keys() {
    let declaration = parse_configuration_declaration_source(
        r#"
        pub struct Machine {
            #[k::cell(color = "green")]
            pub k: k::configuration::KCell<k::builtin::KSequence>,
            #[k::cell(name = "environment", color = "yellow")]
            pub env: k::configuration::Cell<k::builtin::Map<k::builtin::Id, Term<dyn Value>>>,
            #[k::cell]
            pub frame: model::Frame,
        }
        "#,
    )
    .unwrap();
    assert_eq!(
        declaration
            .cells()
            .iter()
            .map(krs_syntax::FixedCellField::emitted_name)
            .collect::<Vec<_>>(),
        ["k", "environment", "frame"]
    );
    assert!(declaration.cells()[0].is_computation_cell());
    assert!(matches!(
        declaration.cells()[1].cell_content(),
        ConfigurationCellContent::Leaf {
            computation: false,
            ..
        }
    ));
    assert!(matches!(
        declaration.cells()[2].cell_content(),
        ConfigurationCellContent::Nested { .. }
    ));
    let refs = declaration
        .reference_candidates()
        .into_iter()
        .map(|candidate| {
            (
                candidate.key().role().to_owned(),
                candidate.key().ordinal(),
                candidate.path_spelling(),
            )
        })
        .collect::<Vec<_>>();
    assert!(refs.contains(&(
        "configuration_cell_content".into(),
        1,
        "k :: builtin :: Map".into()
    )));
    assert!(refs.contains(&(
        "configuration_cell_content".into(),
        2,
        "model :: Frame".into()
    )));

    for source in [
        "struct Empty {}",
        "struct Tuple(Cell<Map>);",
        "struct Bad { env: OptionalCell<Map> }",
        r#"struct Duplicate { #[k::cell(name = "same")] a: Cell<Map>, #[k::cell(name = "same")] b: Cell<Map> }"#,
        r#"struct Unknown { #[k::cell(stream = "stdin")] env: Cell<Map> }"#,
    ] {
        assert!(
            parse_configuration_declaration_source(source).is_err(),
            "{source}"
        );
    }
}

#[test]
fn k_sequences_freeze_prefix_tail_dotk_and_operator_forms() {
    let pattern = parse_k_sequence_pattern_source("Assign(X, V), tail @ ..").unwrap();
    assert_eq!(pattern.items().len(), 1);
    assert!(
        matches!(pattern.tail(), StateMacroRemainder::Bind { binding, .. } if binding == "tail")
    );

    let operator = parse_k_sequence_expression_source("S1 ~> S2 ~> .K").unwrap();
    assert_eq!(operator.items().len(), 2);
    assert_eq!(operator.notation(), KSequenceNotation::Operator);
    assert!(matches!(operator.tail(), StateMacroRemainder::Exact));

    let empty = parse_k_sequence_expression_source(".K").unwrap();
    assert!(empty.is_empty());
    assert_eq!(empty.notation(), KSequenceNotation::DotK);

    let framed = parse_k_sequence_expression_source("S1, ..tail").unwrap();
    assert!(matches!(
        framed.tail(),
        StateMacroRemainder::Reuse { binding, .. } if binding == "tail"
    ));
    let whole_frame = parse_k_sequence_pattern_source("tail @ ..").unwrap();
    assert!(matches!(
        whole_frame.tail(),
        StateMacroRemainder::Bind { binding, .. } if binding == "tail"
    ));

    for source in [
        "S1,",
        "S1 ~> tail @ ..",
        "S1, ..tail, S2",
        ".K, S1",
        "S1, ~> S2",
    ] {
        assert!(
            parse_k_sequence_expression_source(source).is_err(),
            "{source}"
        );
    }
    assert!(parse_k_sequence_pattern_source("S1, ..tail").is_err());
}

#[test]
fn maps_freeze_empty_items_remainders_and_functional_update() {
    assert!(matches!(
        parse_map_expression_source(".Map").unwrap().body(),
        MapBody::Empty { explicit_dot: true }
    ));
    let pattern = parse_map_pattern_source("X -> V, rest @ ..").unwrap();
    assert!(matches!(
        pattern.body(),
        MapBody::Items { items, remainder: StateMacroRemainder::Bind { binding, .. } }
            if items.len() == 1 && binding == "rest"
    ));
    let remainder_only = parse_map_pattern_source("rest @ ..").unwrap();
    assert!(matches!(
        remainder_only.body(),
        MapBody::Items { items, remainder: StateMacroRemainder::Bind { .. } }
            if items.is_empty()
    ));
    let update = parse_map_expression_source("E [ X <- V ]").unwrap();
    assert!(matches!(update.body(), MapBody::Update { .. }));
    let items =
        parse_map_pattern_source(r#"k::id!("$s") -> 3, k::id!("$n") -> 4, rest @ .."#).unwrap();
    assert!(matches!(items.body(), MapBody::Items { items, .. } if items.len() == 2));
    let nested = parse_map_pattern_source("X -> F(A, B), Y -> G(C)").unwrap();
    assert!(matches!(nested.body(), MapBody::Items { items, .. } if items.len() == 2));
    let update = parse_map_expression_source("E; X <- V").unwrap();
    assert!(matches!(update.body(), MapBody::Update { .. }));

    for source in ["X", "X ->", "X -> V, X ->", ".Map, X -> V", "E; X <- V, Y"] {
        assert!(parse_map_expression_source(source).is_err(), "{source}");
    }
    for (source, expected) in [
        (
            "X => V",
            "`=>` is reserved for rewrites; map entries use `->`",
        ),
        (
            "X -> V, Y => Z",
            "`=>` is reserved for rewrites; map entries use `->`",
        ),
        (
            "E; X => V",
            "`=>` is reserved for rewrites; map updates use `<-`",
        ),
        (
            "E [ X => V ]",
            "`=>` is reserved for rewrites; map updates use `<-`",
        ),
    ] {
        let error = parse_map_expression_source(source).unwrap_err();
        assert!(error.to_string().contains(expected), "{source}: {error}");
    }
    assert!(parse_map_pattern_source("E [ X <- V ]").is_err());
    assert!(parse_map_pattern_source("X -> V, ..rest").is_err());
    assert!(parse_map_expression_source(".. ").is_err());
}

#[test]
fn cells_pattern_and_expression_validate_context_duplicates_and_nested_islands() {
    let pattern = parse_cells_pattern_source(
        "k: KCell(Assign(X, V), tail @ ..), env: Cell(map![X -> V, rest @ ..]), state @ ..",
    )
    .unwrap();
    assert_eq!(pattern.entries().len(), 2);
    assert!(matches!(
        pattern.entries()[0].value(),
        StateTerm::KSequence(_)
    ));
    assert!(matches!(pattern.entries()[1].value(), StateTerm::Map(_)));
    assert!(
        matches!(pattern.remainder(), StateMacroRemainder::Bind { binding, .. } if binding == "state")
    );

    let expression =
        parse_cells_expression_source("k: KCell(.K), env: Cell(map![E [ X <- V ]]), ..state")
            .unwrap();
    assert_eq!(expression.entries().len(), 2);
    assert!(
        matches!(expression.remainder(), StateMacroRemainder::Reuse { binding, .. } if binding == "state")
    );

    for source in [
        "",
        "k: KCell(.K), k: KCell(.K)",
        "k: Other(.K)",
        "k: KCell(.K), ..state, env: Cell(E)",
    ] {
        assert!(parse_cells_expression_source(source).is_err(), "{source}");
    }
    assert!(matches!(
        parse_cells_pattern_source("k: KCell(.K), ..state")
            .unwrap_err()
            .kind(),
        SyntaxErrorKind::InvalidStateMacro { .. }
    ));
}

#[test]
fn typed_variables_and_recursive_initializers_are_complete_and_ordered() {
    let initializer = parse_initializer_function_source(
        r#"
        pub fn init(
            #[k::config_var(name = "PGM", main)] program: Term<dyn Stmt>,
            #[k::config_var(name = "ENV")] env: Map<Id, Term<dyn Value>>,
        ) -> Self {
            Self {
                k: KCell::new(k![program]),
                env: Cell::new(env),
                frame: Frame { locals: Cell::new(map![.Map]) },
            }
        }
        "#,
    )
    .unwrap();
    assert_eq!(initializer.variables().len(), 2);
    assert!(initializer.variables()[0].attribute().is_main());
    assert!(!initializer.variables()[1].attribute().is_main());
    assert_eq!(
        initializer.variables()[1]
            .sort()
            .segments
            .last()
            .unwrap()
            .ident,
        "Map"
    );
    assert_eq!(initializer.cells().len(), 3);
    assert!(matches!(
        initializer.cells()[2].content(),
        InitializerCellContent::Nested { children, .. } if children.len() == 1
    ));
    assert_eq!(initializer.cell().term().spelling(), "program");

    for source in [
        r#"fn init(#[k::config_var(name = "A", main)] a: Term<A>, #[k::config_var(name = "B", main)] b: Term<B>) -> Self { Self { k: KCell::new(k![a]) } }"#,
        r#"fn init(#[k::config_var(name = "A", parser = "X")] a: Term<A>) -> Self { Self { k: KCell::new(k![a]) } }"#,
        r#"fn init(#[k::config_var(name = "A")] a: Term<A>) -> Self { Self { env: Cell::new(a), env: Cell::new(a) } }"#,
        r"fn init() -> Self { Self { env: Cell::new(map![X ->]) } }",
    ] {
        assert!(
            parse_initializer_function_source(source).is_err(),
            "{source}"
        );
    }
}

#[test]
fn structured_format_controls_do_not_change_percent_escaping() {
    let attribute = parse_constructor_attribute_source(
        r#"sort = Stmt, syntax = "{first} {second}", format = "%1%n%i%2%d%%""#,
    )
    .unwrap();
    assert_eq!(
        attribute.structured_format().unwrap().fragments(),
        [
            StructuredFormatFragment::Item(1),
            StructuredFormatFragment::Newline,
            StructuredFormatFragment::Indent,
            StructuredFormatFragment::Item(2),
            StructuredFormatFragment::Dedent,
            StructuredFormatFragment::Literal("%".into()),
        ]
    );
    assert!(
        parse_constructor_attribute_source(r#"sort = Stmt, syntax = "unit", format = "%x""#)
            .is_err()
    );
}

#[test]
fn state_macro_provenance_ranges_select_the_exact_authored_tokens() {
    let source = "k: KCell(X, tail @ ..), env: Cell(map![K -> V, rest @ ..]), state @ ..";
    let cells = parse_cells_pattern_source(source).unwrap();
    let anchors = cells.provenance().unwrap();
    let spelling = |anchor: &krs_syntax::ProvenanceAnchor| {
        &source[anchor.range().start().column..anchor.range().end().column]
    };
    assert_eq!(spelling(&anchors[0]), source);
    assert_eq!(spelling(&anchors[1]), "k");
    assert_eq!(spelling(&anchors[2]), "KCell");
    assert_eq!(spelling(anchors.last().unwrap()), "state @ ..");
    assert_eq!(anchors[1].key().unwrap().role(), "cells_field");
    assert_eq!(anchors[3].key().unwrap().ordinal(), 1);

    let StateTerm::KSequence(sequence) = cells.entries()[0].value() else {
        panic!("the first cell is a K sequence")
    };
    let sequence_anchors = sequence.provenance().unwrap();
    assert_eq!(spelling(&sequence_anchors[0]), "X, tail @ ..");
    assert_eq!(spelling(&sequence_anchors[1]), "X");
    assert_eq!(spelling(&sequence_anchors[2]), "tail @ ..");

    let StateTerm::Map(map) = cells.entries()[1].value() else {
        panic!("the second cell is a map")
    };
    let map_anchors = map.provenance().unwrap();
    assert_eq!(spelling(&map_anchors[1]), "K");
    assert_eq!(spelling(&map_anchors[2]), "V");
    assert_eq!(spelling(&map_anchors[3]), "rest @ ..");
}

#[test]
#[allow(clippy::too_many_lines)] // One assertion block freezes the descriptor-wide ordering contract.
fn whole_configuration_rules_share_one_side_specific_provenance_catalog() {
    parse_k_sequence_expression_source("V, ..tail").unwrap();
    let rule = parse_state_rule_item_source(
        r"
        pub fn var(
            x: Term<Id>,
            v: Term<dyn Value>,
            cells! {
                k: KCell(x, tail @ ..),
                env: Cell(map![x -> v, rest @ ..]),
                state @ ..
            }: model::Machine,
        ) -> model::Machine {
            cells! {
                k: KCell(v, ..tail),
                ..state
            }
        }
        ",
    )
    .unwrap();

    assert_eq!(
        rule.bindings()
            .iter()
            .map(|binding| (binding.name().to_string(), binding.kind()))
            .collect::<Vec<_>>(),
        [
            ("x".into(), krs_syntax::StateRuleBindingKind::Term),
            (
                "tail".into(),
                krs_syntax::StateRuleBindingKind::KSequenceFrame,
            ),
            ("v".into(), krs_syntax::StateRuleBindingKind::Term),
            ("rest".into(), krs_syntax::StateRuleBindingKind::MapFrame),
            (
                "state".into(),
                krs_syntax::StateRuleBindingKind::ConfigurationFrame,
            ),
        ]
    );
    assert_eq!(
        rule.bindings()
            .iter()
            .filter_map(|binding| { binding.term_sort().map(krs_syntax::TermSort::sort_spelling) })
            .collect::<Vec<_>>(),
        ["Id", "Value"]
    );

    let anchors = rule.provenance().unwrap();
    let keys = anchors
        .iter()
        .map(|anchor| anchor.key().unwrap())
        .collect::<Vec<_>>();
    let unique = keys.iter().collect::<std::collections::BTreeSet<_>>();
    assert_eq!(unique.len(), keys.len());
    assert!(
        keys.iter()
            .any(|key| key.role() == "rule_left_cells_payload")
    );
    assert!(
        keys.iter()
            .any(|key| key.role() == "rule_right_cells_payload")
    );
    assert_eq!(
        keys.iter()
            .filter(|key| key.role() == "rule_binding_type")
            .map(krs_ir::ProvenanceKey::ordinal)
            .collect::<Vec<_>>(),
        [0, 1]
    );
    assert_eq!(
        keys.iter()
            .filter(|key| key.role() == "rule_left_reference")
            .map(krs_ir::ProvenanceKey::ordinal)
            .collect::<Vec<_>>(),
        [0, 1, 2]
    );
    assert_eq!(
        keys.iter()
            .filter(|key| key.role() == "rule_right_reference")
            .map(krs_ir::ProvenanceKey::ordinal)
            .collect::<Vec<_>>(),
        [0]
    );

    let references = rule.reference_candidates().unwrap();
    assert_eq!(
        references
            .iter()
            .map(|candidate| (candidate.kind(), candidate.path_spelling()))
            .collect::<Vec<_>>(),
        [
            (StateRuleReferenceKind::BindingSort, "Id".into()),
            (StateRuleReferenceKind::BindingSort, "Value".into()),
            (
                StateRuleReferenceKind::Configuration,
                "model :: Machine".into()
            ),
            (
                StateRuleReferenceKind::Configuration,
                "model :: Machine".into()
            ),
            (StateRuleReferenceKind::CellWrapper, "KCell".into()),
            (StateRuleReferenceKind::CellWrapper, "Cell".into()),
            (StateRuleReferenceKind::CellWrapper, "KCell".into()),
        ]
    );
}

#[test]
fn context_aliases_reject_missing_duplicate_or_structural_here_bindings() {
    for (source, here) in [
        (
            "fn bad(cells! { k: KCell(other, tail @ ..), state @ .. }: Machine) {}",
            "site",
        ),
        (
            "fn bad(cells! { k: KCell(site, site, tail @ ..), state @ .. }: Machine) {}",
            "site",
        ),
        (
            "fn bad(cells! { k: KCell(site, tail @ ..), state @ .. }: Machine) {}",
            "tail",
        ),
        (
            "fn bad(cells! { k: KCell(site, tail @ ..), state @ .. }: Machine) {}",
            "state",
        ),
    ] {
        assert!(
            parse_state_context_alias_item_source(source, here).is_err(),
            "{source} with HERE={here}"
        );
    }
}

#[test]
fn context_aliases_reject_return_values_and_nonempty_post_state_bodies() {
    for source in [
        "fn bad(cells! { k: KCell(site, tail @ ..), state @ .. }: Machine) -> Machine { loop {} }",
        "fn bad(cells! { k: KCell(site, tail @ ..), state @ .. }: Machine) { let post_state = (); }",
    ] {
        assert!(
            parse_state_context_alias_item_source(source, "site").is_err(),
            "{source}"
        );
    }
}

#[test]
fn whole_configuration_rule_requires_uses_the_shared_typed_term_catalog() {
    let rule = parse_state_rule_item_source(
        r"
        #[k::requires(builtin::int::le(value, limit))]
        fn guarded(
            value: Term<Int>,
            limit: Term<Int>,
            cells! { k: KCell(value, limit, tail @ ..), state @ .. }: Machine,
        ) -> Machine {
            cells! { k: KCell(value, limit, ..tail), ..state }
        }
        ",
    )
    .unwrap();
    assert!(rule.requires().is_some());
    let keys = rule
        .provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.key().unwrap())
        .filter(|key| key.role().starts_with("rule_requires"))
        .map(|key| (key.role().to_owned(), key.ordinal()))
        .collect::<Vec<_>>();
    assert_eq!(
        keys,
        [
            ("rule_requires".into(), 0),
            ("rule_requires_path".into(), 0),
            ("rule_requires_path".into(), 1),
            ("rule_requires_path".into(), 2),
            ("rule_requires_application_head".into(), 0),
            ("rule_requires_reference".into(), 0),
            ("rule_requires_reference".into(), 1),
        ]
    );
}

#[test]
fn whole_configuration_rules_reject_unbound_frames_and_non_rule_shells() {
    for source in [
        "fn bad(x: Term<Id>, cells! { k: KCell(x, tail @ ..) }: Machine) -> Machine { cells! { k: KCell(x, ..missing) } }",
        "fn bad(term![X]: Machine) -> Machine { cells! { k: KCell(X, ..state) } }",
        "fn bad(x: Term<Id>, cells! { k: KCell(x, tail @ ..) }: Machine) -> Machine { let y = 1; cells! { k: KCell(x, ..tail) } }",
        "fn bad(a: Machine, b: Machine) -> Machine { cells! { k: KCell(.K) } }",
        "fn bad(x: Term<Id>, cells! { k: KCell(x, tail @ ..) }: Machine) { cells! { k: KCell(x, ..tail) } }",
    ] {
        assert!(parse_state_rule_item_source(source).is_err(), "{source}");
    }
}

#[test]
fn whole_configuration_rules_require_exact_typed_term_binding_order() {
    for source in [
        "fn bad(cells! { k: KCell(x, tail @ ..) }: Machine) -> Machine { cells! { k: KCell(x, ..tail) } }",
        "fn bad(x: Term<Id>, unused: Term<Int>, cells! { k: KCell(x, tail @ ..) }: Machine) -> Machine { cells! { k: KCell(x, ..tail) } }",
        "fn bad(v: Term<Value>, x: Term<Id>, cells! { k: KCell(x, v, tail @ ..) }: Machine) -> Machine { cells! { k: KCell(x, v, ..tail) } }",
        "fn bad(tail: Term<Id>, cells! { k: KCell(tail @ ..) }: Machine) -> Machine { cells! { k: KCell(..tail) } }",
        "fn bad(x: Term<Id>, x: Term<Id>, cells! { k: KCell(x, tail @ ..) }: Machine) -> Machine { cells! { k: KCell(x, ..tail) } }",
    ] {
        assert!(parse_state_rule_item_source(source).is_err(), "{source}");
    }
}

#[test]
fn whole_configuration_rule_patterns_retain_nested_wildcards() {
    let rule = parse_state_rule_item_source(
        "fn choose(s: Term<dyn Stmt>, cells! { k: KCell(IfElse(true, s, _), tail @ ..), state @ .. }: Machine) -> Machine { cells! { k: KCell(s, ..tail), ..state } }",
    )
    .unwrap();
    let keys = rule
        .provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.key().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        keys.iter()
            .filter(|key| key.role() == "rule_left_wildcard")
            .map(krs_ir::ProvenanceKey::ordinal)
            .collect::<Vec<_>>(),
        [0]
    );
    assert!(
        parse_state_rule_item_source(
            "fn bad(x: Term<Id>, cells! { k: KCell(x, tail @ ..), state @ .. }: Machine) -> Machine { cells! { k: KCell(_, ..tail), ..state } }",
        )
        .is_err()
    );
}
