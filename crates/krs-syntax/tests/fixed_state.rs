//! Fixed-state authoring parser freeze.

use krs_syntax::KrsSyntax;
use krs_syntax::{
    ConfigurationCellContent, InitializerCellContent, KSequenceNotation, MapBody, ProvenanceRole,
    StateMacroRemainder, StateRuleReferenceKind, StateTerm, StructuredFormatFragment,
    SyntaxErrorKind,
};
use krs_test_support::assert_rejects;

#[test]
fn generated_and_named_roots_and_cell_payloads_are_closed() {
    let generated = krs_syntax::ConfigurationAttribute::parse_source("").unwrap();
    assert!(generated.is_generated_top());
    assert!(generated.root().is_none());
    assert!(generated.provenance().unwrap().is_empty());

    let named = krs_syntax::ConfigurationAttribute::parse_source(r#"root = "machine""#).unwrap();
    assert_eq!(named.root().unwrap().value(), "machine");

    let cell = krs_syntax::CellAttributePayload::parse_source(
        r#"color = "green", name = "currentFrame", multiplicity = "*", cell_type = "Map", nested"#,
    )
    .unwrap();
    assert_eq!(cell.name().unwrap().value(), "currentFrame");
    assert_eq!(cell.color().unwrap().value(), "green");
    assert_eq!(cell.multiplicity().unwrap().value(), "*");
    assert_eq!(cell.cell_type().unwrap().value(), "Map");
    assert!(cell.is_nested());
    assert_eq!(
        cell.provenance()
            .unwrap()
            .iter()
            .map(krs_syntax::ProvenanceAnchor::role)
            .collect::<Vec<_>>(),
        [
            ProvenanceRole::ConfigurationCellName,
            ProvenanceRole::ConfigurationCellColor,
            ProvenanceRole::ConfigurationCellMultiplicity,
            ProvenanceRole::ConfigurationCellType,
        ]
    );

    for (source, expected_kind) in [
        (
            r#"color = "a", color = "b""#,
            SyntaxErrorKind::DuplicateArgument { name: "color" },
        ),
        (
            r#"name = """#,
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "cell metadata values must be nonempty strings",
            },
        ),
        (
            r#"stream = "stdin""#,
            SyntaxErrorKind::UnknownArgument {
                name: "stream".into(),
            },
        ),
        (
            "color = green",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "color",
                expected: "a Rust string literal",
            },
        ),
        (
            r#"multiplicity = "?""#,
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "KRS currently supports only repeated-cell multiplicity `*`",
            },
        ),
        (
            r#"cell_type = "Map""#,
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "`cell_type` requires `multiplicity = \"*\"`",
            },
        ),
        (
            r#"multiplicity = "*", cell_type = "Queue""#,
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "repeated-cell `cell_type` must be Bag, List, Map, or Set",
            },
        ),
    ] {
        let error = krs_syntax::CellAttributePayload::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn multiple_fixed_and_nested_cells_preserve_order_types_metadata_and_keys() {
    let declaration = krs_syntax::ConfigurationDeclaration::parse_source(
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
                candidate.key().role(),
                candidate.key().ordinal(),
                candidate.path_spelling(),
            )
        })
        .collect::<Vec<_>>();
    assert!(refs.contains(&(
        ProvenanceRole::ConfigurationCellContent,
        1,
        "k::builtin::Map".into()
    )));
    assert!(refs.contains(&(
        ProvenanceRole::ConfigurationCellContent,
        2,
        "model::Frame".into()
    )));

    for (source, expected_kind) in [
        (
            "struct Empty {}",
            SyntaxErrorKind::UnsupportedConfigurationDeclaration {
                reason: "a fixed configuration requires at least one cell",
            },
        ),
        (
            "struct Tuple(Cell<Map>);",
            SyntaxErrorKind::UnsupportedConfigurationDeclaration {
                reason: "a fixed configuration must be a named-field struct",
            },
        ),
        (
            "struct Bad { env: OptionalCell<Map> }",
            SyntaxErrorKind::UnsupportedConfigurationField {
                reason: "nested fixed-cell declarations cannot have generic arguments",
            },
        ),
        (
            r#"struct Duplicate { #[k::cell(name = "same")] a: Cell<Map>, #[k::cell(name = "same")] b: Cell<Map> }"#,
            SyntaxErrorKind::UnsupportedConfigurationField {
                reason: "two sibling fields cannot emit the same cell name",
            },
        ),
        (
            r#"struct Unknown { #[k::cell(stream = "stdin")] env: Cell<Map> }"#,
            SyntaxErrorKind::UnknownArgument {
                name: "stream".into(),
            },
        ),
    ] {
        let error = krs_syntax::ConfigurationDeclaration::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn k_sequences_freeze_prefix_tail_dotk_and_operator_forms() {
    let pattern = krs_syntax::parse_k_sequence_pattern(
        krs_syntax::parse::tokens_from_source("Assign(X, V), tail @ ..").unwrap(),
    )
    .unwrap();
    assert_eq!(pattern.items().len(), 1);
    assert!(
        matches!(pattern.tail(), StateMacroRemainder::Bind { binding, .. } if binding == "tail")
    );

    let operator = krs_syntax::parse_k_sequence_expression(
        krs_syntax::parse::tokens_from_source("S1 ~> S2 ~> .K").unwrap(),
    )
    .unwrap();
    assert_eq!(operator.items().len(), 2);
    assert_eq!(operator.notation(), KSequenceNotation::Operator);
    assert!(matches!(operator.tail(), StateMacroRemainder::Exact));

    let empty = krs_syntax::parse_k_sequence_expression(
        krs_syntax::parse::tokens_from_source(".K").unwrap(),
    )
    .unwrap();
    assert!(empty.is_empty());
    assert_eq!(empty.notation(), KSequenceNotation::DotK);

    let framed = krs_syntax::parse_k_sequence_expression(
        krs_syntax::parse::tokens_from_source("S1, ..tail").unwrap(),
    )
    .unwrap();
    assert!(matches!(
        framed.tail(),
        StateMacroRemainder::Reuse { binding, .. } if binding == "tail"
    ));
    let whole_frame = krs_syntax::parse_k_sequence_pattern(
        krs_syntax::parse::tokens_from_source("tail @ ..").unwrap(),
    )
    .unwrap();
    assert!(matches!(
        whole_frame.tail(),
        StateMacroRemainder::Bind { binding, .. } if binding == "tail"
    ));

    for (source, expected_kind) in [
        (
            "S1,",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "k",
                reason: "a sequence separator requires another item",
            },
        ),
        (
            "S1 ~> tail @ ..",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "k",
                reason: "expressions reuse remainders as `..name`",
            },
        ),
        (
            "S1, ..tail, S2",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "k",
                reason: "the sequence tail must be last",
            },
        ),
        (
            ".K, S1",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "k",
                reason: "`.K` must be the complete empty sequence",
            },
        ),
        (
            "S1, S2 ~> S3",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "k",
                reason: "cannot mix `,` and `~>` separators",
            },
        ),
    ] {
        let error = krs_syntax::parse_k_sequence_expression(
            krs_syntax::parse::tokens_from_source(source).unwrap(),
        )
        .unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
    assert_rejects!(
        krs_syntax::parse_k_sequence_pattern(
            krs_syntax::parse::tokens_from_source("S1, ..tail").unwrap()
        ),
        error if error.kind() == &SyntaxErrorKind::InvalidStateMacro {
            macro_name: "k",
            reason: "patterns bind remainders as `name @ ..`",
        }
    );
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One table-driven block freezes the complete map grammar."
)]
fn maps_freeze_empty_items_remainders_and_functional_update() {
    assert!(matches!(
        krs_syntax::parse_map_expression(krs_syntax::parse::tokens_from_source(".Map").unwrap())
            .unwrap()
            .body(),
        MapBody::Empty { explicit_dot: true }
    ));
    let pattern = krs_syntax::parse_map_pattern(
        krs_syntax::parse::tokens_from_source("X -> V, rest @ ..").unwrap(),
    )
    .unwrap();
    assert!(matches!(
        pattern.body(),
        MapBody::Items { items, remainder: StateMacroRemainder::Bind { binding, .. } }
            if items.len() == 1 && binding == "rest"
    ));
    let remainder_only =
        krs_syntax::parse_map_pattern(krs_syntax::parse::tokens_from_source("rest @ ..").unwrap())
            .unwrap();
    assert!(matches!(
        remainder_only.body(),
        MapBody::Items { items, remainder: StateMacroRemainder::Bind { .. } }
            if items.is_empty()
    ));
    let update = krs_syntax::parse_map_expression(
        krs_syntax::parse::tokens_from_source("E [ X <- V ]").unwrap(),
    )
    .unwrap();
    assert!(matches!(update.body(), MapBody::Update { .. }));
    let items = krs_syntax::parse_map_pattern(
        krs_syntax::parse::tokens_from_source(r#"k::id!("$s") -> 3, k::id!("$n") -> 4, rest @ .."#)
            .unwrap(),
    )
    .unwrap();
    assert!(matches!(items.body(), MapBody::Items { items, .. } if items.len() == 2));
    let nested = krs_syntax::parse_map_pattern(
        krs_syntax::parse::tokens_from_source("X -> F(A, B), Y -> G(C)").unwrap(),
    )
    .unwrap();
    assert!(matches!(nested.body(), MapBody::Items { items, .. } if items.len() == 2));
    let update = krs_syntax::parse_map_expression(
        krs_syntax::parse::tokens_from_source("E; X <- V").unwrap(),
    )
    .unwrap();
    assert!(matches!(update.body(), MapBody::Update { .. }));

    for (source, expected_kind) in [
        (
            "X",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "map",
                reason: "expected `->` after a map-item key",
            },
        ),
        (
            "X ->",
            SyntaxErrorKind::RustSyntax("unexpected end of input, expected an expression".into()),
        ),
        (
            "X -> V, X ->",
            SyntaxErrorKind::RustSyntax("unexpected end of input, expected an expression".into()),
        ),
        (
            ".Map, X -> V",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "map",
                reason: "`.Map` must be the complete empty map",
            },
        ),
        (
            "E; X <- V, Y",
            SyntaxErrorKind::RustSyntax("unexpected token".into()),
        ),
    ] {
        let error = krs_syntax::parse_map_expression(
            krs_syntax::parse::tokens_from_source(source).unwrap(),
        )
        .unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
    for (source, expected_kind) in [
        (
            "X => V",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "map",
                reason: "`=>` is reserved for rewrites; map entries use `->`",
            },
        ),
        (
            "X -> V, Y => Z",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "map",
                reason: "`=>` is reserved for rewrites; map entries use `->`",
            },
        ),
        (
            "E; X => V",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "map",
                reason: "`=>` is reserved for rewrites; map updates use `<-`",
            },
        ),
        (
            "E [ X => V ]",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "map",
                reason: "`=>` is reserved for rewrites; map updates use `<-`",
            },
        ),
    ] {
        let error = krs_syntax::parse_map_expression(
            krs_syntax::parse::tokens_from_source(source).unwrap(),
        )
        .unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
    assert_rejects!(
        krs_syntax::parse_map_pattern(
            krs_syntax::parse::tokens_from_source("E [ X <- V ]").unwrap()
        ),
        error if error.kind() == &SyntaxErrorKind::InvalidStateMacro {
            macro_name: "map",
            reason: "functional updates are expression-only",
        }
    );
    assert_rejects!(
        krs_syntax::parse_map_pattern(
            krs_syntax::parse::tokens_from_source("X -> V, ..rest").unwrap()
        ),
        error if error.kind() == &SyntaxErrorKind::InvalidStateMacro {
            macro_name: "map",
            reason: "patterns bind remainders as `name @ ..`",
        }
    );
    assert_rejects!(
        krs_syntax::parse_map_expression(
            krs_syntax::parse::tokens_from_source("X -> V, ..").unwrap()
        ),
        error if error.kind() == &SyntaxErrorKind::InvalidStateMacro {
            macro_name: "map",
            reason: "expression remainders must reuse a named binding as `..name`",
        }
    );
}

#[test]
fn cells_pattern_and_expression_validate_context_duplicates_and_nested_islands() {
    let pattern = krs_syntax::parse_cells_pattern(
        krs_syntax::parse::tokens_from_source(
            "k: KCell(Assign(X, V), tail @ ..), env: Cell(map![X -> V, rest @ ..]), state @ ..",
        )
        .unwrap(),
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

    let qualified = krs_syntax::parse_cells_pattern(
        krs_syntax::parse::tokens_from_source(
            "crate::model::Account::storage: Cell(S), Account::storage: Cell(T)",
        )
        .unwrap(),
    )
    .unwrap();
    assert_eq!(qualified.entries()[0].name(), "storage");
    assert_eq!(
        qualified.entries()[0]
            .owner()
            .map(krs_syntax::surface::path_text)
            .as_deref(),
        Some("crate::model::Account")
    );
    assert_eq!(
        qualified.entries()[1]
            .owner()
            .map(krs_syntax::surface::path_text)
            .as_deref(),
        Some("Account")
    );

    let expression = krs_syntax::parse_cells_expression(
        krs_syntax::parse::tokens_from_source(
            "k: KCell(.K), env: Cell(map![E [ X <- V ]]), ..state",
        )
        .unwrap(),
    )
    .unwrap();
    assert_eq!(expression.entries().len(), 2);
    assert!(
        matches!(expression.remainder(), StateMacroRemainder::Reuse { binding, .. } if binding == "state")
    );

    for (source, expected_kind) in [
        (
            "",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "cells",
                reason: "at least one cell clause is required",
            },
        ),
        (
            "k: KCell(.K), k: KCell(.K)",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "cells",
                reason: "an owner-qualified cell field occurs more than once",
            },
        ),
        (
            "k: Other(.K)",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "cells",
                reason: "entries require `Cell(...)` or `KCell(...)`",
            },
        ),
        (
            "k: KCell(.K), ..state, env: Cell(E)",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "cells",
                reason: "the configuration remainder must be last",
            },
        ),
        (
            "Account::storage: Cell(S), Account::storage: Cell(T)",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "cells",
                reason: "an owner-qualified cell field occurs more than once",
            },
        ),
    ] {
        let error = krs_syntax::parse_cells_expression(
            krs_syntax::parse::tokens_from_source(source).unwrap(),
        )
        .unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
    assert!(matches!(
        krs_syntax::parse_cells_pattern(
            krs_syntax::parse::tokens_from_source("k: KCell(.K), ..state").unwrap()
        )
        .unwrap_err()
        .kind(),
        SyntaxErrorKind::InvalidStateMacro { .. }
    ));
}

#[test]
fn typed_variables_and_recursive_initializers_are_complete_and_ordered() {
    let initializer = krs_syntax::InitializerFunction::parse_source(
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
    assert_eq!(initializer.cell().unwrap().term().spelling(), "program");

    for (source, expected_kind) in [
        (
            r#"fn init(#[k::config_var(name = "A", main)] a: Term<A>, #[k::config_var(name = "B", main)] b: Term<B>) -> Self { Self { k: KCell::new(k![a]) } }"#,
            SyntaxErrorKind::AmbiguousMainConfigurationVariable,
        ),
        (
            r#"fn init(#[k::config_var(name = "A", parser = "X")] a: Term<A>) -> Self { Self { k: KCell::new(k![a]) } }"#,
            SyntaxErrorKind::UnknownArgument {
                name: "parser".into(),
            },
        ),
        (
            r#"fn init(#[k::config_var(name = "A")] a: Term<A>) -> Self { Self { env: Cell::new(a), env: Cell::new(a) } }"#,
            SyntaxErrorKind::DuplicateConfigurationField { name: "fixed cell" },
        ),
        (
            r"fn init() -> Self { Self { env: Cell::new(map![X ->]) } }",
            SyntaxErrorKind::RustSyntax("unexpected end of input, expected an expression".into()),
        ),
    ] {
        let error = krs_syntax::InitializerFunction::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn structured_format_controls_do_not_change_percent_escaping() {
    let attribute = krs_syntax::ConstructorAttribute::parse_source(
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
    assert_rejects!(
        krs_syntax::ConstructorAttribute::parse_source(
            r#"sort = Stmt, syntax = "unit", format = "%x""#
        ),
        error if error.kind() == &SyntaxErrorKind::InvalidFormat {
            reason: "`%` must be followed by `%n`, `%i`, `%d`, `%c`, `%r`, `%%`, or a one-based item position",
        }
    );
}

#[test]
fn state_macro_provenance_ranges_select_the_exact_authored_tokens() {
    let source = "k: KCell(X, tail @ ..), env: Cell(map![K -> V, rest @ ..]), state @ ..";
    let cells =
        krs_syntax::parse_cells_pattern(krs_syntax::parse::tokens_from_source(source).unwrap())
            .unwrap();
    let anchors = cells.provenance().unwrap();
    let spelling = |anchor: &krs_syntax::ProvenanceAnchor| {
        &source[anchor.range().start().column..anchor.range().end().column]
    };
    assert_eq!(spelling(&anchors[0]), source);
    assert_eq!(spelling(&anchors[1]), "k");
    assert_eq!(spelling(&anchors[2]), "KCell");
    assert_eq!(spelling(anchors.last().unwrap()), "state @ ..");
    assert_eq!(anchors[1].key().role(), ProvenanceRole::CellsField);
    assert_eq!(anchors[3].key().ordinal(), 1);

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
#[expect(
    clippy::too_many_lines,
    reason = "One assertion block freezes the descriptor-wide ordering contract."
)]
fn whole_configuration_rules_share_one_side_specific_provenance_catalog() {
    krs_syntax::parse_k_sequence_expression(
        krs_syntax::parse::tokens_from_source("V, ..tail").unwrap(),
    )
    .unwrap();
    let rule = krs_syntax::StateRuleItem::parse_source(
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
            .filter_map(|binding| {
                binding
                    .term_sort()
                    .map(krs_syntax::TermSort::sort_token_text)
            })
            .collect::<Vec<_>>(),
        ["Id", "Value"]
    );

    let anchors = rule.provenance().unwrap();
    let keys = anchors
        .iter()
        .map(krs_syntax::ProvenanceAnchor::key)
        .collect::<Vec<_>>();
    let unique = keys.iter().collect::<std::collections::BTreeSet<_>>();
    assert_eq!(unique.len(), keys.len());
    assert!(
        keys.iter()
            .any(|key| key.role() == ProvenanceRole::RuleLeftCellsPayload)
    );
    assert!(
        keys.iter()
            .any(|key| key.role() == ProvenanceRole::RuleRightCellsPayload)
    );
    assert_eq!(
        keys.iter()
            .filter(|key| key.role() == ProvenanceRole::RuleBindingType)
            .map(krs_ir::ProvenanceKey::ordinal)
            .collect::<Vec<_>>(),
        [0, 1]
    );
    assert_eq!(
        keys.iter()
            .filter(|key| key.role() == ProvenanceRole::RuleLeftReference)
            .map(krs_ir::ProvenanceKey::ordinal)
            .collect::<Vec<_>>(),
        [0, 1, 2]
    );
    assert_eq!(
        keys.iter()
            .filter(|key| key.role() == ProvenanceRole::RuleRightReference)
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
                "model::Machine".into()
            ),
            (
                StateRuleReferenceKind::Configuration,
                "model::Machine".into()
            ),
            (StateRuleReferenceKind::CellWrapper, "KCell".into()),
            (StateRuleReferenceKind::CellWrapper, "Cell".into()),
            (StateRuleReferenceKind::CellWrapper, "KCell".into()),
        ]
    );
}

#[test]
fn context_aliases_reject_missing_duplicate_or_structural_here_bindings() {
    for (source, here, expected_kind) in [
        (
            "fn bad(cells! { k: KCell(other, tail @ ..), state @ .. }: Machine) {}",
            "site",
            SyntaxErrorKind::UnsupportedRulePattern {
                reason: "`here` must select exactly one ordinary term binding",
            },
        ),
        (
            "fn bad(cells! { k: KCell(site, site, tail @ ..), state @ .. }: Machine) {}",
            "site",
            SyntaxErrorKind::UnsupportedRulePattern {
                reason: "`here` must select exactly one ordinary term binding",
            },
        ),
        (
            "fn bad(cells! { k: KCell(site, tail @ ..), state @ .. }: Machine) {}",
            "tail",
            SyntaxErrorKind::UnsupportedRulePattern {
                reason: "`here` must select exactly one ordinary term binding",
            },
        ),
        (
            "fn bad(cells! { k: KCell(site, tail @ ..), state @ .. }: Machine) {}",
            "state",
            SyntaxErrorKind::UnsupportedRulePattern {
                reason: "`here` must select exactly one ordinary term binding",
            },
        ),
    ] {
        let error = krs_syntax::parse_state_context_alias_item(
            krs_syntax::parse::tokens_from_source(source).unwrap(),
            &syn::parse_str(here).unwrap(),
        )
        .unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source} with HERE={here}");
    }
}

#[test]
fn context_aliases_reject_return_values_and_nonempty_post_state_bodies() {
    for (source, expected_kind) in [
        (
            "fn bad(cells! { k: KCell(site, tail @ ..), state @ .. }: Machine) -> Machine { loop {} }",
            SyntaxErrorKind::UnsupportedRuleBody {
                reason: "a context alias must return `()` and have an empty body",
            },
        ),
        (
            "fn bad(cells! { k: KCell(site, tail @ ..), state @ .. }: Machine) { let post_state = (); }",
            SyntaxErrorKind::UnsupportedRuleBody {
                reason: "a context alias must return `()` and have an empty body",
            },
        ),
    ] {
        let error = krs_syntax::parse_state_context_alias_item(
            krs_syntax::parse::tokens_from_source(source).unwrap(),
            &syn::parse_str("site").unwrap(),
        )
        .unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn whole_configuration_rule_requires_uses_the_shared_typed_term_catalog() {
    let rule = krs_syntax::StateRuleItem::parse_source(
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
        .map(|anchor| anchor.key())
        .filter(|key| {
            key.role()
                .as_str()
                .starts_with(ProvenanceRole::RuleRequires.as_str())
        })
        .map(|key| (key.role(), key.ordinal()))
        .collect::<Vec<_>>();
    assert_eq!(
        keys,
        [
            (ProvenanceRole::RuleRequires, 0),
            (ProvenanceRole::RuleRequiresPath, 0),
            (ProvenanceRole::RuleRequiresPath, 1),
            (ProvenanceRole::RuleRequiresPath, 2),
            (ProvenanceRole::RuleRequiresApplicationHead, 0),
            (ProvenanceRole::RuleRequiresReference, 0),
            (ProvenanceRole::RuleRequiresReference, 1),
        ]
    );
}

#[test]
fn whole_configuration_rules_reject_unbound_frames_and_non_rule_shells() {
    for (source, expected_kind) in [
        (
            "fn bad(x: Term<Id>, cells! { k: KCell(x, tail @ ..) }: Machine) -> Machine { cells! { k: KCell(x, ..missing) } }",
            SyntaxErrorKind::UnsupportedRuleBody {
                reason: "a result remainder must reuse a subject frame of the same kind",
            },
        ),
        (
            "fn bad(term![X]: Machine) -> Machine { cells! { k: KCell(X, ..state) } }",
            SyntaxErrorKind::UnsupportedRulePattern {
                reason: "configuration rules require the compiler-owned `cells!` island",
            },
        ),
        (
            "fn bad(x: Term<Id>, cells! { k: KCell(x, tail @ ..) }: Machine) -> Machine { let y = 1; cells! { k: KCell(x, ..tail) } }",
            SyntaxErrorKind::UnsupportedRuleBody {
                reason: "a configuration-rule body must contain exactly one `cells!` expression",
            },
        ),
        (
            "fn bad(a: Machine, b: Machine) -> Machine { cells! { k: KCell(.K) } }",
            SyntaxErrorKind::UnsupportedRulePattern {
                reason: "a configuration-rule subject must be `cells! { ... }`",
            },
        ),
        (
            "fn bad(x: Term<Id>, cells! { k: KCell(x, tail @ ..) }: Machine) { cells! { k: KCell(x, ..tail) } }",
            SyntaxErrorKind::UnsupportedRuleSignature {
                reason: "a configuration rule must declare its configuration result type",
            },
        ),
    ] {
        let error = krs_syntax::StateRuleItem::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn whole_configuration_rules_require_exact_typed_term_binding_order() {
    for (source, expected_kind) in [
        (
            "fn bad(cells! { k: KCell(x, tail @ ..) }: Machine) -> Machine { cells! { k: KCell(x, ..tail) } }",
            SyntaxErrorKind::UnsupportedRuleSignature {
                reason: "typed term parameters must exactly match subject term bindings in first-occurrence order",
            },
        ),
        (
            "fn bad(x: Term<Id>, unused: Term<Int>, cells! { k: KCell(x, tail @ ..) }: Machine) -> Machine { cells! { k: KCell(x, ..tail) } }",
            SyntaxErrorKind::UnsupportedRuleSignature {
                reason: "typed term parameters must exactly match subject term bindings in first-occurrence order",
            },
        ),
        (
            "fn bad(v: Term<Value>, x: Term<Id>, cells! { k: KCell(x, v, tail @ ..) }: Machine) -> Machine { cells! { k: KCell(x, v, ..tail) } }",
            SyntaxErrorKind::UnsupportedRuleSignature {
                reason: "typed term parameters must exactly match subject term bindings in first-occurrence order",
            },
        ),
        (
            "fn bad(tail: Term<Id>, cells! { k: KCell(tail @ ..) }: Machine) -> Machine { cells! { k: KCell(..tail) } }",
            SyntaxErrorKind::UnsupportedRuleSignature {
                reason: "typed term parameters must exactly match subject term bindings in first-occurrence order",
            },
        ),
        (
            "fn bad(x: Term<Id>, x: Term<Id>, cells! { k: KCell(x, tail @ ..) }: Machine) -> Machine { cells! { k: KCell(x, ..tail) } }",
            SyntaxErrorKind::UnsupportedRuleSignature {
                reason: "configuration-rule term parameters must be unique immutable bindings",
            },
        ),
    ] {
        let error = krs_syntax::StateRuleItem::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn whole_configuration_rule_patterns_retain_nested_wildcards() {
    let rule = krs_syntax::StateRuleItem::parse_source(
        "fn choose(s: Term<dyn Stmt>, cells! { k: KCell(IfElse(true, s, _), tail @ ..), state @ .. }: Machine) -> Machine { cells! { k: KCell(s, ..tail), ..state } }",
    )
    .unwrap();
    let keys = rule
        .provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.key())
        .collect::<Vec<_>>();
    assert_eq!(
        keys.iter()
            .filter(|key| key.role() == ProvenanceRole::RuleLeftWildcard)
            .map(krs_ir::ProvenanceKey::ordinal)
            .collect::<Vec<_>>(),
        [0]
    );
    assert_rejects!(
        krs_syntax::StateRuleItem::parse_source(
            "fn bad(x: Term<Id>, cells! { k: KCell(x, tail @ ..), state @ .. }: Machine) -> Machine { cells! { k: KCell(_, ..tail), ..state } }",
        ),
        error if error.kind() == &SyntaxErrorKind::UnsupportedTermExpression {
            reason: "the root must be a named path/call/record or an Int/Bool literal",
        }
    );
}

#[test]
fn map_pattern_binding_conflicts_keep_term_before_frame_order_and_span() {
    let source = "fn rule(cells! { k: KCell(tail @ ..), env: Cell(map![tail -> tail, tail @ ..]) }: Machine) -> Machine { cells! { k: KCell(.K) } }";
    let error = krs_syntax::StateRuleItem::parse_source(source).unwrap_err();
    assert_eq!(
        error.kind(),
        &SyntaxErrorKind::UnsupportedRulePattern {
            reason: "a configuration-rule binding cannot be reused as a different frame or term kind",
        },
    );
    assert_eq!(error.span().start().column, source.find("tail ->").unwrap());
}

#[test]
fn machine_records_may_leave_the_computation_cell_out() {
    // E7: an omitted cell is untouched, and that includes the computation cell.
    let block = krs_syntax::RuleBlock::parse_source(
        r"
        for Machine;

        #[k::requires(int::gt(f, 0))]
        burn: { fuel: f, acc: a } => { fuel: int::sub(f, 1), acc: int::add(a, f) };
        ",
    )
    .unwrap();
    let clause = &block.clauses()[0];
    assert!(clause.head_result().is_none());
    assert!(clause.computation_cell().is_none());
    assert_eq!(
        clause
            .bindings()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        ["f", "a"]
    );
    assert_eq!(clause.extras().len(), 2);
    assert!(clause.rule().requires().is_some());
    let anchors = clause.provenance().unwrap();
    let pattern = anchors
        .iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::RulePattern)
        .collect::<Vec<_>>();
    assert_eq!(
        pattern.len(),
        1,
        "one pattern anchor, at the subject record"
    );
    assert!(
        anchors
            .iter()
            .all(|anchor| anchor.role() != ProvenanceRole::RuleLeftWildcard),
        "the placeholder subject contributes no wildcard"
    );

    for (source, expected) in [
        (
            "for Machine; idle: {} => {};",
            "a machine rule selects at least one cell",
        ),
        (
            "for Machine; two: { k: [A, ..], k2: [B, ..] } => { k: [..], k2: [..] };",
            "a machine rule must match at most one computation-cell sequence",
        ),
    ] {
        let error = krs_syntax::RuleBlock::parse_source(source).unwrap_err();
        assert!(
            error.to_string().contains(expected),
            "expected {expected:?} in {error}"
        );
    }
}

#[test]
fn whole_nested_cell_entries_are_binders_wildcards_or_fragments() {
    let pattern = krs_syntax::parse_cells_pattern(
        krs_syntax::parse::tokens_from_source(
            "k: KCell(Pop(), tail @ ..), frame: f, saved: _, state @ ..",
        )
        .unwrap(),
    )
    .unwrap();
    assert_eq!(pattern.entries().len(), 3);
    assert!(pattern.entries()[0].wrapper().is_some());
    for entry in &pattern.entries()[1..] {
        assert!(entry.wrapper().is_none(), "{}", entry.name());
        assert!(matches!(entry.value(), StateTerm::Group(_)));
    }
    let wrappers = pattern
        .provenance()
        .unwrap()
        .into_iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::CellsWrapper)
        .count();
    assert_eq!(wrappers, 1);

    let expression = krs_syntax::parse_cells_expression(
        krs_syntax::parse::tokens_from_source(
            "k: KCell(..tail), frame: k::fragment![Frame { pc: p, gas: g }], ..state",
        )
        .unwrap(),
    )
    .unwrap();
    assert!(matches!(
        expression.entries()[1].value(),
        StateTerm::Group(term) if matches!(term.tree(), krs_syntax::TermTree::Cell(_))
    ));

    let rule = krs_syntax::StateRuleItem::parse_source(
        r"
        pub fn push(
            s: Term<List>,
            f: crate::Frame,
            cells! {
                k: KCell(Push(), tail @ ..),
                stack: Cell(s),
                frame: f,
                state @ ..
            }: crate::Machine,
        ) -> crate::Machine {
            cells! {
                k: KCell(..tail),
                stack: Cell(list::concat(list::item(f), s)),
                frame: f,
                ..state
            }
        }
        ",
    )
    .unwrap();
    assert_eq!(
        rule.bindings()
            .iter()
            .filter(|binding| binding.kind() == krs_syntax::StateRuleBindingKind::Term)
            .map(|binding| binding.name().to_string())
            .collect::<Vec<_>>(),
        ["s", "f"]
    );

    let group_entry = SyntaxErrorKind::InvalidStateMacro {
        macro_name: "cells",
        reason: "nested cell entries are a binder, `_`, or fragment!",
    };
    for source in ["frame: 3", "frame: [f]", "frame: crate::f"] {
        let error =
            krs_syntax::parse_cells_pattern(krs_syntax::parse::tokens_from_source(source).unwrap())
                .unwrap_err();
        assert_eq!(error.kind(), &group_entry, "{source}");
    }
    let error = krs_syntax::parse_cells_expression(
        krs_syntax::parse::tokens_from_source("frame: _").unwrap(),
    )
    .unwrap_err();
    assert_eq!(error.kind(), &group_entry);
}
