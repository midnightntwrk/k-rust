//! Fixed-state authoring parser freeze.

use krs_syntax::KrsSyntax;
use krs_syntax::{
    ConfigurationCellContent, InitializerCellContent, KSequenceNotation, MapBody, ProvenanceRole,
    StateMacroRemainder, StateRuleReferenceKind, StateTerm, StructuredFormatFragment, SyntaxError,
    SyntaxErrorKind,
};
use krs_test_support::assert_rejects;
use quote::ToTokens;

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
            r#"stream = "stderr""#,
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "K supports stream=\"stdin\" and \"stdout\"",
            },
        ),
        (
            r#"stream = "stdin", stream = "stdout""#,
            SyntaxErrorKind::DuplicateArgument { name: "stream" },
        ),
        (
            r#"exit = """#,
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "exit takes no value",
            },
        ),
        (
            "exit, exit",
            SyntaxErrorKind::DuplicateArgument { name: "exit" },
        ),
        (
            "color = green",
            SyntaxErrorKind::InvalidArgumentValue {
                name: "color",
                expected: "a Rust string literal",
            },
        ),
    ] {
        let error = krs_syntax::CellAttributePayload::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

#[test]
fn optional_and_collection_cell_attributes_are_checked() {
    for (source, expected_kind) in [
        (
            r#"multiplicity = "+""#,
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "cell `multiplicity` is \"?\" (an optional cell) or \"*\" (a cell collection)",
            },
        ),
        (
            r#"cell_type = "Map""#,
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "`cell_type` requires `multiplicity = \"*\"`",
            },
        ),
        (
            r#"multiplicity = "?", cell_type = "Map""#,
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "`cell_type` requires `multiplicity = \"*\"`",
            },
        ),
        (
            r#"multiplicity = "*", cell_type = "Queue", nested"#,
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "a collection's `cell_type` is \"Set\", \"Map\", or \"List\"",
            },
        ),
        (
            r#"multiplicity = "*", cell_type = "Bag", nested"#,
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "cell bags are unsupported by K's LLVM and Haskell backends; use cell_type = \"Set\", \"Map\", or \"List\"",
            },
        ),
        (
            r#"multiplicity = "*", nested"#,
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "a `multiplicity = \"*\"` collection needs `cell_type = \"Set\"`, `\"Map\"`, or `\"List\"`",
            },
        ),
        (
            r#"multiplicity = "*", cell_type = "Set""#,
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "a `multiplicity = \"*\"` collection holds whole cells: add `nested` and declare its instance as a `#[k::cell]` struct",
            },
        ),
        (
            "initial",
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "`initial` belongs to a collection (`multiplicity = \"*\"`) cell",
            },
        ),
        (
            r#"multiplicity = "?", initial"#,
            SyntaxErrorKind::InvalidCellAttribute {
                reason: "`initial` on an optional (`multiplicity = \"?\"`) cell repeats what its initializer says, so drop `initial`: `Some(value)` starts it present and `k::absent!(template)` absent",
            },
        ),
        (
            r#"multiplicity = "?", initial, initial"#,
            SyntaxErrorKind::DuplicateArgument { name: "initial" },
        ),
    ] {
        let error = krs_syntax::CellAttributePayload::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected_kind, "{source}");
    }
}

/// An optional cell's initializer is `Some(value)` or `k::absent!(template)` around a value
/// itself: neither nests the other, and `k::absent!` takes exactly one expression.
#[test]
fn optional_initializers_hold_one_value_or_template() {
    let nested = "an optional cell's initializer holds its value or template itself, not another `Some(..)` or `k::absent!(..)`";
    let one = "`k::absent!` takes one expression, the template of the absent optional cell: `k::absent!(<template>)`";
    for (value, reason, at) in [
        ("Some(k::absent!(0))", nested, "k::absent!(0)"),
        ("k::absent!(Some(0))", nested, "Some(0)"),
        ("k::absent!(k::absent!(0))", nested, "k::absent!(0)"),
        ("k::absent!()", one, "k::absent!()"),
        ("k::absent!(a, b)", one, "k::absent!(a, b)"),
    ] {
        let source = format!("fn init() -> Self {{ Self {{ counter: {value} }} }}");
        let error = krs_syntax::InitializerFunction::parse_source(&source).unwrap_err();
        assert_eq!(
            error.kind(),
            &SyntaxErrorKind::UnsupportedInitializerBody { reason },
            "{value}"
        );
        assert_eq!(
            error.span().start().column,
            source.find(at).unwrap(),
            "{value}"
        );
    }
    for value in ["Some(0)", "k::absent!(0)"] {
        krs_syntax::InitializerFunction::parse_source(&format!(
            "fn init() -> Self {{ Self {{ counter: {value} }} }}"
        ))
        .unwrap();
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
            r#"struct Unknown { #[k::cell(steam = "stdin")] env: Cell<Map> }"#,
            SyntaxErrorKind::UnknownArgument {
                name: "steam".into(),
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
            "S1 ~>",
            SyntaxErrorKind::InvalidStateMacro {
                macro_name: "k",
                reason: "a sequence separator requires another item",
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
    // `name @ ..` names a rest a pattern matched, which a built sequence has none of: K's
    // `#as` outside a pattern, the form's own refusal whatever the cell.
    assert_rejects!(
        krs_syntax::parse_k_sequence_expression(
            krs_syntax::parse::tokens_from_source("S1 ~> tail @ ..").unwrap()
        ),
        error if matches!(error.kind(), SyntaxErrorKind::InvalidPatternAs { .. })
    );
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
    // Brackets that end the last value of `k -> v` items are an index, not
    // the update `base[key <- value]`, and so are brackets that compare with
    // a negative operand, `i < -1`, which holds no `<-`.
    for source in ["X -> m[k]", "X -> m[i < -1]", "X -> 1, Y -> l[0]"] {
        let indexed = krs_syntax::parse_map_expression(
            krs_syntax::parse::tokens_from_source(source).unwrap(),
        )
        .unwrap();
        assert!(matches!(indexed.body(), MapBody::Items { .. }), "{source}");
    }
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
            "X -> V, Y ->",
            SyntaxErrorKind::RustSyntax("unexpected end of input, expected an expression".into()),
        ),
        // A built map writes each entry over the one before, so a key written twice is refused,
        // as a collection literal refuses it.
        (
            "X -> V, X -> W",
            SyntaxErrorKind::InvalidExpressionNotation {
                reason: "the key `X` is written twice; two keys written as the same term are one key, so the earlier entry's value would never be read: write the key once, with the value it maps to".into(),
            },
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
        // A built map is a literal written over the map its rest names, as `map![..]` is.
        error if matches!(
            error.kind(),
            SyntaxErrorKind::InvalidExpressionNotation { reason }
                if reason.contains("an anonymous `..` names no map")
        )
    );
}

/// A result that names no cell keeps the whole state its subject bound: every cell as it was.
/// Whether the sentence may say that is its form's to judge (a claim may, a rule changes no cell).
#[test]
fn a_cells_result_may_keep_the_whole_state() {
    let unchanged = krs_syntax::parse_cells_expression(
        krs_syntax::parse::tokens_from_source("..state").unwrap(),
    )
    .unwrap();
    assert!(unchanged.entries().is_empty());
    assert!(
        matches!(unchanged.remainder(), StateMacroRemainder::Reuse { binding, .. } if binding == "state")
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

/// A result's anonymous `..` leaves the cells it does not name as they are, as its absence does:
/// it is read as no remainder, and it ends the record.
#[test]
fn a_results_anonymous_rest_is_no_remainder() {
    for source in ["k: KCell(.K), ..", "k: KCell(.K), ..,"] {
        let expression = krs_syntax::parse_cells_expression(
            krs_syntax::parse::tokens_from_source(source).unwrap(),
        )
        .unwrap();
        assert!(
            matches!(expression.remainder(), StateMacroRemainder::Exact),
            "{source}"
        );
    }
    let error = krs_syntax::parse_cells_expression(
        krs_syntax::parse::tokens_from_source("k: KCell(.K), .., env: Cell(E)").unwrap(),
    )
    .unwrap_err();
    assert_eq!(
        error.kind(),
        &SyntaxErrorKind::InvalidStateMacro {
            macro_name: "cells",
            reason: "the configuration remainder must be last",
        }
    );
}

/// A result that names no cell, with `..` or without it, leaves every cell as it is: it parses,
/// with no entry and no remainder, as `..state` alone parses with no entry. A pattern that names
/// no cell is refused.
#[test]
fn a_result_naming_no_cell_is_every_cell_unchanged() {
    for source in ["", "..", "..,"] {
        let expression = krs_syntax::parse_cells_expression(
            krs_syntax::parse::tokens_from_source(source).unwrap(),
        )
        .unwrap();
        assert!(expression.entries().is_empty(), "{source:?}");
        assert!(
            matches!(expression.remainder(), StateMacroRemainder::Exact),
            "{source:?}"
        );
    }
    for source in ["", "..", "state @ .."] {
        let error =
            krs_syntax::parse_cells_pattern(krs_syntax::parse::tokens_from_source(source).unwrap())
                .unwrap_err();
        assert_eq!(
            error.kind(),
            &SyntaxErrorKind::InvalidStateMacro {
                macro_name: "cells",
                reason: "at least one cell clause is required",
            },
            "{source:?}"
        );
    }
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

/// A result remainder that names no subject frame of its kind is refused by
/// [`krs_syntax::StateRuleItem::reuse_refusal`], which pairs the result with the subject, not
/// by parsing: the entry it stands in is judged against its cell's kind first.
#[test]
fn a_result_remainder_of_another_frame_is_refused_after_parsing() {
    let reuse = SyntaxErrorKind::UnsupportedRuleBody {
        reason: "a result remainder must reuse a subject frame of the same kind",
    };
    for source in [
        // An unbound frame.
        "fn bad(x: Term<Id>, cells! { k: KCell(x, tail @ ..) }: Machine) -> Machine { cells! { k: KCell(x, ..missing) } }",
        // The configuration's remainder as a computation's tail.
        "fn bad(x: Term<Id>, cells! { k: KCell(x, tail @ ..), state @ .. }: Machine) -> Machine { cells! { k: KCell(x, ..state), ..state } }",
        // Instances written on a plain cell over no instances the subject binds (the class
        // matrix's `cells/result/pc/[k::fragment![..], ..instances0]`).
        "fn bad(x: Term<Id>, old: Term<Int>, cells! { k: KCell(x, tail @ ..), pc: Cell(old) }: Machine) -> Machine { cells! { k: KCell(..tail), pc: [k::fragment![crate::Job { payload: x, ..old }], ..instances0] } }",
    ] {
        let rule = krs_syntax::StateRuleItem::parse_source(source)
            .unwrap_or_else(|error| panic!("{source}: {error}"));
        assert_eq!(
            rule.reuse_refusal().as_ref().map(SyntaxError::kind),
            Some(&reuse),
            "{source}"
        );
    }
    let rule = krs_syntax::StateRuleItem::parse_source(
        "fn good(x: Term<Id>, cells! { k: KCell(x, tail @ ..), state @ .. }: Machine) -> Machine { cells! { k: KCell(..tail), ..state } }",
    )
    .unwrap();
    assert!(rule.reuse_refusal().is_none());
}

#[test]
fn whole_configuration_rules_reject_non_rule_shells() {
    for (source, expected_kind) in [
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
                reason: krs_syntax::BINDER_LIST_CONTRACT,
            },
        ),
        (
            "fn bad(x: Term<Id>, unused: Term<Int>, cells! { k: KCell(x, tail @ ..) }: Machine) -> Machine { cells! { k: KCell(x, ..tail) } }",
            SyntaxErrorKind::InvalidBinderList {
                reason: "binder `unused` is declared but does not occur in the subject".to_owned(),
            },
        ),
        (
            "fn bad(v: Term<Value>, x: Term<Id>, cells! { k: KCell(x, v, tail @ ..) }: Machine) -> Machine { cells! { k: KCell(x, v, ..tail) } }",
            SyntaxErrorKind::UnsupportedRuleSignature {
                reason: krs_syntax::BINDER_LIST_CONTRACT,
            },
        ),
        (
            "fn bad(tail: Term<Id>, cells! { k: KCell(tail @ ..) }: Machine) -> Machine { cells! { k: KCell(..tail) } }",
            SyntaxErrorKind::UnsupportedRuleSignature {
                reason: krs_syntax::BINDER_LIST_CONTRACT,
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
            reason: "the root must be a named path/call/record or an Int/Bool literal".into(),
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

    let error = krs_syntax::RuleBlock::parse_source("for Machine; idle: {} => {};").unwrap_err();
    assert!(
        error
            .to_string()
            .contains("a machine rule selects at least one cell"),
        "{error}"
    );
    // Two bracketed values read as one computation cell and one cons list
    // (F6); the collector checks the configuration declares them so.
    krs_syntax::RuleBlock::parse_source(
        "for Machine; two: { k: [A, ..], k2: [B, ..] } => { k: [..], k2: [..] };",
    )
    .unwrap();
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
    for source in ["frame: 3", "frame: f.x", "frame: crate::f"] {
        let error =
            krs_syntax::parse_cells_pattern(krs_syntax::parse::tokens_from_source(source).unwrap())
                .unwrap_err();
        assert_eq!(error.kind(), &group_entry, "{source}");
    }
    // `_` and `name @ pattern` are pattern-only whole entries (P4's placement): a result refuses
    // them by their classes, whatever the cell's kind.
    for (source, wildcard) in [
        ("frame: _", true),
        ("pc: _", true),
        ("frame: f @ k::fragment![crate::Frame { pc: x }]", false),
    ] {
        let error = krs_syntax::parse_cells_expression(
            krs_syntax::parse::tokens_from_source(source).unwrap(),
        )
        .unwrap_err();
        let class = if wildcard {
            krs_syntax::positions::Class::WildcardOutsidePattern
        } else {
            krs_syntax::positions::Class::AliasOutsidePattern
        };
        assert_eq!(error.kind().code(), class.code(), "{source}");
        assert_eq!(
            error.span().start().column,
            source.find(": ").unwrap() + 2,
            "{source}"
        );
    }
}

/// A leaf's content is a content root, where `..r` puts the named rest back (P6): a result's
/// `Cell([..r])` is the list `r`, as `Cell(r)` is. Below the root the brackets are a term's,
/// which hold no element.
#[test]
fn a_result_leaf_s_named_rest_alone_is_the_rest() {
    for source in ["stack: Cell([..r])", "olist: Some(Cell([..r]))"] {
        assert!(
            krs_syntax::parse_cells_expression(
                krs_syntax::parse::tokens_from_source(source).unwrap(),
            )
            .is_ok(),
            "{source}"
        );
    }
    let below = krs_syntax::parse_cells_expression(
        krs_syntax::parse::tokens_from_source("stack: Cell(list::concat([..r], s))").unwrap(),
    )
    .unwrap_err();
    assert!(matches!(
        below.kind(),
        SyntaxErrorKind::InvalidListNotation { .. }
    ));
}

#[test]
fn qualified_state_macros_in_leaf_cells_read_as_the_unqualified_ones() {
    for (qualified, unqualified) in [
        (
            "k: KCell(X, tail @ ..), env: Cell(k::map![X -> V, rest @ ..]), state @ ..",
            "k: KCell(X, tail @ ..), env: Cell(map![X -> V, rest @ ..]), state @ ..",
        ),
        (
            "k: k::configuration::KCell(X, ..), env: k::configuration::Cell(krs::map![X -> V, ..]), state @ ..",
            "k: k::configuration::KCell(X, ..), env: k::configuration::Cell(map![X -> V, ..]), state @ ..",
        ),
    ] {
        let parse = |source| {
            krs_syntax::parse_cells_pattern(krs_syntax::parse::tokens_from_source(source).unwrap())
                .unwrap()
        };
        // The two spellings differ only in token positions.
        let shape = |cells: &krs_syntax::CellsExpression| {
            let StateTerm::KSequence(_) = cells.entries()[0].value() else {
                panic!("the computation cell is a K sequence")
            };
            let StateTerm::Map(map) = cells.entries()[1].value() else {
                panic!("the env cell is a map")
            };
            let krs_syntax::MapBody::Items { items, remainder } = map.body() else {
                panic!("the map has items")
            };
            let items = items
                .iter()
                .map(|item| {
                    (
                        item.key().expression().to_token_stream().to_string(),
                        item.value().expression().to_token_stream().to_string(),
                    )
                })
                .collect::<Vec<_>>();
            (items, remainder.binding().map(ToString::to_string))
        };
        assert_eq!(shape(&parse(qualified)), shape(&parse(unqualified)));
    }
}

#[test]
fn map_patterns_reject_a_key_named_twice() {
    let repeated = SyntaxErrorKind::InvalidStateMacro {
        macro_name: "map",
        reason: "a map pattern names one key twice; \
                 its items are distinct entries of the map, so no map matches it",
    };
    assert_rejects!(
        krs_syntax::parse_map_pattern(
            krs_syntax::parse::tokens_from_source("Key(1) -> v, b -> w, Key(1) -> u, ..").unwrap()
        ),
        error if error.kind() == &repeated
    );
    assert_rejects!(
        krs_syntax::parse_cells_pattern(
            krs_syntax::parse::tokens_from_source(
                "env: k::configuration::Cell(k::map![a -> x, a -> y, ..]), state @ .."
            )
            .unwrap()
        ),
        error if error.kind() == &repeated
    );
    krs_syntax::parse_map_pattern(
        krs_syntax::parse::tokens_from_source("a -> x, b -> y, ..").unwrap(),
    )
    .unwrap();
    // Two `_` keys match two distinct entries.
    krs_syntax::parse_map_pattern(
        krs_syntax::parse::tokens_from_source("_ -> x, _ -> y, ..").unwrap(),
    )
    .unwrap();
}

/// The empty shells of a `cells!` entry are keyed at their invocation:
/// `k::map![]` path to closing delimiter, and `KCell()` at the parentheses
/// that hold its sequence (the wrapper path is a node of its own). An empty
/// payload read without its invocation has nowhere to anchor.
#[test]
fn empty_cells_entry_shells_are_keyed_at_their_invocation() {
    let source = "k: KCell(), env: Cell(k::map![])";
    let expression =
        krs_syntax::parse_cells_expression(krs_syntax::parse::tokens_from_source(source).unwrap())
            .unwrap();
    let text = |anchor: &krs_syntax::ProvenanceAnchor| {
        let (start, end) = (anchor.range().start(), anchor.range().end());
        (
            anchor.role(),
            anchor.ordinal(),
            &source[start.column..end.column],
        )
    };
    let [k, env] = expression.entries() else {
        panic!("two entries");
    };
    let StateTerm::KSequence(sequence) = k.value() else {
        panic!("`KCell()` holds a K sequence");
    };
    let anchors = sequence.provenance().unwrap();
    assert_eq!(
        anchors.iter().map(text).collect::<Vec<_>>(),
        [(ProvenanceRole::KSequencePayload, 0, "()")]
    );
    assert_eq!(sequence.payload_key(), Some(&anchors[0].key()));
    let StateTerm::Map(map) = env.value() else {
        panic!("`Cell(k::map![])` holds a map");
    };
    let anchors = map.provenance().unwrap();
    assert_eq!(
        anchors.iter().map(text).collect::<Vec<_>>(),
        [(ProvenanceRole::MapPayload, 0, "k::map![]")]
    );
    assert_eq!(map.payload_key(), Some(&anchors[0].key()));

    let alone =
        krs_syntax::parse_map_expression(krs_syntax::parse::tokens_from_source("").unwrap())
            .unwrap();
    assert!(alone.payload_key().is_none());
    assert!(alone.provenance().unwrap().is_empty());
}

/// An anonymous `..` ending a map or a set a `cells!` result builds is the literal's mistake, as
/// in any term (NT-19-1): the rest is the collection the entries are written over, and `..`
/// names none; a `cells!` pattern reads entries with it.
#[test]
fn an_anonymous_rest_in_a_built_collection_is_the_literal_s_mistake() {
    for (collection, entry) in [
        ("map", "acc: Cell(k::map![x -> y, ..])"),
        ("set", "acc: Cell(k::set![x, ..])"),
        (
            "map",
            "Sacks::bag: { k::fragment![crate::Bag { s: set![], m: k::map![x -> y, ..] }], ..instances0 }",
        ),
        (
            "set",
            "Sacks::bag: { k::fragment![crate::Bag { s: k::set![x, ..], m: map![] }], ..instances0 }",
        ),
    ] {
        let source = format!("k: KCell(..tail), {entry}, ..state");
        let error = krs_syntax::parse_cells_expression(source.parse().unwrap())
            .map(|_| ())
            .unwrap_err();
        assert_eq!(
            error.kind().code().as_str(),
            "krs::syntax::invalid-expression-notation",
            "{source}: {error}"
        );
        assert!(
            error
                .to_string()
                .contains(&format!("`{collection}![..]` is a literal")),
            "{source}: {error}"
        );
    }
}

/// A `cells!` fragment's child is its cell's entry, which the descriptor carries as a term: a
/// result's anonymous `..` in a child's list is the term reader's refusal, a result's map literal
/// with an anonymous `..` the literal's, and a pattern child's map read is said as not supported
/// yet. A fragment whose own record is no term keeps the whole entry's message.
#[test]
fn a_result_instance_child_the_term_reader_refuses_waits_for_its_record() {
    // The instance record is the outer construct: whether `..me` updates an instance the subject
    // matched is judged first, so its child's list rest is read out and carried.
    let result = "tjob: [k::fragment![crate::T { tk: [x, ..], ..me }], ..]";
    let source = format!(
        "fn step(x: Term<Id>, cells! {{ k: KCell(x, ..), tjob: [..] }}: Machine) -> Machine {{ cells! {{ {result} }} }}"
    );
    let rule = krs_syntax::StateRuleItem::parse_source(&source).unwrap();
    let refusal = rule.misplaced_tail().expect("the child's fault is carried");
    assert_eq!(
        refusal.kind().code().as_str(),
        "krs::syntax::invalid-list-notation"
    );
    let StateTerm::Instances(list) = rule.result().unwrap().entries()[0].value() else {
        panic!("an instance list");
    };
    let record = list.instances().next().expect("one instance");
    assert!(record.fields().is_empty(), "the faulty child is read out");
    // Read alone, where no entry is judged, the payload is refused as written.
    let tokens = krs_syntax::parse::tokens_from_source(result).unwrap();
    let alone = krs_syntax::parse_cells_expression(tokens).unwrap_err();
    assert_eq!(alone.kind(), refusal.kind());
}

#[test]
fn a_fragment_child_s_notation_is_refused_for_what_it_is() {
    let group_entry = SyntaxErrorKind::InvalidStateMacro {
        macro_name: "cells",
        reason: "nested cell entries are a binder, `_`, or fragment!",
    };
    let list_rest = krs_syntax::parse_cells_expression(
        krs_syntax::parse::tokens_from_source(
            "hcell: k::fragment![crate::H { hl: [x, ..], hb: 0 }]",
        )
        .unwrap(),
    )
    .unwrap_err();
    assert!(
        matches!(
            list_rest.kind(),
            SyntaxErrorKind::InvalidListNotation { .. }
        ),
        "{:?}",
        list_rest.kind()
    );
    // A map read in a pattern's child is the child's entry: the fragment is the group record of
    // its children's entries (TRI-D2), the map child a map state.
    let source = "mcell: k::fragment![crate::M { mm: k::map![y -> x, ..], .. }]";
    let cells =
        krs_syntax::parse_cells_pattern(krs_syntax::parse::tokens_from_source(source).unwrap())
            .unwrap();
    let krs_syntax::StateTerm::Record(record) = cells.entries()[0].value() else {
        panic!("{source} is no group record");
    };
    assert!(record.is_open(), "{source}");
    assert!(
        matches!(record.fields()[0].value(), krs_syntax::StateTerm::Map(_)),
        "{source}"
    );
    let source = "mcell: k::fragment![crate::M { mm: k::map![y -> x, ..], mn: 0 }]";
    let error =
        krs_syntax::parse_cells_expression(krs_syntax::parse::tokens_from_source(source).unwrap())
            .unwrap_err();
    assert!(
        matches!(
            error.kind(),
            SyntaxErrorKind::InvalidExpressionNotation { .. }
        ),
        "{source}: {:?}",
        error.kind()
    );
    let source = "outer: k::fragment![Outer { flag: 0, .. } | Outer { flag: 1, .. }]";
    let error =
        krs_syntax::parse_cells_pattern(krs_syntax::parse::tokens_from_source(source).unwrap())
            .unwrap_err();
    assert_eq!(error.kind(), &group_entry, "{source}");
}

/// An item after a `KCell(..)` entry's tail is the computation cell's mistake, and `KCell(..)`
/// on a cell of another kind is the wrapper's mistake first: a rule's parser keeps the entry,
/// its items in order before the tail, and carries the refusal for the judgement that knows the
/// cell's kind. A parse no such judgement follows refuses it at once.
#[test]
fn an_item_after_a_kcell_tail_waits_for_the_cells_kind() {
    let misplaced = SyntaxErrorKind::InvalidStateMacro {
        macro_name: "k",
        reason: "the sequence tail must be last",
    };
    // Each rule, the side whose entry writes an item after its tail, and its items.
    for (parameters, subject, result, in_subject, items) in [
        (
            "x: Term<Id>",
            "acct: KCell(.., x)",
            "acct: KCell(x, ..)",
            true,
            1,
        ),
        (
            "x: Term<Id>, y: Term<Id>",
            "acct: KCell(x, .., y)",
            "acct: KCell(x, ..)",
            true,
            2,
        ),
        (
            "x: Term<Id>, y: Term<Id>",
            "acct: KCell(x ~> .. ~> y)",
            "acct: KCell(x, ..)",
            true,
            2,
        ),
        (
            "x: Term<Id>",
            "acct: KCell(x, ..)",
            "acct: KCell(x, .., x)",
            false,
            2,
        ),
    ] {
        let source = format!(
            "fn step({parameters}, cells! {{ {subject} }}: Machine) -> Machine {{ cells! {{ {result} }} }}"
        );
        let rule = krs_syntax::StateRuleItem::parse_source(&source).unwrap();
        let refusal = rule
            .misplaced_tail()
            .expect("the item after the tail is carried");
        assert_eq!(refusal.kind(), &misplaced, "{source}");
        let carried = if in_subject {
            rule.subject()
        } else {
            rule.result().unwrap()
        };
        let StateTerm::KSequence(sequence) = carried.entries()[0].value() else {
            panic!("{source}: `KCell(..)` holds a K sequence");
        };
        assert_eq!(sequence.items().len(), items, "{source}");
        assert!(sequence.misplaced_tail().is_some(), "{source}");
        // Read alone, where no kind is judged, the payload is refused as written.
        let tokens = |text: &str| krs_syntax::parse::tokens_from_source(text).unwrap();
        let alone = if in_subject {
            krs_syntax::parse_cells_pattern(tokens(subject)).unwrap_err()
        } else {
            krs_syntax::parse_cells_expression(tokens(result)).unwrap_err()
        };
        assert_eq!(alone.kind(), &misplaced, "{source}");
    }
    // In order, nothing is carried; what follows the tail that is no item is refused as written.
    let rule = krs_syntax::StateRuleItem::parse_source(
        "fn step(x: Term<Id>, cells! { acct: KCell(x, ..) }: Machine) -> Machine { cells! { acct: KCell(x, ..) } }",
    )
    .unwrap();
    assert!(rule.misplaced_tail().is_none());
    for subject in [
        "acct: KCell(.., r @ ..)",
        "acct: KCell(.., x, ..)",
        "acct: KCell(x, .., y ~> z)",
    ] {
        let source = format!(
            "fn step(x: Term<Id>, cells! {{ {subject} }}: Machine) -> Machine {{ cells! {{ acct: KCell(x, ..) }} }}"
        );
        assert!(
            krs_syntax::StateRuleItem::parse_source(&source).is_err(),
            "{source}"
        );
    }
}

/// An initializer's `k!` is the cell's whole initial content: an anonymous `..` keeps no rest
/// there, and `name @ ..` names a rest no pattern matched, whatever the cell's kind.
#[test]
fn an_initializers_k_rest_is_refused_by_its_form() {
    let source = "fn init() -> Self { Self { k: k::k![Cmd::Go(), ..] } }";
    let error = krs_syntax::InitializerFunction::parse_source(source).unwrap_err();
    assert!(
        matches!(
            error.kind(),
            SyntaxErrorKind::UnsupportedInitializerBody { .. }
        ),
        "{error}"
    );
    assert_eq!(error.span().start().column, source.find("..").unwrap());
    for source in [
        "fn init() -> Self { Self { k: k::k![Cmd::Go(), r @ ..] } }",
        "fn init() -> Self { Self { env: k::map![0 -> 1, r @ ..] } }",
    ] {
        let error = krs_syntax::InitializerFunction::parse_source(source).unwrap_err();
        assert!(
            matches!(error.kind(), SyntaxErrorKind::InvalidPatternAs { .. }),
            "{source}: {error}"
        );
        assert_eq!(
            error.span().start().column,
            source.find("r @").unwrap(),
            "{source}"
        );
    }
}
