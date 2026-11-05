//! Stream, exit and unobservable cell attributes and ground initializer terms (KF-035).

use krs_syntax::KrsSyntax;
use krs_syntax::{InitializerCellContent, ProvenanceRole, StateTerm};

#[test]
fn stream_and_exit_keys_parse_with_anchors() {
    let input = krs_syntax::CellAttributePayload::parse_source(r#"stream = "stdin""#).unwrap();
    assert_eq!(input.stream().unwrap().value(), "stdin");
    assert!(input.exit().is_none());
    let status = krs_syntax::CellAttributePayload::parse_source("exit").unwrap();
    assert!(status.exit().is_some());
    assert!(status.stream().is_none());
    let both =
        krs_syntax::CellAttributePayload::parse_source(r#"color = "red", stream = "stdout", exit"#)
            .unwrap();
    assert_eq!(
        both.provenance()
            .unwrap()
            .iter()
            .map(krs_syntax::ProvenanceAnchor::role)
            .collect::<Vec<_>>(),
        [
            ProvenanceRole::ConfigurationCellColor,
            ProvenanceRole::ConfigurationCellStream,
            ProvenanceRole::ConfigurationCellExit,
        ]
    );
}

#[test]
fn configuration_anchors_stream_and_exit_per_field() {
    let declaration = krs_syntax::ConfigurationDeclaration::parse_source(
        r#"struct Machine {
            #[k::cell] k: KSequence,
            #[k::cell(stream = "stdin")] input: List,
            #[k::cell(exit)] status: Int,
        }"#,
    )
    .unwrap();
    let anchors = declaration.provenance().unwrap();
    let stream = anchors
        .iter()
        .find(|anchor| anchor.role() == ProvenanceRole::ConfigurationCellStream)
        .unwrap();
    assert_eq!(stream.ordinal(), 1);
    let exit = anchors
        .iter()
        .find(|anchor| anchor.role() == ProvenanceRole::ConfigurationCellExit)
        .unwrap();
    assert_eq!(exit.ordinal(), 2);
}

#[test]
fn literals_and_calls_are_readable_initializer_terms() {
    let initializer = krs_syntax::InitializerFunction::parse_source(
        "fn init(pgm: Stmt) -> Self { Self { k: k![pgm], input: list::empty(), status: 1, low: -1, made: make(pgm), qualified: self::make(pgm) } }",
    )
    .unwrap();
    for cell in &initializer.cells()[1..] {
        let InitializerCellContent::Leaf {
            value: StateTerm::Term(_),
            computation: false,
            inferred_constructor: true,
            ..
        } = cell.content()
        else {
            panic!("{} is not a readable term", cell.name());
        };
    }
    // The cell forms are no terms: `Some(..)` holds one value, written without attributes or
    // generic arguments, and `Cell::new(..)` one argument.
    for (source, reason) in [
        (
            "fn init() -> Self { Self { status: Some(1, 2) } }",
            "an optional cell's `Some(..)` takes exactly one expression, the value the cell starts present with",
        ),
        (
            "fn init() -> Self { Self { status: #[x] Some(1) } }",
            "an optional cell's start is written `Some(value)`, without attributes or generic arguments",
        ),
        (
            "fn init() -> Self { Self { status: Some::<Int>(1) } }",
            "an optional cell's start is written `Some(value)`, without attributes or generic arguments",
        ),
        (
            "fn init() -> Self { Self { status: Cell::new(1, 2) } }",
            "`Cell::new(..)` and `KCell::new(..)` take exactly one argument, the cell's value",
        ),
    ] {
        let error = krs_syntax::InitializerFunction::parse_source(source).unwrap_err();
        assert!(error.to_string().contains(reason), "{source}: {error}");
    }
}

#[test]
fn unobservable_is_a_bare_flag_with_an_anchor() {
    let scratch = krs_syntax::CellAttributePayload::parse_source("unobservable").unwrap();
    assert!(scratch.unobservable().is_some());
    assert!(scratch.exit().is_none());
    let keyed =
        krs_syntax::CellAttributePayload::parse_source(r#"unobservable, color = "red""#).unwrap();
    assert_eq!(
        keyed
            .provenance()
            .unwrap()
            .iter()
            .map(krs_syntax::ProvenanceAnchor::role)
            .collect::<Vec<_>>(),
        [
            ProvenanceRole::ConfigurationCellColor,
            ProvenanceRole::ConfigurationCellUnobservable,
        ]
    );
    for (source, expected) in [
        (
            r#"unobservable = "x""#,
            krs_syntax::SyntaxErrorKind::InvalidCellAttribute {
                reason: "unobservable takes no value",
            },
        ),
        (
            "unobservable, unobservable",
            krs_syntax::SyntaxErrorKind::DuplicateArgument {
                name: "unobservable",
            },
        ),
    ] {
        let error = krs_syntax::CellAttributePayload::parse_source(source).unwrap_err();
        assert_eq!(error.kind(), &expected, "{source}");
    }
}

#[test]
fn configuration_anchors_unobservable_per_field() {
    let declaration = krs_syntax::ConfigurationDeclaration::parse_source(
        r"struct Machine {
            #[k::cell] k: KSequence,
            #[k::cell(unobservable)] scratch: Int,
        }",
    )
    .unwrap();
    let anchors = declaration.provenance().unwrap();
    let unobservable = anchors
        .iter()
        .find(|anchor| anchor.role() == ProvenanceRole::ConfigurationCellUnobservable)
        .unwrap();
    assert_eq!(unobservable.ordinal(), 1);
}
