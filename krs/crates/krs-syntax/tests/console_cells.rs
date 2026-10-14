//! Stream and exit cell attributes and ground initializer terms (KF-035).

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
fn literals_and_qualified_calls_are_readable_initializer_terms() {
    let initializer = krs_syntax::InitializerFunction::parse_source(
        "fn init(pgm: Stmt) -> Self { Self { k: k![pgm], input: list::empty(), status: 1, low: -1 } }",
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
    // A bare call is still a host call, not a term.
    krs_syntax::InitializerFunction::parse_source("fn init() -> Self { Self { status: make() } }")
        .unwrap_err();
}
