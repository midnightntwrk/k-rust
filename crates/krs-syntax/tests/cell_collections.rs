//! Optional-cell and cell-collection entries (KF-023): `Some`/`None` and
//! instance lists in `cells!` and readable machine records.

use krs_syntax::KrsSyntax;
use krs_syntax::{
    InstanceListDelimiter, InstanceRest, RuleExtra, StateMacroRemainder, StateTerm,
    parse_cells_expression, parse_cells_pattern,
};

fn pattern(source: &str) -> krs_syntax::CellsExpression {
    parse_cells_pattern(krs_syntax::parse::tokens_from_source(source).unwrap()).unwrap()
}

fn expression(source: &str) -> krs_syntax::CellsExpression {
    parse_cells_expression(krs_syntax::parse::tokens_from_source(source).unwrap()).unwrap()
}

#[test]
fn optional_entries_are_present_or_absent() {
    let subject = pattern("counter: Some(Cell(n)), mark: None, state @ ..");
    assert!(matches!(
        subject.entries()[0].value(),
        StateTerm::Present(inner) if matches!(**inner, StateTerm::Term(_))
    ));
    assert!(matches!(subject.entries()[1].value(), StateTerm::Absent(_)));

    let result = expression("counter: None, mark: Some(k::fragment![Mark { seen: n }]), ..state");
    assert!(matches!(result.entries()[0].value(), StateTerm::Absent(_)));
    assert!(matches!(result.entries()[1].value(), StateTerm::Present(_)));
}

#[test]
fn instance_lists_keep_labels_rests_and_delimiters() {
    let subject = pattern(
        "Threads::thread: { me @ k::fragment![Thread { k: k::k![Spawn(b), tail @ ..], .. }], instances0 @ .. }, state @ ..",
    );
    let StateTerm::Instances(list) = subject.entries()[0].value() else {
        panic!("expected an instance list");
    };
    assert_eq!(list.delimiter(), InstanceListDelimiter::Brace);
    assert_eq!(list.front().len(), 1);
    assert!(list.back().is_empty());
    assert_eq!(list.front()[0].label().unwrap(), "me");
    assert!(list.front()[0].is_fragment());
    assert!(matches!(list.front()[0].rest(), InstanceRest::Open(_)));
    assert!(
        matches!(list.rest(), StateMacroRemainder::Bind { binding, .. } if binding == "instances0")
    );

    let result = expression(
        "Threads::thread: { k::fragment![Thread { k: k::k![n, ..tail], ..me }], k::fragment![Thread { id: n, .. }], ..instances0 }, ..state",
    );
    let StateTerm::Instances(list) = result.entries()[0].value() else {
        panic!("expected an instance list");
    };
    assert_eq!(list.front().len(), 2);
    assert!(matches!(list.front()[0].rest(), InstanceRest::Update { label, .. } if label == "me"));
    assert!(matches!(list.front()[1].rest(), InstanceRest::Open(_)));
}

#[test]
fn readable_records_lower_optional_and_collection_entries_to_state_rewrites() {
    let block = krs_syntax::RuleBlock::parse_source(
        r"
        for Machine;
        use Cmd::*;

        enable: { k: [Enable(), ..], counter: None } => { k: [..], counter: Some(0) };

        spawn: {
            thread: { me @ Thread { k: [Spawn(body), ..], .. }, .. },
        } => {
            thread: { Thread { k: [0, ..], ..me }, Thread { k: [body], .. }, .. },
        };

        pop: {
            k: [Pop(), ..],
            job: [.., Job { payload: p, .. }],
        } => {
            k: [p, ..],
            job: [..],
        };
        ",
    )
    .unwrap();

    let [
        RuleExtra::RewriteState {
            cell,
            before,
            after: Some(after),
            ..
        },
    ] = block.clauses()[0].extras()
    else {
        panic!("expected one optional-cell rewrite");
    };
    assert_eq!(cell, "counter");
    assert!(matches!(before.as_ref(), StateTerm::Absent(_)));
    assert!(matches!(after.as_ref(), StateTerm::Present(_)));

    let [
        RuleExtra::RewriteState {
            before,
            after: Some(after),
            ..
        },
    ] = block.clauses()[1].extras()
    else {
        panic!("expected one collection rewrite");
    };
    let (StateTerm::Instances(subject), StateTerm::Instances(result)) =
        (before.as_ref(), after.as_ref())
    else {
        panic!("expected instance lists");
    };
    assert_eq!(subject.front()[0].label().unwrap(), "me");
    assert_eq!(result.front().len(), 2);

    let state = block.clauses()[2]
        .extras()
        .iter()
        .find_map(|extra| match extra {
            RuleExtra::RewriteState { before, .. } => Some(before),
            _ => None,
        })
        .unwrap();
    let StateTerm::Instances(list) = state.as_ref() else {
        panic!("expected a List collection pattern");
    };
    assert_eq!(list.delimiter(), InstanceListDelimiter::Bracket);
    assert!(list.front().is_empty());
    assert_eq!(list.back().len(), 1);
}
