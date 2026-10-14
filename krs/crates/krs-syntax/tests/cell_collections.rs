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

#[test]
fn a_bracket_that_reads_both_ways_carries_its_list_reading() {
    let block = krs_syntax::RuleBlock::parse_source(
        r"
        for Machine;
        use Cmd::*;

        retire: { job: [Job { payload: 0 }, ..] } => { job: [Job { payload: 1 }, ..] };

        pick: { k: [Pick(), ..], job: [Job { payload: p }, ..] } => { k: [p, ..], job: [..] };

        tail: { job: [.., Job { payload: p }] } => { job: [..] };

        head: { k: [Enqueue { value: v }, ..] } => { k: [..] };

        labelled: { job: [first @ Job { payload: 0 }, ..] } => { job: [..] };
        ",
    )
    .unwrap();
    let clauses = block.clauses();

    // `retire` names no other cell: it reads as `job`'s head, with the List
    // reading beside it for the collector to choose.
    let retire = &clauses[0];
    assert_eq!(retire.computation_cell().unwrap(), "job");
    assert!(retire.head_result().is_some());
    let alternative = retire.bracket_alternative().unwrap();
    assert_eq!(alternative.cell(), "job");
    let (StateTerm::Instances(before), Some(StateTerm::Instances(after))) =
        (alternative.before(), alternative.after())
    else {
        panic!("expected List readings on both sides");
    };
    assert_eq!(before.delimiter(), InstanceListDelimiter::Bracket);
    assert_eq!(before.front().len(), 1);
    assert!(matches!(before.front()[0].rest(), InstanceRest::Exact));
    assert_eq!(after.front().len(), 1);
    let anchors = retire.provenance().unwrap();
    for role in [
        krs_syntax::ProvenanceRole::RuleLeftCellsField,
        krs_syntax::ProvenanceRole::RuleRightCellsField,
        krs_syntax::ProvenanceRole::RuleLeftCellsInstance,
        krs_syntax::ProvenanceRole::RuleLeftCellsInstanceField,
        krs_syntax::ProvenanceRole::RuleLeftCellsInstancesRest,
        krs_syntax::ProvenanceRole::RuleRightCellsInstance,
        krs_syntax::ProvenanceRole::RuleRightCellsInstancesRest,
    ] {
        assert_eq!(
            anchors
                .iter()
                .filter(|anchor| anchor.role() == role)
                .count(),
            1,
            "{role:?}"
        );
    }

    // `k` is the computation cell, so `job` is the collection.
    let pick = &clauses[1];
    assert_eq!(pick.computation_cell().unwrap(), "k");
    assert!(pick.bracket_alternative().is_none());
    assert!(matches!(
        pick.extras(),
        [RuleExtra::RewriteState { cell, .. }] if cell == "job"
    ));

    // A back instance reads only as a List collection.
    let tail = &clauses[2];
    assert!(tail.head_result().is_none());
    assert!(tail.bracket_alternative().is_none());

    // A head record reads both ways too; the collector keeps the head.
    let head = &clauses[3];
    assert_eq!(head.computation_cell().unwrap(), "k");
    assert!(head.bracket_alternative().is_some());

    // A labelled front record cannot be a whole head: it reads as a List
    // collection only.
    let labelled = &clauses[4];
    assert!(labelled.head_result().is_none());
    assert!(labelled.bracket_alternative().is_none());
    assert!(labelled.bindings().is_empty());
}
