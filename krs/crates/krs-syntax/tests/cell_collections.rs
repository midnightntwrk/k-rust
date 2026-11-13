//! Optional-cell and cell-collection entries (KF-023): `Some`/`None` and
//! instance lists in `cells!` and readable machine records.

use krs_syntax::KrsSyntax;
use krs_syntax::{
    InstanceListDelimiter, InstanceRest, MapBody, RuleExtra, StateMacroRemainder, StateTerm,
    parse_cells_expression, parse_cells_pattern,
};

fn pattern(source: &str) -> krs_syntax::CellsExpression {
    parse_cells_pattern(krs_syntax::parse::tokens_from_source(source).unwrap()).unwrap()
}

fn expression(source: &str) -> krs_syntax::CellsExpression {
    parse_cells_expression(krs_syntax::parse::tokens_from_source(source).unwrap()).unwrap()
}

/// The refusal a readable clause's subject braces carry where the entry reader reads them as
/// instance braces and the instance reader does not take their items: the clause parses, and
/// the collector judges the braces by the cell's kind first, raising this refusal only where the
/// kind admits them (TOP-BRACE-ONE). Its kind, its text, and the columns its span covers.
fn carried_braces_refusal(source: &str) -> (krs_syntax::SyntaxErrorKind, String, usize, usize) {
    let block = krs_syntax::RuleBlock::parse_source(source)
        .unwrap_or_else(|error| panic!("{source}: {error}"));
    let refusal = block.clauses()[0]
        .pairing_refusal()
        .unwrap_or_else(|| panic!("{source}: no refusal carried"));
    (
        refusal.kind().clone(),
        refusal.to_string(),
        refusal.span().start().column,
        refusal.span().end().column,
    )
}

/// The columns of the first occurrence of `token` in `source`.
fn columns(source: &str, token: &str) -> (usize, usize) {
    let start = source.find(token).expect("the token occurs");
    (start, start + token.len())
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

    // A back record also reads as a `List` cell's last element: the clause
    // takes that reading and carries the List collection's beside it.
    let pop = &block.clauses()[2];
    assert!(matches!(
        pop.extras(),
        [RuleExtra::RewriteList { cell, .. }] if cell == "job"
    ));
    let alternative = pop.bracket_alternative().unwrap();
    assert_eq!(alternative.cell(), "job");
    let StateTerm::Instances(list) = alternative.before() else {
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
    // Each reading keys the cell's names, the List reading its instances.
    let anchors = retire.provenance().unwrap();
    for (role, count) in [
        (krs_syntax::ProvenanceRole::RuleLeftCellsField, 2),
        (krs_syntax::ProvenanceRole::RuleRightCellsField, 2),
        (krs_syntax::ProvenanceRole::RuleLeftCellsInstance, 1),
        (krs_syntax::ProvenanceRole::RuleLeftCellsInstanceField, 1),
        (krs_syntax::ProvenanceRole::RuleLeftCellsInstancesRest, 1),
        (krs_syntax::ProvenanceRole::RuleRightCellsInstance, 1),
        (krs_syntax::ProvenanceRole::RuleRightCellsInstancesRest, 1),
    ] {
        assert_eq!(
            anchors
                .iter()
                .filter(|anchor| anchor.role() == role)
                .count(),
            count,
            "{role:?}"
        );
    }
    assert_eq!(
        retire.computation_cell_keys().cell(),
        Some(&krs_syntax::ProvenanceRole::RuleLeftCellsField.key(1))
    );
    assert_eq!(
        retire.computation_cell_keys().result_cell(),
        Some(&krs_syntax::ProvenanceRole::RuleRightCellsField.key(1))
    );

    // `k` is the computation cell, so `job` is a collection or a list: it
    // reads as list elements with the List reading beside it.
    let pick = &clauses[1];
    assert_eq!(pick.computation_cell().unwrap(), "k");
    assert!(matches!(
        pick.extras(),
        [RuleExtra::RewriteList { cell, .. }] if cell == "job"
    ));
    assert_eq!(pick.bracket_alternative().unwrap().cell(), "job");
    pick.provenance().unwrap();

    // A back record reads as a List collection's back instance and as a
    // list's last element, never as a head.
    let tail = &clauses[2];
    assert!(tail.head_result().is_none());
    assert!(matches!(
        tail.extras(),
        [RuleExtra::RewriteList { cell, .. }] if cell == "job"
    ));
    let alternative = tail.bracket_alternative().unwrap();
    let StateTerm::Instances(back) = alternative.before() else {
        panic!("expected a List reading");
    };
    assert_eq!(back.back().len(), 1);
    tail.provenance().unwrap();

    // A head record reads both ways too; the collector keeps the head.
    let head = &clauses[3];
    assert_eq!(head.computation_cell().unwrap(), "k");
    assert!(head.bracket_alternative().is_some());

    // A labelled front record reads both ways as well: as the computation
    // cell's head, `first` aliases the item; as a List collection's front,
    // it labels the instance. The collector keeps the cell's own reading.
    let labelled = &clauses[4];
    assert!(labelled.head_result().is_some());
    assert!(labelled.bracket_alternative().is_some());
    assert_eq!(labelled.bindings(), ["first"]);
}

/// An item-less `[..]` matches whatever its cell holds: it reads as the cell's
/// `_`, keyed at the brackets, with its instance list beside it for a
/// collection; `[..] => [..]` keeps the cell as `_` does, and so does
/// `Some([..]) => Some([..])` the present cell.
#[test]
fn an_item_less_bracket_reads_as_its_wildcard_beside_its_instances() {
    let source = r"
        for Machine;
        use Cmd::*;

        read: { k: [Go(), ..], stack: [..] } => { k: [..] };

        kept: { k: [Go(), ..], stack: [..] } => { k: [..], stack: [..] };

        two: { stack: [..], seq: [..], pc: x } => { pc: x + 1 };

        present: { k: [Go(), ..], olist: Some([..]) } => { k: [..], olist: Some([..]) };
        ";
    let block = krs_syntax::RuleBlock::parse_source(source).unwrap();
    let clauses = block.clauses();
    for clause in &clauses[..2] {
        assert!(matches!(
            clause.extras(),
            [RuleExtra::RewriteCell { cell, after: None, .. }] if cell == "stack"
        ));
        let alternative = clause.bracket_alternative().unwrap();
        assert_eq!(alternative.cell(), "stack");
        let StateTerm::Instances(before) = alternative.before() else {
            panic!("expected the instance list");
        };
        assert!(before.front().is_empty() && before.back().is_empty());
        let anchors = clause.provenance().unwrap();
        let [wildcard] = anchors
            .iter()
            .filter(|anchor| anchor.role() == krs_syntax::ProvenanceRole::RuleLeftWildcard)
            .collect::<Vec<_>>()[..]
        else {
            panic!("one wildcard");
        };
        assert_eq!(anchored(source, wildcard), "[..]");
    }
    // Only one value's other reading is carried: the first is `_`, a later
    // one keeps its instance list.
    let two = &clauses[2];
    assert_eq!(two.bracket_alternative().unwrap().cell(), "stack");
    assert!(matches!(
        two.extras(),
        [RuleExtra::RewriteCell { cell: stack, .. }, RuleExtra::RewriteState { cell: seq, .. }, ..]
            if stack == "stack" && seq == "seq"
    ));
    let present = &clauses[3];
    assert!(matches!(
        present.extras(),
        [RuleExtra::RewriteState { cell, after: None, .. }] if cell == "olist"
    ));
    present.provenance().unwrap();
}

/// The text `anchor` selects in `source`.
fn anchored<'a>(source: &'a str, anchor: &krs_syntax::ProvenanceAnchor) -> &'a str {
    let offset = |at: proc_macro2::LineColumn| {
        source
            .split_inclusive('\n')
            .take(at.line - 1)
            .map(str::len)
            .sum::<usize>()
            + at.column
    };
    &source[offset(anchor.range().start())..offset(anchor.range().end())]
}

/// The text of the anchor that holds `key` among `anchors`.
fn anchored_key<'a>(
    source: &'a str,
    anchors: &[krs_syntax::ProvenanceAnchor],
    key: Option<&krs_ir::ProvenanceKey>,
) -> &'a str {
    let key = key.expect("the shell is keyed");
    let [anchor] = anchors
        .iter()
        .filter(|anchor| &anchor.key() == key)
        .collect::<Vec<_>>()[..]
    else {
        panic!("one anchor holds {key:?}");
    };
    anchored(source, anchor)
}

/// The fields of the first instance of `state`, an instance list.
fn first_instance_fields(state: &StateTerm) -> &[krs_syntax::InstanceField] {
    let StateTerm::Instances(list) = state else {
        panic!("expected an instance list");
    };
    list.front()[0].fields()
}

/// A `cells!` instance's empty `k::k![]` and `map![]` children are keyed at
/// their invocation, their own delimited text.
#[test]
fn empty_instance_children_are_keyed_at_their_invocation() {
    let source = r"
        pub fn idle(
            cells! {
                thread: { k::fragment![Thread { k: k::k![], env: map![] }], .. },
                state @ ..
            }: model::Machine,
        ) -> model::Machine {
            cells! { thread: { .. }, ..state }
        }
        ";
    let rule = krs_syntax::StateRuleItem::parse_source(source).unwrap();
    let anchors = rule.provenance().unwrap();
    let [k, env] = first_instance_fields(rule.subject().entries()[0].value()) else {
        panic!("two children");
    };
    let StateTerm::KSequence(sequence) = k.value() else {
        panic!("`k::k![]` is a K sequence");
    };
    assert_eq!(
        anchored_key(source, &anchors, sequence.payload_key()),
        "k::k![]"
    );
    let StateTerm::Map(map) = env.value() else {
        panic!("`map![]` is a map");
    };
    assert_eq!(anchored_key(source, &anchors, map.payload_key()), "map![]");
}

/// A readable instance child's empty `[]` is keyed at its brackets.
#[test]
fn an_empty_readable_instance_child_is_keyed_at_its_brackets() {
    let source = r"
        for Machine;
        use Cmd::*;

        idle: { k: [Idle(), ..], thread: { Thread { k: [], .. }, .. } } => { k: [..] };
        ";
    let block = krs_syntax::RuleBlock::parse_source(source).unwrap();
    let clause = &block.clauses()[0];
    let [RuleExtra::RewriteState { before, .. }] = clause.extras() else {
        panic!("expected one collection read");
    };
    let [child] = first_instance_fields(before) else {
        panic!("one child");
    };
    let StateTerm::KSequence(sequence) = child.value() else {
        panic!("`[]` is a K sequence");
    };
    assert_eq!(
        anchored_key(
            source,
            &clause.provenance().unwrap(),
            sequence.payload_key()
        ),
        "[]"
    );
}

/// Each instance child of an instance list, as `name: spelling` for a term
/// child and `name: (state)` for any other.
fn instance_children(state: &StateTerm) -> Vec<String> {
    let StateTerm::Instances(list) = state else {
        panic!("expected an instance list");
    };
    list.front()
        .iter()
        .chain(list.back())
        .flat_map(krs_syntax::InstanceItem::fields)
        .map(|field| match field.value() {
            StateTerm::Term(term) => format!("{}: {}", field.name(), term.spelling()),
            _ => format!("{}: (state)", field.name()),
        })
        .collect()
}

/// A readable clause's bindings, provenance anchors (role and ordinal), and
/// the instance children of its state rewrites, both sides.
type Shape = (
    Vec<String>,
    Vec<String>,
    Vec<(krs_syntax::ProvenanceRole, u32)>,
);

fn readable_shape(source: &str) -> Shape {
    let block = krs_syntax::RuleBlock::parse_source(source).unwrap();
    let clause = &block.clauses()[0];
    let mut children = Vec::new();
    for extra in clause.extras() {
        if let RuleExtra::RewriteState { before, after, .. } = extra {
            children.extend(instance_children(before));
            if let Some(after) = after {
                children.push("=>".to_owned());
                children.extend(instance_children(after));
            }
        }
    }
    let anchors = clause
        .provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| (anchor.role(), anchor.key().ordinal()))
        .collect();
    (
        clause.bindings().iter().map(ToString::to_string).collect(),
        children,
        anchors,
    )
}

/// An instance child that is only a name is `name: name`, Rust's field-init
/// shorthand, as at a record's top level: in a pattern instance it binds the
/// name, in a created instance and in an update it writes the bound
/// variable. Each shorthand reads as its long entry, keyed alike.
#[test]
fn a_shorthand_instance_child_is_the_child_bound_to_its_name() {
    for (shorthand, long) in [
        (
            "for Machine; read: { k: [Go(), ..], account: { Account { id, balance, .. }, .. } } => { k: [balance, ..] };",
            "for Machine; read: { k: [Go(), ..], account: { Account { id: id, balance: balance, .. }, .. } } => { k: [balance, ..] };",
        ),
        (
            "for Machine; put: { k: [Put(id, balance), ..], account: { .. } } => { k: [..], account: { Account { id, balance }, .. } };",
            "for Machine; put: { k: [Put(id, balance), ..], account: { .. } } => { k: [..], account: { Account { id: id, balance: balance }, .. } };",
        ),
        (
            "for Machine; bump: { k: [Go(), ..], account: { me @ Account { id, balance, .. }, .. } } => { k: [id, ..], account: { Account { balance: int::add(balance, 1), ..me }, .. } };",
            "for Machine; bump: { k: [Go(), ..], account: { me @ Account { id: id, balance: balance, .. }, .. } } => { k: [id, ..], account: { Account { balance: int::add(balance, 1), ..me }, .. } };",
        ),
        (
            "for Machine; pop: { k: [Pop(), ..], job: [.., Job { payload, .. }] } => { k: [payload, ..], job: [..] };",
            "for Machine; pop: { k: [Pop(), ..], job: [.., Job { payload: payload, .. }] } => { k: [payload, ..], job: [..] };",
        ),
        (
            "for Machine; tag: { thread: { me @ Thread { r#type, .. }, .. } } => { thread: { Thread { r#type: int::add(r#type, 1), ..me }, .. } };",
            "for Machine; tag: { thread: { me @ Thread { r#type: r#type, .. }, .. } } => { thread: { Thread { r#type: int::add(r#type, 1), ..me }, .. } };",
        ),
    ] {
        assert_eq!(
            readable_shape(shorthand),
            readable_shape(long),
            "{shorthand}"
        );
    }
    let (bindings, children, _) = readable_shape(
        "for Machine; put: { k: [Put(id, balance), ..], account: { .. } } => { k: [..], account: { Account { id, balance }, .. } };",
    );
    assert_eq!(bindings, ["id", "balance"]);
    assert_eq!(children, ["=>", "id: id", "balance: balance"]);
}

/// `_` is no field name: Rust's shorthand has none, and `_: v` would name no
/// child, so a lone `_` is refused as a malformed child, carried at the `_` until the cell's kind
/// has admitted the braces ([`carried_braces_refusal`]).
#[test]
fn a_lone_wildcard_is_no_shorthand_instance_child() {
    let source = "for Machine; read: { thread: { Thread { _, .. }, .. } } => { thread: { .. } };";
    let (kind, text, start, end) = carried_braces_refusal(source);
    assert!(
        matches!(kind, krs_syntax::SyntaxErrorKind::InvalidStateMacro { .. }),
        "{kind:?}"
    );
    assert!(
        text.contains("an instance child is `name: value`, or `name` for `name: name`"),
        "{text}"
    );
    assert_eq!((start, end), columns(source, "_"), "{text}");
}

/// A whole-instance item: one record labelled `label` (or none), writing no child, with the rest
/// `rest`, whose group the collection's declaration gives.
fn is_whole(item: &krs_syntax::InstanceItem, label: Option<&str>, rest: &str) -> bool {
    item.owner().is_none()
        && item.fields().is_empty()
        && item.label().map(ToString::to_string).as_deref() == label
        && match item.rest() {
            InstanceRest::Open(_) => rest == "..",
            InstanceRest::Update { label, .. } => rest == format!("..{label}"),
            InstanceRest::Exact => false,
        }
}

/// An instance-list item that is one name `x` or `_` is the whole instance `x @ Decl { .. }`
/// (`Decl { .. }`) in a pattern, and in a result the instance the pattern bound to `x`, kept as
/// matched, `Decl { ..x }`: readable braces and `cells!` braces and brackets read it so. A
/// keyword or a literal is no name, and stays no instance.
#[test]
fn a_name_or_wildcard_item_is_the_whole_instance_it_labels() {
    let block = krs_syntax::RuleBlock::parse_source(
        "for Machine;
        read: { k: [Go(), ..], acct: { x, .. } } => { k: [..], acct: { x, .. } };
        any: { k: [Go(), ..], acct: { _, A { id: 1, .. }, .. } } => { k: [..] };",
    )
    .unwrap();
    let state = |clause: usize, result: bool| {
        block.clauses()[clause]
            .extras()
            .iter()
            .find_map(|extra| match extra {
                RuleExtra::RewriteState { before, after, .. } => {
                    if result {
                        after.as_deref()
                    } else {
                        Some(&**before)
                    }
                }
                _ => None,
            })
            .cloned()
            .unwrap()
    };
    let front = |state: &StateTerm| {
        let StateTerm::Instances(list) = state else {
            panic!("expected an instance list");
        };
        list.front().to_vec()
    };
    assert!(is_whole(&front(&state(0, false))[0], Some("x"), ".."));
    assert!(is_whole(&front(&state(0, true))[0], None, "..x"));
    let any = front(&state(1, false));
    assert!(is_whole(&any[0], None, ".."));
    assert_eq!(
        any[1]
            .owner()
            .map(krs_syntax::surface::path_text)
            .as_deref(),
        Some("A")
    );

    let subject = pattern("Accts::acct: { x, rest @ .. }, Jobs::job: [_, y, ..], state @ ..");
    assert!(is_whole(
        &front(subject.entries()[0].value())[0],
        Some("x"),
        ".."
    ));
    let jobs = front(subject.entries()[1].value());
    assert!(is_whole(&jobs[0], None, ".."));
    assert!(is_whole(&jobs[1], Some("y"), ".."));
    let result = expression("Accts::acct: { x, ..rest }, ..state");
    assert!(is_whole(
        &front(result.entries()[0].value())[0],
        None,
        "..x"
    ));

    // A keyword or a literal item is no instance: the instance reader's refusal is carried at the
    // item, and the cell's kind answers first (on a Set or Map collection, an item that is no
    // instance record, name or `_` is `instance-list-shape`).
    for (source, item) in [
        (
            "for Machine; read: { k: [Go(), ..], acct: { true, .. } } => { k: [..] };",
            "true",
        ),
        (
            "for Machine; read: { k: [Go(), ..], acct: { 0, .. } } => { k: [..] };",
            "0",
        ),
    ] {
        let (kind, text, start, end) = carried_braces_refusal(source);
        assert!(
            matches!(kind, krs_syntax::SyntaxErrorKind::InvalidStateMacro { .. }),
            "{kind:?}"
        );
        assert!(
            text.contains("a collection instance is a cell record"),
            "{text}"
        );
        assert_eq!((start, end), columns(source, item), "{source}: {text}");
    }
}

/// A List collection's front name, `job: [x, ..]`, reads as a head's item or a list's element
/// as well, so the clause takes that reading and carries the List reading beside it, the whole
/// instance `x @ Decl { .. }`, for the collector to choose by the cell's declaration. A value of
/// instance records keeps its place as the reading carried, and an item-less `[..]` keeps its
/// own.
#[test]
fn a_bracketed_name_carries_its_whole_instance_reading() {
    let block = krs_syntax::RuleBlock::parse_source(
        r"
        for Machine;
        use Cmd::*;

        alone: { job: [x, ..] } => { job: [x, ..] };

        beside: { k: [Go(), ..], job: [x, ..] } => { k: [..] };

        back: { k: [Go(), ..], job: [.., x] } => { k: [..] };

        records: { k: [Go(), ..], stack: [x, ..], job: [.., Job { payload: p }] } => { k: [..] };

        item_less: { k: [x, ..], job: [..] } => { k: [..] };
        ",
    )
    .unwrap();
    let clauses = block.clauses();
    let reading = |clause: usize| {
        let alternative = clauses[clause].bracket_alternative().unwrap();
        let StateTerm::Instances(before) = alternative.before() else {
            panic!("expected a List reading");
        };
        (
            alternative.cell().to_string(),
            before.clone(),
            alternative.after().cloned(),
        )
    };

    let (cell, before, after) = reading(0);
    assert_eq!(clauses[0].computation_cell().unwrap(), "job");
    assert_eq!(cell, "job");
    assert!(is_whole(&before.front()[0], Some("x"), ".."));
    let Some(StateTerm::Instances(after)) = after else {
        panic!("expected a List result");
    };
    assert!(is_whole(&after.front()[0], None, "..x"));

    let (cell, before, _) = reading(1);
    assert_eq!(clauses[1].computation_cell().unwrap(), "k");
    assert_eq!(cell, "job");
    assert!(is_whole(&before.front()[0], Some("x"), ".."));

    let (cell, before, _) = reading(2);
    assert_eq!(cell, "job");
    assert!(is_whole(&before.back()[0], Some("x"), ".."));

    assert_eq!(reading(3).0, "job");
    assert_eq!(reading(4).0, "job");
    for clause in clauses {
        clause.provenance().unwrap();
    }
}

/// `Some(..)` or `None` as an instance child is a `?` cell's presence or absence inside one
/// instance, read by its spelling as a cell entry's is: `cells!` and readable records carry it as
/// that state, in a pattern and in a result, for the collector, which says the limit
/// instance-child-multiplicity once the sentence's entries are admitted
/// ([`krs_syntax::instance_child_multiplicity_reason`]), never as a binder `None` or Rust's
/// `Option`. A child that is only a name is a binder as before, and a `Some(..)` holds the
/// child's content, no other presence.
#[test]
fn an_optional_instance_child_is_carried_as_its_presence() {
    let child = |state: &StateTerm| first_instance_fields(state)[1].value().clone();
    let pattern_child = |source: &str| child(pattern(source).entries()[0].value());
    assert!(matches!(
        pattern_child("account: { k::fragment![crate::Acct { id: z, acounter: Some(y), .. }], .. }, state @ .."),
        StateTerm::Present(inner) if matches!(*inner, StateTerm::Term(_))
    ));
    assert!(matches!(
        pattern_child("account: { Acct { id: z, acounter: None, .. }, .. }, state @ .."),
        StateTerm::Absent(_)
    ));
    let result = expression(
        "account: { k::fragment![crate::Acct { id: z, acounter: Some(x), ..me }], ..instances0 }, ..state",
    );
    let field = &first_instance_fields(result.entries()[0].value())[1];
    assert!(matches!(field.value(), StateTerm::Present(_)));
    assert_eq!(
        krs_syntax::instance_child_multiplicity_reason("acounter", false),
        format!(
            "the instance child `acounter` holds `None`, a `?` cell's absence: {}",
            krs_syntax::INSTANCE_CHILD_MULTIPLICITY
        )
    );
    let readable = krs_syntax::RuleBlock::parse_source(
        "for Machine; read: { k: [Go(), ..], account: { me @ Acct { acounter: None, .. }, .. } } => { k: [..], account: { Acct { acounter: Some(1), ..me }, .. } };",
    );
    assert!(readable.is_ok(), "{:?}", readable.err());
    let nested = parse_cells_pattern(
        krs_syntax::parse::tokens_from_source(
            "account: { k::fragment![crate::Acct { acounter: Some(None), .. }], .. }, state @ ..",
        )
        .unwrap(),
    )
    .unwrap_err();
    assert!(
        nested
            .to_string()
            .contains("an instance child's `Some(..)` holds the cell's content"),
        "{nested}"
    );
    parse_cells_pattern(
        krs_syntax::parse::tokens_from_source(
            "account: { k::fragment![crate::Acct { id: z, acounter, .. }], .. }, state @ ..",
        )
        .unwrap(),
    )
    .unwrap();
}

/// A group record an instance child writes names cells of the same instance, so a `Some(..)` or
/// `None` among its fields, at any depth of records, is the same presence inside one instance:
/// the child is read without it, as a record at a cell's position is, and the limit is the
/// collector's once the entries are admitted (TABLE follow-up (a)), with the text
/// [`krs_syntax::instance_record_multiplicity_reason`] gives.
#[test]
fn an_optional_cell_in_an_instance_child_s_group_record_waits_for_the_collector() {
    for (source, cell, child, written) in [
        (
            "obj: { k::fragment![crate::Obj { key: n, oinfo: k::fragment![crate::Oinfo { omark: Some(n) }] }], .. }, state @ ..",
            "omark",
            "oinfo",
            "`Some(..)`, a `?` cell's presence",
        ),
        (
            "obj: { k::fragment![crate::Obj { oinfo: k::fragment![crate::Oinfo { deep: k::fragment![crate::Deep { mark: None }] }], .. }], .. }, state @ ..",
            "mark",
            "oinfo",
            "`None`, a `?` cell's absence",
        ),
    ] {
        let parsed = pattern(source);
        let field = first_instance_fields(parsed.entries()[0].value())
            .iter()
            .find(|field| field.name() == child)
            .expect("the child is read");
        let read = field.value().terms()[0].spelling();
        assert!(
            !read.contains("Some") && !read.contains("None"),
            "{source}: {read}"
        );
        assert_eq!(
            krs_syntax::instance_record_multiplicity_reason(
                cell,
                child,
                written.starts_with("`Some")
            ),
            format!(
                "the cell `{cell}`, inside the instance child `{child}`, holds {written}: {}",
                krs_syntax::INSTANCE_CHILD_MULTIPLICITY
            ),
            "{source}"
        );
    }
}

/// A keyword is no binder and no variable, so it is no shorthand instance
/// child: readable refuses it as `cells!` does, with the same message (a raw
/// identifier such as `r#type` is a name, above).
#[test]
fn a_keyword_is_no_shorthand_instance_child() {
    for keyword in [
        "self", "Self", "true", "false", "crate", "super", "match", "let", "fn", "async",
    ] {
        let expected = format!("expected identifier, found keyword `{keyword}`");
        // The readable braces carry the refusal at the keyword, for the cell's kind to answer
        // first ([`carried_braces_refusal`]).
        let source = format!(
            "for Machine; read: {{ k: [Go(), ..], account: {{ Account {{ {keyword}, .. }}, .. }} }} => {{ k: [..] }};"
        );
        let (kind, text, start, end) = carried_braces_refusal(&source);
        assert!(
            matches!(kind, krs_syntax::SyntaxErrorKind::RustSyntax(_)),
            "{kind:?}"
        );
        assert!(text.contains(&expected), "{text}");
        let at = source
            .find(&format!("Account {{ {keyword},"))
            .expect("the keyword occurs")
            + "Account { ".len();
        assert_eq!((start, end), (at, at + keyword.len()), "{text}");
        let cells = parse_cells_pattern(
            krs_syntax::parse::tokens_from_source(&format!(
                "Accounts::account: {{ Account {{ {keyword}, .. }}, rest @ .. }}, state @ .."
            ))
            .unwrap(),
        )
        .unwrap_err();
        assert!(cells.to_string().contains(&expected), "{cells}");
    }
}

/// A `cells!` instance child that is only a name is `name: name` in a
/// pattern, a created instance and an update.
#[test]
fn a_shorthand_cells_instance_child_is_the_child_bound_to_its_name() {
    let children = |source: &str, pattern_side: bool| {
        let parsed = if pattern_side {
            pattern(source)
        } else {
            expression(source)
        };
        instance_children(parsed.entries()[0].value())
    };
    for (shorthand, long, pattern_side) in [
        (
            "Accounts::account: { me @ Account { id, balance, .. }, rest @ .. }, state @ ..",
            "Accounts::account: { me @ Account { id: id, balance: balance, .. }, rest @ .. }, state @ ..",
            true,
        ),
        (
            "Accounts::account: { k::fragment![Account { id, balance }], ..rest }, ..state",
            "Accounts::account: { k::fragment![Account { id: id, balance: balance }], ..rest }, ..state",
            false,
        ),
        (
            "Accounts::account: { Account { balance, ..me }, ..rest }, ..state",
            "Accounts::account: { Account { balance: balance, ..me }, ..rest }, ..state",
            false,
        ),
    ] {
        assert_eq!(
            children(shorthand, pattern_side),
            children(long, pattern_side),
            "{shorthand}"
        );
    }
    assert_eq!(
        children(
            "Accounts::account: { k::fragment![Account { id, balance }], ..rest }, ..state",
            false
        ),
        ["id: id", "balance: balance"]
    );
}

/// `Some({ k -> v, .. })` in a readable subject is the present map cell's entries, a map state
/// inside the presence, as an instance's map child is one.
#[test]
fn a_map_read_inside_a_presence_is_the_present_cells_entries() {
    let block = krs_syntax::RuleBlock::parse_source(
        r"
        for Machine;
        use Cmd::*;

        drop: { k: [Drop(), ..], omap: Some({ y -> x, .. }) } => { k: [..], omap: None };
        ",
    )
    .unwrap();
    let [RuleExtra::RewriteState { before, .. }] = block.clauses()[0].extras() else {
        panic!("expected one optional-cell rewrite");
    };
    let StateTerm::Present(inside) = before.as_ref() else {
        panic!("`Some(..)` is a presence");
    };
    let StateTerm::Map(map) = inside.as_ref() else {
        panic!("a map read inside `Some(..)` is a map state");
    };
    let MapBody::Items { items, remainder } = map.body() else {
        panic!("a map read names entries");
    };
    assert_eq!(items.len(), 1);
    assert!(matches!(remainder, StateMacroRemainder::Anonymous(_)));
}

/// A `cells!` map that names only its rest, `map![..]`, names no entry: its `..` is the rest,
/// not the start of `.Map`.
#[test]
fn a_cells_map_of_only_a_rest_names_no_entry() {
    let subject = pattern("k: KCell(..), env: Cell(k::map![..]), state @ ..");
    let StateTerm::Map(map) = subject.entries()[1].value() else {
        panic!("`map![..]` is a map");
    };
    let MapBody::Items { items, remainder } = map.body() else {
        panic!("a rest-only map is the items form with no item");
    };
    assert!(items.is_empty());
    assert!(matches!(remainder, StateMacroRemainder::Anonymous(_)));
}
