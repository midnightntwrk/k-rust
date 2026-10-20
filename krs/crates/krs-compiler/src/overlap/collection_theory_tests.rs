//! List, Set and K-sequence patterns in the overlap check (F2 amendment,
//! clause 7e). Two transitions overlap when some configuration matches both,
//! and configurations hold collections modulo their axioms: `_List_` and
//! `~>` are associative with a unit, and `_Set_` is associative and
//! commutative with a unit, on disjoint operands. A syntactic mismatch of
//! two collection patterns therefore proves nothing, and the check may
//! report two patterns disjoint only when no collection matches both.

use std::collections::BTreeSet;

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, ItemKind, ListOperation, MapOperation,
    NodeOrigin, PackageId, SemanticId, SourceMapKey, StableItemId,
};
use krs_ir_levels::{ListOperands, SemanticSortRef, SemanticTerm, SetOperands};

use super::{
    ClauseView, Frame, Pattern, SortGraph, Unifier, VariableKey, alternatives_ambiguous,
    clauses_overlap,
};

fn graph() -> SortGraph {
    let mut graph = SortGraph {
        candidates: BuiltinSort::ALL
            .into_iter()
            .map(SemanticSortRef::Builtin)
            .collect::<BTreeSet<_>>(),
        ..SortGraph::default()
    };
    graph.build_closure();
    graph
}

fn origin() -> NodeOrigin {
    NodeOrigin::new(
        SourceMapKey::new("sem.collection-theory").unwrap(),
        krs_ir::testing::authored(0, 1),
    )
}

fn id(name: &str) -> SemanticId {
    SemanticId::new(name.to_owned()).unwrap()
}

fn builtin(sort: BuiltinSort) -> SemanticSortRef {
    SemanticSortRef::Builtin(sort)
}

fn variable(name: &str, sort: BuiltinSort) -> SemanticTerm {
    SemanticTerm::variable(origin(), builtin(sort), id(name))
}

fn int(value: &str) -> SemanticTerm {
    SemanticTerm::token(origin(), builtin(BuiltinSort::Int), value).unwrap()
}

/// `list::empty()`.
fn empty_list() -> SemanticTerm {
    SemanticTerm::list(origin(), builtin(BuiltinSort::List), ListOperands::Empty)
}

/// `list::item(element)`.
fn list_item(element: SemanticTerm) -> SemanticTerm {
    SemanticTerm::list(
        origin(),
        builtin(BuiltinSort::List),
        ListOperands::Item { element },
    )
}

/// `list::concat(left, right)`.
fn list_concat(left: SemanticTerm, right: SemanticTerm) -> SemanticTerm {
    SemanticTerm::list(
        origin(),
        builtin(BuiltinSort::List),
        ListOperands::Concat { left, right },
    )
}

fn list_variable(name: &str) -> SemanticTerm {
    variable(name, BuiltinSort::List)
}

/// `set::item(element)`.
fn set_item(element: SemanticTerm) -> SemanticTerm {
    SemanticTerm::set(
        origin(),
        builtin(BuiltinSort::Set),
        SetOperands::Item { element },
    )
}

/// `set::concat(left, right)`.
fn set_concat(left: SemanticTerm, right: SemanticTerm) -> SemanticTerm {
    SemanticTerm::set(
        origin(),
        builtin(BuiltinSort::Set),
        SetOperands::Concat { left, right },
    )
}

fn set_variable(name: &str) -> SemanticTerm {
    variable(name, BuiltinSort::Set)
}

fn int_ge(left: SemanticTerm, right: SemanticTerm) -> SemanticTerm {
    SemanticTerm::application(
        origin(),
        builtin(BuiltinSort::Bool),
        ApplicationRef::Builtin(BuiltinOperation::IntGreaterEqual),
        vec![left, right],
    )
}

fn constructor(name: &str) -> SemanticTerm {
    SemanticTerm::application(
        origin(),
        builtin(BuiltinSort::KSequence),
        ApplicationRef::Declared(
            StableItemId::new(
                PackageId::new("COLLECTIONS", "collections", "0.1.0", "test").unwrap(),
                ["fixture"],
                name,
                ItemKind::Constructor,
                "",
            )
            .unwrap(),
        ),
        Vec::new(),
    )
}

fn sequence(items: Vec<SemanticTerm>) -> SemanticTerm {
    SemanticTerm::k_sequence(origin(), builtin(BuiltinSort::KSequence), items)
}

/// Whether two exact clauses on one cell, with optional guards, overlap.
fn guarded(
    left: &SemanticTerm,
    left_requires: Option<&SemanticTerm>,
    right: &SemanticTerm,
    right_requires: Option<&SemanticTerm>,
) -> bool {
    let cell = id("queue");
    let view = |before| ClauseView {
        cell: &cell,
        before,
        completed_head: false,
        frame: Frame::Exact,
        unconstrained: false,
    };
    clauses_overlap(
        &[view(left)],
        left_requires,
        &[view(right)],
        right_requires,
        &graph(),
    )
}

fn overlap(left: &SemanticTerm, right: &SemanticTerm) -> bool {
    guarded(left, None, right, None)
}

/// Both orders, since the unifier is symmetric in its answer.
fn overlap_both(left: &SemanticTerm, right: &SemanticTerm) -> bool {
    let forward = overlap(left, right);
    assert_eq!(forward, overlap(right, left), "overlap is symmetric");
    forward
}

#[test]
fn a_single_item_overlaps_an_item_with_an_empty_rest() {
    // `queue: list::item(j)` against `queue: list::concat(list::item(k), rest)`:
    // `ListItem(J)` matches both, with `rest = .List`.
    let last = list_item(variable("j", BuiltinSort::Int));
    let next = list_concat(
        list_item(variable("k", BuiltinSort::Int)),
        list_variable("rest"),
    );
    assert!(overlap_both(&last, &next));
    // The last element of a list is also a single item's element.
    let tail = list_concat(list_variable("rest"), list_item(int("1")));
    assert!(overlap_both(
        &list_item(variable("y", BuiltinSort::Int)),
        &tail
    ));
}

#[test]
fn the_empty_list_overlaps_a_concatenation_of_variables() {
    let pair = list_concat(list_variable("xs"), list_variable("ys"));
    assert!(overlap_both(&empty_list(), &pair));
}

#[test]
fn left_and_right_nested_concatenations_overlap() {
    // `[a, b] ++ r` against `(r2 ++ [c]) ++ [d]`: `[a, b, c, d]` matches both.
    let right_nested = list_concat(
        list_item(variable("a", BuiltinSort::Int)),
        list_concat(
            list_item(variable("b", BuiltinSort::Int)),
            list_variable("r"),
        ),
    );
    let left_nested = list_concat(
        list_concat(
            list_variable("r2"),
            list_item(variable("c", BuiltinSort::Int)),
        ),
        list_item(variable("d", BuiltinSort::Int)),
    );
    assert!(overlap_both(&right_nested, &left_nested));
    // Four closed items however nested are one list.
    let closed_right = list_concat(
        list_item(int("1")),
        list_concat(list_item(int("2")), list_item(int("3"))),
    );
    let closed_left = list_concat(
        list_concat(list_item(int("1")), list_item(int("2"))),
        list_item(int("3")),
    );
    assert!(overlap_both(&closed_right, &closed_left));
}

#[test]
fn forced_list_positions_still_separate() {
    // The first element is the same element in every common instance.
    let one = list_concat(list_item(int("1")), list_variable("r"));
    let two = list_concat(list_item(int("2")), list_variable("r2"));
    assert!(!overlap_both(&one, &two));
    // So is the last.
    let ends_one = list_concat(list_variable("r"), list_item(int("1")));
    let ends_two = list_concat(
        list_item(variable("x", BuiltinSort::Int)),
        list_concat(list_variable("s"), list_item(int("2"))),
    );
    assert!(!overlap_both(&ends_one, &ends_two));
    // The empty list has no first element.
    let nonempty = list_concat(
        list_item(variable("x", BuiltinSort::Int)),
        list_variable("r"),
    );
    assert!(!overlap_both(&empty_list(), &nonempty));
    // Two closed lists of different lengths never meet.
    let two_items = list_concat(list_item(int("1")), list_item(int("2")));
    assert!(!overlap_both(&list_item(int("1")), &two_items));
    // A closed list has no room for more elements than it holds.
    let three_framed = list_concat(
        list_item(variable("a", BuiltinSort::Int)),
        list_concat(
            list_variable("r"),
            list_concat(
                list_item(variable("b", BuiltinSort::Int)),
                list_item(variable("c", BuiltinSort::Int)),
            ),
        ),
    );
    assert!(!overlap_both(&two_items, &three_framed));
}

#[test]
fn framed_sets_choosing_different_elements_overlap() {
    // `{1} ⊎ r` against `{2} ⊎ r2`: `{1, 2}` matches both, each rule taking
    // a different element.
    let one = set_concat(set_item(int("1")), set_variable("r"));
    let two = set_concat(set_item(int("2")), set_variable("r2"));
    assert!(overlap_both(&one, &two));
    // `{x}` against `{y} ⊎ r`: `{x}` matches both with `r = .Set`.
    let single = set_item(variable("x", BuiltinSort::Int));
    let framed = set_concat(set_item(variable("y", BuiltinSort::Int)), set_variable("r"));
    assert!(overlap_both(&single, &framed));
}

#[test]
fn set_cardinalities_still_separate() {
    // A concatenation of sets is defined only on disjoint operands, so a
    // closed pattern of n items denotes sets of exactly n elements.
    let pair = set_concat(
        set_item(variable("x", BuiltinSort::Int)),
        set_item(variable("y", BuiltinSort::Int)),
    );
    let single = set_item(variable("z", BuiltinSort::Int));
    assert!(!overlap_both(&pair, &single));
    // A framed pattern of n items needs at least n elements.
    let framed_pair = set_concat(pair.clone(), set_variable("r"));
    assert!(!overlap_both(&single, &framed_pair));
    // One element on each side, one side closed: the elements are equal.
    assert!(!overlap_both(&set_item(int("1")), &set_item(int("2"))));
    let framed_two = set_concat(set_item(int("2")), set_variable("r"));
    assert!(!overlap_both(&set_item(int("1")), &framed_two));
}

#[test]
fn an_element_pairing_chosen_by_the_unifier_does_not_separate_guards() {
    // `{x} ⊎ r if x >= 10` against `{0} ⊎ r2`: `{0, 10}` matches both, with
    // `x = 10`. Pairing `x` with `0` is one choice among several, so it must
    // not reach the guard procedure.
    let left = set_concat(set_item(variable("x", BuiltinSort::Int)), set_variable("r"));
    let guard = int_ge(variable("x", BuiltinSort::Int), int("10"));
    let right = set_concat(set_item(int("0")), set_variable("r2"));
    assert!(guarded(&left, Some(&guard), &right, None));
    // A forced pairing does reach it: `{x}` against `{0}` binds `x = 0`.
    let single = set_item(variable("x", BuiltinSort::Int));
    assert!(!guarded(&single, Some(&guard), &set_item(int("0")), None));
    // The same for a forced List position.
    let list = list_concat(
        list_item(variable("x", BuiltinSort::Int)),
        list_variable("r"),
    );
    let zero = list_concat(list_item(int("0")), list_variable("r2"));
    assert!(!guarded(&list, Some(&guard), &zero, None));
    // ... but not for a List element the unifier did not align.
    let later = list_concat(
        list_variable("s"),
        list_concat(list_item(int("0")), list_variable("r2")),
    );
    assert!(guarded(&list, Some(&guard), &later, None));
}

#[test]
fn a_k_variable_item_splices_into_the_sequence() {
    // `A() ~> R` with `R: K` against `A() ~> B() ~> C()`: `R = B() ~> C()`.
    let spliced = sequence(vec![
        constructor("A"),
        variable("rest", BuiltinSort::KSequence),
    ]);
    let longer = sequence(vec![constructor("A"), constructor("B"), constructor("C")]);
    assert!(overlap_both(&spliced, &longer));
    // The forced first item still separates.
    let other = sequence(vec![constructor("B"), constructor("C")]);
    assert!(!overlap_both(&spliced, &other));
    // A nested sequence is flattened: `(A() ~> B()) ~> C()` is `A() ~> B() ~> C()`.
    let nested = sequence(vec![
        sequence(vec![constructor("A"), constructor("B")]),
        constructor("C"),
    ]);
    assert!(overlap_both(&nested, &longer));
}

#[test]
fn a_k_variable_cell_overlaps_a_framed_sequence() {
    // `k: R` (one `K` item, exact) against `k: [A(), B(), ..]`.
    let k = id("k");
    let whole = sequence(vec![variable("rest", BuiltinSort::KSequence)]);
    let framed = sequence(vec![constructor("A"), constructor("B")]);
    let exact_view = ClauseView {
        cell: &k,
        before: &whole,
        completed_head: false,
        frame: Frame::Exact,
        unconstrained: false,
    };
    let framed_view = ClauseView {
        cell: &k,
        before: &framed,
        completed_head: false,
        frame: Frame::Sequence,
        unconstrained: false,
    };
    assert!(clauses_overlap(
        &[exact_view],
        None,
        &[framed_view],
        None,
        &graph()
    ));
}

#[test]
fn list_or_alternatives_that_align_differently_are_ambiguous() {
    // `[x] ++ _r | (_s ++ [x]) ++ _t` matches `[1, 2]` with x = 1 or x = 2.
    let first = list_concat(
        list_item(variable("x", BuiltinSort::Int)),
        list_variable("_r"),
    );
    let second = list_concat(
        list_concat(
            list_variable("_s"),
            list_item(variable("x", BuiltinSort::Int)),
        ),
        list_variable("_t"),
    );
    assert!(alternatives_ambiguous(
        &first,
        &second,
        &BTreeSet::new(),
        &graph()
    ));
    // `[x] | [x] ++ _r` binds x to the one element in both.
    let single = list_item(variable("x", BuiltinSort::Int));
    assert!(!alternatives_ambiguous(
        &single,
        &first,
        &BTreeSet::new(),
        &graph()
    ));
}

#[test]
fn set_or_alternatives_choosing_different_elements_are_ambiguous() {
    // `{x} ⊎ _r | {_y} ⊎ {x} ⊎ _s` matches `{1, 2}` with x = 1 or x = 2.
    let first = set_concat(
        set_item(variable("x", BuiltinSort::Int)),
        set_variable("_r"),
    );
    let second = set_concat(
        set_item(variable("_y", BuiltinSort::Int)),
        set_concat(
            set_item(variable("x", BuiltinSort::Int)),
            set_variable("_s"),
        ),
    );
    assert!(alternatives_ambiguous(
        &first,
        &second,
        &BTreeSet::new(),
        &graph()
    ));
    // `{x} | {x} ⊎ _r` binds x to the one element in both.
    let single = set_item(variable("x", BuiltinSort::Int));
    assert!(!alternatives_ambiguous(
        &single,
        &first,
        &BTreeSet::new(),
        &graph()
    ));
}

fn pattern_variable(rule: usize, ordinal: usize, sort: BuiltinSort) -> Pattern {
    Pattern::Variable {
        key: VariableKey { rule, ordinal },
        sort: builtin(sort),
    }
}

fn pattern_int(value: &str) -> Pattern {
    Pattern::Token {
        sort: builtin(BuiltinSort::Int),
        value: value.into(),
    }
}

#[test]
fn a_variable_occurring_in_a_collection_proves_nothing() {
    // `X` against `X ++ Y` holds with `Y = .List`.
    let graph = graph();
    let x = pattern_variable(0, 0, BuiltinSort::List);
    let concat = Pattern::List {
        sort: builtin(BuiltinSort::List),
        operation: ListOperation::Concat,
        arguments: vec![x.clone(), pattern_variable(0, 1, BuiltinSort::List)],
    };
    assert!(Unifier::new(&graph).unify(x, concat));
}

#[test]
fn a_map_remainder_may_hold_any_entries() {
    let graph = graph();
    let empty = Pattern::Map {
        sort: builtin(BuiltinSort::Map),
        operation: MapOperation::Empty,
        arguments: Vec::new(),
    };
    let entry = Pattern::Map {
        sort: builtin(BuiltinSort::Map),
        operation: MapOperation::Item,
        arguments: vec![pattern_int("1"), pattern_int("2")],
    };
    // `env: .Map ...` against `env: 1 |-> 2`: the remainder holds the entry.
    assert!(Unifier::new(&graph).unify_clause(
        empty.clone(),
        Frame::Map,
        entry.clone(),
        Frame::Exact,
    ));
    // `env: 1 |-> 2 ...` against the exact empty map: one entry is needed.
    assert!(!Unifier::new(&graph).unify_clause(entry, Frame::Map, empty, Frame::Exact));
}
