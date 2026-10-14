//! Unit tests for overlap over optional cells and cell collections (KF-023,
//! X10.6): an absent or created cell constrains no content, and a collection
//! clause yields one footprint variant per matched instance, so rules that
//! match different instances are not reported.

use std::collections::BTreeSet;

use krs_ir::{
    BuiltinSort, CellClauseKind, CellContentFrame, CellPost, ConfigurationClause, FixedCellClause,
    InstanceClause, InstanceOrdering, InstancesClause, NodeOrigin, OptionalCellClause, Presence,
    SemanticId, SourceMapKey,
};
use krs_ir_levels::{SemanticSortRef, SemanticTerm};

use super::{SortGraph, clause_variants, clauses_overlap};

type Clause = ConfigurationClause<SemanticId, SemanticTerm>;

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
        SourceMapKey::new("sem.collections").unwrap(),
        krs_ir::testing::authored(0, 1),
    )
}

fn id(name: &str) -> SemanticId {
    SemanticId::new(name.to_owned()).unwrap()
}

fn int(value: &str) -> SemanticTerm {
    SemanticTerm::token(origin(), SemanticSortRef::Builtin(BuiltinSort::Int), value).unwrap()
}

fn variable(name: &str) -> SemanticTerm {
    SemanticTerm::variable(
        origin(),
        SemanticSortRef::Builtin(BuiltinSort::Int),
        id(name),
    )
}

fn fixed(cell: &str, before: SemanticTerm) -> Clause {
    FixedCellClause::new(
        origin(),
        id(cell),
        before,
        CellPost::Preserve,
        CellContentFrame::Exact,
    )
    .into()
}

fn optional(cell: &str, before: Option<SemanticTerm>) -> Clause {
    ConfigurationClause::Optional(OptionalCellClause::new(
        origin(),
        id(cell),
        CellClauseKind::Content,
        before.map_or(Presence::Absent, |term| Presence::Present { term }),
        None,
        CellContentFrame::Exact,
    ))
}

/// A kept instance of `thread` whose `tid` child matches `key`.
fn kept(key: SemanticTerm) -> InstanceClause<SemanticId, SemanticTerm> {
    InstanceClause::Kept {
        origin: origin(),
        label: None,
        children: vec![FixedCellClause::new(
            origin(),
            id("tid"),
            key,
            CellPost::Preserve,
            CellContentFrame::Exact,
        )],
        open: true,
    }
}

fn threads(instances: Vec<InstanceClause<SemanticId, SemanticTerm>>) -> Clause {
    ConfigurationClause::Instances(InstancesClause::new(
        origin(),
        id("thread"),
        InstanceOrdering::Unordered,
        instances,
        Vec::new(),
        true,
    ))
}

/// Whether some footprint variant of `left` overlaps some variant of `right`.
fn overlap(left: &[Clause], right: &[Clause]) -> bool {
    let graph = graph();
    let (left, right) = (clause_variants(left), clause_variants(right));
    left.iter().any(|left| {
        right
            .iter()
            .any(|right| clauses_overlap(left, None, right, None, &graph))
    })
}

#[test]
fn an_absent_optional_cell_constrains_no_content() {
    let absent = [optional("counter", None)];
    let present = [optional("counter", Some(int("0")))];
    let absent = clause_variants(&absent);
    assert!(absent.len() == 1 && absent[0].is_empty());
    assert_eq!(clause_variants(&present)[0].len(), 1);
    // Two rules on the counter's content are told apart by it.
    assert!(!overlap(
        &[optional("counter", Some(int("0")))],
        &[optional("counter", Some(int("1")))],
    ));
    assert!(overlap(
        &[optional("counter", Some(variable("N")))],
        &[optional("counter", Some(int("1")))],
    ));
}

#[test]
fn a_collection_clause_has_one_variant_per_matched_instance() {
    let clause = [threads(vec![kept(int("1")), kept(int("2"))])];
    assert_eq!(clause_variants(&clause).len(), 2);
    let created = [threads(vec![InstanceClause::Created {
        origin: origin(),
        children: Vec::new(),
        defaults: true,
    }])];
    let created = clause_variants(&created);
    assert!(created.len() == 1 && created[0].is_empty());
}

#[test]
fn rules_on_different_instances_are_not_reported() {
    // Thread 1 and thread 2 step independently: K's intended concurrency.
    assert!(!overlap(
        &[threads(vec![kept(int("1"))])],
        &[threads(vec![kept(int("2"))])],
    ));
    // A rule over threads 1 and 2 shares an instance pattern with one over 2.
    assert!(overlap(
        &[threads(vec![kept(int("1")), kept(int("2"))])],
        &[threads(vec![kept(int("2"))])],
    ));
    // A shared fixed cell still separates rules whatever their instances.
    assert!(!overlap(
        &[fixed("mode", int("0")), threads(vec![kept(variable("T"))])],
        &[fixed("mode", int("1")), threads(vec![kept(variable("U"))])],
    ));
}
