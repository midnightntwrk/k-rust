//! The rule graph on the fixtures (FZ-G8), compiled in-process from `tests/support`.
//!
//! - GRAPH: the edge from `go` to `finish` exists only because `go`'s right-hand side is keyed
//!   on the subject side, where the `anywhere` head `norm` keys nothing; the result-sort filter
//!   keeps `go` and `call` from enabling `other`.
//! - The self-check: every rewrite rule a real run applied (coverage `applied`) is reachable in
//!   the graph from the rules the run's initial configuration enables, on GRAPH, IMP and RULES.

#[path = "../../tests/support/mod.rs"]
mod support;

use std::collections::{BTreeMap, BTreeSet};

use k_rust::{
    backend::{Backend, ExecuteRequest, ExecutionStrategy, ResultModalityOutput},
    k_rust_backend::{
        definition::BackendDefinition,
        rule::{RuleRhs, rule_index},
    },
    kore::ast::Pattern as KorePattern,
};
use support::{Compiled, GRAPH, IMP, RULES};

use super::RuleGraph;

fn graph_of(compiled: &Compiled) -> (Backend, RuleGraph) {
    let mut backend = compiled.source_backend();
    let graph = RuleGraph::of_backend(&mut backend).expect("the graph builds");
    (backend, graph)
}

/// The id of the one rule labelled `<main module>.<label>`.
fn labelled(compiled: &Compiled, graph: &RuleGraph, label: &str) -> String {
    let full = format!("{}.{label}", compiled.main_module());
    let ids: Vec<&str> = graph
        .rule_ids()
        .filter(|id| {
            graph
                .rules(id)
                .iter()
                .any(|rule| rule.attributes.label.as_deref() == Some(full.as_str()))
        })
        .collect();
    let [id] = ids.as_slice() else {
        panic!("{full}: {ids:?}");
    };
    (*id).to_owned()
}

/// The id of the one rule written on `line` of the fixture's definition.
fn written_on(graph: &RuleGraph, line: usize) -> String {
    let start = format!("Location({line},");
    let ids: Vec<&str> = graph
        .rule_ids()
        .filter(|id| {
            graph.rules(id).iter().any(|rule| {
                rule.attributes.origins.iter().any(|origin| {
                    origin
                        .location
                        .as_deref()
                        .is_some_and(|location| location.starts_with(&start))
                })
            })
        })
        .collect();
    let [id] = ids.as_slice() else {
        panic!("line {line}: {ids:?}");
    };
    (*id).to_owned()
}

/// The one-based line of the fixture's definition that contains `text`.
fn line_of(compiled: &Compiled, text: &str) -> usize {
    let lines: Vec<usize> = compiled
        .fixture
        .source
        .lines()
        .enumerate()
        .filter(|(_, line)| line.contains(text))
        .map(|(index, _)| index + 1)
        .collect();
    let [line] = lines.as_slice() else {
        panic!("{text}: {lines:?}");
    };
    *line
}

/// Run `initial` on every path with coverage, as a campaign case does, and return `applied`.
fn applied(backend: &mut Backend, initial: &KorePattern) -> Vec<String> {
    let result = backend
        .execute(ExecuteRequest {
            strategy: ExecutionStrategy::All,
            result_modality: ResultModalityOutput::PathSet,
            collect_coverage: true,
            ..ExecuteRequest::new(initial.clone())
        })
        .expect("the request executes");
    result.coverage.expect("coverage was asked for").applied
}

fn set(ids: &[&str]) -> BTreeSet<String> {
    ids.iter().map(|id| (*id).to_owned()).collect()
}

#[test]
fn an_anywhere_head_on_the_right_enables_the_rule_its_equation_produces() {
    let compiled = GRAPH.compiled();
    let (mut backend, graph) = graph_of(compiled);
    let go = labelled(compiled, &graph, "go");
    let finish = labelled(compiled, &graph, "finish");
    assert!(graph.has_edge(&go, &finish), "{:#?}", graph.edges());

    // The edge needs the subject-side key: read as a rule's left-hand side, `go`'s right-hand
    // side keys its head `norm` as `Anywhere`, which `finish`'s `Constructor(done)` key does
    // not cover.
    backend
        .with_solver_over(None, &[], |definition: &BackendDefinition, _| {
            let [go_rule] = graph.rules(&go) else {
                panic!("one rule go")
            };
            let [finish_rule] = graph.rules(&finish) else {
                panic!("one rule finish")
            };
            let RuleRhs::Term(rhs) = &go_rule.rhs else {
                panic!("go has one right-hand side")
            };
            let as_written = rule_index(definition, rhs);
            assert!(
                !finish_rule.index.cells()[0].covers(&as_written.cells()[0]),
                "{:?} covers {:?}",
                finish_rule.index.cells(),
                as_written.cells()
            );
            Ok::<_, k_rust::backend::BackendError>(())
        })
        .expect("the definition is selected");
}

#[test]
fn a_right_hand_side_of_one_sort_does_not_enable_a_rule_on_an_unrelated_sort() {
    let compiled = GRAPH.compiled();
    let (_, graph) = graph_of(compiled);
    let [go, call, finish, stray, other] =
        ["go", "call", "finish", "stray", "other"].map(|label| labelled(compiled, &graph, label));
    // `mk(N)` is a function application of sort `Step`, and `norm(N)` an `anywhere` head of
    // sort `Step`: both key nothing on the subject side, and the sort keeps `other` out.
    assert!(graph.has_edge(&call, &finish));
    assert!(!graph.has_edge(&call, &other));
    assert!(!graph.has_edge(&go, &other));
    assert!(graph.has_edge(&stray, &other));
    // `finish` empties `<k>`, so it enables nothing.
    assert_eq!(graph.successors(&finish), BTreeSet::new());
    assert_eq!(graph.enablers(&finish), set(&[&call, &go]));
    assert_eq!(graph.enablers(&other), set(&[&stray]));
    assert_eq!(
        graph.distances_to(&finish),
        BTreeMap::from([(call, 1), (finish.clone(), 0), (go.clone(), 1)])
    );
    assert_eq!(graph.distance(&go, &finish), Some(1));
    assert_eq!(graph.distance(&finish, &go), None);
}

#[test]
fn the_initial_configuration_enables_its_first_rule_and_the_rest_are_warned() {
    let compiled = GRAPH.compiled();
    let (mut backend, graph) = graph_of(compiled);
    let [go, finish, other] =
        ["go", "finish", "other"].map(|label| labelled(compiled, &graph, label));
    let entry = graph
        .entry(&mut backend, &compiled.initial("graph/start.pgm"))
        .expect("the initial configuration simplifies");
    assert_eq!(entry.rules(&graph), set(&[&go]));
    assert_eq!(graph.reachable(&entry), set(&[&finish, &go]));
    assert_eq!(graph.statically_unreachable(&entry, &finish), None);
    let warning = graph
        .statically_unreachable(&entry, &other)
        .expect("other is unreachable from start(5)");
    assert!(warning.starts_with("statically-unreachable"), "{warning}");
    // The self-check reports an applied rule outside the reachable set.
    assert_eq!(
        graph.unreachable_applied(&entry, [other.as_str(), go.as_str()]),
        vec![other]
    );
}

/// Every rewrite rule the runs of `files` applied is reachable from the rules each initial
/// configuration enables.
fn assert_applied_rules_reachable(compiled: &Compiled, files: &[&str]) {
    let (mut backend, graph) = graph_of(compiled);
    for file in files {
        let initial = compiled.initial(file);
        let entry = graph
            .entry(&mut backend, &initial)
            .expect("the initial configuration simplifies");
        let applied = applied(&mut backend, &initial);
        let rewrites: Vec<&String> = applied.iter().filter(|id| graph.contains(id)).collect();
        assert!(!rewrites.is_empty(), "{file} applied no rewrite rule");
        assert_eq!(
            graph.unreachable_applied(&entry, applied.iter().map(String::as_str)),
            Vec::<String>::new(),
            "{file}: applied {rewrites:?}, entry {:?}",
            entry.rules(&graph)
        );
    }
}

#[test]
fn every_rule_a_graph_run_applied_is_reachable() {
    assert_applied_rules_reachable(
        GRAPH.compiled(),
        &["graph/start.pgm", "graph/call.pgm", "graph/stray.pgm"],
    );
}

#[test]
fn every_rule_an_imp_run_applied_is_reachable() {
    assert_applied_rules_reachable(
        IMP.compiled(),
        &[
            "imp/commute.imp",
            "imp/le.imp",
            "imp/div.imp",
            "imp/loop.imp",
        ],
    );
}

#[test]
fn every_rule_a_rules_run_applied_is_reachable() {
    assert_applied_rules_reachable(
        RULES.compiled(),
        &["rules/div.pgm", "rules/check.pgm", "rules/twice.pgm"],
    );
}

#[test]
fn an_imp_arithmetic_result_does_not_enable_a_statement_rule() {
    // `I1 + I2 => I1 +Int I2` leaves an `Int` at the head of `<k>`, which `while`'s
    // left-hand side, a `Stmt`, never matches; the subject-side key alone (a function keys
    // nothing) would give the edge.
    let compiled = IMP.compiled();
    let (_, graph) = graph_of(compiled);
    let plus = written_on(&graph, line_of(compiled, "I1 + I2 =>"));
    let while_rule = labelled(compiled, &graph, "while");
    assert!(!graph.has_edge(&plus, &while_rule));
    assert!(!graph.successors(&plus).is_empty());
}

#[test]
fn function_calls_are_edges_between_symbols_with_equations() {
    let rules = RULES.compiled();
    let (_, graph) = graph_of(rules);
    let twice = labelled(rules, &graph, "twice");
    assert!(
        graph.called_functions(&twice).contains("Lbldouble"),
        "{:?}",
        graph.called_functions(&twice)
    );
    assert_eq!(graph.calls().equations("Lbldouble").len(), 1);
    let check_hit = labelled(rules, &graph, "check-hit");
    assert_eq!(graph.requires_functions(&check_hit), BTreeSet::new());

    let imp = IMP.compiled();
    let (_, graph) = graph_of(imp);
    let var = labelled(imp, &graph, "var");
    let called = graph.called_functions(&var);
    assert!(
        called.iter().any(|name| name.contains("lookup")),
        "{called:?}"
    );
}

#[test]
fn the_graph_is_a_function_of_the_definition() {
    let compiled = IMP.compiled();
    let (_, first) = graph_of(compiled);
    let (_, second) = graph_of(compiled);
    assert_eq!(first.edges(), second.edges());
    assert!(!first.edges().is_empty());
}
