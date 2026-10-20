//! The rule graph on the fixtures (FZ-G8), compiled in-process from `tests/support`.
//!
//! - GRAPH: the edge from `go` to `finish` exists only because `go`'s right-hand side is keyed
//!   on the subject side, where the `anywhere` head `norm` keys nothing; the result-sort filter
//!   keeps `go` and `call` from enabling `other`.
//! - Edges against real steps: on one traced path, the first rewrite rule is in the entry and
//!   every consecutive pair of rewrite rules is an edge, on GRAPH, IMP, RULES and VALUE.
//! - The entry from the hole template: VALUE's `<k> $N:Int </k>` keys the anchor `5` as a value,
//!   which leaves `zero` out; the template, with `$N` a variable of sort `Int`, does not.
//! - The self-check: every rewrite rule a real run applied is reachable from the entry, and ids
//!   that are no node or equation are reported.

#[path = "../../tests/support/mod.rs"]
mod support;

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use k_rust::{
    backend::{
        Backend, BackendError, ExecuteRequest, ExecutionResult, ExecutionStrategy,
        ResultModalityOutput,
    },
    k_rust_backend::{
        definition::BackendDefinition,
        rule::{CellIndex, RuleRhs, rule_index},
        term::{Sort, Symbol, Term},
    },
    kore::{
        ast::{Pattern as KorePattern, Sort as KoreSort},
        codec,
        printer::Printer,
        walk,
    },
};
use support::{Compiled, GRAPH, IMP, RULES, VALUE};

use super::{
    RuleGraph,
    entry::{Entry, ForeignEntry, hole_template},
};

fn graph_of(compiled: &Compiled) -> (Backend, RuleGraph) {
    let mut backend = compiled.source_backend();
    let graph = RuleGraph::of_backend(&mut backend).expect("the graph builds");
    (backend, graph)
}

/// The entry of `configuration` (a hole template, or a configuration without holes), computed
/// on a backend of its own with the default case request.
fn entry_of(compiled: &Compiled, graph: &RuleGraph, configuration: &KorePattern) -> Entry {
    graph
        .entry(
            &mut compiled.source_backend(),
            ExecuteRequest::new(configuration.clone()),
        )
        .expect("the configuration executes at depth 0")
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

fn execute(
    backend: &mut Backend,
    initial: &KorePattern,
    strategy: ExecutionStrategy,
) -> ExecutionResult {
    backend
        .execute(ExecuteRequest {
            strategy,
            result_modality: ResultModalityOutput::PathSet,
            collect_coverage: true,
            trace: true,
            ..ExecuteRequest::new(initial.clone())
        })
        .expect("the request executes")
}

/// Run `initial` on every path with coverage, as a campaign case does, and return `applied`.
fn applied(backend: &mut Backend, initial: &KorePattern) -> Vec<String> {
    execute(backend, initial, ExecutionStrategy::All)
        .coverage
        .expect("coverage was asked for")
        .applied
}

fn set(ids: &[&str]) -> BTreeSet<String> {
    ids.iter().map(|id| (*id).to_owned()).collect()
}

/// The path (`walk::children` indices) to the one integer domain value `value` in `pattern`.
fn path_of_int(pattern: &KorePattern, value: &str) -> Vec<usize> {
    fn search(
        pattern: &KorePattern,
        value: &str,
        path: &mut Vec<usize>,
        found: &mut Vec<Vec<usize>>,
    ) {
        if let KorePattern::DomainValue {
            sort,
            value: written,
        } = pattern
            && matches!(sort, KoreSort::Application { name, .. } if name == "SortInt")
            && written.as_bytes() == value.as_bytes()
        {
            found.push(path.clone());
        }
        for (index, child) in walk::children(pattern).into_iter().enumerate() {
            path.push(index);
            search(child, value, path, found);
            path.pop();
        }
    }
    let mut found = Vec::new();
    search(pattern, value, &mut Vec::new(), &mut found);
    let [path] = found.as_slice() else {
        panic!("{value}: {found:?}");
    };
    path.clone()
}

fn int_sort() -> KoreSort {
    KoreSort::Application {
        name: "SortInt".to_owned(),
        arguments: Vec::new(),
    }
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
            Ok::<_, BackendError>(())
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
    let (_, graph) = graph_of(compiled);
    let [go, finish, other] =
        ["go", "finish", "other"].map(|label| labelled(compiled, &graph, label));
    let entry = entry_of(compiled, &graph, &compiled.initial("graph/start.pgm"));
    assert_eq!(graph.entry_rules(&entry), Ok(set(&[&go])));
    assert_eq!(graph.reachable(&entry), Ok(set(&[&finish, &go])));
    assert_eq!(graph.statically_unreachable(&entry, &finish), Ok(None));
    let warning = graph
        .statically_unreachable(&entry, &other)
        .expect("the graph's own entry")
        .expect("other is unreachable from start(5)");
    assert!(warning.starts_with("statically-unreachable"), "{warning}");
    let check = graph
        .unreachable_applied(&entry, [other.as_str(), go.as_str()])
        .expect("the graph's own entry");
    assert_eq!(check.unreachable, vec![other]);
    assert!(check.unknown.is_empty() && check.ambiguous.is_empty());
}

#[test]
fn a_hole_at_the_head_of_k_is_keyed_by_its_sort_not_by_the_anchor() {
    let compiled = VALUE.compiled();
    let (_, graph) = graph_of(compiled);
    let zero = labelled(compiled, &graph, "zero");
    let anchor = compiled.initial("graph/value.pgm");

    // Keyed on the anchor `5` alone, `zero`'s `Value("0")` key does not cover the head: one
    // case's configuration is no entry for the campaign.
    let concrete = entry_of(compiled, &graph, &anchor);
    assert!(!graph.entry_rules(&concrete).unwrap().contains(&zero));

    let template = hole_template(&anchor, &[(path_of_int(&anchor, "5"), int_sort())])
        .expect("the hole's path leads through applications");
    let entry = entry_of(compiled, &graph, &template);
    assert!(graph.entry_rules(&entry).unwrap().contains(&zero));
    assert_eq!(graph.statically_unreachable(&entry, &zero), Ok(None));

    // The case `$N = 0` applies `zero`, and the template's entry accepts it.
    let case = compiled
        .assemble("graph/value.pgm", "run\n", &[("N", "0")])
        .expect("the case assembles");
    let applied = applied(&mut compiled.source_backend(), &case);
    assert!(applied.contains(&zero), "{applied:?}");
    let check = graph
        .unreachable_applied(&entry, applied.iter().map(String::as_str))
        .expect("the graph's own entry");
    assert!(check.is_clean(), "{check:?}");
}

#[test]
fn every_pair_of_consecutive_traced_rules_is_an_edge() {
    for (compiled, files) in [
        (
            GRAPH.compiled(),
            &["graph/start.pgm", "graph/call.pgm", "graph/stray.pgm"][..],
        ),
        (
            IMP.compiled(),
            &[
                "imp/commute.imp",
                "imp/le.imp",
                "imp/div.imp",
                "imp/loop.imp",
            ][..],
        ),
        (
            RULES.compiled(),
            &["rules/div.pgm", "rules/check.pgm", "rules/twice.pgm"][..],
        ),
        (VALUE.compiled(), &["graph/value.pgm"][..]),
    ] {
        let (mut backend, graph) = graph_of(compiled);
        for file in files {
            let initial = compiled.initial(file);
            let entry = entry_of(compiled, &graph, &initial);
            let result = execute(&mut backend, &initial, ExecutionStrategy::Any);
            let [leaf] = result.leaves.as_slice() else {
                panic!("{file}: one path gives one leaf");
            };
            let steps: Vec<&str> = leaf
                .trace
                .iter()
                .filter(|entry| entry.kind == "rewrite")
                .map(|entry| entry.unique_id.as_str())
                .collect();
            let (first, _) = steps
                .split_first()
                .unwrap_or_else(|| panic!("{file} applied no rewrite rule"));
            assert!(
                graph.entry_rules(&entry).unwrap().contains(*first),
                "{file}: the first rule {first} is not in the entry"
            );
            for pair in steps.windows(2) {
                assert!(
                    graph.has_edge(pair[0], pair[1]),
                    "{file}: no edge {} -> {}",
                    pair[0],
                    pair[1]
                );
            }
        }
    }
}

/// Every rewrite rule the runs of `files` applied is reachable from the rules each initial
/// configuration enables.
fn assert_applied_rules_reachable(compiled: &Compiled, files: &[&str]) {
    let (mut backend, graph) = graph_of(compiled);
    for file in files {
        let initial = compiled.initial(file);
        let entry = entry_of(compiled, &graph, &initial);
        let applied = applied(&mut backend, &initial);
        let rewrites: Vec<&String> = applied.iter().filter(|id| graph.contains(id)).collect();
        assert!(!rewrites.is_empty(), "{file} applied no rewrite rule");
        let check = graph
            .unreachable_applied(&entry, applied.iter().map(String::as_str))
            .expect("the graph's own entry");
        assert!(check.is_clean(), "{file}: {check:?}");
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
fn the_self_check_reports_ids_that_are_no_node_and_no_equation() {
    let compiled = RULES.compiled();
    let (_, graph) = graph_of(compiled);
    let check_hit = labelled(compiled, &graph, "check-hit");
    let entry = entry_of(compiled, &graph, &compiled.initial("rules/check.pgm"));
    // An id of no axiom is unknown; an equation's id is not checked.
    let equation = graph.calls().equations("Lbldouble")[0]
        .attributes
        .unique_id
        .clone();
    let check = graph
        .unreachable_applied(&entry, ["no-such-rule", equation.as_str()])
        .unwrap();
    assert_eq!(check.unknown, vec!["no-such-rule".to_owned()]);
    assert!(check.unreachable.is_empty() && check.ambiguous.is_empty());

    // A rule that is not executable is no node: its id applied is unknown, never dropped.
    let mut backend = compiled.backend_with_non_executable("check-hit");
    let edited = RuleGraph::of_backend(&mut backend).expect("the graph builds");
    assert!(!edited.contains(&check_hit));
    let entry = edited
        .entry(
            &mut compiled.backend_with_non_executable("check-hit"),
            ExecuteRequest::new(compiled.initial("rules/check.pgm")),
        )
        .unwrap();
    let check = edited
        .unreachable_applied(&entry, [check_hit.as_str()])
        .unwrap();
    assert_eq!(check.unknown, vec![check_hit]);
}

#[test]
fn an_entry_is_refused_by_another_graph() {
    let compiled = GRAPH.compiled();
    let (_, graph) = graph_of(compiled);
    let (_, other) = graph_of(compiled);
    let entry = entry_of(compiled, &graph, &compiled.initial("graph/start.pgm"));
    assert_eq!(other.entry_rules(&entry), Err(ForeignEntry));
    assert_eq!(other.reachable(&entry), Err(ForeignEntry));
    assert_eq!(other.statically_unreachable(&entry, "x"), Err(ForeignEntry));
    assert_eq!(other.unreachable_applied(&entry, []), Err(ForeignEntry));
    assert!(graph.clone().entry_rules(&entry).is_ok());
}

#[test]
fn the_graph_programs_end_as_the_readme_says() {
    let compiled = GRAPH.compiled();
    let mut backend = compiled.source_backend();
    for (file, out) in [
        ("graph/start.pgm", "5"),
        ("graph/call.pgm", "5"),
        ("graph/stray.pgm", "-5"),
    ] {
        let result = execute(
            &mut backend,
            &compiled.initial(file),
            ExecutionStrategy::All,
        );
        let [leaf] = result.leaves.as_slice() else {
            panic!("{file}: one leaf");
        };
        let printed =
            Printer::compact().print_pattern(&codec::from_value(&leaf.state).expect("a KORE leaf"));
        assert!(
            printed.contains(&format!(
                r#"Lbl'-LT-'out'-GT-'{{}}(\dv{{SortInt{{}}}}("{out}"))"#
            )),
            "{file}: {printed}"
        );
        assert!(
            printed.contains(r"Lbl'-LT-'k'-GT-'{}(dotk{}())"),
            "{file}: {printed}"
        );
    }
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

#[test]
fn a_rigid_key_takes_its_sort_from_the_conjunct_it_came_from() {
    let constant = |name: &str, sort: &str| {
        Term::application(
            Arc::new(Symbol::constructor(name, Vec::new(), Sort::simple(sort))),
            Vec::new(),
            Vec::new(),
        )
    };
    // `g() /\ c()` keyed `Constructor(c)`: the sort is `c`'s, not that of the leftmost
    // application `g`, which is wider and would drop edges `c` keeps.
    let conjunction = Term::and(constant("Lblg", "SortKItem"), constant("Lblc", "SortStep"));
    assert_eq!(
        super::rooted(&conjunction, &CellIndex::Constructor("Lblc".into())).map(Term::sort),
        Some(Sort::simple("SortStep"))
    );
    assert_eq!(
        super::rooted(&conjunction, &CellIndex::Constructor("Lblh".into())),
        None
    );
}
