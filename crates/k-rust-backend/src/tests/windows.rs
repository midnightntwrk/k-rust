//! Rule windows (`crate::coverage::windows`): a run that asks for windows of length up to `d`
//! reports every sequence of at most `d` rewrite rules some path committed to as consecutive
//! steps.
//!
//! The definition is a double diamond: `a` steps to `b` (`r1`) or `c` (`r2`), both step to `d`
//! (`r3`, `r4`), which steps to `x` (`r5`) or `y` (`r6`), both step to `z` (`r7`, `r8`), which
//! steps to `fe()` (`r9`), a function whose equation `feq` gives `f`, where every path ends.
//! Under `state-set` the arrival at `z` from `y` merges into the one from `x`, inside the subtree
//! of `d`, into which the arrival from `c` then merges. Each rule's id is its label. Every run
//! ends by itself well inside its depth bound and sets no step timeout, so none depends on a
//! clock.

use std::{collections::BTreeSet, num::NonZeroUsize};

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::BackendDefinition,
    rewrite::{ExecutionOptions, ExecutionResult, HaltReason, Pattern, TraceKind, execute},
    search::ResultModality,
};

const MODALITIES: [ResultModality; 2] = [ResultModality::PathSet, ResultModality::StateSet];

/// The rewrite rule `from => to` labelled `label`.
fn rule(label: &str, from: &str, to: &str) -> String {
    format!(
        r#"
            axiom{{}} \rewrites{{SortS{{}}}}(
                \and{{SortS{{}}}}({from}{{}}(), \top{{SortS{{}}}}()),
                \and{{SortS{{}}}}({to}{{}}(), \top{{SortS{{}}}}())
            ) [label{{}}("{label}"), priority{{}}("50")]"#,
    )
}

fn definition() -> BackendDefinition {
    let rules = [
        ("r1", "a", "b"),
        ("r2", "a", "c"),
        ("r3", "b", "d"),
        ("r4", "c", "d"),
        ("r5", "d", "x"),
        ("r6", "d", "y"),
        ("r7", "x", "z"),
        ("r8", "y", "z"),
        ("r9", "z", "fe"),
    ]
    .map(|(label, from, to)| rule(label, from, to));
    let symbols = ["a", "b", "c", "d", "x", "y", "z", "f"]
        .map(|name| {
            format!("symbol {name}{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]")
        })
        .join("\n            ");
    let source = format!(
        r#"[]
        module MAIN
            sort SortS{{}} []
            {symbols}
            symbol fe{{}}() : SortS{{}} [function{{}}(), total{{}}()]
            axiom{{R}} \implies{{R}}(
                \and{{R}}(\top{{R}}(), \top{{R}}()),
                \equals{{SortS{{}}, R}}(fe{{}}(), \and{{SortS{{}}}}(f{{}}(), \top{{SortS{{}}}}()))
            ) [label{{}}("feq")]
            {rules}
        endmodule []"#,
        rules = rules.join("\n"),
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

/// The state `a`.
fn start(definition: &BackendDefinition) -> Pattern {
    Pattern {
        term: definition
            .internalize_term(&parse_pattern("a{}()").expect("term should parse"), &[])
            .expect("term should internalize"),
        constraints: Vec::new(),
    }
}

/// A run with coverage and its committed rules, collecting windows up to `length` when given.
fn options(modality: ResultModality, length: Option<usize>) -> ExecutionOptions {
    ExecutionOptions {
        collect_coverage: true,
        collect_committed: true,
        collect_windows: length.map(|length| NonZeroUsize::new(length).expect("a length")),
        result_modality: modality,
        max_depth: 50,
        ..ExecutionOptions::default()
    }
}

fn run(modality: ResultModality, length: usize) -> ExecutionResult {
    let definition = definition();
    execute(
        &definition,
        start(&definition),
        options(modality, Some(length)),
    )
}

fn windows(result: &ExecutionResult) -> &BTreeSet<Vec<String>> {
    result
        .coverage
        .as_ref()
        .and_then(|coverage| coverage.windows.as_ref())
        .expect("the run collected windows")
}

fn committed(result: &ExecutionResult) -> &BTreeSet<String> {
    result
        .coverage
        .as_ref()
        .and_then(|coverage| coverage.committed.as_ref())
        .expect("the run reported its committed rules")
}

fn window(rules: &[&str]) -> Vec<String> {
    rules.iter().map(|rule| (*rule).to_owned()).collect()
}

/// Every window of length up to `length` of each leaf's trace, by its rewrite entries: under
/// `path-set`, where every path of this definition ends in a leaf of its own that keeps its whole
/// trace, these are the windows of the run.
fn trace_windows(result: &ExecutionResult, length: usize) -> BTreeSet<Vec<String>> {
    let mut windows = BTreeSet::new();
    for leaf in &result.leaves {
        let rules = leaf
            .trace
            .iter()
            .filter(|entry| entry.kind == TraceKind::Rewrite)
            .map(|entry| entry.unique_id.clone())
            .collect::<Vec<_>>();
        for from in 0..rules.len() {
            for to in from + 1..=rules.len().min(from + length) {
                windows.insert(rules[from..to].to_vec());
            }
        }
    }
    windows
}

/// The `path-set` windows are those of the paths' traces; the `state-set` run, which merges two
/// arrivals and so expands fewer states, reports the same windows at every length, among them
/// windows that begin before a merge and end past it, past both merges for the longest.
#[test]
fn state_set_windows_equal_path_set_windows_on_a_merging_diamond() {
    for length in 1..=6 {
        let path_set = run(ResultModality::PathSet, length);
        let state_set = run(ResultModality::StateSet, length);
        assert_eq!(path_set.leaves.len(), 4);
        assert!(
            state_set.expanded < path_set.expanded,
            "the state-set run merged: {} < {}",
            state_set.expanded,
            path_set.expanded
        );
        assert_eq!(windows(&path_set), &trace_windows(&path_set, length));
        assert_eq!(windows(&state_set), windows(&path_set), "length {length}");
    }
    let state_set = run(ResultModality::StateSet, 5);
    for straddling in [
        window(&["r4", "r5"]),
        window(&["r2", "r4", "r6", "r8"]),
        window(&["r4", "r6", "r8", "r9"]),
        window(&["r2", "r4", "r6", "r8", "r9"]),
        window(&["r2", "r4", "r5", "r7", "r9"]),
    ] {
        assert!(
            windows(&state_set).contains(&straddling),
            "{straddling:?} in {:?}",
            windows(&state_set)
        );
    }
    assert!(windows(&state_set).iter().all(|window| window.len() <= 5));
}

/// The windows of length 1 are the committed rules, whatever the length asked.
#[test]
fn windows_of_length_one_are_the_committed_rules() {
    for modality in MODALITIES {
        for length in [1, 3] {
            let result = run(modality, length);
            let singles = windows(&result)
                .iter()
                .filter(|window| window.len() == 1)
                .cloned()
                .collect::<BTreeSet<_>>();
            let expected = committed(&result)
                .iter()
                .map(|rule| vec![rule.clone()])
                .collect::<BTreeSet<_>>();
            assert_eq!(singles, expected, "{modality:?}, length {length}");
            if length == 1 {
                assert_eq!(windows(&result), &expected);
            }
        }
    }
}

/// `feq` is applied on every path, and in no window: an equation is no step.
#[test]
fn an_equation_is_in_no_window() {
    for modality in MODALITIES {
        let result = run(modality, 4);
        let coverage = result.coverage.as_ref().expect("coverage");
        assert!(coverage.applied.contains("feq"), "{coverage:?}");
        assert!(
            windows(&result)
                .iter()
                .all(|window| !window.iter().any(|rule| rule == "feq"))
        );
        assert!(windows(&result).contains(&window(&["r7", "r9"])));
    }
}

/// With `r9` a cut-point rule every path ends at `z` with `r9` proposed, not committed: `r9` is
/// in no window, under either modality, and the modalities agree.
#[test]
fn a_cut_point_proposal_is_in_no_window() {
    let definition = definition();
    let mut collected = Vec::new();
    for modality in MODALITIES {
        let mut options = options(modality, Some(3));
        options.cut_point_rules = BTreeSet::from(["r9".to_owned()]);
        let result = execute(&definition, start(&definition), options);
        assert!(
            result
                .leaves
                .iter()
                .all(|leaf| matches!(leaf.halt_reason, HaltReason::CutPointRule { .. })),
            "{:?}",
            result.leaves
        );
        assert!(!committed(&result).contains("r9"));
        assert!(
            windows(&result)
                .iter()
                .all(|window| !window.iter().any(|rule| rule == "r9")),
            "{:?}",
            windows(&result)
        );
        assert!(windows(&result).contains(&window(&["r6", "r8"])));
        collected.push(windows(&result).clone());
    }
    assert_eq!(collected[0], collected[1]);
}

/// Collecting windows changes no other field of the result, and without `collect_coverage` it
/// is ignored.
#[test]
fn collecting_windows_changes_nothing_else() {
    let definition = definition();
    for modality in MODALITIES {
        let without = execute(&definition, start(&definition), options(modality, None));
        assert_eq!(
            without.coverage.as_ref().map(|coverage| &coverage.windows),
            Some(&None)
        );
        for length in [1, 2, 5] {
            let mut with = execute(
                &definition,
                start(&definition),
                options(modality, Some(length)),
            );
            assert!(
                with.coverage
                    .as_mut()
                    .and_then(|coverage| coverage.windows.take())
                    .is_some()
            );
            assert_eq!(with, without, "{modality:?}, length {length}");
        }
        let uncovered = execute(
            &definition,
            start(&definition),
            ExecutionOptions {
                collect_coverage: false,
                ..options(modality, Some(3))
            },
        );
        assert_eq!(uncovered.coverage, None);
    }
}
