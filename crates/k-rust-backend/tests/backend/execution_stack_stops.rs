//! Every stop for lack of native stack an execution meets is counted on its result
//! (`ExecutionResult::stack_stops`), those that end a state and those a site that only refines a
//! sound result dismisses alike, so a host can tell the runs whose result may depend on the
//! thread's stack (`docs/compatibility.md`, "Determinism and concurrency").
//!
//! Each fixture is run on an 8 MiB thread whose simplifier may not extend its stack with
//! segments (`with_simplification_stack_budget(0, ..)`), so a recursion deeper than that thread's
//! stack stops at the same place every time, and on a thread with the default budget, where it
//! does not stop.

use k_rust_backend::{
    definition::BackendDefinition,
    nesting::with_simplification_stack_budget,
    rewrite::{ExecutionOptions, ExecutionResult, HaltReason, Pattern, execute},
    search::ResultModality,
    stop::{StackLimit, StopCause},
};
use k_rust_kore::{
    kore::{ast as kore, parser::parse_definition},
    measure::{Counter, snapshot},
};

use crate::support::internal_term;

const PRELUDE: &str = r#"
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol subInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.sub"), smt-hook{}("-")]
    hooked-symbol addInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
    hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
    hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
    symbol deep{}(SortInt{}) : SortInt{} [function{}(), total{}()]
    symbol p{}(SortInt{}) : SortInt{} [function{}()]
    sort SortS{} []
    symbol state{}() : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol done{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
"#;

/// The equation `head(X0, ..., Xn) = right requires requires`, each `Xi` bound to
/// `patterns[i]` of sort `sorts[i]`, with the axiom attributes `attributes`.
fn equation(
    head: &str,
    sorts: &[&str],
    result: &str,
    patterns: &[&str],
    right: &str,
    requires: &str,
    attributes: &str,
) -> String {
    let memberships = sorts.iter().zip(patterns).enumerate().rev().fold(
        r"\top{R}()".to_owned(),
        |rest, (index, (sort, pattern))| {
            format!(r"\and{{R}}(\in{{{sort}, R}}(X{index}:{sort}, {pattern}), {rest})")
        },
    );
    let parameters = sorts
        .iter()
        .enumerate()
        .map(|(index, sort)| format!("X{index}:{sort}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        r"axiom{{R}} \implies{{R}}(\and{{R}}({requires}, {memberships}), \equals{{{result}, R}}({head}{{}}({parameters}), \and{{{result}}}({right}, \top{{{result}}}()))) [{attributes}]"
    )
}

fn int(value: u64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// `left` holds as a `requires`: `\equals(left, true)`.
fn holds(left: &str) -> String {
    format!(r#"\equals{{SortBool{{}}, R}}({left}, \dv{{SortBool{{}}}}("true"))"#)
}

/// `deep(0) = 0`, `deep(N) = deep(N -Int 1) +Int 1 requires N >Int 0`: `deep(n)` recurses `n`
/// levels deep, not in tail position.
fn deep_recursion() -> [String; 2] {
    [
        equation(
            "deep",
            &["SortInt{}"],
            "SortInt{}",
            &[&int(0)],
            &int(0),
            r"\top{R}()",
            "",
        ),
        equation(
            "deep",
            &["SortInt{}"],
            "SortInt{}",
            &["VarN:SortInt{}"],
            &format!(
                "addInt{{}}(deep{{}}(subInt{{}}(VarN:SortInt{{}}, {})), {})",
                int(1),
                int(1)
            ),
            &holds(&format!("gtInt{{}}(VarN:SortInt{{}}, {})", int(0))),
            "",
        ),
    ]
}

/// The ceil equation `\ceil(p(X)) = (deep(n) == n)`.
fn ceil_of_p(n: u64) -> String {
    format!(
        r"axiom{{R}} \implies{{R}}(\top{{R}}(), \equals{{R, R}}(\ceil{{SortInt{{}}, R}}(p{{}}(X:SortInt{{}})), \equals{{SortInt{{}}, R}}(deep{{}}({}), {}))) []",
        int(n),
        int(n)
    )
}

/// The rewrite rule `state => right`.
fn rule(right: &str) -> String {
    format!(
        r#"axiom{{}} \rewrites{{SortS{{}}}}(\and{{SortS{{}}}}(state{{}}(), \top{{SortS{{}}}}()), {right}) [label{{}}("advance")]"#
    )
}

fn module(axioms: &[String]) -> kore::Definition {
    let source = format!(
        "[] module MAIN {PRELUDE} {} endmodule []",
        axioms.join("\n")
    );
    parse_definition(&source).expect("the fixture parses")
}

/// `syntax` loaded and `initial` executed on an 8 MiB thread; `bounded` forbids the simplifier
/// to extend the thread's stack with segments.
fn run(
    syntax: kore::Definition,
    initial: &'static str,
    max_depth: u64,
    bounded: bool,
) -> ExecutionResult {
    std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(move || {
            let work = || {
                let definition = BackendDefinition::internalize(&syntax, "MAIN")
                    .expect("the fixture internalizes");
                let initial = Pattern {
                    term: internal_term(&definition, initial),
                    constraints: Vec::new(),
                };
                execute(
                    &definition,
                    initial,
                    ExecutionOptions {
                        max_depth,
                        ..ExecutionOptions::default()
                    },
                )
            };
            if bounded {
                with_simplification_stack_budget(0, work)
            } else {
                work()
            }
        })
        .expect("the thread starts")
        .join()
        .expect("the run does not panic")
}

/// A state whose simplification recurses deeper than the thread's stack holds ends as a leaf
/// stopped for lack of stack, and the run counts the stop; the same run with the default budget
/// meets none.
#[test]
fn a_state_that_runs_out_of_stack_is_a_counted_stopped_leaf() {
    let axioms = deep_recursion().to_vec();
    let initial = r#"done{}(deep{}(\dv{SortInt{}}("100000")))"#;
    let free = run(module(&axioms), initial, 0, false);
    assert_eq!(free.stack_stops, 0, "{:?}", free.leaves);
    assert!(
        free.leaves
            .iter()
            .all(|leaf| !matches!(leaf.halt_reason, HaltReason::Stopped(_))),
        "{:?}",
        free.leaves
    );
    let bounded = run(module(&axioms), initial, 0, true);
    assert!(bounded.stack_stops >= 1, "{:?}", bounded.leaves);
    assert!(
        matches!(
            bounded.leaves.as_slice(),
            [leaf] if leaf.halt_reason == HaltReason::Stopped(StopCause::StackExhausted(StackLimit::ThreadBudget(0)))
        ),
        "{:?}",
        bounded.leaves
    );
}

/// A run whose rule's definedness obligation needs a deep ceil-equation instance counts the stops
/// it meets there, those a refinement dismissed included: the run meets more stack stops than its
/// stopped leaves show, so a count read off the leaves would be smaller. With the default budget
/// it meets none.
#[test]
fn a_run_counts_the_stack_stops_of_its_definedness_obligations() {
    let axioms = [
        deep_recursion().to_vec(),
        vec![
            ceil_of_p(100_000),
            rule(r#"done{}(p{}(\dv{SortInt{}}("0")))"#),
        ],
    ]
    .concat();
    let free = run(module(&axioms), "state{}()", 1, false);
    assert_eq!(free.stack_stops, 0, "{:?}", free.leaves);
    let bounded = run(module(&axioms), "state{}()", 1, true);
    let stopped = bounded
        .leaves
        .iter()
        .filter(|leaf| {
            matches!(
                leaf.halt_reason,
                HaltReason::Stopped(StopCause::StackExhausted(_))
            )
        })
        .count();
    assert!(
        bounded.stack_stops > stopped,
        "{} stack stops counted, {stopped} stopped leaves: {:?}",
        bounded.stack_stops,
        bounded.leaves
    );
}

/// A rule `from => to` labelled `label`, over constructors of `SortS`.
fn edge(label: &str, from: &str, to: &str) -> String {
    format!(
        r#"axiom{{}} \rewrites{{SortS{{}}}}(\and{{SortS{{}}}}({from}, \top{{SortS{{}}}}()), {to}) [label{{}}("{label}")]"#
    )
}

/// `syntax` loaded and `state` executed under `result_modality` on an 8 MiB thread whose
/// simplifier may not extend its stack, with the number of arrivals the run merged.
fn run_in(syntax: kore::Definition, result_modality: ResultModality) -> (ExecutionResult, u64) {
    std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(move || {
            with_simplification_stack_budget(0, || {
                let definition = BackendDefinition::internalize(&syntax, "MAIN")
                    .expect("the fixture internalizes");
                let initial = Pattern {
                    term: internal_term(&definition, "state{}()"),
                    constraints: Vec::new(),
                };
                let before = snapshot();
                let result = execute(
                    &definition,
                    initial,
                    ExecutionOptions {
                        result_modality,
                        ..ExecutionOptions::default()
                    },
                );
                let merged = snapshot()
                    .delta(&before)
                    .get(Counter::ExecutionStatesMerged);
                (result, merged)
            })
        })
        .expect("the thread starts")
        .join()
        .expect("the run does not panic")
}

/// A state-set run counts the stack stops of the states it explores: `state` rewrites to `left`
/// and `right`, both of which rewrite to `mid`, whose successor `done(deep(100000))` runs out of
/// stack. The path-set run reaches that successor twice and counts its stops twice; the state-set
/// run merges the second `mid`, whose subtree the first one's stands for, and counts them once.
#[test]
fn a_merged_run_counts_the_stack_stops_of_the_states_it_explores() {
    let constructor = |name: &str| {
        format!(
            "symbol {name}{{}}() : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]"
        )
    };
    let axioms = [
        deep_recursion().to_vec(),
        vec![
            constructor("left"),
            constructor("right"),
            constructor("mid"),
            edge("state-left", "state{}()", "left{}()"),
            edge("state-right", "state{}()", "right{}()"),
            edge("left-mid", "left{}()", "mid{}()"),
            edge("right-mid", "right{}()", "mid{}()"),
            edge(
                "mid-done",
                "mid{}()",
                r#"done{}(deep{}(\dv{SortInt{}}("100000")))"#,
            ),
        ],
    ]
    .concat();
    let (path_set, _) = run_in(module(&axioms), ResultModality::PathSet);
    let (state_set, merged) = run_in(module(&axioms), ResultModality::StateSet);
    eprintln!(
        "stack stops: path-set {}, state-set {}, merged {merged}",
        path_set.stack_stops, state_set.stack_stops
    );
    assert_eq!(merged, 1, "{:?}", state_set.leaves);
    assert!(state_set.stack_stops >= 1, "{:?}", state_set.leaves);
    assert_eq!(path_set.stack_stops, 2 * state_set.stack_stops);
}
