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
    stop::{StackLimit, StopCause},
};
use k_rust_kore::kore::{ast as kore, parser::parse_definition};

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

/// A run whose rule's definedness obligation needs a deep ceil-equation instance counts the stop
/// it meets there; with the default budget it meets none.
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
    assert!(bounded.stack_stops >= 1, "{:?}", bounded.leaves);
}
