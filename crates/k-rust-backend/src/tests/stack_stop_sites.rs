//! The sites of execution that dismiss a stop met while only refining a sound result
//! (`Stop::forgo_refinement`) still count it when it is for lack of native stack
//! (`stop::counting_stack_stops`, read by `ExecutionResult::stack_stops`). Each test makes one
//! site meet such a stop: it runs on an 8 MiB thread whose simplifier may not extend its stack
//! (`stop::with_segment_budget(0, ..)`) and recurses deeper than that thread holds.
//!
//! The site that refutes a list update (`matching::collections::list_update_cannot_match`)
//! evaluates one builtin hook, which takes no simplifier stack, so it cannot meet such a stop.
//! The leaf normalisation site is tested in `rewrite::execute`'s own tests, and the ceil-condition
//! site end to end (`tests/backend/execution_stack_stops.rs`).

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    deferred::{Folded, fold_hooks_or_keep},
    definition::BackendDefinition,
    fresh::FreshCounter,
    rewrite::{Pattern, RewriteResult, rewrite_step_with_solver},
    smt::NoSolver,
    stop::{counting_stack_stops, with_segment_budget},
    term::Term,
};

/// `deep(N)` recurses `N` levels, not in tail position; `p` is partial, its ceil equation
/// `\ceil(p(X)) = (X ==Int 1)`; `state => done(p(0))` is undefined on every instance.
const DEFINITION: &str = r#"[] module MAIN
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
    axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, \dv{SortInt{}}("0")), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))) []
    axiom{R} \implies{R}(\and{R}(\equals{SortBool{}, R}(gtInt{}(VarN:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarN:SortInt{}), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(addInt{}(deep{}(subInt{}(VarN:SortInt{}, \dv{SortInt{}}("1"))), \dv{SortInt{}}("1")), \top{SortInt{}}()))) []
    axiom{R} \implies{R}(\top{R}(), \equals{R, R}(\ceil{SortInt{}, R}(p{}(X:SortInt{})), \equals{SortBool{}, R}(eqInt{}(X:SortInt{}, \dv{SortInt{}}("1")), \dv{SortBool{}}("true")))) []
    axiom{} \rewrites{SortS{}}(\and{SortS{}}(state{}(), \top{SortS{}}()), done{}(p{}(\dv{SortInt{}}("0")))) [label{}("advance")]
endmodule []"#;

fn definition() -> BackendDefinition {
    let syntax = parse_definition(DEFINITION).expect("the fixture parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the fixture internalizes")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .admit_unverified(&parse_pattern(source).expect("the term parses"), &[])
        .internalize_term()
        .expect("the term internalizes")
}

/// `work` on an 8 MiB thread whose simplifier may take no stack segment, with the stack stops
/// it meets.
fn on_a_bounded_stack<T: Send>(work: impl FnOnce() -> T + Send) -> (T, usize) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn_scoped(scope, || {
                with_segment_budget(0, || counting_stack_stops(work))
            })
            .expect("the thread starts")
            .join()
            .expect("the work does not panic")
    })
}

/// `fold_hooks_or_keep` folds a term of `+Int` nested deeper than the thread's stack holds: the
/// fold stops, the term is kept as it is, and the stop is counted.
#[test]
fn a_fold_that_runs_out_of_stack_keeps_the_term_and_is_counted() {
    // Parsing and internalizing a term this deep take more stack than a test thread has.
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            let definition = definition();
            let depth = 100_000;
            let source = format!(
                "{}{}{}",
                r"addInt{}(X:SortInt{}, ".repeat(depth),
                r#"\dv{SortInt{}}("1")"#,
                ")".repeat(depth)
            );
            let deep = term(&definition, &source);
            let (kept, stops) = on_a_bounded_stack(|| {
                matches!(fold_hooks_or_keep(&definition, &deep), Folded::Term(kept) if kept == deep)
            });
            assert!(stops >= 1, "no stack stop was counted");
            assert!(kept, "the term was not kept as it is");
            let shallow = term(&definition, r#"addInt{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
            let ((), none) = counting_stack_stops(|| {
                let _ = fold_hooks_or_keep(&definition, &shallow);
            });
            assert_eq!(none, 0);
        })
        .expect("the thread starts")
        .join()
        .expect("the test does not panic");
}

/// The undefined instances of a step (`state => done(p(0))`, undefined everywhere) are simplified
/// before they make a `trivial` leaf; with a constraint whose simplification recurses deeper than
/// the thread's stack holds, that simplification stops, the constraints are kept unsimplified,
/// and the stop is counted.
#[test]
fn undefined_instances_that_run_out_of_stack_keep_their_constraints_and_are_counted() {
    let definition = definition();
    let subject = Pattern {
        term: term(&definition, "state{}()"),
        constraints: Vec::new(),
    };
    let result = rewrite_step_with_solver(
        &definition,
        &subject,
        &mut FreshCounter::default(),
        &NoSolver,
    )
    .expect("the step does not stop");
    let RewriteResult::Trivial(_, mut applications) = result else {
        panic!("the step is undefined: {result:?}");
    };
    let (deep, _) = definition
        .admit_unverified(
            &parse_pattern(
                r#"\equals{SortBool{}, SortS{}}(eqInt{}(deep{}(\dv{SortInt{}}("100000")), \dv{SortInt{}}("100000")), \dv{SortBool{}}("true"))"#,
            )
            .expect("the constraint parses"),
            &[],
        )
        .internalize_predicate()
        .expect("the constraint internalizes");
    let mut entry = applications.remove(0);
    entry.before.constraints.push(deep.clone());
    let (instances, stops) = on_a_bounded_stack(|| {
        entry
            .decided_undefined_instances(&definition, 64, &NoSolver)
            .expect("the emptiness query does not stop")
    });
    assert!(stops >= 1, "no stack stop was counted");
    let instances = instances.expect("the instances are not shown empty");
    assert!(
        instances.constraints.contains(&deep),
        "the constraints were not kept unsimplified: {:?}",
        instances.constraints
    );
}
