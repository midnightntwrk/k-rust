//! The native stack one level of a nested function evaluation takes. `deep(N) = deep(N - 1) +Int
//! 1` keeps one lineage per level open in the term simplifier (`simplify::simplify_on_stack`,
//! through the children step of the `+Int` application), so how deep an evaluation a thread's stack
//! holds, with no segment beyond it (`stop::with_segment_budget(0, ..)`), bounds the frames of one
//! level.

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::BackendDefinition,
    simplify::{SimplificationOptions, simplify},
    stop::{StopCause, with_segment_budget},
    term::Term,
};

const DEFINITION: &str = r#"[] module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol subInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.sub"), smt-hook{}("-")]
    hooked-symbol addInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
    hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
    symbol deep{}(SortInt{}) : SortInt{} [function{}(), total{}()]
    axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, \dv{SortInt{}}("0")), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))) []
    axiom{R} \implies{R}(\and{R}(\equals{SortBool{}, R}(gtInt{}(VarN:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarN:SortInt{}), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(addInt{}(deep{}(subInt{}(VarN:SortInt{}, \dv{SortInt{}}("1"))), \dv{SortInt{}}("1")), \top{SortInt{}}()))) []
endmodule []"#;

const STACK: usize = 8 << 20;

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .admit_unverified(&parse_pattern(source).expect("the term parses"), &[])
        .internalize_term()
        .expect("the term internalizes")
}

/// Whether `deep(levels)` evaluates to `levels` on a thread of `STACK` bytes whose simplifier
/// may take no segment; `false` when it stops for want of stack.
fn evaluates(definition: &BackendDefinition, levels: usize) -> bool {
    let subject = term(
        definition,
        &format!(r#"deep{{}}(\dv{{SortInt{{}}}}("{levels}"))"#),
    );
    let expected = term(definition, &format!(r#"\dv{{SortInt{{}}}}("{levels}")"#));
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(STACK)
            .spawn_scoped(scope, || {
                with_segment_budget(0, || {
                    match simplify(definition, &subject, SimplificationOptions::default()) {
                        Ok(Ok(simplified)) => {
                            assert_eq!(simplified.term, expected, "deep({levels})");
                            true
                        }
                        Ok(Err(error)) => panic!("deep({levels}) failed: {error}"),
                        Err(stop) => match stop.into_cause() {
                            StopCause::StackExhausted(_) => false,
                            cause => panic!("deep({levels}) stopped: {cause:?}"),
                        },
                    }
                })
            })
            .expect("the thread starts")
            .join()
            .expect("the work does not panic")
    })
}

/// The most stack one level may take in an optimized build: about 2.1 KiB are taken at opt-level 1
/// with debug assertions on aarch64, where 5.0 KiB were taken while the work of a round after its
/// children step, and the shapes of children that need an order of their own, were part of the
/// recursive frame.
const STACK_PER_LEVEL: usize = 3 * 1024;

/// An unoptimized build keeps every local in its own slot, so the bound holds only where the
/// code is optimized (`build.rs` reports the level).
const OPTIMIZED: bool = cfg!(any(
    k_rust_opt_level = "1",
    k_rust_opt_level = "2",
    k_rust_opt_level = "3",
    k_rust_opt_level = "s",
    k_rust_opt_level = "z"
));

#[test]
fn a_nested_evaluation_takes_at_most_its_bound_of_stack_per_level() {
    let syntax = parse_definition(DEFINITION).expect("the fixture parses");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("the fixture internalizes");
    assert!(evaluates(&definition, 100), "a shallow evaluation fits");
    if OPTIMIZED {
        let levels = STACK / STACK_PER_LEVEL;
        assert!(
            evaluates(&definition, levels),
            "deep({levels}) does not fit in {STACK} bytes: a level takes more than {STACK_PER_LEVEL}"
        );
    }
}
