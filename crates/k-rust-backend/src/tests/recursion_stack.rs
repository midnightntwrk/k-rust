//! The native stack one level of a nested function evaluation takes. `deep(N) = deep(N - 1) +Int
//! 1` keeps one lineage per level open in the term simplifier (`simplify::simplify_on_stack`,
//! through the children step of the `+Int` application), so how deep an evaluation a thread's stack
//! holds, with no segment beyond it (`stop::with_segment_budget(0, ..)`), bounds the frames of one
//! level. `ok(X, N) = true requires ok(X, N -Int 1)` recurses through its equation's `requires`
//! instead: each level is a decision of a condition, whose predicate simplifier enters the next
//! level; `okCeil`, `okNot` and `okOr` do the same through a `\ceil`, a `\not` and an `\or` of
//! the `requires` ([`Requires`]).

use k_rust_kore::{
    kore::parser::{parse_definition, parse_pattern},
    measure::{self, Counter},
};

use crate::{
    definition::BackendDefinition,
    rule::ApartScope,
    simplify::{SimplificationOptions, normal_forms, simplify},
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
    symbol chain{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), total{}()]
    symbol ok{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}()]
    axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, \dv{SortInt{}}("0")), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))) []
    axiom{R} \implies{R}(\and{R}(\equals{SortBool{}, R}(gtInt{}(VarN:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarN:SortInt{}), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(addInt{}(deep{}(subInt{}(VarN:SortInt{}, \dv{SortInt{}}("1"))), \dv{SortInt{}}("1")), \top{SortInt{}}()))) []
    axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \and{R}(\in{SortInt{}, R}(X1:SortInt{}, \dv{SortInt{}}("0")), \top{R}()))), \equals{SortInt{}, R}(chain{}(X0:SortInt{}, X1:SortInt{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))) []
    axiom{R} \implies{R}(\and{R}(\equals{SortBool{}, R}(gtInt{}(VarN:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \and{R}(\in{SortInt{}, R}(X1:SortInt{}, VarN:SortInt{}), \top{R}()))), \equals{SortInt{}, R}(chain{}(X0:SortInt{}, X1:SortInt{}), \and{SortInt{}}(addInt{}(chain{}(VarX:SortInt{}, subInt{}(VarN:SortInt{}, \dv{SortInt{}}("1"))), \dv{SortInt{}}("1")), \top{SortInt{}}()))) []
    axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \and{R}(\in{SortInt{}, R}(X1:SortInt{}, \dv{SortInt{}}("0")), \top{R}()))), \equals{SortBool{}, R}(ok{}(X0:SortInt{}, X1:SortInt{}), \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}()))) [priority{}("40")]
    axiom{R} \implies{R}(\and{R}(\equals{SortBool{}, R}(ok{}(VarX:SortInt{}, subInt{}(VarN:SortInt{}, \dv{SortInt{}}("1"))), \dv{SortBool{}}("true")), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \and{R}(\in{SortInt{}, R}(X1:SortInt{}, VarN:SortInt{}), \top{R}()))), \equals{SortBool{}, R}(ok{}(X0:SortInt{}, X1:SortInt{}), \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}()))) []
    symbol okCeil{}(SortInt{}, SortInt{}) : SortBool{} [function{}()]
    symbol okNot{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}()]
    symbol okOr{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}()]
    axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \and{R}(\in{SortInt{}, R}(X1:SortInt{}, \dv{SortInt{}}("0")), \top{R}()))), \equals{SortBool{}, R}(okCeil{}(X0:SortInt{}, X1:SortInt{}), \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}()))) [priority{}("40")]
    axiom{R} \implies{R}(\and{R}(\ceil{SortBool{}, R}(okCeil{}(VarX:SortInt{}, subInt{}(VarN:SortInt{}, \dv{SortInt{}}("1")))), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \and{R}(\in{SortInt{}, R}(X1:SortInt{}, VarN:SortInt{}), \top{R}()))), \equals{SortBool{}, R}(okCeil{}(X0:SortInt{}, X1:SortInt{}), \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}()))) []
    axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \and{R}(\in{SortInt{}, R}(X1:SortInt{}, \dv{SortInt{}}("0")), \top{R}()))), \equals{SortBool{}, R}(okNot{}(X0:SortInt{}, X1:SortInt{}), \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}()))) [priority{}("40")]
    axiom{R} \implies{R}(\and{R}(\not{R}(\equals{SortBool{}, R}(okNot{}(VarX:SortInt{}, subInt{}(VarN:SortInt{}, \dv{SortInt{}}("1"))), \dv{SortBool{}}("false"))), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \and{R}(\in{SortInt{}, R}(X1:SortInt{}, VarN:SortInt{}), \top{R}()))), \equals{SortBool{}, R}(okNot{}(X0:SortInt{}, X1:SortInt{}), \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}()))) []
    axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \and{R}(\in{SortInt{}, R}(X1:SortInt{}, \dv{SortInt{}}("0")), \top{R}()))), \equals{SortBool{}, R}(okOr{}(X0:SortInt{}, X1:SortInt{}), \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}()))) [priority{}("40")]
    axiom{R} \implies{R}(\and{R}(\or{R}(\equals{SortBool{}, R}(okOr{}(VarX:SortInt{}, subInt{}(VarN:SortInt{}, \dv{SortInt{}}("1"))), \dv{SortBool{}}("true")), \equals{SortInt{}, R}(VarN:SortInt{}, \dv{SortInt{}}("0"))), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \and{R}(\in{SortInt{}, R}(X1:SortInt{}, VarN:SortInt{}), \top{R}()))), \equals{SortBool{}, R}(okOr{}(X0:SortInt{}, X1:SortInt{}), \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}()))) []
endmodule []"#;

const STACK: usize = 8 << 20;

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .admit_unverified(&parse_pattern(source).expect("the term parses"), &[])
        .internalize_term()
        .expect("the term internalizes")
}

/// A nested evaluation of `levels` levels: `deep(levels)` (ground), or `chain(X, levels)`
/// (non-ground), each evaluating to `levels`.
#[derive(Clone, Copy)]
enum Chain {
    /// `deep(levels)`, with no proof's record open.
    Ground,
    /// `chain(X, levels)` with no proof's record open: the routed chain's own unrouted figure.
    Symbolic,
    /// `chain(X, levels)` inside a proof's record of normal forms (`simplify::normal_forms`):
    /// every level is a non-ground application, which the term simplifier routes through the
    /// record (`simplify::simplify_on_stack`), and each misses, so every level is recorded.
    Routed,
    /// `ok(X, levels)` inside a proof's record: every level decides its equation's `requires`,
    /// `ok(X, N -Int 1)`, a non-ground application that the decision's predicate simplifier
    /// enters under the condition being decided, and routes through the record with that
    /// condition active (GAP K17 part e); each misses, so every level is recorded. The
    /// application is the operand of the `requires`' atom of the given shape.
    Condition(Requires),
    /// `ok(X, levels)` with no proof's record open: the condition chain's own unrouted figure.
    UnroutedCondition(Requires),
}

/// The atom of a [`Chain::Condition`] level's `requires` whose operand is the next level.
#[derive(Clone, Copy)]
enum Requires {
    /// `ok(X, N -Int 1) = true`.
    Equals,
    /// `\ceil(okCeil(X, N -Int 1))`, of a partial `okCeil`.
    Ceil,
    /// `\not(okNot(X, N -Int 1) = false)`.
    Not,
    /// `okOr(X, N -Int 1) = true \/ N = 0`.
    Or,
}

impl Requires {
    fn symbol(self) -> &'static str {
        match self {
            Requires::Equals => "ok",
            Requires::Ceil => "okCeil",
            Requires::Not => "okNot",
            Requires::Or => "okOr",
        }
    }
}

/// Whether the evaluation of `chain` at `levels` levels evaluates to `levels` on a thread of
/// `STACK` bytes whose simplifier may take no segment; `false` when it stops for want of stack.
fn evaluates(definition: &BackendDefinition, chain: Chain, levels: usize) -> bool {
    let source = match chain {
        Chain::Ground => format!(r#"deep{{}}(\dv{{SortInt{{}}}}("{levels}"))"#),
        Chain::Symbolic | Chain::Routed => {
            format!(r#"chain{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("{levels}"))"#)
        }
        Chain::Condition(requires) | Chain::UnroutedCondition(requires) => format!(
            r#"{}{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("{levels}"))"#,
            requires.symbol()
        ),
    };
    let subject = term(definition, &source);
    let expected = match chain {
        Chain::Condition(_) | Chain::UnroutedCondition(_) => {
            r#"\dv{SortBool{}}("true")"#.to_owned()
        }
        Chain::Ground | Chain::Symbolic | Chain::Routed => {
            format!(r#"\dv{{SortInt{{}}}}("{levels}")"#)
        }
    };
    let expected = term(definition, &expected);
    // A non-ground level is simplified within its caller's lineage, from the iteration budget
    // that lineage has left, so a deep chain needs an unbounded one.
    let options = match chain {
        Chain::Ground => SimplificationOptions::default(),
        Chain::Symbolic | Chain::Routed | Chain::Condition(_) | Chain::UnroutedCondition(_) => {
            SimplificationOptions::unbounded()
        }
    };
    let run = || match simplify(definition, &subject, options) {
        Ok(Ok(simplified)) => {
            assert_eq!(simplified.term, expected, "{source}");
            true
        }
        Ok(Err(error)) => panic!("{source} failed: {error}"),
        Err(stop) => match stop.into_cause() {
            StopCause::StackExhausted(_) => false,
            cause => panic!("{source} stopped: {cause:?}"),
        },
    };
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(STACK)
            .spawn_scoped(scope, || {
                with_segment_budget(0, || match chain {
                    Chain::Ground | Chain::Symbolic | Chain::UnroutedCondition(_) => run(),
                    Chain::Routed | Chain::Condition(_) => {
                        let _apart = ApartScope::enter();
                        let _record = normal_forms::scope();
                        let before = measure::snapshot();
                        let fits = run();
                        let recorded = measure::snapshot()
                            .delta(&before)
                            .get(Counter::SimplifyNormalFormsSubtermRecorded);
                        assert!(
                            !fits || recorded >= levels as u64,
                            "{source}: {recorded} subterms recorded, not every level"
                        );
                        fits
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

/// The most stack one level of a recursion through an equation's `requires` may take in an
/// optimized build ([`Chain::Condition`]): a level is a decision, with the predicate simplifier's
/// frames and a routed term level inside it. At opt-level 1 with debug assertions on x86_64
/// (`deepest`), a level through an equality or a `\ceil` atom takes about 6.3 KiB, 0.2 KiB of
/// which the routing adds (6,418 bytes routed, 6,190 unrouted), and one through a `\not` about
/// 7.1 KiB (7,313), where 18.8 KiB were taken while the work of each frame on that path besides
/// the recursive call (the builtin step, the record of a verdict, the predicate theories, the
/// combination of several instances, ...) was part of the frame, and while a failure, a stop and
/// an applied equation's result were carried up the frames unboxed. A level through an `\or`
/// takes 7.9 KiB (8,081), too close to the bound to be held to it.
const STACK_PER_DECISION_LEVEL: usize = 8 * 1024;

fn takes_at_most_its_bound_of_stack_per_level(chain: Chain) {
    let syntax = parse_definition(DEFINITION).expect("the fixture parses");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("the fixture internalizes");
    assert!(
        evaluates(&definition, chain, 100),
        "a shallow evaluation fits"
    );
    if OPTIMIZED {
        let levels = STACK
            / match chain {
                Chain::Condition(_) | Chain::UnroutedCondition(_) => STACK_PER_DECISION_LEVEL,
                Chain::Ground | Chain::Symbolic | Chain::Routed => STACK_PER_LEVEL,
            };
        assert!(
            evaluates(&definition, chain, levels),
            "{levels} levels do not fit in {STACK} bytes: a level takes more than {}",
            STACK / levels
        );
    }
}

#[test]
fn a_nested_evaluation_takes_at_most_its_bound_of_stack_per_level() {
    takes_at_most_its_bound_of_stack_per_level(Chain::Ground);
}

/// GAP K17 part b: inside a proof, a level routed through the record of normal forms takes the
/// same bound as one that is not: the record's lookup and its record are out of line, off the
/// recursion path.
#[test]
fn a_nested_evaluation_routed_through_a_proofs_record_takes_at_most_its_bound_of_stack_per_level() {
    takes_at_most_its_bound_of_stack_per_level(Chain::Routed);
}

/// GAP K17 part e: a recursion through an equation's non-ground `requires` inside a proof takes
/// at most its own bound per decision level, a routed term level among its frames.
#[test]
fn a_recursion_through_a_requires_routed_through_a_proofs_record_takes_at_most_its_bound_of_stack_per_level()
 {
    takes_at_most_its_bound_of_stack_per_level(Chain::Condition(Requires::Equals));
}

/// The same bound holds where the next level is the operand of a `\ceil` atom of the `requires`:
/// the work of the ceil's arm before and after the simplification of its operand is out of line.
#[test]
fn a_recursion_through_a_ceil_in_a_requires_takes_at_most_its_bound_of_stack_per_level() {
    takes_at_most_its_bound_of_stack_per_level(Chain::Condition(Requires::Ceil));
}

/// The same bound holds where the next level is under a `\not` of the `requires`: the negation's
/// arm is its own frame, apart from the other connectives' and atoms'.
#[test]
fn a_recursion_through_a_negation_in_a_requires_takes_at_most_its_bound_of_stack_per_level() {
    takes_at_most_its_bound_of_stack_per_level(Chain::Condition(Requires::Not));
}

/// The deepest evaluation of `chain` that fits, and the stack per level it implies (a probe, run
/// by hand: `cargo test ... recursion_stack::deepest -- --ignored --nocapture`).
#[test]
#[ignore = "a measurement, run by hand"]
fn deepest() {
    let syntax = parse_definition(DEFINITION).expect("the fixture parses");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("the fixture internalizes");
    for (name, chain) in [
        ("ground", Chain::Ground),
        ("symbolic", Chain::Symbolic),
        ("routed", Chain::Routed),
        ("condition", Chain::Condition(Requires::Equals)),
        (
            "unrouted condition",
            Chain::UnroutedCondition(Requires::Equals),
        ),
        ("ceil condition", Chain::Condition(Requires::Ceil)),
        (
            "unrouted ceil condition",
            Chain::UnroutedCondition(Requires::Ceil),
        ),
        ("not condition", Chain::Condition(Requires::Not)),
        ("or condition", Chain::Condition(Requires::Or)),
    ] {
        let (mut fits, mut fails) = (1, 1 << 16);
        while fails - fits > 1 {
            let middle = (fits + fails) / 2;
            if evaluates(&definition, chain, middle) {
                fits = middle;
            } else {
                fails = middle;
            }
        }
        println!("{name}: {fits} levels, {} bytes per level", STACK / fits);
    }
}

/// A recursion through an equation's `requires` keeps, at its deepest, one node of the set of
/// rule conditions active against re-entry per level: each level's set is the one around it with
/// that level's key added, sharing it (`simplify::ActiveConditions`). Copying the set around
/// would keep `levels(levels + 1)/2` keys alive at once, which grows a recursion's memory with the
/// square of its depth. The evaluation is ground and concrete, as in an execution.
#[test]
fn a_recursion_through_a_requires_keeps_one_active_condition_node_per_level() {
    let syntax = parse_definition(DEFINITION).expect("the fixture parses");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("the fixture internalizes");
    let levels = 300;
    let subject = term(
        &definition,
        &format!(r#"ok{{}}(\dv{{SortInt{{}}}}("7"), \dv{{SortInt{{}}}}("{levels}"))"#),
    );
    let expected = term(&definition, r#"\dv{SortBool{}}("true")"#);
    let peak = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(STACK)
            .spawn_scoped(scope, || {
                let (simplified, peak) = crate::simplify::active::peak_nodes(|| {
                    simplify(&definition, &subject, SimplificationOptions::unbounded())
                });
                let simplified = simplified
                    .expect("the evaluation does not stop")
                    .expect("the evaluation does not fail");
                assert_eq!(simplified.term, expected);
                peak
            })
            .expect("the thread starts")
            .join()
            .expect("the work does not panic")
    });
    // Every level `N > 0` decides its condition with its own key active, and none more is made
    // per level.
    assert!(
        (levels..=levels + 1).contains(&peak),
        "{peak} active-condition nodes alive at once over {levels} levels"
    );
}
