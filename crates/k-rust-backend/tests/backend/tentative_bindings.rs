//! A left-hand side that holds an application of a function with an algebraic axiom (here a
//! commutative one) matches a subject application of that function as written, binding its
//! arguments in order. Those bindings suffice for the match but are not forced: `cat(1, 2)` equals
//! `cat(2, 1)`, so the arguments may as well be bound the other way round. A later part of the
//! match that fails under the written order, or a `requires` refuted under it, therefore refutes
//! nothing, and the equation is not refuted by it: an `owise` equation is not reached. A part that
//! fails whatever the order still refutes the equation.

#![cfg(feature = "z3")]

use k_rust_backend::{
    definition::BackendDefinition, simplify::SimplificationOptions, smt::Z3Solver, term::Term,
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::{internal_term, unstopped::simplify_with_solver};

/// `cat` is a total commutative function without equations.
/// - `lookcv((cat(K, J) |-> val(J, V)) _)` is `V`, else 0 (`owise`): the key binds `J`, the
///   entry's value reads it again.
/// - `membcv(SetItem(val(cat(K, J), 0)) SetItem(val(J, 1)) _)` is 1, else 0 (`owise`): one
///   element binds `J`, another reads it again.
/// - `reqcv(cat(K, J))` is 1 where `K < J`, else 0 (`owise`).
const DEFINITION: &str = r#"[] module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-sort SortMap{}
        [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
    hooked-sort SortSet{}
        [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
    hooked-symbol ltInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.lt"), smt-hook{}("<")]
    sort SortVal{} []
    symbol val{}(SortInt{}, SortInt{}) : SortVal{} [constructor{}(), functional{}(), injective{}()]
    hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol mapItem{}(SortInt{}, SortVal{}) : SortMap{}
        [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
        [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
    hooked-symbol setUnit{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
    hooked-symbol setItem{}(SortVal{}) : SortSet{} [function{}(), total{}(), hook{}("SET.element")]
    hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{}
        [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
    symbol cat{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), total{}(), comm{}()]
    symbol lookcv{}(SortMap{}) : SortInt{} [function{}(), total{}()]
    symbol membcv{}(SortSet{}) : SortInt{} [function{}(), total{}()]
    symbol reqcv{}(SortInt{}) : SortInt{} [function{}(), total{}()]

    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortMap{}, R}(X0:SortMap{},
            mapConcat{}(mapItem{}(cat{}(VarK:SortInt{}, VarJ:SortInt{}),
                val{}(VarJ:SortInt{}, VarV:SortInt{})), VarM:SortMap{})),
            \top{R}())),
        \equals{SortInt{}, R}(lookcv{}(X0:SortMap{}), \and{SortInt{}}(VarV:SortInt{}, \top{SortInt{}}()))
    ) [label{}("lookcv-found")]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortMap{}, R}(X0:SortMap{}, VarN:SortMap{}), \top{R}())),
        \equals{SortInt{}, R}(lookcv{}(X0:SortMap{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))
    ) [label{}("lookcv-absent"), owise{}()]

    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortSet{}, R}(X0:SortSet{},
            setConcat{}(setItem{}(val{}(cat{}(VarK:SortInt{}, VarJ:SortInt{}), \dv{SortInt{}}("0"))),
                setConcat{}(setItem{}(val{}(VarJ:SortInt{}, \dv{SortInt{}}("1"))), VarS:SortSet{}))),
            \top{R}())),
        \equals{SortInt{}, R}(membcv{}(X0:SortSet{}), \and{SortInt{}}(\dv{SortInt{}}("1"), \top{SortInt{}}()))
    ) [label{}("membcv-found")]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortSet{}, R}(X0:SortSet{}, VarN:SortSet{}), \top{R}())),
        \equals{SortInt{}, R}(membcv{}(X0:SortSet{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))
    ) [label{}("membcv-absent"), owise{}()]

    axiom{R} \implies{R}(
        \and{R}(\equals{SortBool{}, R}(ltInt{}(VarK:SortInt{}, VarJ:SortInt{}), \dv{SortBool{}}("true")),
            \and{R}(\in{SortInt{}, R}(X0:SortInt{}, cat{}(VarK:SortInt{}, VarJ:SortInt{})), \top{R}())),
        \equals{SortInt{}, R}(reqcv{}(X0:SortInt{}), \and{SortInt{}}(\dv{SortInt{}}("1"), \top{SortInt{}}()))
    ) [label{}("reqcv-found")]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarN:SortInt{}), \top{R}())),
        \equals{SortInt{}, R}(reqcv{}(X0:SortInt{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))
    ) [label{}("reqcv-absent"), owise{}()]
endmodule []"#;

fn definition() -> BackendDefinition {
    let syntax = parse_definition(DEFINITION).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

fn cat(left: i64, right: i64) -> String {
    format!("cat{{}}({}, {})", int(left), int(right))
}

fn val(left: &str, right: i64) -> String {
    format!("val{{}}({left}, {})", int(right))
}

/// `source` simplified: the result and the equations applied.
fn simplified(definition: &BackendDefinition, source: &str) -> (Term, Vec<String>) {
    let solver = Z3Solver::new(definition).unwrap();
    let result = simplify_with_solver(
        definition,
        &internal_term(definition, source),
        &[],
        SimplificationOptions::default(),
        &solver,
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    (result.term, result.applied_rules.to_vec())
}

/// `source` stays unevaluated.
fn assert_kept(definition: &BackendDefinition, source: &str) {
    let (term, applied) = simplified(definition, source);
    assert_eq!(term, internal_term(definition, source), "{source}");
    assert!(applied.is_empty(), "{source}: {applied:?}");
}

/// `source` evaluates to `expected` by the equation labelled `rule`.
fn assert_evaluates(definition: &BackendDefinition, source: &str, expected: &str, rule: &str) {
    let (term, applied) = simplified(definition, source);
    assert_eq!(term, internal_term(definition, expected), "{source}");
    assert_eq!(applied, [rule], "{source}");
}

/// `lookcv((cat(1, 2) |-> val(1, 7)) (cat(3, 4) |-> val(9, 9)))` is 7: with `K = 2, J = 1` the
/// key `cat(K, J)` is `cat(1, 2)` and the value `val(J, V)` is `val(1, 7)`. Matching the key as
/// written binds `J` to 2, under which the value fails; that failure refutes only the written
/// order, so the `owise` equation is not reached.
#[test]
fn a_map_value_failing_under_a_key_bound_as_written_does_not_refute_the_entry() {
    let definition = definition();
    let entries = |first: &str| {
        format!(
            "lookcv{{}}(mapConcat{{}}(mapItem{{}}({first}, {}), mapItem{{}}({}, {})))",
            val(&int(1), 7),
            cat(3, 4),
            val(&int(9), 9)
        )
    };
    assert_kept(&definition, &entries(&cat(1, 2)));
    // Control: the order as written matches, and the equation applies.
    let (_, applied) = simplified(&definition, &entries(&cat(2, 1)));
    assert_eq!(applied, ["lookcv-found"]);
}

/// `membcv(SetItem(val(cat(1, 2), 0)) SetItem(val(1, 1)))` is 1, with `K = 2, J = 1`; the
/// element `val(J, 1)` fails only under the written order `J = 2`.
#[test]
fn a_set_element_failing_under_an_element_bound_as_written_does_not_refute_the_set() {
    let definition = definition();
    let set = |first: &str| {
        format!(
            "membcv{{}}(setConcat{{}}(setItem{{}}({}), setItem{{}}({})))",
            val(first, 0),
            val(&int(1), 1)
        )
    };
    assert_kept(&definition, &set(&cat(1, 2)));
    assert_evaluates(&definition, &set(&cat(2, 1)), &int(1), "membcv-found");
    // A set of one element is no instance in any order: the `owise` equation applies.
    assert_evaluates(
        &definition,
        &format!("membcv{{}}(setItem{{}}({}))", val(&int(1), 1)),
        &int(0),
        "membcv-absent",
    );
}

/// `reqcv(cat(2, 1))` is 1, with `K = 1, J = 2`; the `requires` `K < J` is refuted only under the
/// written order `K = 2, J = 1`.
#[test]
fn a_requires_refuted_under_arguments_bound_as_written_does_not_refute_the_equation() {
    let definition = definition();
    assert_kept(&definition, &format!("reqcv{{}}({})", cat(2, 1)));
    assert_evaluates(
        &definition,
        &format!("reqcv{{}}({})", cat(1, 2)),
        &int(1),
        "reqcv-found",
    );
}
