//! Equation matching for concrete nil and cons productions in one overload family.

use k_rust_backend::{
    definition::BackendDefinition,
    matching::{FailReason, MatchMode, MatchResult, match_terms_in_definition},
    rewrite::{Pattern, RewriteResult, rewrite_step},
    simplify::{SimplificationOptions, simplify},
    term::Term,
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

/// FUN's `Bottoms < Vals < Exps` list family with the frontend's symbol attributes, the two
/// total matching functions with `owise` equations, and the two case-selection rules.
fn nil_cons_definition() -> BackendDefinition {
    let syntax = parse_definition(include_str!("../fixtures/overloaded-list-owise.kore"))
        .expect("nil/cons fixture should parse");
    BackendDefinition::internalize(&syntax, "OVERLOADED-LIST-OWISE")
        .expect("nil/cons fixture should internalize")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    let syntax = parse_pattern(source).expect("term should parse");
    definition
        .internalize_term(&syntax, &[])
        .expect("term should internalize")
}

const EMPTY_EXPS: &str = "inj{SortBottoms{}, SortExps{}}(dotBottoms{}())";
const EMPTY_VALS: &str = "inj{SortBottoms{}, SortVals{}}(dotBottoms{}())";
/// `[1]` as the evaluated value list `_,_Vals(1, .Bottoms)`.
const ONE_VALS: &str = "vals{}(one{}(), inj{SortBottoms{}, SortVals{}}(dotBottoms{}()))";
/// `[h|t]`, the cons pattern expression headed by the anywhere production.
const PIPE_EXP: &str = "pipe{}(exps{}(inj{SortName{}, SortExp{}}(name{}()), inj{SortBottoms{}, SortExps{}}(dotBottoms{}())), inj{SortName{}, SortExp{}}(name{}()))";

fn evaluate(definition: &BackendDefinition, pattern: &str, subject: &str) -> MatchResult {
    match_terms_in_definition(
        MatchMode::Evaluate,
        definition,
        &term(definition, pattern),
        &term(definition, subject),
    )
}

// ---------- matching: the pairs the equation scan asks ----------

/// The nil pattern and concrete cons subject have distinct productions in the same overload
/// family.
#[test]
fn nil_pattern_refutes_a_concrete_cons_subject() {
    let definition = nil_cons_definition();
    assert!(
        matches!(
            evaluate(&definition, "dotVals{}()", ONE_VALS),
            MatchResult::Failed(FailReason::DifferentSymbols(..))
        ),
        "{:?}",
        evaluate(&definition, "dotVals{}()", ONE_VALS)
    );
}

/// The same distinction holds at the greater list sort.
#[test]
fn nil_pattern_refutes_a_concrete_cons_subject_of_the_greater_sort() {
    let definition = nil_cons_definition();
    let subject = "exps{}(fun{}(), inj{SortBottoms{}, SortExps{}}(dotBottoms{}()))";
    assert!(
        matches!(
            evaluate(&definition, "dotExps{}()", subject),
            MatchResult::Failed(FailReason::DifferentSymbols(..))
        ),
        "{:?}",
        evaluate(&definition, "dotExps{}()", subject)
    );
}

/// Positive control, equation `aux-cons` argument `X0`: the cons pattern against the injected
/// empty list is decided by the overload-head-versus-rigid arm (`matching.rs:2110`).
#[test]
fn cons_pattern_refutes_an_injected_nil_subject() {
    let definition = nil_cons_definition();
    for (pattern, subject) in [
        ("exps{}(E:SortExp{}, Es:SortExps{})", EMPTY_EXPS),
        ("vals{}(V:SortVal{}, Vs:SortVals{})", EMPTY_VALS),
    ] {
        assert!(
            matches!(
                evaluate(&definition, pattern, subject),
                MatchResult::Failed(FailReason::DifferentSymbols(..))
            ),
            "{pattern} vs {subject}: {:?}",
            evaluate(&definition, pattern, subject)
        );
    }
}

/// Nil and cons productions remain distinct when either production reaches the comparison
/// through an intermediate or least-sort injection in the three-level overload family.
#[test]
fn overload_list_shapes_stay_distinct_through_injections() {
    let definition = nil_cons_definition();
    for (pattern, subject) in [
        (
            "dotExps{}()",
            "inj{SortVals{}, SortExps{}}(vals{}(one{}(), inj{SortBottoms{}, SortVals{}}(dotBottoms{}())))",
        ),
        (
            "dotExps{}()",
            "inj{SortBottoms{}, SortExps{}}(bottoms{}(bottom{}(), dotBottoms{}()))",
        ),
        (
            "exps{}(E:SortExp{}, Es:SortExps{})",
            "inj{SortVals{}, SortExps{}}(dotVals{}())",
        ),
        (
            "exps{}(E:SortExp{}, Es:SortExps{})",
            "inj{SortBottoms{}, SortExps{}}(dotBottoms{}())",
        ),
        (
            "dotVals{}()",
            "inj{SortBottoms{}, SortVals{}}(bottoms{}(bottom{}(), dotBottoms{}()))",
        ),
        (
            "vals{}(V:SortVal{}, Vs:SortVals{})",
            "inj{SortBottoms{}, SortVals{}}(dotBottoms{}())",
        ),
    ] {
        assert!(
            matches!(
                evaluate(&definition, pattern, subject),
                MatchResult::Failed(FailReason::DifferentSymbols(..))
            ),
            "{pattern} vs {subject}: {:?}",
            evaluate(&definition, pattern, subject)
        );
    }
}

/// The overloaded list pattern cannot match a concrete expression headed by another anywhere
/// production.
#[test]
fn list_pattern_refutes_a_concrete_anywhere_head() {
    let definition = nil_cons_definition();
    assert!(
        matches!(
            evaluate(&definition, "listExp{}(Es:SortExps{})", PIPE_EXP),
            MatchResult::Failed(..)
        ),
        "{:?}",
        evaluate(&definition, "listExp{}(Es:SortExps{})", PIPE_EXP)
    );
}

/// An injected name pattern cannot match the same concrete anywhere-headed expression.
#[test]
fn injected_name_pattern_refutes_a_concrete_anywhere_head() {
    let definition = nil_cons_definition();
    let pattern = "inj{SortName{}, SortExp{}}(N:SortName{})";
    assert!(
        matches!(
            evaluate(&definition, pattern, PIPE_EXP),
            MatchResult::Failed(..)
        ),
        "{:?}",
        evaluate(&definition, pattern, PIPE_EXP)
    );
}

/// Negative control: a subject whose list is genuinely symbolic (an ordinary function
/// application, or a variable) must keep the pair deferred. This preserves the symbolic boundary.
#[test]
fn nil_pattern_defers_a_genuinely_symbolic_subject() {
    let definition = nil_cons_definition();
    for subject in [
        "ordinaryVals{}(inj{SortBottoms{}, SortVals{}}(dotBottoms{}()))",
        "Vs:SortVals{}",
        "vals{}(V:SortVal{}, inj{SortBottoms{}, SortVals{}}(dotBottoms{}()))",
        "vals{}(one{}(), Vs:SortVals{})",
    ] {
        assert!(
            matches!(
                evaluate(&definition, "dotVals{}()", subject),
                MatchResult::Indeterminate { .. }
            ),
            "{subject}: {:?}",
            evaluate(&definition, "dotVals{}()", subject)
        );
    }
}

// ---------- evaluation: the owise equation must fire ----------

/// `getMatchingAux(.Bottoms, (1, .Bottoms))` falls through to its `owise` equation.
#[test]
fn nil_against_a_concrete_cons_evaluates_to_the_owise_result() {
    let definition = nil_cons_definition();
    let input = term(
        &definition,
        &format!("getMatchingAux{{}}({EMPTY_EXPS}, {ONE_VALS})"),
    );
    let result = simplify(&definition, &input, SimplificationOptions::default())
        .expect("getMatchingAux should simplify");
    assert_eq!(result.term, term(&definition, "matchFailure{}()"));
}

/// Third instance of the same pair: a bare cons application of the greater sort (a pattern list
/// that is not all names, so it is not injected from `Names`) against the empty value list.
/// `aux-cons` refutes on `X1`, then `aux-nil` refutes on `X0` (`dotExps` against `exps(...)`).
#[test]
fn bare_cons_against_the_empty_value_list_evaluates_to_the_owise_result() {
    let definition = nil_cons_definition();
    let cons_exps = "exps{}(fun{}(), inj{SortBottoms{}, SortExps{}}(dotBottoms{}()))";
    let input = term(
        &definition,
        &format!("getMatchingAux{{}}({cons_exps}, {EMPTY_VALS})"),
    );
    let result = simplify(&definition, &input, SimplificationOptions::default())
        .expect("getMatchingAux should simplify");
    assert_eq!(result.term, term(&definition, "matchFailure{}()"));
}

/// Positive controls: an injected cons against nil (FUN's `[a,b,c]` shape, whose tail is
/// `inj{Names,Exps}`), nil against nil, and cons against cons are decided today.
#[test]
fn decided_list_shapes_evaluate() {
    let definition = nil_cons_definition();
    let cons_exps = "exps{}(fun{}(), inj{SortBottoms{}, SortExps{}}(dotBottoms{}()))";
    let injected_cons_exps = "inj{SortVals{}, SortExps{}}(vals{}(one{}(), inj{SortBottoms{}, SortVals{}}(dotBottoms{}())))";
    for (input, expected) in [
        (
            format!("getMatchingAux{{}}({injected_cons_exps}, {EMPTY_VALS})"),
            "matchFailure{}()",
        ),
        (
            format!("getMatchingAux{{}}({EMPTY_EXPS}, {EMPTY_VALS})"),
            "matchResult{}(one{}())",
        ),
        (
            format!("getMatchingAux{{}}({cons_exps}, {ONE_VALS})"),
            "matchResult{}(one{}())",
        ),
    ] {
        let input = term(&definition, &input);
        let result = simplify(&definition, &input, SimplificationOptions::default())
            .expect("getMatchingAux should simplify");
        assert_eq!(result.term, term(&definition, expected), "{input:?}");
    }
}

/// `getMatching([h|t], [])` falls through after the positive equations are refuted.
#[test]
fn pipe_pattern_against_the_empty_value_list_evaluates_to_the_owise_result() {
    let definition = nil_cons_definition();
    let input = term(
        &definition,
        &format!("getMatching{{}}({PIPE_EXP}, listVal{{}}({EMPTY_VALS}))"),
    );
    let result = simplify(&definition, &input, SimplificationOptions::default())
        .expect("getMatching should simplify");
    assert_eq!(result.term, term(&definition, "matchFailure{}()"));
}

/// Negative control: a genuinely symbolic argument keeps the application unevaluated.
#[test]
fn symbolic_arguments_keep_the_function_unevaluated() {
    let definition = nil_cons_definition();
    for input in [
        format!("getMatchingAux{{}}(Es:SortExps{{}}, {ONE_VALS})"),
        format!(
            "getMatchingAux{{}}({EMPTY_EXPS}, ordinaryVals{{}}(inj{{SortBottoms{{}}, SortVals{{}}}}(dotBottoms{{}}())))"
        ),
    ] {
        let input = term(&definition, &input);
        let result = simplify(&definition, &input, SimplificationOptions::default())
            .expect("getMatchingAux should simplify");
        assert_eq!(result.term, input);
    }
}

// ---------- rewriting: no narrowing of a ground configuration ----------

fn ground_case_configuration(definition: &BackendDefinition) -> Pattern {
    Pattern {
        term: term(
            definition,
            &format!("state{{}}(getMatchingAux{{}}({EMPTY_EXPS}, {ONE_VALS}))"),
        ),
        constraints: Vec::new(),
    }
}

fn assert_one_failed_successor(definition: &BackendDefinition, result: RewriteResult) {
    let RewriteResult::Finished(applied) = result else {
        panic!("the ground case selection must be decided: {result:?}");
    };
    assert_eq!(applied.unique_id, "fail");
    assert_eq!(applied.pattern.term, term(definition, "failed{}()"));
    assert!(applied.pattern.constraints.is_empty());
}

/// Simplification decides the total function before rewriting, so the no-solver step returns one
/// `failed()` successor without needing a satisfiability query.
#[test]
fn blocked_total_function_does_not_narrow_a_ground_configuration() {
    let definition = nil_cons_definition();
    let subject = ground_case_configuration(&definition);
    assert_one_failed_successor(&definition, rewrite_step(&definition, &subject, &mut 0));
}

/// The same step with Z3 has no existential binding branch or rule-complement remainder.
#[cfg(feature = "z3")]
#[test]
fn blocked_total_function_does_not_narrow_a_ground_configuration_with_z3() {
    let definition = nil_cons_definition();
    let subject = ground_case_configuration(&definition);
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    assert_one_failed_successor(
        &definition,
        k_rust_backend::rewrite::rewrite_step_with_solver(&definition, &subject, &mut 0, &solver),
    );
}
