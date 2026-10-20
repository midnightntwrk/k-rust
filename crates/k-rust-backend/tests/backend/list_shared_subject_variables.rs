//! A list pattern that reads a variable the left-hand side bound before it holds, under that
//! binding, the subject's term: here a subject variable. Matching it against a subject list that
//! mentions the same variable is one-way matching with a variable on both sides, which matching
//! leaves undecided; the answer must not depend on whether the subject happens to reuse the
//! name. Undecided is no refutation, so the `owise` equation, whose premise is that the first
//! equation does not apply, must not apply either.

use k_rust_backend::{definition::BackendDefinition, simplify::SimplificationOptions, term::Term};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::{internal_term, unstopped::simplify};

/// `f(V, ListItem(K) ListItem(V) L)` is 1, and `f` is 0 otherwise (`owise`); `foo` is a list
/// function without equations, so `foo(B)` may be any list, `ListItem(B)` among them.
fn definition() -> BackendDefinition {
    let source = r#"[] module MAIN
        hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        sort SortKItem{} []
        hooked-sort SortList{}
            [hook{}("LIST.List"), unit{}(Lbl'Stop'List{}()), element{}(LblListItem{}()),
             concat{}(Lbl'Unds'List'Unds'{}())]
        hooked-symbol Lbl'Stop'List{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
        hooked-symbol LblListItem{}(SortKItem{}) : SortList{}
            [function{}(), total{}(), hook{}("LIST.element")]
        hooked-symbol Lbl'Unds'List'Unds'{}(SortList{}, SortList{}) : SortList{}
            [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
        symbol inj{From, To}(From) : To [sortInjection{}()]
        axiom{R} \exists{R}(Val:SortKItem{},
            \equals{SortKItem{}, R}(Val:SortKItem{}, inj{SortInt{}, SortKItem{}}(From:SortInt{})))
            [subsort{SortInt{}, SortKItem{}}()]
        symbol foo{}(SortInt{}) : SortList{} [function{}(), total{}()]
        symbol f{}(SortInt{}, SortList{}) : SortInt{} [function{}(), total{}()]
        axiom{R} \implies{R}(
            \and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarV:SortInt{}),
                \and{R}(\in{SortList{}, R}(X1:SortList{},
                    Lbl'Unds'List'Unds'{}(LblListItem{}(VarK:SortKItem{}),
                        Lbl'Unds'List'Unds'{}(
                            LblListItem{}(inj{SortInt{}, SortKItem{}}(VarV:SortInt{})),
                            VarL:SortList{}))),
                    \top{R}()))),
            \equals{SortInt{}, R}(f{}(X0:SortInt{}, X1:SortList{}),
                \and{SortInt{}}(\dv{SortInt{}}("1"), \top{SortInt{}}()))
        ) [label{}("f-second")]
        axiom{R} \implies{R}(
            \and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarJ:SortInt{}),
                \and{R}(\in{SortList{}, R}(X1:SortList{}, VarN:SortList{}), \top{R}()))),
            \equals{SortInt{}, R}(f{}(X0:SortInt{}, X1:SortList{}),
                \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))
        ) [label{}("f-other"), owise{}()]
    endmodule []"#;
    let syntax = parse_definition(source).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

/// `source` simplified: the result and the equations applied.
fn simplified(definition: &BackendDefinition, source: &str) -> (Term, Vec<String>) {
    let result = simplify(
        definition,
        &internal_term(definition, source),
        SimplificationOptions::default(),
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    (result.term, result.applied_rules.to_vec())
}

fn subject(first: &str, rest: &str) -> String {
    format!("f{{}}({first}, Lbl'Unds'List'Unds'{{}}(LblListItem{{}}(VarA:SortKItem{{}}), {rest}))")
}

/// `f(B, ListItem(A) foo(B))`: the first equation binds `V = B`, so its list pattern is
/// `ListItem(K) ListItem(B) L` against `ListItem(A) foo(B)`, which holds where
/// `foo(B) = ListItem(B) L`. That is undecided, so the application stays, as it does for
/// `foo(C)`, where the two sides share no variable.
#[test]
fn a_list_pattern_sharing_a_subject_variable_is_not_refuted() {
    let definition = definition();
    for rest in ["foo{}(VarB:SortInt{})", "foo{}(VarC:SortInt{})"] {
        let source = subject("VarB:SortInt{}", rest);
        let (term, applied) = simplified(&definition, &source);
        assert_eq!(term, internal_term(&definition, &source), "{source}");
        assert!(applied.is_empty(), "{source}: {applied:?}");
    }
}

/// The first equation applies where its list pattern matches outright.
#[test]
fn the_list_equation_applies_to_a_closed_list() {
    let definition = definition();
    let source = subject(
        "VarB:SortInt{}",
        "LblListItem{}(inj{SortInt{}, SortKItem{}}(VarB:SortInt{}))",
    );
    let (term, applied) = simplified(&definition, &source);
    assert_eq!(term, internal_term(&definition, r#"\dv{SortInt{}}("1")"#));
    assert_eq!(applied, ["f-second"]);
}
