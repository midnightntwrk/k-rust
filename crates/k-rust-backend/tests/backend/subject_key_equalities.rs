//! A left-hand side that binds a variable and reads it again as a map key matches a subject map
//! whose key is another symbolic term exactly where the two keys are equal, also when the entry's
//! value reads the variable once more. An `owise` equation's premise negates that left-hand side,
//! so the `owise` equation applies where the path condition refutes every such key equality, and
//! only there: where one may hold, the application stays unevaluated, and a map with a frame may
//! hold the key in the frame.

#![cfg(feature = "z3")]

use k_rust_backend::{
    definition::BackendDefinition, rule::Predicate, simplify::SimplificationOptions, smt::Z3Solver,
    term::Term,
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::support::{internal_term, unstopped::simplify_with_solver};

/// `look(K, M)` is the amount of the record `M` holds at `K`, else 0 (`owise`); `lookv(K, M)`
/// likewise, reading only a record that names `K` again, as an account cell holds its own
/// identifier; `lookc(K, M)` is the amount `M` holds at `cat(K, 0)`, where `cat` is a commutative
/// function without equations, so `cat(K, 0)` may equal `cat(B, 0)` for a `K` other than `B`;
/// `h` is a function without equations.
fn definition() -> BackendDefinition {
    let lookup = |head: &str, key: &str, value: &str| {
        format!(
            r#"
            axiom{{R}} \implies{{R}}(
                \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortInt{{}}, R}}(X0:SortInt{{}}, VarK:SortInt{{}}),
                    \and{{R}}(\in{{SortMap{{}}, R}}(X1:SortMap{{}},
                        mapConcat{{}}(mapItem{{}}({key}, {value}), VarM:SortMap{{}})), \top{{R}}()))),
                \equals{{SortInt{{}}, R}}({head}{{}}(X0:SortInt{{}}, X1:SortMap{{}}),
                    \and{{SortInt{{}}}}(VarV:SortInt{{}}, \top{{SortInt{{}}}}()))
            ) [label{{}}("{head}-found")]
            axiom{{R}} \implies{{R}}(
                \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortInt{{}}, R}}(X0:SortInt{{}}, VarJ:SortInt{{}}),
                    \and{{R}}(\in{{SortMap{{}}, R}}(X1:SortMap{{}}, VarN:SortMap{{}}), \top{{R}}()))),
                \equals{{SortInt{{}}, R}}({head}{{}}(X0:SortInt{{}}, X1:SortMap{{}}),
                    \and{{SortInt{{}}}}(\dv{{SortInt{{}}}}("0"), \top{{SortInt{{}}}}()))
            ) [label{{}}("{head}-absent"), owise{{}}()]
            "#
        )
    };
    let source = format!(
        r#"[] module MAIN
            hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            hooked-sort SortMap{{}}
                [hook{{}}("MAP.Map"), unit{{}}(mapUnit{{}}()), element{{}}(mapItem{{}}()), concat{{}}(mapConcat{{}}())]
            hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.eq"), smt-hook{{}}("=")]
            hooked-symbol mapUnit{{}}() : SortMap{{}} [function{{}}(), total{{}}(), hook{{}}("MAP.unit")]
            sort SortVal{{}} []
            symbol val{{}}(SortInt{{}}, SortInt{{}}) : SortVal{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            hooked-symbol mapItem{{}}(SortInt{{}}, SortVal{{}}) : SortMap{{}}
                [function{{}}(), total{{}}(), hook{{}}("MAP.element")]
            hooked-symbol mapConcat{{}}(SortMap{{}}, SortMap{{}}) : SortMap{{}}
                [function{{}}(), hook{{}}("MAP.concat"), assoc{{}}(), comm{{}}()]
            symbol cat{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}(), comm{{}}()]
            symbol look{{}}(SortInt{{}}, SortMap{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            symbol lookv{{}}(SortInt{{}}, SortMap{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            symbol lookc{{}}(SortInt{{}}, SortMap{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            symbol h{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            {}
            {}
            {}
        endmodule []"#,
        lookup(
            "look",
            "VarK:SortInt{}",
            "val{}(VarW:SortInt{}, VarV:SortInt{})"
        ),
        lookup(
            "lookv",
            "VarK:SortInt{}",
            "val{}(VarK:SortInt{}, VarV:SortInt{})"
        ),
        lookup(
            "lookc",
            r#"cat{}(VarK:SortInt{}, \dv{SortInt{}}("0"))"#,
            "val{}(VarW:SortInt{}, VarV:SortInt{})"
        ),
    );
    let syntax = parse_definition(&source).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// The map of `entries`, each a key and an amount, holding at each key the record of that key and
/// amount, and `frame` as its rest.
fn map(entries: &[(&str, String)], frame: Option<&str>) -> String {
    entries
        .iter()
        .map(|(key, amount)| format!("mapItem{{}}({key}, val{{}}({key}, {amount}))"))
        .chain(frame.map(str::to_owned))
        .reduce(|left, right| format!("mapConcat{{}}({left}, {right})"))
        .unwrap_or_else(|| "mapUnit{}()".to_owned())
}

/// The path condition that the Int variables `left` and `right` differ.
fn differ(definition: &BackendDefinition, left: &str, right: &str) -> Predicate {
    let syntax = parse_pattern(&format!(
        r#"\equals{{SortBool{{}}, SortInt{{}}}}(eqInt{{}}(Var{left}:SortInt{{}}, Var{right}:SortInt{{}}), \dv{{SortBool{{}}}}("false"))"#
    ))
    .expect("the path condition parses");
    definition
        .admit_unverified(&syntax, &[])
        .internalize_predicate()
        .expect("the path condition internalizes")
        .0
}

/// `source` simplified under the path condition `known`: the result and the equations applied.
fn simplified(
    definition: &BackendDefinition,
    source: &str,
    known: &[Predicate],
) -> (Term, Vec<String>) {
    let solver = Z3Solver::new(definition).unwrap();
    let result = simplify_with_solver(
        definition,
        &internal_term(definition, source),
        known,
        SimplificationOptions::default(),
        &solver,
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    (result.term, result.applied_rules.to_vec())
}

/// `source` stays unevaluated under `known`.
fn assert_kept(definition: &BackendDefinition, source: &str, known: &[Predicate]) {
    let (term, applied) = simplified(definition, source, known);
    assert_eq!(term, internal_term(definition, source), "{source}");
    assert!(applied.is_empty(), "{source}: {applied:?}");
}

/// `source` evaluates to `expected` by the equation labelled `rule` under `known`.
fn assert_evaluates(
    definition: &BackendDefinition,
    source: &str,
    known: &[Predicate],
    expected: &str,
    rule: &str,
) {
    let (term, applied) = simplified(definition, source, known);
    assert_eq!(term, internal_term(definition, expected), "{source}");
    assert_eq!(applied, [rule], "{source}");
}

/// One record under the symbolic key `B`: `look(A, B |-> val(B, 7))` is 7 where `A = B` and 0
/// elsewhere. With nothing known it stays; under `A =/= B` the `owise` equation applies.
#[test]
fn an_owise_equation_applies_where_the_one_key_a_match_needs_is_refuted() {
    let definition = definition();
    for head in ["look", "lookv"] {
        let subject = format!(
            "{head}{{}}(VarA:SortInt{{}}, {})",
            map(&[("VarB:SortInt{}", int(7))], None)
        );
        assert_kept(&definition, &subject, &[]);
        assert_evaluates(
            &definition,
            &subject,
            &[differ(&definition, "A", "B")],
            &int(0),
            &format!("{head}-absent"),
        );
    }
}

/// Two records under the symbolic keys `B1` and `B2`: the first equation has one instance per
/// key, each matching where `A` equals that key, also when the record names the key again
/// (`lookv`). With nothing known, or with only `A =/= B1`, one instance may match and the
/// application stays; with both disequalities the `owise` equation applies.
#[test]
fn an_owise_equation_applies_only_where_every_key_a_match_needs_is_refuted() {
    let definition = definition();
    for head in ["lookv", "look"] {
        let subject = format!(
            "{head}{{}}(VarA:SortInt{{}}, {})",
            map(
                &[("VarB1:SortInt{}", int(7)), ("VarB2:SortInt{}", int(8))],
                None
            )
        );
        assert_kept(&definition, &subject, &[]);
        assert_kept(&definition, &subject, &[differ(&definition, "A", "B1")]);
        assert_evaluates(
            &definition,
            &subject,
            &[
                differ(&definition, "A", "B1"),
                differ(&definition, "A", "B2"),
            ],
            &int(0),
            &format!("{head}-absent"),
        );
    }
}

/// A map with a frame may hold `A` in the frame, which no key disequality refutes.
#[test]
fn a_map_frame_keeps_the_application_whatever_the_keys() {
    let definition = definition();
    for head in ["look", "lookv"] {
        let subject = format!(
            "{head}{{}}(VarA:SortInt{{}}, {})",
            map(&[("VarB:SortInt{}", int(7))], Some("VarF:SortMap{}"))
        );
        assert_kept(&definition, &subject, &[differ(&definition, "A", "B")]);
    }
}

/// The key `cat(A, 0)` against the subject's `cat(B, 0)`: `cat` is commutative and has no
/// equations, so the two may be equal although `A =/= B`; binding `A` to `B` only suffices for
/// the match, and refuting `A = B` does not refute it. The application stays.
#[test]
fn a_key_under_an_algebraic_function_is_not_refuted_by_its_arguments() {
    let definition = definition();
    let subject = format!(
        "lookc{{}}(VarA:SortInt{{}}, {})",
        map(
            &[(&format!("cat{{}}(VarB:SortInt{{}}, {})", int(0)), int(7))],
            None
        )
    );
    assert_kept(&definition, &subject, &[differ(&definition, "A", "B")]);
}

/// Controls: a key the subject holds syntactically, and ground keys, decide the match without
/// the path condition.
#[test]
fn equal_and_ground_keys_decide_the_match() {
    let definition = definition();
    for head in ["look", "lookv"] {
        assert_evaluates(
            &definition,
            &format!(
                "{head}{{}}(VarA:SortInt{{}}, {})",
                map(&[("VarA:SortInt{}", int(7))], None)
            ),
            &[],
            &int(7),
            &format!("{head}-found"),
        );
        assert_evaluates(
            &definition,
            &format!(
                "{head}{{}}({}, {})",
                int(1),
                map(&[(&int(2), int(7))], None)
            ),
            &[],
            &int(0),
            &format!("{head}-absent"),
        );
        assert_evaluates(
            &definition,
            &format!(
                "{head}{{}}({}, {})",
                int(2),
                map(&[(&int(2), int(7))], None)
            ),
            &[],
            &int(7),
            &format!("{head}-found"),
        );
    }
}

/// A record whose value names its own key under a function (`val(h(B), 8)` at `B`) matches
/// `lookv(A, ..)` only where `A` equals `B` and `h(B)` equals `B`; the second equality is not
/// one the path condition decides, so the application is kept, alone and beside a refuted
/// sibling record.
#[test]
fn a_record_naming_its_key_under_a_function_keeps_the_application() {
    let definition = definition();
    let subject = format!(
        "lookv{{}}(VarA:SortInt{{}}, mapItem{{}}(VarB:SortInt{{}}, val{{}}(h{{}}(VarB:SortInt{{}}), {})))",
        int(8)
    );
    assert_kept(&definition, &subject, &[]);
    let subject = format!(
        "lookv{{}}(VarA:SortInt{{}}, mapConcat{{}}(mapItem{{}}(VarB:SortInt{{}}, val{{}}(h{{}}(VarB:SortInt{{}}), {})), mapItem{{}}(VarC:SortInt{{}}, val{{}}(VarC:SortInt{{}}, {}))))",
        int(8),
        int(9)
    );
    assert_kept(&definition, &subject, &[differ(&definition, "A", "C")]);
}
