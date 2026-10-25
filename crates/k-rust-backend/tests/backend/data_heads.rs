//! Data heads beyond overloads (KRUST-ANYWHERE-HEAD): an `anywhere` production that is not a
//! declared function, whose irreducible applications are elements (`value-production` or a
//! totality declaration), with no hook, lemma or ceil equation at its index, and whose equations
//! are executable (canonical where they carry `overload`). Its instance-normal applications over
//! data are data, and every data term exists ([`BackendDefinition::ground_defined`]).
//!
//! The fixture models SIMPLE's array lookup `_[_]` (`simple.md` 647 and 650): `idx(E, Is)` is
//! declared `anywhere, function, value-production`, as k-rust's compiler declares a non-function
//! production with `anywhere` rules, and roots two plain `anywhere` equations, `lookup`
//! (`idx(arr(L), [N]) = got(N)`, SIMPLE's `array(L, _)[N] => lookup(L +Int N)`) and `split`
//! (`idx(V:Val, [N1, N2 | Ns]) = idx(idx(V, [N1]), [N2 | Ns])`, SIMPLE's
//! `V:Val[N1, N2, Vs] => V[N1][N2, Vs]`). `Id` is not below `Val`, so an application whose
//! receiver is an `Id` (`a[4]`, a stored array access) matches neither.

use k_rust_backend::{
    data_term::Finding, definedness::application_owes_nothing, definition::BackendDefinition,
    term::Term,
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

const SOURCE: &str = r#"[]
module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol geInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.ge"), smt-hook{}(">=")]
    sort SortKItem{} []
    sort SortId{} []
    sort SortVal{} []
    sort SortExp{} []
    sort SortInts{} []
    hooked-sort SortMap{}
        [hook{}("MAP.Map"), unit{}(Lbl'Stop'Map{}()), element{}(Lbl'UndsPipe'-'-GT-Unds'{}()),
         concat{}(Lbl'Unds'Map'Unds'{}())]
    hooked-symbol Lbl'Stop'Map{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol Lbl'UndsPipe'-'-GT-Unds'{}(SortKItem{}, SortKItem{}) : SortMap{}
        [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol Lbl'Unds'Map'Unds'{}(SortMap{}, SortMap{}) : SortMap{}
        [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
    symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
    symbol a{}() : SortId{} [constructor{}(), functional{}()]
    symbol b{}() : SortId{} [constructor{}(), functional{}()]
    symbol arr{}(SortInt{}) : SortVal{} [constructor{}(), functional{}(), injective{}()]
    symbol got{}(SortInt{}) : SortExp{} [constructor{}(), functional{}(), injective{}()]
    symbol nil{}() : SortInts{} [constructor{}(), functional{}()]
    symbol ints{}(SortInt{}, SortInts{}) : SortInts{} [constructor{}(), functional{}(), injective{}()]
    symbol idx{}(SortExp{}, SortInts{}) : SortExp{} [anywhere{}(), function{}(), value-production{}()]
    axiom{R} \exists{R}(V:SortVal{}, \equals{SortVal{}, R}(V:SortVal{}, inj{SortInt{}, SortVal{}}(F:SortInt{})))
        [subsort{SortInt{}, SortVal{}}()]
    axiom{R} \exists{R}(V:SortExp{}, \equals{SortExp{}, R}(V:SortExp{}, inj{SortInt{}, SortExp{}}(F:SortInt{})))
        [subsort{SortInt{}, SortExp{}}()]
    axiom{R} \exists{R}(V:SortExp{}, \equals{SortExp{}, R}(V:SortExp{}, inj{SortVal{}, SortExp{}}(F:SortVal{})))
        [subsort{SortVal{}, SortExp{}}()]
    axiom{R} \exists{R}(V:SortExp{}, \equals{SortExp{}, R}(V:SortExp{}, inj{SortId{}, SortExp{}}(F:SortId{})))
        [subsort{SortId{}, SortExp{}}()]
    axiom{R} \exists{R}(V:SortKItem{}, \equals{SortKItem{}, R}(V:SortKItem{}, inj{SortExp{}, SortKItem{}}(F:SortExp{})))
        [subsort{SortExp{}, SortKItem{}}()]
    axiom{R} \exists{R}(V:SortKItem{}, \equals{SortKItem{}, R}(V:SortKItem{}, inj{SortId{}, SortKItem{}}(F:SortId{})))
        [subsort{SortId{}, SortKItem{}}()]
    axiom{R} \exists{R}(V:SortKItem{}, \equals{SortKItem{}, R}(V:SortKItem{}, inj{SortVal{}, SortKItem{}}(F:SortVal{})))
        [subsort{SortVal{}, SortKItem{}}()]
    axiom{R} \exists{R}(V:SortKItem{}, \equals{SortKItem{}, R}(V:SortKItem{}, inj{SortInt{}, SortKItem{}}(F:SortInt{})))
        [subsort{SortInt{}, SortKItem{}}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(),
            \and{R}(\in{SortExp{}, R}(X0:SortExp{}, inj{SortVal{}, SortExp{}}(arr{}(VarL:SortInt{}))),
            \and{R}(\in{SortInts{}, R}(X1:SortInts{}, ints{}(VarN:SortInt{}, nil{}())), \top{R}()))),
        \equals{SortExp{}, R}(idx{}(X0:SortExp{}, X1:SortInts{}),
            \and{SortExp{}}(got{}(VarN:SortInt{}), \top{SortExp{}}())))
        [label{}("lookup"), anywhere{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(),
            \and{R}(\in{SortExp{}, R}(X0:SortExp{}, inj{SortVal{}, SortExp{}}(VarV:SortVal{})),
            \and{R}(\in{SortInts{}, R}(X1:SortInts{},
                ints{}(VarN1:SortInt{}, ints{}(VarN2:SortInt{}, VarNs:SortInts{}))), \top{R}()))),
        \equals{SortExp{}, R}(idx{}(X0:SortExp{}, X1:SortInts{}),
            \and{SortExp{}}(
                idx{}(idx{}(inj{SortVal{}, SortExp{}}(VarV:SortVal{}), ints{}(VarN1:SortInt{}, nil{}())),
                    ints{}(VarN2:SortInt{}, VarNs:SortInts{})),
                \top{SortExp{}}())))
        [label{}("split"), anywhere{}()]
endmodule []"#;

const IDX: &str = "symbol idx{}(SortExp{}, SortInts{}) : SortExp{} [anywhere{}(), function{}(), value-production{}()]";

fn internalize(source: &str) -> BackendDefinition {
    let syntax = parse_definition(source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

/// The fixture with `extra` sentences added before `endmodule`.
fn with_sentences(extra: &str) -> BackendDefinition {
    internalize(&SOURCE.replace("endmodule []", &format!("{extra}\nendmodule []")))
}

/// The fixture with `idx` declared by `declaration` instead.
fn with_idx(declaration: &str) -> BackendDefinition {
    internalize(&SOURCE.replace(IDX, declaration))
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    let syntax = parse_pattern(source).expect("term should parse");
    definition
        .admit_unverified(&syntax, &[])
        .internalize_term()
        .expect("term should internalize")
}

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// The index list `[n1, ..., nk]`.
fn indices(values: &[i64]) -> String {
    values
        .iter()
        .rev()
        .fold("nil{}()".to_owned(), |rest, value| {
            format!("ints{{}}({}, {rest})", int(*value))
        })
}

/// `receiver[indices]`, the receiver an `Exp`.
fn at(receiver: &str, values: &[i64]) -> String {
    format!("idx{{}}({receiver}, {})", indices(values))
}

const A: &str = "inj{SortId{}, SortExp{}}(a{}())";
const B: &str = "inj{SortId{}, SortExp{}}(b{}())";

fn array(base: i64) -> String {
    format!("inj{{SortVal{{}}, SortExp{{}}}}(arr{{}}({}))", int(base))
}

fn heads(definition: &BackendDefinition) -> Vec<String> {
    definition
        .data_heads()
        .names()
        .map(ToString::to_string)
        .collect()
}

/// Whether `source` is data in `definition` (with its own heads) and whether it is shown to exist.
fn judged(definition: &BackendDefinition, source: &str) -> (bool, bool) {
    let term = term(definition, source);
    let data = definition.is_data(&term, &definition.data_heads());
    let defined = definition.ground_defined(&term);
    // Data implies existence for every term of this file (no map keys of several shapes).
    assert!(!data || defined, "data but not shown defined: {source}");
    (data, defined)
}

#[test]
fn a_plain_value_production_anywhere_head_is_a_data_head() {
    let definition = internalize(SOURCE);
    let heads = definition.data_heads();
    assert!(heads.confluent(), "{:?}", heads.findings());
    assert_eq!(self::heads(&definition), ["idx"]);
}

/// `a[4]` and `a[3, 4]`: no equation of `idx` matches an `Id` receiver, so both are normal forms
/// in every context, and `value-production` makes them elements.
#[test]
fn an_application_no_equation_matches_is_data_and_exists() {
    let definition = internalize(SOURCE);
    for source in [at(A, &[4]), at(A, &[3, 4])] {
        assert_eq!(judged(&definition, &source), (true, true), "{source}");
    }
    // The stored `ceil_free` attribute, which does not read the definition, refuses it.
    assert!(!term(&definition, &at(A, &[4])).attributes().ceil_free());
}

/// `arr(1)[4]` is reducible (`lookup`), and so is `5[3, 4]` (`split`, with `Int` below `Val`): not
/// data, and not shown to exist (`value-production` covers only applications no equation reduces).
#[test]
fn an_application_an_equation_matches_is_neither_data_nor_shown_defined() {
    let definition = internalize(SOURCE);
    for source in [
        at(&array(1), &[4]),
        at(
            &format!("inj{{SortInt{{}}, SortExp{{}}}}({})", int(5)),
            &[3, 4],
        ),
    ] {
        assert_eq!(judged(&definition, &source), (false, false), "{source}");
    }
}

/// `a[3][4]` nests a data application as the receiver of another, which no equation matches:
/// data. `arr(1)[0][4]` holds the reducible `arr(1)[0]`: not data, and not defined.
#[test]
fn nested_applications_are_judged_at_every_node() {
    let definition = internalize(SOURCE);
    assert_eq!(judged(&definition, &at(&at(A, &[3]), &[4])), (true, true));
    assert_eq!(
        judged(&definition, &at(&at(&array(1), &[0]), &[4])),
        (false, false)
    );
}

/// An `owise` equation applies wherever nothing higher does, so it counts as applying wherever
/// its left-hand side matches: the head stays a data head, but none of its applications is data.
#[test]
fn a_head_with_an_owise_equation_has_no_data_application() {
    let definition = with_sentences(
        r#"
    axiom{R} \implies{R}(
        \and{R}(\top{R}(),
            \and{R}(\in{SortExp{}, R}(X0:SortExp{}, VarE:SortExp{}),
            \and{R}(\in{SortInts{}, R}(X1:SortInts{}, VarIs:SortInts{}), \top{R}()))),
        \equals{SortExp{}, R}(idx{}(X0:SortExp{}, X1:SortInts{}),
            \and{SortExp{}}(got{}(\dv{SortInt{}}("0")), \top{SortExp{}}())))
        [label{}("default"), anywhere{}(), owise{}()]
"#,
    );
    assert_eq!(heads(&definition), ["idx"]);
    assert!(!judged(&definition, &at(A, &[4])).0);
}

/// A conditional equation whose left-hand side matches `a[4]` withholds data, though its
/// `requires` (`N >= 10`) is false there: the scan ignores `requires`, which only loses
/// precision. The application is not shown to exist either (the evaluator's own definedness
/// discharges only applications no equation reaches).
#[test]
fn a_head_whose_conditional_equation_matches_withholds_data() {
    let definition = with_sentences(
        r#"
    axiom{R} \implies{R}(
        \and{R}(\equals{SortBool{}, R}(geInt{}(VarN:SortInt{}, \dv{SortInt{}}("10")), \dv{SortBool{}}("true")),
            \and{R}(\in{SortExp{}, R}(X0:SortExp{}, inj{SortId{}, SortExp{}}(VarX:SortId{})),
            \and{R}(\in{SortInts{}, R}(X1:SortInts{}, ints{}(VarN:SortInt{}, nil{}())), \top{R}()))),
        \equals{SortExp{}, R}(idx{}(X0:SortExp{}, X1:SortInts{}),
            \and{SortExp{}}(got{}(VarN:SortInt{}), \top{SortExp{}}())))
        [label{}("guarded"), anywhere{}()]
"#,
    );
    assert_eq!(heads(&definition), ["idx"]);
    assert_eq!(judged(&definition, &at(A, &[4])), (false, false));
    // `a[3, 4]` has two indices, which `guarded` does not match.
    assert_eq!(judged(&definition, &at(A, &[3, 4])), (true, true));
}

/// H1 and H2. A declared function with `anywhere` rules (`function` without `value-production`)
/// is a function, and an `anywhere` head with neither a totality declaration nor
/// `value-production` claims nothing about its irreducible applications: neither is a data head,
/// and `a[4]` is neither data nor shown to exist. An `anywhere` head declared `functional` is a
/// data head, and `a[4]` is data and exists through the totality declaration.
#[test]
fn only_heads_whose_irreducible_applications_are_elements_are_data_heads() {
    for declaration in [
        "symbol idx{}(SortExp{}, SortInts{}) : SortExp{} [anywhere{}(), function{}()]",
        "symbol idx{}(SortExp{}, SortInts{}) : SortExp{} [anywhere{}()]",
    ] {
        let definition = with_idx(declaration);
        assert!(heads(&definition).is_empty(), "{declaration}");
        assert_eq!(
            judged(&definition, &at(A, &[4])),
            (false, false),
            "{declaration}"
        );
    }
    let total =
        with_idx("symbol idx{}(SortExp{}, SortInts{}) : SortExp{} [anywhere{}(), functional{}()]");
    assert_eq!(heads(&total), ["idx"]);
    assert_eq!(judged(&total, &at(A, &[4])), (true, true));
}

/// H3. A hooked head, and a head with a `simplification` lemma at its index, are no data heads.
#[test]
fn a_hooked_head_or_one_with_a_lemma_is_not_a_data_head() {
    let hooked = internalize(&SOURCE.replace(
        IDX,
        r#"hooked-symbol idx{}(SortExp{}, SortInts{}) : SortExp{} [anywhere{}(), function{}(), value-production{}(), hook{}("ARRAY.idx")]"#,
    ));
    assert!(heads(&hooked).is_empty());
    assert!(!judged(&hooked, &at(A, &[4])).0);
    let lemma = with_sentences(
        r#"
    axiom{R} \implies{R}(
        \top{R}(),
        \equals{SortExp{}, R}(idx{}(inj{SortId{}, SortExp{}}(b{}()), VarIs:SortInts{}),
            \and{SortExp{}}(got{}(\dv{SortInt{}}("0")), \top{SortExp{}}())))
        [label{}("lemma"), simplification{}()]
"#,
    );
    assert!(heads(&lemma).is_empty());
    assert!(!judged(&lemma, &at(A, &[4])).0);
}

/// S1: a ceil lemma at the head's index (`\ceil(idx(E, [N | Ns])) = N >= 0`) states the
/// existence of its applications, which the definedness walk honours before
/// `value-production`. The head is no data head, and `a[-1]`, which the lemma makes `\bottom`, is
/// not shown to exist; `a[4]`, where the lemma's condition holds, is.
#[test]
fn a_head_with_a_ceil_lemma_is_not_a_data_head_and_existence_reads_the_lemma() {
    let definition = with_sentences(
        r#"
    axiom{R} \implies{R}(\top{R}(), \equals{R, R}(
        \ceil{SortExp{}, R}(idx{}(VarE:SortExp{}, ints{}(VarN:SortInt{}, VarNs:SortInts{}))),
        \and{R}(
            \equals{SortBool{}, R}(geInt{}(VarN:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")),
            \top{R}())))
        [label{}("ceil-idx"), simplification{}()]
"#,
    );
    assert!(heads(&definition).is_empty());
    assert_eq!(judged(&definition, &at(A, &[-1])), (false, false));
    assert_eq!(judged(&definition, &at(A, &[4])), (false, true));
}

/// S2: existence is the definedness walk, so a map whose value holds `a[4]` exists, while a map
/// with the key `a[4]` beside another key owes their disequality unless k-rust shows the two
/// apart. Its apartness test does not separate an application of an equation head from another
/// key (`b[4]`, `a[5]`, a constructor `got(1)`, or an `Id` under another injection), so each such
/// map is data (its keys are distinct normal forms of `M+`) but is not shown to exist: in another
/// model two of its keys may be equal. This is the known direction (review M2) in which data
/// does not imply `ground_defined`.
#[test]
fn existence_reads_map_values_and_requires_keys_shown_apart() {
    let definition = internalize(SOURCE);
    let kitem = |exp: &str| format!("inj{{SortExp{{}}, SortKItem{{}}}}({exp})");
    let entry = |key: &str, value: &str| format!("Lbl'UndsPipe'-'-GT-Unds'{{}}({key}, {value})");
    let map = |left: String, right: String| format!("Lbl'Unds'Map'Unds'{{}}({left}, {right})");
    let id = |name: &str| format!("inj{{SortId{{}}, SortKItem{{}}}}({name}{{}}())");
    let value = map(
        entry(&id("a"), &kitem(&at(A, &[4]))),
        entry(&id("b"), &kitem(&at(B, &[4]))),
    );
    assert_eq!(judged(&definition, &value), (true, true));
    let keys = map(
        entry(&kitem(&at(A, &[4])), &id("a")),
        entry(&kitem(&at(B, &[4])), &id("b")),
    );
    let keys = term(&definition, &keys);
    assert!(definition.is_data(&keys, &definition.data_heads()));
    assert!(!definition.ground_defined(&keys));
    for (left, right) in [
        (kitem(&at(A, &[4])), id("b")),
        (kitem(&at(A, &[4])), kitem(&format!("got{{}}({})", int(1)))),
        (kitem(&at(A, &[4])), kitem(&at(A, &[5]))),
    ] {
        let keys = term(
            &definition,
            &map(entry(&left, &id("a")), entry(&right, &id("b"))),
        );
        assert!(
            definition.is_data(&keys, &definition.data_heads()),
            "{right}"
        );
        assert!(!definition.ground_defined(&keys), "{right}");
    }
}

/// `application_owes_nothing` names the node a term is not shown defined by: `a[4]` owes
/// nothing beyond its arguments, `arr(1)[4]` owes its `\ceil`.
#[test]
fn the_witness_of_a_refusal_is_the_first_application_that_owes() {
    let definition = internalize(SOURCE);
    assert!(application_owes_nothing(
        &definition,
        &term(&definition, &at(A, &[4]))
    ));
    assert!(!application_owes_nothing(
        &definition,
        &term(&definition, &at(&array(1), &[4]))
    ));
}

/// M5: two equations of a plain head with different results at an overlap (`g(X) = a`,
/// `g(c) = b`) are a pair the full check does not join, so the definition has no data. Assuming
/// the pair joined reads the definition as if it did; the load's own check withdraws the claims
/// its taint reaches, and `g` stays no data head under the assumption: an assumed pair can only
/// make fewer terms data.
#[test]
fn an_assumed_pair_of_a_plain_heads_equations_leaves_the_head_withdrawn() {
    let definition = internalize(
        r#"[]
module MAIN
    sort SortS{} []
    symbol c{}() : SortS{} [constructor{}(), functional{}()]
    symbol d{}() : SortS{} [constructor{}(), functional{}()]
    symbol ra{}() : SortS{} [constructor{}(), functional{}()]
    symbol rb{}() : SortS{} [constructor{}(), functional{}()]
    symbol g{}(SortS{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortS{}, R}(X0:SortS{}, VarX:SortS{}), \top{R}())),
        \equals{SortS{}, R}(g{}(X0:SortS{}), \and{SortS{}}(ra{}(), \top{SortS{}}())))
        [label{}("any"), anywhere{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortS{}, R}(X0:SortS{}, c{}()), \top{R}())),
        \equals{SortS{}, R}(g{}(X0:SortS{}), \and{SortS{}}(rb{}(), \top{SortS{}}())))
        [label{}("at-c"), anywhere{}()]
endmodule []"#,
    );
    let heads = definition.data_heads();
    assert!(!heads.confluent());
    assert!(
        heads
            .findings()
            .iter()
            .any(|finding| matches!(finding, Finding::Pair { .. })),
        "{:?}",
        heads.findings()
    );
    let assumed = definition.data_heads_assuming(&heads, |finding| finding.pair().is_some());
    assert!(assumed.confluent(), "{:?}", assumed.findings());
    assert_eq!(
        assumed.names().map(ToString::to_string).collect::<Vec<_>>(),
        Vec::<String>::new()
    );
}
