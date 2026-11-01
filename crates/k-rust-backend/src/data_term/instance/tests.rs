//! The ground-instance search's readings of stuck applications (S2B-T3), on FUN's overloaded
//! list fixture (`tests/fixtures/overloaded-list-owise.kore`, as `tests/backend/data_terms.rs`
//! reads it): which side holds what, and the defect switch `stuck_partial_is_value`. Also the
//! search's decline on an equation holding an open literal (GAP K3), on small definitions over
//! the hooked `Int` and `Float`.

use k_rust_kore::kore::parser::parse_definition;

use super::Stuck;
use crate::{
    confluence::switches::{self, Switches},
    data_term::Finding,
    definition::BackendDefinition,
};

const FIXTURE: &str = include_str!("../../../tests/fixtures/overloaded-list-owise.kore");

/// The fixture with `extra` sentences added to its module.
fn with_sentences(extra: &str) -> BackendDefinition {
    let (head, tail) = FIXTURE
        .rsplit_once("endmodule")
        .expect("the fixture has one module");
    let syntax = parse_definition(&format!("{head}\n{extra}\nendmodule{tail}"))
        .expect("fixture should parse");
    BackendDefinition::internalize(&syntax, "OVERLOADED-LIST-OWISE")
        .expect("fixture should internalize")
}

/// `HEAD(X0) = RHS` over `X0:SortVal` bound to `V`, of sort `SORT`.
fn equation(head: &str, sort: &str, rhs: &str, label: &str) -> String {
    format!(
        r#"
    axiom{{R}} \implies{{R}}(
        \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortVal{{}}, R}}(X0:SortVal{{}}, V:SortVal{{}}), \top{{R}}())),
        \equals{{{sort}, R}}({head}{{}}(X0:SortVal{{}}), \and{{{sort}}}({rhs}, \top{{{sort}}}())))
        [label{{}}("{label}")]
"#
    )
}

/// The one pair finding of `definition` whose description names `label`.
fn pair_finding(definition: &BackendDefinition, label: &str) -> Finding {
    let heads = definition.data_heads();
    let found = heads
        .findings()
        .iter()
        .filter(|finding| finding.pair().is_some() && finding.to_string().contains(label))
        .cloned()
        .collect::<Vec<_>>();
    let [finding] = &found[..] else {
        panic!("one pair finding naming {label}: {:?}", heads.findings());
    };
    finding.clone()
}

/// Which sides hold a stuck application, sorted (the order of the sides is the pair's).
fn stuck_sides(finding: &Finding) -> Vec<Option<Stuck>> {
    let instance = finding.instance().expect("a genuine finding");
    let mut sides = vec![instance.stuck.0, instance.stuck.1];
    sides.sort();
    sides
}

/// `p(V) = one` beside `p(V) = cap(V)`, `cap` total without an equation: one side is data, the
/// other holds a stuck total application.
#[test]
fn a_stuck_total_side_is_marked_total() {
    let definition = with_sentences(&format!(
        "    symbol cap{{}}(SortVal{{}}) : SortVal{{}} [function{{}}(), total{{}}()]
    symbol p{{}}(SortVal{{}}) : SortVal{{}} [function{{}}(), total{{}}()]\n{}{}",
        equation("p", "SortVal{}", "one{}()", "p-one"),
        equation("p", "SortVal{}", "cap{}(V:SortVal{})", "p-cap"),
    ));
    let finding = pair_finding(&definition, "p-one");
    assert_eq!(stuck_sides(&finding), [None, Some(Stuck::Total)]);
}

/// `s(V) = failed` beside `s(V) = bound(nb(V))`, `nb` partial without an equation: one side is
/// data, the other undefined.
#[test]
fn a_stuck_partial_side_is_marked_partial() {
    let definition = with_sentences(&format!(
        "    symbol nb{{}}(SortVal{{}}) : SortVal{{}} [function{{}}()]
    symbol s{{}}(SortVal{{}}) : SortState{{}} [function{{}}(), total{{}}()]\n{}{}",
        equation("s", "SortState{}", "failed{}()", "s-failed"),
        equation("s", "SortState{}", "bound{}(nb{}(V:SortVal{}))", "s-nb"),
    ));
    let finding = pair_finding(&definition, "s-failed");
    assert_eq!(stuck_sides(&finding), [None, Some(Stuck::Partial)]);
}

/// V7: `f(V) = g(V)` beside `f(V) = h(V)`, with `g` and `h` partial and equation-free but for
/// one agreeing equation each at `listVal(_)`, stays undecided: both reducts are undefined at
/// `f(one)`. Reading a stuck partial application as a value, `stuck_partial_is_value` labels the
/// pair genuine there, which this test sees.
#[test]
fn reading_a_stuck_partial_application_as_a_value_is_caught() {
    let definition = || {
        with_sentences(&format!(
            r#"
    symbol g{{}}(SortVal{{}}) : SortVal{{}} [function{{}}()]
    symbol h{{}}(SortVal{{}}) : SortVal{{}} [function{{}}()]
    symbol f{{}}(SortVal{{}}) : SortVal{{}} [function{{}}(), total{{}}()]
    axiom{{R}} \implies{{R}}(
        \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortVal{{}}, R}}(X0:SortVal{{}}, listVal{{}}(Vs:SortVals{{}})), \top{{R}}())),
        \equals{{SortVal{{}}, R}}(g{{}}(X0:SortVal{{}}), \and{{SortVal{{}}}}(one{{}}(), \top{{SortVal{{}}}}())))
        [label{{}}("g-list")]
    axiom{{R}} \implies{{R}}(
        \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortVal{{}}, R}}(X0:SortVal{{}}, listVal{{}}(Vs:SortVals{{}})), \top{{R}}())),
        \equals{{SortVal{{}}, R}}(h{{}}(X0:SortVal{{}}), \and{{SortVal{{}}}}(one{{}}(), \top{{SortVal{{}}}}())))
        [label{{}}("h-list")]
{}{}"#,
            equation("f", "SortVal{}", "g{}(V:SortVal{})", "f-g"),
            equation("f", "SortVal{}", "h{}(V:SortVal{})", "f-h"),
        ))
    };
    assert!(!pair_finding(&definition(), "f-g").is_genuine());
    let switched = switches::with(
        Switches {
            stuck_partial_is_value: true,
            ..Switches::default()
        },
        || pair_finding(&definition(), "f-g"),
    );
    assert_eq!(
        stuck_sides(&switched),
        [Some(Stuck::Total), Some(Stuck::Total)]
    );
}

/// A definition over the hooked `Bool`, `Int`, `Float` and `MInt{8}` with `_==Int_`, `_==Float_`
/// and `_==MInt_`, of `symbols` and `axioms` (written as KORE, without escaping).
fn with_builtins(symbols: &str, axioms: &str) -> BackendDefinition {
    let source = format!(
        r#"[] module MAIN
    hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
    hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
    hooked-sort SortFloat{{}} [hook{{}}("FLOAT.Float"), hasDomainValues{{}}()]
    hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}} [function{{}}(), total{{}}(), hook{{}}("INT.eq")]
    hooked-symbol eqFloat{{}}(SortFloat{{}}, SortFloat{{}}) : SortBool{{}} [function{{}}(), hook{{}}("FLOAT.eq")]
    hooked-sort SortMInt{{S}} [hook{{}}("MINT.MInt"), hasDomainValues{{}}()]
    sort Sort8{{}} []
    hooked-symbol eqMInt{{}}(SortMInt{{Sort8{{}}}}, SortMInt{{Sort8{{}}}}) : SortBool{{}} [function{{}}(), total{{}}(), hook{{}}("MINT.eq")]
{symbols}
{axioms}
endmodule []"#
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

/// `HEAD(X0) = RHS` over `X0:SortInt` bound to `_`, guarded by `requires` (a `\top{R}()` or an
/// `\equals` predicate), with the attributes `attributes`.
fn int_equation(head: &str, requires: &str, rhs: &str, attributes: &str) -> String {
    format!(
        r#"    axiom{{R}} \implies{{R}}(
        \and{{R}}({requires}, \and{{R}}(\in{{SortInt{{}}, R}}(X0:SortInt{{}}, Any:SortInt{{}}), \top{{R}}())),
        \equals{{SortInt{{}}, R}}({head}{{}}(X0:SortInt{{}}), \and{{SortInt{{}}}}({rhs}, \top{{SortInt{{}}}}())))
        [{attributes}]
"#
    )
}

/// `\dv{SortInt{}}(value)`.
fn int(value: &str) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// The 8-bit machine integer `255p8`, the element `256p8` names in one model of the literal rules
/// (k-rust's is the residue, `0p8`).
const NEAR: &str = "255p8";

/// The largest finite double. GAP A2: `1.0e400` names the infinity in every model (AM-8), so a
/// sentence holding it decides as one holding a determined literal does.
const MAX: &str = "1.7976931348623157e308";

/// `\dv{SORT}(value)` for the sort of `NEAR` (`SortMInt{Sort8{}}`) or of `MAX` (`SortFloat{}`).
fn literal(sort: &str, value: &str) -> String {
    format!(r#"\dv{{{sort}}}("{value}")"#)
}

const MINT: &str = "SortMInt{Sort8{}}";
const FLOAT: &str = "SortFloat{}";
/// d0/d1 (GAP K3 fix round 2): `f(_) = 2 requires GUARD [priority(10)]` above `f(_) = 0` and
/// `f(_) = 1`, `f` total. The search reads the lower pair as genuine only where the higher
/// equation is decided not to apply at the witness.
fn guarded(guard: &str) -> BackendDefinition {
    let requires = format!(r#"\equals{{SortBool{{}}, R}}({guard}, \dv{{SortBool{{}}}}("true"))"#);
    with_builtins(
        r#"    symbol f{}(SortInt{}) : SortInt{} [function{}(), total{}()]"#,
        &[
            int_equation(
                "f",
                &requires,
                &int("2"),
                r#"label{}("f-two"), priority{}("10")"#,
            ),
            int_equation("f", r"\top{R}()", &int("0"), r#"label{}("f-zero")"#),
            int_equation("f", r"\top{R}()", &int("1"), r#"label{}("f-one")"#),
        ]
        .concat(),
    )
}

/// d0: with the determined guard `1 ==Int 2`, false in every model, the priority-10 equation
/// never applies, and `f(0)` reduces to `0` and to `1`: the pair is genuine.
#[test]
fn a_determined_false_guard_leaves_the_lower_pair_genuine() {
    let definition = guarded(&format!("eqInt{{}}({}, {})", int("1"), int("2")));
    assert!(pair_finding(&definition, "f-zero").is_genuine());
}

/// d1: with the guard `256p8 ==MInt 255p8`, true in the model where the literal's element is
/// `255p8`, the priority-10 equation then always applies and the pair never fires. The search
/// does not decide the guard on k-rust's element (`0p8`), so the pair is undecided, not genuine.
/// GAP A2: with `1.0e400 ==Float MAX` the guard is false in every model, as d0's is.
#[test]
fn a_guard_holding_an_open_literal_leaves_the_lower_pair_undecided() {
    let definition = guarded(&format!(
        "eqMInt{{}}({}, {})",
        literal(MINT, "256p8"),
        literal(MINT, NEAR)
    ));
    let finding = pair_finding(&definition, "f-zero");
    assert!(!finding.is_genuine(), "{finding}");
    let definition = guarded(&format!(
        "eqFloat{{}}({}, {})",
        literal(FLOAT, "1.0e400"),
        literal(FLOAT, MAX)
    ));
    assert!(pair_finding(&definition, "f-zero").is_genuine());
}

/// d2: `g(LITERAL) = 5` is the only equation of the partial `g` over `sort`, beside
/// `k(_) = g(near)` and `k(_) = 5`, `k` total. The pair is genuine only where `g(near)` is
/// stuck, hence undefined.
fn partial_at(sort: &str, value: &str, near: &str) -> BackendDefinition {
    with_builtins(
        &format!(
            r#"    symbol g{{}}({sort}) : SortInt{{}} [function{{}}()]
    symbol k{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]"#
        ),
        &[
            format!(
                r#"    axiom{{R}} \implies{{R}}(
        \and{{R}}(\top{{R}}(), \and{{R}}(\in{{{sort}, R}}(X0:{sort}, {}), \top{{R}}())),
        \equals{{SortInt{{}}, R}}(g{{}}(X0:{sort}), \and{{SortInt{{}}}}({}, \top{{SortInt{{}}}}())))
        [label{{}}("g-lit")]
"#,
                literal(sort, value),
                int("5")
            ),
            int_equation(
                "k",
                r"\top{R}()",
                &format!("g{{}}({})", literal(sort, near)),
                r#"label{}("k-g")"#,
            ),
            int_equation("k", r"\top{R}()", &int("5"), r#"label{}("k-five")"#),
        ]
        .concat(),
    )
}

/// d2 with `1p8`, apart from `255p8` in every model: `g(255p8)` is stuck at a partial symbol,
/// so `k(0)` reduces to an undefined term and to `5`: the pair is genuine. GAP A2: so with
/// `1.0e400` beside MAX, the literal being the infinity in every model (AM-8).
#[test]
fn a_partial_application_stuck_in_every_model_leaves_the_pair_genuine() {
    assert!(pair_finding(&partial_at(MINT, "1p8", NEAR), "k-g").is_genuine());
    assert!(pair_finding(&partial_at(FLOAT, "1.0e400", MAX), "k-g").is_genuine());
}

/// d2 with `256p8`: in the model where its element is `255p8`, `g(255p8)` is `5` and the pair
/// joins. The search does not read `g(255p8)` as stuck on k-rust's element (`0p8`, apart from
/// `255p8`), so the pair is undecided, not genuine.
#[test]
fn a_partial_application_an_open_literal_may_define_leaves_the_pair_undecided() {
    let finding = pair_finding(&partial_at(MINT, "256p8", NEAR), "k-g");
    assert!(!finding.is_genuine(), "{finding}");
}
