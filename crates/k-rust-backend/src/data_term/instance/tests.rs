//! The ground-instance search's readings of stuck applications (S2B-T3), on FUN's overloaded
//! list fixture (`tests/fixtures/overloaded-list-owise.kore`, as `tests/backend/data_terms.rs`
//! reads it): which side holds what, and the defect switch `stuck_partial_is_value`.

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
