//! The V7 switches of review 1's classes (the design's "Revision after review 1", R1.7): each
//! switch restores one rule revision 2 had, and the probe of that class sees it.

use k_rust_kore::kore::parser::parse_definition;

use crate::{
    confluence::switches::{self, Switches},
    definition::BackendDefinition,
};

const PRELUDE: &str = r#"
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
    sort SortS{} []
    symbol mk{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol inj{From, To}(From) : To [sortInjection{}()]
"#;

fn load(declarations: &str, axioms: &str) -> BackendDefinition {
    let source = format!("[] module MAIN {PRELUDE} {declarations} {axioms} endmodule []");
    let syntax = parse_definition(&source).expect("the probe parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the probe internalizes")
}

fn tainted(definition: &BackendDefinition, symbol: &str) -> bool {
    definition
        .value_claims()
        .tainted_symbols()
        .iter()
        .any(|name| name.as_ref() == symbol)
}

/// `name(X:sort) = right`, with `attributes`.
fn unary(
    name: &str,
    sort: &str,
    result: &str,
    pattern: &str,
    right: &str,
    attributes: &str,
) -> String {
    format!(
        r"axiom{{R}} \implies{{R}}(\and{{R}}(\top{{R}}(), \and{{R}}(\in{{{sort}, R}}(X0:{sort}, {pattern}), \top{{R}}())), \equals{{{result}, R}}({name}{{}}(X0:{sort}), \and{{{result}}}({right}, \top{{{result}}}()))) [{attributes}]"
    )
}

/// N1 through `wrapper` (or through a subsort when `wrapper` is `None`): `g(X:A) = c1`,
/// `g(X:A) = c2`, `A` built from `B`, `B` only by the value production `v`.
fn n1(wrapper: Option<&str>) -> BackendDefinition {
    let link = match wrapper {
        Some(attributes) => format!("symbol u{{}}(SortB{{}}) : SortA{{}} [{attributes}]"),
        None => r"axiom{R} \exists{R}(Val:SortA{}, \equals{SortA{}, R}(Val:SortA{}, inj{SortB{}, SortA{}}(From:SortB{}))) [subsort{SortB{}, SortA{}}()]".to_owned(),
    };
    let declarations = format!(
        r"
        sort SortA{{}} []
        sort SortB{{}} []
        sort SortC{{}} []
        symbol c1{{}}() : SortC{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
        symbol c2{{}}() : SortC{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
        symbol v{{}}(SortInt{{}}) : SortB{{}} [anywhere{{}}(), value-production{{}}()]
        symbol g{{}}(SortA{{}}) : SortC{{}} [function{{}}()]
        {link}
    "
    );
    let axioms = [
        unary("g", "SortA{}", "SortC{}", "VarX:SortA{}", "c1{}()", ""),
        unary("g", "SortA{}", "SortC{}", "VarX:SortA{}", "c2{}()", ""),
    ]
    .join("\n");
    load(&declarations, &axioms)
}

/// Review 1's F2 probe: `f(Y) = h(g(Y), Y)`, `f(Y) = v(Y)`, `g(tw(Y)) = mk(1 /Int 0)`, with `tw`
/// total and without equations.
fn stuck_total_branch() -> BackendDefinition {
    let declarations = r"
        sort SortW{} []
        symbol tw{}(SortInt{}) : SortW{} [function{}(), total{}()]
        symbol g{}(SortW{}) : SortS{} [anywhere{}()]
        symbol h{}(SortS{}, SortW{}) : SortS{} [anywhere{}()]
        symbol v{}(SortW{}) : SortS{} [anywhere{}(), value-production{}()]
        symbol f{}(SortW{}) : SortS{} [anywhere{}()]
    ";
    let undefined = r#"mk{}(divInt{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("0")))"#;
    let axioms = [
        unary("g", "SortW{}", "SortS{}", "tw{}(VarY:SortInt{})", undefined, "anywhere{}()"),
        r"axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortS{}, R}(X0:SortS{}, VarZ:SortS{}), \and{R}(\in{SortW{}, R}(X1:SortW{}, VarY:SortW{}), \top{R}()))), \equals{SortS{}, R}(h{}(X0:SortS{}, X1:SortW{}), \and{SortS{}}(v{}(VarY:SortW{}), \top{SortS{}}()))) [anywhere{}()]".to_owned(),
        unary("f", "SortW{}", "SortS{}", "VarY:SortW{}", "h{}(g{}(VarY:SortW{}), VarY:SortW{})", "anywhere{}()"),
        unary("f", "SortW{}", "SortS{}", "VarY:SortW{}", "v{}(VarY:SortW{})", "anywhere{}()"),
    ]
    .join("\n");
    load(declarations, &axioms)
}

#[test]
fn the_f1_probes_withdraw_v_and_see_the_revision_two_collapse() {
    for wrapper in ["function{}(), total{}()", "functional{}()"] {
        assert!(tainted(&n1(Some(wrapper)), "v"), "{wrapper}");
        let collapsed = switches::with(
            Switches {
                collapse_every_total: true,
                ..Switches::default()
            },
            || n1(Some(wrapper)),
        );
        assert!(!tainted(&collapsed, "v"), "{wrapper}");
    }
}

#[test]
fn the_subsort_probe_withdraws_v_and_sees_a_missing_supersort_closure() {
    assert!(tainted(&n1(None), "v"));
    let vacuous = switches::with(
        Switches {
            drop_supersort_inhabitation: true,
            ..Switches::default()
        },
        || n1(None),
    );
    assert!(!tainted(&vacuous, "v"));
}

#[test]
fn the_f2_probe_withdraws_v_and_sees_stuck_totals_read_as_bottom() {
    let definition = stuck_total_branch();
    assert!(tainted(&definition, "f"));
    assert!(tainted(&definition, "v"));
    let bottom = switches::with(
        Switches {
            stuck_total_is_bottom: true,
            ..Switches::default()
        },
        stuck_total_branch,
    );
    assert!(!tainted(&bottom, "f"));
    assert!(!tainted(&bottom, "v"));
}
