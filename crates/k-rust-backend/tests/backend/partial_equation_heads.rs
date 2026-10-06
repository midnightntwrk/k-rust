use k_rust_backend::{
    definition::{BackendDefinition, DefinitionError},
    rule::Predicate,
    simplify::SimplificationOptions,
    smt::NoSolver,
    term::{FunctionType, HeadRole, SymbolType},
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::support::{
    internal_term,
    unstopped::{simplify, simplify_predicate_with_solver},
};

const SOURCE: &str = r#"[]
    module MAIN
        hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
        hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{}
            [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
        hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
            [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
        sort SortS{} []
        symbol mk{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        symbol wrap{}(SortInt{}) : SortS{} [anywhere{}()]
        axiom{R} \implies{R}(
            \and{R}(
                \equals{SortBool{}, R}(
                    eqInt{}(VarX:SortInt{}, \dv{SortInt{}}("0")),
                    \dv{SortBool{}}("true")
                ),
                \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \top{R}())
            ),
            \equals{SortS{}, R}(
                wrap{}(X0:SortInt{}),
                \and{SortS{}}(
                    mk{}(divInt{}(VarX:SortInt{}, \dv{SortInt{}}("0"))),
                    \top{SortS{}}()
                )
            )
        ) [anywhere{}()]
        symbol half{}(SortInt{}) : SortS{} [macro{}()]
    endmodule []"#;

fn internalize(source: &str) -> Result<BackendDefinition, DefinitionError> {
    let syntax = parse_definition(source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
}

#[test]
fn an_unclaimed_anywhere_head_is_a_partial_equation_head() {
    let definition = internalize(SOURCE).expect("unclaimed equation heads should internalize");
    let attributes = &definition.symbols()["wrap"].attributes;
    assert_eq!(
        attributes.symbol_type,
        SymbolType::Function(FunctionType::Partial)
    );
    assert_eq!(attributes.head_role(), HeadRole::EquationHead);
}

#[test]
fn an_unclaimed_macro_symbol_is_a_partial_residual() {
    let definition = internalize(SOURCE).expect("unclaimed equation heads should internalize");
    let attributes = &definition.symbols()["half"].attributes;
    assert_eq!(
        attributes.symbol_type,
        SymbolType::Function(FunctionType::Partial)
    );
    assert_eq!(attributes.head_role(), HeadRole::Residual);
}

/// Single-valuedness does not make a value production a computed function.
/// Its equation can still make an application undefined, so the marker must not imply totality.
#[test]
fn marked_value_productions_keep_the_unclaimed_roles_and_definedness() {
    let source = SOURCE
        .replace(
            "symbol wrap{}(SortInt{}) : SortS{} [anywhere{}()]",
            "symbol wrap{}(SortInt{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]",
        )
        .replace(
            "[macro{}()]",
            "[macro{}(), function{}(), value-production{}()]",
        );
    let definition = internalize(&source).expect("marked value productions should internalize");
    for (name, role) in [
        ("wrap", HeadRole::EquationHead),
        ("half", HeadRole::Residual),
    ] {
        let attributes = &definition.symbols()[name].attributes;
        assert_eq!(
            attributes.symbol_type,
            SymbolType::Function(FunctionType::Partial)
        );
        assert_eq!(attributes.head_role(), role);
    }
    for name in ["divInt", "eqInt"] {
        assert!(
            matches!(
                definition.symbols()[name].attributes.head_role(),
                HeadRole::Function { declared: true, .. }
            ),
            "{name}"
        );
    }
    assert_eq!(
        simplified_predicate(&definition, r"\ceil{SortS{}, SortS{}}(wrap{}(X:SortInt{}))"),
        Predicate::Ceil(internal_term(&definition, "wrap{}(X:SortInt{})")),
    );
    assert_eq!(
        simplified_predicate(
            &definition,
            r#"\ceil{SortS{}, SortS{}}(wrap{}(\dv{SortInt{}}("0")))"#
        ),
        Predicate::False,
    );
    let computed = internalize(&SOURCE.replace("[anywhere{}()]", "[anywhere{}(), function{}()]"))
        .expect("a declared function should internalize");
    assert!(matches!(
        computed.symbols()["wrap"].attributes.head_role(),
        HeadRole::Function { declared: true, .. }
    ));
}

#[test]
fn a_symbol_without_claim_or_equation_marker_is_still_rejected() {
    let source = SOURCE.replace(
        "sort SortS{} []",
        "sort SortS{} []\n        symbol plain{}(SortInt{}) : SortS{} []",
    );
    assert!(matches!(
        internalize(&source),
        Err(DefinitionError::InvalidSymbolType(_))
    ));
}

fn simplified_predicate(definition: &BackendDefinition, source: &str) -> Predicate {
    let syntax = parse_pattern(source).expect("predicate should parse");
    let (predicate, _) = definition
        .admit_unverified(&syntax, &[])
        .internalize_predicate()
        .expect("predicate should internalize");
    simplify_predicate_with_solver(
        definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("predicate should simplify")
}

/// A value production whose anywhere equation `wrap(s(X)) = wrap(X)` reapplies its own head, so
/// no totality claim is emitted for it; `t` is a second constructor of the argument sort.
const VALUE_HEAD: &str = r#"[]
    module MAIN
        sort SortNat{} []
        symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
        symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
        symbol t{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
        sort SortW{} []
        symbol wrap{}(SortNat{}) : SortW{} [anywhere{}(), function{}(), value-production{}()]
        axiom{R} \implies{R}(
            \and{R}(
                \top{R}(),
                \and{R}(\in{SortNat{}, R}(X0:SortNat{}, s{}(VarX:SortNat{})), \top{R}())
            ),
            \equals{SortW{}, R}(
                wrap{}(X0:SortNat{}),
                \and{SortW{}}(wrap{}(VarX:SortNat{}), \top{SortW{}}())
            )
        ) [anywhere{}()]
    endmodule []"#;

/// `value-production` states that an application no equation reduces is a value of its sort.
/// So where no equation can reach any instance of an application, its definedness is that of
/// its arguments: `wrap(z)` and `wrap(t(Y))` (whose arguments the equation's `s(_)` cannot match)
/// are defined, and `wrap(s(z))` is defined because it evaluates to `wrap(z)`. `wrap(Y)` keeps
/// its obligation, since the equation reaches its instance `wrap(s(z))`. Without the marker the
/// anywhere head claims nothing about an irreducible application, so `wrap(z)` keeps its
/// obligation too.
#[test]
fn an_irreducible_value_production_application_is_defined() {
    let definition = internalize(VALUE_HEAD).expect("value production should internalize");
    for (query, expected) in [
        ("wrap{}(z{}())", Predicate::True),
        ("wrap{}(t{}(Y:SortNat{}))", Predicate::True),
        ("wrap{}(s{}(z{}()))", Predicate::True),
        (
            "wrap{}(Y:SortNat{})",
            Predicate::Ceil(internal_term(&definition, "wrap{}(Y:SortNat{})")),
        ),
    ] {
        assert_eq!(
            simplified_predicate(
                &definition,
                &format!(r"\ceil{{SortW{{}}, SortW{{}}}}({query})")
            ),
            expected,
            "{query}"
        );
    }
    let unmarked = internalize(&VALUE_HEAD.replace(
        "[anywhere{}(), function{}(), value-production{}()]",
        "[anywhere{}()]",
    ))
    .expect("an unmarked anywhere head should internalize");
    assert_eq!(
        simplified_predicate(&unmarked, r"\ceil{SortW{}, SortW{}}(wrap{}(z{}()))"),
        Predicate::Ceil(internal_term(&unmarked, "wrap{}(z{}())")),
    );
}

/// Without a totality claim, `ceil(wrap(X))` remains an obligation.
/// The equation makes both `ceil(wrap(0))` and `wrap(0)` bottom.
/// Adding `functional` makes the symbolic query top, contradicting its bottom instance at `X = 0`.
#[test]
fn the_definedness_of_a_partial_equation_head_is_decided_by_its_equations() {
    let definition = internalize(SOURCE).expect("unclaimed equation heads should internalize");
    let query = r"\ceil{SortS{}, SortS{}}(wrap{}(X:SortInt{}))";
    let symbolic = simplified_predicate(&definition, query);
    assert_ne!(symbolic, Predicate::True);
    assert_eq!(
        symbolic,
        Predicate::Ceil(internal_term(&definition, "wrap{}(X:SortInt{})"))
    );
    assert_eq!(
        simplified_predicate(
            &definition,
            r#"\ceil{SortS{}, SortS{}}(wrap{}(\dv{SortInt{}}("0")))"#,
        ),
        Predicate::False,
    );
    let result = simplify(
        &definition,
        &internal_term(&definition, r#"wrap{}(\dv{SortInt{}}("0"))"#),
        SimplificationOptions::default(),
    )
    .expect("term should simplify");
    // The result conjoins its constraints to the retained term, so false makes it bottom.
    assert_eq!(result.constraints(), [Predicate::False]);

    let claimed = internalize(&SOURCE.replace(
        "symbol wrap{}(SortInt{}) : SortS{} [anywhere{}()]",
        "symbol wrap{}(SortInt{}) : SortS{} [anywhere{}(), functional{}()]",
    ))
    .expect("claimed equation heads should internalize");
    assert_eq!(simplified_predicate(&claimed, query), Predicate::True);
}

/// `SOURCE` with `wrap` marked as a value production, and `u()`, an unmarked anywhere constant
/// that no equation reduces: its definedness stays an obligation of its own.
fn conditional_value_production() -> BackendDefinition {
    internalize(
        &SOURCE
            .replace(
                "symbol wrap{}(SortInt{}) : SortS{} [anywhere{}()]",
                "symbol wrap{}(SortInt{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]\n        symbol u{}() : SortInt{} [anywhere{}()]",
            ),
    )
    .expect("a conditional value production should internalize")
}

fn simplified_predicate_under(
    definition: &BackendDefinition,
    source: &str,
    known: &[&str],
) -> Predicate {
    let internalize = |source: &str| {
        let syntax = parse_pattern(source).expect("predicate should parse");
        definition
            .admit_unverified(&syntax, &[])
            .internalize_predicate()
            .expect("predicate should internalize")
            .0
    };
    let known = known
        .iter()
        .map(|source| internalize(source))
        .collect::<Vec<_>>();
    simplify_predicate_with_solver(
        definition,
        &internalize(source),
        &known,
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("predicate should simplify")
}

/// `wrap`'s only equation `wrap(X) = mk(X /Int 0) requires X ==Int 0` reduces an application
/// only where its `requires` holds. `value-production` makes an application that no equation
/// reduces a value, so where the `requires` is false the application's definedness is that of
/// its argument: `wrap(1)` is defined on every valuation, `wrap(X)` wherever the path condition
/// refutes `X ==Int 0`, and `wrap(u())` there exactly when `u()` is. Without such a refutation
/// `wrap(X)` keeps its obligation, `wrap(0)` is still undefined (its equation applies and
/// divides by zero), and an unmarked head keeps the obligation of `wrap(1)`.
#[test]
fn a_value_production_application_whose_reaching_equations_are_refuted_is_defined() {
    let definition = conditional_value_production();
    let ceil = |argument: &str| format!(r"\ceil{{SortS{{}}, SortS{{}}}}(wrap{{}}({argument}))");
    let refuted = |argument: &str| {
        format!(
            r#"\equals{{SortBool{{}}, SortS{{}}}}(eqInt{{}}({argument}, \dv{{SortInt{{}}}}("0")), \dv{{SortBool{{}}}}("false"))"#
        )
    };
    let one = r#"\dv{SortInt{}}("1")"#;
    assert_eq!(
        simplified_predicate_under(&definition, &ceil(one), &[]),
        Predicate::True
    );
    assert_eq!(
        simplified_predicate_under(
            &definition,
            &ceil("X:SortInt{}"),
            &[&refuted("X:SortInt{}")]
        ),
        Predicate::True
    );
    assert_eq!(
        simplified_predicate_under(&definition, &ceil("u{}()"), &[&refuted("u{}()")]),
        Predicate::Ceil(internal_term(&definition, "u{}()"))
    );
    assert_eq!(
        simplified_predicate_under(&definition, &ceil("X:SortInt{}"), &[]),
        Predicate::Ceil(internal_term(&definition, "wrap{}(X:SortInt{})"))
    );
    assert_eq!(
        simplified_predicate_under(&definition, &ceil(r#"\dv{SortInt{}}("0")"#), &[]),
        Predicate::False
    );
    let unmarked = internalize(SOURCE).expect("an unmarked anywhere head should internalize");
    assert_eq!(
        simplified_predicate_under(&unmarked, &ceil(one), &[]),
        Predicate::Ceil(internal_term(&unmarked, &format!("wrap{{}}({one})")))
    );
}
