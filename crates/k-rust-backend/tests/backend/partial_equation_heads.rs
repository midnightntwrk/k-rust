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
    let attributes = &definition.symbols["wrap"].attributes;
    assert_eq!(
        attributes.symbol_type,
        SymbolType::Function(FunctionType::Partial)
    );
    assert_eq!(attributes.head_role(), HeadRole::EquationHead);
}

#[test]
fn an_unclaimed_macro_symbol_is_a_partial_residual() {
    let definition = internalize(SOURCE).expect("unclaimed equation heads should internalize");
    let attributes = &definition.symbols["half"].attributes;
    assert_eq!(
        attributes.symbol_type,
        SymbolType::Function(FunctionType::Partial)
    );
    assert_eq!(attributes.head_role(), HeadRole::Residual);
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
