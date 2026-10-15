//! A collection sort's unit, element and concatenation symbols have the signature of their role.
//!
//! A collection sort `C` (`hook(LIST.List)`, `hook(SET.Set)`, `hook(MAP.Map)`) names its unit,
//! element and concatenation symbols, and every application of one of them is built as a value
//! of `C`. Each symbol's declaration also fixes the sort of its applications, so a definition in
//! which the two disagree gives a role application two sorts and is refused at load: the symbol
//! has no sort parameters, its result sort is `C`, the unit takes no argument, the element one
//! (two for a map), the concatenation two of sort `C`, and its hook, if any, is the role's own.
//! A role symbol need not carry a hook.

use k_rust_backend::{
    definition::{BackendDefinition, DefinitionError},
    term::TermKind,
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::internal_term;

/// A list sort whose role symbols have their roles' signatures and carry no hook.
const WELL_SORTED: &str = r#"[]
module MAIN
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  sort SortKItem{} []
  sort SortFoo{} []
  symbol inj{From, To}(From) : To [sortInjection{}()]
  hooked-sort SortLI{}
    [hook{}("LIST.List"), unit{}(dotLI{}()), element{}(liItem{}()), concat{}(liConcat{}())]
  symbol dotLI{}() : SortLI{} [function{}(), total{}()]
  symbol liItem{}(SortInt{}) : SortLI{} [function{}(), total{}()]
  symbol liConcat{}(SortLI{}, SortLI{}) : SortLI{} [function{}(), total{}()]
endmodule []"#;

const UNIT: &str = "symbol dotLI{}() : SortLI{} [function{}(), total{}()]";
const ELEMENT: &str = "symbol liItem{}(SortInt{}) : SortLI{} [function{}(), total{}()]";
const CONCAT: &str = "symbol liConcat{}(SortLI{}, SortLI{}) : SortLI{} [function{}(), total{}()]";

fn internalize(source: &str) -> Result<BackendDefinition, DefinitionError> {
    let syntax = parse_definition(source).expect("the definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
}

/// `WELL_SORTED` with the declaration `original` replaced by `replacement`.
fn with(original: &str, replacement: &str) -> String {
    assert!(WELL_SORTED.contains(original), "{original}");
    WELL_SORTED.replace(original, replacement)
}

/// The fields of the role misfit loading `source` gives: sort, role, symbol and reason.
fn role_misfit(source: &str) -> (String, String, String, String) {
    match internalize(source) {
        Err(DefinitionError::CollectionRoleMisfit {
            sort,
            role,
            symbol,
            position: _,
            reason,
        }) => (sort, role, symbol, reason),
        Ok(_) => panic!("the definition loaded"),
        Err(error) => panic!("the definition was refused for another reason: {error}"),
    }
}

/// The handoff's shape: the list's element symbol builds a `Foo`, and the function `g` reaches
/// it through an equation, so no axiom writes `mkFoo` as an application argument.
#[test]
fn element_symbol_of_another_result_sort_is_refused() {
    let source = WELL_SORTED
        .replace("element{}(liItem{}())", "element{}(mkFoo{}())")
        .replace(
            ELEMENT,
            r#"symbol mkFoo{}(SortInt{}) : SortFoo{} [constructor{}(), functional{}()]
  symbol g{}(SortInt{}) : SortFoo{} [function{}(), total{}()]
  axiom{R} \implies{R}(
      \and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \top{R}())),
      \equals{SortFoo{}, R}(
        g{}(X0:SortInt{}),
        \and{SortFoo{}}(mkFoo{}(VarX:SortInt{}), \top{SortFoo{}}())
      )
    ) []"#,
        );
    let (sort, role, symbol, reason) = role_misfit(&source);
    assert_eq!(
        (sort.as_str(), role.as_str(), symbol.as_str()),
        ("SortLI", "element", "mkFoo")
    );
    assert!(
        reason.contains("SortFoo") && reason.contains("SortLI"),
        "{reason}"
    );
}

#[test]
fn unit_symbol_with_an_argument_is_refused() {
    let source = with(
        UNIT,
        "symbol dotLI{}(SortInt{}) : SortLI{} [function{}(), total{}()]",
    );
    let (sort, role, symbol, reason) = role_misfit(&source);
    assert_eq!(
        (sort.as_str(), role.as_str(), symbol.as_str()),
        ("SortLI", "unit", "dotLI")
    );
    assert!(reason.contains("takes 1 argument"), "{reason}");
}

#[test]
fn concat_with_a_non_collection_operand_is_refused() {
    let source = with(
        CONCAT,
        "symbol liConcat{}(SortLI{}, SortInt{}) : SortLI{} [function{}(), total{}()]",
    );
    let (sort, role, symbol, reason) = role_misfit(&source);
    assert_eq!(
        (sort.as_str(), role.as_str(), symbol.as_str()),
        ("SortLI", "concat", "liConcat")
    );
    assert!(
        reason.contains("argument 2") && reason.contains("SortInt"),
        "{reason}"
    );
}

#[test]
fn concat_of_another_result_sort_is_refused() {
    let source = with(
        CONCAT,
        "symbol liConcat{}(SortLI{}, SortLI{}) : SortKItem{} [function{}(), total{}()]",
    );
    let (sort, role, symbol, reason) = role_misfit(&source);
    assert_eq!(
        (sort.as_str(), role.as_str(), symbol.as_str()),
        ("SortLI", "concat", "liConcat")
    );
    assert!(reason.contains("result sort SortKItem"), "{reason}");
}

#[test]
fn role_symbol_with_sort_parameters_is_refused() {
    let source = with(
        ELEMENT,
        "symbol liItem{S}(SortInt{}) : SortLI{} [function{}(), total{}()]",
    );
    let (sort, role, symbol, reason) = role_misfit(&source);
    assert_eq!(
        (sort.as_str(), role.as_str(), symbol.as_str()),
        ("SortLI", "element", "liItem")
    );
    assert!(reason.contains("sort parameter"), "{reason}");
}

/// `SET.union` states a coherent theory (idempotent union), but not the one k-rust builds for a
/// set's concatenation, so the hook contradicts the role.
#[test]
fn set_concat_hooked_union_is_refused() {
    let source = WELL_SORTED
        .replace(r#"hook{}("LIST.List")"#, r#"hook{}("SET.Set")"#)
        .replace(
            CONCAT,
            r#"hooked-symbol liConcat{}(SortLI{}, SortLI{}) : SortLI{}
    [function{}(), total{}(), hook{}("SET.union")]"#,
        );
    let (sort, role, symbol, reason) = role_misfit(&source);
    assert_eq!(
        (sort.as_str(), role.as_str(), symbol.as_str()),
        ("SortLI", "concat", "liConcat")
    );
    assert!(
        reason.contains("SET.union") && reason.contains("SET.concat"),
        "{reason}"
    );
}

/// Hooks on role symbols are optional: the collection sort's attributes alone fix what its role
/// symbols build.
#[test]
fn hookless_well_sorted_roles_load_and_build_collections() {
    let definition = internalize(WELL_SORTED).expect("well-sorted hookless roles should load");
    let item = internal_term(&definition, r#"liItem{}(\dv{SortInt{}}("1"))"#);
    assert!(
        matches!(item.kind(), TermKind::List { .. }),
        "{:?}",
        item.kind()
    );
}

/// A role symbol declared `constructor` has the hooked collection sort as its result sort,
/// which no constructor may have; the combination never loads, whichever check refuses it.
#[test]
fn a_constructor_role_symbol_is_refused() {
    let source = with(
        UNIT,
        "symbol dotLI{}() : SortLI{} [constructor{}(), functional{}()]",
    );
    let result = internalize(&source);
    assert!(
        matches!(
            result,
            Err(DefinitionError::Verification(_) | DefinitionError::CollectionRoleMisfit { .. })
        ),
        "a constructor unit symbol must be refused as a constructor of a hooked sort or as a \
         role misfit: {:?}",
        result.err()
    );
}

/// The refusal names the role symbol where its declaration was written, not where another
/// declaration of the collection was.
#[test]
fn the_refusal_carries_the_role_symbols_written_position() {
    const SOURCE: &str = "org'Stop'kframework'Stop'attributes'Stop'Source{}";
    const LOCATION: &str = "org'Stop'kframework'Stop'attributes'Stop'Location{}";
    let located = |line: u32| {
        format!(r#"{SOURCE}("Source(/p/role.k)"), {LOCATION}("Location({line},18,{line},40)")"#)
    };
    let source = with(
        UNIT,
        &format!(
            "symbol dotLI{{}}(SortInt{{}}) : SortLI{{}} [function{{}}(), total{{}}(), {}]",
            located(6)
        ),
    )
    .replace(
        ELEMENT,
        &format!(
            "symbol liItem{{}}(SortInt{{}}) : SortLI{{}} [function{{}}(), total{{}}(), {}]",
            located(7)
        ),
    );
    match internalize(&source) {
        Err(DefinitionError::CollectionRoleMisfit {
            symbol, position, ..
        }) => {
            assert_eq!(symbol, "dotLI");
            assert_eq!(position.as_deref(), Some("/p/role.k:6:18"));
        }
        Ok(_) => panic!("the definition loaded"),
        Err(error) => panic!("the definition was refused for another reason: {error}"),
    }
}
