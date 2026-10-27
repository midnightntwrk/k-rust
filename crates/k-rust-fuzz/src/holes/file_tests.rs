//! The flat `[[hole]]` form decoded from JSON, in the portable build (no `cli`, no TOML): every
//! key, each kind of choice, a binding's text (`"$NAME"`), and the refusals.

use num_bigint::{BigInt, BigUint};
use serde_json::json;

use super::{HoleChoice, HoleFile};
use crate::{
    holes::{HoleDecl, HoleLocation, SpanAddress},
    values::{Constraints, ElementSorts, IntRange, LengthRange, Value},
};

fn decl(hole: serde_json::Value, program: Option<&str>) -> Result<HoleDecl, String> {
    serde_json::from_value::<HoleFile>(hole)
        .map_err(|error| error.to_string())?
        .into_decl(program)
}

#[test]
fn every_span_key_decodes_into_the_declaration() {
    let hole = decl(
        json!({
            "name": "AMOUNT",
            "sort": "Int",
            "program": "transfer.imp",
            "line": 4,
            "column": 12,
            "find": "amount = 250;",
            "literal": "250",
            "range": { "min": -5, "max": "100000000000000000000000" },
            "allow-refused-sort": true,
        }),
        Some("ignored.imp"),
    )
    .unwrap();
    assert_eq!(
        hole,
        HoleDecl {
            name: "AMOUNT".into(),
            sort: "Int".into(),
            location: HoleLocation::Span(SpanAddress {
                program: "transfer.imp".into(),
                line: Some(4),
                column: Some(12),
                find: "amount = 250;".into(),
                literal: "250".into(),
            }),
            constraints: Constraints {
                range: Some(IntRange {
                    min: Some(BigInt::from(-5)),
                    max: Some("100000000000000000000000".parse().unwrap()),
                }),
                ..Constraints::default()
            },
            allow_refused_sort: true,
        }
    );
}

#[test]
fn a_span_hole_takes_the_campaign_program_or_a_binding_and_find_defaults_to_the_literal() {
    let hole = decl(
        json!({ "name": "N", "sort": "Int", "literal": "3" }),
        Some("go.pgm"),
    )
    .unwrap();
    assert_eq!(
        hole.location,
        HoleLocation::Span(SpanAddress {
            program: "go.pgm".into(),
            line: None,
            column: None,
            find: "3".into(),
            literal: "3".into(),
        })
    );
    assert!(!hole.allow_refused_sort);
    assert_eq!(hole.constraints, Constraints::default());
    let hole = decl(
        json!({ "name": "A", "sort": "Int", "program": "$TX", "find": "(30,", "literal": "30" }),
        Some("go.pgm"),
    )
    .unwrap();
    assert!(matches!(
        hole.location,
        HoleLocation::Span(SpanAddress { ref program, .. }) if program == "$TX"
    ));
}

#[test]
fn a_config_var_hole_drops_the_dollar_and_collections_take_their_constraints() {
    for written in ["TX", "$TX"] {
        let hole = decl(
            json!({
                "name": "T",
                "sort": "List",
                "config-var": written,
                "length": { "min": 1, "max": 4 },
                "elements": { "element": "Int" },
            }),
            None,
        )
        .unwrap();
        assert_eq!(hole.location, HoleLocation::ConfigVar { name: "TX".into() });
        assert_eq!(
            hole.constraints.length,
            Some(LengthRange {
                min: Some(1),
                max: Some(4)
            })
        );
        assert_eq!(
            hole.constraints.elements,
            Some(ElementSorts::Elements {
                element: "Int".into()
            })
        );
    }
    let hole = decl(
        json!({
            "name": "M",
            "sort": "Map",
            "config-var": "M",
            "elements": { "key": "Int", "value": "Bool" },
        }),
        None,
    )
    .unwrap();
    assert_eq!(
        hole.constraints.elements,
        Some(ElementSorts::Entries {
            key: "Int".into(),
            value: "Bool".into()
        })
    );
}

#[test]
fn each_kind_of_choice_becomes_a_value_at_the_hole_sort() {
    let hole = decl(
        json!({
            "name": "C",
            "sort": "Int",
            "config-var": "C",
            "choices": [
                -7,
                true,
                "text",
                { "int": "123456789012345678901234567890" },
                { "list": [{ "int": "1" }] },
                { "token": { "sort": "Id", "text": "x" } },
            ],
        }),
        None,
    )
    .unwrap();
    assert_eq!(
        hole.constraints.choices,
        Some(vec![
            Value::Int(BigInt::from(-7)),
            Value::Bool(true),
            Value::String("text".into()),
            Value::Int("123456789012345678901234567890".parse().unwrap()),
            Value::List(vec![Value::Int(BigInt::from(1))]),
            Value::Token {
                sort: "Id".into(),
                text: "x".into()
            },
        ])
    );
    let hole = decl(
        json!({ "name": "W", "sort": "MInt{8}", "config-var": "W", "choices": [0, 255] }),
        None,
    )
    .unwrap();
    assert_eq!(
        hole.constraints.choices,
        Some(vec![
            Value::MInt {
                width: 8,
                value: BigUint::from(0u8)
            },
            Value::MInt {
                width: 8,
                value: BigUint::from(255u8)
            },
        ])
    );
}

/// The refusals of `krust fuzz`'s campaign file, word for word.
#[test]
fn the_refusals_name_the_hole() {
    let refusal = |hole| decl(hole, Some("p.imp")).unwrap_err();
    assert_eq!(
        refusal(json!({ "name": "X", "sort": "Int", "config-var": "X", "literal": "1" })),
        "hole `X`: `config-var` addresses a whole variable; it takes no `program`, `line`, \
         `column`, `find` or `literal`"
    );
    assert_eq!(
        refusal(json!({ "name": "X", "sort": "Int", "config-var": "X", "program": "$X" })),
        "hole `X`: `config-var` addresses a whole variable; it takes no `program`, `line`, \
         `column`, `find` or `literal`"
    );
    assert_eq!(
        refusal(json!({ "name": "X", "sort": "Int", "find": "x = 1;" })),
        "hole `X`: give its `literal` (and `find`), or a `config-var`"
    );
    assert_eq!(
        decl(json!({ "name": "X", "sort": "Int", "literal": "1" }), None).unwrap_err(),
        "hole `X`: no program to address; give the hole a `program`"
    );
    assert_eq!(
        refusal(json!({ "name": "X", "sort": "Int", "literal": "1", "range": { "max": "1e3" } })),
        "hole `X`: `1e3` is not a decimal integer: invalid digit found in string"
    );
    assert_eq!(
        refusal(json!({ "name": "X", "sort": "MInt{8}", "literal": "1", "choices": [-1] })),
        "hole `X`: -1 is negative; an MInt{8} value is unsigned"
    );
}

/// A choice that is no value, and a misspelt key, are refused when the hole is decoded.
#[test]
fn what_is_no_value_and_unknown_keys_are_refused_on_decoding() {
    let refusal = |choice| {
        decl(
            json!({ "name": "X", "sort": "Int", "literal": "1", "choices": [choice] }),
            Some("p.imp"),
        )
        .unwrap_err()
    };
    for (choice, says) in [
        (json!(1.5), "invalid type: floating point `1.5`"),
        (json!([1, 2]), "invalid type: sequence"),
        (json!(null), "invalid type: "),
        (json!({ "integer": "1" }), "unknown variant `integer`"),
        (
            json!({ "int": "1", "bool": true }),
            "a value table has exactly one key",
        ),
        (
            json!(u64::MAX),
            "write it as { int = \"18446744073709551615\" }",
        ),
    ] {
        let message = refusal(choice.clone());
        assert!(message.contains(says), "{choice}: {message}");
    }
    assert!(
        refusal(json!(1.5)).contains("write collections and other values as tables"),
        "the non-value message keeps the campaign file's advice"
    );
    let misspelt = decl(
        json!({ "name": "X", "sort": "Int", "literal": "1", "choice": [1] }),
        Some("p.imp"),
    )
    .unwrap_err();
    assert!(
        misspelt.starts_with("unknown field `choice`, expected one of `name`, `sort`, `program`"),
        "{misspelt}"
    );
    assert_eq!(
        serde_json::from_value::<HoleChoice>(json!(i64::MIN)).unwrap(),
        HoleChoice::Integer(i64::MIN)
    );
}

/// FZ-REPLAY-WHOLE N2: a range bound that is neither an integer nor a decimal string is refused
/// with what a bound may be, not with the name of an internal type.
#[test]
fn a_fractional_range_bound_says_what_a_bound_is() {
    let error = decl(
        json!({ "name": "N", "sort": "Int", "literal": "3", "range": { "max": 8.5 } }),
        Some("p.imp"),
    )
    .expect_err("a fractional bound is refused");
    assert!(
        error.contains("a range bound: an integer, or a decimal string")
            && !error.contains("IntText"),
        "{error}"
    );
    let wide = decl(
        json!({ "name": "N", "sort": "Int", "literal": "3", "range": { "max": u64::MAX } }),
        Some("p.imp"),
    )
    .expect("a bound above i64 reads as its digits");
    assert_eq!(
        wide.constraints.range.and_then(|range| range.max),
        Some(BigInt::from(u64::MAX))
    );
}
