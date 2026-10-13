//! The construction routes of domain values: each builds the canonical text of the element it
//! denotes, with the kind its sort's hook gives in the loaded definition, and builds no text that
//! names no element of its sort.

use indoc::indoc;
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    builtin::{BuiltinResult, UnsupportedHookReason, evaluate, evaluate_in_definition},
    definition::BackendDefinition,
    term::{Sort, Term, TermKind},
};

/// String-to-token functions at a sort hooked `INT.Int` under its own name, at machine-integer
/// sorts, at a token sort, at a renamed `BYTES.Bytes` sort and at a sort named `SortMInt`
/// without the hook, each `total` and partial; and builtin hooks declared at sorts whose hook
/// differs from the builtin's.
const DEFINITION: &str = indoc! {r#"
    []
    module MAIN
        hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
        hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        hooked-sort SortFloat{} [hook{}("FLOAT.Float"), hasDomainValues{}()]
        hooked-sort SortMyInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        hooked-sort SortMyFloat{} [hook{}("FLOAT.Float"), hasDomainValues{}()]
        hooked-sort SortMyBytes{} [hook{}("BYTES.Bytes"), hasDomainValues{}()]
        hooked-sort SortMInt{S} [hook{}("MINT.MInt"), hasDomainValues{}()]
        sort Sort8{} []
        sort Sort33554432{} []
        sort SortId{} [hasDomainValues{}()]
        sort SortText{} [hasDomainValues{}()]
        hooked-symbol LblString2MyInt{}(SortString{}) : SortMyInt{}
            [function{}(), total{}(), hook{}("STRING.string2token")]
        hooked-symbol LblString2MyIntPartial{}(SortString{}) : SortMyInt{}
            [function{}(), hook{}("STRING.string2token")]
        hooked-symbol LblString2Word{}(SortString{}) : SortMInt{Sort8{}}
            [function{}(), total{}(), hook{}("STRING.string2token")]
        hooked-symbol LblString2Wide{}(SortString{}) : SortMInt{Sort33554432{}}
            [function{}(), total{}(), hook{}("STRING.string2token")]
        hooked-symbol LblString2WidePartial{}(SortString{}) : SortMInt{Sort33554432{}}
            [function{}(), hook{}("STRING.string2token")]
        hooked-symbol LblString2Id{}(SortString{}) : SortId{}
            [function{}(), total{}(), hook{}("STRING.string2token")]
        hooked-symbol LblString2MyBytes{}(SortString{}) : SortMyBytes{}
            [function{}(), total{}(), hook{}("STRING.string2token")]
        hooked-symbol LblInt2MyFloat{}(SortInt{}, SortInt{}, SortInt{}) : SortMyFloat{}
            [function{}(), total{}(), hook{}("FLOAT.int2float")]
        hooked-symbol LblconcatText{}(SortString{}, SortString{}) : SortText{}
            [function{}(), total{}(), hook{}("STRING.concat")]
    endmodule []
"#};

/// A sort named `SortMInt` declared without the `MINT.MInt` hook: a token sort.
const UNHOOKED_MINT_DEFINITION: &str = indoc! {r#"
    []
    module MAIN
        hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
        sort SortMInt{S} [hasDomainValues{}()]
        sort Sort8{} []
        hooked-symbol LblString2W{}(SortString{}) : SortMInt{Sort8{}}
            [function{}(), total{}(), hook{}("STRING.string2token")]
    endmodule []
"#};

fn load(source: &str) -> BackendDefinition {
    let syntax = parse_definition(source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn term(definition: &BackendDefinition, pattern: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(pattern).expect("pattern should parse"), &[])
        .unwrap_or_else(|error| panic!("{pattern}: {error}"))
}

/// The hook evaluation of the application `pattern` in `definition`.
fn evaluated(definition: &BackendDefinition, pattern: &str) -> BuiltinResult {
    evaluate_in_definition(&term(definition, pattern), definition)
        .expect("evaluation should not stop")
        .unwrap_or_else(|error| panic!("{pattern}: {error:?}"))
}

fn string_to(symbol: &str, text: &str) -> String {
    format!(r#"{symbol}{{}}(\dv{{SortString{{}}}}("{text}"))"#)
}

fn value_text(result: &BuiltinResult) -> String {
    let BuiltinResult::Value(value) = result else {
        panic!("not a value: {result:?}");
    };
    let TermKind::DomainValue { value, .. } = value.kind() else {
        panic!("not a domain value: {value:?}");
    };
    value.as_utf8().unwrap().to_owned()
}

/// `STRING.string2token` reads its text by the kind its result sort's hook gives: `"07"` at a
/// sort hooked `INT.Int` is the integer 7, `"-1p8"` at `MInt{8}` is the residue `255p8`, and a
/// token sort keeps the text.
#[test]
fn string_to_token_reads_its_text_by_the_hook_of_its_result_sort() {
    let definition = load(DEFINITION);
    let my_int = evaluated(&definition, &string_to("LblString2MyInt", "07"));
    assert_eq!(
        my_int,
        BuiltinResult::Value(term(&definition, r#"\dv{SortMyInt{}}("7")"#))
    );
    assert_eq!(value_text(&my_int), "7");
    assert_eq!(
        value_text(&evaluated(
            &definition,
            &string_to("LblString2Word", "-1p8")
        )),
        "255p8"
    );
    for text in ["x", "_42", "07"] {
        assert_eq!(
            value_text(&evaluated(&definition, &string_to("LblString2Id", text))),
            text
        );
    }
}

/// A text that names no element of the result sort has no value the definition gives: a
/// `total` declaration has a value the definition does not determine, and a partial one is
/// undefined there.
#[test]
fn string_to_token_of_a_text_that_names_no_element_has_no_value() {
    let definition = load(DEFINITION);
    for (symbol, text) in [
        ("LblString2MyInt", "abc"),
        ("LblString2Word", "1p16"),
        ("LblString2Word", "abc"),
        ("LblString2MyBytes", "\\u0101"),
    ] {
        let result = evaluated(&definition, &string_to(symbol, text));
        assert!(
            matches!(
                result,
                BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified { .. })
            ),
            "{symbol}({text:?}): {result:?}"
        );
    }
    assert_eq!(
        evaluated(&definition, &string_to("LblString2MyIntPartial", "abc")),
        BuiltinResult::Bottom
    );
}

/// A text beyond a bound of k-rust names an element that k-rust declines to compute: it is the
/// resource refusal whatever the declaration's totality, never undefined.
#[test]
fn string_to_token_beyond_a_bound_is_too_large_whatever_its_totality() {
    let definition = load(DEFINITION);
    for symbol in ["LblString2Wide", "LblString2WidePartial"] {
        let result = evaluated(&definition, &string_to(symbol, "-1p33554432"));
        assert!(
            matches!(
                result,
                BuiltinResult::Unsupported(UnsupportedHookReason::ResultTooLarge { .. })
            ),
            "{symbol}: {result:?}"
        );
    }
}

/// Without a definition the result sort has no kind, so no token is built.
#[test]
fn string_to_token_without_a_definition_is_not_applicable() {
    let definition = load(DEFINITION);
    let application = term(&definition, &string_to("LblString2Id", "x"));
    assert_eq!(
        evaluate(&application).unwrap().unwrap(),
        BuiltinResult::NotApplicable
    );
}

/// A sort named `SortMInt` without the `MINT.MInt` hook is a token sort on every route: the
/// literal `256p8` loaded and the token `String2W("256p8")` built at run time are one term,
/// with that text, distinct from `0p8`.
#[test]
fn an_unhooked_sort_named_sort_mint_is_a_token_sort_on_every_route() {
    let definition = load(UNHOOKED_MINT_DEFINITION);
    let loaded = term(&definition, r#"\dv{SortMInt{Sort8{}}}("256p8")"#);
    let BuiltinResult::Value(built) = evaluated(&definition, &string_to("LblString2W", "256p8"))
    else {
        panic!("String2W(\"256p8\") is not a value");
    };
    assert_eq!(built, loaded);
    assert_eq!(value_text(&BuiltinResult::Value(built.clone())), "256p8");
    assert_ne!(built, term(&definition, r#"\dv{SortMInt{Sort8{}}}("0p8")"#));
}

/// A sort hooked `BYTES.Bytes` under another name holds its payload in the encoding of its KORE
/// name, UTF-8 code points, on every route: a loaded literal and a `string2token` value with a
/// byte above `0x7F` are one term. A code point above U+00FF names no byte and is refused at
/// load.
#[test]
fn a_renamed_bytes_sort_has_one_payload_per_value_on_every_route() {
    let definition = load(DEFINITION);
    let loaded = term(&definition, r#"\dv{SortMyBytes{}}("\xe9")"#);
    let BuiltinResult::Value(built) =
        evaluated(&definition, &string_to("LblString2MyBytes", "\\xe9"))
    else {
        panic!("String2MyBytes(\"\\xe9\") is not a value");
    };
    assert_eq!(built, loaded);
    let refused = definition
        .internalize_term(
            &parse_pattern(r#"\dv{SortMyBytes{}}("\u0101")"#).unwrap(),
            &[],
        )
        .expect_err("a code point above U+00FF names no byte");
    assert!(
        refused.to_string().starts_with("Invalid domain value"),
        "{refused}"
    );
}

/// A builtin hook's value is a value of its builtin sort: declared at a sort whose hook gives
/// another kind (a sort hooked `FLOAT.Float` under another name, a token sort for `STRING`'s
/// results), the application is not evaluated.
#[test]
fn a_builtin_value_at_a_sort_of_another_kind_is_not_applicable() {
    let definition = load(DEFINITION);
    for pattern in [
        r#"LblInt2MyFloat{}(\dv{SortInt{}}("3"), \dv{SortInt{}}("53"), \dv{SortInt{}}("11"))"#,
        r#"LblconcatText{}(\dv{SortString{}}("a"), \dv{SortString{}}("b"))"#,
    ] {
        assert_eq!(
            evaluated(&definition, pattern),
            BuiltinResult::NotApplicable,
            "{pattern}"
        );
    }
}

/// Internalization and the library constructor read a text by the hook of its sort: `+07` at a
/// sort hooked `INT.Int` is `7` on both, and a text that names no element, or a sort without
/// domain values, is refused by both.
#[test]
fn internalization_and_the_library_constructor_read_a_text_by_the_hook_of_its_sort() {
    let definition = load(DEFINITION);
    let loaded = term(&definition, r#"\dv{SortMyInt{}}("+07")"#);
    assert_eq!(value_text(&BuiltinResult::Value(loaded.clone())), "7");
    let my_int = Sort::simple("SortMyInt");
    assert_eq!(definition.domain_value(my_int.clone(), "+07"), Ok(loaded));
    assert_eq!(
        definition
            .domain_value(my_int.clone(), "-1p8")
            .map(|term| value_text(&BuiltinResult::Value(term)))
            .map_err(|error| error.to_string()),
        Err(r#"Invalid domain value "-1p8" for sort SortMyInt{}"#.to_owned())
    );
    let word = Sort::application("SortMInt", vec![Sort::simple("Sort8")]);
    assert_eq!(
        definition
            .domain_value(word, "-1p8")
            .map(|term| value_text(&BuiltinResult::Value(term))),
        Ok("255p8".to_owned())
    );
    assert!(
        definition.domain_value(Sort::simple("Sort8"), "1").is_err(),
        "Sort8 has no domain values"
    );
}

/// A builtin hook's value at its builtin's sort is built in that builtin's canonical text: the
/// sum of two integers is the term the literal `03` loads as.
#[test]
fn an_integer_hook_result_is_the_canonical_integer() {
    let definition = load(indoc! {r#"
        []
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-symbol LblplusInt{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), hook{}("INT.add")]
        endmodule []
    "#});
    assert_eq!(
        evaluated(
            &definition,
            r#"LblplusInt{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("2"))"#
        ),
        BuiltinResult::Value(term(&definition, r#"\dv{SortInt{}}("03")"#))
    );
}

/// Renaming a bound `KVar` token builds the fresh token at the token's own sort with the kind the
/// definition gives it: the renamed binder is the token the definition loads with that text.
#[test]
fn a_renamed_kvar_token_is_a_token_of_its_own_sort() {
    let definition = load(indoc! {r#"
        []
        module MAIN
            hooked-sort SortKVar{} [hook{}("KVAR.KVar"), hasDomainValues{}()]
            sort SortExp{} []
            symbol inj{From, To}(From) : To [sortInjection{}()]
            symbol lambda{}(SortKVar{}, SortExp{}) : SortExp{} [constructor{}(), binder{}()]
            hooked-symbol substOne{}(SortExp{}, SortExp{}, SortKVar{}) : SortExp{}
                [function{}(), total{}(), hook{}("SUBSTITUTION.substOne")]
            axiom{R}
                \exists{R}(
                    Val:SortExp{},
                    \equals{SortExp{}, R}(
                        Val:SortExp{},
                        inj{SortKVar{}, SortExp{}}(From:SortKVar{})
                    )
                )
                [subsort{SortKVar{}, SortExp{}}()]
        endmodule []
    "#});
    let variable =
        |name: &str| format!(r#"inj{{SortKVar{{}}, SortExp{{}}}}(\dv{{SortKVar{{}}}}("{name}"))"#);
    let application = format!(
        r#"substOne{{}}(lambda{{}}(\dv{{SortKVar{{}}}}("y"), {}), {}, \dv{{SortKVar{{}}}}("x"))"#,
        variable("x"),
        variable("y"),
    );
    let expected = format!(
        r#"lambda{{}}(\dv{{SortKVar{{}}}}("y0"), {})"#,
        variable("y")
    );
    assert_eq!(
        evaluated(&definition, &application),
        BuiltinResult::Value(term(&definition, &expected))
    );
}
