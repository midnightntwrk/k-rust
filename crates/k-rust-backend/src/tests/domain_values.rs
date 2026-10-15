//! The construction routes of domain values: each builds the canonical text of the element it
//! denotes, with the kind its sort's hook gives in the loaded definition, and builds no text that
//! names no element of its sort.

use indoc::indoc;
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    builtin::{
        BuiltinResult, UnsupportedHookReason, evaluate, evaluate_declared, evaluate_in_definition,
    },
    definition::BackendDefinition,
    evaluation::{EvaluationMode, with_evaluation},
    term::{FunctionType, Sort, SymbolType, Term, TermKind},
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

/// At a sort named `SortBytes` whose payload is one byte per code point, a code point above
/// U+00FF names no byte of the `Bytes` kind, so a partial `String2Token` there is undefined; at
/// such a sort declared without the hook, a token sort, the text names a token that the payload
/// encoding cannot hold, and the application is not decided, never undefined.
#[test]
fn a_code_point_beyond_a_byte_at_sort_bytes_is_undefined_only_for_the_bytes_kind() {
    let source = |declaration: &str| {
        format!(
            r#"[]
            module MAIN
                hooked-sort SortString{{}} [hook{{}}("STRING.String"), hasDomainValues{{}}()]
                {declaration}
                hooked-symbol LblString2Bytes{{}}(SortString{{}}) : SortBytes{{}}
                    [function{{}}(), hook{{}}("STRING.string2token")]
            endmodule []"#
        )
    };
    let application = string_to("LblString2Bytes", "\\u0101");
    assert_eq!(
        evaluated(
            &load(&source(
                r#"hooked-sort SortBytes{} [hook{}("BYTES.Bytes"), hasDomainValues{}()]"#
            )),
            &application
        ),
        BuiltinResult::Bottom
    );
    assert_eq!(
        evaluated(
            &load(&source("sort SortBytes{} [hasDomainValues{}()]")),
            &application
        ),
        BuiltinResult::NotApplicable
    );
}

/// A machine-integer result sort whose width argument is a sort variable has a width that is
/// not known yet, so `String2Token` there is not decided; a closed sort hooked `MINT.MInt` that
/// names no width has no literal, so a partial declaration there is undefined.
#[test]
fn string_to_token_at_a_machine_integer_sort_of_unknown_width_is_not_decided() {
    let definition = load(indoc! {r#"
        []
        module MAIN
            hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
            hooked-sort SortMInt{S} [hook{}("MINT.MInt"), hasDomainValues{}()]
            sort SortFoo{} []
            hooked-symbol LblString2W{S}(SortString{}) : SortMInt{S}
                [function{}(), hook{}("STRING.string2token")]
        endmodule []
    "#});
    let application = |width: Sort| {
        Term::application(
            definition.symbols()["LblString2W"].clone(),
            vec![width],
            vec![Term::string("1p8")],
        )
    };
    let outcome = |term: &Term| {
        evaluate_in_definition(term, &definition)
            .expect("evaluation should not stop")
            .expect("evaluation should not fail")
    };
    assert_eq!(
        outcome(&application(Sort::Variable("S".into()))),
        BuiltinResult::NotApplicable
    );
    assert_eq!(
        outcome(&application(Sort::simple("SortFoo"))),
        BuiltinResult::Bottom
    );
}

/// A KORE string pattern is a value of `SortString`, validated for the kind the definition
/// gives that sort as a `\dv` of it is: at a `SortString` hooked `INT.Int`, `"07"` is `7` and
/// `"abc"` is refused.
#[test]
fn a_string_pattern_is_validated_for_the_kind_of_sort_string() {
    let definition = load(indoc! {r#"
        []
        module MAIN
            hooked-sort SortString{} [hook{}("INT.Int"), hasDomainValues{}()]
        endmodule []
    "#});
    assert_eq!(
        value_text(&BuiltinResult::Value(term(&definition, r#""07""#))),
        "7"
    );
    let refused = definition
        .internalize_term(&parse_pattern(r#""abc""#).unwrap(), &[])
        .expect_err("abc is no integer");
    assert!(
        refused.to_string().starts_with("Invalid domain value"),
        "{refused}"
    );
}

/// A definition whose `SortFloat` and a user sort `SortMyFloat` are hooked `FLOAT.Float`, with
/// `String2Token` functions into both (`total` and partial) and the Float addition.
const FLOAT_DEFINITION: &str = indoc! {r#"
    []
    module MAIN
        hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
        hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
        hooked-sort SortFloat{} [hook{}("FLOAT.Float"), hasDomainValues{}()]
        hooked-sort SortMyFloat{} [hook{}("FLOAT.Float"), hasDomainValues{}()]
        hooked-symbol LblString2Float{}(SortString{}) : SortFloat{}
            [function{}(), total{}(), hook{}("STRING.string2token")]
        hooked-symbol LblString2FloatPartial{}(SortString{}) : SortFloat{}
            [function{}(), hook{}("STRING.string2token")]
        hooked-symbol LblString2MyFloat{}(SortString{}) : SortMyFloat{}
            [function{}(), total{}(), hook{}("STRING.string2token")]
        hooked-symbol Lbl'Unds'plusFloat'Unds'{}(SortFloat{}, SortFloat{}) : SortFloat{}
            [function{}(), total{}(), hook{}("FLOAT.add")]
        hooked-symbol Lbl'UndsEqlsEqls'Float'Unds'{}(SortFloat{}, SortFloat{}) : SortBool{}
            [function{}(), total{}(), hook{}("FLOAT.eq")]
    endmodule []
"#};

/// The same declarations with `SortFloat` declared without its hook: a token sort.
const UNHOOKED_FLOAT_DEFINITION: &str = indoc! {r#"
    []
    module MAIN
        hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
        hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
        sort SortFloat{} [hasDomainValues{}()]
        hooked-symbol LblString2Float{}(SortString{}) : SortFloat{}
            [function{}(), total{}(), hook{}("STRING.string2token")]
        hooked-symbol Lbl'Unds'plusFloat'Unds'{}(SortFloat{}, SortFloat{}) : SortFloat{}
            [function{}(), total{}(), hook{}("FLOAT.add")]
        hooked-symbol Lbl'UndsEqlsEqls'Float'Unds'{}(SortFloat{}, SortFloat{}) : SortBool{}
            [function{}(), total{}(), hook{}("FLOAT.eq")]
    endmodule []
"#};

fn float_text(definition: &BackendDefinition, sort: &str, text: &str) -> String {
    value_text(&BuiltinResult::Value(term(
        definition,
        &format!(r#"\dv{{{sort}{{}}}}("{text}")"#),
    )))
}

/// Internalization reads a Float literal by the hook of its sort, at `SortFloat` and at a user
/// sort hooked `FLOAT.Float`: every spelling of one value is the canonical text of that value,
/// in binary64 and in a format the hooks do not compute, and so is the library constructor's.
#[test]
fn float_literals_load_as_the_canonical_text_of_their_value() {
    let definition = load(FLOAT_DEFINITION);
    for sort in ["SortFloat", "SortMyFloat"] {
        for text in [
            "2.0",
            "0.2e1",
            "2.0d",
            "2.0p53x11",
            "2.0p053x011",
            "2.00000000000000001",
        ] {
            assert_eq!(
                float_text(&definition, sort, text),
                "2.0000000000000000e+00p53x11",
                "{sort} {text}"
            );
        }
        for text in ["1.0p11x5", "1.0001p11x5"] {
            assert_eq!(
                float_text(&definition, sort, text),
                "1e0p11x5",
                "{sort} {text}"
            );
        }
        assert_eq!(float_text(&definition, sort, "NaNd"), "NaNp53x11");
        assert_ne!(
            float_text(&definition, sort, "0.0"),
            float_text(&definition, sort, "-0.0")
        );
        assert_ne!(
            float_text(&definition, sort, "0.5"),
            float_text(&definition, sort, "0.5f")
        );
    }
    assert_eq!(
        term(&definition, r#"\dv{SortFloat{}}("1.00")"#),
        term(&definition, r#"\dv{SortFloat{}}("1.0")"#)
    );
    assert_eq!(
        definition.domain_value(Sort::simple("SortFloat"), "0.2e1"),
        Ok(term(&definition, r#"\dv{SortFloat{}}("2.0")"#))
    );
}

/// A sort named `SortFloat` declared without the `FLOAT.Float` hook is a token sort: its texts
/// `1.0` and `1.00` are two values, loaded as written.
#[test]
fn an_unhooked_sort_named_sort_float_keeps_its_tokens_text() {
    let definition = load(UNHOOKED_FLOAT_DEFINITION);
    assert_eq!(float_text(&definition, "SortFloat", "1.00"), "1.00");
    assert_ne!(
        term(&definition, r#"\dv{SortFloat{}}("1.00")"#),
        term(&definition, r#"\dv{SortFloat{}}("1.0")"#)
    );
}

fn load_error(definition: &BackendDefinition, pattern: &str) -> String {
    definition
        .internalize_term(&parse_pattern(pattern).unwrap(), &[])
        .map(|term| format!("loaded {term:?}"))
        .unwrap_or_else(|error| error.to_string())
}

/// A Float text that names no element (outside FLOAT-SYNTAX, or a format field of 0) is an
/// invalid domain value; one that names a value k-rust does not build (a format field of 1, a
/// canonical text beyond the bound) is the resource refusal.
#[test]
fn float_literals_that_name_no_element_or_exceed_a_bound_are_refused_at_load() {
    let definition = load(FLOAT_DEFINITION);
    for text in ["inf", "1.0p0x11", "-.5"] {
        let error = load_error(&definition, &format!(r#"\dv{{SortFloat{{}}}}("{text}")"#));
        assert!(error.starts_with("Invalid domain value"), "{text}: {error}");
    }
    for text in [
        "1.0p1x8",
        "1.0p8x1",
        "0.1p99999999999x8",
        "1e-1000000p53x32",
    ] {
        let error = load_error(&definition, &format!(r#"\dv{{SortMyFloat{{}}}}("{text}")"#));
        assert!(
            error.starts_with("Domain value") && error.contains("resource bound"),
            "{text}: {error}"
        );
    }
}

/// `STRING.string2token` into a sort hooked `FLOAT.Float` builds the canonical text of the value
/// its text names, the term the literal loads as.
#[test]
fn string_to_float_builds_the_canonical_text_of_its_value() {
    let definition = load(FLOAT_DEFINITION);
    assert_eq!(
        evaluated(&definition, &string_to("LblString2Float", "0.2e1")),
        BuiltinResult::Value(term(&definition, r#"\dv{SortFloat{}}("2.0")"#))
    );
    assert_eq!(
        value_text(&evaluated(
            &definition,
            &string_to("LblString2MyFloat", "1.0001p11x5")
        )),
        "1e0p11x5"
    );
}

/// A text that names no Float has no value the definition gives; one that names a value k-rust
/// does not build is the resource refusal whatever the declaration's totality, never undefined.
#[test]
fn string_to_float_beyond_a_bound_is_too_large_whatever_its_totality() {
    let definition = load(FLOAT_DEFINITION);
    assert!(matches!(
        evaluated(&definition, &string_to("LblString2Float", "inf")),
        BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified { .. })
    ));
    assert_eq!(
        evaluated(
            &definition,
            &string_to("LblString2FloatPartial", "1.0p0x11")
        ),
        BuiltinResult::Bottom
    );
    for symbol in ["LblString2Float", "LblString2FloatPartial"] {
        for text in ["0.1p99999999999x8", "1.0p1x8", "1.0p8x1"] {
            let result = evaluated(&definition, &string_to(symbol, text));
            assert!(
                matches!(
                    result,
                    BuiltinResult::Unsupported(UnsupportedHookReason::ResultTooLarge { .. })
                ),
                "{symbol}({text}): {result:?}"
            );
        }
    }
}

/// A Float hook's value is checked against the kind the definition gives its sort: at a
/// `SortFloat` hooked `FLOAT.Float` the sum is the canonical value the literal `2.0` loads as;
/// at an unhooked `SortFloat` (a token sort) the hook's value is no value of the sort, and the
/// application is not evaluated.
#[test]
fn a_float_hook_result_is_checked_against_the_kind_of_its_sort() {
    let sum = r#"Lbl'Unds'plusFloat'Unds'{}(\dv{SortFloat{}}("1.0"), \dv{SortFloat{}}("1.00"))"#;
    let definition = load(FLOAT_DEFINITION);
    assert_eq!(
        evaluated(&definition, sum),
        BuiltinResult::Value(term(&definition, r#"\dv{SortFloat{}}("2.0")"#))
    );
    assert_eq!(
        evaluated(&load(UNHOOKED_FLOAT_DEFINITION), sum),
        BuiltinResult::NotApplicable
    );
}

/// The Float hooks read only Float values: at a `SortFloat` hooked `FLOAT.Float`, `1.0 ==Float
/// 1.00` is `true`; at an unhooked `SortFloat`, whose tokens `1.0` and `1.00` are two values of a
/// token sort, the comparison is not evaluated, although its result is a Boolean.
#[test]
fn float_hooks_read_no_token_of_an_unhooked_sort_float() {
    let equal =
        r#"Lbl'UndsEqlsEqls'Float'Unds'{}(\dv{SortFloat{}}("1.0"), \dv{SortFloat{}}("1.00"))"#;
    let definition = load(FLOAT_DEFINITION);
    assert_eq!(
        evaluated(&definition, equal),
        BuiltinResult::Value(term(&definition, r#"\dv{SortBool{}}("true")"#))
    );
    assert_eq!(
        evaluated(&load(UNHOOKED_FLOAT_DEFINITION), equal),
        BuiltinResult::NotApplicable
    );
}

/// `INT.add` at its natural sorts, at a token sort and at a sort hooked `INT.Int` under another
/// name, `FLOAT.sign`, and `STRING.token2string` of a token.
const DECLARED_DEFINITION: &str = indoc! {r#"
    []
    module MAIN
        hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
        hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
        hooked-sort SortFloat{} [hook{}("FLOAT.Float"), hasDomainValues{}()]
        hooked-sort SortMyInt{} [hook{}("INT.Int"), hasDomainValues{}()]
        sort SortTok{} [hasDomainValues{}()]
        sort SortId{} [hasDomainValues{}()]
        hooked-symbol LbladdInt{}(SortInt{}, SortInt{}) : SortInt{}
            [function{}(), total{}(), hook{}("INT.add")]
        hooked-symbol LbladdTok{}(SortInt{}, SortInt{}) : SortTok{}
            [function{}(), total{}(), hook{}("INT.add")]
        hooked-symbol LbladdMyInt{}(SortMyInt{}, SortMyInt{}) : SortMyInt{}
            [function{}(), total{}(), hook{}("INT.add")]
        hooked-symbol LblsignFloat{}(SortFloat{}) : SortBool{}
            [function{}(), total{}(), hook{}("FLOAT.sign")]
        hooked-symbol LblId2String{}(SortId{}) : SortString{}
            [function{}(), total{}(), hook{}("STRING.token2string")]
    endmodule []
"#};

/// `evaluate_declared` over a loaded definition's own declarations is the evaluation entry for
/// the hooks those declarations decide: in both evaluation modes it gives every application below
/// the outcome the entry gives it in the definition. The applications reach each outcome: a value, no value of the declared sort, a
/// value only an execution chooses, a value the definition does not determine, `\bottom`, and a
/// value beyond a bound.
#[test]
fn evaluate_declared_agrees_with_the_entry() {
    let int = |text: &str| format!(r#"\dv{{SortInt{{}}}}("{text}")"#);
    let float = |text: &str| format!(r#"\dv{{SortFloat{{}}}}("{text}")"#);
    let cases = [
        (
            DEFINITION,
            vec![
                string_to("LblString2MyInt", "07"),
                string_to("LblString2MyInt", "abc"),
                string_to("LblString2MyIntPartial", "abc"),
                string_to("LblString2Word", "-1p8"),
                string_to("LblString2Id", "_42"),
                string_to("LblString2Wide", "-1p33554432"),
                format!(
                    "LblInt2MyFloat{{}}({}, {}, {})",
                    int("3"),
                    int("53"),
                    int("11")
                ),
                r#"LblconcatText{}(\dv{SortString{}}("a"), \dv{SortString{}}("b"))"#.to_owned(),
            ],
        ),
        (
            FLOAT_DEFINITION,
            vec![
                format!(
                    r"Lbl'Unds'plusFloat'Unds'{{}}({}, {})",
                    float("1.0"),
                    float("1.00")
                ),
                format!(
                    r"Lbl'Unds'plusFloat'Unds'{{}}({}, {})",
                    float("1.0f"),
                    float("1.0")
                ),
            ],
        ),
        (
            UNHOOKED_FLOAT_DEFINITION,
            vec![format!(
                r"Lbl'Unds'plusFloat'Unds'{{}}({}, {})",
                float("1.0"),
                float("1.00")
            )],
        ),
        (
            DECLARED_DEFINITION,
            vec![
                format!("LbladdInt{{}}({}, {})", int("1"), int("2")),
                format!("LbladdTok{{}}({}, {})", int("1"), int("2")),
                r#"LbladdMyInt{}(\dv{SortMyInt{}}("1"), \dv{SortMyInt{}}("2"))"#.to_owned(),
                format!("LblsignFloat{{}}({})", float("NaN")),
                format!("LblsignFloat{{}}({})", float("-1.0")),
                r#"LblId2String{}(\dv{SortId{}}("x"))"#.to_owned(),
            ],
        ),
    ];
    let mut outcomes = std::collections::BTreeSet::new();
    for (source, patterns) in cases {
        let definition = load(source);
        for pattern in patterns {
            let application = term(&definition, &pattern);
            let TermKind::Application {
                symbol, arguments, ..
            } = application.kind()
            else {
                panic!("{pattern} is no application");
            };
            let hook = symbol.attributes.hook.as_deref().unwrap();
            let total = symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Total);
            for mode in [EvaluationMode::Proof, EvaluationMode::Execution] {
                let entry =
                    with_evaluation(mode, || evaluate_in_definition(&application, &definition))
                        .unwrap()
                        .unwrap();
                let declared = evaluate_declared(
                    hook,
                    arguments,
                    &application.sort(),
                    total,
                    &definition,
                    mode,
                    None,
                )
                .unwrap()
                .unwrap();
                assert_eq!(declared, entry, "{pattern} in {mode:?}");
                outcomes.insert(match (mode, &declared) {
                    (_, BuiltinResult::Value(_)) => "value",
                    (_, BuiltinResult::NotApplicable) => "no value of the sort",
                    (
                        EvaluationMode::Proof,
                        BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified {
                            defined: true,
                            ..
                        }),
                    ) if hook.starts_with("FLOAT.") => "chosen only in an execution",
                    (_, BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified { .. })) => {
                        "not determined"
                    }
                    (_, BuiltinResult::Bottom) => "undefined",
                    (
                        _,
                        BuiltinResult::Unsupported(UnsupportedHookReason::ResultTooLarge {
                            ..
                        }),
                    ) => "beyond a bound",
                    (_, other) => panic!("{pattern}: {other:?}"),
                });
            }
        }
    }
    assert_eq!(outcomes.len(), 6, "{outcomes:?}");

    // A hook whose evaluator reads more of a loaded definition than its declarations (here
    // `KEQUAL`, which reads the sort graph) is not evaluated over the declarations alone.
    let definition = load(DECLARED_DEFINITION);
    assert_eq!(
        evaluate_declared(
            "KEQUAL.eq",
            &[Term::int(1), Term::int(1)],
            &Sort::builtin(k_rust_kore::names::BuiltinSort::Bool),
            true,
            &definition,
            EvaluationMode::Proof,
            None,
        ),
        Ok(Ok(BuiltinResult::NotApplicable))
    );
}

/// A caller's bound on the results it uses refuses a larger result before it is built, and the
/// evaluation entry, which has none, still computes it: `2 ^Int (2^20)` and a `replaceAll` of
/// 2^17 + 1 bytes are too large for a bound of 2^20 bits and computed by the entry.
#[test]
fn a_result_bound_refuses_a_larger_result_before_it_is_built() {
    let definition = load(DECLARED_DEFINITION);
    let bound = Some(1 << 20);
    let declared = |hook: &str, arguments: &[Term], sort: k_rust_kore::names::BuiltinSort| {
        evaluate_declared(
            hook,
            arguments,
            &Sort::builtin(sort),
            false,
            &definition,
            EvaluationMode::Proof,
            bound,
        )
        .unwrap()
        .unwrap()
    };
    let too_large = |result: &BuiltinResult| {
        matches!(
            result,
            BuiltinResult::Unsupported(UnsupportedHookReason::ResultTooLarge { .. })
        )
    };
    let power = [Term::int(2), Term::int(1 << 20)];
    assert!(too_large(&declared(
        "INT.pow",
        &power,
        k_rust_kore::names::BuiltinSort::Int
    )));
    let small = declared(
        "INT.pow",
        &[Term::int(2), Term::int(10)],
        k_rust_kore::names::BuiltinSort::Int,
    );
    assert_eq!(small, BuiltinResult::Value(Term::int(1024)));
    let haystack = Term::string("a".repeat(1 << 9));
    let replaced = |replacement: usize| {
        declared(
            "STRING.replaceAll",
            &[
                haystack.clone(),
                Term::string("a"),
                Term::string("a".repeat(replacement)),
            ],
            k_rust_kore::names::BuiltinSort::String,
        )
    };
    assert!(matches!(replaced(1 << 8), BuiltinResult::Value(_)));
    assert!(too_large(&replaced((1 << 8) + 1)));
    // `^%Int` is refused when its work exceeds a sixteenth of the bound squared: a 1,024-bit
    // exponent with a 65,536-bit modulus is 2^42 bit operations, above 2^36, and a 15-bit one is
    // below it.
    let powmod = |exponent: u32| {
        [
            Term::int(3),
            Term::int((num_bigint::BigInt::from(1) << exponent) - 1),
            Term::int((num_bigint::BigInt::from(1) << 65_535u32) + 1),
        ]
    };
    assert_eq!(
        declared(
            "INT.powmod",
            &powmod(1024),
            k_rust_kore::names::BuiltinSort::Int
        ),
        BuiltinResult::NotApplicable
    );
    assert!(matches!(
        declared(
            "INT.powmod",
            &powmod(15),
            k_rust_kore::names::BuiltinSort::Int
        ),
        BuiltinResult::Value(_)
    ));
    // Without a bound, as in the evaluation entry, both results are computed.
    let unbounded = evaluate_declared(
        "INT.pow",
        &power,
        &Sort::builtin(k_rust_kore::names::BuiltinSort::Int),
        false,
        &definition,
        EvaluationMode::Proof,
        None,
    )
    .unwrap()
    .unwrap();
    assert!(
        matches!(unbounded, BuiltinResult::Value(_)),
        "{unbounded:?}"
    );
}
