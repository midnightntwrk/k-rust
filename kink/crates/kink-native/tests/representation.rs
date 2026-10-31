//! Clause-level representation premises and the pre-existing fixture admission boundary.

#[path = "../../../testdata/k/passage.rs"]
mod passage;
#[path = "../../../testdata/k/support.rs"]
mod support;

use std::{path::Path, sync::Arc};

use k_rust::{
    backend::{Backend, BackendOptions},
    definition::{Attributes, Definition, FlatModule, Sentence},
    kast::{Sort, Term},
    kompile::CompileOptions,
    kore::{
        ast::Pattern,
        parser::{parse_definition, parse_pattern},
    },
};
use kink_native::{
    NativeValidator,
    bridge::validate_test_initial_state,
    representation::{
        RepresentationClause, RepresentationError, validate_representation,
        validate_representation_ast, validate_representation_kore,
    },
};

const DECLARATIONS: &str = r#"
 hooked-sort SortFloat{} [hook{}("FLOAT.Float")]
 hooked-sort SortMInt{} [hook{}("MINT.MInt")]
 hooked-sort SortBool{} [hook{}("BOOL.Bool")]
 hooked-sort SortInt{} [hook{}("INT.Int")]
 hooked-sort SortOtherInt{} [hook{}("INT.Int")]
 hooked-sort SortText{} [hook{}("STRING.String")]
 sort SortId{} []
"#;

fn kore(declarations: &str, sentences: &str) -> k_rust::kore::ast::Definition {
    parse_definition(&format!(
        "[] module MAIN {declarations} {sentences} endmodule []"
    ))
    .expect("test KORE parses")
}

/// `definition` with the payload of every top-level domain value spelled `RAW` (an axiom's
/// pattern or an alias body) replaced by `bytes`. Re-pin R0a (finding E-08; k-rust 4a3b0b099):
/// at 501f18b9 every KORE reader stores a String literal as the UTF-8 of its code points, so a
/// String payload that is not UTF-8 reaches the representation scan only in a host-built
/// definition AST.
fn with_raw_payload(
    mut definition: k_rust::kore::ast::Definition,
    bytes: &[u8],
) -> k_rust::kore::ast::Definition {
    use k_rust::kore::ast::Sentence as KoreSentence;
    let mut replaced = 0;
    for module in &mut definition.modules {
        for sentence in &mut module.sentences {
            let (KoreSentence::Axiom { pattern, .. }
            | KoreSentence::AliasDeclaration { right: pattern, .. }) = sentence
            else {
                continue;
            };
            if let Pattern::DomainValue { value, .. } = pattern.as_mut()
                && *value == *"RAW"
            {
                *value = bytes.to_vec().into();
                replaced += 1;
            }
        }
    }
    assert_eq!(replaced, 1, "one RAW payload");
    definition
}

fn loaded(token: Option<&str>) -> Definition {
    let local_sentences = token
        .map(|token| {
            Arc::new(Sentence::Rule {
                body: Term::Token {
                    token: token.into(),
                    sort: Sort::new("Text"),
                },
                requires: Term::variable("REQUIRES"),
                ensures: Term::variable("ENSURES"),
                attributes: Attributes::new(std::collections::BTreeMap::from([
                    ("UNIQUE_ID".into(), serde_json::json!("loaded-id")),
                    (
                        "org.kframework.attributes.Source".into(),
                        serde_json::json!("source.k"),
                    ),
                ])),
            })
        })
        .into_iter()
        .collect();
    Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: vec![],
            local_sentences,
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    }
}

#[test]
fn every_literal_axiom_kind_and_nested_position_is_scanned() {
    for (sort, hook, value, clause) in [
        ("SortFloat", "FLOAT.Float", "1.0", None),
        ("SortMInt", "MINT.MInt", "1p8", None),
        (
            "SortOtherInt",
            "INT.Int",
            "007",
            Some(RepresentationClause::RenamedIntLiteral),
        ),
    ] {
        let declarations = format!(
            r#"hooked-sort {sort}{{}} [hook{{}}("{hook}")] symbol wrap{{}}({sort}{{}}):{sort}{{}} [hook{{}}("FLOAT.abs")]"#
        );
        for attributes in [
            r#"UNIQUE'Unds'ID{}("rule-id")"#,
            r#"simplification{}(), UNIQUE'Unds'ID{}("lemma-id")"#,
            r#"function{}(), UNIQUE'Unds'ID{}("equation-id")"#,
            "",
        ] {
            for pattern in [
                format!(r#"\dv{{{sort}{{}}}}("{value}")"#),
                format!(r#"wrap{{}}(\dv{{{sort}{{}}}}("{value}"))"#),
                format!(
                    r#"\equals{{{sort}{{}},{sort}{{}}}}(\dv{{{sort}{{}}}}("{value}"), X:{sort}{{}})"#
                ),
            ] {
                let definition = kore(
                    &declarations,
                    &format!("axiom{{}} {pattern} [{attributes}]"),
                );
                let result = validate_representation_ast(&definition, None, &loaded(None));
                let Some(clause) = clause else {
                    assert!(result.is_ok(), "{pattern} [{attributes}]: {result:?}");
                    continue;
                };
                let finding = result.unwrap_err();
                assert_eq!(finding.clause, clause);
                assert_eq!(finding.sort, sort);
                assert!(finding.source.contains("MAIN sentence"));
                assert!(finding.to_string().contains(clause.reason()));
            }
        }
        let definition = kore(&declarations, &format!("axiom{{}} X:{sort}{{}} []"));
        assert!(validate_representation_ast(&definition, None, &loaded(None)).is_ok());
        let macro_definition = kore(
            "",
            &format!(r#"axiom{{}} \dv{{{sort}{{}}}}("{value}") [UNIQUE'Unds'ID{{}}("macro-id")]"#),
        );
        let result =
            validate_representation_ast(&definition, Some(&macro_definition), &loaded(None));
        let Some(clause) = clause else {
            assert!(result.is_ok(), "{sort} macro: {result:?}");
            continue;
        };
        let finding = result.unwrap_err();
        assert_eq!(finding.clause, clause);
        assert_eq!(finding.sentence_unique_id.as_deref(), Some("macro-id"));
    }
}

#[test]
fn renamed_hooked_sorts_and_collection_key_literals_are_scanned() {
    for (hook, value, clause) in [
        ("FLOAT.Float", "1", None),
        ("MINT.MInt", "1", None),
        (
            "INT.Int",
            "01",
            Some(RepresentationClause::RenamedIntLiteral),
        ),
    ] {
        let declarations = format!(
            r#"hooked-sort SortRenamed{{}} [hook{{}}("{hook}")] sort SortMap{{}} [] symbol item{{}}(SortRenamed{{}}):SortMap{{}} []"#
        );
        for head in ["item", "setItem"] {
            let definition = kore(
                &declarations,
                &format!(r#"axiom{{}} {head}{{}}(\dv{{SortRenamed{{}}}}("{value}")) []"#),
            );
            let result = validate_representation_ast(&definition, None, &loaded(None));
            match clause {
                None => assert!(result.is_ok(), "{hook} {head}: {result:?}"),
                Some(clause) => assert_eq!(result.unwrap_err().clause, clause, "{hook} {head}"),
            }
        }
    }
}

#[test]
fn unapplied_token_creators_are_refused_only_by_the_specified_result_clause() {
    for result in [
        "SortFloat{}",
        "SortMInt{}",
        "SortBool{}",
        "SortOtherInt{}",
        "S",
        "SortId{S}",
    ] {
        let definition = kore(
            DECLARATIONS,
            &format!(
                r#"hooked-symbol parse{{S}}(SortText{{}}):{result} [hook{{}}("STRING.string2token")]"#
            ),
        );
        assert_eq!(
            validate_representation_ast(&definition, None, &loaded(None))
                .unwrap_err()
                .clause,
            RepresentationClause::TokenCreator,
            "{result}"
        );
    }
    for result in ["SortId{}", "SortInt{}"] {
        let definition = kore(
            DECLARATIONS,
            &format!(
                r#"hooked-symbol parse{{}}(SortText{{}}):{result} [hook{{}}("STRING.string2token")]"#
            ),
        );
        assert!(
            validate_representation_ast(&definition, None, &loaded(None)).is_ok(),
            "{result}"
        );
    }
    // VI-T13's nonstandard result signatures are an explicitly open upstream residue.
    let definition = kore(
        DECLARATIONS,
        r#"hooked-symbol relabel{}(SortBool{}):SortFloat{} [hook{}("KEQUAL.ite")]"#,
    );
    assert!(validate_representation_ast(&definition, None, &loaded(None)).is_ok());
}

#[test]
fn renamed_int_literals_require_canonical_decimal_but_sort_int_is_unchanged() {
    for spelling in [
        "0",
        "1",
        "-1",
        "123456789123456789123456789",
        "-123456789123456789123456789",
    ] {
        let definition = kore(
            DECLARATIONS,
            &format!(r#"axiom{{}} \dv{{SortOtherInt{{}}}}("{spelling}") []"#),
        );
        assert!(
            validate_representation_ast(&definition, None, &loaded(None)).is_ok(),
            "{spelling}"
        );
    }
    for spelling in ["00", "01", "-0", "+1", " 1", "1 ", "", "1.0", "a"] {
        let definition = kore(
            DECLARATIONS,
            &format!(r#"axiom{{}} \dv{{SortOtherInt{{}}}}("{spelling}") []"#),
        );
        assert_eq!(
            validate_representation_ast(&definition, None, &loaded(None))
                .unwrap_err()
                .clause,
            RepresentationClause::RenamedIntLiteral,
            "{spelling}"
        );
        let definition = kore(
            DECLARATIONS,
            &format!(r#"axiom{{}} \dv{{SortInt{{}}}}("{spelling}") []"#),
        );
        assert!(validate_representation_ast(&definition, None, &loaded(None)).is_ok());
    }
}

#[test]
fn string_spellings_check_raw_loaded_kast_and_both_decoders() {
    let definition = kore(DECLARATIONS, "");
    for token in [
        r#""\101""#,
        r#""\xe9""#,
        r#""\xc3\xa9""#,
        r#""\q""#,
        r#""\x""#,
        r#""\uD800""#,
        r#""\U00110000""#,
        "unquoted",
        r#""\"#,
    ] {
        let finding =
            validate_representation_ast(&definition, None, &loaded(Some(token))).unwrap_err();
        assert_eq!(
            finding.clause,
            RepresentationClause::StringSpelling,
            "{token}"
        );
        assert_eq!(finding.sort, "SortText");
        assert_eq!(finding.sentence_unique_id.as_deref(), Some("loaded-id"));
        assert_eq!(finding.source, "source.k");
    }
    for token in [
        r#""\x41""#,
        "\"é\"",
        r#""\u00e9""#,
        r#""\U0001f642""#,
        r#""\\x80""#,
        r#""\\101""#,
        r#""\n\r\t\f\"\\""#,
        "\"\"",
    ] {
        assert!(
            validate_representation_ast(&definition, None, &loaded(Some(token))).is_ok(),
            "{token}"
        );
    }
    // Loaded sorts outside the compiled main-module closure still belong to the G-S scan.
    let mut source_only = loaded(Some(r#""\101""#));
    source_only.modules[0]
        .local_sentences
        .push(Arc::new(Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new("Text"),
            attributes: Attributes::new(std::collections::BTreeMap::from([(
                "hook".into(),
                serde_json::json!("STRING.String"),
            )])),
        }));
    assert_eq!(
        validate_representation_ast(&kore("", ""), None, &source_only)
            .unwrap_err()
            .clause,
        RepresentationClause::StringSpelling
    );
    // Bytes is outside G-S; identical spelling at a non-String sort remains admitted.
    let definition = kore(r#"hooked-sort SortText{} [hook{}("BYTES.Bytes")]"#, "");
    assert!(validate_representation_ast(&definition, None, &loaded(Some(r#""\xe9""#))).is_ok());
}

fn input_backend() -> Backend {
    let text = format!(
        r#"[] module MAIN {DECLARATIONS}
        symbol generic{{S}}():S [function{{}}(), functional{{}}(), total{{}}()]
        symbol userF{{}}(SortInt{{}}):SortFloat{{}} [function{{}}(), functional{{}}(), total{{}}()]
        symbol userM{{}}(SortInt{{}}):SortMInt{{}} [function{{}}(), functional{{}}(), total{{}}()]
        hooked-symbol int2float{{}}(SortInt{{}},SortInt{{}},SortInt{{}}):SortFloat{{}} [function{{}}(), functional{{}}(), total{{}}(), hook{{}}("FLOAT.int2float")]
        endmodule []"#
    );
    Backend::new(&text, "MAIN", BackendOptions::default()).expect("input test backend")
}

#[test]
fn input_mint_and_non_float_namespace_results_are_refused_at_any_polarity() {
    let mut backend = input_backend();
    for syntax in [
        r#"\dv{SortMInt{}}("1p8")"#,
        r#"userF{}(\dv{SortInt{}}("1"))"#,
        r#"userM{}(\dv{SortInt{}}("1"))"#,
        "generic{SortFloat{}}()",
        "generic{SortMInt{}}()",
    ] {
        let node = parse_pattern(syntax).unwrap();
        for state in [
            node.clone(),
            Pattern::Not {
                sort: k_rust::kompile::initial_configuration::kore_sort("SortInt"),
                argument: Box::new(node),
            },
        ] {
            assert!(
                validate_test_initial_state(&mut backend, &state).is_err(),
                "{syntax}"
            );
        }
    }
    for syntax in [
        r#"\dv{SortInt{}}("1")"#,
        r#"int2float{}(\dv{SortInt{}}("1"),\dv{SortInt{}}("53"),\dv{SortInt{}}("11"))"#,
        "X:SortFloat{}",
        "X:SortMInt{}",
        "generic{SortInt{}}()",
    ] {
        let node = parse_pattern(syntax).unwrap();
        assert!(
            validate_test_initial_state(&mut backend, &node).is_ok(),
            "{syntax}"
        );
    }
}

#[test]
fn token_creator_clause_overlaps_the_existing_input_definition_refusal() {
    let text = format!(
        r#"[] module MAIN {DECLARATIONS} hooked-symbol parseF{{}}(SortText{{}}):SortFloat{{}} [function{{}}(), functional{{}}(), total{{}}(), hook{{}}("STRING.string2token")] endmodule []"#
    );
    let definition = parse_definition(&text).unwrap();
    assert_eq!(
        validate_representation_ast(&definition, None, &loaded(None))
            .unwrap_err()
            .clause,
        RepresentationClause::TokenCreator
    );
    let mut backend =
        Backend::new(&text, "MAIN", BackendOptions::default()).expect("token hook backend");
    let failure = validate_test_initial_state(&mut backend, &support::int(1)).unwrap_err();
    assert!(format!("{failure:?}").contains("token hook"));
}

#[test]
fn syntax_axioms_share_the_hook_registry_and_parse_failures_are_typed() {
    let declarations = format!("[] module MAIN {DECLARATIONS} endmodule []");
    let axiom = r#"[] module SYNTAX axiom{} \dv{SortOtherInt{}}("007") [UNIQUE'Unds'ID{}("syntax-id")] endmodule []"#;
    for (syntax, macros) in [(axiom, ""), ("", axiom)] {
        let error =
            validate_representation_kore(&declarations, syntax, macros, &loaded(None)).unwrap_err();
        let RepresentationError::Finding(finding) = error else {
            panic!("expected literal finding")
        };
        assert_eq!(finding.clause, RepresentationClause::RenamedIntLiteral);
        assert_eq!(finding.sentence_unique_id.as_deref(), Some("syntax-id"));
    }
    for (definition, syntax, macros) in [
        ("invalid", "", ""),
        (&declarations, "invalid", ""),
        (&declarations, "", "invalid"),
    ] {
        assert!(matches!(
            validate_representation_kore(definition, syntax, macros, &loaded(None)),
            Err(RepresentationError::KoreParse(_))
        ));
    }
}

/// TB-03 review 1 F1, defence in depth: a compiled String domain value must be UTF-8 text
/// (k-rust's String values are UTF-8). Bytes values remain byte sequences.
///
/// Re-pin R0a (finding E-08; k-rust 4a3b0b099, 3a8af2805, 61fa9e32d): at 501f18b9 the text
/// `\xe9` is U+00E9 (valid UTF-8 `c3 a9`), so the refused rows are built as definition ASTs whose
/// payloads are the old bytes; the texts are admitted.
#[test]
fn review1_compiled_string_domain_values_must_be_utf8() {
    for value in [&[0xe9][..], &[0xc3], b"A\xff"] {
        let definition = with_raw_payload(
            kore(
                DECLARATIONS,
                r#"axiom{} \dv{SortText{}}("RAW") [UNIQUE'Unds'ID{}("byte-id")]"#,
            ),
            value,
        );
        let finding = validate_representation_ast(&definition, None, &loaded(None)).unwrap_err();
        assert_eq!(
            finding.clause,
            RepresentationClause::StringSpelling,
            "{value:?}"
        );
        assert_eq!(finding.sort, "SortText");
        assert_eq!(finding.sentence_unique_id.as_deref(), Some("byte-id"));
    }
    // The first three were refused at 927b9ce6 (E-08): code points at 501f18b9.
    for value in [
        r#"\xe9"#,
        r#"\xc3"#,
        r#"A\xff"#,
        r#"\xc3\xa9"#,
        r#"é"#,
        "A",
        "",
    ] {
        let definition = kore(
            DECLARATIONS,
            &format!(r#"axiom{{}} \dv{{SortText{{}}}}("{value}") []"#),
        );
        assert!(
            validate_representation_ast(&definition, None, &loaded(None)).is_ok(),
            "{value}"
        );
    }
    let definition = kore(
        r#"hooked-sort SortText{} [hook{}("BYTES.Bytes")]"#,
        r#"axiom{} \dv{SortText{}}("\xe9") []"#,
    );
    assert!(validate_representation_ast(&definition, None, &loaded(None)).is_ok());
}

/// TB-03 review 1 minor: alias bodies are unfolded into axioms by the backend, so G-I and the
/// String rule scan them too (kompile emits no alias at 927b9ce6). Float and MInt literals of a
/// hooked sort are admitted there as anywhere else (R3-ADMIT-FLOAT).
#[test]
fn review1_alias_declaration_bodies_are_scanned() {
    for (sort, value, clause) in [
        (
            "SortOtherInt",
            "007",
            RepresentationClause::RenamedIntLiteral,
        ),
        // Re-pin R0a (finding E-08; k-rust 4a3b0b099): the text `\xe9` is U+00E9 at 501f18b9,
        // so the String row's payload is the old byte `e9`, set in the AST (`with_raw_payload`).
        ("SortText", "RAW", RepresentationClause::StringSpelling),
    ] {
        let definition = kore(
            DECLARATIONS,
            &format!(
                r#"alias lit{{}}() : {sort}{{}} where lit{{}}() := \dv{{{sort}{{}}}}("{value}") []"#
            ),
        );
        let definition = if value == "RAW" {
            with_raw_payload(definition, &[0xe9])
        } else {
            definition
        };
        assert_eq!(
            validate_representation_ast(&definition, None, &loaded(None))
                .unwrap_err()
                .clause,
            clause,
            "{sort}"
        );
    }
    let definition = kore(
        DECLARATIONS,
        r#"alias lit{}() : SortOtherInt{} where lit{}() := \dv{SortOtherInt{}}("7") []"#,
    );
    assert!(validate_representation_ast(&definition, None, &loaded(None)).is_ok());
    for (sort, value) in [("SortFloat", "1.0"), ("SortMInt", "1p8")] {
        let definition = kore(
            DECLARATIONS,
            &format!(
                r#"alias lit{{}}() : {sort}{{}} where lit{{}}() := \dv{{{sort}{{}}}}("{value}") []"#
            ),
        );
        let result = validate_representation_ast(&definition, None, &loaded(None));
        assert!(result.is_ok(), "{sort}: {result:?}");
    }
}

/// TB-03 review 1 F2: a test-written value of a renamed INT.Int-hooked sort must be canonical
/// decimal at any polarity; k-rust canonicalizes Int text only at `SortInt`.
#[test]
fn review1_input_renamed_int_values_must_be_canonical_decimal() {
    let mut backend = input_backend();
    for value in ["007", "+7", "-0", "07", " 7", "0x7", "", "-"] {
        let node = parse_pattern(&format!(r#"\dv{{SortOtherInt{{}}}}("{value}")"#)).unwrap();
        for state in [
            node.clone(),
            Pattern::Not {
                sort: k_rust::kompile::initial_configuration::kore_sort("SortInt"),
                argument: Box::new(node),
            },
        ] {
            let failure = validate_test_initial_state(&mut backend, &state).unwrap_err();
            assert!(format!("{failure:?}").contains("noncanonical"), "{value}");
        }
    }
    for syntax in [
        r#"\dv{SortOtherInt{}}("7")"#,
        r#"\dv{SortOtherInt{}}("0")"#,
        r#"\dv{SortOtherInt{}}("-12")"#,
        r#"\dv{SortInt{}}("007")"#,
        r#"\dv{SortInt{}}("+7")"#,
    ] {
        let node = parse_pattern(syntax).unwrap();
        assert!(
            validate_test_initial_state(&mut backend, &node).is_ok(),
            "{syntax}"
        );
    }
}

/// TB-03M: the emitted bare-sentence form is parsed and every sentence in it is scanned; text
/// that is not a sentence list (or that closes the synthetic module) stays refused, and an empty
/// list is admitted.
#[test]
fn audit_vi_t12_macros_text_is_parsed_in_the_emitted_form() {
    let declarations = format!("[] module MAIN {DECLARATIONS} endmodule []");
    let clean = r#"axiom{} \dv{SortInt{}}("1") [UNIQUE'Unds'ID{}("clean-id")]"#;
    let float = r#"axiom{} \dv{SortFloat{}}("1.0") [UNIQUE'Unds'ID{}("macro-id")]"#;
    let mint = r#"axiom{} \dv{SortMInt{}}("1p8") [UNIQUE'Unds'ID{}("macro-id")]"#;
    let renamed = r#"axiom{} \dv{SortOtherInt{}}("007") [UNIQUE'Unds'ID{}("macro-id")]"#;
    // Re-pin R0a (finding E-08; k-rust 4a3b0b099, 3a8af2805): at 501f18b9 the text `\xe9` is
    // U+00E9, valid UTF-8, and no KORE text spells a String payload that is not UTF-8, so this
    // route can no longer reach the String rule: the row moved from the refused rows to the
    // admitted ones. The rule is pinned on definition ASTs in
    // review1_compiled_string_domain_values_must_be_utf8.
    let string = r#"axiom{} \dv{SortText{}}("\xe9") [UNIQUE'Unds'ID{}("macro-id")]"#;
    let alias = r#"alias lit{}() : SortFloat{} where lit{}() := \dv{SortFloat{}}("1.0") [UNIQUE'Unds'ID{}("macro-id")]"#;
    let renamed_alias = r#"alias lit{}() : SortOtherInt{} where lit{}() := \dv{SortOtherInt{}}("007") [UNIQUE'Unds'ID{}("macro-id")]"#;
    for (text, clause) in [
        (
            format!("{renamed}\n"),
            RepresentationClause::RenamedIntLiteral,
        ),
        (
            format!("{clean}\n// comment\n{renamed}"),
            RepresentationClause::RenamedIntLiteral,
        ),
        (
            format!("{clean}\n{renamed}\n"),
            RepresentationClause::RenamedIntLiteral,
        ),
        (
            format!("{renamed_alias}\n"),
            RepresentationClause::RenamedIntLiteral,
        ),
    ] {
        match validate_representation_kore(&declarations, "", &text, &loaded(None)) {
            Err(RepresentationError::Finding(finding)) => {
                assert_eq!(finding.clause, clause, "{text}");
                assert_eq!(
                    finding.sentence_unique_id.as_deref(),
                    Some("macro-id"),
                    "{text}"
                );
            }
            other => panic!("{text}: {other:?}"),
        }
    }
    for text in [
        "",
        "\n",
        " \n\n",
        &format!("{clean}\n"),
        &format!("{clean}\n{clean}"),
        &format!("{clean}\n{string}\n"),
        // Float and MInt literals of a hooked sort are admitted (R3-ADMIT-FLOAT).
        &format!("{float}\n"),
        &format!("{clean}\n{float}\n"),
        &format!("{clean}\n// comment\n{mint}"),
        &format!("{alias}\n"),
    ] {
        assert_eq!(
            validate_representation_kore(&declarations, "", text, &loaded(None)),
            Ok(()),
            "{text:?}"
        );
    }
    for text in [
        "invalid".to_owned(),
        "axiom{}".to_owned(),
        format!("{clean} endmodule []"),
        format!("{clean} endmodule [] module EXTRA {float} endmodule []"),
        format!("{clean} endmodule [] module EXTRA {clean}"),
        format!("{clean} /*"),
        format!("{clean} \"unterminated"),
        format!("module EXTRA {clean} endmodule []"),
    ] {
        assert!(
            matches!(
                validate_representation_kore(&declarations, "", &text, &loaded(None)),
                Err(RepresentationError::KoreParse(_))
            ),
            "{text}"
        );
    }
}

/// R3-ADMIT-FLOAT: G-F and G-M are retired. k-rust builds every domain value of a sort hooked
/// `FLOAT.Float` or `MINT.MInt` as the canonical text of its value on every route
/// (`docs/compatibility.md`, "Domain values"), so two spellings of one element are one term and
/// two elements stay two terms. The gate admits every Float and MInt text, and k-rust's load
/// decides which element it names or refuses it: the Float rows name elements of their format
/// (`1.0`/`1.0e0` one element, `-0.0`, `NaN`, `Infinity`, `1.0p53x11`, `0.5f` others, by k-rust's
/// readings, kink README P-F1 to P-F3). At `SortMInt{}`, a sort hooked `MINT.MInt` with no width
/// argument, load refuses every literal (NoWidth), so those rows show only that the gate does not
/// decide it; at the parametric `SortMInt{Sort8{}}`, `1p8`, `01p8` and `257p8` name one element,
/// and `-1p8` and `255p8` another (in range by domains.md 2880-2882 and 2889; `257p8` by premise
/// P-M1).
#[test]
fn float_and_mint_spellings_are_admitted_where_g_f_refused() {
    for (sort, value) in [
        ("SortFloat", "1.0"),
        ("SortFloat", "1.0e0"),
        ("SortFloat", "-0.0"),
        ("SortFloat", "NaN"),
        ("SortFloat", "Infinity"),
        ("SortFloat", "1.0p53x11"),
        ("SortFloat", "0.5f"),
        ("SortMInt", "1p8"),
        ("SortMInt", "01p8"),
        ("SortMInt", "-1p8"),
    ] {
        let definition = kore(
            DECLARATIONS,
            &format!(r#"axiom{{}} \dv{{{sort}{{}}}}("{value}") []"#),
        );
        let result = validate_representation_ast(&definition, None, &loaded(None));
        assert!(result.is_ok(), "{sort} {value}: {result:?}");
    }
    let width = r#"
 hooked-sort SortMInt{S} [hook{}("MINT.MInt")]
 sort Sort8{} []
"#;
    for value in ["1p8", "01p8", "257p8", "-1p8", "255p8"] {
        let definition = kore(
            width,
            &format!(r#"axiom{{}} \dv{{SortMInt{{Sort8{{}}}}}}("{value}") []"#),
        );
        let result = validate_representation_ast(&definition, None, &loaded(None));
        assert!(result.is_ok(), "SortMInt{{Sort8{{}}}} {value}: {result:?}");
    }
}

/// R3-ADMIT-FLOAT: the passages of k-rust's contract that Float and MInt admission rests on.
/// The first four say that every route stores a Float or MInt domain value as the canonical text
/// of its value, so a respelled literal is the same element in every rule k-rust applies. The
/// others state the readings that decide which element a literal names and which value kompile's
/// fold writes, which K's text does not fix and kink takes on as premises (kink README, premises
/// P-F1 to P-F4 and P-M1, decision D-3): IEEE roundTiesToEven with its overflow (Backend scope
/// and the Float literal paragraph), the sign of a zero literal (the `precisionFloat` paragraph
/// and the Float literal paragraph), one NaN per format, the residue and decimal reading of an
/// MInt literal, the fold of binary32/64 `FLOAT` applications over literals, and k-rust's IEEE
/// arithmetic (the `Float` paragraph of Backend scope, and `rootFloat`'s NaN). A change of any of
/// them fails here, and the admission is read again against it.
///
/// GAP K1 re-pin (`draft/kink27/gap`, ticket K1): four passages changed, and each change narrows
/// what admission takes on, so it is read again and re-pinned without a change to admission.
/// (1) The roundTiesToEven passage of Backend scope is split: `Int2Float`, `roundFloat`, a
/// `Float2Int` tie and an inexact `rootFloat` are now open (class `float-rounding`), taken only
/// by an execution, which marks the run, and withheld elsewhere, the fold included; the literal
/// reading (ties, overflow, a rounded zero, roundTiesToEven) is unchanged and now on its own line,
/// pinned beside it. (2) One NaN per format is now stated as fixed by `domains.md`
/// (`Float2String`'s round trip and the one `NaN` lexeme per format), the same element k-rust
/// stores. (3) The fold leaves the `float-rounding` and `outside-domain` applications unfolded, so
/// it writes fewer of k-rust's values into the compiled definition. (4) `rootFloat` outside a
/// positive finite value (its NaN of a negative value among them) is `outside-domain`: an
/// execution's value, marked, not a value the fold or a proof takes. So no Float literal names
/// another element, and every value the fold writes is one it wrote before; the premises the
/// README states for these hooks (P-F1 to P-F4) are narrower than needed now, which the kink
/// session's GK-1/GK-2 restate.
///
/// GAP K3 re-pin (ticket K3): five passages changed, each narrowing what admission takes on.
/// (1) The literal line of Backend scope and (2) the Float literal paragraph of Domain values no
/// longer state a reading used on every route: a literal at a tie, at or beyond half an ulp past
/// the largest finite value, of a nonzero value rounding to a zero, and an `Infinity` lexeme are
/// class `literal`, which an execution marks on every attempt of the sentence holding one (so
/// such a run is excluded as for any mark) and every other route withholds; the element k-rust
/// builds is the one it built before, and the sign of a zero literal is now stated as fixed by
/// `domains.md`. (3) The `precisionFloat` line drops the sign of an underflowing literal, which is
/// that class. (4) A machine-integer literal its width cannot hold is that class too; an in-range
/// one keeps its residue reading. (5) The fold writes no infinite result and reads no literal of
/// the class, so it writes a subset of the values it wrote. So no unmarked run reads a literal
/// whose element is open, and every value the fold writes is one it wrote before.
///
/// GAP K6 re-pin (ticket K6, the documentation sweep): the Float literal paragraph of Domain
/// values (0c0ab74d -> e144923d) no longer states two of k-rust's picks as facts of the format:
/// overflow to the infinity of the sign is now said of the arithmetic hooks, whose `smt-hook`s fix
/// it, with a literal past the threshold class `literal`, and the element of an `Infinity` lexeme
/// is k-rust's, class `literal`; the paragraph's first sentence already classified both, so the
/// element k-rust builds, the marks and the canonical texts are unchanged, and admission reads
/// the same.
///
/// GAP final fix round re-pin (text only; no class, mark or element moves): (1) the literal line
/// of Backend scope (37b6af1d -> 838f6d89) no longer says the literal rule gives the largest
/// finite value past the threshold: it states the rule's two readings there (the largest finite
/// value, or the infinity of the sign as the nearest value in the extended reals), which the text
/// does not decide, which is why such a literal is class `literal`, as the line already said; it
/// also cites the arithmetic `smt-hook`s at their lines in the embedded `domains.md`. (2) The
/// Float literal paragraph of Domain values (e144923d -> 56151f56) says the same of the
/// threshold and that k-rust's element past it is the infinity, the element it built before.
/// (3) The machine-integer literal paragraph (d083c9e9 -> ed76b97a) states the residue reading
/// as k-rust's element, determined in `[-2^(W-1), 2^W)`, the range the paragraph already gave and
/// outside which the literal was already class `literal`. Admission reads the same.
#[test]
fn the_domain_value_passages_float_and_mint_admission_rests_on_are_pinned() {
    let passage = |anchor, opening, digest| passage::Passage {
        file: "docs/compatibility.md",
        anchor,
        opening,
        lines: 1,
        digest,
    };
    passage::assert_pinned(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.."),
        &[
            passage(
                "## Domain values",
                "The backend reads every domain value it holds by the hook",
                "48b47c78acc5068302fccee48f225f945e260fd93a11193d6fe1953468bab93d",
            ),
            passage(
                "## Domain values",
                "Every route validates a text for its sort's kind",
                "9840cb13d02403ca457b8abe2c93bfeb1b6e0cc20099977a7b580523bab7ed47",
            ),
            passage(
                "## Domain values",
                "The backend stores every machine-integer domain value",
                "6651ae404df97ea3d3a1b681a3ff30b7f1eccad4e0396a37eee0b3c09aa2d84c",
            ),
            passage(
                "## Domain values",
                "The backend stores every domain value of a sort hooked `FLOAT.Float`",
                "efdbb72ddfa511c671393734e94341b95568ca609bf72eca5e1dd4b8cc665915",
            ),
            passage(
                "## Backend scope",
                "Where the `FLOAT` text says \"nearest\" without a rule for ties",
                "67a5a97207ccc9ff6af3e305465008bb1b16eb78bba22e42478b646050238f67",
            ),
            // GAP K1: the literal reading moved to its own line after the conversions' classes.
            passage(
                "## Backend scope",
                "The arithmetic hooks are not affected: their `smt-hook`s name",
                "838f6d89768caf91439605d208bec3e5507500b49d25cead15813d32db52f932",
            ),
            passage(
                "## Backend scope",
                "Each format has one NaN, and every spelling of `NaN` in one format",
                "1dd84283101ed96fcefe6ecee7dc1eb22168c8ed6daa11e0c23bc4656f436a20",
            ),
            // Fix round 1: the passages the further premises rest on.
            passage(
                "## Backend scope",
                "A `Float` is an IEEE 754 value whose precision and exponent width",
                "6c9e9468529f06e497884d8cbf602a4c8a8304d64c9386ebc634fc03d2d8491c",
            ),
            passage(
                "## Backend scope",
                "`precisionFloat`, `exponentBitsFloat`, `signFloat` and `isNaN` are evaluated",
                "420d340cb7da9f6af25a8876f30f2767649e3c059c456cbb9932d8b81487b614",
            ),
            passage(
                "## Domain values",
                "A machine-integer literal of `MInt{W}`",
                "ed76b97a5d453164e49d703946cdaf75980fea3eef02bd6e6962205d3f57bb81",
            ),
            passage(
                "## Domain values",
                "A `Float` literal names a rational number",
                "56151f566a48df0f947fef7382ee52386f03519614e4e9073ab936fecda1c7ab",
            ),
            passage(
                "## Constant folding",
                "The `FLOAT` hooks are folded exactly where the backend computes them",
                "099e0422e034b24c857051e1f2d94bef215124ca866bc9c230e995c010a240a2",
            ),
            passage(
                "## Hook values at the edges of their domains",
                "- `rootFloat(F, N)` is \"the Nth integer root\" of `F`",
                "7eeea18cde5a4cc3707deaa5e978dfbf36b922eaa0d6555c333718041e480130",
            ),
        ],
    );
}

/// kink27 R5-BYTES-ENDS: the passages the trusted `Bytes` codec of TV-01 rests on (kink README,
/// "A `Bytes` domain value in an end is compared"). K's text fixes the value: a `Bytes` is a byte
/// sequence whose literal names one byte per item (`domains.md`, `BYTES-SYNTAX`). k-rust's
/// contract fixes the payload: one stored form per value, kept by every reader and route, chosen
/// by the sort's KORE name, and printed one fixed way. A change of any of them fails here, and the
/// codec is read again against it.
#[test]
fn the_passages_the_bytes_end_codec_rests_on_are_pinned() {
    let passage = |file, anchor, opening, digest| passage::Passage {
        file,
        anchor,
        opening,
        lines: 1,
        digest,
    };
    let strings = |opening, digest| {
        passage(
            "docs/compatibility.md",
            "## Strings and their literals",
            opening,
            digest,
        )
    };
    // "Byte Arrays" is a setext heading, which the helper does not read; the nearest ATX heading
    // above `BYTES-SYNTAX` is "### Implementation of Strings".
    let bytes = |opening, digest| {
        passage(
            "crates/k-rust/builtin/domains.md",
            "### Implementation of Strings",
            opening,
            digest,
        )
    };
    passage::assert_pinned(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.."),
        &[
            strings(
                "A K `String` is a sequence of code points too",
                "bebe6540b5aef3bb778c2cc4c4dff7bb4bebb4f18109b08cf3b5005d853ec5bd",
            ),
            strings(
                "k-rust stores a domain value's code points in one form only",
                "59402ce6fb97b6a6b999dd5983ecd6ff758a32b4732d1edb363b9ad9faed7206",
            ),
            strings(
                "Every reader keeps that form",
                "9be8848ccab0a47ca40b76f007097ea2284acd186a5363b5b1a82d44e6ce0d9d",
            ),
            strings(
                "The form is chosen by the sort's KORE name",
                "c54e6e6d36f497a6870a39456a8563ea5754229a342b3403b7bcba741761bff4",
            ),
            strings(
                "The writers write printable ASCII as itself",
                "e317ce5698f333f38b3f7edc07fa4851448fe4b0ce312636005477000d920e13",
            ),
            passage(
                "docs/compatibility.md",
                "## Domain values",
                "Every route validates a text for its sort's kind",
                "9840cb13d02403ca457b8abe2c93bfeb1b6e0cc20099977a7b580523bab7ed47",
            ),
            bytes(
                "syntax Bytes [hook(BYTES.Bytes)]",
                "032782d5196d3c225be5fd416d9d07a67d0a37a2033006ca259e03117e7c2d96",
            ),
            bytes(
                "syntax Bytes ::= r\"b",
                "1214afd67e422dce90a7856661d3e9627a5b3efeb8c53875d258c23d60e5b956",
            ),
        ],
    );
}

mod kink_tier {
    use super::*;

    /// TB-03M (TB-03 review 2): kompile emits macro and alias rules to `macros_kore` as bare
    /// sentences, without a module wrapper. The gate parses that form and scans every macro
    /// sentence: the clean macro and alias modules are admitted, the Float literal that occurs only
    /// in an unused macro body is admitted (a Float literal of a hooked sort is stored as the
    /// canonical text of its value; R3-ADMIT-FLOAT), and a constant-folded String in a macro body
    /// is refused by G-S. Every row is measured before the first assertion.
    #[test]
    #[ignore = "kink"]
    fn audit_vi_t12_macros_compiled_sentences_are_scanned() {
        let file = Path::new(support::DIR).join("t12macro.k");
        let mut rows = Vec::new();
        for module in ["T12MACRO", "T12ALIAS", "T12MACROFLOAT", "T12MACROFOLD"] {
            let side =
                NativeValidator::bind(support::load_path(&file, module), CompileOptions::default())
                    .compile_baseline()
                    .unwrap_or_else(|error| panic!("{module}: {error}"));
            let artifacts = side.artifacts();
            eprintln!("TB-03M {module} macros_kore:\n{}", artifacts.macros_kore);
            let result = validate_representation(&side);
            let without_macros = validate_representation_kore(
                &artifacts.definition_kore,
                &artifacts.syntax_definition_kore,
                "",
                &artifacts.execution_definition,
            );
            eprintln!("TB-03M {module}: {result:?}; without macros_kore: {without_macros:?}");
            rows.push((
                module,
                artifacts.macros_kore.clone(),
                result.map_err(|error| match error {
                    RepresentationError::Finding(finding) => format!("{}", finding.clause),
                    RepresentationError::KoreParse(error) => format!("KoreParse: {error}"),
                }),
                without_macros.map_err(|error| error.to_string()),
            ));
        }
        for (module, macros, result, without_macros) in rows {
            // k-rust's emitted form: one or more bare sentences, no definition attributes or module.
            let text = macros.trim_start();
            assert!(text.starts_with("axiom{"), "{module}: {macros}");
            assert!(!macros.contains("endmodule"), "{module}: {macros}");
            match module {
                "T12MACRO" | "T12ALIAS" => assert_eq!(result, Ok(()), "{module}"),
                "T12MACROFLOAT" => {
                    assert_eq!(result, Ok(()), "{module}");
                    assert_eq!(without_macros, Ok(()), "{module}");
                }
                "T12MACROFOLD" => assert_eq!(result, Err("G-S".to_owned()), "{module}"),
                _ => unreachable!(),
            }
        }
    }

    /// TB-03 review 1 F1: constant folding creates String tokens after the loaded KAST, spelling
    /// U+0080..U+00FF as `\xHH`; the KORE emitter reads that as one raw byte. G-S therefore also
    /// scans the compiled execution definition, where the folded token is visible.
    #[test]
    #[ignore = "kink"]
    fn review1_constant_folded_string_tokens_are_refused_in_the_execution_definition() {
        let file = Path::new(support::DIR).join("t12fold.k");
        for module in ["T12FOLDCHR", "T12FOLDCAT", "T12FOLDPAIR"] {
            let side =
                NativeValidator::bind(support::load_path(&file, module), CompileOptions::default())
                    .compile_baseline()
                    .unwrap_or_else(|error| panic!("{module}: {error}"));
            match validate_representation(&side) {
                Err(RepresentationError::Finding(finding)) => {
                    assert_eq!(
                        finding.clause,
                        RepresentationClause::StringSpelling,
                        "{module}"
                    );
                    assert_eq!(finding.sort, "SortString", "{module}");
                }
                other => panic!("{module}: folded String admitted: {other:?}"),
            }
        }
        let side = NativeValidator::bind(
            support::load_path(&file, "T12FOLDCLEAN"),
            CompileOptions::default(),
        )
        .compile_baseline()
        .expect("clean fold fixture");
        assert_eq!(validate_representation(&side), Ok(()));
    }
}
