//! Clause-level representation premises and the pre-existing fixture admission boundary.

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
    for (sort, hook, clause) in [
        (
            "SortFloat",
            "FLOAT.Float",
            RepresentationClause::FloatLiteral,
        ),
        ("SortMInt", "MINT.MInt", RepresentationClause::MIntLiteral),
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
                format!(r#"\dv{{{sort}{{}}}}("1.0")"#),
                format!(r#"wrap{{}}(\dv{{{sort}{{}}}}("1.0"))"#),
                format!(
                    r#"\equals{{{sort}{{}},{sort}{{}}}}(\dv{{{sort}{{}}}}("1.0"), X:{sort}{{}})"#
                ),
            ] {
                let definition = kore(
                    &declarations,
                    &format!("axiom{{}} {pattern} [{attributes}]"),
                );
                let finding =
                    validate_representation_ast(&definition, None, &loaded(None)).unwrap_err();
                assert_eq!(finding.clause, clause);
                assert_eq!(finding.sort, sort);
                assert!(finding.source.contains("MAIN sentence"));
                assert!(finding.to_string().contains("respelling does not help"));
                assert!(
                    finding
                        .to_string()
                        .contains("k-rust compares Float/MInt tokens by spelling (VI-T12)")
                );
            }
        }
        let definition = kore(&declarations, &format!("axiom{{}} X:{sort}{{}} []"));
        assert!(validate_representation_ast(&definition, None, &loaded(None)).is_ok());
        let macro_definition = kore(
            "",
            &format!(r#"axiom{{}} \dv{{{sort}{{}}}}("1.0") [UNIQUE'Unds'ID{{}}("macro-id")]"#),
        );
        let finding =
            validate_representation_ast(&definition, Some(&macro_definition), &loaded(None))
                .unwrap_err();
        assert_eq!(finding.clause, clause);
        assert_eq!(finding.sentence_unique_id.as_deref(), Some("macro-id"));
    }
}

#[test]
fn renamed_hooked_sorts_and_collection_key_literals_are_scanned() {
    for (hook, clause) in [
        ("FLOAT.Float", RepresentationClause::FloatLiteral),
        ("MINT.MInt", RepresentationClause::MIntLiteral),
    ] {
        let declarations = format!(
            r#"hooked-sort SortRenamed{{}} [hook{{}}("{hook}")] sort SortMap{{}} [] symbol item{{}}(SortRenamed{{}}):SortMap{{}} []"#
        );
        for head in ["item", "setItem"] {
            let definition = kore(
                &declarations,
                &format!(r#"axiom{{}} {head}{{}}(\dv{{SortRenamed{{}}}}("1")) []"#),
            );
            assert_eq!(
                validate_representation_ast(&definition, None, &loaded(None))
                    .unwrap_err()
                    .clause,
                clause
            );
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
fn the_gate_preserves_every_preexisting_tracked_fixture() {
    // Snapshot of tracked fixture/module pairs at TB-03's start; new t12 fixtures deliberately
    // exercise refusal and are tested separately. Support and alternate main modules included.
    for (file, module) in [
        ("annotated.k", "ANNOTATED"),
        ("claims.k", "CLAIMS"),
        ("conflate.k", "CONFLATE"),
        ("conflate2.k", "CONFLATE2"),
        ("conflate3.k", "CONFLATE3"),
        ("conflatem.k", "CONFLATEM"),
        ("counter.k", "COUNTER"),
        ("counter_bytwo.k", "COUNTER_BYTWO"),
        ("duplicate_unlabelled.k", "DUPLICATE_UNLABELLED"),
        ("effectmem.k", "EFFECTMEM"),
        ("equation-ensures-support.k", "EQSUPPORT"),
        ("freshgen.k", "FRESHGEN"),
        ("guardeddiv.k", "GUARDEDDIV"),
        ("guardedeq.k", "GUARDEDEQ"),
        ("guardedmem.k", "GUARDEDMEM"),
        ("memory.k", "MEMORY"),
        ("nd.k", "ND"),
        ("nextgap.k", "NEXTGAP"),
        ("opaquemem.k", "OPAQUEMEM"),
        ("partialreq.k", "PARTIALREQ"),
        ("partialreq.k", "TV01UNSAT"),
        ("partialstep.k", "PARTIALSTEP"),
        ("residue.k", "RESIDUE"),
        ("rulecondfail.k", "RULECONDFAIL"),
        ("scopeforge.k", "SCOPEFORGE"),
        ("subsort_steps.k", "SUBSORT_STEPS"),
        ("symbolic-claim-mutation.k", "SYMPARTIAL"),
        ("symbolic-claim-survivor.k", "SYMPARTIAL"),
        ("symbolic-equation-ensures.k", "SYMPARTIAL"),
        ("symbottom.k", "SYMBOTTOM"),
        ("symensures.k", "SYMENSURES"),
        ("symmem.k", "SYMMEM"),
        ("symmem_existential.k", "SYMMEM_EXISTENTIAL"),
        ("symmem_release.k", "SYMMEM_RELEASE"),
        ("symnarrow.k", "SYMNARROW"),
        ("symowise.k", "SYMOWISE"),
        ("sympartial.k", "SYMPARTIAL"),
        ("symwrap.k", "SYMWRAP"),
        ("symwraptotal.k", "SYMWRAPTOTAL"),
        ("tb02bytes.k", "TB02BYTES"),
        ("tb02bytestoken.k", "TB02BYTESTOKEN"),
        ("tb02float.k", "TB02FLOAT"),
        ("tb02input.k", "TB02INPUT"),
        ("tb02input.k", "TB02PRED"),
        ("tb02string.k", "TB02STRING"),
        ("tb02stringtoken.k", "TB02STRINGTOKEN"),
        ("tb02token.k", "TB02TOKEN"),
        ("unbound.k", "UNBOUND"),
        ("unbound.k", "TV01TERMINAL"),
        ("undecided.k", "UNDECIDED"),
        ("unlabelled.k", "UNLABELLED"),
    ] {
        let baseline = support::load_path(&Path::new(support::DIR).join(file), module);
        let side = NativeValidator::bind(baseline, CompileOptions::default())
            .compile_baseline()
            .unwrap_or_else(|error| panic!("{file}/{module} compilation: {error}"));
        let result = validate_representation(&side);
        if matches!(file, "tb02float.k" | "rulecondfail.k") {
            assert_eq!(
                match result.unwrap_err() {
                    RepresentationError::Finding(finding) => finding.clause,
                    RepresentationError::KoreParse(error) => panic!("{error}"),
                },
                RepresentationClause::FloatLiteral,
                "{file}/{module}"
            );
        } else {
            assert!(
                result.is_ok(),
                "STOP: existing fixture {file}/{module}: {result:?}"
            );
        }
    }
}

#[test]
fn syntax_axioms_share_the_hook_registry_and_parse_failures_are_typed() {
    let declarations = format!("[] module MAIN {DECLARATIONS} endmodule []");
    let axiom = r#"[] module SYNTAX axiom{} \dv{SortFloat{}}("1.0") [UNIQUE'Unds'ID{}("syntax-id")] endmodule []"#;
    for (syntax, macros) in [(axiom, ""), ("", axiom)] {
        let error =
            validate_representation_kore(&declarations, syntax, macros, &loaded(None)).unwrap_err();
        let RepresentationError::Finding(finding) = error else {
            panic!("expected literal finding")
        };
        assert_eq!(finding.clause, RepresentationClause::FloatLiteral);
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

/// TB-03 review 1 F1: constant folding creates String tokens after the loaded KAST, spelling
/// U+0080..U+00FF as `\xHH`; the KORE emitter reads that as one raw byte. G-S therefore also
/// scans the compiled execution definition, where the folded token is visible.
#[test]
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

/// TB-03 review 1 F1, defence in depth: a compiled String domain value must be UTF-8 text
/// (k-rust's String values are UTF-8). Bytes values remain byte sequences.
#[test]
fn review1_compiled_string_domain_values_must_be_utf8() {
    for value in [r#"\xe9"#, r#"\xc3"#, r#"A\xff"#] {
        let definition = kore(
            DECLARATIONS,
            &format!(r#"axiom{{}} \dv{{SortText{{}}}}("{value}") [UNIQUE'Unds'ID{{}}("byte-id")]"#),
        );
        let finding = validate_representation_ast(&definition, None, &loaded(None)).unwrap_err();
        assert_eq!(
            finding.clause,
            RepresentationClause::StringSpelling,
            "{value}"
        );
        assert_eq!(finding.sort, "SortText");
        assert_eq!(finding.sentence_unique_id.as_deref(), Some("byte-id"));
    }
    for value in [r#"\xc3\xa9"#, r#"é"#, "A", ""] {
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

/// TB-03 review 1 minor: alias bodies are unfolded into axioms by the backend, so G-F, G-M,
/// G-I and the String rule scan them too (kompile emits no alias at 927b9ce6).
#[test]
fn review1_alias_declaration_bodies_are_scanned() {
    for (sort, value, clause) in [
        ("SortFloat", "1.0", RepresentationClause::FloatLiteral),
        ("SortMInt", "1p8", RepresentationClause::MIntLiteral),
        (
            "SortOtherInt",
            "007",
            RepresentationClause::RenamedIntLiteral,
        ),
        ("SortText", r#"\xe9"#, RepresentationClause::StringSpelling),
    ] {
        let definition = kore(
            DECLARATIONS,
            &format!(
                r#"alias lit{{}}() : {sort}{{}} where lit{{}}() := \dv{{{sort}{{}}}}("{value}") []"#
            ),
        );
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

/// TB-03M (TB-03 review 2): kompile emits macro and alias rules to `macros_kore` as bare
/// sentences, without a module wrapper. The gate parses that form and scans every macro
/// sentence: the clean macro and alias modules are admitted, a Float literal that occurs only in
/// an unused macro body is refused by G-F, and a constant-folded String in a macro body is
/// refused by G-S. Every row is measured before the first assertion.
#[test]
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
                assert_eq!(result, Err("G-F".to_owned()), "{module}");
                // The Float literal is only in the macro sentence.
                assert_eq!(without_macros, Ok(()), "{module}");
            }
            "T12MACROFOLD" => assert_eq!(result, Err("G-S".to_owned()), "{module}"),
            _ => unreachable!(),
        }
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
    let string = r#"axiom{} \dv{SortText{}}("\xe9") [UNIQUE'Unds'ID{}("macro-id")]"#;
    let alias = r#"alias lit{}() : SortFloat{} where lit{}() := \dv{SortFloat{}}("1.0") [UNIQUE'Unds'ID{}("macro-id")]"#;
    for (text, clause) in [
        (format!("{float}\n"), RepresentationClause::FloatLiteral),
        (
            format!("{clean}\n{float}\n"),
            RepresentationClause::FloatLiteral,
        ),
        (
            format!("{clean}\n// comment\n{mint}"),
            RepresentationClause::MIntLiteral,
        ),
        (
            format!("{clean}\n{renamed}\n"),
            RepresentationClause::RenamedIntLiteral,
        ),
        (
            format!("{clean}\n{string}\n"),
            RepresentationClause::StringSpelling,
        ),
        (format!("{alias}\n"), RepresentationClause::FloatLiteral),
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
