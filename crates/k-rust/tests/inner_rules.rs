// Standard-prelude fixtures require native Z3 inference; their semantic assertions are
// feature-gated below. inner_rules::portable_build_rejects_the_standard_prelude covers
// the portable boundary instead of duplicating that rejection for each fixture.

use indoc::indoc;
use k_rust::definition::{Attributes, Sentence, StructuralCheckOptions, check_rhs_variables};
use k_rust::inner::{ParseError, RuleError, parse_rule_content, resolve_rule_bubbles};
use k_rust::kast::{Sort, Term, TermSpan};
use k_rust::outer::{LoadOptions, ResolvedSource, load, load_with_options};
use k_rust::provenance::{SourceId, SourceTable};
#[cfg(feature = "z3-inference")]
use serde::Deserialize;
use std::collections::BTreeMap;

#[derive(Debug)]
#[allow(dead_code)]
struct SentenceSummary<'a> {
    kind: &'static str,
    body: String,
    requires: String,
    ensures: Option<String>,
    label: Option<&'a str>,
}

#[derive(Debug)]
#[allow(dead_code)]
struct MetadataSummary<'a> {
    term: String,
    source: Option<&'a str>,
    logical_source: Option<&'a str>,
    span: Option<TermSpan>,
    production: Option<usize>,
}

#[cfg(feature = "z3-inference")]
#[derive(Deserialize)]
struct CellAssociationOracle {
    rule: Vec<CellAssociationRule>,
}

#[cfg(feature = "z3-inference")]
#[derive(Deserialize)]
struct CellAssociationRule {
    shape: String,
}

#[cfg(feature = "z3-inference")]
fn cell_association_shape(term: &Term) -> Option<String> {
    let Term::Apply { label, arguments } = term.unannotated() else {
        return None;
    };
    if label.name != "#cells" {
        return Some(label.name.clone());
    }
    let [left, right] = arguments.as_slice() else {
        return None;
    };
    Some(format!(
        "#cells({}, {})",
        cell_association_shape(left)?,
        cell_association_shape(right)?
    ))
}

#[cfg(feature = "z3-inference")]
fn cell_leaves<'a>(term: &'a Term, leaves: &mut Vec<&'a str>) {
    let Term::Apply { label, arguments } = term.unannotated() else {
        return;
    };
    if label.name == "#cells" {
        for argument in arguments {
            cell_leaves(argument, leaves);
        }
    } else {
        leaves.push(&label.name);
    }
}

fn metadata_summary<'a>(
    term: &Term,
    source: &'a str,
    source_table: &'a SourceTable,
    output: &mut Vec<MetadataSummary<'a>>,
) {
    let metadata = term.metadata();
    let span = metadata.and_then(|metadata| metadata.span);
    output.push(MetadataSummary {
        term: term.to_string(),
        source: span.and_then(|span| source.get(span.start..span.end)),
        logical_source: span
            .and_then(|span| source_table.get(span.source))
            .map(|identity| identity.logical.as_str()),
        span,
        production: metadata
            .and_then(|metadata| metadata.production)
            .map(|production| production.0),
    });
    match term.unannotated() {
        Term::Rewrite { left, right } => {
            metadata_summary(left, source, source_table, output);
            metadata_summary(right, source, source_table, output);
        }
        Term::As { pattern, alias } => {
            metadata_summary(pattern, source, source_table, output);
            metadata_summary(alias, source, source_table, output);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                metadata_summary(item, source, source_table, output);
            }
        }
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
        Term::Annotated { .. } => unreachable!(),
    }
}

fn sentence_summary(sentence: &Sentence) -> Option<SentenceSummary<'_>> {
    let (kind, body, requires, ensures, attributes) = match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        } => ("rule", body, requires, Some(ensures), attributes),
        Sentence::Claim {
            body,
            requires,
            ensures,
            attributes,
        } => ("claim", body, requires, Some(ensures), attributes),
        Sentence::Context {
            body,
            requires,
            attributes,
        } => ("context", body, requires, None, attributes),
        Sentence::ContextAlias {
            body,
            requires,
            attributes,
        } => ("alias", body, requires, None, attributes),
        _ => return None,
    };
    Some(SentenceSummary {
        kind,
        body: body.to_string(),
        requires: requires.to_string(),
        ensures: ensures.map(ToString::to_string),
        label: attributes.get_str("label"),
    })
}

fn lowered(source: &str) -> k_rust::definition::Definition {
    lowered_module(source, "MAIN")
}

fn lowered_module(source: &str, main_module: &str) -> k_rust::definition::Definition {
    let parsed = k_rust::outer::parse("rules.k", source).unwrap();
    k_rust::outer::lower(&parsed, main_module).unwrap()
}

#[test]
fn standalone_rule_content_parses_every_condition_shape_and_retains_attributes() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Bool ::= r"true|false" [token]
          syntax Exp ::= "a" [symbol(a)]
        endmodule
    "#});
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&definition).unwrap();
    let attributes = Attributes::new(BTreeMap::from([
        (
            k_rust::definition::SOURCE_ATTRIBUTE.into(),
            serde_json::json!("pattern.k"),
        ),
        (
            k_rust::definition::SOURCE_ID_ATTRIBUTE.into(),
            serde_json::json!(17),
        ),
        ("contentStartOffset".into(), serde_json::json!(23)),
        ("label".into(), serde_json::json!("selected")),
    ]));

    for contents in [
        "a => a",
        "a => a requires false",
        "a => a ensures false",
        "a => a requires false ensures false",
    ] {
        let sentence = parse_rule_content(&resolved, "MAIN", contents, attributes.clone()).unwrap();
        let Sentence::Rule {
            body,
            requires,
            ensures,
            attributes: retained,
        } = sentence
        else {
            panic!("standalone rule parser returned a non-rule sentence")
        };
        assert!(body.to_string().contains("=>"), "{body}");
        assert_eq!(retained, attributes);
        assert_eq!(retained.source(), Some("pattern.k"));
        assert_eq!(retained.source_id(), Some(SourceId(17)));
        let span = body
            .metadata()
            .and_then(|metadata| metadata.span)
            .expect("parsed rule body should retain its source span");
        assert_eq!(span.source, SourceId(17));
        assert_eq!(span.start, 23);
        assert_eq!(
            requires.to_string().contains("false"),
            contents.contains("requires false")
        );
        assert_eq!(
            ensures.to_string().contains("false"),
            contents.contains("ensures false")
        );
    }
}

#[test]
fn standalone_rule_content_uses_the_reachable_global_scanner() {
    let definition = lowered(indoc! {r#"
        module TOKEN
          syntax Id ::= r"[A-Z]+" [prec(3), token]
        endmodule
        module RULES
        endmodule
        module MAIN
          imports TOKEN
          imports RULES
        endmodule
    "#});
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&definition).unwrap();

    assert!(matches!(
        parse_rule_content(
            &resolved,
            "RULES",
            "X => X",
            Attributes::default(),
        ),
        Err(RuleError::Parse(ref error))
            if error.module == "RULES" && matches!(error.error, ParseError::NoParse { .. })
    ));
}

#[test]
fn standalone_rule_content_reports_typed_module_and_source_aware_parse_errors() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
        endmodule
    "#});
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&definition).unwrap();
    let attributes = Attributes::new(BTreeMap::from([
        (
            k_rust::definition::SOURCE_ATTRIBUTE.into(),
            serde_json::json!("command-line-pattern"),
        ),
        (
            k_rust::definition::LOCATION_ATTRIBUTE.into(),
            serde_json::json!([7, 11, 7, 20]),
        ),
    ]));

    assert!(matches!(
        parse_rule_content(&resolved, "MISSING", "a => a", attributes.clone()),
        Err(RuleError::MissingModule { ref module }) if module == "MISSING"
    ));

    let RuleError::Parse(error) =
        parse_rule_content(&resolved, "MAIN", "not-a-rule", attributes).unwrap_err()
    else {
        panic!("expected a parse error")
    };
    assert_eq!(error.source.as_deref(), Some("command-line-pattern"));
    assert_eq!(
        error.location,
        Some(k_rust::definition::Location {
            start_line: 7,
            start_column: 11,
            end_line: 7,
            end_column: 20,
        })
    );
    assert!(matches!(
        error.error,
        ParseError::NoParse { span: None, .. }
    ));
}

macro_rules! assert_rule_resolution_snapshot {
    ($source:expr) => {{
        let source = $source;
        let resolved = resolve_rule_bubbles(&lowered(source)).unwrap();
        let sentences = resolved
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .filter_map(sentence_summary)
            .collect::<Vec<_>>();
        insta::with_settings!({
            description => format!("K definition:\n\n{source}"),
            omit_expression => true,
            prepend_module_to_snapshot => true,
        }, {
            insta::assert_debug_snapshot!(sentences);
        });
    }};
}

macro_rules! rule_snapshot {
    ($(#[$attribute:meta])* $name:ident, $source:expr) => {
        $(#[$attribute])*
        #[test]
        fn $name() {
            let source = indoc!($source);
            assert_rule_resolution_snapshot!(source);
        }
    };
}

#[test]
fn preserves_nested_term_spans_and_resolved_productions() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= Exp "+" Exp [symbol(_+_)]
          syntax Exp ::= "f(" Exp ")" [symbol(f)]

          rule f(f(1 + 2)) => f(3)
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let loaded = load(
        ResolvedSource::new("nested.k", source),
        "MAIN",
        &mut resolver,
    )
    .unwrap();
    let body = loaded
        .definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    let mut metadata = Vec::new();
    metadata_summary(body, source, &loaded.source_table, &mut metadata);

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(metadata);
    });
}

#[test]
fn rule_parsing_always_includes_default_layout() {
    let source = indoc! {r#"
        module MAIN
          syntax #Layout [token]
          syntax Exp ::= "x" [symbol(x)]
          rule x => x
        endmodule
    "#};
    let definition = resolve_rule_bubbles(&lowered(source)).unwrap();

    assert!(
        definition
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .any(|sentence| matches!(sentence, Sentence::Rule { .. }))
    );
}

#[test]
fn rule_synonym_casts_use_the_target_sort_in_production_arguments() {
    for (cast, accepted) in [
        ("Rat", true),
        ("Wad", true),
        ("Ray", true),
        ("Other", false),
    ] {
        let source = format!(
            r#"
            module MAIN
              syntax Rat ::= r"[0-9]+" [token]
              syntax Wad = Rat
              syntax Ray = Rat
              syntax Other ::= "other" [symbol(other)]
              syntax Wad ::= "f(" Ray ")" [symbol(f)]
              rule f(0:{cast}) => 0
            endmodule
            "#
        );
        let definition = k_rust::definition::apply_sort_synonyms(&lowered(&source)).unwrap();
        let result = resolve_rule_bubbles(&definition);
        if !accepted {
            assert!(
                matches!(result, Err(RuleError::Parse(ref error))
                    if matches!(error.error, ParseError::NoParse { .. })),
                "{result:?}"
            );
            continue;
        }
        let resolved = result.unwrap_or_else(|error| panic!("{cast}: {error}"));
        let body = resolved
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::Rule { body, .. } => Some(body),
                _ => None,
            })
            .unwrap();
        assert_eq!(
            body.to_string(),
            "f(#SemanticCastToRat(#token(\"0\",\"Rat\")))=>#token(\"0\",\"Rat\")",
            "{cast}"
        );
    }
}

#[cfg(feature = "z3-inference")]
#[test]
fn prunes_nested_rewrites_while_parsing_a_long_recursive_chain() {
    let source = indoc! {r##"
        module MAIN
          syntax Int
          syntax CallSixOp
          syntax OpCode ::= CallSixOp | InternalOp
          syntax KItem ::= OpCode
          syntax InternalOp ::= "#exec" "[" OpCode "]" [symbol(exec)]
                              | "#gas" "[" OpCode "," OpCode "]" [symbol(gas)]
                              | CallSixOp Int Int Int Int Int Int [symbol(callSix)]
          syntax WordStack ::= ".WordStack" [symbol(dotWordStack)]
                             | Int ":" WordStack [symbol(consWordStack)]
          syntax Bytes ::= Int ":" Bytes [symbol(consBytes), function]
          syntax State ::= "<k>" K "..." "</k>"
                           "<wordStack>" WordStack "</wordStack>" [symbol(state)]

          rule <k> #exec [ CSO:CallSixOp ] => #gas [ CSO , CSO W0 W1 W2 W3 W4 W5 ] ~> CSO W0 W1 W2 W3 W4 W5 ... </k>
               <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : WS => WS </wordStack>
        endmodule
    "##};
    resolve_rule_bubbles(&lowered(source)).unwrap();
}

#[cfg(feature = "z3-inference")]
#[test]
fn rule_conditions_can_select_an_overloaded_rewrite_super_sort() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Gas ::= Int
          syntax Gas ::= cap(Gas) [symbol(capGas), overload(cap)]
          syntax Int ::= cap(Int) [symbol(capInt), overload(cap)]
          syntax Bool ::= Gas "<Gas" Gas [symbol(ltGas)]

          rule cap(GCAP) => 0 requires GCAP <Gas 0
        endmodule
    "#};
    let resolved = resolve_rule_bubbles(&lowered(source)).unwrap();
    let Sentence::Rule { body, requires, .. } = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find(|sentence| matches!(sentence, Sentence::Rule { .. }))
        .unwrap()
    else {
        unreachable!()
    };

    assert!(body.to_string().contains("capGas"), "{body}");
    assert!(!body.to_string().contains("capInt"), "{body}");
    assert!(requires.to_string().contains("GCAP"), "{requires}");
}

#[cfg(feature = "z3-inference")]
#[test]
fn user_list_singletons_participate_in_rule_overload_selection() {
    let source = indoc! {r#"
        module MAIN
          syntax Foo ::= "foo" [symbol(foo)]
                       | "bar" [symbol(bar)]
          syntax Foos ::= List{Foo, ","} [symbol(foos)]
          syntax Bool ::= "test" "(" Foo ")" [function, overload(test), symbol(testFoo)]
                        | "test" "(" Foos ")" [function, overload(test), symbol(testFoos)]

          rule test(foo) => test(foo)
        endmodule
    "#};
    let resolved = resolve_rule_bubbles(&lowered(source))
        .expect("the synthetic Foo < Foos rule-grammar subsort should select the Foo overload");
    let body = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .expect("the parsed definition should retain the rule");

    assert!(body.contains("testFoo"), "{body}");
    assert!(!body.contains("testFoos"), "{body}");
}

#[cfg(feature = "z3-inference")]
#[test]
fn user_list_singletons_remain_ambiguous_without_an_overload_group() {
    let source = indoc! {r#"
        module MAIN
          syntax Foo ::= "foo" [symbol(foo)]
          syntax Foos ::= List{Foo, ","} [symbol(foos)]
          syntax Bool ::= "test" "(" Foo ")" [function, symbol(testFoo)]
                        | "test" "(" Foos ")" [function, symbol(testFoos)]

          rule test(foo) => test(foo)
        endmodule
    "#};
    let error = resolve_rule_bubbles(&lowered(source))
        .expect_err("the synthetic list subsort alone must not select a production");

    assert!(
        matches!(
            error,
            RuleError::Parse(ref error)
                if matches!(error.error, ParseError::Ambiguous { parses: 2, .. })
        ),
        "{error:?}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn polymorphic_rhs_keeps_overload_branch_parameters_independent() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Gas ::= Int
          syntax Gas ::= cap(Gas, Gas, Int, Int) [symbol(capGas), overload(cap), function, total]
          syntax Int ::= cap(Int, Int, Int, Int) [symbol(capInt), overload(cap), function, total]
          syntax Bool ::= Int "<=Int" Int [symbol(leInt), function, total]
          syntax {S} S ::= "ite" "(" Bool "," S "," S ")" [symbol(ite), function, total]

          rule [cgascap]:
               cap(GCAP:Int, GAVAIL:Int, GEXTRA, IGNORED)
            => ite(0 <=Int GEXTRA, GCAP, GAVAIL)
            requires 0 <=Int GCAP
            [concrete]
        endmodule
    "#};
    let prelude = k_rust::builtin::embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        k_rust::builtin::embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("cgascap.k", source),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            ..LoadOptions::default()
        },
    )
    .expect("the reduced Cgascap definition should load");
    let body = loaded
        .definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .expect("the reduced Cgascap rule should resolve");

    assert!(body.contains("capInt"), "{body}");
    assert!(!body.contains("capGas"), "{body}");
    assert!(body.contains("ite{Int}"), "{body}");
}

#[cfg(feature = "z3-inference")]
#[test]
fn incomparable_maximal_typings_are_reported_as_ambiguity() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Foo ::= "foo"
          syntax A ::= "a" "(" K "," Int ")" [symbol(aK)]
          syntax B ::= "a" "(" Int "," Foo ")" [symbol(aF)]

          rule a(X, Y) => X ~> Y
        endmodule
    "#};
    let error = resolve_rule_bubbles(&lowered(source))
        .expect_err("incomparable maximal typings must remain ambiguous");
    let RuleError::Parse(error) = error else {
        panic!("expected a parse error, got {error:?}")
    };
    let ParseError::Ambiguous {
        parses,
        alternatives,
        span,
    } = error.error
    else {
        panic!("expected an ambiguity, got {:?}", error.error)
    };

    assert_eq!(parses, 2);
    assert!(span.is_some());
    assert_eq!(alternatives.len(), 2, "{alternatives:#?}");
    assert!(
        alternatives
            .iter()
            .any(|alternative| alternative.term.contains("aF")),
        "{alternatives:#?}"
    );
    assert!(
        alternatives
            .iter()
            .any(|alternative| alternative.term.contains("aK")),
        "{alternatives:#?}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn a_dominating_typing_still_selects_one_parse() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax A ::= "a" "(" K ")" [symbol(aK)]
          syntax B ::= "a" "(" Int ")" [symbol(aI)]

          rule a(X) => X
        endmodule
    "#};
    let resolved = resolve_rule_bubbles(&lowered(source)).expect("the maximal K typing should win");
    let body = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .expect("the rule should be resolved");

    assert!(body.contains("aK"), "{body}");
    assert!(!body.contains("aI"), "{body}");
}

#[test]
fn rejects_non_function_rewrite_siblings_that_remain_ambiguous() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Bytes ::= ".Bytes" [symbol(.Bytes)]
          syntax WordStack ::= ".WordStack" [symbol(.WordStack)]
          syntax Bytes ::= Bytes "[" Int ":=" Bytes "]" [symbol(mapWriteRange)]
          syntax WordStack ::= WordStack "[" Int ":=" Int "]" [symbol(setWordStack)]

          rule _ [ START := _ ] => .Bytes
        endmodule
    "#};
    let error = resolve_rule_bubbles(&lowered(source))
        .expect_err("rewrite siblings must not silently select mapWriteRange");
    #[cfg(not(feature = "z3-inference"))]
    assert!(
        matches!(&error, RuleError::Parse(error)
            if matches!(error.error, ParseError::Z3InferenceRequired { ambiguity: true, .. })),
        "{error:?}"
    );
    #[cfg(feature = "z3-inference")]
    {
        let rendered = error.to_string();
        assert!(rendered.starts_with("rules.k:8:8:"), "{rendered}");
        assert!(rendered.contains("\n1: syntax "), "{rendered}");
        assert!(rendered.contains("\n2: syntax "), "{rendered}");
        assert!(!rendered.contains("<generated production>"), "{rendered}");
        let RuleError::Parse(error) = error else {
            panic!("expected a parse error, got {error:?}")
        };
        let ParseError::Ambiguous {
            parses,
            alternatives,
            span,
        } = error.error
        else {
            panic!("expected an ambiguity, got {:?}", error.error)
        };

        assert_eq!(parses, 2);
        assert!(span.is_some());
        assert_eq!(alternatives.len(), 2, "{alternatives:#?}");
        assert!(alternatives[0].term.contains("mapWriteRange"));
        assert!(alternatives[1].term.contains("setWordStack"));
        assert!(
            alternatives
                .iter()
                .any(|alternative| alternative.term.contains("mapWriteRange")),
            "{alternatives:#?}"
        );
        assert!(
            alternatives
                .iter()
                .any(|alternative| alternative.term.contains("setWordStack")),
            "{alternatives:#?}"
        );
    }
}

#[test]
fn rewrite_sibling_sort_does_not_select_constant_or_variable_overloads() {
    for left in ["a(1)", "a(X)"] {
        let source = format!(
            r#"module MAIN
  syntax Int ::= r"[0-9]+" [token]
  syntax A ::= "a" "(" Int ")" [symbol(aA)]
  syntax B ::= "a" "(" Int ")" [symbol(aB)]
  syntax A ::= "mkA" "(" ")" [symbol(mkA)]
  rule {left} => mkA()
endmodule
"#
        );
        let error = resolve_rule_bubbles(&lowered(&source))
            .expect_err("unrelated result sorts must remain ambiguous");
        #[cfg(not(feature = "z3-inference"))]
        assert!(
            matches!(&error, RuleError::Parse(error)
                if matches!(error.error, ParseError::Z3InferenceRequired { ambiguity: true, .. })),
            "{left}: {error:?}"
        );
        #[cfg(feature = "z3-inference")]
        assert!(
            matches!(
                error,
                RuleError::Parse(ref error)
                    if matches!(error.error, ParseError::Ambiguous { parses: 2, .. })
            ),
            "{left}: {error:?}"
        );
    }
}

#[cfg(feature = "z3-inference")]
#[test]
fn function_rewrite_siblings_are_selected_by_whole_rule_inference() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Bool ::= Int "<Int" Int [function, symbol(ltInt)]
          syntax Bytes ::= ".Bytes" [symbol(.Bytes)]
          syntax WordStack ::= ".WordStack" [symbol(.WordStack)]
          syntax Bytes ::= Bytes "[" Int ":=" Bytes "]"
                           [function, total, symbol(mapWriteRange)]
          syntax WordStack ::= WordStack "[" Int ":=" Int "]"
                               [function, total, symbol(setWordStack)]

          rule _ [ START := _ ] => .Bytes requires START <Int 0
        endmodule
    "#};
    let resolved = resolve_rule_bubbles(&lowered(source))
        .expect("the rule condition should select the Bytes function");
    let body = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .expect("the rule should be resolved");

    assert!(body.contains("mapWriteRange"), "{body}");
    assert!(!body.contains("setWordStack"), "{body}");
}

#[test]
fn keeps_a_valid_concrete_application_when_a_kapply_alternative_is_unknown() {
    let source = indoc! {r##"
        module MAIN
          syntax WordStack ::= ".WordStack" [symbol(.WordStack)]
          syntax Int ::= "#sizeWordStack" "(" WordStack ")"
                         [symbol(#sizeWordStack), function]
                       | "#sizeWordStack" "(" WordStack "," Int ")"
                         [symbol(sizeWordStackAux), function]

          rule #sizeWordStack(.WordStack, SIZE) => SIZE
        endmodule
    "##};
    let resolved = resolve_rule_bubbles(&lowered(source)).unwrap();
    let body = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .unwrap();

    assert!(body.contains("sizeWordStackAux"), "{body}");
}

#[cfg(feature = "z3-inference")]
#[test]
fn parses_a_semantic_cast_inside_nested_map_and_bytes_lookups() {
    let source = indoc! {r##"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
                       | "lengthBytes" "(" Bytes ")" [symbol(lengthBytes), function]
                       | Bytes "[" Int "]" [symbol(bytesLookup), function]
                       | Int "-Int" Int [symbol(subInt), function]
          syntax Bytes ::= "bytes" [symbol(bytes)]
                         | "#range" "(" Bytes "," Int "," Int ")" [symbol(range), function]
          syntax Map ::= "map" [symbol(map)]
                       | Map "[" KItem "<-" KItem "]" [symbol(updateMap), function, prefer]
          syntax KItem ::= Map "[" KItem "]" [symbol(lookupMap), function]
          syntax KItem ::= Int | MerkleTree
          syntax MerkleTree ::= "tree" [symbol(tree)]
                              | "MerkleBranch" "(" Map "," String ")" [symbol(MerkleBranch)]
                              | "MerkleDelete" "(" MerkleTree "," Bytes ")" [symbol(MerkleDelete), function]
                              | "MerkleCheck" "(" MerkleTree ")" [symbol(MerkleCheck), function]

          rule MerkleDelete( MerkleBranch( M, V ), PATH )
            => MerkleCheck( MerkleBranch( M[PATH[0] <- MerkleDelete( {M[PATH[0]]}:>MerkleTree, #range(PATH, 1, lengthBytes(PATH) -Int 1) )], V ) )
        endmodule
    "##};
    resolve_rule_bubbles(&lowered(source)).unwrap();
}

#[test]
fn semcast2_is_accepted_end_to_end() {
    let source = include_str!("fixtures/reference/inner/semcast2/test.k");
    let resolved = resolve_rule_bubbles(&lowered_module(source, "TEST"))
        .expect("unambiguous rules use non-strict portable inference");
    let sentence = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find(|sentence| matches!(sentence, Sentence::Rule { .. }))
        .expect("the rule should be resolved");
    let Sentence::Rule { body, .. } = sentence else {
        unreachable!()
    };

    assert!(
        body.to_string().contains("#SemanticCastToSmall(X)"),
        "{body}"
    );
    assert!(check_rhs_variables(&[sentence], StructuralCheckOptions::default()).is_empty());
}

#[test]
fn reference_canonicalizes_an_eighty_operand_casted_chain_without_truncation() {
    fn assert_cast_operand(term: &Term, index: usize) {
        let Term::Apply { label, arguments } = term.unannotated() else {
            panic!("operand {index} is not a semantic cast: {term}");
        };
        assert_eq!(label.name, "#SemanticCastToVal", "operand {index}: {term}");
        let [argument] = arguments.as_slice() else {
            panic!("operand {index} cast has the wrong arity: {term}");
        };
        assert!(
            matches!(
                argument.unannotated(),
                Term::Variable { name, .. } if name == &format!("X{index}")
            ),
            "operand {index} cast has the wrong variable: {argument}"
        );
    }

    fn assert_left_chain(term: &Term, operands: usize) {
        if operands == 1 {
            assert_cast_operand(term, 1);
            return;
        }
        let Term::Apply { label, arguments } = term.unannotated() else {
            panic!("prefix of {operands} operands is not an application: {term}");
        };
        assert_eq!(label.name, "plus", "prefix of {operands} operands: {term}");
        let [prefix, operand] = arguments.as_slice() else {
            panic!("plus at operand {operands} has the wrong arity: {term}");
        };
        assert_left_chain(prefix, operands - 1);
        assert_cast_operand(operand, operands);
    }

    let source = include_str!("fixtures/reference/inner/casted-chain/test.k");
    let resolved = resolve_rule_bubbles(&lowered_module(source, "CASTED-CHAIN"))
        .expect("the reference-accepted casted chain should parse without a forest limit");
    let body = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .expect("the resolved casted-chain rule should exist");
    let Term::Rewrite { left, right } = body.unannotated() else {
        panic!("the rule body is not a rewrite: {body}");
    };

    assert_left_chain(left, 80);
    assert!(
        matches!(right.unannotated(), Term::Token { token, sort } if token == "0" && sort == &Sort::new("Int")),
        "unexpected casted-chain RHS: {right}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn semcast3_and_semcast4_stay_rejected() {
    for (name, source) in [
        (
            "semcast3",
            include_str!("fixtures/reference/inner/semcast3/test.k"),
        ),
        (
            "semcast4",
            include_str!("fixtures/reference/inner/semcast4/test.k"),
        ),
    ] {
        let result = resolve_rule_bubbles(&lowered_module(source, "TEST"));
        assert!(
            matches!(
                result,
                Err(RuleError::Parse(ref error))
                    if matches!(error.error, ParseError::SortInference { .. })
            ),
            "{name} should stay on strict Z3 inference: {result:?}"
        );
    }
}

#[test]
fn parses_rule_claim_context_and_alias_bubbles() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= Exp "+" Exp [klabel(_+_)]
          syntax Bool ::= Exp "==" Exp [klabel(_==_)]

          rule [plus-zero]: X:Exp + 0 => X:Exp requires X == 0 ensures false
          claim X:Exp + 0 => X:Exp ensures X == 0
          context HOLE + 0 requires true
          context alias [simplify-zero]: X + 0 => X requires true
        endmodule
    "#};
    assert_rule_resolution_snapshot!(source);
}

#[test]
fn parses_sort_predicate_context_aliases() {
    let source = indoc! {r#"
        module MAIN
          syntax Foo ::= foo(Int)
          syntax Int ::= r"[0-9]+" [token]

          context alias [foo]: HERE
            requires isFoo(HOLE)
        endmodule
    "#};
    assert_rule_resolution_snapshot!(source);
}

#[test]
fn loader_parses_rules_against_generated_rule_cells() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Int ::= Int "+" Int [klabel(_+Int_)]
          configuration <top><k> 0 </k><counter> 0 </counter></top>
          rule <top>
            <k> X => 1 ... </k>
            <counter> N => N + 1 </counter>
          </top>
          rule [[ X => 1 ]] <counter> N </counter>
          syntax K
          syntax Map
        endmodule
    "#};
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    let loaded = load(
        ResolvedSource::new("cells.k", source),
        "MAIN",
        &mut resolver,
    )
    .unwrap();
    let bubbles = loaded
        .definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter(|sentence| matches!(sentence, Sentence::Bubble { .. }))
        .count();
    assert_eq!(bubbles, 0);
    let rules = loaded
        .definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter(|sentence| {
            matches!(
                sentence,
                Sentence::Rule { attributes, .. }
                    if attributes.source() == Some("cells.k")
            )
        })
        .filter_map(sentence_summary)
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(rules);
    });
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_three_sibling_rule_cells_associate_left() {
    // reference: k/result/bin/kompile test.k --backend kore --main-module TEST --emit-json
    let source = include_str!("fixtures/reference/inner/cell-association/test.k");
    let oracle: CellAssociationOracle = toml::from_str(include_str!(
        "fixtures/reference/inner/cell-association/association.toml"
    ))
    .expect("reference cell-association oracle should parse");
    let prelude = k_rust::builtin::embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        k_rust::builtin::embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("cell-association.k", source),
        "TEST",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            ..LoadOptions::default()
        },
    )
    .expect("reference cell-association fixture should load");
    let actual = loaded
        .definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.source() == Some("cell-association.k") => Some(body),
            _ => None,
        })
        .filter(|body| {
            let mut leaves = Vec::new();
            cell_leaves(body, &mut leaves);
            leaves == ["<k>", "<key>", "<value>"]
        })
        .map(|body| cell_association_shape(body).expect("three sibling cells should form a tree"))
        .collect::<Vec<_>>();
    let expected = oracle
        .rule
        .into_iter()
        .map(|rule| rule.shape)
        .collect::<Vec<_>>();

    assert_eq!(actual, expected);
}

#[cfg(feature = "z3-inference")]
#[test]
fn loader_parses_parenthesized_sequence_rewrites_before_cell_dots() {
    let source = indoc! {r#"
        module MAIN
          syntax Foo ::= "a"
          configuration <k> a </k>
          claim <k> (a ~> _ => .K) ... </k>
          syntax K
          syntax Map
        endmodule
    "#};
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    let loaded = load(
        ResolvedSource::new("parenthesized-rewrite.k", source),
        "MAIN",
        &mut resolver,
    )
    .unwrap();
    let claims = loaded
        .definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(sentence_summary)
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(claims);
    });
}

#[test]
fn loader_parses_legacy_empty_k_before_cell_dots() {
    let source = indoc! {r##"
        module MAIN
          syntax State ::= "a" | ".State"
          syntax KItem ::= "#setAStateSymbolic" [klabel(setAStateSymbolic)]
          syntax Bool ::= condition(State) [function, total, no-evaluators]
          configuration <k> #setAStateSymbolic </k>
                        <a-state> .State </a-state>

          rule <k> #setAStateSymbolic => . ... </k>
               <a-state> _ => ?X </a-state>
               ensures condition(?X)
          syntax K
          syntax Map
        endmodule
    "##};
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    let loaded = load(
        ResolvedSource::new("legacy-empty-k.k", source),
        "MAIN",
        &mut resolver,
    )
    .unwrap();
    let rules = loaded
        .definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(sentence_summary)
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(rules);
    });
}

#[test]
fn loader_parses_rewrites_between_bags_inside_collection_cells() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Stmt ::= insert(Int, Int)
          configuration
            <k> $PGM:Stmt </k>
            <map>
              <entry multiplicity="*" type="Map">
                <key> .K </key>
                <value> .K </value>
              </entry>
            </map>

          rule
            <k> insert(Key, Value) => .K ...</k>
            <map>...
              .Bag => <entry> <key> Key </key> <value> Value </value> </entry>
            ...</map>
          syntax K
          syntax Map
        endmodule
    "#};
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    let loaded = load(
        ResolvedSource::new("collection-cells.k", source),
        "MAIN",
        &mut resolver,
    )
    .unwrap();
    let rules = loaded
        .definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(sentence_summary)
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(rules);
    });
}

#[cfg(feature = "z3-inference")]
#[test]
fn loader_parses_parenthesized_rewrites_between_bags_before_cell_dots() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Stmt ::= insert(Int, Int)
          configuration
            <k> $PGM:Stmt </k>
            <map>
              <entry multiplicity="*" type="Map">
                <key> .K </key>
                <value> .K </value>
              </entry>
            </map>

          rule
            <k> insert(Key, Value) => .K ...</k>
            <map>
              ( .Bag => <entry> <key> Key </key> <value> Value </value> </entry> )
              ...
            </map>
          syntax K
          syntax Map
        endmodule
    "#};
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    let loaded = load(
        ResolvedSource::new("parenthesized-collection-cells.k", source),
        "MAIN",
        &mut resolver,
    )
    .unwrap();

    assert!(
        loaded
            .definition
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .any(|sentence| matches!(sentence, Sentence::Rule { .. }))
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn loader_parses_parenthesized_cell_deletion_inside_collection_cells() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <accounts>
              <account multiplicity="*" type="Map">
                <acctID> 0 </acctID>
              </account>
            </accounts>

          rule <accounts>
            ( <account>
                <acctID> ACCT </acctID>
                ...
              </account>
           => .Bag
            )
            ...
          </accounts>
        endmodule
    "#};
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    let loaded = load(
        ResolvedSource::new("collection-cell-deletion.k", source),
        "MAIN",
        &mut resolver,
    )
    .unwrap();
    let rules = loaded
        .definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(sentence_summary)
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(rules);
    });
}

#[cfg(feature = "z3-inference")]
#[test]
fn loader_keeps_unparenthesized_cell_deletion_inside_collection_cell_scope() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <accounts>
              <account multiplicity="*" type="Map">
                <acctID> 0 </acctID>
              </account>
            </accounts>

          rule <accounts>
            <account>
              <acctID> ACCT </acctID>
              ...
            </account>
            => .Bag
            ...
          </accounts>
        endmodule
    "#};
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    let loaded = load(
        ResolvedSource::new("unparenthesized-collection-cell-deletion.k", source),
        "MAIN",
        &mut resolver,
    )
    .unwrap();
    let body = loaded
        .definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } if body.to_string().starts_with("`<accounts>`") => {
                Some(body.to_string())
            }
            _ => None,
        })
        .expect("the source deletion rule must remain inside the accounts cell");

    assert_eq!(
        body,
        "`<accounts>`(#noDots(.KList),`<account>`(#noDots(.KList),`<acctID>`(#noDots(.KList),#SemanticCastToInt(ACCT),#noDots(.KList)),#dots(.KList))=>#cells(.KList),#dots(.KList))"
    );
}

#[test]
fn rejects_ensures_on_contexts_and_aliases() {
    for source in [
        "module MAIN\ncontext HOLE ensures true\nendmodule",
        "module MAIN\ncontext alias [nope]: HOLE ensures true\nendmodule",
    ] {
        let error = resolve_rule_bubbles(&lowered(source)).unwrap_err();
        assert!(
            matches!(error, RuleError::IllegalEnsures { .. }),
            "{error:?}"
        );
    }
}

#[test]
fn preserves_genuine_ambiguity_until_disambiguation_is_ported() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Exp ::= "same" [symbol(first)]
          syntax Exp ::= "same" [symbol(second)]
          rule same => same
        endmodule
    "#});
    let error = resolve_rule_bubbles(&definition).unwrap_err();
    #[cfg(feature = "z3-inference")]
    let expected = matches!(
        error,
        RuleError::Parse(ref error) if matches!(error.error, ParseError::Ambiguous { .. })
    );
    #[cfg(not(feature = "z3-inference"))]
    let expected = matches!(
        error,
        RuleError::Parse(ref error)
            if matches!(
                error.error,
                ParseError::Z3InferenceRequired { ambiguity: true, .. }
            )
    );
    assert!(expected, "{error:?}");
}

#[test]
fn reference_scan_c_uppercase_identifier_is_a_variable_over_a_prec1_token() {
    let source = include_str!("fixtures/reference/inner/tokens/scan-c.k");
    let definition = resolve_rule_bubbles(&lowered(source)).expect("rule should parse");
    let body = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .expect("resolved rule should exist");
    let mut variables = Vec::new();
    let mut id_tokens = Vec::new();
    body.visit_preorder(&mut |term| match term.unannotated() {
        Term::Variable { name, sort } if name == "X" => variables.push(sort.clone()),
        Term::Token { token, sort } if token == "X" && sort == &Sort::new("Id") => {
            id_tokens.push(token.clone());
        }
        _ => {}
    });

    assert_eq!(variables, [None, None]);
    assert!(id_tokens.is_empty(), "X was silently parsed as an Id token");
}

#[test]
fn reference_scan_a_lowercase_klabel_application_resolves_to_the_user_production() {
    let source = include_str!("fixtures/reference/inner/tokens/scan-a.k");
    let definition = resolve_rule_bubbles(&lowered(source)).expect("rule should parse");
    let body = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .expect("resolved rule should exist");
    let mut pluses = 0;
    body.visit_preorder(&mut |term| {
        if matches!(term.unannotated(), Term::Apply { label, .. } if label.name == "plus") {
            pluses += 1;
        }
    });
    assert_eq!(
        pluses, 2,
        "both application and infix syntax resolve to plus"
    );
}

#[test]
fn reference_scan_b_lowercase_identifier_is_not_a_user_token_in_rules() {
    let source = include_str!("fixtures/reference/inner/tokens/scan-b.k");
    let error = resolve_rule_bubbles(&lowered(source)).unwrap_err();
    assert!(
        matches!(
            error,
            RuleError::Parse(ref error)
                if matches!(error.error, ParseError::NoParse { .. })
        ),
        "{error:?}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_scan_d_upperid_token_and_variable_are_a_reported_ambiguity() {
    let source = include_str!("fixtures/reference/inner/tokens/scan-d.k");
    let error = resolve_rule_bubbles(&lowered(source)).unwrap_err();
    let RuleError::Parse(error) = error else {
        panic!("expected a parse error, got {error:?}")
    };
    let ParseError::Ambiguous { alternatives, .. } = error.error else {
        panic!("expected ambiguity, got {:?}", error.error)
    };
    assert_eq!(alternatives.len(), 2, "{alternatives:#?}");
    assert!(alternatives.iter().any(|alternative| {
        alternative
            .production
            .as_deref()
            .is_some_and(|production| production.contains("syntax Id ::= #UpperId [token]"))
            && alternative.term.contains("#token(\"X\",\"Id\")")
    }));
    assert!(alternatives.iter().any(|alternative| {
        alternative
            .production
            .as_deref()
            .is_some_and(|production| production.contains("syntax K ::= K \":K\""))
            && alternative.term.contains("#SemanticCastToK(X)")
    }));
}

#[test]
fn reference_invalid_prec_is_rejected_without_any_rule_bubble() {
    let source = include_str!("fixtures/reference/inner/tokens/invalidPrec.k");
    let error = resolve_rule_bubbles(&lowered(source)).unwrap_err();
    assert!(matches!(
        error,
        RuleError::InconsistentTokenPrecedence {
            ref declarations,
            ..
        } if declarations.len() == 2
    ));
    assert!(
        error
            .to_string()
            .starts_with("Inconsistent token precedence detected.")
    );
    assert!(
        error
            .to_string()
            .contains("syntax Foo ::= r\"[0-9]+\" [token]")
    );
    assert!(
        error
            .to_string()
            .contains("syntax Int ::= r\"[0-9]+\" [prec(2), token]")
    );
}

#[test]
fn imported_rule_modules_use_the_main_modules_global_scanner() {
    let source = indoc! {r#"
        module TOKEN
          syntax Id ::= r"[A-Z]+" [prec(3), token]
        endmodule
        module RULES
          rule X => X
        endmodule
        module MAIN
          imports TOKEN
          imports RULES
        endmodule
    "#};
    let error = resolve_rule_bubbles(&lowered(source)).unwrap_err();
    assert!(matches!(
        error,
        RuleError::Parse(ref error)
            if error.module == "RULES" && matches!(error.error, ParseError::NoParse { .. })
    ));
}

#[test]
fn reference_private_import_hides_imported_syntax_from_rules() {
    let source = include_str!("fixtures/reference/inner/signature/private-import/test.k");
    let parsed = k_rust::outer::parse("private-import/test.k", source).unwrap();
    let definition = k_rust::outer::lower(&parsed, "PRIVATE-IMPORT").unwrap();
    let error = resolve_rule_bubbles(&definition)
        .expect_err("BASE's syntax must not cross MID's private import");

    assert!(
        matches!(
            error,
            RuleError::Parse(ref error)
                if error.module == "PRIVATE-IMPORT"
                    && matches!(error.error, ParseError::NoParse { position: 4, .. })
        ),
        "{error:?}"
    );
}

#[test]
fn reference_private_import_explicit_hides_imported_syntax_from_rules() {
    let source = include_str!("fixtures/reference/inner/signature/private-import-explicit/test.k");
    let parsed = k_rust::outer::parse("private-import-explicit/test.k", source).unwrap();
    let definition = k_rust::outer::lower(&parsed, "PRIVATE-IMPORT-EXPLICIT").unwrap();
    let error = resolve_rule_bubbles(&definition)
        .expect_err("BASE's syntax must not cross MID's explicit private import");

    assert!(
        matches!(
            error,
            RuleError::Parse(ref error)
                if error.module == "PRIVATE-IMPORT-EXPLICIT"
                    && matches!(error.error, ParseError::NoParse { position: 4, .. })
        ),
        "{error:?}"
    );
}

#[test]
fn reference_signature_k_reports_six_visibility_errors() {
    let source = include_str!("fixtures/reference/inner/signature/signature.k");
    let parsed = k_rust::outer::parse("signature.k", source).unwrap();
    let definition = k_rust::outer::lower(&parsed, "SIGNATURE").unwrap();
    let hidden_rules = [
        "foo() => .K",
        "bam() => .K",
        "fu() => .K",
        "bar => .K",
        "baz => .K",
        "b() => .K",
    ];

    for hidden_rule in hidden_rules {
        let mut one_rule = definition.clone();
        let module = one_rule
            .modules
            .iter_mut()
            .find(|module| module.name == "C")
            .unwrap();
        module.local_sentences.retain(|sentence| {
            !matches!(
                sentence,
                Sentence::Bubble {
                    sentence_type,
                    contents,
                    ..
                } if sentence_type == "rule" && contents != hidden_rule
            )
        });
        let error = resolve_rule_bubbles(&one_rule)
            .expect_err("syntax outside C's signature must be rejected");
        assert!(
            matches!(
                error,
                RuleError::Parse(ref error)
                    if error.module == "C" && matches!(error.error, ParseError::NoParse { .. })
            ),
            "{hidden_rule}: {error:?}"
        );
    }

    let mut public_rule = definition;
    let module = public_rule
        .modules
        .iter_mut()
        .find(|module| module.name == "C")
        .unwrap();
    module.local_sentences.retain(|sentence| {
        !matches!(
            sentence,
            Sentence::Bubble {
                sentence_type,
                contents,
                ..
            } if sentence_type == "rule" && contents != "a() => .K"
        )
    });
    resolve_rule_bubbles(&public_rule).expect("B's public a() production stays visible in C");
}

fn selector_source(attribute: &str) -> String {
    format!(
        r#"module MAIN
syntax Int ::= r"[0-9]+" [token]
syntax Exp ::= Int
syntax Exp ::= Exp "+" Exp [symbol(plus), {attribute}]
syntax Exp ::= Exp "*" Exp [symbol(times)]
rule 1 + 2 * 3 => 1
endmodule"#
    )
}

#[cfg(not(feature = "z3-inference"))]
fn assert_ambiguity_requires_z3(source: &str) {
    assert!(matches!(
        resolve_rule_bubbles(&lowered(source)),
        Err(RuleError::Parse(ref error))
            if matches!(
                error.error,
                ParseError::Z3InferenceRequired {
                    ambiguity: true,
                    ..
                }
            )
    ));
}

#[test]
fn preferred_production_selects_its_ambiguity_branch() {
    let source = selector_source("prefer");
    #[cfg(feature = "z3-inference")]
    assert_rule_resolution_snapshot!(source.as_str());
    #[cfg(not(feature = "z3-inference"))]
    assert_ambiguity_requires_z3(&source);
}

#[test]
fn avoided_production_removes_its_ambiguity_branch() {
    let source = selector_source("avoid");
    #[cfg(feature = "z3-inference")]
    assert_rule_resolution_snapshot!(source.as_str());
    #[cfg(not(feature = "z3-inference"))]
    assert_ambiguity_requires_z3(&source);
}

#[test]
fn infers_a_rule_parameter_used_as_the_result_sort() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Box ::= "box(" Int ")" [symbol(box)]
          syntax {S} S ::= "same(" S ")" [symbol(same)]
          rule box(same(1)) => box(1)
        endmodule
    "#};
    assert_rule_resolution_snapshot!(source);
}

#[test]
fn infers_a_rule_parameter_used_only_by_an_argument() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax {S} Int ::= "take(" S ")" [symbol(take)]
          rule take(1) => 1
        endmodule
    "#};
    assert_rule_resolution_snapshot!(source);
}

#[test]
fn parametric_origin_nodes_get_per_node_parameter_variables() {
    let source = indoc! {r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax Pair ::= "pair(" A "," B ")" [symbol(pair)]
          syntax {S} S ::= "same(" S ")" [symbol(same)]
          rule pair(same(a), same(b)) => pair(a, b)
        endmodule
    "#};
    let resolved = resolve_rule_bubbles(&lowered(source)).unwrap();
    let body = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .expect("the rule should be resolved");

    assert!(body.contains("same{A}"), "{body}");
    assert!(body.contains("same{B}"), "{body}");
}

#[cfg(feature = "z3-inference")]
rule_snapshot!(
    z3_prunes_ill_typed_ambiguity_branches,
    r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax Exp ::= "f(" A ")" [symbol(fa)]
                       | "f(" B ")" [symbol(fb)]
          syntax Pair ::= "pair(" Exp "," A ")" [symbol(pair)]
          rule pair(f(X), X) => pair(f(a), a)
        endmodule
    "#
);

#[cfg(not(feature = "z3-inference"))]
#[test]
fn portable_build_reports_ambiguity_that_requires_z3() {
    let error = resolve_rule_bubbles(&lowered(indoc! {r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax Exp ::= "f(" A ")" [symbol(fa)]
                       | "f(" B ")" [symbol(fb)]
          syntax Pair ::= "pair(" Exp "," A ")" [symbol(pair)]
          rule pair(f(X), X) => pair(f(a), a)
        endmodule
    "#}))
    .unwrap_err();
    assert!(matches!(
        error,
        RuleError::Parse(ref error)
            if matches!(
                error.error,
                ParseError::Z3InferenceRequired {
                    ambiguity: true,
                    ..
                }
            )
    ));
}

rule_snapshot!(
    resolves_syntax_priority,
    r#"
        module MAIN
          syntax Id ::= r"[a-z]" [prec(3), token]
          syntax Exp ::= Id
          syntax Exp ::= Exp "*" Exp [symbol(times)]
                       > Exp "+" Exp [symbol(plus)]
          rule a + b * c => c * b + a
        endmodule
    "#
);

#[cfg(feature = "z3-inference")]
fn prefix_list_rule_source(priority: &str, rule: &str) -> String {
    // The parametric bracket is the reduced KSEQ declaration from builtin/kast.md.
    // Its priority must apply to the enclosed list, including concrete instantiations.
    indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Name ::= "+" [symbol(plus)]
          syntax Exp ::= Int | Name
                       | "(" Name ExpList ")" [symbol(prefix)]
          syntax ExpList ::= List{Exp,""}
            [symbol(expressions), terminator-symbol(.Expressions), group(expList)]
          syntax {S} S ::= "(" S ")"
            [bracket, group(defaultBracket), applyPriority(1)]
          PRIORITY
          rule RULE
        endmodule
    "#}
    .replace("PRIORITY", priority)
    .replace("RULE", rule)
}

#[cfg(feature = "z3-inference")]
#[test]
fn bracket_priority_selects_prefix_application_over_a_bracketed_list() {
    for rule in ["(+ I1:Int I2:Int) => I1", "(+ 1 2) => 1"] {
        let source = prefix_list_rule_source("syntax priority defaultBracket > expList", rule);
        let resolved = resolve_rule_bubbles(&lowered(&source)).unwrap();
        let body = resolved
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::Rule { body, .. } => Some(body),
                _ => None,
            })
            .unwrap();
        let Term::Rewrite { left, .. } = body.unannotated() else {
            panic!("expected a rewrite: {body}");
        };
        let Term::Apply { label, arguments } = left.unannotated() else {
            panic!("expected a prefix application: {left}");
        };
        assert_eq!(label.name, "prefix");
        let [name, arguments] = arguments.as_slice() else {
            panic!("prefix application has a name and its argument list: {left}");
        };
        assert_eq!(name, &Term::apply("plus", vec![]));
        let mut rest = arguments;
        let mut entries = 0;
        while let Term::Apply { label, arguments } = rest.unannotated() {
            if label.name != "expressions" {
                break;
            }
            let [_, tail] = arguments.as_slice() else {
                panic!("list constructor has an element and tail: {rest}");
            };
            entries += 1;
            rest = tail;
        }
        assert_eq!(entries, 2, "{left}");
        assert_eq!(rest, &Term::apply(".Expressions", vec![]));
    }
}

#[cfg(feature = "z3-inference")]
#[test]
fn declared_bracket_priority_preserves_parenthesized_rewrite_scope() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax {S} S ::= "(" S ")" [bracket, applyPriority(1)]
          rule (1 => 2)
        endmodule
    "#};
    let resolved = resolve_rule_bubbles(&lowered(source)).unwrap();
    assert!(resolved.main_module().unwrap().local_sentences.iter().any(|sentence| {
        matches!(sentence, Sentence::Rule { body, .. } if matches!(body.unannotated(), Term::Rewrite { .. }))
    }));
}

#[cfg(feature = "z3-inference")]
#[test]
fn implicit_kseq_bracket_priority_selects_the_prefix_application() {
    let source = prefix_list_rule_source(
        "syntax priority defaultBracket > expList",
        "(+ I1:Int I2:Int) => I1",
    );
    // KSEQ is available to the implicit rule grammar without a user-module import.
    let source = source.replace(
        "syntax {S} S ::= \"(\" S \")\"\n    [bracket, group(defaultBracket), applyPriority(1)]",
        "",
    );
    let source = format!(
        "{source}\nmodule KSEQ\n syntax {{S}} S ::= \"(\" S \")\" [bracket, group(defaultBracket), applyPriority(1)]\nendmodule\n"
    );
    let resolved = resolve_rule_bubbles(&lowered(&source)).unwrap();
    let body = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    let Term::Rewrite { left, .. } = body.unannotated() else {
        panic!("expected a rewrite: {body}");
    };
    assert!(
        matches!(left.unannotated(), Term::Apply { label, .. } if label.name == "prefix"),
        "{left}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn prefix_application_and_bracketed_list_remain_distinct_without_the_priority() {
    for priority in ["", "syntax priority expList > defaultBracket"] {
        let source = prefix_list_rule_source(priority, "(+ I1:Int I2:Int) => I1");
        let error = resolve_rule_bubbles(&lowered(&source)).unwrap_err();
        let RuleError::Parse(error) = error else {
            panic!("expected a parse error: {error:?}");
        };
        let ParseError::Ambiguous { alternatives, .. } = error.error else {
            panic!(
                "expected distinct prefix/list interpretations: {:?}",
                error.error
            );
        };
        assert!(
            alternatives
                .iter()
                .any(|alternative| alternative.term.contains("prefix(")),
            "{alternatives:?}"
        );
        assert!(
            alternatives
                .iter()
                .any(|alternative| alternative.term.contains("expressions(plus(")),
            "{alternatives:?}"
        );
    }
}

rule_snapshot!(
    resolves_prefix_terminals_with_the_global_scanner,
    r#"
        module MAIN
          syntax Id ::= r"[a-z]" [prec(3), token]
          syntax Exp ::= Id
          syntax Exp ::= Exp "==" Exp [symbol(eq)]
          syntax Exp ::= Exp "==K" Exp [symbol(eqK)]
          rule a ==K b => a == b
        endmodule
    "#
);

rule_snapshot!(
    resolves_left_and_right_associativity,
    r#"
        module MAIN
          syntax Id ::= r"[a-z]" [prec(3), token]
          syntax LeftExp ::= Id
          syntax LeftExp ::= left: LeftExp "+" LeftExp [symbol(leftPlus)]
          syntax RightExp ::= Id
          syntax RightExp ::= right: RightExp "^" RightExp [symbol(rightPow)]
          rule a + b + c => a + b + c
          rule a ^ b ^ c => a ^ b ^ c
        endmodule
    "#
);

rule_snapshot!(
    scopes_a_top_level_rewrite_over_boolean_connectives,
    r##"
        module MAIN
          syntax Bool ::= "a" [symbol(a)]
          syntax Bool ::= Bool "#And" Bool [symbol(#And), assoc, left]
          rule a => a #And a
        endmodule
    "##
);

rule_snapshot!(
    scopes_a_cross_sort_top_level_rewrite_over_its_rhs_operator,
    r#"
        module MAIN
          syntax Pgm ::= "run" [symbol(run)]
          syntax Exp ::= "value" [symbol(value)]
                       | Exp "*" Exp [symbol(times)]
          rule run => value * value
        endmodule
    "#
);

#[cfg(feature = "z3-inference")]
rule_snapshot!(
    prefers_a_lifted_rewrite_over_a_nested_operator_interpretation,
    r#"
        module MAIN
          syntax Key ::= "a" [symbol(a)]
          syntax Value ::= "b" [symbol(b)] | "c" [symbol(c)]
          syntax Pair ::= Key "|->" Value [symbol(pair)]
          syntax Foo ::= "foo(" Pair ")" [symbol(foo)]
          rule foo(a |-> b => a |-> c)
        endmodule
    "#
);

#[cfg(feature = "z3-inference")]
rule_snapshot!(
    scopes_rewrites_inside_local_functions_before_infix_operators,
    r##"
        module MAIN
          syntax Type ::= "type" [symbol(type)]
          syntax KItem ::= Type
          syntax Map ::= KItem "|->" KItem [symbol(pair)]
          syntax KItem ::= Map
          syntax Foo ::= "foo(" Map ")" [symbol(foo)]
          rule foo(type |-> type => type |-> #fun(T::Type => T |-> T)(type))
        endmodule
    "##
);

#[cfg(feature = "z3-inference")]
rule_snapshot!(
    prefers_the_most_specific_generated_bracket,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax AExp ::= Int | "(" AExp ")" [bracket]
          syntax KResult ::= Int
          syntax Map ::= ".Map" [symbol(dotMap)]
                       | KItem "|->" KItem [symbol(mapEntry)]
          syntax KItem ::= Map
          rule (0 |-> (_ => I:Int)) => .Map
        endmodule
    "#
);

rule_snapshot!(
    parses_whitespace_between_an_unquoted_prefix_label_and_parenthesis,
    r#"
        module MAIN
          syntax Float ::= r"[0-9]+" [token]
          syntax Pgm ::= f32mul ( Float, Float )
          rule f32mul ( F1, F2 ) => f32mul(F2, F1)
        endmodule
    "#
);

rule_snapshot!(
    brackets_shield_associativity,
    r#"
        module MAIN
          syntax Id ::= r"[a-z]" [prec(3), token]
          syntax Exp ::= Id
          syntax Exp ::= "(" Exp ")" [bracket]
          syntax Exp ::= left: Exp "+" Exp [symbol(plus)]
          rule a + (b + c) => (a + b) + c
        endmodule
    "#
);

rule_snapshot!(
    parses_and_cleans_all_cast_forms,
    r#"
        module MAIN
          syntax Id ::= r"[a-z]" [prec(3), token]
          syntax Exp ::= Id
          syntax Exp ::= "e" [symbol(e)]
          rule X::Exp => {X}::Exp
          rule X:Exp => {X}:>Exp
          rule e::Exp => {e}::Exp
        endmodule
    "#
);

rule_snapshot!(
    uses_layout_from_an_imported_module,
    r#"
        module CUSTOM-LAYOUT
          syntax #Layout ::= r"(~+)" | r"([ \n\r\t])"
        endmodule

        module MAIN
          imports CUSTOM-LAYOUT
          syntax Exp ::= "x" [klabel(x)]
          rule ~~ x ~~~ => x
        endmodule
    "#
);

#[test]
fn rejects_an_unscoped_cast_over_a_production_ending_in_a_nonterminal() {
    let source = indoc! {r#"
        module MAIN
          syntax Atom ::= r"[a-z]" [prec(3), token]
          syntax Other ::= Atom
          syntax Exp ::= "f" Other [symbol(f)]
          rule f a::Exp => f a
        endmodule
    "#};
    let definition = lowered(source);
    let error = resolve_rule_bubbles(&definition).unwrap_err();
    assert!(matches!(
        error,
        RuleError::Parse(ref error)
            if matches!(error.error, ParseError::CastPriority { .. })
    ));

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(error);
    });
}

rule_snapshot!(
    resolves_generic_k_applications,
    r#"
        module MAIN
          syntax Id ::= r"[a-z]" [prec(3), token]
          syntax Exp ::= Id
          syntax Exp ::= "zero" [symbol(zero)]
          syntax Exp ::= Exp "+" Exp [symbol(_+_)]
          syntax Exp ::= "tri" Exp Exp Exp [symbol(tri)]
          rule `_+_`(`_+_`(a, b), c) => zero(.KList)
          rule tri(a, b, c) => tri a b c
        endmodule
    "#
);

rule_snapshot!(
    resolves_an_explicit_kast_token_over_a_generic_application,
    r##"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= "use" "(" Int ")" [symbol(use)]
          rule use(#token("1", "Int")) => use(1)
        endmodule
    "##
);

rule_snapshot!(
    parses_an_explicit_kast_label,
    r##"
        module MAIN
          syntax KItem ::= "hold" "(" KItem ")" [symbol(hold)]
                         | "foo" [symbol(foo)]
          rule hold(#klabel(foo)) => hold(foo)
        endmodule
    "##
);

rule_snapshot!(
    infers_the_tightest_shared_variable_sort,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Pair ::= "pair(" Exp "," Int ")" [symbol(pair)]
          rule pair(X, X) => pair(X, X)
        endmodule
    "#
);

rule_snapshot!(
    infers_anonymous_variable_occurrences_independently,
    r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax Pair ::= "pair(" A "," B ")" [symbol(pair)]
          rule pair(_, _) => pair(_, _)
        endmodule
    "#
);

rule_snapshot!(
    #[cfg(feature = "z3-inference")]
    infers_anonymous_collection_values_at_their_exact_kitem_sort,
    r#"
        module MAIN
          syntax Val ::= "a" [symbol(a)]
          syntax KItem ::= Val
          syntax Map ::= ".Map" [symbol(dotMap)]
                       | KItem "|->" KItem [symbol(mapEntry)]
          syntax KItem ::= Map
          rule (a |-> _) => .Map
        endmodule
    "#
);

rule_snapshot!(
    #[cfg(feature = "z3-inference")]
    shares_inference_identity_for_a_parenthesized_rewrite_across_bracket_alternatives,
    r#"
        module MAIN
          syntax Id ::= r"[a-z]+" [prec(3), token]
          syntax KItem ::= Id
          syntax Map ::= ".Map" [symbol(dotMap)]
                       | KItem "|->" KItem [symbol(mapEntry)]
          syntax KItem ::= Map
          rule x |-> (_ => ?_) => .Map
        endmodule
    "#
);

rule_snapshot!(
    #[cfg(feature = "z3-inference")]
    infers_shared_collection_values_at_kitem_instead_of_k,
    r#"
        module MAIN
          syntax Id ::= r"[a-z]+" [prec(3), token]
          syntax KItem ::= Id
          syntax Map ::= ".Map" [symbol(dotMap)]
                       | KItem "|->" KItem [symbol(mapEntry)]
          syntax KItem ::= Map
                       | "(" KItem ")" [bracket]
          rule X:Id ~> (X |-> I) => I
        endmodule
    "#
);

rule_snapshot!(
    infers_boolean_condition_variables_from_builtin_rule_syntax,
    r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          rule a => a requires B
        endmodule
    "#
);

rule_snapshot!(
    infers_an_anonymous_bag_variable,
    r#"
        module MAIN
          syntax Result ::= "clear" "(" Bag ")" [symbol(clear)]
          rule clear(_) => clear(.Bag)
        endmodule
    "#
);

#[test]
fn infers_an_anonymous_cell_variable() {
    let source = indoc! {r#"
        module MAIN
          syntax Result ::= "clear" "(" Cell ")" [symbol(clear)]
          rule clear(_) => clear(_)
        endmodule
    "#};
    let resolved = resolve_rule_bubbles(&lowered(source)).unwrap();
    let body = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .unwrap();

    assert_eq!(
        body,
        "clear(#SemanticCastToCell(_))=>clear(#SemanticCastToCell(_))"
    );
}

rule_snapshot!(
    collapses_record_productions_and_fills_omitted_fields,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Pair ::= "pair" "(" left: Int "," right: Int ")" [symbol(pair)]
          rule pair(... right: 2, left: 1) => pair(... left: 3)
          rule pair(... left: 4) => pair(... left: 5)
        endmodule
    "#
);

rule_snapshot!(
    #[cfg(feature = "z3-inference")]
    collapses_a_record_pattern_before_an_as_pattern,
    r##"
        module MAIN
          syntax Map ::= ".Map" [symbol(dotMap)]
          syntax Int ::= "0" [symbol(zero)]
          syntax TypesInfo ::= "#ti" "(" t2i: Map "," count: Int ")" [symbol(ti)]
          syntax Result ::= "use" "(" TypesInfo ")" [symbol(use)]
          rule use(#ti(... t2i: M) #as TI) => use(TI)
        endmodule
    "##
);

rule_snapshot!(
    parses_nested_collection_operations_in_a_record_field,
    r##"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
                       | Int "+Int" Int [symbol(addInt)]
          syntax Key ::= "key" [symbol(key)]
          syntax KItem ::= Int | Key
          syntax Map ::= ".Map" [symbol(dotMap)]
                       | Map "[" key: KItem "<-" value: KItem "]" [symbol(updateMap), prefer]
          syntax KItem ::= Map "[" KItem "]" "orDefault" KItem [symbol(lookupMap)]
          syntax TypesInfo ::= "#ti" "(" t2i: Map "," count: Int ")" [symbol(ti)]
          syntax Result ::= "use" "(" TypesInfo ")" [symbol(use)]
          rule use(#ti(... t2i: M, count: N))
            => use(#ti(... t2i: M [ key <- (M [ key ] orDefault N) ], count: N +Int 1))
        endmodule
    "##
);

rule_snapshot!(
    #[cfg(feature = "z3-inference")]
    collapses_a_record_with_a_rewrite_in_a_field,
    r##"
        module MAIN
          syntax Defn ::= "t" [symbol(t)]
          syntax Defns ::= List{Defn, ""} [symbol(listDefns), terminator-symbol(".Defns")]
          syntax ModuleDecl ::= "#module" "(" types: Defns "," funcs: Defns ")" [symbol(aModuleDecl)]
          syntax Result ::= "#structureModule" "(" Defns "," ModuleDecl ")" [symbol(structureModule)]
          rule #structureModule((T:Defn DS:Defns => DS), #module(... types: TS => T TS))
        endmodule
    "##
);

rule_snapshot!(
    collapses_single_and_unnamed_record_productions,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Box ::= "box" "(" value: Int ")" [symbol(box)]
          syntax Pair ::= "pair" "(" Int "," Int ")" [symbol(pair)]
          rule box(... value: 1) => box(...)
          rule `box`(2) => box(... value: 2)
          rule pair(...) => pair(...)
        endmodule
    "#
);

#[test]
fn rejects_duplicate_record_production_keys() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Pair ::= "pair" "(" left: Int "," right: Int ")" [symbol(pair)]
          rule pair(... left: 1, left: 2) => pair(...)
        endmodule
    "#});
    let error = resolve_rule_bubbles(&definition).unwrap_err();
    assert!(
        matches!(
            error,
            RuleError::Parse(ref error)
                if matches!(
                    error.error,
                    ParseError::RecordProduction { ref message }
                        if message == "Duplicate record production key: left"
                )
        ),
        "{error:?}"
    );
}

#[test]
fn rejects_incompatible_variable_sort_bounds() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax Pair ::= "pair(" A "," B ")" [symbol(pair)]
          rule pair(X, X) => pair(X, X)
        endmodule
    "#});
    let error = resolve_rule_bubbles(&definition).unwrap_err();
    assert!(
        matches!(
            error,
            RuleError::Parse(ref error)
                if matches!(error.error, ParseError::SortInference { .. })
        ),
        "{error:?}"
    );
}

#[test]
fn anywhere_rules_cannot_widen_the_rewrite_sort() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Small ::= "small" [symbol(small)]
          syntax Big ::= Small
          syntax Big ::= "big" [symbol(big)]
          rule small => big [anywhere]
        endmodule
    "#});
    let error = resolve_rule_bubbles(&definition).unwrap_err();
    assert!(
        matches!(
            error,
            RuleError::Parse(ref error)
                if matches!(error.error, ParseError::SortInference { .. })
        ),
        "{error:?}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn anywhere_attributes_do_not_constrain_nested_rewrites() {
    for attribute in ["anywhere", "simplification"] {
        let source = format!(
            r#"
            module MAIN
              syntax A ::= "a" [symbol(a)]
              syntax B ::= "b" [symbol(b)]
              syntax Base ::= A | B
              syntax Foo ::= "foo(" Base ")" [symbol(foo)]
              rule foo(a => b) [{attribute}]
            endmodule
            "#
        );
        resolve_rule_bubbles(&lowered(&source)).unwrap_or_else(|error| {
            panic!("nested rewrite with [{attribute}] should parse: {error}")
        });
    }
}

#[test]
fn ordinary_rules_may_widen_the_rewrite_sort() {
    let resolved = resolve_rule_bubbles(&lowered(indoc! {r#"
        module MAIN
          syntax Small ::= "small" [symbol(small)]
          syntax Big ::= Small
          syntax Big ::= "big" [symbol(big)]
          rule small => big
        endmodule
    "#}))
    .unwrap();
    assert!(resolved.main_module().unwrap().local_sentences.iter().any(
        |sentence| matches!(sentence, Sentence::Rule { body, .. } if body.to_string() == "small(.KList)=>big(.KList)")
    ));
}

#[test]
fn function_rules_cannot_widen_the_rewrite_sort() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Small ::= "small" [symbol(small), function]
          syntax Big ::= Small
          syntax Big ::= "big" [symbol(big)]
          rule small => big
        endmodule
    "#});
    let error = resolve_rule_bubbles(&definition).unwrap_err();
    assert!(
        matches!(
            error,
            RuleError::Parse(ref error)
                if matches!(error.error, ParseError::SortInference { .. })
        ),
        "{error:?}"
    );
}

#[test]
fn reports_unknown_generic_k_applications() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Id ::= r"[a-z]" [prec(3), token]
          syntax Exp ::= Id
          rule missing(a) => a
        endmodule
    "#});
    let error = resolve_rule_bubbles(&definition).unwrap_err();
    assert!(
        matches!(
            error,
            RuleError::Parse(ref error)
                if matches!(
                    error.error,
                    ParseError::UnknownApplication { ref label, arity: 1 } if label == "missing"
                )
        ),
        "{error:?}"
    );
}

rule_snapshot!(
    retains_concrete_syntax_when_a_generic_application_is_invalid,
    r##"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Stack ::= ".Stack" [symbol(.Stack)]
          syntax Int ::= "#size" "(" Stack ")" [symbol(#size), function]
                       | "#size" "(" Stack "," Int ")" [symbol(sizeAux), function]
          rule #size(.Stack, 0) => 0
        endmodule
    "##
);

rule_snapshot!(
    does_not_duplicate_generated_sort_lattice_productions,
    r#"
        module MAIN
          syntax KBott
          syntax KItem
          syntax {Sort} Sort ::= KBott
          syntax {Sort} KItem ::= Sort
          syntax Int ::= r"[0-9]+" [token]
          syntax Bool ::= Int "<Int" Int [symbol(_<Int_)]
          syntax Buf ::= ".Buf" [symbol(.Buf)]
          syntax Buf ::= Buf "[" Int ":=" Buf "]" [symbol(write), function]
          rule _ [ START := _ ] => .Buf requires START <Int 0
        endmodule
    "#
);

rule_snapshot!(
    does_not_duplicate_explicit_kitem_subsorts,
    r##"
        module MAIN
          syntax KItem
          syntax Int ::= r"[0-9]+" [token]
          syntax Bytes ::= "bytes" [symbol(bytes)]
          syntax String ::= "\"\"" [symbol(emptyString)]
          syntax Map ::= ".Map" [symbol(.Map)]
          syntax Int ::= "lengthBytes" "(" Bytes ")" [symbol(lengthBytes), function]
                       | Bytes "[" Int "]" [symbol(bytesGet), function]
          syntax Bool ::= Int ">Int" Int [symbol(_>Int_), function]
                        | Int "=/=Int" Int [symbol(_=/=Int_), function]
                        | Bool "andBool" Bool [symbol(_andBool_), function, left]
          syntax Tree ::= ".Tree" [symbol(.Tree)]
                        | "branch" "(" Map "," String ")" [symbol(branch)]
                        | "leaf" "(" Bytes "," String ")" [symbol(leaf)]
          syntax KItem ::= Tree
          syntax Tree ::= "put" "(" Tree "," Bytes "," String ")" [symbol(put), function]
          rule put(leaf(LEAFPATH, LEAFVALUE), PATH, VALUE)
            => put(put(branch(.Map, ""), LEAFPATH, LEAFVALUE), PATH, VALUE)
            requires lengthBytes(LEAFPATH) >Int 0
             andBool lengthBytes(PATH) >Int 0
             andBool LEAFPATH[0] =/=Int PATH[0]
        endmodule
    "##
);

rule_snapshot!(
    #[cfg(feature = "z3-inference")]
    uses_the_shared_rewrite_sort_to_prune_syntax_alternatives,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Bool ::= Int "<Int" Int [symbol(_<Int_)]
          syntax Buf ::= ".Buf" [symbol(.Buf)]
          syntax Buf ::= Buf "[" Int ":=" Buf "]" [symbol(writeBuf), function]
          syntax Stack ::= ".Stack" [symbol(.Stack)]
          syntax Stack ::= Stack "[" Int ":=" Stack "]" [symbol(writeStack), function]
          rule _ [ START := _ ] => .Buf requires START <Int 0
        endmodule
    "#
);

rule_snapshot!(
    parses_large_generic_application_argument_lists_without_forest_truncation,
    r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
          syntax Exp ::= "declared-f" "(" Exp "," Exp "," Exp "," Exp "," Exp "," Exp "," Exp "," Exp "," Exp "," Exp "," Exp ")" [symbol(f)]
          rule f(a, a, a, a, a, a, a, a, a, a, a) => a
        endmodule
    "#
);

rule_snapshot!(
    scans_adjacent_closing_brackets_as_separate_terminals,
    r#"
        module MAIN
          syntax Item ::= "x" [symbol(x)]
                        | "[" Items "]" [symbol(list)]
          syntax Items ::= List{Item, ","} [symbol(items)]
          syntax Out ::= "declared-f" "(" Item ")" [symbol(f)]
          rule f([x, [x]]) => f(x)
        endmodule
    "#
);

rule_snapshot!(
    parses_named_anonymous_variables_in_nested_prefix_syntax,
    r##"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Bytes ::= "bytes" [symbol(bytes)]
          syntax PrefixType ::= "#str" | "#list"
          syntax Prefix ::= PrefixType "(" Int "," Int ")"
          syntax JSONs ::= List{JSON, ","} [symbol(jsons)]
          syntax JSON ::= Bytes | "[" JSONs "]" [symbol(jsonList)]
          syntax JSON ::= "#decode" "(" Bytes "," Prefix ")" [symbol(decode)]
          syntax JSONs ::= "#decodeList" "(" Bytes "," Int ")" [symbol(decodeList)]
          rule #decode(BYTES, #list(_LEN, POS)) => [#decodeList(BYTES, POS)]
        endmodule
    "##
);

rule_snapshot!(
    records_variables_inferred_as_the_builtin_bag_sort,
    r#"
        module MAIN
          syntax StateCell ::= "<state>" Bag "</state>" [cell]
          rule <state> ITEMS => .Bag </state>
        endmodule
    "#
);

rule_snapshot!(
    #[cfg(feature = "z3-inference")]
    parses_seven_argument_operations_over_long_word_stacks,
    r##"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax WordStack ::= ".WordStack" [symbol(.WordStack)]
                             | Int ":" WordStack [symbol(_:_)]
          syntax CallOp ::= "CALL" [symbol(CALL)]
          syntax InternalOp ::= CallOp Int Int Int Int Int Int Int [symbol(call)]
          syntax KItem ::= "#exec" "[" CallOp "]" [symbol(exec)]
                         | "#gas" "[" CallOp "," InternalOp "]" [symbol(gas)]
                         | InternalOp
          syntax KCell ::= "<k>" K "</k>" [cell]
          syntax WordStackCell ::= "<wordStack>" WordStack "</wordStack>" [cell]
          rule <k> #exec [ CO:CallOp ] => #gas [ CO, CO W0 W1 W2 W3 W4 W5 W6 ] ~> CO W0 W1 W2 W3 W4 W5 W6 ... </k>
               <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : W6 : WS => WS </wordStack>
        endmodule
    "##
);

rule_snapshot!(
    #[cfg(feature = "z3-inference")]
    parses_a_rewrite_followed_by_a_cast_word_stack_tail,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax WordStack ::= ".WordStack"
                             | Int ":" WordStack
          syntax Bytes ::= Int ":" Bytes [function]
          syntax WordStackCell ::= "<wordStack>" WordStack "</wordStack>" [cell]
          rule <wordStack> ( ( W0:Int => 1 ) : _WS:WordStack ) </wordStack>
        endmodule
    "#
);

rule_snapshot!(
    parses_generated_sort_projection_syntax,
    r#"
        module MAIN
          syntax Set ::= ".Set" [symbol(.Set)]
          syntax SetCell ::= "<set>" Set "</set>" [cell]
          rule <set> project:Set ( .K ) => .Set </set>
        endmodule
    "#
);

#[cfg(feature = "z3-inference")]
rule_snapshot!(
    z3_prunes_ill_typed_overloaded_generic_applications,
    r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax A ::= "pa" A [symbol(pick)]
          syntax B ::= "pb" B [symbol(pick)]
          rule pick(a) => a
        endmodule
    "#
);

#[cfg(not(feature = "z3-inference"))]
#[test]
fn portable_build_reports_overloaded_generic_application_inference_boundary() {
    let source = indoc! {r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax A ::= "pa" A [symbol(pick)]
          syntax B ::= "pb" B [symbol(pick)]
          rule pick(a) => a
        endmodule
    "#};
    // Pruning this ambiguity needs native inference even though only one typing survives.
    assert_ambiguity_requires_z3(source);
}

#[test]
fn reports_overloaded_terminators_without_a_unique_least_sort() {
    let source = indoc! {r#"
        module MAIN
          syntax First ::= "first" [symbol(unit)]
          syntax Second ::= "second" [symbol(unit)]
          syntax General ::= First
                           | Second
                           | "general" [symbol(unit)]
          rule general => general
        endmodule
    "#};
    let definition = lowered(source);
    let error = resolve_rule_bubbles(&definition).unwrap_err();
    assert!(
        matches!(
            error,
            RuleError::Parse(ref error)
                if matches!(
                    error.error,
                    ParseError::OverloadedTerminator { ref possible_sorts }
                        if possible_sorts == &[Sort::new("First"), Sort::new("Second")]
                )
        ),
        "{error:?}"
    );

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(error);
    });
}

#[test]
fn reconstructs_implicit_user_lists_after_sort_inference() {
    let source = indoc! {r#"
        module MAIN
          syntax Id ::= r"[a-z]" [prec(3), token]
          syntax Ids ::= List{Id, ","} [symbol(ids)]
          syntax Wrapped ::= "wrap" Ids [symbol(wrap)]
          rule wrap a => wrap a,b
        endmodule
    "#};
    let definition = lowered(source);
    let resolved = resolve_rule_bubbles(&definition).unwrap();
    let bodies = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(bodies);
    });
}

#[test]
fn wraps_a_single_user_list_element_on_a_function_rhs() {
    let source = indoc! {r##"
        module MAIN
          syntax Item ::= "i" [symbol(i)]
          syntax Items ::= List{Item, ""} [symbol(items), terminator-symbol(.Items)]
          syntax Items ::= "pick" Item [function, symbol(pick)]
          rule pick i => i
        endmodule
    "##};
    let resolved = resolve_rule_bubbles(&lowered(source)).unwrap();
    let body = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    let Term::Rewrite { right, .. } = body.unannotated() else {
        panic!("expected a rewrite, found {body}");
    };

    assert!(
        right.to_string().contains(".Items"),
        "the singleton list should include its terminator: {body}"
    );
}

#[test]
fn infers_empty_user_list_in_a_function_rule() {
    let source = indoc! {r#"
        module MAIN
          syntax TypeKeyWord ::= "param" | "result"
          syntax ValType ::= "i32"
          syntax ValTypes ::= List{ValType, ""} [symbol(listValTypes), terminator-symbol(".List{\"listValTypes\"}")]
          syntax TypeDecl ::= TypeKeyWord ValTypes
          syntax TypeDecls ::= List{TypeDecl, ""} [symbol(listTypeDecl), terminator-symbol(".List{\"listTypeDecl\"}")]
          syntax VecType ::= "[" ValTypes "]" [symbol(aVecType)]
          syntax VecType ::= #gatherTypes(TypeKeyWord, TypeDecls, ValTypes) [function, symbol(gatherTypes)]

          rule #gatherTypes(_, .TypeDecls, TYPES) => [ TYPES ]
        endmodule
    "#};
    let definition = resolve_rule_bubbles(&lowered(source)).unwrap();

    assert!(
        definition
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .any(|sentence| matches!(sentence, Sentence::Rule { .. }))
    );
}

#[test]
fn resolves_an_element_of_an_overloaded_user_list() {
    let source = indoc! {r##"
        module MAIN
          syntax EmptyStmt
          syntax Instr ::= EmptyStmt
          syntax Defn ::= EmptyStmt | "d" [symbol(d)]
          syntax Stmt ::= Instr | Defn
          syntax EmptyStmts ::= List{EmptyStmt, ""} [overload(listStmt), terminator-symbol(".List{\"listStmt\"}")]
          syntax Instrs ::= List{Instr, ""} [overload(listStmt)]
          syntax Defns ::= List{Defn, ""} [overload(listStmt)]
          syntax Stmts ::= List{Stmt, ""} [overload(listStmt)]
          syntax Instrs ::= EmptyStmts
          syntax Defns ::= EmptyStmts
          syntax Stmts ::= Instrs | Defns
          syntax TypesInfo ::= "info" [symbol(info)]
          syntax TypesInfo ::= "#types2indices" "(" Defns "," TypesInfo ")" [function, symbol(types2indices)]
          rule #types2indices(_D DS, M) => #types2indices(DS, M) [owise]
        endmodule
    "##};
    #[cfg(feature = "z3-inference")]
    assert_rule_resolution_snapshot!(source);
    #[cfg(not(feature = "z3-inference"))]
    assert_ambiguity_requires_z3(source);
}

#[cfg(not(feature = "z3-inference"))]
#[test]
fn portable_build_rejects_the_standard_prelude() {
    let error = load_with_prelude("module MAIN endmodule", "test.k", "MAIN")
        .expect_err("the standard prelude requires native Z3 inference");
    assert!(
        matches!(&error, k_rust::outer::LoadError::RuleParsing(RuleError::Parse(error))
            if matches!(error.error, ParseError::Z3InferenceRequired { ambiguity: true, .. })),
        "{error:?}"
    );
}

fn load_with_prelude(
    source: &str,
    name: &str,
    main_module: &str,
) -> Result<k_rust::outer::LoadedDefinition, k_rust::outer::LoadError> {
    let prelude = k_rust::builtin::embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        k_rust::builtin::embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
        ResolvedSource::new(name, source.to_owned()),
        main_module,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            ..LoadOptions::default()
        },
    )
}

#[cfg(feature = "z3-inference")]
#[test]
fn rejects_parametric_completion_without_a_unique_least_upper_bound() {
    // reference: k/result/bin/kompile test.k --backend haskell
    //   --main-module PARAMETRIC-COMPLETION-LUB
    //   --syntax-module PARAMETRIC-COMPLETION-LUB (exit 113 before parsed.txt)
    // AddEmptyLists asks AddSortInjections to complete #fun3's Sort2 parameter from its two
    // parser-layer #KToken children. Both are KBott until TreeNodesToKORE materializes their
    // semantic Missing sort, and filtering KBott's upper bounds leaves no unique admissible LUB.
    let source = include_str!("fixtures/reference/inner/parametric-completion-lub/test.k");
    let Err(error) = load_with_prelude(
        source,
        "parametric-completion-lub.k",
        "PARAMETRIC-COMPLETION-LUB",
    ) else {
        panic!("the reference rejects a parametric production without a unique completion LUB");
    };
    assert!(
        matches!(&error, k_rust::outer::LoadError::RuleParsing(RuleError::Parse(error))
            if matches!(&error.error, ParseError::SortInference { message }
                if message.contains("least upper bound"))),
        "{error:?}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn accepts_parametric_completion_with_an_admissible_singleton_bound() {
    let source = include_str!("fixtures/reference/inner/parametric-completion-lub/control.k");
    load_with_prelude(
        source,
        "parametric-completion-lub-control.k",
        "PARAMETRIC-COMPLETION-LUB-CONTROL",
    )
    .expect("equal Int bounds have the unique admissible completion LUB Int");
}

#[cfg(feature = "z3-inference")]
fn rule_bodies(loaded: &k_rust::outer::LoadedDefinition) -> Vec<String> {
    loaded
        .definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .collect()
}

#[cfg(feature = "z3-inference")]
#[test]
fn mint_literal_width_comes_from_the_token_text() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module CHECKMINTLITERAL --syntax-module CHECKMINTLITERAL --output-definition ref-kompiled (exit 113)
    // EarleyParser substitutes the digits after the first `p`/`P` of a MINT.literal token into
    // the parametric production, so `0p32` is an `MInt{32}` even when the `MInt{6}` instantiation
    // scanned it, and the ordinary `<=Sort` check against `foo(MInt{6})` then fails.
    let source = include_str!("fixtures/reference/inner/mint3/test.k");
    let Err(error) = load_with_prelude(source, "checkMIntLiteral.k", "CHECKMINTLITERAL") else {
        panic!(
            "the reference rejects foo(0p32) over foo(MInt{{6}}); krust accepted the definition"
        );
    };
    let message = error.to_string();
    assert!(message.contains("Unexpected sort MInt{32}"), "{message}");
    assert!(message.contains("Expected: MInt{6}"), "{message}");
}

#[cfg(feature = "z3-inference")]
#[test]
fn matching_mint_literal_width_is_accepted() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module CHECKMINTLITERAL --syntax-module CHECKMINTLITERAL --output-definition ref-kompiled (exit 0)
    let source = include_str!("fixtures/reference/inner/mint2/test.k");
    let loaded = load_with_prelude(source, "checkMIntLiteral.k", "CHECKMINTLITERAL")
        .expect("the reference accepts foo(0p6) over foo(MInt{6})");
    let bodies = rule_bodies(&loaded);
    assert_eq!(bodies.len(), 1, "{bodies:?}");
    assert!(
        bodies[0].contains("#token(\"0p6\",\"MInt{6}\")"),
        "{}",
        bodies[0]
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn declared_mint_instances_get_the_kitem_subsort_and_casts() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --output-definition ref-kompiled (exit 0)
    // RuleGrammarGenerator builds `KItem ::= MInt{8}` and the `MInt{8}` casts from
    // Module.allSorts, which contains every declared instantiation of a parametric sort.
    let source = include_str!("fixtures/reference/inner/mintcast/test.k");
    let loaded = load_with_prelude(source, "mintcast.k", "TEST")
        .expect("every MInt{8} rule shape of mint-llvm/test.k is accepted by the reference");
    let bodies = rule_bodies(&loaded);
    assert_eq!(bodies.len(), 5, "{bodies:?}");
    let semantic_casts = bodies
        .iter()
        .filter(|body| body.contains("#SemanticCastToMInt{8}"))
        .count();
    assert!(semantic_casts >= 1, "{bodies:?}");
    // `{term}:>MInt{8}` lowers to the projection generated for the cast sort (TreeNodesToKORE).
    assert!(
        bodies.iter().any(|body| body.contains("project:MInt{8}")),
        "{bodies:?}"
    );
}

/// Bodies and conditions of the rule-like sentences the main module declares in `name`, in
/// declaration order, as `body requires requires` text.
#[cfg(feature = "z3-inference")]
fn rule_like_texts(loaded: &k_rust::outer::LoadedDefinition, name: &str) -> Vec<String> {
    loaded
        .definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body,
                requires,
                attributes,
                ..
            }
            | Sentence::Context {
                body,
                requires,
                attributes,
            }
            | Sentence::ContextAlias {
                body,
                requires,
                attributes,
            } if attributes.source() == Some(name) => Some(format!("{body} requires {requires}")),
            _ => None,
        })
        .collect()
}

/// Re-run one test of this binary under the hidden `checked` inference mode, which the
/// conformance driver uses (`ktest.mak` passes `--type-inference-mode checked`): every rule is
/// inferred by both the portable and the Z3 engine and the definition is rejected when they
/// disagree. The child process owns the environment variable, so no other test observes it.
#[cfg(feature = "z3-inference")]
fn assert_test_passes_under_checked_inference(test_name: &str) {
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "--nocapture", test_name])
        .env("KRUST_TYPE_INFERENCE_MODE", "checked")
        .output()
        .expect("the test binary re-runs itself");
    assert!(
        output.status.success(),
        "{test_name} fails under KRUST_TYPE_INFERENCE_MODE=checked:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_withconfig_function_rule_casts_the_variable_at_the_function_sort() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --type-inference-mode checked --output-definition ref-kompiled (exit 0)
    // parsed.txt: rule #withConfig(`foo(_)_TEST_Int_Int`(#token("0","Int"))=>#SemanticCastToInt(I),`<bar>`(#noDots(.KList),#SemanticCastToInt(I),#noDots(.KList))) requires #token("true","Bool") ensures #token("true","Bool")
    // Reduced from regression-new/issue-1436 (test.k:20); configuration-composition
    // (config-comp.k:40), unification-lemmas2 (with-config.k:30) and fun-llvm (fun-test.k:58)
    // have the same shape: a function rule whose rewrite sits under `#withConfig`.
    let source = include_str!("fixtures/reference/inner/withconfig-fn/test.k");
    let loaded = load_with_prelude(source, "test.k", "TEST")
        .expect("the reference accepts the function rule with a configuration context");
    assert_eq!(
        rule_like_texts(&loaded, "test.k"),
        [
            "#withConfig(`foo(_)_TEST_Int_Int`(#token(\"0\",\"Int\"))=>#SemanticCastToInt(I),`<bar>`(#noDots(.KList),#SemanticCastToInt(I),#noDots(.KList))) requires #token(\"true\",\"Bool\")"
        ]
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn withconfig_function_rule_agrees_under_checked_inference() {
    // TypeInferencer.java:592 treats a `#RuleBody`-expected node as a top-sort node, so at :640
    // the `#withConfig` production bounds its rewrite child by the function sort exactly as
    // `#RuleContent` does for a bare rewrite; both engines must instantiate the rewrite at Int.
    assert_test_passes_under_checked_inference(
        "reference_withconfig_function_rule_casts_the_variable_at_the_function_sort",
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_function_rule_without_configuration_casts_the_variable_at_the_function_sort() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --type-inference-mode checked --output-definition ref-kompiled (exit 0)
    // parsed.txt: rule `foo(_)_TEST_Int_Int`(#SemanticCastToInt(I))=>`_+Int_`(#SemanticCastToInt(I),#token("1","Int")) requires `_>Int_`(#SemanticCastToInt(I),#token("0","Int")) ensures #token("true","Bool")
    // Control: the same function rule without `#withConfig` already agrees between the engines.
    let source = include_str!("fixtures/reference/inner/withconfig-fn-control/test.k");
    let loaded = load_with_prelude(source, "test.k", "TEST")
        .expect("the reference accepts the plain function rule");
    assert_eq!(
        rule_like_texts(&loaded, "test.k"),
        [
            "`foo(_)_TEST_Int_Int`(#SemanticCastToInt(I))=>`_+Int_`(#SemanticCastToInt(I),#token(\"1\",\"Int\")) requires `_>Int_`(#SemanticCastToInt(I),#token(\"0\",\"Int\"))"
        ]
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn function_rule_without_configuration_agrees_under_checked_inference() {
    assert_test_passes_under_checked_inference(
        "reference_function_rule_without_configuration_casts_the_variable_at_the_function_sort",
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_bare_variable_alias_body_is_cast_to_k() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --type-inference-mode checked --output-definition ref-kompiled (exit 0)
    // parsed.txt: context alias #SemanticCastToK(HERE) requires isFoo(#SemanticCastToK(HOLE)) [label(foo), ...]
    // Reduced from regression-new/context-alias-3 (test.k:7): the rule body is a bare variable,
    // which the reference grammar reaches through `#RuleBody ::= K` (kast.md:343).
    let source = include_str!("fixtures/reference/inner/alias-bare-variable/test.k");
    let loaded = load_with_prelude(source, "test.k", "TEST")
        .expect("the reference accepts a context alias whose body is a bare variable");
    assert_eq!(
        rule_like_texts(&loaded, "test.k"),
        ["#SemanticCastToK(HERE) requires isFoo(#SemanticCastToK(HOLE))"]
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn bare_variable_alias_body_agrees_under_checked_inference() {
    // The reference's Z3 encoder bounds HERE by K through the `#RuleBody ::= K` production
    // (TypeInferencer.java:644 `expectedSort = nt.sort()` for that node), and SimpleSub bounds
    // every variable by K on creation (InferenceDriver.java:49-53); one solution, cast to K.
    assert_test_passes_under_checked_inference("reference_bare_variable_alias_body_is_cast_to_k");
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_alias_variable_under_a_production_is_cast_at_the_argument_sort() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --type-inference-mode checked --output-definition ref-kompiled (exit 0)
    // parsed.txt: context alias `foo(_)_TEST_Foo_Int`(#SemanticCastToInt(HERE)) requires isFoo(#SemanticCastToK(HOLE)) [label(foo), ...]
    // Control: HERE under a real-sorted nonterminal already agrees between the engines.
    let source = include_str!("fixtures/reference/inner/alias-bare-variable-control/test.k");
    let loaded = load_with_prelude(source, "test.k", "TEST")
        .expect("the reference accepts the context alias");
    assert_eq!(
        rule_like_texts(&loaded, "test.k"),
        ["`foo(_)_TEST_Foo_Int`(#SemanticCastToInt(HERE)) requires isFoo(#SemanticCastToK(HOLE))"]
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn alias_variable_under_a_production_agrees_under_checked_inference() {
    assert_test_passes_under_checked_inference(
        "reference_alias_variable_under_a_production_is_cast_at_the_argument_sort",
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_exists_binder_variable_is_inferred_at_k() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --type-inference-mode checked --output-definition ref-kompiled (exit 0)
    // parsed.txt: rule `foo(_)_TEST_Exp_Int`(#SemanticCastToInt(_X))=>#Exists(#SemanticCastToK(Y),#Equals(#SemanticCastToK(?_I),#SemanticCastToK(Y))) requires #token("true","Bool") ensures #token("true","Bool")
    // Reduced from regression-new/checkWarns existsLHSBoundPass.k (rule at line 11), the one
    // ktest-fail step of that case whose verdict differs from the reference. parsed.txt omits
    // the inferred sort parameters of #Exists and #Equals; the casts to K fix them at {K,K},
    // which k-rust renders.
    let source = include_str!("fixtures/reference/inner/exists-binder/test.k");
    let loaded = load_with_prelude(source, "test.k", "TEST")
        .expect("the reference accepts the existential over a fresh variable");
    assert_eq!(
        rule_like_texts(&loaded, "test.k"),
        [
            "`foo(_)_TEST_Exp_Int`(#SemanticCastToInt(_X))=>#Exists{K,K}(#SemanticCastToK(Y),#Equals{K,K}(#SemanticCastToK(?_I),#SemanticCastToK(Y))) requires #token(\"true\",\"Bool\")"
        ]
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn exists_binder_variable_agrees_under_checked_inference() {
    // The reference's Z3 encoder declares every variable and sort parameter over the datatype
    // of real sorts (TypeInferencer.isRealSort: no parser sort except K, KItem and KLabel, plus
    // Nat and parametric sorts), so the bound variable Y and the sort parameters of #Exists and
    // #Equals never range over KList; one maximal model, at K.
    assert_test_passes_under_checked_inference("reference_exists_binder_variable_is_inferred_at_k");
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_rule_applies_a_named_field_projection() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --type-inference-mode checked --output-definition ref-kompiled (exit 0)
    // parsed.txt: rule `getFoo(_)_TEST_Int_Foo`(#SemanticCastToFoo(F))=>`project:test(_,_,_)_TEST_Foo_Int_Int_Int:foo`(#SemanticCastToFoo(F)) requires #token("true","Bool") ensures #token("true","Bool")
    // RuleGrammarGenerator.getCombinedGrammar adds GenerateSortProjections.gen(p) for every
    // production of the module: a named nonterminal `foo: Int` of `test(...)` yields the
    // function production `Int ::= "foo" "(" Foo ")"` with label project:<klabel>:foo, usable in
    // rules and (record-llvm 3.test/4.test) in programs.
    let source = include_str!("fixtures/reference/inner/record-projection/test.k");
    let loaded = load_with_prelude(source, "test.k", "TEST")
        .expect("the reference accepts a rule applying the generated field projection");
    assert_eq!(
        rule_like_texts(&loaded, "test.k"),
        [
            "`getFoo(_)_TEST_Int_Foo`(#SemanticCastToFoo(F))=>`project:test(_,_,_)_TEST_Foo_Int_Int_Int:foo`(#SemanticCastToFoo(F)) requires #token(\"true\",\"Bool\")"
        ]
    );
}

/// `load_with_prelude` with the module attributes `kcompile --backend llvm` excludes
/// (`symbolic`), the module set the conformance driver compiles ktest cases with.
#[cfg(feature = "z3-inference")]
fn load_with_prelude_for_llvm(
    source: &'static str,
    name: &str,
    main_module: &str,
) -> Result<k_rust::outer::LoadedDefinition, k_rust::outer::LoadError> {
    let prelude = k_rust::builtin::embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        k_rust::builtin::embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
        ResolvedSource::new(name, source),
        main_module,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec!["symbolic".into()],
            ..LoadOptions::default()
        },
    )
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_top_rewrite_over_a_bare_variable_keeps_its_parameter_at_k() {
    // reference: k/result/bin/kompile checkStrictBOOLInclusion.k --backend llvm --syntax-module CHECKSTRICTBOOLINCLUSION-SYNTAX --type-inference-mode checked (regression-new/checks, ktest-fail recipe, exit 0: the reference accepts)
    // regression-new/checks checkStrictBOOLInclusion.k, verbatim: `rule mytrue myand B2 => B2`
    // under the llvm module set. Both engines instantiate the top #KRewrite at K, the sort the
    // portable engine assigns; k-rust renders the parameter.
    let source = include_str!("fixtures/reference/inner/strict-bool-inclusion/test.k");
    let loaded = load_with_prelude_for_llvm(source, "test.k", "CHECKSTRICTBOOLINCLUSION")
        .expect("the reference accepts the strictness definition");
    let bodies = rule_like_texts(&loaded, "test.k");
    assert_eq!(bodies.len(), 2, "{bodies:?}");
    assert!(
        bodies[0].starts_with("`_myand__CHECKSTRICTBOOLINCLUSION-SYNTAX_BExp_BExp_BExp`("),
        "{bodies:?}"
    );
    assert!(
        bodies[0].contains("=>#SemanticCastToBExp(B2)") && !bodies[0].contains("{KItem}"),
        "{bodies:?}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn top_rewrite_over_a_bare_variable_agrees_under_checked_inference() {
    // Host ratchet run 20: with the Z3 domain restricted to real sorts (3769711) the seed model
    // still prefers K for the #KRewrite parameter, but the maximality climb over the real
    // variables re-reads every constant from an unconstrained model and the parameter came back
    // as KItem, which checked mode reported against the portable engine's K. The parameter
    // preference of the seed must survive the climb.
    assert_test_passes_under_checked_inference(
        "reference_top_rewrite_over_a_bare_variable_keeps_its_parameter_at_k",
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_anywhere_rule_over_a_nullary_constructor_is_instantiated_at_its_sort() {
    // reference: k/result/bin/kompile test.k --backend llvm --main-module TEST --syntax-module TEST --type-inference-mode checked --allow-anywhere-haskell -w none --output-definition ref-kompiled (regression-new/issue-2909-allow-anywhere-haskell/llvm, verbatim, exit 0)
    // parsed.txt: rule `foo()_TEST_Foo`(.KList)=>`bar()_TEST_Foo`(.KList) requires #token("true","Bool") ensures #token("true","Bool") [anywhere, ..., priority(20)]
    //             rule `foo()_TEST_Foo`(.KList)=>`baz()_TEST_Foo`(.KList) requires #token("true","Bool") ensures #token("true","Bool")
    // For an anywhere rule `isFunction(t, isAnywhere)` (TypeInferencer.java:413-421) holds
    // regardless of the left-hand side's production, so at :640 the `#RuleContent` node bounds
    // its rewrite child by `getFunctionSort` (:429), the sort of `foo()`: the rewrite is
    // instantiated at Foo, as the portable engine's anywhere bound already does.
    let source = include_str!("fixtures/reference/inner/anywhere-nullary/test.k");
    let loaded = load_with_prelude_for_llvm(source, "test.k", "TEST")
        .expect("the reference accepts the anywhere rule over a nullary constructor");
    assert_eq!(
        rule_like_texts(&loaded, "test.k"),
        [
            "`foo()_TEST_Foo`(.KList)=>`bar()_TEST_Foo`(.KList) requires #token(\"true\",\"Bool\")",
            "`foo()_TEST_Foo`(.KList)=>`baz()_TEST_Foo`(.KList) requires #token(\"true\",\"Bool\")",
        ]
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn anywhere_rule_over_a_nullary_constructor_agrees_under_checked_inference() {
    // Host ratchet runs 16 to 26 (issue-2909-allow-anywhere-haskell/llvm, kompile step): the Z3
    // engine bounded only the rewrite's right-hand side by the anywhere left-hand side and left
    // the #KRewrite parameter at the seed's K, while the portable engine and the reference bound
    // the rewrite itself by the left-hand side's sort (Foo).
    assert_test_passes_under_checked_inference(
        "reference_anywhere_rule_over_a_nullary_constructor_is_instantiated_at_its_sort",
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_anywhere_rule_over_a_token_is_instantiated_at_the_token_sort() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --type-inference-mode checked --allow-anywhere-haskell -w none --output-definition ref-kompiled (regression-new/issue-2909-allow-anywhere-haskell/check, verbatim, exit 0; with -w2e -w all the same kompile exits 113 at the later `Removed anywhere rule for Haskell backend execution` check, after parsing)
    // parsed.txt: rule #token("1","Int")=>#token("2","Int") requires #token("true","Bool") ensures #token("true","Bool") [anywhere, ...]
    // `getFunction` (TypeInferencer.java:380-404) returns the token `1` itself: a `Constant` is a
    // `ProductionReference`, so the rewrite of an anywhere rule is bounded by the token's sort.
    let source = include_str!("fixtures/reference/inner/anywhere-token/test.k");
    let loaded = load_with_prelude(source, "test.k", "TEST")
        .expect("the reference parses the anywhere rule over a token");
    assert_eq!(
        rule_like_texts(&loaded, "test.k"),
        ["#token(\"1\",\"Int\")=>#token(\"2\",\"Int\") requires #token(\"true\",\"Bool\")"]
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn anywhere_rule_over_a_token_agrees_under_checked_inference() {
    assert_test_passes_under_checked_inference(
        "reference_anywhere_rule_over_a_token_is_instantiated_at_the_token_sort",
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_nullary_function_with_a_parametric_instance_result_sort_parses_bare() {
    // reference: k/result/bin/kompile test.k --backend llvm --main-module TEST --syntax-module TEST (regression-new/mint-llvm-2, exit 0)
    // parsed.txt: rule `m64()_TEST_MInt`(.KList)=>#token("0p64","MInt{64}") requires #token("true","Bool") ensures #token("true","Bool")
    //             rule `m32()_TEST_MInt`(.KList)=>#token("0p32","MInt{32}") requires #token("true","Bool") ensures #token("true","Bool")
    // `syntax MInt{64} ::= m64() [function]` has no sort parameters, so TypeInferenceVisitor:278
    // (`pr.production().params().nonEmpty() && hasParametricSort(...)`) adds no cast around it
    // and CheckFunctions sees the function at the top of the LHS.
    let source = include_str!("fixtures/reference/inner/mint-fn/test.k");
    let loaded = load_with_prelude(source, "test.k", "TEST")
        .expect("the reference accepts a nullary function returning a declared MInt instance");
    assert_eq!(
        rule_like_texts(&loaded, "test.k"),
        [
            "`m64()_TEST_MInt`(.KList)=>#token(\"0p64\",\"MInt{64}\") requires #token(\"true\",\"Bool\")",
            "`m32()_TEST_MInt`(.KList)=>#token(\"0p32\",\"MInt{32}\") requires #token(\"true\",\"Bool\")",
        ]
    );
    let diagnostics = k_rust::definition::check_definition(&loaded.resolved)
        .expect("definition checks run on the loaded definition");
    assert!(
        diagnostics.iter().all(|diagnostic| diagnostic.code
            != k_rust::diagnostic::DiagnosticCode::IllegalFunctionOnLhs),
        "{diagnostics:?}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn nullary_function_with_a_parametric_instance_result_sort_agrees_under_checked_inference() {
    assert_test_passes_under_checked_inference(
        "reference_nullary_function_with_a_parametric_instance_result_sort_parses_bare",
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_parametric_result_in_a_placeholder_slot_infers_the_declared_width() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --output-definition ref-kompiled (exit 0)
    // parsed.txt: rule `testBytesGet_TEST_Bool`(.KList)=>`_andBool_`(#SemanticCastToBool(`_==MInt__MINT_Bool_MInt_MInt`{64}(`project:MInt{64}`(`#SemanticCastToMInt{64}`(`_[_]_BYTES-HOOKED_MInt_Bytes_MInt`(`bytesString2_TEST_Bytes`(.KList),#token("2p64","MInt{64}")))),`#SemanticCastToMInt{64}`(`Int2MInt(_)_MINT_MInt_Int`{64}(`_[_]_BYTES-HOOKED_Int_Bytes_Int`(`bytesString2_TEST_Bytes`(.KList),#token("2","Int")))))),#SemanticCastToBool(`_==MInt__MINT_Bool_MInt_MInt`{256}(`project:MInt{256}`(`#SemanticCastToMInt{256}`(`_[_]_BYTES-HOOKED_MInt_Bytes_MInt`(`bytesString2_TEST_Bytes`(.KList),#token("2p256","MInt{256}")))),`#SemanticCastToMInt{256}`(`Int2MInt(_)_MINT_MInt_Int`{256}(`_[_]_BYTES-HOOKED_Int_Bytes_Int`(`bytesString2_TEST_Bytes`(.KList),#token("2","Int"))))))) requires #token("true","Bool") ensures #token("true","Bool")
    //             rule `testBytesGetBare_TEST_Bool`(.KList)=>#SemanticCastToBool(`_==MInt__MINT_Bool_MInt_MInt`(`#SemanticCastToMInt{64}`(`_[_]_BYTES-HOOKED_MInt_Bytes_MInt`(`bytesString2_TEST_Bytes`(.KList),#token("2p64","MInt{64}"))),#token("0p64","MInt{64}"))) requires #token("true","Bool") ensures #token("true","Bool")
    // The rule grammar instantiates `{Width} Bool ::= MInt{Width} "==MInt" MInt{Width}` with the
    // placeholder `MInt{K}` and bridges it with `MInt{K} ::= MInt{64}` (RuleGrammarGenerator
    // :629-637), but that bridge is added to the parsing module only, after disambProds is
    // captured (:627): the TypeInferencer's `<=Sort` relation has no `MInt{64} <= MInt{K}` pair,
    // so the widths of `bytesString2[2p64]` and `Int2MInt(...)` are forced to the declared
    // instance the token or cast anchors, never to `K`. k-rust's printer also renders the
    // inferred label parameters (`{64}`, `{256}`) the reference's parsed.txt omits; the KORE
    // emission of mint-llvm-4 instantiates the symbols' `{SortWidth}` from them.
    let source = include_str!("fixtures/reference/inner/mint-bridge/test.k");
    let loaded = load_with_prelude(source, "test.k", "TEST")
        .expect("the reference accepts a parametric result in the MInt{K} slot of ==MInt");
    let bodies = rule_like_texts(&loaded, "test.k")
        .into_iter()
        .filter(|body| body.starts_with("`testBytesGet"))
        .collect::<Vec<_>>();
    assert_eq!(
        bodies,
        [
            "`testBytesGet_TEST_Bool`(.KList)=>`_andBool_`(#SemanticCastToBool(`_==MInt__MINT_Bool_MInt_MInt`{64}(`project:MInt{64}`(`#SemanticCastToMInt{64}`(`_[_]_BYTES-HOOKED_MInt_Bytes_MInt`{64}(`bytesString2_TEST_Bytes`(.KList),#token(\"2p64\",\"MInt{64}\")))),`#SemanticCastToMInt{64}`(`Int2MInt(_)_MINT_MInt_Int`{64}(`_[_]_BYTES-HOOKED_Int_Bytes_Int`(`bytesString2_TEST_Bytes`(.KList),#token(\"2\",\"Int\")))))),#SemanticCastToBool(`_==MInt__MINT_Bool_MInt_MInt`{256}(`project:MInt{256}`(`#SemanticCastToMInt{256}`(`_[_]_BYTES-HOOKED_MInt_Bytes_MInt`{256}(`bytesString2_TEST_Bytes`(.KList),#token(\"2p256\",\"MInt{256}\")))),`#SemanticCastToMInt{256}`(`Int2MInt(_)_MINT_MInt_Int`{256}(`_[_]_BYTES-HOOKED_Int_Bytes_Int`(`bytesString2_TEST_Bytes`(.KList),#token(\"2\",\"Int\"))))))) requires #token(\"true\",\"Bool\")",
            "`testBytesGetBare_TEST_Bool`(.KList)=>#SemanticCastToBool(`_==MInt__MINT_Bool_MInt_MInt`{64}(`#SemanticCastToMInt{64}`(`_[_]_BYTES-HOOKED_MInt_Bytes_MInt`{64}(`bytesString2_TEST_Bytes`(.KList),#token(\"2p64\",\"MInt{64}\"))),#token(\"0p64\",\"MInt{64}\"))) requires #token(\"true\",\"Bool\")",
        ]
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn parametric_result_in_a_placeholder_slot_agrees_under_checked_inference() {
    assert_test_passes_under_checked_inference(
        "reference_parametric_result_in_a_placeholder_slot_infers_the_declared_width",
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn claims_parse_the_implicit_generated_counter_as_a_sibling_cell() {
    for explicit_counter in [false, true] {
        let counter = if explicit_counter {
            "<generatedCounter> GC => GC +Int 1 </generatedCounter>"
        } else {
            ""
        };
        let source = format!(
            r#"module TEST
              imports INT
              syntax Pgm ::= "quux"
              configuration <k> quux </k> <c1> .K </c1> <c2> .K </c2>
              claim <k> quux => .K </k>
                    <c1> .K => ?C </c1>
                    <c2> .K => ?C </c2>
                    {counter}
            endmodule"#
        );
        let loaded = load_with_prelude(&source, "counter-claim.k", "TEST")
            .expect("implicit rule-cell syntax must be available to proof claims");
        let body = loaded
            .definition
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|s| {
                if let Sentence::Claim { body, .. } = s {
                    Some(body)
                } else {
                    None
                }
            })
            .unwrap();
        let mut leaves = Vec::new();
        cell_leaves(body, &mut leaves);
        let mut expected = vec!["<k>", "<c1>", "<c2>"];
        if explicit_counter {
            expected.push("<generatedCounter>");
        }
        assert_eq!(leaves, expected);
        let mut shared = Vec::new();
        let mut rewrites = 0;
        body.visit_preorder(&mut |term| {
            if let Term::Variable { name, sort } = term
                && name == "?C"
            {
                shared.push(sort.clone());
            }
            if matches!(term, Term::Rewrite { .. }) {
                rewrites += 1;
            }
        });
        assert_eq!(shared, vec![None, None]);
        assert_eq!(rewrites, expected.len());
        assert!(!loaded.definition.main_module().unwrap().local_sentences.iter().any(|s| {
            matches!(s, Sentence::Production { sort, .. } if sort.name == "GeneratedCounterCell")
        }), "the implicit counter production is parse-only");
        let nested = source.replace("<c1> .K => ?C </c1>", "<c1> .K => ?C => ?D </c1>");
        assert!(
            matches!(
                load_with_prelude(&nested, "nested-counter-claim.k", "TEST"),
                Err(k_rust::outer::LoadError::RuleParsing(RuleError::Parse(error)))
                    if matches!(error.error, ParseError::Associativity { ref parent, ref child, .. }
                        if parent == "#KRewrite" && child == "#KRewrite")
            ),
            "genuinely nested rewrites remain rejected"
        );
    }
}
