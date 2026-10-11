// The embedded standard prelude loads in the portable build to the same definition as in the
// z3-inference build (inner_rules::the_standard_prelude_loads_to_the_same_definition_in_both_builds).
// Fixtures gated on `z3-inference` below are gated for their own rules or pinned results, not for
// the prelude: parametric sort inference, an ambiguous forest outside the portable decision, or
// an assertion not yet checked against the portable build.

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
    production: Option<String>,
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
            .map(|production| production.to_hex()),
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
        ensures: ensures.map(|term| term.to_string()),
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

/// The `X` occurrences of the body of `rule`, as variables and as `Id` tokens.
fn x_variables_and_id_tokens(rule: &Sentence) -> (usize, usize) {
    let Sentence::Rule { body, .. } = rule else {
        panic!("expected a rule, got {rule:?}")
    };
    let (mut variables, mut tokens) = (0, 0);
    body.visit_preorder(&mut |term| match term.unannotated() {
        Term::Variable { name, .. } if name == "X" => variables += 1,
        Term::Token { token, sort } if token == "X" && sort == &Sort::new("Id") => tokens += 1,
        _ => {}
    });
    (variables, tokens)
}

/// A rule is parsed with the scanner of its own module: a token that only a sibling module
/// declares does not lex the rule's variables, though the main module sees both modules.
#[test]
fn standalone_rule_content_uses_its_own_modules_scanner() {
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

    let rule = parse_rule_content(&resolved, "RULES", "X => X", Attributes::default())
        .expect("RULES does not see TOKEN's Id lexeme");
    assert_eq!(x_variables_and_id_tokens(&rule), (2, 0));
    // MAIN sees the prec(3) Id lexeme, which outranks the variable lexeme.
    let rule = parse_rule_content(&resolved, "MAIN", "X => X", Attributes::default())
        .expect("MAIN parses X as an Id token");
    assert_eq!(x_variables_and_id_tokens(&rule), (0, 2));
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
            .filter_map(|sentence| sentence_summary(&**sentence))
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
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    let mut metadata = Vec::new();
    metadata_summary(body, source, loaded.source_table(), &mut metadata);

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
            .any(|sentence| matches!(&**sentence, Sentence::Rule { .. }))
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
            .find_map(|sentence| match &**sentence {
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

#[test]
fn rule_casts_through_a_synonym_chain_use_the_end_of_the_chain() {
    for (cast, accepted) in [
        ("Rat", true),
        ("Other", false),
        ("Ray", true),
        ("Wad", true),
    ] {
        let source = format!(
            r#"
            module MAIN
              syntax Rat ::= r"[0-9]+" [token]
              syntax Ray = Rat
              syntax Wad = Ray
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
                "{cast}: {result:?}"
            );
            continue;
        }
        let resolved = result.unwrap_or_else(|error| panic!("{cast}: {error}"));
        let body = resolved
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match &**sentence {
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

    let source = indoc! {r#"
        module MAIN
          syntax Rat ::= r"[0-9]+" [token]
          syntax Ray = Rat
          syntax Wad = Ray
          syntax Wad ::= "h(" K ")" [symbol(h), function]
          rule h(X) => {X}:>Wad
        endmodule
    "#};
    let definition = k_rust::definition::apply_sort_synonyms(&lowered(source)).unwrap();
    let projection_result = resolve_rule_bubbles(&definition);

    let resolved = projection_result.unwrap();
    let body = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    assert!(body.to_string().contains("project:Rat"), "{body}");
}

#[test]
fn a_cast_through_a_privately_imported_synonym_uses_its_denotation() {
    for (cast, accepted) in [("B", false), ("A", true)] {
        let source = format!(
            r#"
            module M0
              syntax Rat ::= r"[0-9]+" [token]
              syntax B = Rat
            endmodule
            module M1
              imports private M0
              syntax A = B
            endmodule
            module MAIN
              imports M1
              syntax Foo ::= "f(" A ")" [symbol(f)] | "g(" A ")" [symbol(g)]
              rule f(X:{cast}) => g(X)
            endmodule
            "#
        );
        let definition = k_rust::definition::apply_sort_synonyms(&lowered(&source)).unwrap();
        let result = resolve_rule_bubbles(&definition);
        if !accepted {
            assert!(
                result.is_err(),
                "the private alias {cast} parsed: {result:?}"
            );
            continue;
        }
        let resolved = result.unwrap_or_else(|error| panic!("{cast}: {error}"));
        let body = resolved
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match &**sentence {
                Sentence::Rule { body, .. } => Some(body),
                _ => None,
            })
            .unwrap();
        assert!(body.to_string().contains("#SemanticCastToRat"), "{body}");
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
    let Sentence::Rule { body, requires, .. } = &**resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find(|sentence| matches!(&***sentence, Sentence::Rule { .. }))
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
        .find_map(|sentence| match &**sentence {
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

    // Each side reads `test(foo)` as `testFoo` or `testFoos`, independently of the other.
    let RuleError::Parse(ref parse) = error else {
        panic!("{error:?}")
    };
    let ParseError::Ambiguous { ref places, .. } = parse.error else {
        panic!("{error:?}")
    };
    assert_eq!(
        places
            .iter()
            .map(|place| place.alternatives.len())
            .collect::<Vec<_>>(),
        [2, 2],
        "{error:?}"
    );
    // Each subterm is located in the source, since both print the same readings.
    assert_eq!(
        places
            .iter()
            .map(|place| place
                .location
                .map(|location| (location.start_line, location.start_column)))
            .collect::<Vec<_>>(),
        [Some((7, 8)), Some((7, 21))],
        "{error:?}"
    );
    let message = error.to_string();
    assert!(
        message.contains("\nSubterm 1 at 7:8:\n") && message.contains("\nSubterm 2 at 7:21:\n"),
        "{message}"
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
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .expect("the reduced Cgascap rule should resolve");

    assert!(body.contains("capInt"), "{body}");
    assert!(!body.contains("capGas"), "{body}");
    assert!(body.contains("=>ite("), "{body}");
}

/// The two well-sorted readings, `capGas … => ite{Gas}(…)` and `capInt … => ite{Int}(…)`, give
/// every variable the same sort, so they are one maximal typing and differ only in the overload
/// and in the instantiation of `ite`'s parameter. The typing does not choose between them and
/// they lower to different terms, so the portable build leaves the rule to Z3 instead of
/// reporting an ambiguity; the z3 build takes the `Int` reading.
#[test]
fn one_maximal_typing_split_by_overload_and_parameter_is_left_to_z3() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Gas ::= Int
          syntax Gas ::= cap(Gas, Gas, Int, Int) [symbol(capGas), overload(cap), function, total]
          syntax Int ::= cap(Int, Int, Int, Int) [symbol(capInt), overload(cap), function, total]
          syntax {S} S ::= "ite" "(" Int "," S "," S ")" [symbol(ite), function, total]

          rule cap(GCAP:Int, GAVAIL:Int, GEXTRA, IGNORED) => ite(GEXTRA, GCAP, GAVAIL)
        endmodule
    "#};
    let resolved = resolve_rule_bubbles(&lowered(source));

    #[cfg(not(feature = "z3-inference"))]
    {
        let error = resolved.expect_err("the portable build does not choose within one typing");
        let RuleError::Parse(error) = error else {
            panic!("expected a parse error, got {error:?}")
        };
        assert_eq!(
            error.error,
            ParseError::Z3InferenceRequired {
                ambiguity: true,
                parametric_sorts: false,
            }
        );
    }
    #[cfg(feature = "z3-inference")]
    {
        let resolved = resolved.expect("the z3 build decides the rule");
        let body = resolved
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match &**sentence {
                Sentence::Rule { body, .. } => Some(body.to_string()),
                _ => None,
            })
            .expect("the rule should be resolved");
        assert!(body.contains("capInt"), "{body}");
        assert!(!body.contains("capGas"), "{body}");
        assert!(body.contains("=>ite("), "{body}");
    }
}

/// The body of the one rule `resolve_rule_bubbles` resolved in `definition`'s main module.
fn only_rule_body(definition: &k_rust::definition::Definition) -> String {
    definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .expect("the rule should be resolved")
}

/// A module whose user syntax reuses `=>` as an ordinary production (a match arm), with one
/// rule over it.
fn arrow_module(rule: &str) -> String {
    format!(
        r#"module MAIN
  syntax A ::= "a" [symbol(a)]
             | A "*" A [left, symbol(times)]
             > A "+" A [left, symbol(plus)]
  syntax KItem ::= A "=>" A [symbol(arrow)]
  syntax KItem ::= f(KItem) [symbol(f)]
  rule {rule}
endmodule
"#
    )
}

/// With user syntax that reuses `=>`, a rule body has a reading through it beside the rewrite
/// its `=>` spells. Among the readings of the whole body that denote a term, the one rooted at
/// the rule's own rewrite is the body. The choice is made on the readings of the whole body, per
/// tree, so it does not depend on an invalid reading packed beside a valid one: `a => a`, which
/// has none (no reading puts a rewrite below `+`), reads as the rewrite like `a => a + a`.
#[test]
fn a_rule_body_whose_arrow_user_syntax_reuses_reads_as_the_rewrite() {
    for (rule, expected) in [
        ("a => a", "a(.KList)=>a(.KList)"),
        ("a => a + a", "a(.KList)=>plus(a(.KList),a(.KList))"),
        ("a + a => a", "plus(a(.KList),a(.KList))=>a(.KList)"),
        ("a => a * a", "a(.KList)=>times(a(.KList),a(.KList))"),
    ] {
        let definition = resolve_rule_bubbles(&lowered(&arrow_module(rule)))
            .unwrap_or_else(|error| panic!("{rule}: {error}"));
        assert_eq!(only_rule_body(&definition), expected, "{rule}");
    }
}

/// The rule's own rewrite is preferred wherever it stands, not only at the body's root: in an
/// argument, the text `a => a` has a rewrite reading and an `arrow` reading at the same place, and
/// the rewrite is what the rule means there, whether or not an invalid reading (`(a => a) + a`, a
/// rewrite below `+`) exists beside them, and however deep the argument is.
#[test]
fn a_rewrite_below_the_body_root_wins_over_user_syntax_reusing_its_token() {
    for (rule, expected) in [
        ("f(a => a)", "f(a(.KList)=>a(.KList))"),
        ("f(a => a + a)", "f(a(.KList)=>plus(a(.KList),a(.KList)))"),
        (
            "f(f(a + a => a))",
            "f(f(plus(a(.KList),a(.KList))=>a(.KList)))",
        ),
    ] {
        let definition = resolve_rule_bubbles(&lowered(&arrow_module(rule)))
            .unwrap_or_else(|error| panic!("{rule}: {error}"));
        assert_eq!(only_rule_body(&definition), expected, "{rule}");
    }
}

/// In a cell, as in an argument, the rule's rewrite is preferred over user syntax that reuses
/// its token: `<k> a => a ... </k>` rewrites the cell's first item.
#[test]
fn a_rewrite_in_a_cell_wins_over_user_syntax_reusing_its_token() {
    for (rule, expected) in [
        ("<k> a => a ... </k>", "a(.KList)=>a(.KList)"),
        (
            "<k> a => a + a ... </k>",
            "a(.KList)=>plus(a(.KList),a(.KList))",
        ),
    ] {
        let source = format!(
            r#"module MAIN
  syntax A ::= "a" [symbol(a)]
             | A "+" A [left, symbol(plus)]
  syntax KItem ::= A "=>" A [symbol(arrow)]
  configuration <k> a </k>
  rule {rule}
  syntax K
endmodule
"#
        );
        let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
        let loaded = load(
            ResolvedSource::new("cells.k", &source),
            "MAIN",
            &mut resolver,
        )
        .unwrap_or_else(|error| panic!("{rule}: {error:?}"));
        let bodies = loaded
            .definition()
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .filter_map(|sentence| match &**sentence {
                Sentence::Rule { body, .. } => Some(body.to_string()),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(
            bodies
                .iter()
                .any(|body| body.contains("<k>") && body.contains(expected)),
            "{rule}: {bodies:?}"
        );
    }
}

/// A module whose user syntax reuses `=>` and `~>` (`arrow`, `seqish`), with wrappers that put a
/// `K` (`j`) or a `KItem` (`h`) inside an `A`, and one rule over it.
fn arrow_sequence_module(rule: &str) -> String {
    format!(
        r#"module MAIN
  syntax A ::= "a" [symbol(a)]
             | j(K) [symbol(j)]
             | h(KItem) [symbol(h)]
             | A "+" A [left, symbol(plus)]
  syntax KItem ::= A "=>" A [symbol(arrow)]
  syntax KItem ::= A "~>" A [symbol(seqish)]
  syntax KItem ::= f(KItem) [symbol(f)]
  rule {rule}
endmodule
"#
    )
}

/// The choice is made at each position among the readings that agree above it. In
/// `f(j(a ~> a) => a)` the argument of `f` is the rule's rewrite or `arrow`, and the rewrite is
/// chosen there; the argument of `j` is then the rule's sequence or `seqish`, and the sequence is
/// chosen. The `j` below the `arrow` reading is another position, which that reading's removal
/// leaves without a choice to make. The reading `(a ~> a) + a` puts the sequence below `+` and is
/// gone before the choice, so `j(a ~> a + a)` reads like `j(a ~> a)`.
#[test]
fn a_choice_is_made_at_each_position_of_the_readings_kept_above_it() {
    for (rule, expected) in [
        ("f(j(a ~> a) => a)", "f(j(a(.KList)~>a(.KList))=>a(.KList))"),
        (
            "f(j(a ~> a + a) => a)",
            "f(j(a(.KList)~>plus(a(.KList),a(.KList)))=>a(.KList))",
        ),
        ("f(a => j(a ~> a))", "f(a(.KList)=>j(a(.KList)~>a(.KList)))"),
    ] {
        let definition = resolve_rule_bubbles(&lowered(&arrow_sequence_module(rule)))
            .unwrap_or_else(|error| panic!("{rule}: {error}"));
        assert_eq!(only_rule_body(&definition), expected, "{rule}");
    }
}

/// A sequence has sort `K`, so it cannot be the argument of `h(KItem)`: there the rule's
/// sequence is not a reading that means anything, the choice does not prefer it, and the user's
/// `seqish` is the argument, as it would be with no preference at all.
#[test]
fn a_construct_whose_sort_cannot_stand_at_a_place_is_not_preferred_there() {
    for (rule, expected) in [
        (
            "h(a ~> a) => a",
            "h(seqish(a(.KList),a(.KList)))=>a(.KList)",
        ),
        (
            "f(h(a ~> a) => a)",
            "f(h(seqish(a(.KList),a(.KList)))=>a(.KList))",
        ),
    ] {
        let definition = resolve_rule_bubbles(&lowered(&arrow_sequence_module(rule)))
            .unwrap_or_else(|error| panic!("{rule}: {error}"));
        assert_eq!(only_rule_body(&definition), expected, "{rule}");
    }
}

/// Readings that differ above a position are not compared at it. With `A "~>" A` and
/// `A "=>" A` both reused, `a => a ~> a => a` has two readings rooted at the rule's rewrite,
/// `(arrow(a, a) ~> a) => a` and `a => (a ~> arrow(a, a))`: they split the text at different
/// `=>`, so every position below the root belongs to one of them only, and both remain an
/// ambiguity. `a => a ~> a` has one split, so its readings agree at the root and differ only at
/// the rewrite's right side, where the sequence is chosen over `seqish(a, a)`.
#[test]
fn readings_that_differ_above_a_position_are_not_compared_at_it() {
    let source = |rule: &str| {
        format!(
            r#"module MAIN
  syntax A ::= "a" [symbol(a)]
  syntax KItem ::= A "=>" A [symbol(arrow)]
  syntax KItem ::= A "~>" A [symbol(seqish)]
  rule {rule}
endmodule
"#
        )
    };
    let definition = resolve_rule_bubbles(&lowered(&source("a => a ~> a"))).unwrap();
    assert_eq!(
        only_rule_body(&definition),
        "a(.KList)=>a(.KList)~>a(.KList)"
    );
    let rule = "a => a ~> a => a";
    let error =
        resolve_rule_bubbles(&lowered(&source(rule))).expect_err("two readings differ at the root");
    let RuleError::Parse(ref parse) = error else {
        panic!("{rule}: {error:?}")
    };
    assert!(
        matches!(parse.error, ParseError::Ambiguous { .. }),
        "{rule}: {error:?}"
    );
}

/// A rewrite's sort is a parameter that inference chooses, at most the sort of the place it
/// stands at, so the rewrite is preferred at a place of any sort (`h(Foo)`, with the user's
/// `Foo ::= Bar "=>" Bar`), and its sides stand at that place: as the argument of `g(K)` the
/// rule's sequence is its right side, as the argument of `f(KItem)` a sequence cannot be, and
/// the user's `seqish` is.
#[test]
fn a_rewrite_is_preferred_at_a_place_of_any_sort_and_its_sides_stand_there() {
    let source = |rule: &str| {
        format!(
            r#"module MAIN
  syntax A ::= "a" [symbol(a)]
  syntax KItem ::= A "~>" A [symbol(seqish)]
  syntax KItem ::= f(KItem) [symbol(f)] | g(K) [symbol(g)]
  syntax Bar ::= "bar" [symbol(bar)]
  syntax Foo ::= Bar
  syntax Foo ::= Bar "=>" Bar [symbol(arrowfoo)]
  syntax KItem ::= h(Foo) [symbol(h)]
  rule {rule}
endmodule
"#
        )
    };
    for (rule, expected) in [
        ("h(bar => bar)", "h(bar(.KList)=>bar(.KList))"),
        ("g(a => a ~> a)", "g(a(.KList)=>a(.KList)~>a(.KList))"),
        (
            "f(a => a ~> a)",
            "f(a(.KList)=>seqish(a(.KList),a(.KList)))",
        ),
    ] {
        let definition = resolve_rule_bubbles(&lowered(&source(rule)))
            .unwrap_or_else(|error| panic!("{rule}: {error}"));
        assert_eq!(only_rule_body(&definition), expected, "{rule}");
    }
}

/// A rewrite's sort is at least each of its sides' sorts, so where a side's sort cannot stand
/// at a place the rewrite cannot either, and the choice does not prefer it there: in a match
/// arm `syntax Arm ::= Pat "=>" Exp`, the `=>` of `match(V, p => e)` cannot be the rule's
/// rewrite of an `Arm` (a `Pat` and an `Exp` are no `Arm`), so it is the arm, whatever other
/// sorts the module declares; so with a token (`1`, a `Num`) or a sort written on a variable
/// (`P:Pat`) on a side.
#[test]
fn a_rewrite_whose_sides_cannot_stand_at_a_place_is_not_preferred_there() {
    let source = |rule: &str| {
        format!(
            r#"module MAIN
  syntax Num ::= r"[0-9]+" [token]
  syntax Pat ::= "p" [symbol(p)] | Num
  syntax Exp ::= "e" [symbol(e)] | Num
  syntax Arm ::= Pat "=>" Exp [symbol(arm)]
  syntax Exp ::= match(Exp, Arm) [symbol(match)]
  rule {rule}
endmodule
"#
        )
    };
    for (rule, expected) in [
        (
            "match(V, p => e) => e",
            "match(#SemanticCastToExp(V),arm(p(.KList),e(.KList)))=>e(.KList)",
        ),
        (
            "match(V, 1 => B) => B",
            r#"match(#SemanticCastToExp(V),arm(#token("1","Num"),#SemanticCastToExp(B)))=>#SemanticCastToExp(B)"#,
        ),
        (
            "match(V, P:Pat => B) => B",
            "match(#SemanticCastToExp(V),arm(#SemanticCastToPat(P),#SemanticCastToExp(B)))=>#SemanticCastToExp(B)",
        ),
    ] {
        let definition = resolve_rule_bubbles(&lowered(&source(rule)))
            .unwrap_or_else(|error| panic!("{rule}: {error}"));
        assert_eq!(only_rule_body(&definition), expected, "{rule}");
    }
}

/// Each reading of a body is judged by itself. With user syntax that reuses `=>` twice
/// (`A "=>" A "=>" A`), `a => (b => a) + a => a` has readings rooted at either of the rule's
/// unparenthesized `=>`, and each puts one rewrite directly below the other, which the rewrite's
/// associativity forbids, so neither denotes a term. The reading through the user's syntax,
/// `two(a, (b => a) + a, a)`, puts its one rewrite under parentheses, where a rewrite may stand:
/// it is the only term the text denotes, so it is the body, with no error to report.
#[test]
fn a_body_whose_rewrite_readings_all_break_a_relation_reads_through_user_syntax() {
    let source = r#"module MAIN
  syntax A ::= "a" [symbol(a)]
             | "b" [symbol(b)]
             | A "*" A [left, symbol(times)]
             > A "+" A [left, symbol(plus)]
  syntax S ::= A "=>" A "=>" A [symbol(two)]
  rule a => (b => a) + a => a
endmodule
"#;
    let definition = resolve_rule_bubbles(&lowered(source)).unwrap();
    assert_eq!(
        only_rule_body(&definition),
        "two(a(.KList),plus(b(.KList)=>a(.KList),a(.KList)),a(.KList))"
    );
}

/// The error of a rule body none of whose readings denotes a term, in a module of plain operators
/// that reuse no structural token.
fn plain_rule_error(rule: &str) -> ParseError {
    let source = format!(
        r#"module MAIN
  syntax A ::= "a" [symbol(a)]
             | A "*" A [left, symbol(times)]
             > A "+" A [left, symbol(plus)]
  syntax KItem ::= g(K, K) [symbol(g)]
  rule {rule}
endmodule
"#
    );
    match resolve_rule_bubbles(&lowered(&source)) {
        Err(RuleError::Parse(error)) => error.error,
        other => panic!("{rule}: expected a parse error, got {other:?}"),
    }
}

/// When no reading of a body denotes a term and some derivation puts a rewrite where it has no
/// meaning, the misplaced rewrite is reported: `a => a ~> a => a` meant `(a => a) ~> (a => a)`,
/// and parentheses are the fix. Every derivation that keeps both rewrites out of the sequence
/// makes one the right child of the other, but that violation only follows from moving a rewrite
/// out of the place the user wrote it.
///
/// The portable build's rule grammar derives a rewrite's sides from the rewritten sort, so a
/// rewrite is never a side there: the `#let` body, each of whose readings needs one rewrite as a
/// side of another or inside the `#let`, has no derivation, and the text is reported where it
/// ends.
#[test]
fn a_body_with_no_reading_reports_a_misplaced_rewrite_before_another_violation() {
    for (rule, parent) in [
        ("a => a => a ~> a", "#KSequence"),
        ("a => a ~> a => a", "#KSequence"),
        ("a ~> a => a => a", "#KSequence"),
        ("a => #let a = a #in a => a", "#let"),
    ] {
        #[cfg(not(feature = "z3-inference"))]
        if parent == "#let" {
            let error = plain_rule_error(rule);
            assert!(
                matches!(error, ParseError::NoParse { position, .. } if position == rule.len()),
                "{rule}: {error:?}"
            );
            continue;
        }
        assert_eq!(
            plain_rule_error(rule),
            ParseError::Scope {
                parent: parent.to_owned(),
                child: "#KRewrite".to_owned(),
            },
            "{rule}"
        );
    }
}

/// Without a derivation that breaks a scope where the readings fail, the violation of a body
/// with no reading is the one its derivations do break there: `a => a => a` keeps every rewrite
/// where a rewrite may stand. In `g(a => a => a, a => a + a)` only the first argument has no
/// reading; the second has a valid one (`a => (a + a)`), so its misplaced reading
/// (`(a => a) + a`) is not what fails, and the first argument's violation is reported.
///
/// Both readings of `a => a => a` break the rewrite's associativity, one at its left child and
/// one at its right; the two errors differ only in the side they name, and the reported one is
/// the least by what it says (`ParseError::violation_order`), the left.
///
/// In the portable build's rule grammar a rewrite is never a side of another, so `a => a => a`
/// has no derivation and is reported where it ends: the whole body, or the first argument.
#[test]
fn a_body_with_no_misplaced_construct_reports_its_own_violation() {
    for rule in ["a => a => a", "g(a => a => a, a => a + a)"] {
        let error = plain_rule_error(rule);
        #[cfg(feature = "z3-inference")]
        let reported = matches!(
            error,
            ParseError::Associativity { ref parent, ref child, side }
                if parent == "#KRewrite" && child == "#KRewrite" && side == "left"
        );
        #[cfg(not(feature = "z3-inference"))]
        let reported = matches!(
            error,
            ParseError::NoParse { position, .. }
                if position == rule.find(',').unwrap_or(rule.len())
        );
        assert!(reported, "{rule}: {error:?}");
    }
}

/// `polymorphic_rhs_keeps_overload_branch_parameters_independent` (cgascap) without the
/// prelude, so that the portable build reaches the rule: its two well-sorted readings share one
/// maximal typing and differ in the `cap` overload and the instantiation of `ite`'s parameter.
#[test]
fn cgascap_is_left_to_z3_in_the_portable_build() {
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
    let resolved = resolve_rule_bubbles(&lowered(source));

    #[cfg(not(feature = "z3-inference"))]
    {
        let error = resolved.expect_err("the portable build does not choose within one typing");
        let RuleError::Parse(error) = error else {
            panic!("expected a parse error, got {error:?}")
        };
        assert_eq!(
            error.error,
            ParseError::Z3InferenceRequired {
                ambiguity: true,
                parametric_sorts: false,
            }
        );
    }
    #[cfg(feature = "z3-inference")]
    {
        let body = only_rule_body(&resolved.expect("the z3 build decides the rule"));
        assert!(body.contains("capInt"), "{body}");
        assert!(!body.contains("capGas"), "{body}");
        assert!(body.contains("=>ite("), "{body}");
    }
}

/// `lam(0 => 0)(0)` reads as `lam1` over a rewrite or as `lam2` over a pattern and a body
/// (the shape of the prelude's `#fun2` and `#fun3`). The rule has no variable, so both trees
/// share the empty typing; they instantiate different parametric productions and lower to
/// different terms. The z3 build keeps every tree that some parameter vector types, so both
/// readings reach `prefer`, which takes `lam1{Int}`. The portable decision does not model the
/// choice among parameter instantiations and leaves the rule to Z3. A portable rule grammar
/// that offers only the `lam2` reading (one that does not parse a rewrite as the argument of
/// `lam1`) gives the portable engine a single tree, which it may decide; either way the
/// portable build never takes `lam1` over `lam2` by itself.
#[test]
fn preferred_reading_among_parameter_instantiations_is_left_to_z3() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Int ::= "trigger" [symbol(trigger), function]
          syntax {S} S ::= "lam" "(" S ")" "(" S ")" [symbol(lam1), prefer]
          syntax {S1, S2} S1 ::= "lam" "(" S2 "=>" S1 ")" "(" S2 ")" [symbol(lam2)]

          rule trigger => lam(0 => 0)(0)
        endmodule
    "#};
    let resolved = resolve_rule_bubbles(&lowered(source));

    #[cfg(not(feature = "z3-inference"))]
    match resolved {
        Err(RuleError::Parse(error))
            if error.error
                == ParseError::Z3InferenceRequired {
                    ambiguity: true,
                    parametric_sorts: false,
                } => {}
        Ok(definition) => {
            let body = only_rule_body(&definition);
            assert!(body.contains("lam2"), "{body}");
            assert!(!body.contains("lam1"), "{body}");
        }
        Err(error) => panic!("expected Z3InferenceRequired or the lam2 reading, got {error:?}"),
    }
    #[cfg(feature = "z3-inference")]
    {
        let body = only_rule_body(&resolved.expect("the z3 build decides the rule"));
        assert!(body.contains("lam1("), "{body}");
        assert!(!body.contains("lam2"), "{body}");
    }
}

/// `pick(pick(0))` over `pick1 [prefer]` (`{S} S ::= pick(S)`) and `pick2` (`{S1, S2} S1 ::=
/// pick(S2)`): every reading shares the empty typing and the readings differ only in which
/// parametric production each `pick` instantiates and at which sort. One parameter vector
/// (`pick2`'s argument parameter at `Int`) types all four readings, so the z3 build does not
/// trade a reading for a parameter at `K` (which gave `pick2{Int, K}(pick1{K}(0))`), and
/// `prefer` resolves the group to `pick1{Int}(pick1{Int}(0))`. The portable decision does not
/// model the choice among parameter instantiations, so it leaves the rule to Z3.
#[test]
fn nested_preferred_reading_among_parameter_instantiations_is_left_to_z3() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Int ::= "trigger" [symbol(trigger), function]
          syntax {S} S ::= "pick" "(" S ")" [symbol(pick1), prefer]
          syntax {S1, S2} S1 ::= "pick" "(" S2 ")" [symbol(pick2)]

          rule trigger => pick(pick(0))
        endmodule
    "#};
    let resolved = resolve_rule_bubbles(&lowered(source));

    #[cfg(not(feature = "z3-inference"))]
    {
        let error = resolved.expect_err("the portable build does not choose within one typing");
        let RuleError::Parse(error) = error else {
            panic!("expected a parse error, got {error:?}")
        };
        assert_eq!(
            error.error,
            ParseError::Z3InferenceRequired {
                ambiguity: true,
                parametric_sorts: false,
            }
        );
    }
    #[cfg(feature = "z3-inference")]
    {
        let body = only_rule_body(&resolved.expect("the z3 build decides the rule"));
        assert_eq!(body, r#"trigger(.KList)=>pick1(pick1(#token("0","Int")))"#);
    }
}

/// `pick(0)` over `pick1 [prefer]` and `pick2`: `pick1{Int}(0)` and `pick2{Int, S2}(0)` share
/// the empty typing. Placing `pick2`'s free argument parameter at `K` keeps both readings, so
/// the parameter preference chooses only `pick2`'s instantiation and `prefer` takes `pick1`.
#[test]
fn flat_preferred_reading_among_parameter_instantiations_is_the_prefer_reading() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Int ::= "trigger" [symbol(trigger), function]
          syntax {S} S ::= "pick" "(" S ")" [symbol(pick1), prefer]
          syntax {S1, S2} S1 ::= "pick" "(" S2 ")" [symbol(pick2)]

          rule trigger => pick(0)
        endmodule
    "#};
    let resolved = resolve_rule_bubbles(&lowered(source));

    #[cfg(not(feature = "z3-inference"))]
    {
        let error = resolved.expect_err("the portable build does not choose within one typing");
        let RuleError::Parse(error) = error else {
            panic!("expected a parse error, got {error:?}")
        };
        assert_eq!(
            error.error,
            ParseError::Z3InferenceRequired {
                ambiguity: true,
                parametric_sorts: false,
            }
        );
    }
    #[cfg(feature = "z3-inference")]
    {
        let body = only_rule_body(&resolved.expect("the z3 build decides the rule"));
        assert_eq!(body, r#"trigger(.KList)=>pick1(#token("0","Int"))"#);
    }
}

/// `pickB [prefer]` has the result sort `Bool`, which no parameter vector places under the
/// `Int` the rule's right-hand side expects, so its reading is ill-sorted under every vector
/// and is dropped before `prefer` could take it; `pick2{Int, K}(0)` is the rule.
#[test]
fn preferred_reading_ill_sorted_under_every_parameter_vector_is_dropped() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Bool ::= "true" [symbol(true)]
          syntax Int ::= "trigger" [symbol(trigger), function]
          syntax {S} Bool ::= "pick" "(" S ")" [symbol(pickB), prefer]
          syntax {S1, S2} S1 ::= "pick" "(" S2 ")" [symbol(pick2)]

          rule trigger => pick(0)
        endmodule
    "#};
    let body = only_rule_body(
        &resolve_rule_bubbles(&lowered(source)).expect("the well-sorted reading is the rule"),
    );
    assert_eq!(body, r#"trigger(.KList)=>pick2(#token("0","Int"))"#);
}

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
    // The two readings differ at the left-hand application and at the sorts of both
    // variables on the right, each reported as a subterm.
    let ParseError::Ambiguous {
        alternatives,
        span,
        places,
    } = error.error
    else {
        panic!("expected an ambiguity, got {:?}", error.error)
    };

    assert!(span.is_some());
    assert!(alternatives.is_empty(), "{alternatives:#?}");
    assert_eq!(
        places
            .iter()
            .map(|place| place
                .alternatives
                .iter()
                .map(|alternative| alternative.term.as_str())
                .collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        [
            vec![
                "aF(#SemanticCastToInt(X),#SemanticCastToFoo(Y))",
                "aK(#SemanticCastToK(X),#SemanticCastToInt(Y))"
            ],
            vec!["#SemanticCastToInt(X)", "#SemanticCastToK(X)"],
            vec!["#SemanticCastToFoo(Y)", "#SemanticCastToInt(Y)"],
        ],
        "{places:#?}"
    );
    // Each subterm is located, the variables by the text the casts inference added cover.
    assert!(
        places.iter().all(|place| place.location.is_some()),
        "{places:#?}"
    );
}

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
        .find_map(|sentence| match &**sentence {
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
            alternatives, span, ..
        } = error.error
        else {
            panic!("expected an ambiguity, got {:?}", error.error)
        };

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
        assert!(
            matches!(
                error,
                RuleError::Parse(ref error)
                    if matches!(
                        error.error,
                        ParseError::Ambiguous { ref alternatives, .. } if alternatives.len() == 2
                    )
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
        .find_map(|sentence| match &**sentence {
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
        .find_map(|sentence| match &**sentence {
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
        .find(|sentence| matches!(&***sentence, Sentence::Rule { .. }))
        .expect("the rule should be resolved");
    let Sentence::Rule { body, .. } = &**sentence else {
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
        .find_map(|sentence| match &**sentence {
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

/// `X:Big` bounds X from above by Big; `a(X)` is ambiguous between `aS(Small)` and `aF(Foo)`.
/// The `aF` reading needs a sort below both Big and Foo, and there is none, so the one
/// well-sorted reading is `aS` with X at Small.
#[test]
fn semcast3_and_semcast4_take_their_one_well_sorted_reading() {
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
        let resolved = resolve_rule_bubbles(&lowered_module(source, "TEST"))
            .unwrap_or_else(|error| panic!("{name} has one well-sorted reading: {error:?}"));
        let sentence = resolved
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find(|sentence| matches!(&***sentence, Sentence::Rule { .. }))
            .unwrap_or_else(|| panic!("{name}: the rule should be resolved"));
        let Sentence::Rule { body, .. } = &**sentence else {
            unreachable!()
        };
        let text = body.to_string();
        assert!(
            text.contains("aS(#SemanticCastToSmall(X))"),
            "{name}: {text}"
        );
        assert!(!text.contains("aF("), "{name}: {text}");
        let resolved_views = k_rust::definition::ResolvedDefinition::resolve(&resolved).unwrap();
        let subsorts = resolved_views
            .subsorts(resolved_views.module_id("TEST").unwrap())
            .unwrap();
        let Sentence::Rule { body, .. } =
            k_rust::kompile::resolve_semantic_casts_in_sentence(&subsorts, (**sentence).clone())
                .unwrap()
        else {
            unreachable!()
        };
        let resolved_body = format!("{:?}", body.unannotated());
        let small_x =
            r#"Variable { name: "X", sort: Some(Sort { name: "Small", parameters: [] }) }"#;
        assert_eq!(
            resolved_body
                .matches(r#"Variable { name: "X", sort: "#)
                .count(),
            resolved_body.matches(small_x).count(),
            "{name}: every occurrence of X is at Small: {resolved_body}"
        );
        assert_eq!(
            resolved_body.matches(small_x).count(),
            3,
            "{name}: {resolved_body}"
        );
    }
}

/// Resolves the one rule of `source` and returns its body after `resolve_semantic_casts`,
/// asserting that every occurrence of `X` carries `Small`.
fn assert_every_x_is_small_after_resolving_casts(name: &str, source: &str, occurrences: usize) {
    let resolved = resolve_rule_bubbles(&lowered_module(source, "TEST"))
        .unwrap_or_else(|error| panic!("{name}: X at Small is well-sorted: {error:?}"));
    let sentence = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find(|sentence| matches!(&***sentence, Sentence::Rule { .. }))
        .unwrap_or_else(|| panic!("{name}: the rule should be resolved"));
    let resolved_views = k_rust::definition::ResolvedDefinition::resolve(&resolved).unwrap();
    let subsorts = resolved_views
        .subsorts(resolved_views.module_id("TEST").unwrap())
        .unwrap();
    let Sentence::Rule { body, .. } =
        k_rust::kompile::resolve_semantic_casts_in_sentence(&subsorts, (**sentence).clone())
            .unwrap()
    else {
        unreachable!()
    };
    let resolved_body = format!("{:?}", body.unannotated());
    let small_x = r#"Variable { name: "X", sort: Some(Sort { name: "Small", parameters: [] }) }"#;
    assert_eq!(
        resolved_body
            .matches(r#"Variable { name: "X", sort: "#)
            .count(),
        occurrences,
        "{name}: {resolved_body}"
    );
    assert_eq!(
        resolved_body.matches(small_x).count(),
        occurrences,
        "{name}: every occurrence of X is at Small: {resolved_body}"
    );
}

/// The cast occurrence `X:Big` comes after the occurrence that narrows X to Small, so the cast
/// must itself record the inferred sort; the rule is unambiguous (portable engine).
#[test]
fn semantic_cast_after_the_narrowing_occurrence_keeps_the_inferred_sort() {
    let source = include_str!("fixtures/reference/inner/semcast2/test.k").replace(
        "rule bar(X:Big) => foo(X)",
        "rule foo(X) ~> bar(X:Big) => .K",
    );
    assert_every_x_is_small_after_resolving_casts("foo(X) ~> bar(X:Big)", &source, 2);
}

/// As above with the ambiguous `a(X)`, decided in both builds: only `aS` is well-sorted, with X
/// at Small.
#[test]
fn semantic_cast_after_an_ambiguous_narrowing_occurrence_keeps_the_inferred_sort() {
    let source = include_str!("fixtures/reference/inner/semcast3/test.k").replace(
        "rule bar(X:Big) => foo(X) ~> a(X)",
        "rule a(X) ~> bar(X:Big) => .K",
    );
    assert_every_x_is_small_after_resolving_casts("a(X) ~> bar(X:Big)", &source, 2);
}

/// The strict cast is the exact annotation: `X::Big` gives X all of Big, so the occurrence in
/// `foo(Small)` is a sort error.
#[test]
fn semcast2_with_a_strict_cast_is_a_sort_error() {
    let source = include_str!("fixtures/reference/inner/semcast2/test.k")
        .replace("rule bar(X:Big) => foo(X)", "rule bar(X::Big) => foo(X)");
    let result = resolve_rule_bubbles(&lowered_module(&source, "TEST"));
    assert!(
        matches!(
            result,
            Err(RuleError::Parse(ref error))
                if matches!(error.error, ParseError::SortInference { .. })
        ),
        "X::Big must be a sort error: {result:?}"
    );
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
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter(|sentence| matches!(&***sentence, Sentence::Bubble { .. }))
        .count();
    assert_eq!(bubbles, 0);
    let rules = loaded
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter(|sentence| {
            matches!(
                &***sentence,
                Sentence::Rule { attributes, .. }
                    if attributes.source() == Some("cells.k")
            )
        })
        .filter_map(|sentence| sentence_summary(sentence))
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
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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

// `P #as V` matches P and binds V to the matched subterm, so both of its sides are
// left-hand-side patterns and a rewrite on either side has no before/after reading.
// Both rule grammars compose `#as` and `=>` (the portable one decides the resulting ambiguous
// monomorphic forest by sort inference); rewrite placement is a property of the whole rule,
// which the definition checks enforce, as they do for nested rewrites. This pins the rejection
// through the public load path in both builds.
const REWRITE_ON_THE_VARIABLE_SIDE_OF_AS: &str = indoc! {r##"
    module MAIN
      syntax Foo ::= "a"
      syntax KItem ::= foo(Foo)
      configuration <k> foo(a) </k>
      rule <k> foo(a) #as (V => W) </k>
      syntax K
      syntax Map
    endmodule
"##};

fn load_rewrite_on_the_variable_side_of_as()
-> Result<k_rust::outer::LoadedDefinition, k_rust::outer::LoadError> {
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    load(
        ResolvedSource::new("as-rewrite.k", REWRITE_ON_THE_VARIABLE_SIDE_OF_AS),
        "MAIN",
        &mut resolver,
    )
}

#[test]
fn rewrite_on_the_variable_side_of_an_as_pattern_is_rejected_by_the_definition_checks() {
    let loaded = load_rewrite_on_the_variable_side_of_as()
        .expect("the z3 rule grammar parses a rewrite as the alias of an #as pattern");
    let diagnostics = k_rust::definition::check_definition(loaded.resolved())
        .expect("definition checks run on the loaded definition");
    let placement = diagnostics
        .iter()
        .filter(|diagnostic| {
            diagnostic.code == k_rust::diagnostic::DiagnosticCode::InvalidRewrite
                && diagnostic.severity == k_rust::diagnostic::Severity::Error
        })
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        placement,
        ["Rewrites are not allowed inside an #as pattern."],
        "{diagnostics:?}"
    );
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
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| sentence_summary(sentence))
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
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| sentence_summary(sentence))
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
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| sentence_summary(sentence))
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
            .definition()
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .any(|sentence| matches!(&**sentence, Sentence::Rule { .. }))
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
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| sentence_summary(sentence))
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
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
    assert!(
        matches!(
            error,
            RuleError::Parse(ref error) if matches!(error.error, ParseError::Ambiguous { .. })
        ),
        "{error:?}"
    );
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
        .find_map(|sentence| match &**sentence {
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
        .find_map(|sentence| match &**sentence {
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
fn imported_rule_modules_use_their_own_scanner() {
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
    let definition = resolve_rule_bubbles(&lowered(source)).expect("RULES does not see TOKEN");
    let rules = definition
        .modules
        .iter()
        .find(|module| module.name == "RULES")
        .unwrap();
    assert_eq!(x_variables_and_id_tokens(&rules.local_sentences[0]), (2, 0));
}

/// A terminal that only an importing module declares is no lexeme of an imported module's
/// rule-like sentences, whatever their kind; the importing module's own sentences see both
/// its own terminals and the imported ones.
#[test]
fn an_importing_modules_terminal_does_not_split_an_imported_modules_sentences() {
    let source = indoc! {r#"
        module LIB
          syntax Exp ::= "a" [symbol(a)]
                       | Exp "+" Exp [symbol(plus), left]
          syntax KResult
          context a+HOLE:Exp
          rule a+a => a
          claim a+a => a
        endmodule
        module MAIN
          imports LIB
          syntax Exp ::= "+a" [symbol(plusA)]
          rule a + a => +a
          rule +a + a => a
        endmodule
    "#};
    let definition = resolve_rule_bubbles(&lowered(source)).unwrap_or_else(|error| {
        panic!("every module parses its sentences with its own scanner: {error}")
    });
    let lib = definition
        .modules
        .iter()
        .find(|module| module.name == "LIB")
        .unwrap();
    for sentence in &lib.local_sentences {
        if matches!(
            &**sentence,
            Sentence::Context { .. } | Sentence::Rule { .. } | Sentence::Claim { .. }
        ) {
            let text = format!("{sentence:?}");
            assert!(text.contains("plus"), "{text}");
            assert!(!text.contains("plusA"), "{text}");
        }
    }
    let main = definition.main_module().unwrap();
    let rules = main
        .local_sentences
        .iter()
        .filter(|sentence| matches!(&***sentence, Sentence::Rule { .. }))
        .map(|sentence| format!("{sentence:?}"))
        .collect::<Vec<_>>();
    assert_eq!(rules.len(), 2);
    for rule in &rules {
        assert!(rule.contains("\"plus\""), "{rule}");
        assert!(rule.contains("\"plusA\""), "{rule}");
    }
}

/// A terminal the main module declares spells part of a builtin module's rule (`0` after
/// `+Int` in INT-SYMBOLIC, `-1` after `==Int` in STRING-COMMON). The builtin modules do not
/// import MAIN, so their rules are lexed without it: the definition loads, compiles, and the
/// backend accepts it.
#[test]
fn a_main_module_terminal_does_not_split_a_builtin_modules_rules() {
    for (import, terminal) in [("INT", "0"), ("STRING", "-1")] {
        let source = format!(
            "module MAIN\n  imports {import}\n  syntax Foo ::= \"a\" | \"{terminal}\"\nendmodule\n"
        );
        let loaded = load_with_prelude_options(
            &source,
            "main.k",
            "MAIN",
            vec![
                k_rust::kompile::CompilationBackend::Rust
                    .excluded_module_attribute()
                    .into(),
            ],
        )
        .unwrap_or_else(|error| panic!("{terminal:?} beside {import} loads: {error}"));
        let artifacts = k_rust::kompile::compile_loaded_definition(
            &loaded,
            k_rust::kompile::CompileOptions::default(),
        )
        .unwrap_or_else(|error| panic!("{terminal:?} beside {import} compiles: {error}"));
        let kore = k_rust::kore::parser::parse_definition(&artifacts.definition_kore).unwrap();
        k_rust_backend::definition::BackendDefinition::internalize(&kore, "MAIN")
            .unwrap_or_else(|error| panic!("{terminal:?} beside {import}: backend load: {error}"));
    }
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
                &**sentence,
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
            &**sentence,
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

#[test]
fn preferred_production_selects_its_ambiguity_branch() {
    let source = selector_source("prefer");
    assert_rule_resolution_snapshot!(source.as_str());
}

#[test]
fn avoided_production_removes_its_ambiguity_branch() {
    let source = selector_source("avoid");
    assert_rule_resolution_snapshot!(source.as_str());
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
        .find_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .expect("the rule should be resolved");

    // The loaded rule carries no instance; the two `same` nodes are typed at `A` and `B`, which
    // only independent parameter variables admit.
    assert_eq!(
        body,
        "pair(same(a(.KList)),same(b(.KList)))=>pair(a(.KList),b(.KList))"
    );
}

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
            .find_map(|sentence| match &**sentence {
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
        matches!(&**sentence, Sentence::Rule { body, .. } if matches!(body.unannotated(), Term::Rewrite { .. }))
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
        .find_map(|sentence| match &**sentence {
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
        .find_map(|sentence| match &**sentence {
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

// `P #as V` patterns. Each snapshot is shared by the portable and the z3-inference builds, so
// the two parses must resolve to the same rule sentence: the alias takes the sort of the
// position the `#as` occupies, like its pattern.
macro_rules! as_pattern_snapshot {
    ($name:ident, $rule:expr) => {
        #[test]
        fn $name() {
            let source = format!(
                indoc! {r#"
                    module MAIN
                      syntax Int ::= r"[0-9]+" [token]
                      syntax Exp ::= Int | bar(Exp) [symbol(bar)]
                      syntax KItem ::= foo(Int) [symbol(foo)]
                      syntax List ::= ListItem(KItem) [symbol(ListItem)]
                                    | List List [symbol(_List_)]
                                    | ".List" [symbol(.List)]
                      syntax KCell ::= "<k>" K "</k>" [cell]
                      rule {}
                    endmodule
                "#},
                $rule
            );
            assert_rule_resolution_snapshot!(source.as_str());
        }
    };
}

as_pattern_snapshot!(as_pattern_alias_of_an_application, "foo(0) #as V");
as_pattern_snapshot!(as_pattern_inside_a_cell, "<k> foo(0) #as V </k>");
as_pattern_snapshot!(
    as_pattern_inside_a_cell_with_dots,
    "<k> foo(0) #as V ... </k>"
);
as_pattern_snapshot!(as_pattern_alias_with_a_semantic_cast, "foo(0) #as V:KItem");
as_pattern_snapshot!(as_pattern_alias_with_a_narrower_cast, "foo(0) #as V:Int");
as_pattern_snapshot!(
    as_pattern_alias_with_a_syntactic_cast,
    "foo(0) #as V::KItem"
);
as_pattern_snapshot!(as_pattern_anonymous_alias, "foo(0) #as _");
// Argument positions: the alias takes the sort of the argument the `#as` fills (`Int`, `Exp`,
// `KItem`), which rule sorts at argument positions make available to the `#as` production.
as_pattern_snapshot!(as_pattern_at_an_argument_position, "foo(0 #as V)");
as_pattern_snapshot!(as_pattern_at_a_supersort_argument_position, "bar(0 #as V)");
as_pattern_snapshot!(
    as_pattern_at_an_argument_position_with_a_cast,
    "foo(0 #as V:Int)"
);
as_pattern_snapshot!(
    as_pattern_at_a_kitem_argument_position,
    "ListItem(foo(0) #as V)"
);
// A rewrite side is a pattern of the rewrite's sort, and `P #as V` is one: an `#as` stands as
// either side of a rewrite, at the top of the rule, in a cell, or at an argument position.
as_pattern_snapshot!(
    as_pattern_as_the_left_side_of_a_rewrite,
    "foo(0) #as V => V"
);
as_pattern_snapshot!(
    as_pattern_as_the_left_side_of_a_rewrite_in_a_cell,
    "<k> foo(0) #as V => V </k>"
);
as_pattern_snapshot!(
    as_pattern_as_the_left_side_of_a_rewrite_in_a_cell_with_dots,
    "<k> foo(0) #as V => V ... </k>"
);
as_pattern_snapshot!(
    as_pattern_as_the_left_side_of_a_rewrite_at_an_argument_position,
    "foo(0 #as V => 1)"
);
as_pattern_snapshot!(
    as_pattern_as_the_right_side_of_a_rewrite_at_a_kitem_argument_position,
    "ListItem(foo(0) => foo(1) #as V)"
);
as_pattern_snapshot!(
    as_pattern_as_both_sides_of_a_rewrite,
    "foo(0) #as V => foo(1) #as W"
);
as_pattern_snapshot!(
    as_pattern_with_a_nested_alias_as_a_rewrite_side,
    "bar(0 #as V) #as W => W"
);
as_pattern_snapshot!(
    as_pattern_with_a_cast_alias_as_a_rewrite_side,
    "bar(0 #as V:Int) => bar(V)"
);
as_pattern_snapshot!(
    as_pattern_as_both_sides_of_a_rewrite_at_an_argument_position,
    "bar(0 #as V => 1 #as W)"
);
as_pattern_snapshot!(
    as_pattern_as_the_left_side_of_a_rewrite_followed_by_a_sequence,
    "<k> foo(0) #as V => V ~> X ... </k>"
);
as_pattern_snapshot!(
    as_pattern_with_a_cast_alias_as_the_left_side_of_a_rewrite,
    "foo(0) #as V:KItem => V"
);
as_pattern_snapshot!(
    as_pattern_with_an_anonymous_alias_as_the_left_side_of_a_rewrite,
    "foo(0) #as _ => .K"
);

/// A parenthesized `#as` or rewrite means the same rule as the unparenthesized one. The
/// portable build either parses it to that rule or reports that it needs Z3 inference.
#[test]
fn parenthesized_as_pattern_under_a_rewrite_means_the_unparenthesized_rule() {
    let rule_body = |rule: &str| {
        let source = format!(
            indoc! {r#"
                module MAIN
                  syntax Int ::= r"[0-9]+" [token]
                  syntax KItem ::= foo(Int) [symbol(foo)]
                  syntax KCell ::= "<k>" K "</k>" [cell]
                  rule {}
                endmodule
            "#},
            rule
        );
        resolve_rule_bubbles(&lowered(&source)).map(|resolved| {
            resolved
                .main_module()
                .unwrap()
                .local_sentences
                .iter()
                .find_map(|sentence| match &**sentence {
                    Sentence::Rule { body, .. } => Some(body.to_string()),
                    _ => None,
                })
                .unwrap()
        })
    };
    for (parenthesized, plain) in [
        ("(foo(0) #as V) => V", "foo(0) #as V => V"),
        ("(foo(0) #as V => V)", "foo(0) #as V => V"),
        ("foo(0) #as (V) => V", "foo(0) #as V => V"),
        (
            "<k> (foo(0) #as V) => V ... </k>",
            "<k> foo(0) #as V => V ... </k>",
        ),
        ("foo((0 #as V) => 1)", "foo(0 #as V => 1)"),
    ] {
        let expected = rule_body(plain).expect(plain);
        match rule_body(parenthesized) {
            Ok(body) => assert_eq!(body, expected, "{parenthesized}"),
            #[cfg(not(feature = "z3-inference"))]
            Err(RuleError::Parse(error))
                if matches!(error.error, ParseError::Z3InferenceRequired { .. }) => {}
            Err(error) => panic!("{parenthesized}: {error:?}"),
        }
    }
}

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
        |sentence| matches!(&**sentence, Sentence::Rule { body, .. } if body.to_string() == "small(.KList)=>big(.KList)")
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
        .filter_map(|sentence| match &**sentence {
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
        .find_map(|sentence| match &**sentence {
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
            .any(|sentence| matches!(&**sentence, Sentence::Rule { .. }))
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
    assert_rule_resolution_snapshot!(source);
}

/// The size and SHA-256 of a large artifact. Its snapshot is recorded by the z3-inference build
/// and asserted by the portable build, so both builds must produce the same bytes; the artifact
/// itself is written under the test binary's temporary directory, where a mismatch can be
/// diffed against the other build's copy.
#[derive(Debug)]
#[allow(dead_code)]
struct ArtifactDigest {
    bytes: usize,
    sha256: String,
}

fn artifact_digest(name: &str, text: &str) -> ArtifactDigest {
    use sha2::Digest;
    // A rerun under a type-inference mode writes its own copy.
    let mode = std::env::var("KRUST_TYPE_INFERENCE_MODE").map_or(String::new(), |mode| mode + "-");
    let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join(mode + name);
    std::fs::write(&path, text).unwrap();
    eprintln!("{name}: {}", path.display());
    ArtifactDigest {
        bytes: text.len(),
        sha256: sha2::Sha256::digest(text.as_bytes())
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect(),
    }
}

/// The embedded prelude is inside the portable boundary: an empty main module with the prelude
/// loads in either build, under either backend's module exclusion, to the same definition.
/// Checked inference (`every_rule_test_passes_under_checked_inference`) runs the portable
/// decision beside Z3 on every forest of the prelude and fails on any disagreement, so the
/// equality is also tested rule by rule.
#[test]
fn the_standard_prelude_loads_to_the_same_definition_in_both_builds() {
    for excluded in ["concrete", "symbolic"] {
        let loaded =
            load_with_prelude_excluding("module MAIN endmodule", "test.k", "MAIN", excluded)
                .unwrap_or_else(|error| {
                    panic!("the prelude should load with {excluded} excluded: {error}")
                });
        let json = k_rust::definition::json::to_string_pretty(loaded.definition()).unwrap();
        let digest = artifact_digest(&format!("standard-prelude-{excluded}.json"), &json);
        insta::with_settings!({
            description => format!(
                "definition::json::to_string_pretty of `module MAIN endmodule` loaded with the embedded prelude, {excluded} excluded"
            ),
            omit_expression => true,
            prepend_module_to_snapshot => true,
            snapshot_suffix => excluded,
        }, {
            insta::assert_debug_snapshot!("standard_prelude_definition", digest);
        });
    }
}

fn load_with_prelude(
    source: &str,
    name: &str,
    main_module: &str,
) -> Result<k_rust::outer::LoadedDefinition, k_rust::outer::LoadError> {
    load_with_prelude_options(source, name, main_module, Vec::new())
}

fn load_with_prelude_excluding(
    source: &str,
    name: &str,
    main_module: &str,
    excluded_module_attribute: &str,
) -> Result<k_rust::outer::LoadedDefinition, k_rust::outer::LoadError> {
    load_with_prelude_options(
        source,
        name,
        main_module,
        vec![excluded_module_attribute.into()],
    )
}

fn load_with_prelude_options(
    source: &str,
    name: &str,
    main_module: &str,
    excluded_module_attributes: Vec<String>,
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
            excluded_module_attributes,
            ..LoadOptions::default()
        },
    )
}

#[cfg(feature = "z3-inference")]
#[test]
fn preferred_fun2_reading_needs_no_fun3_completion() {
    // reference: k/result/bin/kompile test.k --backend haskell
    //   --main-module PARAMETRIC-COMPLETION-LUB
    //   --syntax-module PARAMETRIC-COMPLETION-LUB (exit 113 before parsed.txt)
    // The rule reads as `#fun2` over a rewrite or as `#fun3`. Both readings are well-sorted
    // (the parser-layer `#KToken` children have sort KBott), so `#fun2 [prefer]` is the rule
    // and `#fun3`'s `Sort2` is never completed from its two KBott children. The pinned
    // reference completes `#fun3` and rejects the rule for want of a unique least upper bound;
    // that is a recorded divergence. The completion error itself is covered by
    // `rejects_parametric_completion_without_a_unique_least_upper_bound`.
    let source = include_str!("fixtures/reference/inner/parametric-completion-lub/test.k");
    let loaded = load_with_prelude(
        source,
        "parametric-completion-lub.k",
        "PARAMETRIC-COMPLETION-LUB",
    )
    .expect("the preferred #fun2 reading is well-sorted");
    let bodies = rule_bodies(&loaded);
    assert!(
        bodies.iter().any(|body| body.contains("#fun2")),
        "{bodies:?}"
    );
    assert!(
        !bodies.iter().any(|body| body.contains("#fun3")),
        "{bodies:?}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn rejects_parametric_completion_without_a_unique_least_upper_bound() {
    // List completion instantiates `lam3`'s `S2` parameter as the least sort that holds both
    // positions it occupies. Both children are `#token` literals, which the parser reads at
    // `KBott`, the sort of its `#token` production: the sort a token spells, `Missing`, is the
    // sort of the term built afterwards. `KBott` is not a sort a term can have, and the sorts
    // above it that are have no unique least one, so the instantiation is refused. `lam3` has the
    // shape of the prelude's `#fun3` without a preferred `#fun2` reading.
    let source = indoc! {r#"
        module PARAMETRIC-COMPLETION-LUB
          imports INT

          syntax {S1, S2} S1 ::= "lam" "(" S2 "=>" S1 ")" "(" S2 ")" [symbol(lam3)]
          syntax Int ::= trigger() [function]
          rule trigger() => lam(#token("pattern", "Missing") => 0)(#token("argument", "Missing"))
        endmodule
    "#};
    let Err(error) = load_with_prelude(
        source,
        "parametric-completion-lub.k",
        "PARAMETRIC-COMPLETION-LUB",
    ) else {
        panic!("a parametric production without a unique completion LUB is rejected");
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
    // The control of `rejects_parametric_completion_without_a_unique_least_upper_bound`: equal
    // semantic Int children give `lam3`'s `S2` the unique admissible completion bound Int.
    let source = indoc! {r#"
        module PARAMETRIC-COMPLETION-LUB-CONTROL
          imports INT

          syntax {S1, S2} S1 ::= "lam" "(" S2 "=>" S1 ")" "(" S2 ")" [symbol(lam3)]
          syntax Int ::= trigger() [function]
          rule trigger() => lam(0 => 0)(0)
        endmodule
    "#};
    let loaded = load_with_prelude(
        source,
        "parametric-completion-lub-control.k",
        "PARAMETRIC-COMPLETION-LUB-CONTROL",
    )
    .expect("equal Int bounds have the unique admissible completion LUB Int");
    let bodies = rule_bodies(&loaded);
    assert!(
        bodies.iter().any(|body| body.contains("lam3")),
        "{bodies:?}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn fun_over_an_inner_rewrite_takes_the_preferred_fun2() {
    // `#fun(0 => 0)(0)` reads as `#fun2{Int}` over the rewrite `0 => 0` or as `#fun3{Int, S}`
    // with pattern `0` and body `0`. Some parameter vector types each reading (`#fun3`'s
    // pattern parameter at `Int` types both), so both reach `prefer`, which takes `#fun2`.
    let source = include_str!("fixtures/reference/inner/parametric-completion-lub/control.k");
    let loaded = load_with_prelude(
        source,
        "parametric-completion-lub-control.k",
        "PARAMETRIC-COMPLETION-LUB-CONTROL",
    )
    .expect("the preferred #fun2 reading is well-sorted");
    let bodies = rule_bodies(&loaded);
    assert!(
        bodies.iter().any(|body| body.contains("#fun2(")),
        "{bodies:?}"
    );
    assert!(
        !bodies.iter().any(|body| body.contains("#fun3")),
        "{bodies:?}"
    );
}

/// The rule bodies of `source`'s main module `TEST`, loaded with the prelude.
#[cfg(feature = "z3-inference")]
fn test_rule_bodies(source: &str, name: &str) -> Vec<String> {
    let loaded = load_with_prelude(source, name, "TEST")
        .unwrap_or_else(|error| panic!("{name} should load: {error:?}"));
    rule_bodies(&loaded)
}

#[cfg(feature = "z3-inference")]
#[test]
fn bracketed_parametric_result_is_one_reading_instantiated_at_k() {
    // A bracket has no node in the parsed term, and its concrete instances (one per sort) are how
    // the parser covers `{Sort} Sort ::= "(" Sort ")"`; they differ only in the instantiation of
    // `#Top`'s parameter, so they are one reading, whose free parameter is inferred as `K`. The
    // bracketed rule therefore has one parse and lowers exactly as the unbracketed one.
    let rule = |right: &str| {
        format!(
            "module TEST\n  imports INT\n  imports BOOL\n  syntax W ::= \"w32\" | \"w64\"\n  \
             rule #Ceil(@A0:W) => {right} [simplification]\nendmodule\n"
        )
    };
    let bracketed = test_rule_bodies(&rule("(#Top)"), "bracketed.k");
    let bare = test_rule_bodies(&rule("#Top"), "bare.k");
    assert_eq!(bracketed, bare);
    assert_eq!(bare.len(), 1, "{bare:?}");
}

#[cfg(feature = "z3-inference")]
#[test]
fn nested_bracketed_ml_connectives_are_one_reading() {
    // Reduced from wasm-data.md:461 (`#Ceil(#signed(..)) => (({ .. #Equals true } #And
    // #Ceil(..)) #And #Ceil(..))`): every bracket instance of the nested `#And`s is one reading,
    // so the rule has one parse, the parse of the same rule without brackets.
    let rule = |right: &str| {
        format!(
            "module TEST\n  imports INT\n  imports BOOL\n  syntax W ::= \"w32\" | \"w64\"\n  \
             syntax Int ::= sgn(W, Int) [function, total]\n  \
             syntax Bool ::= ok(W, Int) [function, total]\n  \
             rule ok(_, _) => true\n  rule sgn(_, N) => N\n  \
             rule #Ceil(sgn(@A0:W, @A1:Int))\n    => {right} [simplification]\nendmodule\n"
        )
    };
    let bracketed = test_rule_bodies(
        &rule("(({ ok(@A0, @A1) #Equals true } #And #Ceil(@A0)) #And #Ceil(@A1))"),
        "bracketed.k",
    );
    let bare = test_rule_bodies(
        &rule("{ ok(@A0, @A1) #Equals true } #And #Ceil(@A0) #And #Ceil(@A1)"),
        "bare.k",
    );
    assert_eq!(bracketed, bare);
    assert_eq!(bare.len(), 3, "{bare:?}");
}

#[cfg(feature = "z3-inference")]
#[test]
fn bracketed_parametric_term_in_a_k_cell_lowers_like_the_bare_term() {
    let rule = |right: &str| {
        format!(
            "module TEST\n  imports INT\n  imports ML-SYNTAX\n  syntax S ::= \"c\" | Int\n  \
             configuration <k> $PGM:K </k>\n  rule <k> c => {right} </k>\nendmodule\n"
        )
    };
    let bracketed = test_rule_bodies(&rule("(0 #And 1)"), "bracketed.k");
    let bare = test_rule_bodies(&rule("0 #And 1"), "bare.k");
    assert_eq!(bracketed, bare);
    assert!(bare.iter().any(|body| body.contains("#And(")), "{bare:?}");
}

#[cfg(feature = "z3-inference")]
#[test]
fn distinct_readings_that_only_a_parameter_preference_separates_are_ambiguous() {
    // The shape of issue-2287 a5-spec.k (`2 #And n +Int n`): `(2 #And n) +Int n` and
    // `2 #And (n +Int n)` are both well-sorted, the sentence has no variable to maximise, and no
    // priority, `prefer` or `avoid` relates `_+Int_` and `#And`. Only a preference for `#And`'s
    // free parameter at `K` would make the first ill-sorted, and a free parameter cannot reject a
    // reading, so the rule is ambiguous.
    let source = indoc! {r#"
        module TEST
          imports INT
          imports ML-SYNTAX
          syntax Int ::= "n" [function, total, no-evaluators]
          syntax S ::= "c" | Int
          configuration <k> $PGM:K </k>
          rule <k> c => 2 #And n +Int n </k>
        endmodule
    "#};
    let Err(error) = load_with_prelude(source, "a5.k", "TEST") else {
        panic!("two distinct well-sorted readings must be ambiguous");
    };
    let k_rust::outer::LoadError::RuleParsing(RuleError::Parse(error)) = &error else {
        panic!("expected a rule parse error, got {error:?}");
    };
    let ParseError::Ambiguous { alternatives, .. } = &error.error else {
        panic!("expected ParseError::Ambiguous, got {:?}", error.error);
    };
    let mut terms = alternatives
        .iter()
        .map(|alternative| alternative.term.as_str())
        .collect::<Vec<_>>();
    terms.sort_unstable();
    assert_eq!(
        terms,
        [
            "#And{K}(#token(\"2\",\"Int\"),`_+Int_`(`n_TEST_Int`(.KList),`n_TEST_Int`(.KList)))",
            "`_+Int_`(#And{Int}(#token(\"2\",\"Int\"),`n_TEST_Int`(.KList)),`n_TEST_Int`(.KList))",
        ]
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn sort_parameter_choice_visible_after_lowering_is_ambiguous() {
    // `wrap(I)` under `f(A) | f(B)` has one maximal typing (`I:Int`). The result of `wrap` is its
    // own parameter `S`, so `S` equals the sort its position expects: `A` under `f(A)`, `B` under
    // `f(B)`. Both vectors are admissible and no inference criterion orders them, so each is a
    // parse; they lower to distinct terms (`S` stays in the `wrap{S}` label), and no
    // post-inference pass orders `f(A)` against `f(B)`, so the rule is ambiguous.
    let source = include_str!("fixtures/sort-inference/parameter-choice.k");
    let Err(error) = load_with_prelude(source, "parameter-choice.k", "TEST") else {
        panic!("a sentence with differently lowering parameter choices must be ambiguous");
    };
    let k_rust::outer::LoadError::RuleParsing(RuleError::Parse(error)) = &error else {
        panic!("expected a rule parse error, got {error:?}");
    };
    let ParseError::Ambiguous { alternatives, .. } = &error.error else {
        panic!("expected ParseError::Ambiguous, got {:?}", error.error);
    };
    assert_eq!(error.module, "TEST");
    assert_eq!(
        error.location.map(|location| location.start_line),
        Some(10),
        "the error names the rule's location"
    );
    let mut terms = alternatives
        .iter()
        .map(|alternative| alternative.term.as_str())
        .collect::<Vec<_>>();
    terms.sort_unstable();
    assert_eq!(
        terms,
        [
            "`f(_)_TEST_Top_A`(`wrap(_)_TEST_S_S`{A}(#SemanticCastToInt(I)))",
            "`f(_)_TEST_Top_B`(`wrap(_)_TEST_S_S`{B}(#SemanticCastToInt(I)))",
        ]
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn sort_parameter_choice_resolved_by_prefer_compiles() {
    // The `#KRewrite` result is its own parameter, so the parameter equals the sort its position
    // expects: `Small` under `f(Small) [prefer]`, `Item` under `f(Item)`. Both vectors are
    // admissible; lowering erases the parameter, so the parses are `f` of `Small` and `f` of
    // `Item` over the same rewrite, and `prefer` keeps `f(Small)`. Keeping only the vector Z3
    // returned would lose the `f(Small)` parse whenever Z3 returns `Item`.
    let source = include_str!("fixtures/sort-inference/parameter-choice-prefer.k");
    let loaded = load_with_prelude(
        source,
        "parameter-choice-prefer.k",
        "PARAMETER-CHOICE-PREFER",
    )
    .expect("the post-inference prefer filter resolves the admissible parameter choices");
    assert_eq!(
        rule_bodies(&loaded),
        ["`run(_)_PARAMETER-CHOICE-PREFER_KItem_Wrapped`(\
             `f(_)_PARAMETER-CHOICE-PREFER_Wrapped_Small`(\
             `small(_)_PARAMETER-CHOICE-PREFER_Small_Int`(#SemanticCastToInt(I))=>\
             `small(_)_PARAMETER-CHOICE-PREFER_Small_Int`(\
             `_+Int_`(#SemanticCastToInt(I),#token(\"1\",\"Int\")))))"],
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn sort_parameter_choice_erased_by_lowering_compiles() {
    // The parenthesized rewrite's sort parameter may be `Small` or `Item`, and the surviving
    // bracket follows it; lowering drops brackets and `#KRewrite`'s sort, so every admissible
    // choice gives the same term and the rule compiles.
    let source = include_str!("fixtures/sort-inference/parameter-choice-lowered.k");
    let loaded = load_with_prelude(
        source,
        "parameter-choice-lowered.k",
        "PARAMETER-CHOICE-LOWERED",
    )
    .expect("admissible parameter choices that lower to the same term are accepted");
    assert_eq!(
        rule_bodies(&loaded),
        ["`run(_)_PARAMETER-CHOICE-LOWERED_KItem_Items`(\
             `___PARAMETER-CHOICE-LOWERED_Items_Item_Items`(\
             `small(_)_PARAMETER-CHOICE-LOWERED_Small_Int`(#SemanticCastToInt(I))=>\
             `small(_)_PARAMETER-CHOICE-LOWERED_Small_Int`(\
             `_+Int_`(#SemanticCastToInt(I),#token(\"1\",\"Int\"))),\
             #SemanticCastToItems(_Rest)))"],
    );
}

#[cfg(feature = "z3-inference")]
fn rule_bodies(loaded: &k_rust::outer::LoadedDefinition) -> Vec<String> {
    loaded
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .collect()
}

#[cfg(feature = "z3-inference")]
#[test]
fn mint_literal_width_comes_from_the_token_text() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module CHECKMINTLITERAL --syntax-module CHECKMINTLITERAL --output-definition ref-kompiled (exit 113)
    // A MINT.literal token spells its width in the digits after its first `p`/`P`, so `0p32` is
    // an `MInt{32}` even when the `MInt{6}` instantiation scanned it, and the ordinary subsort
    // check against `foo(MInt{6})` then fails.
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
    // A declared instance of a parametric sort, here `MInt{8}`, is a sort of the module like any
    // other: its values are K items, so the rule grammar has `KItem ::= MInt{8}`, and a rule may
    // cast a term to it.
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
    // `{term}:>MInt{8}` narrows the term to `MInt{8}`, so it lowers to the projection generated
    // for the cast sort.
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
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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

/// Every other test of this binary also passes under the hidden `checked` inference mode, which
/// the conformance driver uses (`ktest.mak` passes `--type-inference-mode checked`): every rule
/// is inferred by both the portable and the Z3 engine and the definition is rejected when they
/// disagree. So a rule on which the two engines disagree fails the suite even when no test
/// names it. The failure message starts with the name of each test that failed in the rerun,
/// so a test report shows them, and then gives the rerun's whole output. The rerun is a child
/// process, which owns the environment variable, so no other test observes it.
#[cfg(feature = "z3-inference")]
#[test]
fn every_rule_test_passes_under_checked_inference() {
    // This binary is already running under checked inference.
    if std::env::var("KRUST_TYPE_INFERENCE_MODE").as_deref() == Ok("checked") {
        return;
    }
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--skip", "every_rule_test_passes_under_checked_inference"])
        .env("KRUST_TYPE_INFERENCE_MODE", "checked")
        .output()
        .expect("the test binary re-runs itself");
    if output.status.success() {
        return;
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    let failed = failed_tests(&stdout);
    let summary = if failed.is_empty() {
        format!(
            "the rerun under KRUST_TYPE_INFERENCE_MODE=checked exited with {} without reporting a failed test",
            output.status
        )
    } else {
        format!(
            "{} inner_rules test(s) fail under KRUST_TYPE_INFERENCE_MODE=checked: {}",
            failed.len(),
            failed.join(", ")
        )
    };
    panic!(
        "{summary}\n\nrerun output:\n{stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// The tests a libtest run reports as failed, from its `test NAME ... FAILED` lines, in order.
#[cfg(feature = "z3-inference")]
fn failed_tests(stdout: &str) -> Vec<&str> {
    stdout
        .lines()
        .filter_map(|line| line.strip_prefix("test ")?.strip_suffix(" ... FAILED"))
        .collect()
}

/// `failed_tests` reads the names of the failed tests and nothing else from a libtest report.
#[cfg(feature = "z3-inference")]
#[test]
fn the_failed_tests_of_a_rerun_are_read_from_its_report() {
    let report = "\nrunning 3 tests\ntest a_rule_parses ... ok\ntest semcast2_is_accepted_end_to_end ... FAILED\ntest other::case ... FAILED\n\nfailures:\n\n---- semcast2_is_accepted_end_to_end stdout ----\ntest x ... FAILED inside a panic message\n\nfailures:\n    semcast2_is_accepted_end_to_end\n    other::case\n\ntest result: FAILED. 1 passed; 2 failed; 0 ignored\n";
    assert_eq!(
        failed_tests(report),
        ["semcast2_is_accepted_end_to_end", "other::case"]
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
    // A node expected at `#RuleBody` is a rule body just as one at `#RuleContent` is, and a
    // function rule's rewrite has the function's result sort, so the `#withConfig` production
    // bounds its rewrite child by the function sort exactly as `#RuleContent` does for a bare
    // rewrite; under checked inference (`every_rule_test_passes_under_checked_inference`) both
    // engines must instantiate the rewrite at Int.
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
fn reference_bare_variable_alias_body_is_cast_to_k() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --type-inference-mode checked --output-definition ref-kompiled (exit 0)
    // parsed.txt: context alias #SemanticCastToK(HERE) requires isFoo(#SemanticCastToK(HOLE)) [label(foo), ...]
    // Reduced from regression-new/context-alias-3 (test.k:7): the rule body is a bare variable,
    // which K's rule grammar reaches through `#RuleBody ::= K` (kast.md:343).
    // The bare body HERE stands at the `K` nonterminal of K's `#RuleBody ::= K` production, so
    // it is bounded by K, and K is also the largest sort a variable can have; one solution, cast
    // to K, on which both engines agree under checked inference
    // (`every_rule_test_passes_under_checked_inference`).
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
fn reference_exists_binder_variable_is_inferred_at_k() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --type-inference-mode checked --output-definition ref-kompiled (exit 0)
    // parsed.txt: rule `foo(_)_TEST_Exp_Int`(#SemanticCastToInt(_X))=>#Exists(#SemanticCastToK(Y),#Equals(#SemanticCastToK(?_I),#SemanticCastToK(Y))) requires #token("true","Bool") ensures #token("true","Bool")
    // Reduced from regression-new/checkWarns existsLHSBoundPass.k (rule at line 11), the one
    // ktest-fail step of that case whose verdict differs from the reference. parsed.txt omits
    // the inferred sort parameters of #Exists and #Equals, and so does the loaded rule; the casts
    // to K fix them at {K,K} when sort injection instantiates them.
    // Variables and sort parameters range over the sorts a term can have: of the parser's own
    // sorts only K, KItem and KLabel are among them, while KList is the sort of argument lists,
    // so the bound variable Y and the sort parameters of #Exists and #Equals never range over
    // KList; one maximal model, at K, on which both engines agree under checked inference
    // (`every_rule_test_passes_under_checked_inference`).
    let source = include_str!("fixtures/reference/inner/exists-binder/test.k");
    let loaded = load_with_prelude(source, "test.k", "TEST")
        .expect("the reference accepts the existential over a fresh variable");
    assert_eq!(
        rule_like_texts(&loaded, "test.k"),
        [
            "`foo(_)_TEST_Exp_Int`(#SemanticCastToInt(_X))=>#Exists(#SemanticCastToK(Y),#Equals(#SemanticCastToK(?_I),#SemanticCastToK(Y))) requires #token(\"true\",\"Bool\")"
        ]
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_rule_applies_a_named_field_projection() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --type-inference-mode checked --output-definition ref-kompiled (exit 0)
    // parsed.txt: rule `getFoo(_)_TEST_Int_Foo`(#SemanticCastToFoo(F))=>`project:test(_,_,_)_TEST_Foo_Int_Int_Int:foo`(#SemanticCastToFoo(F)) requires #token("true","Bool") ensures #token("true","Bool")
    // A named nonterminal `foo: Int` of `test(...)` declares a field of that production, and
    // the module provides the function that reads it, the production `Int ::= "foo" "(" Foo ")"`
    // labelled project:<klabel>:foo, which rules and (record-llvm 3.test/4.test) programs apply
    // like any other function of the module.
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
    // Host ratchet run 20: with the Z3 domain restricted to real sorts (3769711) the seed model
    // still prefers K for the #KRewrite parameter, but the maximality climb over the real
    // variables re-reads every constant from an unconstrained model and the parameter came back
    // as KItem, which checked mode reported against the portable engine's K. The parameter
    // preference of the seed must survive the climb; checked inference
    // (`every_rule_test_passes_under_checked_inference`) reruns this test.
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
fn reference_anywhere_rule_over_a_nullary_constructor_is_instantiated_at_its_sort() {
    // reference: k/result/bin/kompile test.k --backend llvm --main-module TEST --syntax-module TEST --type-inference-mode checked --allow-anywhere-haskell -w none --output-definition ref-kompiled (regression-new/issue-2909-allow-anywhere-haskell/llvm, verbatim, exit 0)
    // parsed.txt: rule `foo()_TEST_Foo`(.KList)=>`bar()_TEST_Foo`(.KList) requires #token("true","Bool") ensures #token("true","Bool") [anywhere, ..., priority(20)]
    //             rule `foo()_TEST_Foo`(.KList)=>`baz()_TEST_Foo`(.KList) requires #token("true","Bool") ensures #token("true","Bool")
    // An anywhere rule rewrites its left-hand side in place wherever that term occurs, so its
    // rewrite has the left-hand side's sort regardless of the production: the `#RuleContent`
    // node bounds its rewrite child by the sort of `foo()`, and the rewrite is instantiated at
    // Foo, as the portable engine's anywhere bound already does.
    // Host ratchet runs 16 to 26 (issue-2909-allow-anywhere-haskell/llvm, kompile step): the Z3
    // engine bounded only the rewrite's right-hand side by the anywhere left-hand side and left
    // the #KRewrite parameter at the seed's K, while the portable engine bound the rewrite itself
    // by the left-hand side's sort (Foo); checked inference
    // (`every_rule_test_passes_under_checked_inference`) reruns this test.
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
fn reference_anywhere_rule_over_a_token_is_instantiated_at_the_token_sort() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --type-inference-mode checked --allow-anywhere-haskell -w none --output-definition ref-kompiled (regression-new/issue-2909-allow-anywhere-haskell/check, verbatim, exit 0; with -w2e -w all the same kompile exits 113 at the later `Removed anywhere rule for Haskell backend execution` check, after parsing)
    // parsed.txt: rule #token("1","Int")=>#token("2","Int") requires #token("true","Bool") ensures #token("true","Bool") [anywhere, ...]
    // The left-hand side is the token `1` itself, an application of its token production, so
    // the rewrite of an anywhere rule is bounded by the token's sort.
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
fn reference_nullary_function_with_a_parametric_instance_result_sort_parses_bare() {
    // reference: k/result/bin/kompile test.k --backend llvm --main-module TEST --syntax-module TEST (regression-new/mint-llvm-2, exit 0)
    // parsed.txt: rule `m64()_TEST_MInt`(.KList)=>#token("0p64","MInt{64}") requires #token("true","Bool") ensures #token("true","Bool")
    //             rule `m32()_TEST_MInt`(.KList)=>#token("0p32","MInt{32}") requires #token("true","Bool") ensures #token("true","Bool")
    // `syntax MInt{64} ::= m64() [function]` declares no sort parameter: its sort is the fixed
    // instance `MInt{64}`, so no parameter selects a member of the `MInt` family and inference
    // wraps the application in no cast. The function stays at the top of the left-hand side,
    // where a function rule must have it.
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
    let diagnostics = k_rust::definition::check_definition(loaded.resolved())
        .expect("definition checks run on the loaded definition");
    assert!(
        diagnostics.iter().all(|diagnostic| diagnostic.code
            != k_rust::diagnostic::DiagnosticCode::IllegalFunctionOnLhs),
        "{diagnostics:?}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_parametric_result_in_a_placeholder_slot_infers_the_declared_width() {
    // reference: k/result/bin/kompile test.k --backend haskell --main-module TEST --syntax-module TEST --output-definition ref-kompiled (exit 0)
    // parsed.txt: rule `testBytesGet_TEST_Bool`(.KList)=>`_andBool_`(#SemanticCastToBool(`_==MInt__MINT_Bool_MInt_MInt`{64}(`project:MInt{64}`(`#SemanticCastToMInt{64}`(`_[_]_BYTES-HOOKED_MInt_Bytes_MInt`(`bytesString2_TEST_Bytes`(.KList),#token("2p64","MInt{64}")))),`#SemanticCastToMInt{64}`(`Int2MInt(_)_MINT_MInt_Int`{64}(`_[_]_BYTES-HOOKED_Int_Bytes_Int`(`bytesString2_TEST_Bytes`(.KList),#token("2","Int")))))),#SemanticCastToBool(`_==MInt__MINT_Bool_MInt_MInt`{256}(`project:MInt{256}`(`#SemanticCastToMInt{256}`(`_[_]_BYTES-HOOKED_MInt_Bytes_MInt`(`bytesString2_TEST_Bytes`(.KList),#token("2p256","MInt{256}")))),`#SemanticCastToMInt{256}`(`Int2MInt(_)_MINT_MInt_Int`{256}(`_[_]_BYTES-HOOKED_Int_Bytes_Int`(`bytesString2_TEST_Bytes`(.KList),#token("2","Int"))))))) requires #token("true","Bool") ensures #token("true","Bool")
    //             rule `testBytesGetBare_TEST_Bool`(.KList)=>#SemanticCastToBool(`_==MInt__MINT_Bool_MInt_MInt`(`#SemanticCastToMInt{64}`(`_[_]_BYTES-HOOKED_MInt_Bytes_MInt`(`bytesString2_TEST_Bytes`(.KList),#token("2p64","MInt{64}"))),#token("0p64","MInt{64}"))) requires #token("true","Bool") ensures #token("true","Bool")
    // The rule grammar instantiates `{Width} Bool ::= MInt{Width} "==MInt" MInt{Width}` with the
    // placeholder `MInt{K}` and bridges it with `MInt{K} ::= MInt{64}` so the parser accepts a
    // width-64 argument there. The bridge is a parsing device, not a subsort: an `MInt{64}`
    // value is no value of another width, so the subsort order inference reads has no
    // `MInt{64} <= MInt{K}` pair, and the widths of `bytesString2[2p64]` and `Int2MInt(...)` are
    // forced to the declared instance the token or cast anchors, never to `K`. The loaded rule
    // carries no label parameter; sort injection instantiates each symbol's `{SortWidth}` from
    // its arguments and position.
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
            "`testBytesGet_TEST_Bool`(.KList)=>`_andBool_`(#SemanticCastToBool(`_==MInt__MINT_Bool_MInt_MInt`(`project:MInt{64}`(`#SemanticCastToMInt{64}`(`_[_]_BYTES-HOOKED_MInt_Bytes_MInt`(`bytesString2_TEST_Bytes`(.KList),#token(\"2p64\",\"MInt{64}\")))),`#SemanticCastToMInt{64}`(`Int2MInt(_)_MINT_MInt_Int`(`_[_]_BYTES-HOOKED_Int_Bytes_Int`(`bytesString2_TEST_Bytes`(.KList),#token(\"2\",\"Int\")))))),#SemanticCastToBool(`_==MInt__MINT_Bool_MInt_MInt`(`project:MInt{256}`(`#SemanticCastToMInt{256}`(`_[_]_BYTES-HOOKED_MInt_Bytes_MInt`(`bytesString2_TEST_Bytes`(.KList),#token(\"2p256\",\"MInt{256}\")))),`#SemanticCastToMInt{256}`(`Int2MInt(_)_MINT_MInt_Int`(`_[_]_BYTES-HOOKED_Int_Bytes_Int`(`bytesString2_TEST_Bytes`(.KList),#token(\"2\",\"Int\"))))))) requires #token(\"true\",\"Bool\")",
            "`testBytesGetBare_TEST_Bool`(.KList)=>#SemanticCastToBool(`_==MInt__MINT_Bool_MInt_MInt`(`#SemanticCastToMInt{64}`(`_[_]_BYTES-HOOKED_MInt_Bytes_MInt`(`bytesString2_TEST_Bytes`(.KList),#token(\"2p64\",\"MInt{64}\"))),#token(\"0p64\",\"MInt{64}\"))) requires #token(\"true\",\"Bool\")",
        ]
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn a_declared_mint_k_keeps_its_subsorts_while_the_bridges_stay_recognition_only() {
    // `syntax MInt{K}` declares the spelling the rule grammar also uses for the slot of an
    // `MInt` whose width has no parse-time value. The declared instance is a defined sort, so
    // its unary productions state inclusions: the generated `KItem ::= MInt{K}`, which
    // `g(X) => f(X)` needs, and the definition's `Thing ::= MInt{K}`, which
    // `g(B:MInt{K}) => t(B)` needs. The bridge `MInt{K} ::= MInt{64}` only lets an `MInt{64}` be
    // recognized at that slot; `MInt{64}` and `MInt{K}` are different instances of `MInt`, so
    // `h(X) => f(X)` is still rejected.
    let definition = |sentences: &str| {
        format!(
            "module TEST\n  imports INT\n  imports MINT\n  imports BOOL\n  syntax MInt{{64}}\n  \
             syntax MInt{{K}}\n  syntax Bool ::= f(MInt{{K}}) [function]\n  \
             rule f(_) => true\n{sentences}endmodule\n"
        )
    };
    // Parametric sorts in rules need the Z3 engine; the portable build reports
    // `Z3InferenceRequired` for them.
    let load = |sentences: &str| load_with_prelude(&definition(sentences), "test.k", "TEST");

    // Only the generated `KItem ::= MInt{K}` relates `MInt{K}` to `KItem` here.
    load(indoc! {"
        syntax Bool ::= g(KItem) [function]
        rule g(X) => f(X)
    "})
    .expect("MInt{K} <= KItem holds for the declared instance MInt{K}");

    load(indoc! {r#"
        syntax Thing ::= MInt{K} | "thing"
        syntax Bool ::= g(KItem) [function] | t(Thing) [function]
        rule t(_) => true
        rule g(B:MInt{K}) => t(B)
    "#})
    .expect("MInt{K} <= Thing holds for the declared instance MInt{K}");

    let Err(error) = load(indoc! {"
        syntax Bool ::= h(MInt{64}) [function]
        rule h(X) => f(X)
    "}) else {
        panic!("MInt{{64}} <= MInt{{K}} must not hold through the recognition bridge");
    };
    let message = error.to_string();
    assert!(message.contains("Unexpected sort MInt{64}"), "{message}");
    assert!(message.contains("Expected: MInt{K}"), "{message}");
}

#[cfg(feature = "z3-inference")]
#[test]
fn a_definition_production_shaped_like_a_recognition_bridge_keeps_its_subsort() {
    // `syntax MInt{K} ::= MInt{Foo}` is the definition's own unary production between two
    // declared instances, so it states `MInt{Foo} <= MInt{K}`. The grammar also adds the
    // recognition bridge `MInt{K} ::= MInt{Foo}` for the declared instance `MInt{Foo}`, with the
    // same shape. Only that bridge is recognition-only, so `h(X) => f(X)` is well sorted through
    // the definition's own production.
    let module = |own_production: &str| {
        format!(
            r#"module TEST
              imports SORT-K
              syntax MInt{{Foo}}
              syntax MInt{{K}}
              {own_production}
              syntax MInt{{Foo}} ::= "a"
              syntax Foo ::= "foo"
              syntax Foo ::= f(MInt{{K}}) [function]
              rule f(_) => foo
              syntax Foo ::= h(MInt{{Foo}}) [function]
              rule h(X) => f(X)
            endmodule
            "#
        )
    };
    load_with_prelude(&module("syntax MInt{K} ::= MInt{Foo}"), "test.k", "TEST")
        .expect("the definition's MInt{Foo} <= MInt{K} holds");

    // Without the definition's own production, only the recognition bridge relates the two
    // instances, and it states no subsort.
    let Err(error) = load_with_prelude(&module(""), "test.k", "TEST") else {
        panic!("MInt{{Foo}} <= MInt{{K}} must not hold through the recognition bridge alone");
    };
    let message = error.to_string();
    assert!(message.contains("Unexpected sort MInt{Foo}"), "{message}");
    assert!(message.contains("Expected: MInt{K}"), "{message}");
}

#[test]
fn nested_and_other_arity_parametric_sorts_are_rejected_at_load() {
    let messages = |source: &str| {
        let Err(k_rust::outer::LoadError::SourceDiagnostics(diagnostics)) =
            load_with_prelude(source, "test.k", "TEST")
        else {
            panic!("the parametric sorts of the definition must be rejected at load");
        };
        diagnostics
            .into_iter()
            .map(|diagnostic| diagnostic.message)
            .collect::<Vec<_>>()
    };

    let nested = messages(
        "module TEST\n  imports INT\n  imports MINT-SYNTAX\n  syntax MInt{8}\n  syntax {W} MInt{MInt{W}} ::= nest(x: Int, y: Int)\nendmodule\n",
    );
    assert!(
        nested
            .iter()
            .any(|message| message
                == "Nested parametric sorts are currently unsupported: MInt{MInt{W}}"),
        "{nested:#?}"
    );

    let other_arity = messages(
        "module TEST\n  imports INT\n  syntax Foo ::= \"g\"\n  syntax {A, B} MInt{A, B}\n  syntax MInt{8, 16}\n  syntax {A, B} Foo ::= pair(x: MInt{A, B}, y: Int) [function]\nendmodule\n",
    );
    for expected in [
        "User-defined parametric sorts are currently unsupported: MInt{A,B}",
        "User-defined parametric sorts are currently unsupported: MInt{8,16}",
    ] {
        assert!(
            other_arity.iter().any(|message| message == expected),
            "{expected}: {other_arity:#?}"
        );
    }
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
            .definition()
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|s| {
                if let Sentence::Claim { body, .. } = &**s {
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
        assert!(!loaded.definition().main_module().unwrap().local_sentences.iter().any(|s| {
            matches!(&**s, Sentence::Production { sort, .. } if sort.name == "GeneratedCounterCell")
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

// Argument-position rewrites. Each snapshot is shared by the portable and the z3-inference
// builds, so the two parses must resolve to the same rule sentence.
macro_rules! argument_rewrite_snapshot {
    ($name:ident, $rule:expr) => {
        #[test]
        fn $name() {
            let source = format!(
                indoc! {r#"
                    module MAIN
                      syntax Int ::= r"[0-9]+" [token]
                      syntax Exp ::= Int | bar(Exp) [symbol(bar)]
                      syntax KItem ::= foo(Int) [symbol(foo)]
                      syntax List ::= ListItem(KItem) [symbol(ListItem)]
                                    | List List [symbol(_List_)]
                                    | ".List" [symbol(.List)]
                      syntax KCell ::= "<k>" K "</k>" [cell]
                      rule {}
                    endmodule
                "#},
                $rule
            );
            assert_rule_resolution_snapshot!(source.as_str());
        }
    };
}

argument_rewrite_snapshot!(argument_rewrite_of_constants, "foo(0 => 1)");
argument_rewrite_snapshot!(argument_rewrite_of_an_unsorted_variable, "foo(I => 0)");
argument_rewrite_snapshot!(argument_rewrite_of_a_cast_variable, "foo(I:Int => 0)");
argument_rewrite_snapshot!(argument_rewrite_inside_a_cell, "<k> foo(I:Int => 0) </k>");
argument_rewrite_snapshot!(
    argument_rewrite_inside_a_nested_application,
    "ListItem(foo(I:Int => 0))"
);
argument_rewrite_snapshot!(argument_rewrite_at_a_supersort_position, "bar(X => 1)");

// Rewrites directly at a declared `KItem` argument position (`ListItem`, `SetItem`, a user
// `KItem` argument). Shared by both builds like the snapshots above.
macro_rules! kitem_argument_rewrite_snapshot {
    ($name:ident, $rule:expr) => {
        #[test]
        fn $name() {
            let source = format!(
                indoc! {r#"
                    module MAIN
                      syntax Int ::= r"[0-9]+" [token]
                      syntax KItem ::= foo(Int) [symbol(foo)]
                      syntax KItem ::= wrap(KItem) [symbol(wrap)]
                      syntax List ::= ListItem(KItem) [symbol(ListItem)]
                                    | List List [symbol(_List_)]
                                    | ".List" [symbol(.List)]
                      syntax Set ::= SetItem(KItem) [symbol(SetItem)]
                      rule {}
                    endmodule
                "#},
                $rule
            );
            assert_rule_resolution_snapshot!(source.as_str());
        }
    };
}

kitem_argument_rewrite_snapshot!(
    kitem_argument_rewrite_of_applications,
    "ListItem(foo(0) => foo(1))"
);
kitem_argument_rewrite_snapshot!(
    kitem_argument_rewrite_of_a_variable,
    "ListItem(X => foo(1))"
);
kitem_argument_rewrite_snapshot!(
    kitem_argument_rewrite_at_a_user_production,
    "wrap(foo(0) => foo(1))"
);
kitem_argument_rewrite_snapshot!(
    kitem_argument_rewrite_in_a_set_element,
    "SetItem(foo(0) => foo(1))"
);
// Sides of a concrete sort: the only derivation is the `KItem` rewrite over the `KItem ::= Int`
// subsort, because unlabeled chains are not widened, so no sort has to be chosen.
kitem_argument_rewrite_snapshot!(
    kitem_argument_rewrite_of_concrete_sides,
    "ListItem(I:Int => 0)"
);

// A parenthesized rewrite at a `KItem` position has one derivation per bracket that reaches it
// (the `Int` bracket under the `KItem ::= Int` subsort and the `KItem` bracket), which are
// rewrites of different sorts. The forest is ambiguous but monomorphic, so sort inference
// decides it in either build, and both builds give one rule.
#[test]
fn kitem_argument_rewrite_inside_a_bracket_is_decided_by_sort_inference() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax List ::= ListItem(KItem) [symbol(ListItem)]
          rule ListItem((0 => 1))
        endmodule
    "#};
    assert_rule_resolution_snapshot!(source);
}

// A parenthesized rewrite has one derivation per bracket that reaches its position: here the
// `Int` bracket under `foo` and the `K` bracket under the `foo(...)` label application, which
// are distinct rewrites (of sort `Int` and of sort `K`). The forest is ambiguous but
// monomorphic, so sort inference decides it in either build, and both builds give one rule.
#[test]
fn argument_rewrite_inside_a_bracket_is_decided_by_sort_inference() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax KItem ::= foo(Int) [symbol(foo)]
          rule foo((I:Int => 0))
        endmodule
    "#};
    assert_rule_resolution_snapshot!(source);
}

#[test]
fn argument_rewrite_does_not_lift_a_rewrite_into_a_rewrite_operand() {
    // `(0 => 1) => 2` at an Int position has a derivation only through the bracket, and the
    // rewrite check rejects the nested rewrite after parsing in either build.
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax KItem ::= foo(Int) [symbol(foo)]
          rule foo(0 => 1 => 2)
        endmodule
    "#};
    // Without inference the operands of `S => S` are plain `S`, so the chain has no derivation;
    // with inference the non-associative rewrite rejects it.
    let error = resolve_rule_bubbles(&lowered(source)).unwrap_err();
    #[cfg(not(feature = "z3-inference"))]
    assert!(
        matches!(error, RuleError::Parse(ref error) if matches!(error.error, ParseError::NoParse { .. })),
        "{error:?}"
    );
    #[cfg(feature = "z3-inference")]
    assert!(
        matches!(error, RuleError::Parse(ref error)
            if matches!(error.error, ParseError::Associativity { ref parent, ref child, .. }
                if parent == "#KRewrite" && child == "#KRewrite")),
        "{error:?}"
    );
    let nested = resolve_rule_bubbles(&lowered(&source.replace("0 => 1 => 2", "(0 => 1) => 2")))
        .expect("a bracketed rewrite operand parses");
    let diagnostics = k_rust::definition::check_rewrites(
        &nested
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .map(|sentence| &**sentence)
            .collect::<Vec<_>>(),
    );
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message == "Rewrites are not allowed to be nested."),
        "{diagnostics:?}"
    );
}

/// The embedded prelude with every rule-like bubble removed except those of `kept` modules, so
/// that their rules are parsed with the grammar of their full import closure while the rules
/// of other prelude modules, some of which need Z3 sort inference, are not parsed at all.
fn prelude_with_rules_only_in(kept: &[&str]) -> k_rust::definition::Definition {
    let mut combined: Option<k_rust::outer::SourceFile> = None;
    for name in ["prelude.md", "kast.md", "domains.md"] {
        let text = k_rust::builtin::embedded(name).unwrap().text;
        let code = k_rust::outer::extract_fenced_k_code(&text, "k").unwrap();
        let file = k_rust::outer::parse(name, &code).unwrap();
        match &mut combined {
            Some(combined) => combined.modules.extend(file.modules),
            None => combined = Some(file),
        }
    }
    let mut combined = combined.unwrap();
    combined.requires.clear();
    let main = format!(
        "module KEPT-RULES\n{}endmodule\n",
        kept.iter()
            .map(|module| format!("  imports {module}\n"))
            .collect::<String>()
    );
    combined
        .modules
        .extend(k_rust::outer::parse("kept.k", &main).unwrap().modules);
    let mut definition = k_rust::outer::lower(&combined, "KEPT-RULES").unwrap();
    for module in &mut definition.modules {
        if kept.contains(&module.name.as_str()) {
            continue;
        }
        module.local_sentences.retain(|sentence| {
            !matches!(&**sentence, Sentence::Bubble { sentence_type, .. } if sentence_type != "config")
        });
    }
    definition
}

fn assert_stream_rules_snapshot(excluded: &str) {
    const STREAMS: [&str; 2] = ["STDIN-STREAM", "STDOUT-STREAM"];
    let loaded = k_rust::outer::load_structured(
        prelude_with_rules_only_in(&STREAMS),
        &LoadOptions {
            excluded_module_attributes: vec![excluded.into()],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("stream rules should parse with {excluded} excluded: {error}"));
    let rules = STREAMS
        .iter()
        .flat_map(|name| {
            loaded
                .definition()
                .modules
                .iter()
                .find(|module| module.name == *name)
                .unwrap()
                .local_sentences
                .iter()
                .filter_map(|sentence| sentence_summary(sentence))
        })
        .collect::<Vec<_>>();
    for name in STREAMS {
        let module = loaded
            .definition()
            .modules
            .iter()
            .find(|module| module.name == name)
            .unwrap();
        assert!(
            !module
                .local_sentences
                .iter()
                .any(|sentence| matches!(&**sentence, Sentence::Bubble { .. })),
            "{name} retains an unparsed bubble"
        );
    }
    insta::with_settings!({
        description => format!("STDIN-STREAM and STDOUT-STREAM rules of the embedded prelude, {excluded} excluded"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
        snapshot_suffix => excluded,
    }, {
        insta::assert_debug_snapshot!("prelude_stream_rules", rules);
    });
}

#[test]
fn prelude_stream_rules_parse_with_argument_position_rewrites() {
    assert_stream_rules_snapshot("concrete");
    assert_stream_rules_snapshot("symbolic");
}

/// A strict cast (`t::S`, `{t}::S`) fixes the sort of its inner term to exactly `S`. Both
/// inference engines must implement that one relation, so a strict cast whose inner term has a
/// proper subsort of the cast sort is ill-sorted in either build, and a cast at the term's own
/// sort still selects the same term.
fn strict_cast_source(rule: &str) -> String {
    format!(
        "module MAIN\n  syntax K\n  syntax A ::= B\n  syntax B ::= \"b\"\n  syntax B ::= g(KItem)\n  syntax KItem ::= f(A)\n  rule {rule}\nendmodule\n"
    )
}

fn strict_cast_rule_bodies(rule: &str) -> Result<Vec<String>, RuleError> {
    let resolved = resolve_rule_bubbles(&lowered(&strict_cast_source(rule)))?;
    Ok(resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .collect())
}

#[test]
fn strict_cast_rejects_an_inner_term_of_a_proper_subsort() {
    for rule in ["f({b}::A) => .K", "f(b::A) => .K", "f({g(X)}::A) => .K"] {
        let result = strict_cast_rule_bodies(rule);
        assert!(
            matches!(
                result,
                Err(RuleError::Parse(ref error))
                    if matches!(error.error, ParseError::SortInference { .. })
            ),
            "`rule {rule}` casts a B-sorted term to its proper supersort A: {result:?}"
        );
    }
}

#[test]
fn strict_cast_at_the_inner_terms_own_sort_selects_the_same_term() {
    for (rule, body) in [
        (
            "f({b}::B) => .K",
            "`f(_)_MAIN_KItem_A`(`b_MAIN_B`(.KList))=>.K",
        ),
        (
            "f({g(X)}::B) => .K",
            "`f(_)_MAIN_KItem_A`(`g(_)_MAIN_B_KItem`(#SemanticCastToKItem(X)))=>.K",
        ),
        (
            "f(X::A) => .K",
            "`f(_)_MAIN_KItem_A`(#SemanticCastToA(X))=>.K",
        ),
        // `#token(_,_)` and `#klabel(_)` have the synthetic bottom sort, which says nothing
        // about the term's sort; the cast is the only statement of it and is not contradicted.
        (
            r#"f(#token("b","B")::B) => .K"#,
            r#"`f(_)_MAIN_KItem_A`(#token("b","B"))=>.K"#,
        ),
        (
            r#"f({#token("b","B")}::A) => .K"#,
            r#"`f(_)_MAIN_KItem_A`(#token("b","B"))=>.K"#,
        ),
        (
            "f({#klabel(`g(_)_MAIN_B_KItem`)}::A) => .K",
            r#"`f(_)_MAIN_KItem_A`(#WrappedKLabel(#token("`g(_)_MAIN_B_KItem`","KLabel")))=>.K"#,
        ),
    ] {
        assert_eq!(
            strict_cast_rule_bodies(rule).unwrap(),
            [body],
            "`rule {rule}`"
        );
    }
}

// Ambiguous monomorphic forests decided by the maximal typings of their trees. One reduced
// fixture per class of ambiguity the embedded prelude has; each snapshot is recorded by the
// z3-inference build and asserted unchanged by the portable build, and each fixture reruns
// under checked mode, which compares the lowered results of both engines.

rule_snapshot!(
    ambiguity_class_lookup_eliminated_by_the_variable_sort,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax List ::= ".List" [symbol(.List)]
          syntax Array ::= arr(List) [symbol(arr)]
          syntax KItem ::= List "[" Int "]" [function, symbol(List:get)]
          syntax KItem ::= Array "[" Int "]" [function, symbol(Array:get)]
          rule arr(L)[I] => L[I]
        endmodule
    "#
);

rule_snapshot!(
    ambiguity_class_overload_with_one_well_sorted_alternative,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Endianness ::= "LE" [symbol(LE)] | "BE" [symbol(BE)]
          syntax Signedness ::= "Signed" [symbol(Signed)] | "Unsigned" [symbol(Unsigned)]
          syntax Bytes ::= Int2Bytes(Int, Int, Endianness) [function, symbol(Int2Bytes)]
                         | Int2Bytes(Int, Endianness, Signedness) [function, symbol(Int2BytesNoLen)]
          rule Int2Bytes(I, E, Unsigned) => Int2Bytes(0, I, E)
        endmodule
    "#
);

rule_snapshot!(
    ambiguity_class_brackets_lowering_to_one_term,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Int ::= "(" Int ")" [bracket]
          syntax Bool ::= "true" [token]
          syntax Bool ::= "(" Bool ")" [bracket]
          syntax Bool ::= Int "dividesInt" Int [function, symbol(dividesInt)]
          rule (I1:Int dividesInt I2:Int) => true
        endmodule
    "#
);

rule_snapshot!(
    ambiguity_class_grouping_decided_by_the_maximal_typing,
    r#"
        module MAIN
          syntax Bool ::= "true" [token]
          syntax Map ::= Map "[" KItem "<-" KItem "]" [function, symbol(Map:update)]
          syntax Bool ::= K "==K" K [function, symbol(_==K_)]
          syntax Bool ::= Bool "orBool" Bool [function, left, symbol(_orBool_)]
          syntax Bool ::= KItem "in_keys" "(" Map ")" [function, symbol(in_keys)]
          rule K1 in_keys(M [ K2 <- _ ]) => true requires K1 ==K K2 orBool K1 in_keys(M)
        endmodule
    "#
);

rule_snapshot!(
    ambiguity_class_overload_decided_by_a_strict_cast,
    r#"
        module MAIN
          syntax String ::= r"[a-z]+" [token]
          syntax String ::= String "+String" String [function, symbol(_+String__STRING-COMMON)]
          syntax StringBuffer ::= StringBuffer "+String" String [function, avoid, symbol(_+String__STRING-BUFFER-IN-K)]
          syntax StringBuffer ::= String
          rule {SB:String +String S:String}::StringBuffer => (SB +String S)::String
        endmodule
    "#
);

// `prefer`/`avoid` between maximal trees that diverge at several positions (the frontier step of
// the post-inference filter). Reduced from pl-tutorial kool-typed-static.md:358, `rule
// (T[])[int, Ts:Types] => T[Ts]`: `Type ::= Id [symbol(class)]` is a constructor, not a subsort,
// so `T:Type` and `T:Id` (under `class`) are both maximal typings. The two trees share the
// rewrite and differ at the left-hand `_[]` argument and at the right-hand `arrayRef` argument.

fn class_constructor_source(attribute: &str) -> String {
    format!(
        r#"
        module MAIN
          syntax Id ::= r"[A-Z][a-zA-Z]*" [token]
          syntax Type ::= "int"
                        | Id [symbol(class){attribute}]
                        | Type "[" "]"
                        | "(" Type ")" [bracket]
          syntax Types ::= List{{Type,","}} [overload(exps)]
          syntax Exp ::= Id | Type
          syntax Exps ::= List{{Exp,","}} [overload(exps)]
          syntax Exps ::= Types
          syntax Exp ::= Exp "[" Exps "]" [symbol(arrayRef)]
          rule (T[])[int, Ts:Types] => T[Ts]
        endmodule
    "#
    )
}

fn resolved_rule_body(source: &str) -> Result<String, RuleError> {
    let resolved = resolve_rule_bubbles(&lowered(source))?;
    let bodies = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => Some(body.to_string()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [body] = bodies.as_slice() else {
        panic!("expected one rule, got {bodies:?}")
    };
    Ok(body.clone())
}

/// Assert that `result` is an ambiguity whose readings differ at subterms with these readings,
/// one entry per root key each.
fn assert_ambiguous_at<const N: usize>(result: Result<String, RuleError>, places: [&[&str]; N]) {
    let Err(RuleError::Parse(error)) = &result else {
        panic!("expected an ambiguity, got {result:?}")
    };
    let ParseError::Ambiguous {
        alternatives,
        places: reported,
        ..
    } = &error.error
    else {
        panic!("expected an ambiguity, got {:?}", error.error)
    };
    assert!(alternatives.is_empty(), "{alternatives:#?}");
    assert_eq!(
        reported
            .iter()
            .map(|place| place
                .alternatives
                .iter()
                .map(|alternative| alternative.term.as_str())
                .collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        places.map(<[&str]>::to_vec),
        "{reported:#?}"
    );
}

fn assert_ambiguous_between<const N: usize>(
    result: Result<String, RuleError>,
    readings: [&str; N],
) {
    let Err(RuleError::Parse(error)) = &result else {
        panic!("expected an ambiguity, got {result:?}")
    };
    let ParseError::Ambiguous { alternatives, .. } = &error.error else {
        panic!("expected an ambiguity, got {:?}", error.error)
    };
    assert_eq!(alternatives.len(), N, "{alternatives:#?}");
    let mut terms = alternatives
        .iter()
        .map(|alternative| alternative.term.as_str())
        .collect::<Vec<_>>();
    terms.sort_unstable();
    let mut readings = readings;
    readings.sort_unstable();
    assert_eq!(terms, readings);
}

const CLASS_TYPE_READING: &str = "arrayRef(`_[]_MAIN_Type_Type`(#SemanticCastToType(T)),`_,__MAIN_Types_Type_Types`(`int_MAIN_Type`(.KList),#SemanticCastToTypes(Ts)))=>arrayRef(#SemanticCastToType(T),#SemanticCastToTypes(Ts))";
const CLASS_ID_READING: &str = "arrayRef(`_[]_MAIN_Type_Type`(class(#SemanticCastToId(T))),`_,__MAIN_Types_Type_Types`(`int_MAIN_Type`(.KList),#SemanticCastToTypes(Ts)))=>arrayRef(class(#SemanticCastToId(T)),#SemanticCastToTypes(Ts))";

#[test]
fn avoided_constructor_at_one_of_two_divergence_points_is_dropped() {
    let body = resolved_rule_body(&class_constructor_source(", avoid"))
        .expect("avoid on class decides between the two maximal trees");
    assert!(!body.contains("class("), "{body}");
    assert_eq!(body, CLASS_TYPE_READING);
}

// Both engines rank maximal typings in the subsort order, where `Id` and `Type` are
// incomparable, so without an attribute nothing decides and `prefer` keeps the `class` reading.
//
// Without an attribute nothing decides. Inside the `T:Id` tree the right-hand `T` is an `Exp`
// either through `Exp ::= Id` or as `class(T)` through `Exp ::= Type`.
#[test]
fn constructor_without_prefer_or_avoid_leaves_two_maximal_trees_ambiguous() {
    // The `Type` typing of `T` has one reading. The `Id` typing has two, which differ on the
    // right side only. The readings differ at the left `T`, read as a `Type` or as `class` of
    // an `Id`, and at the right one, read in those two ways or as an `Id`.
    assert_ambiguous_at(
        resolved_rule_body(&class_constructor_source("")),
        [
            &["#SemanticCastToType(T)", "class(#SemanticCastToId(T))"],
            &[
                "#SemanticCastToId(T)",
                "#SemanticCastToType(T)",
                "class(#SemanticCastToId(T))",
            ],
        ],
    );
}

#[test]
fn preferred_constructor_at_one_of_two_divergence_points_is_kept() {
    let body = resolved_rule_body(&class_constructor_source(", prefer"))
        .expect("prefer on class decides between the two maximal trees");
    assert_eq!(body, CLASS_ID_READING);
}

// `f : A ::= B` and `g : B ::= A` are a legal pair of constructors: they make the chain relation
// cyclic but add nothing to the subsort order, which stays acyclic. They are not a
// `CircularSubsorts` error, so a rule elsewhere in the grammar is inferred: `q Y` has the
// incomparable maximal typings `Y:C` and `Y:D`.
fn constructor_cycle_source(rule: &str) -> String {
    format!(
        r#"
        module MAIN
          syntax A ::= "a" | B [symbol(f)]
          syntax B ::= "b" | A [symbol(g)]
          syntax R ::= "p" A [symbol(pa)]
                     | "p" B [symbol(pb)]
          syntax C ::= "c"
          syntax D ::= "d"
          syntax S ::= "q" C [symbol(qc)]
                     | "q" D [symbol(qd)]
          rule {rule}
        endmodule
    "#
    )
}

#[test]
fn constructor_cycle_leaves_an_ambiguous_rule_to_inference() {
    assert_ambiguous_between(
        resolved_rule_body(&constructor_cycle_source("q Y => .K")),
        ["qc(#SemanticCastToC(Y))", "qd(#SemanticCastToD(Y))"],
    );
}

// A rule over the cycle's own sorts is not reached by inference: `p X` has the readings
// `pa(X)`, `pa(f(X))`, `pa(f(g(X)))`, and so on without end, and the parser reports that
// forest as cyclic.
#[test]
fn constructor_cycle_makes_a_rule_over_its_sorts_a_cyclic_forest() {
    let result = resolved_rule_body(&constructor_cycle_source("p X => .K"));
    let Err(RuleError::Parse(error)) = &result else {
        panic!("expected a parse error, got {result:?}")
    };
    let ParseError::CyclicDerivation(cycle) = &error.error else {
        panic!("expected a cyclic derivation, got {:?}", error.error);
    };
    assert_eq!(cycle.sort, Sort::new("B"));
    assert_eq!(cycle.empty, Vec::<String>::new());
    assert_eq!(cycle.productions.len(), 2);
    assert!(
        cycle
            .productions
            .iter()
            .any(|text| text.contains("syntax A ::= B"))
    );
    assert!(
        cycle
            .productions
            .iter()
            .any(|text| text.contains("syntax B ::= A"))
    );
    assert!(cycle.span.is_some());
    let message = error.error.to_string();
    assert!(
        message.contains("`X` has infinitely many parses"),
        "{message}"
    );
    assert!(message.contains("syntax A ::= B"), "{message}");
    assert!(message.contains("syntax B ::= A"), "{message}");
    assert!(!message.contains("where "), "{message}");
}

#[test]
fn unary_cycle_message_names_its_productions_and_location() {
    let error = resolved_rule_body(&constructor_cycle_source("p X => .K")).unwrap_err();
    let RuleError::Parse(parse) = &error else {
        panic!("expected a parse error, got {error:?}");
    };
    assert!(parse.location.is_some());
    let message = error.to_string();
    assert!(message.starts_with("rules.k:"), "{message}");
    assert!(message.contains("syntax B ::= A [symbol(g)]"), "{message}");
    assert!(message.contains("syntax A ::= B [symbol(f)]"), "{message}");
    assert!(!message.contains("where "), "{message}");
}

// `wrap : Exp ::= Opt Exp Opt` with a nullable `Opt` derives `Exp` from `Exp` over the same text,
// so every `Exp` has infinitely many parses. The parser reports the repetition at the first rule
// instead of building ever deeper wrappers.
#[cfg(feature = "z3-inference")]
#[test]
fn a_nullable_wrapper_makes_a_rule_over_its_sort_a_cyclic_derivation() {
    let source = indoc! {r#"
        module NULL1
          imports INT
          syntax Opt ::= "" [klabel(none), symbol] | "q" [klabel(someq), symbol]
          syntax Exp ::= Int | Opt Exp Opt [klabel(wrap), symbol] | Exp "+" Exp [left, klabel(plus), symbol] | "(" Exp ")" [bracket]
          syntax KItem ::= e(Exp)
          rule e(q 1 + 2 q) => e(3)
          rule e(( 1 ) + q 2) => .K
        endmodule
    "#};
    let Err(error) = load_with_prelude(source, "null1.k", "NULL1") else {
        panic!("a rule over a cyclic sort is rejected");
    };
    let k_rust::outer::LoadError::RuleParsing(RuleError::Parse(error)) = &error else {
        panic!("expected a rule parse error, got {error:?}");
    };
    assert_eq!(
        error.error.to_string(),
        "Parsing ambiguity: `q 1` has infinitely many parses because these productions \
         derive Exp from itself without consuming input:\n    syntax Exp ::= Opt Exp Opt [klabel(wrap), symbol]\n\
         where Opt matches the empty string."
    );
    let ParseError::CyclicDerivation(cycle) = &error.error else {
        panic!("expected a cyclic derivation, got {:?}", error.error);
    };
    let span = cycle.span.expect("the cyclic text has a span");
    assert_eq!(&source[span.start..span.end].trim_end(), &"q 1");
}

// Without single-nonterminal productions both orders agree. The two readings of `a(X, Y)`
// differ at the left-hand application and at the right-hand variables' sorts.
fn two_applications_source(k_attribute: &str, int_attribute: &str) -> String {
    format!(
        r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Foo ::= "foo"
          syntax A ::= "a" "(" K "," Int ")" [symbol(aK){k_attribute}]
          syntax B ::= "a" "(" Int "," Foo ")" [symbol(aF){int_attribute}]
          rule a(X, Y) => X ~> Y
        endmodule
    "#
    )
}

const APPLICATION_K_READING: &str =
    "aK(#SemanticCastToK(X),#SemanticCastToInt(Y))=>#SemanticCastToK(X)~>#SemanticCastToInt(Y)";

#[test]
fn maximal_trees_avoided_at_every_divergence_point_stay_ambiguous() {
    assert_ambiguous_at(
        resolved_rule_body(&two_applications_source(", avoid", ", avoid")),
        [
            &[
                "aF(#SemanticCastToInt(X),#SemanticCastToFoo(Y))",
                "aK(#SemanticCastToK(X),#SemanticCastToInt(Y))",
            ],
            &["#SemanticCastToInt(X)", "#SemanticCastToK(X)"],
            &["#SemanticCastToFoo(Y)", "#SemanticCastToInt(Y)"],
        ],
    );
}

#[test]
fn maximal_tree_avoided_at_one_of_two_divergence_points_is_dropped() {
    assert_eq!(
        resolved_rule_body(&two_applications_source("", ", avoid")).unwrap(),
        APPLICATION_K_READING
    );
}

#[test]
fn a_tree_without_a_greatest_typing_keeps_an_ambiguous_forest_at_the_z3_boundary() {
    // `X` is bounded by `A` and by `B`, whose common subsorts `C1` and `C2` are incomparable,
    // so each tree of the ambiguous `a(Y)` has no greatest typing and the portable engine
    // does not choose between them.
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Foo ::= "foo"
          syntax C1 ::= "c1"
          syntax C2 ::= "c2"
          syntax A ::= C1 | C2
          syntax B ::= C1 | C2
          syntax KItem ::= f(A) [symbol(f)] | g(B) [symbol(g)]
          syntax P ::= "a" "(" Int ")" [symbol(aI)]
          syntax Q ::= "a" "(" Foo ")" [symbol(aF)]
          rule f(X) ~> g(X) ~> a(Y) => .K
        endmodule
    "#};
    let result = resolve_rule_bubbles(&lowered(source));
    #[cfg(not(feature = "z3-inference"))]
    assert!(
        matches!(
            result,
            Err(RuleError::Parse(ref error))
                if error.error == ParseError::Z3InferenceRequired {
                    ambiguity: true,
                    parametric_sorts: false,
                }
        ),
        "{result:?}"
    );
    #[cfg(feature = "z3-inference")]
    assert!(result.is_err(), "{result:?}");
}

/// Load `source` with the prelude as the rule grammar sees it and return its rule-parse error.
fn sort_parameter_rule_parse_error(source: &str) -> k_rust::inner::RuleParseError {
    match load_with_prelude_options(source, "sort-parameter.k", "MAIN", Vec::new()) {
        Err(k_rust::outer::LoadError::RuleParsing(RuleError::Parse(error))) => *error,
        Err(error) => panic!("expected a rule parse error, got {error}"),
        Ok(_) => panic!("expected a rule parse error, the definition loaded"),
    }
}

#[test]
fn a_production_sort_parameter_is_not_a_cast_sort_in_rules() {
    // `Sort1` is bound by the ML productions of ML-SYNTAX and names no sort of MAIN, so the cast
    // `X:Sort1` has no production, exactly as for the undeclared sort `Foo`.
    let module = |sort: &str| {
        format!(
            "module MAIN\n  imports ML-SYNTAX\n  imports INT\n  syntax KItem ::= g(K)\n  rule g(X:{sort}) => .K\nendmodule\n"
        )
    };
    let parameter = sort_parameter_rule_parse_error(&module("Sort1"));
    let undeclared = sort_parameter_rule_parse_error(&module("Foo"));
    assert!(
        matches!(parameter.error, ParseError::NoParse { .. }),
        "{parameter:?}"
    );
    assert_eq!(parameter.error, undeclared.error);
}

#[test]
fn a_production_sort_parameter_has_no_sort_predicate_in_rules() {
    // Without a sort `Sort1` there is no predicate `isSort1`, so the condition fails to parse
    // exactly as a predicate of the undeclared sort `Undef` does. The two names have the same
    // length, so the error positions, which follow the end of the condition, are comparable.
    let module = |sort: &str| {
        format!(
            "module MAIN\n  imports ML-SYNTAX\n  imports INT\n  imports BOOL\n  syntax Int ::= f(Int) [function]\n  rule f(X) => 1 requires is{sort}(X)\nendmodule\n"
        )
    };
    let parameter = sort_parameter_rule_parse_error(&module("Sort1"));
    let undeclared = sort_parameter_rule_parse_error(&module("Undef"));
    assert_eq!(parameter.error, undeclared.error, "{parameter:?}");
}

#[test]
fn a_declared_sort_named_like_a_sort_parameter_is_a_rule_sort() {
    let source = indoc! {r#"
        module MAIN
          imports INT
          imports BOOL
          syntax Sort ::= "s"
          syntax KItem ::= g(K)
          rule g(X:Sort) => X
        endmodule
    "#};
    let loaded = load_with_prelude_excluding(
        source,
        "declared-sort.k",
        "MAIN",
        k_rust::kompile::CompilationBackend::Rust.excluded_module_attribute(),
    )
    .expect("a declared sort Sort is a cast sort");
    let compiled = k_rust::kompile::compile_loaded_definition(
        &loaded,
        k_rust::kompile::CompileOptions::default(),
    )
    .expect("the definition compiles");
    assert!(
        compiled.definition_kore.contains("sort SortSort{} []"),
        "the compiled KORE declares SortSort"
    );
}

/// A case-1 production whose slot `MInt{W}` has no parse-time width is recognized at the
/// placeholder `MInt{K}`, which denotes no set of terms whether or not the module declares an
/// instance of `MInt`. Its unary instances (`Int ::= MInt{K}`, `Bool ::= MInt{K}`) therefore state
/// no inclusion, and a variable used at `Int` and at `Bool` is a sort error rather than a variable
/// inferred at the placeholder.
#[test]
fn a_placeholder_slot_without_a_declared_instance_states_no_subsort() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Bool ::= "true" | "false"
          syntax {W} MInt{W} [hook(MINT.MInt)]
          syntax {S, W} S ::= MInt{W}
          syntax Foo ::= f(Int, Bool) | "g"
          rule f(X, X) => g
        endmodule
    "#};
    let error =
        resolve_rule_bubbles(&lowered(source)).expect_err("X is used at two incomparable sorts");
    let message = error.to_string();
    assert!(message.contains("incompatible sort bounds"), "{message}");
    assert!(!message.contains("MInt{K}"), "{message}");
}

/// A production with sort parameters binds `W` in that sentence alone, so its named nonterminals
/// give record syntax but no field projection: a projection `x(Foo)` of sort `MInt{W}` would
/// mention `W` outside its binder. The rule grammar of a module declaring one is therefore built
/// without such a projection, and the module's rules resolve.
#[test]
fn a_production_with_sort_parameters_contributes_no_field_projection_to_the_rule_grammar() {
    let source = indoc! {r#"
        module MAIN
          syntax {W} MInt{W} [hook(MINT.MInt)]
          syntax Bar ::= "b"
          syntax {W} Foo ::= pick(x: MInt{W}, y: Bar)
          syntax Foo ::= "g"
          rule g => g
        endmodule
    "#};
    resolve_rule_bubbles(&lowered(source))
        .expect("the rule grammar has no projection of the parametric pick");
}

/// Run `f` on its own thread and return its result, panicking when it does not finish within
/// 120 seconds, so that a sort inference that never terminates fails the test instead of
/// hanging the suite. The thread of a timed-out `f` is left running; the test process ends it.
#[cfg(feature = "z3-inference")]
fn within_deadline<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    let (sender, receiver) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        // The receiver is gone only after a timeout, when the result is no longer wanted.
        let _ = sender.send(f());
    });
    match receiver.recv_timeout(std::time::Duration::from_secs(120)) {
        Ok(result) => result,
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
            panic!("sort inference did not terminate within 120 s")
        }
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
            panic!("the inference thread panicked")
        }
    }
}

/// The rule bodies of `source`, loaded with the prelude within the deadline, or the load error's
/// text.
#[cfg(feature = "z3-inference")]
fn rule_bodies_within_deadline(
    source: &'static str,
    name: &'static str,
) -> Result<Vec<String>, String> {
    within_deadline(move || {
        load_with_prelude(source, name, "TEST")
            .map(|loaded| rule_bodies(&loaded))
            .map_err(|error| error.to_string())
    })
}

#[cfg(feature = "z3-inference")]
#[test]
fn a_width_only_the_module_decides_takes_its_one_declared_instance() {
    // `W` is bound by `foo`'s production alone and nothing in the rule fixes it, so the width of
    // `X` is whatever the module's `MInt` sorts allow. The module declares one, `MInt{8}`: the
    // rule has exactly one well-sorted reading over the module's sorts.
    let source = indoc! {r#"
        module TEST
          imports INT
          imports BOOL
          imports MINT-SYNTAX
          syntax MInt{8}
          syntax {W} Foo ::= foo(MInt{W}) [symbol(foo)]
          syntax Foo ::= "g"
          rule foo(X) => g
        endmodule
    "#};
    let bodies = rule_bodies_within_deadline(source, "one-width.k")
        .expect("the one declared width is the rule's only reading");
    let [body] = bodies.as_slice() else {
        panic!("expected one rule, got {bodies:?}");
    };
    assert!(body.contains("MInt{8}"), "{body}");
    assert!(!body.contains("MInt{K}"), "{body}");
}

#[cfg(feature = "z3-inference")]
#[test]
fn a_width_without_a_declared_instance_is_rejected_naming_the_production() {
    // No `MInt` instance is a sort of the module, so no instantiation of `foo` is one either:
    // the rule has no reading, and the rejection names the production, not a sort the user never
    // wrote.
    let source = indoc! {r#"
        module TEST
          imports INT
          imports BOOL
          imports MINT-SYNTAX
          syntax {W} Foo ::= foo(MInt{W}) [symbol(foo)]
          syntax Foo ::= "g"
          rule foo(X) => g
        endmodule
    "#};
    let message = rule_bodies_within_deadline(source, "no-width.k")
        .expect_err("no instantiation of foo is a sort of the module");
    assert!(
        message.contains("No sort declared in this module instantiates MInt{W}"),
        "{message}"
    );
    assert!(message.contains("foo"), "{message}");
}

#[cfg(feature = "z3-inference")]
#[test]
fn two_declared_widths_make_a_free_width_ambiguous() {
    // Two declared instances give two well-sorted readings that no criterion orders.
    let source = indoc! {r#"
        module TEST
          imports INT
          imports BOOL
          imports MINT-SYNTAX
          syntax MInt{8}
          syntax MInt{16}
          syntax {W} Foo ::= foo(MInt{W}) [symbol(foo)]
          syntax Foo ::= "g"
          rule foo(X) => g
        endmodule
    "#};
    let alternatives = within_deadline(move || {
        let Err(error) = load_with_prelude(source, "two-widths.k", "TEST") else {
            return Err("the definition loaded".to_owned());
        };
        let k_rust::outer::LoadError::RuleParsing(RuleError::Parse(error)) = &error else {
            return Err(format!("expected a rule parse error, got {error:?}"));
        };
        let ParseError::Ambiguous { alternatives, .. } = &error.error else {
            return Err(format!(
                "expected ParseError::Ambiguous, got {:?}",
                error.error
            ));
        };
        Ok(alternatives
            .iter()
            .map(|alternative| alternative.term.clone())
            .collect::<Vec<_>>())
    })
    .expect("two declared widths are two readings");
    assert_eq!(alternatives.len(), 2, "{alternatives:#?}");
    assert!(
        alternatives.iter().any(|term| term.contains("{8}")),
        "{alternatives:#?}"
    );
    assert!(
        alternatives.iter().any(|term| term.contains("{16}")),
        "{alternatives:#?}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn a_free_width_of_a_parametric_result_takes_the_declared_instance() {
    // The widths of `bitwidthMInt` and `Int2MInt` must agree and nothing else fixes them. No
    // unknown has the instantiated sort, so it is the instantiated positions themselves that must
    // be sorts of the module: `MInt{8}` is the only one.
    let source = indoc! {r#"
        module TEST
          imports INT
          imports BOOL
          imports MINT
          syntax MInt{8}
          syntax Foo ::= "g" | h(Int)
          rule h(I) => g requires bitwidthMInt(Int2MInt(I)) ==Int 8
        endmodule
    "#};
    let texts = within_deadline(move || {
        load_with_prelude(source, "free-result.k", "TEST")
            .map(|loaded| rule_like_texts(&loaded, "free-result.k"))
            .map_err(|error| error.to_string())
    })
    .expect("the one declared width is the rule's only reading");
    let [text] = texts.as_slice() else {
        panic!("expected one rule, got {texts:?}");
    };
    assert!(text.contains("#SemanticCastToMInt{8}"), "{text}");
}

#[cfg(feature = "z3-inference")]
#[test]
fn an_overload_whose_parametric_alternative_has_no_instance_keeps_the_other() {
    // The `MInt` alternative of `foo` has no instantiation that is a sort of the module, so it is
    // a dead reading; being part of that alternative's own constraint, its instantiation
    // constrains nothing else, and the `Int` overload stays the rule's reading.
    let source = indoc! {r#"
        module TEST
          imports INT
          imports BOOL
          imports MINT-SYNTAX
          syntax {W} Foo ::= foo(MInt{W}) [symbol(foo)]
          syntax Foo ::= foo(Int) [symbol(fooInt)] | "g"
          rule foo(X) => g
        endmodule
    "#};
    let bodies =
        rule_bodies_within_deadline(source, "overload.k").expect("the Int overload is a reading");
    let [body] = bodies.as_slice() else {
        panic!("expected one rule, got {bodies:?}");
    };
    assert!(body.contains("fooInt"), "{body}");
}

#[test]
fn named_fields_of_parametric_productions_build_checked_grammars() {
    let outcomes = [
        (
            "result-parameter",
            "module TEST\n  imports BOOL-SYNTAX\n  syntax {W} MInt{W}\n  syntax A ::= \"a\"\n  syntax MInt{A} ::= ka() [function]\n  syntax {T} T ::= inner(x: MInt{T}) [function]\nendmodule\n",
        ),
        (
            "result-instance",
            "module TEST\n  imports INT\n  imports MINT-SYNTAX\n  syntax MInt{8}\n  syntax {S} MInt{S} ::= wrap(x: S) [function]\nendmodule\n",
        ),
        (
            "two-fields",
            "module TEST\n  imports INT\n  imports MINT-SYNTAX\n  syntax MInt{8}\n  syntax {S} S ::= pick(x: MInt{S}, y: Int) [function]\nendmodule\n",
        ),
    ]
    .into_iter()
    .map(|(name, source)| {
        std::panic::catch_unwind(|| load_with_prelude(source, name, "TEST").unwrap())
    })
    .collect::<Vec<_>>();
    assert!(outcomes.into_iter().all(|outcome| outcome.is_ok()));
}

#[test]
#[cfg(feature = "z3-inference")]
fn a_named_result_parameter_production_is_typed_at_the_declared_instance() {
    let source = indoc! {r#"
        module TEST
          imports BOOL-SYNTAX
          syntax {W} MInt{W}
          syntax A ::= "a"
          syntax MInt{A} ::= ka() [function]
          syntax {T} T ::= inner(x: MInt{T}) [function]
          syntax Foo ::= "g" | f(A) [function] | h() [function]
          rule h() => f(inner(ka()))
        endmodule
    "#};
    load_with_prelude(source, "named-result-parameter", "TEST").unwrap();
}

#[test]
fn fu24_token_sort_synonyms_denote_in_rules() {
    for aliases in ["syntax A = Int", "syntax B = Int syntax A = B"] {
        let source = format!(
            r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              {aliases}
              syntax Int ::= "f(" Int ")" [symbol(f)]
              rule f(_) => #token("1", "A")
            endmodule
            "#,
        );
        let definition = k_rust::definition::apply_sort_synonyms(&lowered(&source)).unwrap();
        let resolved = resolve_rule_bubbles(&definition).unwrap();
        let body = resolved
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match &**sentence {
                Sentence::Rule { body, .. } => Some(body),
                _ => None,
            })
            .unwrap();
        let Term::Rewrite { right, .. } = body.unannotated() else {
            panic!("expected a rewrite: {body}");
        };
        assert!(
            matches!(right.unannotated(), Term::Token { token, sort }
            if token == "1" && sort == &Sort::new("Int")),
            "{aliases}: {right}"
        );
    }
}

#[test]
fn fu24_token_sort_uses_privately_imported_synonyms_in_rules() {
    let source = indoc! {r#"
        module HIDDEN
          syntax P = Int
        endmodule
        module MAIN
          imports private HIDDEN
          syntax Int ::= r"[0-9]+" [token]
          syntax Int ::= "f(" Int ")" [symbol(f)]
          rule f(_) => #token("1", "P")
        endmodule
    "#};
    let definition = k_rust::definition::apply_sort_synonyms(&lowered(source)).unwrap();
    let resolved = resolve_rule_bubbles(&definition).unwrap();
    let body = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    let Term::Rewrite { right, .. } = body.unannotated() else {
        panic!("expected a rewrite: {body}");
    };
    assert!(
        matches!(right.unannotated(), Term::Token { token, sort }
        if token == "1" && sort == &Sort::new("Int")),
        "{right}"
    );
}
