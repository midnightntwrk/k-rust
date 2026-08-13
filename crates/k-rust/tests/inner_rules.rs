use indoc::indoc;
use k_rust::definition::Sentence;
use k_rust::inner::{ParseError, RuleError, resolve_rule_bubbles};
use k_rust::kast::{Sort, Term, TermSpan};
use k_rust::outer::{ResolvedSource, load};

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
    span: Option<TermSpan>,
    production: Option<usize>,
}

fn metadata_summary<'a>(term: &Term, source: &'a str, output: &mut Vec<MetadataSummary<'a>>) {
    let metadata = term.metadata();
    let span = metadata.and_then(|metadata| metadata.span);
    output.push(MetadataSummary {
        term: term.to_string(),
        source: span.and_then(|span| source.get(span.start..span.end)),
        span,
        production: metadata
            .and_then(|metadata| metadata.production)
            .map(|production| production.0),
    });
    match term.unannotated() {
        Term::Rewrite { left, right } => {
            metadata_summary(left, source, output);
            metadata_summary(right, source, output);
        }
        Term::As { pattern, alias } => {
            metadata_summary(pattern, source, output);
            metadata_summary(alias, source, output);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                metadata_summary(item, source, output);
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
    let parsed = k_rust::outer::parse("rules.k", source).unwrap();
    k_rust::outer::lower(&parsed, "MAIN").unwrap()
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
    ($name:ident, $source:expr) => {
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

          rule 1 + 2 => 3
        endmodule
    "#};
    let rule_source = "1 + 2 => 3";
    let definition = resolve_rule_bubbles(&lowered(source)).unwrap();
    let body = definition
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
    metadata_summary(body, rule_source, &mut metadata);

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(metadata);
    });
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

#[cfg(not(feature = "z3-inference"))]
fn assert_parametric_rule_requires_z3(source: &str) {
    let result = resolve_rule_bubbles(&lowered(source));
    assert!(
        matches!(
        result,
        Err(RuleError::Parse(ref error))
            if matches!(
                error.error,
                ParseError::Z3InferenceRequired {
                    ambiguity: true,
                    ..
                } | ParseError::Z3InferenceRequired {
                    parametric_sorts: true,
                    ..
                } | ParseError::Ambiguous { .. }
            )
        ),
        "expected a parametric-inference boundary, found {result:?}"
    );
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
    #[cfg(feature = "z3-inference")]
    assert_rule_resolution_snapshot!(source);
    #[cfg(not(feature = "z3-inference"))]
    assert_parametric_rule_requires_z3(source);
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
    #[cfg(feature = "z3-inference")]
    assert_rule_resolution_snapshot!(source);
    #[cfg(not(feature = "z3-inference"))]
    assert_parametric_rule_requires_z3(source);
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
          syntax Id ::= r"[a-z]" [token]
          syntax Exp ::= Id
          syntax Exp ::= Exp "*" Exp [symbol(times)]
                       > Exp "+" Exp [symbol(plus)]
          rule a + b * c => c * b + a
        endmodule
    "#
);

rule_snapshot!(
    resolves_prefix_terminals_with_the_global_scanner,
    r#"
        module MAIN
          syntax Id ::= r"[a-z]" [token]
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
          syntax Id ::= r"[a-z]" [token]
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
    brackets_shield_associativity,
    r#"
        module MAIN
          syntax Id ::= r"[a-z]" [token]
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
          syntax Id ::= r"[a-z]" [token]
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
          syntax Atom ::= r"[a-z]" [token]
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
          syntax Id ::= r"[a-z]" [token]
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
    infers_boolean_condition_variables_from_builtin_rule_syntax,
    r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          rule a => a requires B
        endmodule
    "#
);

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
          syntax Id ::= r"[a-z]" [token]
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
fn overloaded_generic_applications_require_z3_inference() {
    let source = indoc! {r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax A ::= "pa" A [symbol(pick)]
          syntax B ::= "pb" B [symbol(pick)]
          rule pick(a) => a
        endmodule
    "#};
    assert_parametric_rule_requires_z3(source);
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
          syntax Id ::= r"[a-z]" [token]
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
