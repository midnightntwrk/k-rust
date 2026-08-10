use indoc::indoc;
use k_rust::definition::Sentence;
use k_rust::inner::{ParseError, RuleError, resolve_rule_bubbles};
use k_rust::kast::Sort;
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

macro_rules! rule_snapshot {
    ($name:ident, $source:expr) => {
        #[test]
        fn $name() {
            let resolved = resolve_rule_bubbles(&lowered(indoc!($source))).unwrap();
            let sentences = resolved
                .main_module()
                .unwrap()
                .local_sentences
                .iter()
                .filter_map(sentence_summary)
                .collect::<Vec<_>>();
            insta::assert_debug_snapshot!(sentences);
        }
    };
}

#[test]
fn parses_rule_claim_context_and_alias_bubbles() {
    let definition = lowered(indoc! {r#"
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
    "#});
    let resolved = resolve_rule_bubbles(&definition).unwrap();
    let sentences = resolved
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(sentence_summary)
        .collect::<Vec<_>>();

    insta::assert_debug_snapshot!(sentences);
}

#[test]
fn loader_parses_rules_against_generated_rule_cells() {
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    let loaded = load(
        ResolvedSource::new(
            "cells.k",
            indoc! {r#"
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
            "#},
        ),
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

    insta::assert_debug_snapshot!(rules);
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
            RuleError::Parse(ref error)
                if matches!(error.error, ParseError::Ambiguous { .. })
        ),
        "{error:?}"
    );
}

#[test]
fn preserves_prefer_and_avoid_until_post_inference_disambiguation() {
    let errors = ["prefer", "avoid"]
        .into_iter()
        .map(|attribute| {
            let source = format!(
                r#"module MAIN
syntax Int ::= r"[0-9]+" [token]
syntax Exp ::= Int
syntax Exp ::= Exp "+" Exp [symbol(plus), {attribute}]
syntax Exp ::= Exp "*" Exp [symbol(times)]
rule 1 + 2 * 3 => 1
endmodule"#
            );
            resolve_rule_bubbles(&lowered(&source)).unwrap_err()
        })
        .collect::<Vec<_>>();
    assert!(errors.iter().all(|error| matches!(
        error,
        RuleError::Parse(error) if matches!(error.error, ParseError::Ambiguous { .. })
    )));

    insta::assert_debug_snapshot!(errors);
}

#[test]
fn builds_parametric_parse_forests_before_reaching_the_z3_boundary() {
    for source in [
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax Box ::= "box(" Int ")" [symbol(box)]
              syntax {S} S ::= "same(" S ")" [symbol(same)]
              rule box(same(1)) => box(1)
            endmodule
        "#},
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax {S} Int ::= "take(" S ")" [symbol(take)]
              rule take(1) => 1
            endmodule
        "#},
    ] {
        let error = resolve_rule_bubbles(&lowered(source)).unwrap_err();
        assert!(
            matches!(
                error,
                RuleError::Parse(ref error)
                    if matches!(&error.error, ParseError::Ambiguous { parses } if *parses > 0)
                        || matches!(
                            &error.error,
                            ParseError::SortInference { message }
                                if message.contains("parametric productions")
                        )
            ),
            "{error:?}"
        );
    }
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

#[test]
fn preserves_overloaded_generic_applications_for_sort_inference() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax A ::= "pa" A [symbol(pick)]
          syntax B ::= "pb" B [symbol(pick)]
          rule pick(a) => a
        endmodule
    "#});
    let error = resolve_rule_bubbles(&definition).unwrap_err();
    assert!(
        matches!(
            error,
            RuleError::Parse(ref error)
                if matches!(error.error, ParseError::Ambiguous { parses: 2 })
        ),
        "{error:?}"
    );
}

#[test]
fn reports_overloaded_terminators_without_a_unique_least_sort() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax First ::= "first" [symbol(unit)]
          syntax Second ::= "second" [symbol(unit)]
          syntax General ::= First
                           | Second
                           | "general" [symbol(unit)]
          rule general => general
        endmodule
    "#});
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

    insta::assert_debug_snapshot!(error);
}

#[test]
fn reconstructs_implicit_user_lists_after_sort_inference() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Id ::= r"[a-z]" [token]
          syntax Ids ::= List{Id, ","} [symbol(ids)]
          syntax Wrapped ::= "wrap" Ids [symbol(wrap)]
          rule wrap a => wrap a,b
        endmodule
    "#});
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

    insta::assert_debug_snapshot!(bodies);
}
