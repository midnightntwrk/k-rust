use indoc::indoc;
use k_rust::definition::Sentence;
use k_rust::inner::{ParseError, RuleError, resolve_rule_bubbles};
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
