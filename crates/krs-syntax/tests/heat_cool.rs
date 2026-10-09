//! `heat`, `cool`, `hole = x`, and `result = S` on `#[k::rule]` (KF-014).

use krs_syntax::{KrsSyntax, ProvenanceRole, SyntaxErrorKind};

fn rule_key_error(source: &str) -> SyntaxErrorKind {
    krs_syntax::RuleAttribute::parse_source(source)
        .unwrap_err()
        .kind()
        .clone()
}

#[test]
fn heat_and_cool_name_their_hole_and_optional_result_sort() {
    let heat =
        krs_syntax::RuleAttribute::parse_source(r#"heat, hole = h, label = "heat-add""#).unwrap();
    let (kind, _) = heat.evaluation().unwrap();
    assert_eq!(kind, krs_ir::EvaluationKind::Heat);
    assert_eq!(heat.hole().unwrap(), "h");
    assert!(heat.result_sort().is_none());
    let roles = heat
        .provenance()
        .unwrap()
        .iter()
        .map(krs_syntax::ProvenanceAnchor::role)
        .collect::<Vec<_>>();
    assert_eq!(
        roles,
        [
            ProvenanceRole::RuleLabel,
            ProvenanceRole::RuleHeat,
            ProvenanceRole::RuleHole
        ]
    );

    let cool = krs_syntax::RuleAttribute::parse_source("cool, hole = value, result = crate::Value")
        .unwrap();
    let (kind, _) = cool.evaluation().unwrap();
    assert_eq!(kind, krs_ir::EvaluationKind::Cool);
    let result = cool.result_sort().unwrap();
    assert_eq!(
        quote::ToTokens::to_token_stream(result).to_string(),
        "crate :: Value"
    );
    assert_eq!(
        cool.provenance().unwrap().last().unwrap().role(),
        ProvenanceRole::RuleResultSort
    );
}

#[test]
fn heat_and_cool_reject_each_other_a_missing_hole_and_ordering_keys() {
    assert_eq!(
        rule_key_error("heat, cool, hole = h"),
        SyntaxErrorKind::InvalidRuleKey {
            reason: "a rule is a heating step or a cooling step, not both; write `heat` or `cool`",
        }
    );
    for source in ["heat", "cool, result = Value"] {
        assert_eq!(
            rule_key_error(source),
            SyntaxErrorKind::InvalidRuleKey {
                reason: "a heat or cool rule names the subterm it moves with `hole = x`, K's HOLE; bind `x` on the left side",
            },
            "{source}"
        );
    }
    for source in ["hole = h", "result = Value", r#"hole = h, label = "x""#] {
        assert_eq!(
            rule_key_error(source),
            SyntaxErrorKind::InvalidRuleKey {
                reason: "`hole` and `result` are keys of a heat or cool rule; add `heat` or `cool`",
            },
            "{source}"
        );
    }
    for source in [
        "owise, heat, hole = h",
        "priority = 10, cool, hole = h",
        "heat, hole = h, nondet = g",
        "heat, hole = h, anywhere",
    ] {
        assert_eq!(
            rule_key_error(source),
            SyntaxErrorKind::InvalidRuleKey {
                reason: "a heat or cool rule is ordered by its hole: K adds `requires notBool isKResult(HOLE)` to heating and `requires isKResult(HOLE)` to cooling; it takes no `owise`, `priority`, `nondet`, or `anywhere`",
            },
            "{source}"
        );
    }
}

#[test]
fn hole_and_result_values_are_checked() {
    assert_eq!(
        rule_key_error("heat, hole = h, hole = g"),
        SyntaxErrorKind::DuplicateArgument { name: "hole" }
    );
    assert_eq!(
        rule_key_error("heat, hole = h, result = A, result = B"),
        SyntaxErrorKind::DuplicateArgument { name: "result" }
    );
    assert_eq!(
        rule_key_error("heat, hole = a::b"),
        SyntaxErrorKind::InvalidArgumentValue {
            name: "hole",
            expected: "an unqualified Rust identifier",
        }
    );
    assert_eq!(
        rule_key_error(r#"heat, hole = h, result = "Value""#),
        SyntaxErrorKind::InvalidArgumentValue {
            name: "result",
            expected: "a sort path",
        }
    );
}
