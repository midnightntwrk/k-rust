//! Operator wire refusals and original-relative action interpretation.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::builtin;
use k_rust::definition::{AttributeKey, Sentence, sentence_mut};
use k_rust::kast::{Sort, Term};
use k_rust::kompile::SentenceTyper;
use k_rust::outer::ResolvedSource;
use kink_patch::{
    Action, BUILTIN_CELL_SYNTAX_SORTS, Baseline, CandidateDisposition, Clause, CodecError,
    Completeness, Edit, OperatorSpec, PatchFailureKind, Universe, apply, canonical_json, generate,
    payload_digest, resolve_universe,
};
use serde_json::{Value, json};
use std::collections::BTreeSet;

fn spec(clauses: Vec<Clause>, action: Action) -> OperatorSpec {
    OperatorSpec::new("inline", "row", 7, clauses, action).expect("valid spec")
}

fn token(value: &str) -> Term {
    Term::Token {
        token: value.to_owned(),
        sort: Sort::new("Int"),
    }
}

fn load(text: &str) -> Baseline {
    let mut resolver = |_: &str, name: &str| {
        builtin::embedded(name).ok_or_else(|| format!("{name} is not embedded"))
    };
    Baseline::load(
        ResolvedSource::new("operator.k", text),
        "OPERATOR",
        None,
        &mut resolver,
        &support::options(),
    )
    .expect("inline fixture loads")
}

fn fixture() -> Baseline {
    load(
        r#"
module OPERATOR
 imports INT
 imports BASIC-K
 syntax Int ::= pair(Int, Int) [symbol(pair)]
              | other(Int, Int) [symbol(other)]
              | unary(Int) [symbol(unary)]
              | hold(Int) [symbol(hold)]
 rule [edit]: pair(1, 2) => unary(3) [owise, priority(7)]
 rule [keep]: other(4, 5) => 6
endmodule
"#,
    )
}

#[test]
fn every_clause_and_action_round_trips_with_exact_bytes_and_domain_digest() {
    let parametric = Sort::with_parameters(
        "Box",
        vec![Sort::with_parameters(
            "Pair",
            vec![Sort::new("Int"), Sort::new("Bool")],
        )],
    );
    let clauses = vec![
        Clause::RuleLabel("M.rule".to_owned()),
        Clause::Path(vec![0, 1, u32::MAX]),
        Clause::Sort(parametric.clone()),
        Clause::Head {
            label: "h".to_owned(),
        },
        Clause::NotHead {
            label: "h".to_owned(),
        },
        Clause::NotToken {
            token: "x\n\"".to_owned(),
            sort: parametric.clone(),
        },
        Clause::TokenOfSort {
            sort: parametric.clone(),
        },
        Clause::RuleAttribute {
            key: "priority".to_owned(),
            present: false,
        },
        Clause::ArgumentCount { count: u32::MAX },
    ];
    let actions = [
        Action::ReplaceHead {
            to: "target".to_owned(),
        },
        Action::ReplaceWithToken {
            token: "x\n\"".to_owned(),
            sort: parametric,
        },
        Action::Wrap {
            label: "wrap".to_owned(),
        },
        Action::Unwrap { argument: u32::MAX },
        Action::SwapArguments([0, u32::MAX]),
        Action::IntOffset(i64::MIN),
        Action::RemoveAttribute {
            key: "priority".to_owned(),
        },
        Action::DeleteRule,
    ];
    for action in actions {
        let original = spec(clauses.clone(), action);
        let bytes = original.canonical_json();
        assert_eq!(original.name(), "inline/row@7");
        assert_eq!(
            original.digest(),
            payload_digest("kink/operator/v1", bytes.as_bytes())
        );
        let decoded = OperatorSpec::from_canonical_json(&bytes).expect("round trip");
        assert_eq!(decoded, original);
        assert_eq!(decoded.canonical_json(), bytes);
        assert_eq!(decoded.digest(), original.digest());
        assert_eq!(
            decoded.canonical_value()["selector"][2]["sort"],
            "Box{Pair{Int,Bool}}"
        );
    }
}

fn assert_decode(value: &Value) {
    assert!(
        matches!(
            OperatorSpec::from_canonical_json(&canonical_json(value)),
            Err(CodecError::Decode(_))
        ),
        "{value}"
    );
}

#[test]
fn codec_refuses_unknown_missing_and_mistyped_keys_at_every_level() {
    let base = spec(vec![], Action::DeleteRule).canonical_value();
    for key in ["id", "variant", "version", "selector", "policy", "action"] {
        let mut missing = base.clone();
        missing.as_object_mut().expect("object").remove(key);
        assert_decode(&missing);
        let mut mistyped = base.clone();
        mistyped[key] = Value::Null;
        assert_decode(&mistyped);
    }
    let mut extra = base.clone();
    extra["extra"] = json!(0);
    assert_decode(&extra);
    for version in [
        json!(-1),
        json!(u64::from(u32::MAX) + 1),
        json!(1.5),
        json!("1"),
    ] {
        let mut bad = base.clone();
        bad["version"] = version;
        assert_decode(&bad);
    }
    for policy in [json!("all-matches"), json!({"each":true})] {
        let mut bad = base.clone();
        bad["policy"] = policy;
        assert_decode(&bad);
    }
    let bad_clauses = [
        json!({"unknown":true}),
        json!({"head":"h","path":[0]}),
        json!({}),
        json!({"rule-label":1}),
        json!({"path":[-1]}),
        json!({"path":[4294967296_u64]}),
        json!({"sort":{}}),
        json!({"sort":"not a sort"}),
        json!({"head":true}),
        json!({"not-head":[]}),
        json!({"token-of-sort":null}),
        json!({"argument-count":4294967296_u64}),
        json!({"not-token":{"token":"x","sort":"Int","extra":0}}),
        json!({"not-token":{"token":"x"}}),
        json!({"not-token":{"token":1,"sort":"Int"}}),
        json!({"rule-attribute":{"key":"owise","present":true,"extra":0}}),
        json!({"rule-attribute":{"key":"owise"}}),
        json!({"rule-attribute":{"key":1,"present":true}}),
        json!({"rule-attribute":{"key":"owise","present":"true"}}),
    ];
    for clause in bad_clauses {
        let mut bad = base.clone();
        bad["selector"] = json!([clause]);
        assert_decode(&bad);
    }
    let actions = [
        json!({"replace-head":{"to":"h"}}),
        json!({"replace-with-token":{"token":"0","sort":"Int"}}),
        json!({"wrap":{"label":"h"}}),
        json!({"unwrap":{"argument":0}}),
        json!({"remove-attribute":{"key":"owise"}}),
    ];
    for action in actions {
        let (tag, nested) = action
            .as_object()
            .expect("action")
            .iter()
            .next()
            .expect("tag");
        for key in nested.as_object().expect("nested").keys() {
            let mut missing = action.clone();
            missing[tag].as_object_mut().expect("nested").remove(key);
            let mut bad = base.clone();
            bad["action"] = missing;
            assert_decode(&bad);
            let mut mistyped = action.clone();
            mistyped[tag][key] = Value::Null;
            bad["action"] = mistyped;
            assert_decode(&bad);
        }
        let mut extra = action.clone();
        extra[tag]["extra"] = json!(0);
        let mut bad = base.clone();
        bad["action"] = extra;
        assert_decode(&bad);
    }
    for action in [
        json!("unknown"),
        json!({"unknown":{}}),
        json!({"delete-rule":{}}),
        json!({"swap-arguments":[0]}),
        json!({"swap-arguments":[0,1,2]}),
        json!({"swap-arguments":[0,-1]}),
        json!({"unwrap":{"argument":4294967296_u64}}),
        json!({"int-offset":9223372036854775808_u64}),
        json!({"int-offset":1.5}),
    ] {
        let mut bad = base.clone();
        bad["action"] = action;
        assert_decode(&bad);
    }
}

#[test]
fn codec_refuses_noncanonical_bytes_including_duplicate_keys() {
    let original = spec(vec![], Action::DeleteRule);
    let canonical = original.canonical_json();
    let reordered = r#"{"version":7,"variant":"row","selector":[],"policy":"each","id":"inline","action":"delete-rule"}"#;
    let duplicate = canonical.replacen(
        "\"id\":\"inline\"",
        "\"id\":\"discarded\",\"id\":\"inline\"",
        1,
    );
    for bytes in [
        reordered.to_owned(),
        duplicate,
        format!("{canonical}\n"),
        serde_json::to_string_pretty(&original.canonical_value()).expect("pretty JSON"),
    ] {
        assert_eq!(
            OperatorSpec::from_canonical_json(&bytes),
            Err(CodecError::NonCanonical)
        );
    }
}

#[test]
fn builtin_syntax_result_sorts_are_derived_and_refused_before_discovery() {
    let baseline = load(
        r#"
module OPERATOR
 imports INT
 imports BASIC-K
 syntax KItem ::= go() [symbol(go)] | done() [symbol(done)]
 configuration <top> <k> .K </k> <n> 0 </n> </top>
 rule [go]: <k> go() => done() ... </k> <n> N => N +Int 1 </n>
endmodule
"#,
    );
    let mut labels = BTreeSet::new();
    let mut sorts = BTreeSet::new();
    for module in &baseline.definition().modules {
        for sentence in &module.local_sentences {
            if let Sentence::Production {
                label: Some(label),
                sort,
                attributes,
                ..
            } = &**sentence
                && ["#cells", "#dots", "#noDots"].contains(&label.name.as_str())
            {
                assert_eq!(
                    attributes.string(AttributeKey::Source),
                    Some("krust-builtin://kast.md")
                );
                labels.insert(label.name.clone());
                sorts.insert(sort.name.clone());
            }
        }
    }
    assert_eq!(
        labels,
        ["#cells", "#dots", "#noDots"].map(str::to_owned).into()
    );
    assert_eq!(sorts, BUILTIN_CELL_SYNTAX_SORTS.map(str::to_owned).into());
    for sort in sorts {
        assert!(matches!(
            OperatorSpec::new(
                "x",
                "v",
                1,
                vec![Clause::Sort(Sort::new(&sort))],
                Action::DeleteRule
            ),
            Err(CodecError::Decode(_))
        ));
        let mut value = spec(vec![], Action::DeleteRule).canonical_value();
        value["selector"] = json!([{"sort":sort}]);
        assert_decode(&value);
    }
    let accepted = spec(vec![Clause::Sort(Sort::new("Int"))], Action::IntOffset(1));
    let universe = resolve_universe(&baseline, &Universe::v1());
    let generation =
        generate(&baseline, &universe, &accepted, usize::MAX).expect("placed Int sites");
    assert!(generation.scored());
    for origin in generation.selected_origins() {
        let at = &origin.site_tuple[0];
        let typer =
            SentenceTyper::new(baseline.loaded().resolved(), &at.sentence.module).expect("typer");
        let typing = typer
            .typing(baseline.sentence(&at.sentence).expect("rule"))
            .expect("typing");
        if let Some(position) = typing.positions.get(&at.path.0) {
            assert_eq!(position.sort, Some(Sort::new("Int")));
        } else {
            let branches = typing.branches.get(&at.path.0).expect("placed branches");
            assert_eq!(branches.left.sort, Some(Sort::new("Int")));
            assert_eq!(branches.right.sort, Some(Sort::new("Int")));
        }
    }
    for candidate in generation.candidates() {
        for origin in &candidate.origins {
            let term = baseline.term(&origin.site_tuple[0]).expect("site");
            assert!(
                !matches!(term.unannotated(), Term::Apply {label,..} if ["#cells", "#dots", "#noDots"].contains(&label.name.as_str()))
            );
        }
    }
}

fn replace_at(term: &mut Term, path: &[u32], replacement: Term) {
    if path.is_empty() {
        *term = replacement;
        return;
    }
    // Annotations are transparent in original-relative paths.
    match term {
        Term::Annotated { term, .. } => replace_at(term, path, replacement),
        Term::Apply { arguments, .. } | Term::Sequence(arguments) => {
            replace_at(&mut arguments[path[0] as usize], &path[1..], replacement)
        }
        Term::Rewrite { left, right } => replace_at(
            if path[0] == 0 { left } else { right },
            &path[1..],
            replacement,
        ),
        _ => panic!("unexpected fixture path {path:?}: {term:?}"),
    }
}

#[test]
fn each_action_changes_exactly_its_site_or_its_origin_sentence() {
    let baseline = fixture();
    let universe = resolve_universe(&baseline, &Universe::v1());
    assert_eq!(universe.included().len(), 2);
    let rows = [
        (
            vec![0, 0],
            Action::ReplaceHead {
                to: "other".to_owned(),
            },
            Some(Term::apply("other", vec![token("1"), token("2")])),
        ),
        (
            vec![0, 0],
            Action::ReplaceWithToken {
                token: "0".to_owned(),
                sort: Sort::new("Int"),
            },
            Some(token("0")),
        ),
        (
            vec![0, 0],
            Action::Wrap {
                label: "hold".to_owned(),
            },
            Some(Term::apply(
                "hold",
                vec![Term::apply("pair", vec![token("1"), token("2")])],
            )),
        ),
        (vec![0, 1], Action::Unwrap { argument: 0 }, Some(token("3"))),
        (
            vec![0, 0],
            Action::SwapArguments([0, 1]),
            Some(Term::apply("pair", vec![token("2"), token("1")])),
        ),
        (vec![0, 1, 0], Action::IntOffset(-1), Some(token("2"))),
        (
            vec![0],
            Action::RemoveAttribute {
                key: "priority".to_owned(),
            },
            None,
        ),
        (vec![0], Action::DeleteRule, None),
    ];
    for (path, action, replacement) in rows {
        let original_action = action.clone();
        let operator = spec(
            vec![
                Clause::RuleLabel("OPERATOR.edit".to_owned()),
                Clause::Path(path.clone()),
            ],
            action,
        );
        let generation = generate(&baseline, &universe, &operator, 16).expect("action generation");
        assert_eq!(
            generation.candidates().len(),
            1,
            "{original_action:?} {generation:?}"
        );
        let candidate = &generation.candidates()[0];
        assert_eq!(candidate.operator, "inline/row@7");
        assert!(candidate.patch.is_pinned());
        assert_eq!(candidate.patch.edits().len(), 1);
        assert_eq!(
            candidate.patch.written_sentences(),
            vec![support::rule(&baseline, "OPERATOR.edit")]
        );
        let mut expected = support::authored_rules(baseline.definition(), "OPERATOR");
        if let Some(replacement) = replacement {
            replace_at(
                &mut expected[0].fields[path[0] as usize],
                &path[1..],
                replacement.clone(),
            );
            let [
                Edit::ReplaceTerm {
                    at,
                    expected: old,
                    replacement: actual,
                },
            ] = candidate.patch.edits()
            else {
                panic!("term edit")
            };
            assert_eq!(at.path.0, path);
            assert_eq!(old, baseline.term(at).expect("old site"));
            assert_eq!(actual, &replacement);
        } else if matches!(original_action, Action::DeleteRule) {
            expected.remove(0);
            assert!(matches!(
                candidate.patch.edits(),
                [Edit::DeleteSentence { .. }]
            ));
        } else {
            expected[0].attributes.remove("priority");
            let [
                Edit::RemoveAttribute {
                    key,
                    expected: value,
                    ..
                },
            ] = candidate.patch.edits()
            else {
                panic!("attribute edit")
            };
            assert_eq!(key, "priority");
            assert_eq!(
                value,
                baseline
                    .sentence(&support::rule(&baseline, "OPERATOR.edit"))
                    .expect("sentence")
                    .attributes()
                    .get("priority")
                    .expect("attribute")
            );
        }
        let mutant = apply(&baseline, &candidate.patch).expect("pinned mutant applies");
        assert_eq!(
            support::authored_rules(mutant.definition(), "OPERATOR"),
            expected,
            "{original_action:?}"
        );
    }
}

fn with_requires(term: Term) -> Baseline {
    let baseline = fixture();
    let at = support::rule(&baseline, "OPERATOR.edit");
    let mut definition = baseline.definition().clone();
    let module = definition
        .modules
        .iter_mut()
        .find(|module| module.name == at.module)
        .expect("module");
    let Sentence::Rule { requires, .. } =
        sentence_mut(&mut module.local_sentences[at.index as usize])
    else {
        panic!("rule")
    };
    *requires = term;
    Baseline::new(
        baseline
            .loaded()
            .with_definition(definition)
            .expect("relinks"),
    )
}

#[test]
fn inapplicable_actions_reject_the_origin_as_no_change() {
    let rows = [
        (
            token("1"),
            Action::ReplaceHead {
                to: "other".to_owned(),
            },
        ),
        (token("1"), Action::Unwrap { argument: 0 }),
        (
            Term::apply("unary", vec![token("1")]),
            Action::Unwrap { argument: 1 },
        ),
        (token("1"), Action::SwapArguments([0, 1])),
        (
            Term::apply("unary", vec![token("1")]),
            Action::SwapArguments([0, 1]),
        ),
        (
            Term::Token {
                token: "true".to_owned(),
                sort: Sort::new("Bool"),
            },
            Action::IntOffset(1),
        ),
        (Term::apply("unary", vec![token("1")]), Action::IntOffset(1)),
        (token("not-an-integer"), Action::IntOffset(1)),
        (
            token("170141183460469231731687303715884105728"),
            Action::IntOffset(-1),
        ),
        (token(&i128::MAX.to_string()), Action::IntOffset(1)),
        (token(&i128::MIN.to_string()), Action::IntOffset(-1)),
        (
            token("1"),
            Action::RemoveAttribute {
                key: "absent".to_owned(),
            },
        ),
    ];
    for (term, action) in rows {
        let baseline = with_requires(term);
        let universe = resolve_universe(
            &baseline,
            &Universe {
                typed: false,
                ..Universe::v1()
            },
        );
        let operator = spec(
            vec![
                Clause::RuleLabel("OPERATOR.edit".to_owned()),
                Clause::Path(vec![1]),
            ],
            action,
        );
        let generation =
            generate(&baseline, &universe, &operator, 16).expect("fallback generation");
        assert_eq!(generation.selected_origins().len(), 1);
        assert!(generation.candidates().is_empty());
        let [CandidateDisposition::Rejected(failure)] = generation.dispositions() else {
            panic!("fallback rejected")
        };
        assert_eq!(failure.kind(), PatchFailureKind::NoChange);
        assert!(!generation.scored());
    }
}

#[test]
fn a_candidate_cap_makes_generation_incomplete_and_unscored() {
    let baseline = fixture();
    let universe = resolve_universe(&baseline, &Universe::v1());
    let operator = spec(
        vec![Clause::TokenOfSort {
            sort: Sort::new("Int"),
        }],
        Action::IntOffset(1),
    );
    let full = generate(&baseline, &universe, &operator, usize::MAX).expect("uncapped");
    assert_eq!(full.candidates().len(), 6);
    assert!(full.scored());
    let capped = generate(&baseline, &universe, &operator, 1).expect("capped");
    assert_eq!(capped.candidates().len(), 1);
    assert_eq!(capped.completeness(), Completeness::Incomplete);
    assert!(!capped.scored());
    assert!(generate(&baseline, &universe, &operator, 0).is_err());
}
