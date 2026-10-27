//! Conformance of the changed saturation schedule, including every callback input.
//! Model: KRust.SubstitutionSaturation.replay, with arbitrary indexed callback results.
//! Term reconstruction is unchanged and stays in the callback, outside this optimization's model.
use std::collections::BTreeMap;

use lean_conformance::check;
use proptest::prelude::*;
use serde_json::{Value, json};

use super::generators;
use crate::{
    substitution::{Substitution, saturate_with, saturation_tests::reference_saturate_with},
    term::{Sort, Term, Variable},
};

#[derive(Clone, Debug)]
struct Case {
    raw_bindings: Vec<(usize, usize)>,
    answers: Vec<usize>,
    term: Term,
}

fn cases() -> impl Strategy<Value = Case> {
    (
        prop::collection::vec((0usize..6, 0usize..5), 0..9),
        prop::collection::vec(0usize..5, 0..40),
        generators::term(),
    )
        .prop_map(|(raw_bindings, answers, term)| Case {
            raw_bindings,
            answers,
            term,
        })
}

impl Case {
    fn terms(&self) -> Vec<Term> {
        vec![
            self.term.clone(),
            Term::variable(Variable::new("X", Sort::simple("S"))),
            Term::variable(Variable::set("X", Sort::simple("S"))),
            Term::raw_domain_value(Sort::simple("S"), "a"),
            Term::raw_domain_value(Sort::simple("S"), "b"),
        ]
    }

    fn bindings(&self) -> Substitution {
        // Same names across sorts/kinds exercise the real Variable Eq/Ord, before ordinal encoding.
        let variables = [
            Variable::new("X", Sort::simple("S")),
            Variable::set("X", Sort::simple("S")),
            Variable::new("X", Sort::simple("T")),
            Variable::new("Y", Sort::simple("S")),
            Variable::new("Z", Sort::simple("S")),
            Variable::set("Y", Sort::simple("T")),
        ];
        let terms = self.terms();
        self.raw_bindings
            .iter()
            .map(|(key, value)| (variables[*key].clone(), terms[*value].clone()))
            .collect()
    }

    fn encode(&self) -> Value {
        let terms = self.terms();
        let bindings = self.bindings();
        let initial = bindings
            .values()
            .enumerate()
            .map(|(key, value)| json!([key, value_id(&terms, value)]))
            .collect::<Vec<_>>();
        json!({"bindings": initial, "answers": self.answers.iter().map(|index| value_id(&terms, &terms[*index])).collect::<Vec<_>>()})
    }

    fn observe(&self, restoring: bool) -> Value {
        let terms = self.terms();
        let mut bindings = self.bindings();
        let ordinals = bindings
            .keys()
            .cloned()
            .enumerate()
            .map(|(id, key)| (key, id))
            .collect::<BTreeMap<_, _>>();
        let mut calls = Vec::new();
        let mut apply = |value: &Term, others: &Substitution| {
            let missing = ordinals
                .keys()
                .filter(|key| !others.contains_key(*key))
                .collect::<Vec<_>>();
            assert_eq!(
                missing.len(),
                1,
                "each call excludes exactly its current key"
            );
            calls.push(json!({"key": ordinals[missing[0]], "value": value_id(&terms, value), "others": entries_json(&ordinals, &terms, others)}));
            self.answers
                .get(calls.len() - 1)
                .map_or_else(|| value.clone(), |index| terms[*index].clone())
        };
        if restoring {
            saturate_with(&mut bindings, &mut apply);
        } else {
            reference_saturate_with(&mut bindings, &mut apply);
        }
        json!({"bindings": entries_json(&ordinals, &terms, &bindings), "cursor": calls.len(), "calls": calls})
    }
}

fn value_id(terms: &[Term], value: &Term) -> usize {
    // The first equal member is the equality-class ID, including repeated pool entries.
    terms
        .iter()
        .position(|term| term == value)
        .expect("callback returns only members of its finite term pool")
}

fn entries_json(
    keys: &BTreeMap<Variable, usize>,
    terms: &[Term],
    bindings: &Substitution,
) -> Value {
    json!(
        bindings
            .iter()
            .map(|(key, value)| json!([keys[key], value_id(terms, value)]))
            .collect::<Vec<_>>()
    )
}

#[test]
fn restoring_saturation_agrees_with_lean_schedule() {
    let Some(answers) = check("substitutionSaturation", cases(), Case::encode, |case| {
        case.observe(true)
    }) else {
        return;
    };
    if answers.len() >= 1024 {
        assert!(answers.iter().any(|answer| answer["cursor"] == 0));
        assert!(
            answers
                .iter()
                .any(|answer| answer["cursor"].as_u64().unwrap() > 6)
        );
        assert!(
            answers.iter().any(|answer| {
                let count = answer["bindings"].as_array().unwrap().len();
                let calls = answer["cursor"].as_u64().unwrap() as usize;
                count > 1 && calls < count * count
            }),
            "early convergence must be exercised"
        );
    }
}

#[test]
fn old_saturation_agrees_with_lean_schedule() {
    check("substitutionSaturationOld", cases(), Case::encode, |case| {
        case.observe(false)
    });
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4096))]
    #[test]
    fn restoring_saturation_has_exact_old_trace(case in cases()) {
        prop_assert_eq!(case.observe(true), case.observe(false));
    }
}
