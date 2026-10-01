//! Canonical bounded-proof frontiers and termination classification.

use std::collections::BTreeSet;

use k_rust::kast::Term;
use serde_json::{Value, json};

use super::{
    canonical_json,
    reader::{self, Document},
};

fn root_label(term: &Term) -> Option<&str> {
    match term.unannotated() {
        Term::Apply { label, .. } => Some(&label.name),
        _ => None,
    }
}

fn flatten<'a>(term: &'a Term, label: &str, result: &mut Vec<&'a Term>) {
    if let Term::Apply {
        label: root,
        arguments,
    } = term.unannotated()
        && root.name == label
    {
        for child in arguments {
            flatten(child, label, result);
        }
    } else {
        result.push(term);
    }
}

fn frontier(term: &Term, constraint_labels: &BTreeSet<String>) -> Result<Vec<String>, String> {
    if matches!(root_label(term), Some("#Top" | "#Bottom")) {
        return Ok(Vec::new());
    }
    let mut branches = Vec::new();
    flatten(term, "#Or", &mut branches);
    let mut result = Vec::with_capacity(branches.len());
    for branch in branches {
        let mut conjuncts = Vec::new();
        flatten(branch, "#And", &mut conjuncts);
        let mut states = Vec::new();
        let mut constraints = Vec::new();
        for conjunct in conjuncts {
            let value = reader::term_value(conjunct)?;
            if root_label(conjunct).is_some_and(|name| constraint_labels.contains(name)) {
                constraints.push(value);
            } else {
                states.push(value);
            }
        }
        states.sort_by_cached_key(canonical_json);
        constraints.sort_by_cached_key(canonical_json);
        result.push(canonical_json(
            &json!({"states":states,"constraints":constraints}),
        ));
    }
    result.sort();
    Ok(result)
}

fn python_whitespace(character: char) -> bool {
    character.is_whitespace() || matches!(character, '\u{001c}'..='\u{001f}')
}

fn stalled(stderr: &str) -> bool {
    stderr
        .match_indices("configuration cannot be")
        .any(|(index, prefix)| {
            let tail = &stderr[index + prefix.len()..];
            let trimmed = tail.trim_start_matches(python_whitespace);
            trimmed.len() < tail.len() && trimmed.starts_with("rewritten further")
        })
}

fn classify(returncode: i64, root: Option<&str>, stderr: &str) -> Result<&'static str, String> {
    match (returncode, root) {
        (0, Some("#Top")) => Ok("proved"),
        (1, Some("#Bottom")) => Ok("failed"),
        (1, root) if !matches!(root, Some("#Top" | "#Bottom")) && stalled(stderr) => {
            Ok("incomplete")
        }
        _ => Err(format!(
            "unclassified proof termination: rc={returncode}, root={root:?}"
        )),
    }
}

pub(crate) fn handle(request: &Value, document: &Document) -> Result<Value, String> {
    let term = document.term()?;
    let action = match request.get("action") {
        None => "proof",
        Some(Value::String(action)) => action,
        Some(_) => return Err("frontier action must be a string".into()),
    };
    match action {
        "proof" => {
            let code = request
                .get("returncode")
                .and_then(Value::as_i64)
                .ok_or("proof frontier requires returncode")?;
            let stderr = request
                .get("stderr")
                .and_then(Value::as_str)
                .ok_or("proof frontier requires stderr")?;
            let root = root_label(term);
            let status = classify(code, root, stderr)?;
            let labels = match request.get("constraint_labels") {
                Some(labels) => serde_json::from_value(labels.clone())
                    .map_err(|error| format!("invalid constraint_labels: {error}"))?,
                None => ["#Equals", "#Ceil", "#And", "#Not", "#Top", "#Bottom"]
                    .into_iter()
                    .map(str::to_owned)
                    .collect(),
            };
            Ok(json!({"root":root,"status":status,"frontier":frontier(term,&labels)?}))
        }
        "search_set" => {
            let mut terms = Vec::new();
            flatten(term, "#Or", &mut terms);
            let values = terms
                .into_iter()
                .map(|term| reader::term_value(term).map(|value| canonical_json(&value)))
                .collect::<Result<BTreeSet<_>, _>>()?;
            Ok(json!(values))
        }
        action => Err(format!("unknown frontier action {action:?}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_frontier_preserves_branch_multiplicity_and_separates_constraints() {
        let state = Term::apply("state", vec![]);
        let constraint = Term::apply("#Ceil", vec![]);
        let branch = Term::apply("#And", vec![state.clone(), constraint.clone()]);
        let term = Term::apply("#Or", vec![branch.clone(), branch]);
        let expected = canonical_json(
            &json!({"states":[reader::term_value(&state).unwrap()],"constraints":[reader::term_value(&constraint).unwrap()]}),
        );
        assert_eq!(
            frontier(&term, &BTreeSet::from(["#Ceil".into()])).unwrap(),
            vec![expected.clone(), expected]
        );
    }

    #[test]
    fn completed_proofs_have_no_frontier() {
        for label in ["#Top", "#Bottom"] {
            assert!(
                frontier(&Term::apply(label, vec![]), &BTreeSet::new())
                    .unwrap()
                    .is_empty()
            );
        }
    }

    #[test]
    fn classification_requires_matching_root_and_stalled_evidence() {
        assert_eq!(classify(0, Some("#Top"), "").unwrap(), "proved");
        assert_eq!(classify(1, Some("#Bottom"), "").unwrap(), "failed");
        assert_eq!(
            classify(1, None, "configuration cannot be\n\t rewritten further").unwrap(),
            "incomplete"
        );
        assert!(classify(1, Some("#Top"), "configuration cannot be rewritten further").is_err());
        assert!(classify(1, None, "configuration cannot berewritten further").is_err());
        assert!(classify(0, Some("state"), "").is_err());
    }

    #[test]
    fn proof_action_returns_combined_evidence_and_requires_termination_fields() {
        let document = Document::Term(Term::apply("#Top", vec![]));
        assert_eq!(
            handle(&json!({"returncode":0,"stderr":""}), &document).unwrap(),
            json!({"root":"#Top","status":"proved","frontier":[]})
        );
        assert!(handle(&json!({"returncode":0}), &document).is_err());
        assert!(handle(&json!({"stderr":""}), &document).is_err());
        let document = Document::Term(Term::Sequence(vec![]));
        let result = handle(
            &json!({"returncode":1,"stderr":"configuration cannot be rewritten further"}),
            &document,
        )
        .unwrap();
        assert_eq!(result["root"], Value::Null);
        assert_eq!(result["status"], "incomplete");
        assert_eq!(result["frontier"].as_array().unwrap().len(), 1);
    }

    #[test]
    fn search_set_sorts_and_deduplicates_disjunctions() {
        let a = Term::apply("a", vec![]);
        let b = Term::apply("b", vec![]);
        let document = Document::Term(Term::apply(
            "#Or",
            vec![b.clone(), Term::apply("#Or", vec![a.clone(), b])],
        ));
        let mut expected = vec![
            canonical_json(&reader::term_value(&a).unwrap()),
            canonical_json(&reader::term_value(&Term::apply("b", vec![])).unwrap()),
        ];
        expected.sort();
        assert_eq!(
            handle(&json!({"action":"search_set"}), &document).unwrap(),
            json!(expected)
        );
    }
}
