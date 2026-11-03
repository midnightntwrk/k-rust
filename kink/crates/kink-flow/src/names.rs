//! Every rule a document names, for a front end that adds its own names to them.
//!
//! A kink-flow document names a sentence of the baseline specification by a JSON object with the
//! sentence's `module` (a string) and `index` (its position in the module, an unsigned integer),
//! and often its `label`, the `file` and the lines. The `kink-flow-check`, `-results`, `-run`,
//! `-report`, `-query` and `-fuzz` documents name every baseline sentence that way: results
//! `rules[]`, `untargeted_rules[]` and each record's `coverage.*[]`, run `mutations[].rules[]`,
//! `removed_claims`, `typing_diagnostics`, `weakening` and `untargeted_rules[]`, a check row's
//! `rules[]` and each finding's `rule`, a fuzz reach job's `job.rule`, and, in `spec.exclusion`,
//! the `authors[]` of each compiled sentence a cause names (its `rule`, a function link's
//! `equation`, a hook reference's or an `\equals` condition's `sentence`: the baseline sentences
//! the compiled one was compiled from, `crate::exclusion`). No other object of a document has
//! both keys. [`visit_rules`] relies on that convention instead of a list of paths, so a document
//! that gains a rule object is covered without a change here.
//!
//! The convention covers baseline sentences. A document also names compiled rules by their
//! compiled id or K label alone, which name no baseline sentence by themselves and are not
//! visited: a specification diagnostic's `rule_id` and `observing_rule_id` (a compiled id of the
//! definition that ran, the mutant's in a mutation's executed entry), a query witness path's
//! `rules` (each a label or position as text), and the k-rust-fuzz reports a `fuzz` document
//! embeds.
//!
//! It is meant for the krs front end, which adds, to every rule a document names, the KRS item
//! and the Rust position the sentence was emitted from.

use kink_patch::SentenceRef;
use serde_json::{Map, Value};
use std::collections::BTreeMap;

/// A rule as a document names it: the baseline sentence and its label.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuleRef {
    pub at: SentenceRef,
    /// The object's own `label`, else the label another object of the same document gives the
    /// same sentence; `None` when no object of the document gives one (the sentence may still
    /// have one: the front end then reads it from the definition by [`Self::at`]).
    pub label: Option<String>,
}

/// The sentence an object names: its `module` and `index`, when it has both.
fn sentence(object: &Map<String, Value>) -> Option<SentenceRef> {
    let module = object.get("module")?.as_str()?;
    let index = u32::try_from(object.get("index")?.as_u64()?).ok()?;
    Some(SentenceRef::new(module, index))
}

/// Call `visit` once on every JSON object of `document` that names a sentence of the baseline
/// (module documentation), with the sentence and the object, which `visit` may change. An
/// object is visited after the objects inside it, so nothing `visit` adds is visited.
pub fn visit_rules(document: &mut Value, visit: &mut dyn FnMut(&RuleRef, &mut Map<String, Value>)) {
    let mut labels = BTreeMap::new();
    collect_labels(document, &mut labels);
    walk(document, &labels, visit);
}

fn collect_labels(value: &Value, labels: &mut BTreeMap<SentenceRef, String>) {
    match value {
        Value::Object(object) => {
            if let (Some(at), Some(label)) = (
                sentence(object),
                object.get("label").and_then(Value::as_str),
            ) {
                labels.entry(at).or_insert_with(|| label.to_owned());
            }
            for value in object.values() {
                collect_labels(value, labels);
            }
        }
        Value::Array(values) => {
            for value in values {
                collect_labels(value, labels);
            }
        }
        _ => {}
    }
}

fn walk(
    value: &mut Value,
    labels: &BTreeMap<SentenceRef, String>,
    visit: &mut dyn FnMut(&RuleRef, &mut Map<String, Value>),
) {
    match value {
        Value::Object(object) => {
            for value in object.values_mut() {
                walk(value, labels, visit);
            }
            if let Some(at) = sentence(object) {
                let label = object
                    .get("label")
                    .and_then(Value::as_str)
                    .map(str::to_owned)
                    .or_else(|| labels.get(&at).cloned());
                visit(&RuleRef { at, label }, object);
            }
        }
        Value::Array(values) => {
            for value in values {
                walk(value, labels, visit);
            }
        }
        _ => {}
    }
}
