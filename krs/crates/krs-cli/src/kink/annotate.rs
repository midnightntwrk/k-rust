//! The KRS names of every rule a kink-flow document names.
//!
//! kink-flow names a sentence of the baseline by its K module and position, and often its label
//! ([`kink_flow::visit_rules`]). The emission's rule table ([`EmittedRule`]) names the same
//! sentences by K module and label, labels being unique in the emitted K, so `(module, label)`
//! names one sentence of both, and the front end adds to its object
//! `krs = {item, package, file, line, column, kind, claim_helper}` from the table: the item the
//! `// KRS` line above the sentence names, and its Rust position. A sentence the emission wrote
//! no `// KRS` line for (KRS generated it, no Rust item is its author) has `null` there.
//!
//! A document also names compiled rules by their label alone, where no baseline position is
//! known: a specification diagnostic's `rule_label` and `observing_rule_label`, the `rule` of
//! each of a run's `short_circuit_readings` (`{id, label, source, location}`, the rewrite rule
//! whose work read the operand), and the steps of a query witness (`rules`, each the rewrite
//! rule's label, else a `file:line` or a compiled id). The rule a compiled rule was compiled from
//! carries the authored sentence's label (K's compile keeps it), so where that label is one of
//! the table's the front end names it too: `krs_rule` and `krs_observing_rule` beside the two
//! labels, `krs` inside a reading's `rule`, and `krs_rules` beside a witness's steps (`null` for
//! a step it does not name). A compiled rule with no label, or with one that
//! is not in the table, was written by no rule KRS emitted (K generates it from a production or
//! a configuration), so no Rust item is its author, and it is left as kink-flow names it; the
//! embedded k-rust-fuzz reports of a `fuzz` document are kink-flow's evidence and are left so.
//!
//! A mutation a command refuses before running it (a run row of status `invalid-mutation`, a check
//! row's refusal with no `rule`) names its offending edit by index (`edit`), and a refusal of a
//! stale anchor, such as `find-not-found` after the specification changed the text the edit
//! replaces, names the rule only inside its `detail`, by its label. Where the edit's anchor alone
//! (its `rule` and `line`, without the text it finds) still names one rule of the baseline, the
//! front end names that rule as resolution's first step addresses it: `anchor`
//! (`{module, index, label}`) on the run row and `rule` on the check row's refusal, each with its
//! `krs` object as above, so that a stale patch is reported with the KRS item and the Rust position
//! its anchor names, whatever the rule's label spells. An edit anchored by the text it finds alone
//! names no rule once that text is gone, and is left as kink-flow reports it.
//!
//! A corpus's `[stop]` names rules by KRS item or label, which the front end maps to K labels
//! before kink-flow reads them, so every document's `stop` names the labels; the front end adds
//! `krs = {items}` to it, each name as the corpus wrote it with the labels it selects.
//!
//! The table and the K are the same emission, so a labelled baseline rule with no table entry
//! means the front end cannot name it: such rules are listed under the document's
//! `krs.unnamed_rules` rather than named by a guess. That holds only of a document of this
//! command's emission, which is why `report`, which prints a document an earlier `run` wrote
//! (and named), neither builds the package nor annotates the document again.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::OnceLock;

use kink_flow::{EditAction, EditSpec, FlowManifest, MutationList, RuleRef};
use serde_json::{Map, Value, json};

/// The labels of the loaded definition's rules by `(module, index)`.
type LoadedLabels = BTreeMap<(String, u32), String>;

/// The rule each edit of each listed mutation names by its anchor alone, by mutation id and then
/// by edit index: the sentence's module and index and its label, `None` for an edit whose anchor
/// names no one rule.
type Anchors = BTreeMap<String, Vec<Option<Anchor>>>;

/// A rule an anchor names: its module, its index in the module and its label.
type Anchor = (String, u32, Option<String>);

use crate::{EmittedDefinition, EmittedRule};

/// The module-qualified form of a label `label` of a sentence of module `module`, as K stores a
/// `rule [x]:` label (`MODULE.x`); a label already qualified is unchanged.
pub(crate) fn qualified(label: &str, module: &str) -> String {
    if label.contains('.') {
        label.to_owned()
    } else {
        format!("{module}.{label}")
    }
}

/// The `krs` object of one table entry.
fn krs_value(rule: &EmittedRule) -> Value {
    json!({
        "item": rule.item,
        "package": rule.package,
        "file": rule.file,
        "line": rule.line,
        "column": rule.column,
        "kind": kind_name(rule.kind),
        "claim_helper": rule.claim_helper,
    })
}

/// The name a `krs` object gives a sentence kind.
const fn kind_name(kind: krs_ir::SentenceKind) -> &'static str {
    match kind {
        krs_ir::SentenceKind::Transition => "rule",
        krs_ir::SentenceKind::Equation => "equation",
        krs_ir::SentenceKind::Simplification => "simplification",
        krs_ir::SentenceKind::Alias => "alias",
        krs_ir::SentenceKind::Claim => "claim",
        krs_ir::SentenceKind::Desugar => "desugar",
        krs_ir::SentenceKind::Context => "context",
    }
}

/// The annotation of the documents of one command.
pub(crate) struct Annotator {
    /// Each table entry's `krs` object, by module-qualified label.
    by_qualified: BTreeMap<String, Value>,
    /// Each table entry's `krs` object, by label as the emission writes it.
    by_label: BTreeMap<String, Value>,
    /// Reads the labels of the loaded definition's rules, for [`Self::loaded_labels`].
    load_labels: Box<dyn Fn() -> LoadedLabels + Send + Sync>,
    /// The labels of the loaded definition's rules by `(module, index)`, read on first need: a
    /// document object that names a sentence without its label, when no other object of the
    /// document gives it.
    loaded_labels: OnceLock<LoadedLabels>,
    /// Reads the anchors of the command's mutation list, for [`Self::anchors`].
    load_anchors: Box<dyn Fn() -> Anchors + Send + Sync>,
    /// The anchors of the command's mutation list, read on first need: a row of a mutation the
    /// command refused, which names its offending edit.
    anchors: OnceLock<Anchors>,
    /// Each `[stop]` name as the corpus wrote it, with the labels it selects; `None` without a
    /// stop.
    stop_items: Option<Value>,
}

impl Annotator {
    /// The annotator of `emitted`'s documents on the corpus `manifest` binds, which loads the
    /// emitted definition when a document names a sentence by position alone, and, when a
    /// document refuses a mutation of the list at `mutations` (the command's), the edits'
    /// anchors.
    pub(crate) fn new(
        emitted: &EmittedDefinition,
        manifest: FlowManifest,
        mutations: Option<PathBuf>,
    ) -> Self {
        let anchored = manifest.clone();
        Self::from_rules(
            &emitted.rules,
            move || {
                let source = kink_flow::admit::corpus_source(&manifest);
                kink_corpus::load_source(&source)
                    .map(|loaded| {
                        kink_flow::rule_texts(&manifest, &loaded)
                            .into_iter()
                            .filter_map(|text| Some(((text.at.module, text.at.index), text.label?)))
                            .collect()
                    })
                    .unwrap_or_default()
            },
            move || {
                let Some(list) = mutations
                    .as_deref()
                    .and_then(|path| MutationList::read(path).ok())
                else {
                    return Anchors::new();
                };
                let source = kink_flow::admit::corpus_source(&anchored);
                let Ok(loaded) = kink_corpus::load_source(&source) else {
                    return Anchors::new();
                };
                list.mutations
                    .iter()
                    .map(|mutation| {
                        let anchors = mutation
                            .edits
                            .iter()
                            .map(|edit| anchored_rule(&anchored, &loaded, edit))
                            .collect();
                        (mutation.id.clone(), anchors)
                    })
                    .collect()
            },
        )
    }

    /// The annotator of the table `rules`, reading the loaded definition's labels with
    /// `load_labels` and the mutation list's anchors with `load_anchors`, each on first need.
    fn from_rules(
        rules: &[EmittedRule],
        load_labels: impl Fn() -> LoadedLabels + Send + Sync + 'static,
        load_anchors: impl Fn() -> Anchors + Send + Sync + 'static,
    ) -> Self {
        let mut by_qualified = BTreeMap::new();
        let mut by_label = BTreeMap::new();
        for rule in rules {
            let value = krs_value(rule);
            by_qualified.insert(qualified(&rule.label, &rule.module), value.clone());
            by_label.insert(rule.label.clone(), value);
        }
        Self {
            by_qualified,
            by_label,
            load_labels: Box::new(load_labels),
            loaded_labels: OnceLock::new(),
            load_anchors: Box::new(load_anchors),
            anchors: OnceLock::new(),
            stop_items: None,
        }
    }

    /// This annotator naming the corpus's stop: `items`, each `[stop]` name as written with the
    /// labels it selects, is added to every document's `stop` as `krs.items`.
    pub(crate) fn naming_stop(mut self, items: Option<Value>) -> Self {
        self.stop_items = items;
        self
    }

    /// The table's `krs` object of a sentence of `module` stored with `label` (bare or
    /// qualified).
    fn sentence(&self, module: &str, label: &str) -> Option<&Value> {
        self.by_qualified.get(&qualified(label, module))
    }

    /// The table's `krs` object of a compiled rule labelled `label`, whose module is unknown.
    fn labelled(&self, label: &str) -> Option<&Value> {
        self.by_label
            .get(label)
            .or_else(|| self.by_qualified.get(label))
    }

    /// The label of the loaded definition's rule at `(module, index)`.
    fn loaded_label(&self, module: &str, index: u32) -> Option<String> {
        self.loaded_labels
            .get_or_init(|| (self.load_labels)())
            .get(&(module.to_owned(), index))
            .cloned()
    }

    /// The rule edit `edit` of the mutation `id` names by its anchor alone, as a document object
    /// names a sentence.
    fn anchor(&self, id: &str, edit: u64) -> Option<Value> {
        let anchors = self.anchors.get_or_init(|| (self.load_anchors)());
        let edit = usize::try_from(edit).ok()?;
        let (module, index, label) = anchors.get(id)?.get(edit)?.as_ref()?;
        Some(json!({"module": module, "index": index, "label": label}))
    }

    /// Name the rule of each refused mutation's offending edit by its anchor (module
    /// documentation): a run row's `anchor`, a check row's refusal's `rule` where it has none.
    fn anchor_refused_edits(&self, document: &mut Value) {
        let Some(Value::Array(rows)) = document.get_mut("mutations") else {
            return;
        };
        for row in rows {
            let Some(row) = row.as_object_mut() else {
                continue;
            };
            let Some(id) = row.get("id").and_then(Value::as_str).map(str::to_owned) else {
                continue;
            };
            let edit_of = |object: &Map<String, Value>| object.get("edit").and_then(Value::as_u64);
            if row.get("status").and_then(Value::as_str)
                == Some(kink_flow::search::INVALID_MUTATION)
                && !row.contains_key("anchor")
                && let Some(anchor) = edit_of(row).and_then(|edit| self.anchor(&id, edit))
            {
                row.insert("anchor".into(), anchor);
            }
            if let Some(Value::Array(refusals)) = row.get_mut("refusals") {
                for refusal in refusals {
                    let Some(refusal) = refusal.as_object_mut() else {
                        continue;
                    };
                    if refusal.get("rule") == Some(&Value::Null)
                        && let Some(anchor) =
                            edit_of(refusal).and_then(|edit| self.anchor(&id, edit))
                    {
                        refusal.insert("rule".into(), anchor);
                    }
                }
            }
        }
    }

    /// Add the KRS names to every rule `document` names (module documentation). Applying it
    /// twice gives what applying it once does.
    pub(crate) fn annotate(&self, document: &mut Value) {
        self.anchor_refused_edits(document);
        if let (Some(items), Some(stop)) = (
            &self.stop_items,
            document.get_mut("stop").and_then(Value::as_object_mut),
        ) {
            stop.insert("krs".into(), json!({ "items": items }));
        }
        let mut unnamed = Vec::new();
        kink_flow::visit_rules(document, &mut |rule: &RuleRef, object| {
            let label = rule
                .label
                .clone()
                .or_else(|| self.loaded_label(&rule.at.module, rule.at.index));
            // A sentence with no label is no rule KRS emitted (every one it emits has one).
            let Some(label) = label else {
                return;
            };
            match self.sentence(&rule.at.module, &label) {
                Some(krs) => {
                    object.insert("krs".into(), krs.clone());
                }
                None => unnamed.push(json!({
                    "sentence": format!("{}#{}", rule.at.module, rule.at.index),
                    "label": label,
                })),
            }
        });
        self.annotate_labels(document);
        unnamed.sort_by_key(ToString::to_string);
        unnamed.dedup();
        if let Some(top) = document.as_object_mut() {
            if unnamed.is_empty() {
                top.remove("krs");
            } else {
                top.insert("krs".into(), json!({ "unnamed_rules": unnamed }));
            }
        }
    }

    /// The objects that name a compiled rule by label alone (module documentation).
    fn annotate_labels(&self, value: &mut Value) {
        match value {
            Value::Object(object) => {
                for value in object.values_mut() {
                    self.annotate_labels(value);
                }
                self.label_keys(object);
            }
            Value::Array(values) => {
                for value in values {
                    self.annotate_labels(value);
                }
            }
            _ => {}
        }
    }

    fn label_keys(&self, object: &mut Map<String, Value>) {
        for (key, added) in [
            ("rule_label", "krs_rule"),
            ("observing_rule_label", "krs_observing_rule"),
        ] {
            let found = object
                .get(key)
                .and_then(Value::as_str)
                .and_then(|label| self.labelled(label))
                .cloned();
            if let Some(found) = found {
                object.insert(added.into(), found);
            }
        }
        // A run's short-circuit readings: each names the rule whose work read the operand.
        if let Some(Value::Array(readings)) = object.get_mut("short_circuit_readings") {
            for reading in readings {
                let Some(Value::Object(rule)) = reading.get_mut("rule") else {
                    continue;
                };
                let found = rule
                    .get("label")
                    .and_then(Value::as_str)
                    .and_then(|label| self.labelled(label))
                    .cloned();
                if let Some(found) = found {
                    rule.insert("krs".into(), found);
                }
            }
        }
        // A query witness: its depth, its state's rendering and the labels of its steps.
        if object.contains_key("depth")
            && object.contains_key("rendering")
            && let Some(Value::Array(steps)) = object.get("rules")
        {
            let named = steps
                .iter()
                .map(|step| {
                    step.as_str()
                        .and_then(|label| self.labelled(label))
                        .cloned()
                        .unwrap_or(Value::Null)
                })
                .collect::<Vec<_>>();
            object.insert("krs_rules".into(), Value::Array(named));
        }
    }
}

/// The rule `edit` names by its anchor alone, its `rule` and `line` without the text it finds:
/// `None` for an edit anchored by that text alone, or whose anchor names no one rule.
fn anchored_rule(
    manifest: &FlowManifest,
    loaded: &kink_corpus::LoadedSource,
    edit: &EditSpec,
) -> Option<Anchor> {
    if edit.rule.is_none() && edit.line.is_none() {
        return None;
    }
    let anchor = EditSpec {
        action: EditAction::Delete,
        ..edit.clone()
    };
    let (at, label) = kink_flow::addressed_rule(manifest, loaded, &anchor)?;
    Some((at.module, at.index, label))
}

#[cfg(test)]
mod tests {
    use super::Annotator;
    use crate::EmittedRule;
    use serde_json::{Value, json};
    use std::collections::BTreeMap;

    fn rule(label: &str, item: &str, line: u32) -> EmittedRule {
        EmittedRule {
            module: "NAT".into(),
            label: label.into(),
            kind: krs_ir::SentenceKind::Equation,
            item: Some(item.into()),
            package: Some("story-plus".into()),
            file: Some("src/lib.rs".into()),
            line: Some(line),
            column: Some(1),
            claim_helper: false,
        }
    }

    /// The annotator of the story's two equations; the loaded definition's labels name the
    /// sentence `NAT#7` `nat--plus_succ`.
    /// The mutation list's anchors name, for `plus/c`, edit 0 by its rule `NAT#7` and edit 1 by
    /// nothing (an edit anchored by the text it finds alone).
    fn annotator() -> Annotator {
        Annotator::from_rules(
            &[
                rule("nat--plus_zero", "plus_zero", 32),
                rule("nat--plus_succ", "plus_succ", 38),
            ],
            || BTreeMap::from([(("NAT".to_owned(), 7), "nat--plus_succ".to_owned())]),
            || {
                BTreeMap::from([(
                    "plus/c".to_owned(),
                    vec![
                        Some(("NAT".to_owned(), 7, Some("nat--plus_succ".to_owned()))),
                        None,
                    ],
                )])
            },
        )
    }

    fn item(value: &Value) -> &Value {
        &value["krs"]["item"]
    }

    #[test]
    fn compiled_rules_named_by_label_alone_gain_their_items() {
        let mut document = json!({
            "diagnostics": [{
                "rule_label": "nat--plus_zero",
                "observing_rule_label": "NAT.nat--plus_succ",
            }, {
                "rule_label": "generated-by-k",
            }],
            "short_circuit_readings": [
                {"rule": {"id": "r1", "label": "nat--plus_zero", "source": null, "location": null}},
                {"rule": {"id": "r2", "label": "elsewhere", "source": null, "location": null}},
                {"rule": null},
            ],
            "witness": {"depth": 2, "rendering": "..", "rules": ["nat--plus_succ", "src/x.k:3"]},
        });
        annotator().annotate(&mut document);
        let diagnostic = &document["diagnostics"][0];
        assert_eq!(diagnostic["krs_rule"]["item"], "plus_zero");
        assert_eq!(diagnostic["krs_observing_rule"]["item"], "plus_succ");
        assert_eq!(diagnostic["krs_observing_rule"]["line"], 38);
        assert!(document["diagnostics"][1].get("krs_rule").is_none());
        let readings = &document["short_circuit_readings"];
        assert_eq!(item(&readings[0]["rule"]), "plus_zero");
        assert!(readings[1]["rule"].get("krs").is_none());
        assert_eq!(readings[2]["rule"], Value::Null);
        let steps = &document["witness"]["krs_rules"];
        assert_eq!(steps[0]["item"], "plus_succ");
        assert_eq!(steps[1], Value::Null);
        assert!(document.get("krs").is_none());
    }

    #[test]
    fn a_labelled_rule_the_table_lacks_is_listed_unnamed() {
        let mut document = json!({
            "rules": [
                {"module": "NAT", "index": 3, "label": "nat--plus_zero"},
                {"module": "NAT", "index": 7},
                {"module": "NAT", "index": 9, "label": "nat--gone"},
                {"module": "NAT", "index": 11},
            ],
        });
        let annotator = annotator();
        annotator.annotate(&mut document);
        let rules = &document["rules"];
        assert_eq!(item(&rules[0]), "plus_zero");
        // No object of the document labels NAT#7; the loaded definition does.
        assert_eq!(item(&rules[1]), "plus_succ");
        assert!(rules[2].get("krs").is_none());
        // A sentence with no label anywhere is no rule KRS emitted, and is not listed.
        assert!(rules[3].get("krs").is_none());
        assert_eq!(
            document["krs"],
            json!({"unnamed_rules": [{"sentence": "NAT#9", "label": "nat--gone"}]})
        );
        let once = document.clone();
        annotator.annotate(&mut document);
        assert_eq!(document, once);
    }

    /// A refused mutation's offending edit is named by the rule its anchor names, with its item:
    /// on a run row as `anchor`, on a check row's refusal as its `rule`.
    #[test]
    fn a_refused_edit_is_named_by_its_anchor() {
        let stale = |edit: u64| {
            json!({
                "id": "plus/c",
                "status": "invalid-mutation",
                "reason": "find-not-found",
                "edit": edit,
                "refusals": [
                    {"reason": "find-not-found", "edit": edit, "rule": null},
                    {"reason": "generated-only", "edit": edit, "rule": {"module": "NAT", "index": 3, "label": "nat--plus_zero"}},
                ],
            })
        };
        let mut document = json!({
            "mutations": [stale(0), stale(1), {"id": "plus/a", "status": "killed", "edit": 0}],
        });
        let annotator = annotator();
        annotator.annotate(&mut document);
        let rows = &document["mutations"];
        assert_eq!(item(&rows[0]["anchor"]), "plus_succ");
        assert_eq!(rows[0]["anchor"]["label"], "nat--plus_succ");
        assert_eq!(item(&rows[0]["refusals"][0]["rule"]), "plus_succ");
        // A refusal that names its rule keeps it.
        assert_eq!(item(&rows[0]["refusals"][1]["rule"]), "plus_zero");
        // An edit whose anchor names no rule, and a mutation that ran, gain nothing.
        assert!(rows[1].get("anchor").is_none());
        assert_eq!(rows[1]["refusals"][0]["rule"], Value::Null);
        assert!(rows[2].get("anchor").is_none());
        let once = document.clone();
        annotator.annotate(&mut document);
        assert_eq!(document, once);
    }
}
