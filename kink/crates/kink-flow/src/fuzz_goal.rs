//! The goals of `fuzz --cover ITEM` and `fuzz --refuted RULE` (CS-8): a coverage obligation as
//! the facts of a run that cover it.
//!
//! An obligation of `coverage` is covered by a comparable program whose baseline run's record
//! shows the family's predicate ([`crate::coverage`]). Every such predicate is a disjunction of
//! facts the backend records of one run: a guard node reached with a truth, a guard outcome, a
//! rule fired, a fired instance's operand head or binder value. A fuzz job for the obligation is
//! a k-rust-fuzz coverage target over exactly those facts (`k_rust_fuzz::target::CoverageTarget`),
//! with a hit's run required comparable as kink counts only comparable programs, and its
//! candidate is confirmed by `coverage` itself listing the program as covering the item. So the
//! search reads the records `coverage` reads, and a witness is what `coverage` counts.
//!
//! The item is named by its id in the document `coverage` gives (as the front end names it),
//! looked up among the obligations of the specification with no program
//! ([`crate::coverage::universe`]): each family's universe is a function of the definition, so
//! every obligation is listed there, and no program runs to find it. The facts by family:
//!
//! - a requirement: of the sentence's guarded axioms (one skeleton each), the node's truth at its
//!   path in the written `requires` (the row's display path read back through the rendering,
//!   [`crate::guards::display_paths`]); the condition's `held` or `refuted` as the guard outcome,
//!   and, where a front end grouped the guard by its own constructs, as the author's condition
//!   (its last authored conjunct `true`, or an authored conjunct `false`); and where the root's
//!   truth restates a node's (`node_truth`), that node's truth too. A unique-cause requirement is
//!   a pair of entries, which no one run's fact states, so it gets no job.
//! - a production of the syntax family: an operand of a fired instance of a counted sentence's
//!   axiom with the production's head, or a firing of an axiom whose one alternative, or of an
//!   alternative of one, inspects or builds it ([`kink_native::coverage::SyntaxFacts`]).
//! - a field value a front end adds: a fired instance's binding of the template's binder to one
//!   of the encodings at which the field has the value (the item's `binder`).
//! - a rules item: the firing of the rule (each of its compiled ids k-rust's coverage can name),
//!   of a heating item its heating rule.

use crate::{
    admit::AdmittedSpec,
    cli::FrontEnd,
    coverage::{FIELD_VALUE, HEATING, MCDC, PRODUCTION, universe},
    manifest::FlowManifest,
};
use k_rust_fuzz::target::{CoverageFact, RuleRef};
use kink_corpus::admission::AdmissionRecord;
use kink_patch::SentenceRef;
use serde_json::{Value, json};
use std::collections::BTreeSet;

/// A fuzz job's coverage goal: the obligation's id, its value for the document, and the facts
/// that cover it.
pub(crate) struct Goal {
    /// The obligation's id, as `coverage` names it.
    pub(crate) item: String,
    /// The document's `job.item`: `{id, family, kind, text, facts}`.
    pub(crate) value: Value,
    /// The facts, any one of which covers the obligation.
    pub(crate) facts: Vec<CoverageFact>,
}

/// Why a goal is refused: a reason token and a detail.
pub(crate) type Refused = (&'static str, String);

/// The families an id is looked up in, in the document's order.
const FAMILIES: [&str; 3] = ["rules", "requirements", "syntax"];

/// Every obligation of `document`'s tier-1 families, with its family.
fn items(document: &Value) -> impl Iterator<Item = (&'static str, &Value)> {
    FAMILIES.into_iter().flat_map(move |family| {
        document["families"][family]["items"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|item| item["obligation"] != false)
            .map(move |item| (family, item))
    })
}

/// The goal of the obligation `id` of the specification (module documentation).
pub(crate) fn resolve(
    spec: &AdmittedSpec,
    record: &AdmissionRecord,
    manifest: &FlowManifest,
    front: &FrontEnd<'_>,
    id: &str,
) -> Result<Goal, Refused> {
    let document = universe(spec, record, manifest, front);
    resolve_in(&document, spec, manifest, id)
}

/// The id of the requirement that the condition of the rule at `at` is refuted, in the
/// specification's obligations: `requirement:<the rule's name>:refuted`.
pub(crate) fn refuted_item(
    spec: &AdmittedSpec,
    record: &AdmissionRecord,
    manifest: &FlowManifest,
    front: &FrontEnd<'_>,
    at: &SentenceRef,
) -> Result<Goal, Refused> {
    let document = universe(spec, record, manifest, front);
    let rule = crate::coverage::rule_item(&document, at)
        .and_then(|rule| rule.get("id"))
        .and_then(Value::as_str)
        .ok_or_else(|| {
            (
                "no-obligation",
                "the rule is no obligation of the rules family (out of scope, a claim helper, or \
                 a rule k-rust's coverage cannot name)"
                    .to_owned(),
            )
        })?;
    let name = rule.strip_prefix("rule:").unwrap_or(rule);
    let id = format!("requirement:{name}:refuted");
    if !items(&document).any(|(_, item)| item["id"] == id.as_str()) {
        return Err((
            "no-requirement",
            format!(
                "{rule} states no requirement {id}: its condition has no conjunct of the \
                 author's (an unconditional rule, or a condition of templates and inserted tests \
                 only)"
            ),
        ));
    }
    resolve_in(&document, spec, manifest, &id)
}

/// [`resolve`] in the document of the obligations.
fn resolve_in(
    document: &Value,
    spec: &AdmittedSpec,
    manifest: &FlowManifest,
    id: &str,
) -> Result<Goal, Refused> {
    let Some((family, item)) = items(document).find(|(_, item)| item["id"] == id) else {
        let wanted = id.to_lowercase();
        let near = items(document)
            .filter_map(|(_, item)| item["id"].as_str())
            .filter(|known| {
                let known = known.to_lowercase();
                known.contains(&wanted) || wanted.contains(&known)
            })
            .take(5)
            .collect::<Vec<_>>();
        return Err((
            "unknown-item",
            if near.is_empty() {
                format!(
                    "no obligation of the rules, requirements or syntax family has the id \
                     {id:?}; `coverage` lists each open one's id under its target's `item`"
                )
            } else {
                format!(
                    "no obligation has the id {id:?}; the ids that contain it, or that it \
                     contains, are: {}",
                    near.join(", ")
                )
            },
        ));
    };
    let facts = match family {
        "requirements" => requirement_facts(document, spec, item)?,
        "syntax" if item["kind"] == FIELD_VALUE => field_value_facts(manifest, item)?,
        "syntax" => production_facts(document, spec, item)?,
        _ => rule_facts(spec, item)?,
    };
    if facts.is_empty() {
        return Err((
            "no-fact",
            format!("no fact of a run's records covers {id}: the definition gives it none"),
        ));
    }
    let kind = match family {
        "requirements" => item["truth"].clone(),
        "syntax" => item["kind"].clone(),
        _ => item["kind"].clone(),
    };
    Ok(Goal {
        item: id.to_owned(),
        value: json!({
            "id": id,
            "family": family,
            "kind": kind,
            "file": item["file"],
            "line": item["line"].as_u64().or_else(|| item["start_line"].as_u64()),
            "facts": facts.len(),
        }),
        facts,
    })
}

/// A sentence position of a document object, `{module, index}`.
fn at_of(value: &Value) -> Option<SentenceRef> {
    Some(SentenceRef::new(
        value["module"].as_str()?.to_owned(),
        u32::try_from(value["index"].as_u64()?).ok()?,
    ))
}

/// The facts of a requirement item (module documentation).
pub(crate) fn requirement_facts(
    document: &Value,
    spec: &AdmittedSpec,
    item: &Value,
) -> Result<Vec<CoverageFact>, Refused> {
    if item["level"] == MCDC {
        return Err((
            "mcdc-requirement",
            "a unique-cause requirement is covered by a pair of entries of the condition, which \
             no one run's fact states; cover each side's valuation with its own case"
                .to_owned(),
        ));
    }
    let rule = items(document)
        .find(|(family, rule)| *family == "rules" && rule["id"] == item["rule"])
        .map(|(_, rule)| rule)
        .ok_or_else(|| {
            (
                "unknown-item",
                "the requirement's rule is not listed".to_owned(),
            )
        })?;
    let at = at_of(rule).ok_or_else(|| ("unknown-item", "the rule has no sentence".to_owned()))?;
    let skeletons = spec
        .guard_skeletons
        .as_ref()
        .ok()
        .and_then(|skeletons| skeletons.by_sentence.get(&at))
        .map(|skeletons| crate::guards::skeleton_values(skeletons))
        .unwrap_or_default();
    let axioms = skeletons
        .iter()
        .filter_map(|axiom| {
            Some((
                axiom["axiom"].as_str()?.to_owned(),
                crate::guards::display_paths(axiom),
            ))
        })
        .collect::<Vec<_>>();
    if axioms.is_empty() {
        return Err((
            "no-skeleton",
            "the sentence's condition has no skeleton the definition gives (no guarded axiom)"
                .to_owned(),
        ));
    }
    let mut facts = Vec::new();
    let node = |facts: &mut Vec<CoverageFact>, path: &str, truth: bool| {
        for (axiom, paths) in &axioms {
            if let Some(node) = paths.get(path) {
                facts.push(CoverageFact::GuardNode {
                    rule: RuleRef::UniqueId(axiom.clone()),
                    node: node.clone(),
                    truth,
                });
            }
        }
    };
    let truth = item["truth"].as_str().unwrap_or_default();
    match truth {
        "true" | "false" => {
            let path = item["node"].as_str().unwrap_or_default();
            node(&mut facts, path, truth == "true");
        }
        "held" | "refuted" => {
            let held = truth == "held";
            if let (Some(path), Some(restated)) =
                (item["node"].as_str(), item["node_truth"].as_str())
            {
                node(&mut facts, path, restated == "true");
            }
            let guard = &rule["guard"];
            let operands = guard["operands"].as_array().map_or(&[][..], Vec::as_slice);
            if guard["krs"].is_object() && !operands.is_empty() {
                // The author's condition: its conjuncts are the nodes below the condition's
                // conjunctions, and the authored ones are the author's.
                let authored = conjuncts(operands)
                    .into_iter()
                    .filter(|conjunct| conjunct["krs"]["origin"] == "authored")
                    .filter_map(|conjunct| conjunct["path"].as_str())
                    .collect::<Vec<_>>();
                if held {
                    if let Some(last) = authored.last() {
                        node(&mut facts, last, true);
                    }
                } else {
                    for path in authored {
                        node(&mut facts, path, false);
                    }
                }
            } else {
                for (axiom, _) in &axioms {
                    facts.push(CoverageFact::GuardOutcome {
                        rule: RuleRef::UniqueId(axiom.clone()),
                        held,
                    });
                }
            }
        }
        _ => {}
    }
    Ok(dedup(facts))
}

/// The conjuncts of a row guard's display tree: the nodes below its conjunctions, in written
/// order (a front end's grouping reads the author's condition from them).
fn conjuncts(operands: &[Value]) -> Vec<&Value> {
    fn below<'o>(operands: &'o [Value], parent: &str, conjuncts: &mut Vec<&'o Value>) {
        for operand in operands {
            let path = operand["path"].as_str().unwrap_or_default();
            let child = match path.rsplit_once('.') {
                Some((above, _)) => above == parent,
                None => parent.is_empty(),
            };
            if !child {
                continue;
            }
            if operand["kind"] == "conjunction" {
                below(operands, path, conjuncts);
            } else {
                conjuncts.push(operand);
            }
        }
    }
    let mut conjuncts = Vec::new();
    below(operands, "", &mut conjuncts);
    conjuncts
}

/// The sentences of the rules universe whose fired instances count for the syntax family: the
/// authored rules (no heating item) that are obligations.
fn counted(document: &Value) -> BTreeSet<SentenceRef> {
    items(document)
        .filter(|(family, rule)| *family == "rules" && rule["kind"] != HEATING)
        .filter_map(|(_, rule)| at_of(rule))
        .collect()
}

/// The facts of a production item (module documentation).
fn production_facts(
    document: &Value,
    spec: &AdmittedSpec,
    item: &Value,
) -> Result<Vec<CoverageFact>, Refused> {
    debug_assert_eq!(item["kind"], PRODUCTION);
    let symbol = item["symbol"]
        .as_str()
        .ok_or_else(|| ("no-symbol", "the production has no symbol".to_owned()))?;
    let facts_of = spec.syntax.as_ref().map_err(|reason| {
        (
            "no-syntax-facts",
            format!("the definition's syntax facts cannot be read: {reason}"),
        )
    })?;
    let authors = kink_native::coverage::RuleAuthors::of(&spec.compiled);
    let domain = kink_native::coverage::coverage_domain(&spec.compiled);
    let several = facts_of
        .by_alternative
        .keys()
        .map(|key| key.axiom.as_str())
        .collect::<BTreeSet<_>>();
    let mut facts = Vec::new();
    for at in counted(document) {
        let ids = authors
            .ids_of(&at)
            .filter(|id| domain.contains(*id))
            .map(str::to_owned)
            .collect::<Vec<_>>();
        let touches = |sets: &kink_native::coverage::SentenceSymbols| {
            sets.inspected.contains(symbol) || sets.built.contains(symbol)
        };
        if facts_of.single.get(&at).is_some_and(touches) {
            for id in ids.iter().filter(|id| !several.contains(id.as_str())) {
                facts.push(CoverageFact::Fired {
                    rule: RuleRef::UniqueId(id.clone()),
                    lhs: None,
                    rhs: None,
                });
            }
        }
        for (key, sets) in &facts_of.by_alternative {
            if ids.contains(&key.axiom) && touches(sets) {
                facts.push(CoverageFact::Fired {
                    rule: RuleRef::UniqueId(key.axiom.clone()),
                    lhs: key.lhs,
                    rhs: key.rhs,
                });
            }
        }
        for id in &ids {
            facts.push(CoverageFact::Operand {
                rule: RuleRef::UniqueId(id.clone()),
                symbol: symbol.to_owned(),
            });
        }
    }
    Ok(dedup(facts))
}

/// The facts of a field-value item a front end adds: its `binder` (`{axiom, variable}`, the
/// binder the front end selects) bound to one of its `binder.encodings` (hexadecimal points and
/// runs `0xA-0xB`).
fn field_value_facts(manifest: &FlowManifest, item: &Value) -> Result<Vec<CoverageFact>, Refused> {
    let binder = &item["binder"];
    let (Some(axiom), Some(variable)) = (binder["axiom"].as_str(), binder["variable"].as_str())
    else {
        return Err((
            "no-binder",
            "the field value names no template binder (`binder`): its front end gives no fact \
             of a run that reaches it"
                .to_owned(),
        ));
    };
    let mut values = Vec::new();
    for run in binder["encodings"].as_array().into_iter().flatten() {
        let Some(run) = run.as_str() else { continue };
        let point =
            |text: &str| u128::from_str_radix(text.trim().trim_start_matches("0x"), 16).ok();
        let (first, last) = match run.split_once('-') {
            Some((first, last)) => (point(first), point(last)),
            None => (point(run), point(run)),
        };
        let (Some(first), Some(last)) = (first, last) else {
            return Err((
                "no-binder",
                format!("the encoding {run:?} is no hexadecimal run"),
            ));
        };
        values.extend((first..=last).map(|value| value.to_string()));
    }
    let cap = manifest
        .syntax
        .iter()
        .flat_map(|selection| &selection.binders)
        .find(|(selected, name, _)| selected == axiom && name == variable)
        .map_or(values.len(), |(_, _, cap)| *cap);
    Ok(vec![CoverageFact::Binder {
        rule: RuleRef::Label(axiom.to_owned()),
        variable: variable.to_owned(),
        values,
        cap,
    }])
}

/// The facts of a rules item: the firing of each compiled id of its sentence k-rust's coverage
/// names, of a heating item its heating rule.
pub(crate) fn rule_facts(spec: &AdmittedSpec, item: &Value) -> Result<Vec<CoverageFact>, Refused> {
    if item["kind"] == HEATING {
        let axiom = item["heating"]["heat"]["axiom"]
            .as_str()
            .ok_or_else(|| ("no-fact", "the heating item names no rule".to_owned()))?;
        return Ok(vec![CoverageFact::Fired {
            rule: RuleRef::UniqueId(axiom.to_owned()),
            lhs: None,
            rhs: None,
        }]);
    }
    let at = at_of(item).ok_or_else(|| ("unknown-item", "the rule has no sentence".to_owned()))?;
    let authors = kink_native::coverage::RuleAuthors::of(&spec.compiled);
    let domain = kink_native::coverage::coverage_domain(&spec.compiled);
    Ok(authors
        .ids_of(&at)
        .filter(|id| domain.contains(*id))
        .map(|id| CoverageFact::Fired {
            rule: RuleRef::UniqueId(id.to_owned()),
            lhs: None,
            rhs: None,
        })
        .collect())
}

/// `facts` without repeats, in their first order.
fn dedup(facts: Vec<CoverageFact>) -> Vec<CoverageFact> {
    let mut kept: Vec<CoverageFact> = Vec::new();
    for fact in facts {
        if !kept.contains(&fact) {
            kept.push(fact);
        }
    }
    kept
}

/// Whether `document`, a `coverage` document of a corpus whose one program is `program`, lists
/// that program as covering the obligation `item`: the item is covered and its covering list
/// (`covered_by`, `reached_by` or `fired_by`) names the program. `None` when the document lists
/// no such item.
pub(crate) fn covered_by(document: &Value, item: &str, program: &str) -> Option<bool> {
    let (_, found) = FAMILIES.into_iter().find_map(|family| {
        document["families"][family]["items"]
            .as_array()?
            .iter()
            .find(|candidate| candidate["id"] == item)
            .map(|found| (family, found))
    })?;
    let listed = ["covered_by", "reached_by", "fired_by"].iter().any(|key| {
        found[*key]
            .as_array()
            .is_some_and(|programs| programs.iter().any(|p| p == program))
    });
    Some(found["covered"] == true && listed)
}
