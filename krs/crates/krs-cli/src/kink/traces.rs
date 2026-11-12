//! `krs kink compare`'s trace views: an implementation's record of the corpus's `[observe]`
//! channels compared with the definition's, by krs-exec's comparison of two records
//! ([`krs_exec::compare_records`]), as `krs compare` compares two observation documents.
//!
//! Both sides are records of one declaration, and two elements are equal exactly when their
//! values are:
//!
//! - The definition's side is kink's value run of the baseline ([`ChannelValues`]). Each element
//!   is the document the corpus's own functions gave it ([`super::observe`]: every content of a
//!   KRS corpus is the front end's, so an element is [`Element::Evaluated`]), which is the
//!   canonical document of its value in the typed encoding: an object of a class's components
//!   by name, or a log's element.
//! - The implementation's side is the answer's `observations`, a `krs-observations/1` document
//!   read exactly ([`Observations::from_document`]) and then made a record of the declaration
//!   ([`ResolvedObservations::foreign_record`]): each stated value is decoded at its component's
//!   type and written as its canonical document, so whichever of a value's documents the
//!   implementation wrote, equal values have equal documents and unequal values unequal ones;
//!   and a `collapse` class's channel is collapsed as the definition's is, so its indices are
//!   those of the definition's channel whatever granularity the implementation stated it at.
//!
//! A record that is none of the declaration makes the answer malformed, named by its place.
//!
//! Each trace view compares the two records restricted to its channels, the implementation's on
//! the left and the definition's on the right, so that where several channels differ the
//! difference shown is the one the definition's run reached first. A channel a view names is
//! held by both records before anything is compared: krs-exec's comparison leaves out a channel
//! only one side has, and a view over a channel nothing was compared on would then agree.
//!
//! What the comparison finds is handed to kink-flow as facts ([`TraceJudged`]), which decides
//! the verdict's word and status: how far each channel agrees and whether both sides close
//! there; the first difference, each side shown as its element or its closure, the definition's
//! with the point it was read at (its rule, named as a `krs run` report names a rule, its side,
//! and the steps its run took to it) and the implementation's with its own count; or that an
//! element before any difference is not decided. An element of the definition some part of
//! which has no document in the typed encoding ([`UNDOCUMENTED`]) is not decided: its document
//! holds the part's KORE text, which no implementation states, so an inequality of documents
//! there would not be an inequality of values.
//!
//! That element `k` of the implementation's channel is read where the definition's element `k`
//! is, is the implementation's claim; nothing here checks it.

use std::collections::BTreeMap;

use kink_campaign::Element;
use kink_flow::{
    ChannelAgreed, ChannelValues, StopSide, TraceAnswer, TraceDifference, TraceJudged,
    TraceQuestion, TraceReach, ValuesEnd,
};
use krs_exec::{
    ChannelAgreement, ChannelKind, OBSERVATIONS_FORMAT, Observations, Observed, Reach,
    RecordComparison, RecordSide, ResolvedObservations, Semantics, UNDOCUMENTED, compare_records,
};
use serde_json::{Value, json};

/// Whether some part of the document `value` has no document in the typed encoding.
fn undocumented(value: &Value) -> bool {
    match value {
        Value::Object(object) => {
            object.contains_key(UNDOCUMENTED) || object.values().any(undocumented)
        }
        Value::Array(items) => items.iter().any(undocumented),
        _ => false,
    }
}

/// The definition's record of the channels `values`, as a record of the declaration `resolved`:
/// each element with its value, or as unknown where it is not decided or some part of it has no
/// document; each rule by its K label, which [`rule_name`] names for a reader.
fn definition_record(
    resolved: &ResolvedObservations,
    values: &[&ChannelValues],
) -> Result<Observations, String> {
    let channels = values
        .iter()
        .map(|channel| {
            let kind = resolved
                .channels()
                .find_map(|(name, kind)| (name == channel.name).then_some(kind))
                .ok_or_else(|| {
                    format!(
                        "the definition's values name `{}`, no channel of `[observe]`",
                        channel.name
                    )
                })?;
            let elements = channel
                .elements
                .iter()
                .enumerate()
                .map(|(index, element)| {
                    let (rule, side) = match &element.point {
                        Some((rule, side)) => (json!(&**rule), json!(side_name(*side))),
                        None => (Value::Null, Value::Null),
                    };
                    let mut document = json!({
                        "index": index,
                        "depth": element.depth,
                        "rule": rule,
                        "side": side,
                    });
                    match &element.element {
                        Element::Evaluated(value) if undocumented(value) => {
                            document["undecided"] = json!(
                                "a part of the definition's element has no document in the typed \
                                 encoding, so no stated value is compared with it"
                            );
                        }
                        Element::Evaluated(value) => document["value"] = value.clone(),
                        Element::Undecided => {
                            document["undecided"] =
                                json!("the definition's run does not decide the element");
                        }
                        Element::Content(_) => {
                            return Err(format!(
                                "the definition's element {index} of `{}` is a K term, not the \
                                 document the corpus's `[observe]` functions give it: the value \
                                 run did not evaluate them",
                                channel.name
                            ));
                        }
                        Element::End | Element::Undefined | Element::Cycle => {
                            return Err(format!(
                                "the definition's element {index} of `{}` is a closure, which is \
                                 no element",
                                channel.name
                            ));
                        }
                    }
                    Ok(document)
                })
                .collect::<Result<Vec<_>, String>>()?;
            let (closed, open) = match channel.ending() {
                ValuesEnd::End => (json!("end"), Value::Null),
                ValuesEnd::Undefined => (json!("undefined"), Value::Null),
                ValuesEnd::Open { index, reason, .. } => {
                    (Value::Null, json!({"index": index, "reason": reason}))
                }
            };
            Ok(json!({
                "name": channel.name,
                "kind": match kind {
                    ChannelKind::Point => "point",
                    ChannelKind::Log => "log",
                },
                "elements": elements,
                "closed": closed,
                "open": open,
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    Observations::from_document(&json!({"schema": OBSERVATIONS_FORMAT, "channels": channels}))
        .map_err(|error| format!("the definition's values are no record: {error}"))
}

const fn side_name(side: StopSide) -> &'static str {
    match side {
        StopSide::Before => "before",
        StopSide::After => "after",
    }
}

/// `record` restricted to the channels `names`, in their order; the first it does not hold.
fn restricted<'n>(record: &Observations, names: &'n [String]) -> Result<Observations, &'n str> {
    let channels = names
        .iter()
        .map(|name| {
            record
                .channels
                .iter()
                .find(|channel| channel.name == *name)
                .cloned()
                .ok_or(name.as_str())
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Observations {
        channels,
        conversions: 0,
    })
}

/// The answer to `question` over the declaration `resolved` (module documentation). A
/// difference's definition side names its rule by K label ([`name_rules`] names it for a
/// reader).
pub(super) fn judge(
    resolved: &ResolvedObservations,
    question: &TraceQuestion<'_>,
) -> Result<TraceAnswer, String> {
    let stated = match Observations::from_document(question.observations)
        .and_then(|record| resolved.foreign_record(&record))
    {
        Ok(stated) => stated,
        Err(detail) => return Ok(TraceAnswer::Malformed(detail)),
    };
    let asked = question
        .channels
        .iter()
        .map(|asked| {
            question
                .definition
                .iter()
                .find(|values| values.name == asked.name)
                .ok_or_else(|| {
                    format!(
                        "the definition's values hold no channel `{}`, which the request asked for",
                        asked.name
                    )
                })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let definition = definition_record(resolved, &asked)?;
    let mut judged = Vec::new();
    for view in question.implementation.trace_views() {
        let names = view.channels.as_deref().unwrap_or_default();
        if names.is_empty() {
            return Err(format!("the trace view `{}` names no channel", view.name));
        }
        let left = match restricted(&stated, names) {
            Ok(left) => left,
            Err(name) => {
                return Ok(TraceAnswer::Malformed(format!(
                    "at `channels`: no channel `{name}`, which the view `{}` compares",
                    view.name
                )));
            }
        };
        let right = restricted(&definition, names).map_err(|name| {
            format!(
                "the view `{}` compares `{name}`, which the request did not ask for",
                view.name
            )
        })?;
        judged.push(match compare_records(&left, &right) {
            RecordComparison::Differs(difference) => {
                let values = asked
                    .iter()
                    .find(|values| values.name == difference.channel)
                    .ok_or_else(|| format!("no values of `{}`", difference.channel))?;
                let both = matches!(
                    (&difference.left, &difference.right),
                    (Observed::Element(_), Observed::Element(_))
                );
                TraceJudged::Different(TraceDifference {
                    kind: if both { "value" } else { "closure" }.to_owned(),
                    index: difference.index,
                    path: difference.path.clone(),
                    definition: definition_side(values, difference.index, &difference.right)?,
                    implementation: implementation_side(&difference.left),
                    channel: difference.channel,
                })
            }
            RecordComparison::Agree(agreements) => {
                if agreements.len() != names.len() {
                    return Err(format!(
                        "the view `{}` names {} channels, and {} were compared",
                        view.name,
                        names.len(),
                        agreements.len()
                    ));
                }
                agreed(agreements)
            }
        });
    }
    Ok(TraceAnswer::Judged(judged))
}

/// What the channels' agreements say of a view no channel of which differs: that an element
/// before where a comparison stopped is not decided, naming the first such channel, its index
/// and the side; else how far each channel agrees, and whether both sides close there.
fn agreed(agreements: Vec<ChannelAgreement>) -> TraceJudged {
    let undecided = agreements.iter().find_map(|agreement| {
        agreement.undecided().map(|(side, index, reason)| {
            let side = match side {
                Some(RecordSide::Left) => "the implementation's element is not decided",
                Some(RecordSide::Right) => "the definition's element is not decided",
                None => "the two elements are not compared",
            };
            format!("`{}` element {index}: {side}: {reason}", agreement.channel)
        })
    });
    if let Some(detail) = undecided {
        return TraceJudged::Undecided(detail);
    }
    TraceJudged::Agree(
        agreements
            .into_iter()
            .map(|agreement| ChannelAgreed {
                reach: match (&agreement.left, &agreement.right) {
                    (Reach::Closed(_), Reach::Closed(_)) => TraceReach::Closed,
                    // The implementation's channel is open there: its own reason.
                    (Reach::Open(open), _) => TraceReach::Bounded {
                        implementation: Some(open.reason.clone()),
                    },
                    _ => TraceReach::Bounded {
                        implementation: None,
                    },
                },
                channel: agreement.channel,
                elements: agreement.through,
            })
            .collect(),
    )
}

/// The definition's side of a difference at `index` of the channel `values`, where the
/// comparison read `observed`: its element as the value run gave it with the point it was read
/// at (the rule by K label) and the steps its run took to it, or its closure.
fn definition_side(
    values: &ChannelValues,
    index: u64,
    observed: &Observed,
) -> Result<Value, String> {
    let closed =
        |closure: &str| json!({"closed": closure, "rule": null, "side": null, "steps": null});
    Ok(match observed {
        Observed::End => closed("end"),
        Observed::Undefined => closed("undefined"),
        Observed::Element(_) => {
            let element = usize::try_from(index)
                .ok()
                .and_then(|index| values.elements.get(index))
                .ok_or_else(|| {
                    format!(
                        "the definition's `{}` holds no element {index}",
                        values.name
                    )
                })?;
            let (rule, side) = match &element.point {
                Some((rule, side)) => (json!(&**rule), json!(side_name(*side))),
                None => (Value::Null, Value::Null),
            };
            json!({
                "element": match &element.element {
                    Element::Evaluated(value) => value.clone(),
                    _ => json!("undecided"),
                },
                "rule": rule,
                "side": side,
                "steps": element.depth,
            })
        }
    })
}

/// The implementation's side of a difference: its element, as its canonical document, with its
/// own count, or its closure.
fn implementation_side(observed: &Observed) -> Value {
    match observed {
        Observed::End => json!({"closed": "end", "count": null}),
        Observed::Undefined => json!({"closed": "undefined", "count": null}),
        Observed::Element(element) => json!({
            "element": element.value.clone().unwrap_or_else(|| json!("undecided")),
            "count": element.depth,
        }),
    }
}

/// `judged` with the rule of each difference's definition side named as a `krs run` report
/// names a rule ([`Semantics::stop_name`]): its KRS item's spelling where that names the item
/// alone, else its K label. The value run names a rule by its K label; the label stays where it
/// selects no one name.
pub(super) fn name_rules(semantics: &Semantics, judged: &mut [TraceJudged]) {
    let mut names = BTreeMap::<String, String>::new();
    for judged in judged {
        let TraceJudged::Different(difference) = judged else {
            continue;
        };
        let Some(label) = difference.definition["rule"].as_str().map(str::to_owned) else {
            continue;
        };
        let name = names
            .entry(label.clone())
            .or_insert_with(|| rule_name(semantics, &label));
        difference.definition["rule"] = json!(name);
    }
}

/// The name a report gives the rewrite rule the K label `label` selects.
fn rule_name(semantics: &Semantics, label: &str) -> String {
    let mut names = semantics
        .stop_rules(label)
        .into_iter()
        .flatten()
        .filter(|(_, selected)| selected.as_deref() == Some(label))
        .filter_map(|(id, _)| semantics.stop_name(&id))
        .collect::<Vec<_>>();
    names.sort();
    names.dedup();
    match names.as_slice() {
        [name] => name.clone(),
        _ => label.to_owned(),
    }
}
