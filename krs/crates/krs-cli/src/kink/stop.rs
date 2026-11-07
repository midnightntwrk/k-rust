//! `[stop]` in a KRS corpus: each rule named as `krs run --stop-before` and `--stop-after` name
//! one (a KRS item, `crate::` and its path for an item of the root package or the crate name of
//! the package that declares it, else a K label), mapped to the exact K labels of the rewrite
//! rules it selects, which kink-flow reads.
//!
//! The names resolve through krs-exec's own resolver over the definition's native compile
//! ([`krs_exec::Semantics::stop_rules`]), the one `krs run` resolves a stop with, so a name
//! selects in `krs kink` exactly the rules it selects in `krs run`, and a name `krs run` refuses
//! is refused here with its message: an item that wrote no rewrite rule (a function, whose
//! equations take no step), a label of an equation, a name that matches no rule or several. An
//! item lowers to several rewrite rules where K generates them from its one sentence (a
//! context's heat and cool rules), and a stop at the item is a stop at any of them, so its name
//! maps to every one of their labels. The labels are the native compile's; kink-flow checks each
//! against the K it loads, so a label the two compiles named differently would refuse the corpus
//! at stage `stop` rather than stop anywhere else.
//!
//! `[stop] when` names a stop condition with KRS's spellings, which the `condition` submodule
//! resolves and hands kink as the condition kink-campaign asks at each arrival.

use std::collections::BTreeMap;
use std::sync::Arc;

use kink_flow::FlowManifest;
use serde_json::{Value, json};

use super::condition::{self, KrsCondition};
use super::inputs::KrsInputs;
use super::render::Observers;

/// Why a corpus's `[stop]` cannot be bound: the reason and detail of its refusal at stage
/// `stop`.
pub(crate) struct Unbound {
    pub(crate) reason: &'static str,
    pub(crate) detail: String,
}

/// One written name's selection: its side, the name, and the labels it selects or why it
/// selects none.
type Selection = (&'static str, String, Result<Vec<String>, String>);

/// `manifest` with its `[stop]` names mapped to exact K labels and its condition, when it states
/// one, resolved and set ([`FlowManifest::with_stop_when`]), and the `krs` object the documents'
/// `stop` gains: `items`, each name as written to the labels it selects, and `when`, the
/// condition as written, when there is one; `manifest` unchanged, no object and no compile
/// without `[stop]`. The names resolve over `decoder`'s native compile, made here on first need
/// and kept for the decoder's later use on this thread; the condition's observer is the one
/// `observers` holds by its name, else `definition`, the corpus's own.
///
/// # Errors
///
/// `stop-unresolved` with why a name selects no rewrite rule, why a selected rule has no label to
/// name it by, or why the mapped stop names one rule on both sides; `native-compile` when the
/// definition does not compile natively, which resolving a name needs;
/// `stop-condition-unresolved` with krs's refusal of the condition or of its observer.
pub(crate) fn bind(
    mut manifest: FlowManifest,
    decoder: &Arc<KrsInputs>,
    observers: &Observers,
    definition: &krs_ir_levels::DefinitionIr,
) -> Result<(FlowManifest, Option<Value>), Unbound> {
    let Some(stop) = manifest.stop.as_mut() else {
        return Ok((manifest, None));
    };
    let written = stop
        .before
        .iter()
        .map(|name| ("before", name.clone()))
        .chain(stop.after.iter().map(|name| ("after", name.clone())))
        .collect::<Vec<_>>();
    let selections = decoder
        .with_semantics("resolving the [stop] names", |semantics| {
            Ok(written
                .into_iter()
                .map(|(side, name)| {
                    let labels = semantics
                        .stop_rules(&name)
                        .map_err(|error| format!("[stop] {side} `{name}`: {error}"))
                        .and_then(|rules| {
                            rules
                                .into_iter()
                                .map(|(id, label)| {
                                    label.ok_or_else(|| {
                                        format!(
                                            "[stop] {side} `{name}` selects the rewrite rule \
                                             {id}, which has no label, and kink-flow names a \
                                             stop's rules by label"
                                        )
                                    })
                                })
                                .collect()
                        });
                    (side, name, labels)
                })
                .collect::<Vec<Selection>>())
        })
        .map_err(|detail| Unbound {
            reason: "native-compile",
            detail,
        })?;
    let unresolved = |detail: String| Unbound {
        reason: "stop-unresolved",
        detail,
    };
    let mut items = BTreeMap::<String, Vec<String>>::new();
    let (mut before, mut after) = (Vec::new(), Vec::new());
    for (side, name, labels) in selections {
        let mut labels = labels.map_err(unresolved)?;
        labels.sort();
        labels.dedup();
        let selected = if side == "before" {
            &mut before
        } else {
            &mut after
        };
        selected.extend(labels.iter().cloned());
        items.insert(name, labels);
    }
    for labels in [&mut before, &mut after] {
        labels.sort();
        labels.dedup();
    }
    if let Some(label) = before.iter().find(|label| after.contains(label)) {
        return Err(unresolved(format!(
            "[stop] selects the rule `{label}` both before and after: a path stops before its \
             step, so it never stops after it; name it once"
        )));
    }
    stop.before = before;
    stop.after = after;
    let mut krs = json!({ "items": items });
    if let Some(when) = stop.when.clone() {
        krs["when"] = condition::written(&when);
        let asked = KrsCondition::bind(
            krs_exec::StopWhen {
                function: when.function,
                cells: when.cells,
                observer: when.observer,
            },
            definition,
            decoder,
            observers,
        )
        .map_err(|unbound| Unbound {
            reason: unbound.reason,
            detail: unbound.detail,
        })?;
        manifest = manifest.with_stop_when(asked);
    }
    Ok((manifest, Some(krs)))
}
