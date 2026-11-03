//! What a definition exclusion is and why it holds, as every command reports it: one formatter
//! for `check`, `results` and `run`, whose `detail` `fuzz` gives too.
//!
//! A definition exclusion (kink-native `DefinitionExclusions::definition_exclusion`) excludes
//! every run on the definition, so no program can be judged on it. kink-native records, for each
//! exclusion, the sentences that make it hold, and for the short-circuit reading the cause chain
//! of each rule it excludes (`ShortCircuitCause`): the rule, the part of it where the dependence
//! shows, every function applied with the equation through which it depends on the reading, and
//! the short-circuit operator with the operand a backend may skip and the term in it that may be
//! undefined. This module prints them, as data ([`definition_exclusion`]) and as one text
//! ([`detail`]), and says why a program's baseline run is excluded before it runs
//! ([`program_detail`]).
//!
//! Every term is printed as K text by the command's [`EndReader`], cut at [`VALUE_CAP`]
//! characters in the data and at [`HEAD_CAP`] in the text; a term the printer refuses is printed
//! as KORE, as kill evidence prints it (the text leaves out such a condition leaf, which the data
//! holds). A position is the `Source` and `Location` attributes the
//! compiled sentence or symbol declaration carries: the file as the load named it, and the span
//! `start_line:start_column-end_line:end_column`.

use crate::evidence::{EndReader, HEAD_CAP, VALUE_CAP};
use k_rust::{kast::identifier::label_or_name, kore::ast::Pattern};
use kink_native::exclusion::{
    CauseLink, CausePart, DefinitionExclusions, Exclusion, OperatorLink, ReadingDependence,
    SentenceLink, ShortCircuitCause, ShortCircuitEffect, SymbolLink,
};
use serde_json::{Value, json};
use std::collections::BTreeSet;

/// The most causes [`detail`] names; the data lists every one.
pub const DETAIL_CAUSES: usize = 8;

/// Where an exclusion of every run of a program on the baseline comes from, as admission reads it
/// without running the program (`crate::admit::ProgramExclusion`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExclusionScope {
    /// The specification's definition exclusion, which excludes every run on it.
    Definition,
    /// The exclusion of the program's initial configuration (kink-native
    /// `DefinitionExclusions::state_exclusion`): it applies an implementation-chosen hook, or a
    /// function or operator whose value depends on the short-circuit reading.
    InitialState,
}

impl ExclusionScope {
    /// The name a document gives the scope (a check document's program `stage`).
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Definition => "definition",
            Self::InitialState => "initial-state",
        }
    }
}

/// The definition exclusion of `facts` as data: null when there is none, else
/// `{exclusion, detail, causes}`, where `exclusion` is its name, `detail` is [`detail`]'s text and
/// `causes` lists what makes it hold:
///
/// - `short-circuit-reading`: each rule's cause chain, `{rule, effect, part, links}`: `rule` a
///   sentence; `effect` `applicability` (whether the rule applies can differ between the
///   readings) or `result` (its result can be undefined in k-rust's reading where a
///   short-circuiting backend gives a value); `part` where in the rule the first link sits; and
///   `links` in order from the rule, each `{link: "function", function, dependence, equation,
///   part}` (`dependence` `valued` or `undefined`) or `{link: "operator", operator, position,
///   operand, term, term_symbol}`;
/// - `implementation-chosen-hook`: `{sentence, symbol, hook}` per reference;
/// - `equals-condition`: `{sentence}` per sentence;
/// - `load-stack-stop`: none (`detail` gives the count).
///
/// A sentence is `{name, module, label, id, source, location}` (`id` its compiled `UNIQUE_ID`),
/// a symbol `{id, module, label, hook, source, location}` (`id` its KORE name), a location
/// `{start_line, start_column, end_line, end_column}`, and a part `{part: "condition", leaf}` or
/// `{part: "right-side"}`. A term (`leaf`, `operand`, `term`) is printed
/// `{text, rendering, truncated}` (and `note`), as kill evidence prints a value.
#[must_use]
pub fn definition_exclusion(facts: &DefinitionExclusions, reader: &EndReader) -> Value {
    let Some(exclusion) = facts.static_exclusion() else {
        return Value::Null;
    };
    let sentence = |name: &str| sentence_named(facts, name);
    let causes = match exclusion {
        Exclusion::ShortCircuitReading => facts
            .short_circuit_causes
            .iter()
            .map(|cause| cause_value(cause, reader))
            .collect(),
        Exclusion::ImplementationChosenHook => facts
            .implementation_chosen
            .iter()
            .map(|reference| {
                json!({
                    "sentence": sentence(&reference.sentence),
                    "symbol": reference.symbol,
                    "hook": reference.hook,
                })
            })
            .collect(),
        Exclusion::EqualsCondition => facts
            .equals_conditions
            .iter()
            .map(|name| json!({"sentence": sentence(name)}))
            .collect(),
        _ => Vec::new(),
    };
    json!({
        "exclusion": exclusion.name(),
        "detail": detail(facts, exclusion, reader),
        "causes": causes,
    })
}

/// What makes `exclusion` hold on a definition with these facts, in one text that names its
/// sentences with their positions; for the short-circuit reading, each rule's cause chain (at
/// most [`DETAIL_CAUSES`]; [`definition_exclusion`]'s data lists every one).
#[must_use]
pub fn detail(facts: &DefinitionExclusions, exclusion: Exclusion, reader: &EndReader) -> String {
    match exclusion {
        Exclusion::LoadStackStop => format!(
            "its load counted {} stop(s) for lack of native stack, so the theory a run executes \
             is not a function of the definition",
            facts.load_stack_stops
        ),
        Exclusion::ImplementationChosenHook => format!(
            "it references a hook whose value the definition leaves open and k-rust chooses: {}",
            listed(facts.implementation_chosen.iter().map(|reference| format!(
                "{} applies {} ({})",
                sentence_text(facts, &reference.sentence),
                reference.symbol,
                reference.hook
            )))
        ),
        Exclusion::ShortCircuitReading => {
            let causes = &facts.short_circuit_causes;
            let shown = causes
                .iter()
                .take(DETAIL_CAUSES)
                .map(|cause| cause_text(cause, reader))
                .collect::<Vec<_>>();
            let named = causes
                .iter()
                .map(|cause| cause.rule.name.clone())
                .collect::<BTreeSet<_>>();
            // A rule a list names without a cause (none, as kink-native builds the lists) is
            // still named, by its sentence.
            let uncaused = facts
                .short_circuit_conditions
                .iter()
                .chain(&facts.short_circuit_results)
                .filter(|name| !named.contains(*name))
                .cloned()
                .collect::<BTreeSet<_>>();
            let mut text = format!(
                "a rule's applicability or result depends on whether andBool, orBool, \
                 impliesBool, #if, andThenBool or orElseBool skip an operand that may be \
                 undefined, which the definition leaves to the backend: {}",
                shown.join("; ")
            );
            if causes.len() > DETAIL_CAUSES {
                text.push_str(&format!(
                    "; and {} more cause(s)",
                    causes.len() - DETAIL_CAUSES
                ));
            }
            if !uncaused.is_empty() {
                text.push_str(&format!(
                    "; and rules with no recorded cause: {}",
                    listed(uncaused.iter().map(|name| sentence_text(facts, name)))
                ));
            }
            text
        }
        Exclusion::EqualsCondition => format!(
            "a rule or equation has a condition equating two terms ({{ A #Equals B }}), which \
             k-rust may decide wrongly when they may be undefined: {}",
            listed(
                facts
                    .equals_conditions
                    .iter()
                    .map(|name| sentence_text(facts, name))
            )
        ),
        other => other.name().to_owned(),
    }
}

/// Why every run of a program on the baseline is excluded before it runs, for `exclusion` in
/// `scope`: for [`ExclusionScope::Definition`] a pointer to the document's `spec.exclusion`,
/// which says why once for every program; for [`ExclusionScope::InitialState`] what the
/// program's initial configuration applies.
#[must_use]
pub fn program_detail(exclusion: Exclusion, scope: ExclusionScope) -> String {
    match scope {
        ExclusionScope::Definition => format!(
            "the specification has a definition exclusion ({}), which excludes every run on it, \
             so no program can be judged; the document's spec.exclusion names its causes",
            exclusion.name()
        ),
        ExclusionScope::InitialState => match exclusion {
            Exclusion::ImplementationChosenHook => format!(
                "the program's initial configuration applies a hook whose value the definition \
                 leaves open and k-rust chooses ({})",
                exclusion.name()
            ),
            Exclusion::ShortCircuitReading => format!(
                "the program's initial configuration applies a function whose value depends on \
                 whether a short-circuit operator skips an operand that may be undefined, or \
                 such an operator itself, which the definition leaves to the backend ({})",
                exclusion.name()
            ),
            other => format!(
                "the program's initial configuration is excluded ({})",
                other.name()
            ),
        },
    }
}

/// Up to eight items, then how many more.
fn listed(items: impl IntoIterator<Item = String>) -> String {
    let items = items.into_iter().collect::<Vec<_>>();
    let shown = items.iter().take(8).cloned().collect::<Vec<_>>().join("; ");
    if items.len() > 8 {
        format!("{shown}; and {} more", items.len() - 8)
    } else {
        shown
    }
}

/// The sentence a list of `facts` names `name`, as data; `{name}` alone when the facts hold no
/// link for it.
fn sentence_named(facts: &DefinitionExclusions, name: &str) -> Value {
    facts
        .sentences
        .get(name)
        .map_or_else(|| json!({"name": name}), sentence_value)
}

/// The sentence a list of `facts` names `name`, as text: its label (or name) and position.
fn sentence_text(facts: &DefinitionExclusions, name: &str) -> String {
    facts
        .sentences
        .get(name)
        .map_or_else(|| name.to_owned(), sentence_link_text)
}

fn location_value(location: Option<k_rust::definition::ast::Location>) -> Value {
    location.map_or(Value::Null, |l| {
        json!({
            "start_line": l.start_line,
            "start_column": l.start_column,
            "end_line": l.end_line,
            "end_column": l.end_column,
        })
    })
}

fn sentence_value(link: &SentenceLink) -> Value {
    json!({
        "name": link.name,
        "module": link.module,
        "label": link.label,
        "id": link.id,
        "source": link.source,
        "location": location_value(link.location),
    })
}

fn symbol_value(link: &SymbolLink) -> Value {
    json!({
        "id": link.id,
        "module": link.module,
        "label": link.label,
        "hook": link.hook,
        "source": link.source,
        "location": location_value(link.location),
    })
}

/// `source:start_line:start_column-end_line:end_column`, as far as they are known; `None` with
/// neither.
fn position(
    source: Option<&str>,
    location: Option<k_rust::definition::ast::Location>,
) -> Option<String> {
    let span = location.map(|l| {
        format!(
            "{}:{}-{}:{}",
            l.start_line, l.start_column, l.end_line, l.end_column
        )
    });
    match (source, span) {
        (Some(source), Some(span)) => Some(format!("{source}:{span}")),
        (Some(source), None) => Some(source.to_owned()),
        (None, Some(span)) => Some(span),
        (None, None) => None,
    }
}

/// A sentence as text: its label, else its name, then its position.
fn sentence_link_text(link: &SentenceLink) -> String {
    let name = link.label.as_deref().unwrap_or(&link.name);
    match position(link.source.as_deref(), link.location) {
        Some(position) => format!("{name} ({position})"),
        None => name.to_owned(),
    }
}

/// A symbol as text: its K label (else its KORE name decoded), its hook, and its declaration's
/// position.
fn symbol_text(link: &SymbolLink) -> String {
    let name = link
        .label
        .clone()
        .unwrap_or_else(|| label_or_name(&link.id));
    let mut notes = Vec::new();
    if let Some(hook) = &link.hook {
        notes.push(hook.clone());
    }
    if let Some(position) = position(link.source.as_deref(), link.location) {
        notes.push(format!("declared at {position}"));
    }
    if notes.is_empty() {
        name
    } else {
        format!("{name} ({})", notes.join(", "))
    }
}

/// A term as data, printed by `reader` and cut at [`VALUE_CAP`].
fn term_value(term: &Pattern, reader: &EndReader) -> Value {
    reader.print(term, VALUE_CAP)
}

/// A term as text, printed by `reader`, cut at [`HEAD_CAP`] (an ellipsis marks the cut).
fn term_text(term: &Pattern, reader: &EndReader) -> String {
    let printed = reader.print(term, HEAD_CAP);
    let text = printed["text"].as_str().unwrap_or_default();
    if printed["truncated"] == true {
        format!("`{text}...`")
    } else {
        format!("`{text}`")
    }
}

fn part_value(part: &CausePart, reader: &EndReader) -> Value {
    match part {
        CausePart::Condition { leaf } => {
            json!({"part": "condition", "leaf": term_value(leaf, reader)})
        }
        CausePart::RightSide => json!({"part": "right-side"}),
    }
}

/// Where a link sits, as text. A condition leaf is shown only when it prints as K text: one the
/// printer refuses is long KORE, which the data holds.
fn part_text(part: &CausePart, reader: &EndReader) -> String {
    match part {
        CausePart::Condition { leaf } if reader.print(leaf, HEAD_CAP)["rendering"] == "k" => {
            format!("at its condition {}", term_text(leaf, reader))
        }
        CausePart::Condition { .. } => "at its condition".to_owned(),
        CausePart::RightSide => "in its right-hand side".to_owned(),
    }
}

const fn effect_name(effect: ShortCircuitEffect) -> &'static str {
    match effect {
        ShortCircuitEffect::Applicability => "applicability",
        ShortCircuitEffect::Result => "result",
    }
}

const fn dependence_name(dependence: ReadingDependence) -> &'static str {
    match dependence {
        ReadingDependence::Undefined => "undefined",
        ReadingDependence::Valued => "valued",
    }
}

fn operator_value(link: &OperatorLink, reader: &EndReader) -> Value {
    json!({
        "link": "operator",
        "operator": symbol_value(&link.operator),
        "position": link.position,
        "operand": term_value(&link.operand, reader),
        "term": term_value(&link.term, reader),
        "term_symbol": symbol_value(&link.term_symbol),
    })
}

/// One cause chain as data ([`definition_exclusion`]).
fn cause_value(cause: &ShortCircuitCause, reader: &EndReader) -> Value {
    let links = cause
        .links
        .iter()
        .map(|link| match link {
            CauseLink::Function {
                function,
                dependence,
                equation,
                part,
            } => json!({
                "link": "function",
                "function": symbol_value(function),
                "dependence": dependence_name(*dependence),
                "equation": sentence_value(equation),
                "part": part_value(part, reader),
            }),
            CauseLink::Operator(operator) => operator_value(operator, reader),
        })
        .collect::<Vec<_>>();
    json!({
        "rule": sentence_value(&cause.rule),
        "effect": effect_name(cause.effect),
        "part": part_value(&cause.part, reader),
        "links": links,
    })
}

/// One cause chain as text: the rule and how it depends on the reading, then each link in order,
/// from the rule to the operator.
fn cause_text(cause: &ShortCircuitCause, reader: &EndReader) -> String {
    let effect = match cause.effect {
        ShortCircuitEffect::Applicability => "whether it applies depends on the reading",
        ShortCircuitEffect::Result => {
            "its result can be undefined in k-rust's reading where a short-circuiting backend \
             gives a value"
        }
    };
    let mut text = format!(
        "rule {}: {effect}, {}",
        sentence_link_text(&cause.rule),
        part_text(&cause.part, reader)
    );
    for link in &cause.links {
        match link {
            CauseLink::Function {
                function,
                dependence,
                equation,
                part,
            } => {
                let how = match dependence {
                    ReadingDependence::Valued => "whose value depends on the reading",
                    ReadingDependence::Undefined => "which can be undefined in k-rust's reading",
                };
                text.push_str(&format!(
                    ", which applies {} {how} through its equation {} {}",
                    symbol_text(function),
                    sentence_link_text(equation),
                    part_text(part, reader)
                ));
            }
            CauseLink::Operator(operator) => text.push_str(&format!(
                ", which applies {} over its operand {} {}, which a backend may skip, where {} \
                 ({}) may be undefined",
                symbol_text(&operator.operator),
                operator.position,
                term_text(&operator.operand, reader),
                term_text(&operator.term, reader),
                symbol_text(&operator.term_symbol)
            )),
        }
    }
    text
}
