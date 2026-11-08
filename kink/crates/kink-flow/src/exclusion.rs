//! What a definition exclusion is and why it holds, as every command reports it: one formatter
//! for `check`, `coverage` and `run`, whose `detail` `fuzz` gives too.
//!
//! A definition exclusion (kink-native `DefinitionExclusions::definition_exclusion`) excludes
//! every run on the definition, so no program can be judged on it. kink-native records, for each
//! exclusion, the sentences that make it hold. This module prints them, as data
//! ([`definition_exclusion`]) and as one text ([`detail`]), and says why a program's baseline run
//! is excluded before it runs ([`program_detail`]).
//!
//! The short-circuit reading is no definition exclusion: a run of a definition whose analysis
//! flags a rule is judged by k-rust's `shortCircuitReadings` list of that run (kink-native
//! `DefinitionExclusions::run_exclusion`). The analysis records the cause chain of each rule it
//! flags (`ShortCircuitCause`): the rule, the part of it where the dependence shows, every
//! function applied with the equation through which it depends on the reading, and the
//! short-circuit operator with the operand a backend may skip and the term in it that may be
//! undefined. [`short_circuit`] prints them as the places where a run can read such an operand,
//! and [`readings_value`] and [`readings_text`] print the entries of a run's list that exclude
//! it, the step that did.
//!
//! Every term is printed as K text by the command's [`EndReader`], cut at [`VALUE_CAP`]
//! characters in the data and at [`HEAD_CAP`] in the text; a term the printer refuses is printed
//! as KORE, as kill evidence prints it (the text leaves out such a condition leaf, which the data
//! holds). A run's reading is printed as KORE text, cut the same way: it is one instance of the
//! operand, and the mutant's runs have no reader of their own. A position is the `Source` and
//! `Location` attributes the compiled sentence or symbol declaration carries: the file as the
//! load named it, and the span `start_line:start_column-end_line:end_column`.

use crate::{
    admit::AdmittedSpec,
    evidence::{EndReader, HEAD_CAP, VALUE_CAP},
};
use k_rust::{
    backend::{ObservedInOutput, ReadingOutcomeOutput, ShortCircuitReadingOutput},
    kast::identifier::label_or_name,
    kore::ast::Pattern,
};
use kink_native::coverage::{Authorship, RuleAuthors};
use kink_native::exclusion::{
    CauseLink, CausePart, DefinitionExclusions, Exclusion, OperatorLink, ReadingDependence,
    SentenceLink, ShortCircuitCause, ShortCircuitEffect, SymbolLink,
};
use serde_json::{Value, json};
use std::collections::BTreeSet;

/// The most causes [`detail`] names; the data lists every one.
pub const DETAIL_CAUSES: usize = 8;

/// Where an exclusion of every run of a program on the baseline comes from, as admission reads it
/// without running a step of the program (`crate::admit::ProgramExclusion`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExclusionScope {
    /// The specification's definition exclusion, which excludes every run on it.
    Definition,
    /// The exclusion of the program's initial configuration (kink-native
    /// `DefinitionExclusions::state_exclusion`): it applies an implementation-chosen hook, or a
    /// function or operator whose value depends on the short-circuit reading where its
    /// normalization, the depth-0 run, lists a reading that counts against it.
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

/// The definition exclusion of `spec` as data: null when there is none, else
/// `{exclusion, detail, causes}`, where `exclusion` is its name, `detail` is [`detail`]'s text and
/// `causes` lists what makes it hold:
///
/// - `implementation-chosen-hook`: `{sentence, symbol, hook}` per reference;
/// - `equals-condition`: `{sentence}` per sentence;
/// - `load-stack-stop`: none (`detail` gives the count).
///
/// A sentence is `{name, module, label, id, source, location, authors}` (`id` its compiled
/// `UNIQUE_ID`, `module` its KORE module), where `authors` lists the baseline sentences it was
/// compiled from (kink-native `RuleAuthors`), each named as every document names a rule
/// (`crate::results::sentence_value`: `{module, index, label, file, start_line, end_line}`, the
/// object [`crate::names::visit_rules`] visits), empty for a sentence that no baseline sentence
/// wrote (one a compiler pass generated) or with no compiled id; a symbol `{id, module, label, hook, source, location}` (`id` its KORE name), a location
/// `{start_line, start_column, end_line, end_column}`, and a part `{part: "condition", leaf}` or
/// `{part: "right-side"}`. A term (`leaf`, `operand`, `term`) is printed
/// `{text, rendering, truncated}` (and `note`), as kill evidence prints a value.
#[must_use]
pub fn definition_exclusion(spec: &AdmittedSpec, reader: &EndReader) -> Value {
    let facts = &spec.exclusions;
    let Some(exclusion) = facts.definition_exclusion() else {
        return Value::Null;
    };
    let authors = RuleAuthors::of(&spec.compiled);
    let links = Links {
        spec,
        authors: &authors,
    };
    let sentence = |name: &str| links.named(facts, name);
    let causes = match exclusion {
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
        Exclusion::ShortCircuitReading => format!(
            "a rule's applicability or result depends on whether andBool, orBool, impliesBool, \
             #if, andThenBool or orElseBool skip an operand that may be undefined, which the \
             definition leaves to the backend: {}",
            causes_text(facts, reader)
        ),
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

/// Each flagged rule's cause chain as text (at most [`DETAIL_CAUSES`]; the data lists every
/// one), then any rule a list names without a cause.
fn causes_text(facts: &DefinitionExclusions, reader: &EndReader) -> String {
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
    // A rule a list names without a cause (none, as kink-native builds the lists) is still
    // named, by its sentence.
    let uncaused = facts
        .short_circuit_conditions
        .iter()
        .chain(&facts.short_circuit_results)
        .filter(|name| !named.contains(*name))
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut text = shown.join("; ");
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

/// The rules the short-circuit analysis flags on `spec`'s definition, as data: null when it
/// flags none (kink-native `DefinitionExclusions::short_circuit_flagged`), else `{detail,
/// causes}`. No run is excluded for them as such: each run of a flagged definition is judged by
/// k-rust's `shortCircuitReadings` list of that run, and only a run whose list holds an entry
/// that counts is `short-circuit-reading` (its row names the entry, [`readings_value`]). The
/// flagged rules are where a run can read the definedness of an operand a short-circuiting
/// backend may skip, so a program is best written so that its runs read none there.
///
/// `causes` holds each flagged rule's cause chain, `{rule, effect, part, links}`: `rule` a
/// sentence; `effect` `applicability` (whether the rule applies can differ between the
/// readings) or `result` (its result can be undefined in k-rust's reading where a
/// short-circuiting backend gives a value); `part` where in the rule the first link sits; and
/// `links` in order from the rule, each `{link: "function", function, dependence, equation,
/// part}` (`dependence` `valued` or `undefined`) or `{link: "operator", operator, position,
/// operand, term, term_symbol}`. Sentences, symbols, parts and terms are printed as
/// [`definition_exclusion`] prints them; `detail` names the chains in one text, with positions.
#[must_use]
pub fn short_circuit(spec: &AdmittedSpec, reader: &EndReader) -> Value {
    let facts = &spec.exclusions;
    if !facts.short_circuit_flagged() {
        return Value::Null;
    }
    let authors = RuleAuthors::of(&spec.compiled);
    let links = Links {
        spec,
        authors: &authors,
    };
    json!({
        "detail": format!(
            "the short-circuit analysis flags rules whose applicability or result can depend on \
             whether andBool, orBool, impliesBool, #if, andThenBool or orElseBool skip an operand \
             that may be undefined, which the definition leaves to the backend; a run is \
             excluded (short-circuit-reading) only when k-rust lists such a reading of it that \
             counts, and every other run is judged: {}",
            causes_text(facts, reader)
        ),
        "causes": facts
            .short_circuit_causes
            .iter()
            .map(|cause| cause_value(cause, &links, reader))
            .collect::<Vec<_>>(),
    })
}

/// A run's readings that exclude it (kink-native
/// `DefinitionExclusions::counting_short_circuit_readings`, or the entries the campaign runner's
/// notes of the run carry) as data: each `{operator, outcome, head, operand, rule, observed_in}`.
/// `operator` is the hook of the short-circuit operator whose operand after the deciding one
/// k-rust read (`BOOL.andThen`, `KEQUAL.ite`, ...), null where the reading is a deferred
/// definedness atom's decision, which does not know its operator; `outcome` is `undefined`
/// (k-rust found the operand `\bottom`) or `undecided` (it kept the operand's definedness as an
/// open condition); `head` the KORE symbol at the operand's root, or null; `operand` one instance
/// of it as KORE text, `{text, rendering: "kore", truncated}`, cut at [`VALUE_CAP`]; `rule` the
/// rewrite rule whose work read it, `{id, label, source, location}` (k-rust's `rewriteRule*`),
/// null for work of no rule (the initial state's normalization, a step's remainder, a leaf's
/// constraints, the load); and `observed_in` `run` or `load`.
#[must_use]
pub fn readings_value(readings: &[ShortCircuitReadingOutput<Pattern>]) -> Value {
    Value::Array(
        readings
            .iter()
            .map(|reading| {
                let (text, truncated) = operand_text(reading, VALUE_CAP);
                json!({
                    "operator": reading.operator,
                    "outcome": outcome_name(reading.outcome),
                    "head": reading.head,
                    "operand": {"text": text, "rendering": "kore", "truncated": truncated},
                    "rule": reading_rule(reading).map_or(Value::Null, |_| json!({
                        "id": reading.rewrite_rule_id,
                        "label": reading.rewrite_rule_label,
                        "source": reading.rewrite_rule_origin.as_ref().and_then(|o| o.source.clone()),
                        "location": reading.rewrite_rule_origin.as_ref().and_then(|o| o.location.clone()),
                    })),
                    "observed_in": observed_name(reading.observed_in),
                })
            })
            .collect(),
    )
}

/// A run's readings that exclude it ([`readings_value`]) as one text: for each, the step that
/// read it (the rule, else where the work was), the operator, the outcome and the operand (cut at
/// [`HEAD_CAP`]); at most [`DETAIL_CAUSES`], then how many more.
#[must_use]
pub fn readings_text(readings: &[ShortCircuitReadingOutput<Pattern>]) -> String {
    let mut text = readings
        .iter()
        .take(DETAIL_CAUSES)
        .map(|reading| {
            let (operand, truncated) = operand_text(reading, HEAD_CAP);
            let operand = if truncated {
                format!("`{operand}...`")
            } else {
                format!("`{operand}`")
            };
            let what = reading.operator.as_deref().map_or_else(
                || format!("a deferred definedness atom's subject {operand}"),
                |operator| format!("the operand of {operator} after its deciding one, {operand},"),
            );
            let outcome = match reading.outcome {
                ReadingOutcomeOutput::Undefined => "undefined",
                ReadingOutcomeOutput::Undecided => "of undecided definedness",
            };
            let place = match (reading_rule(reading), reading.observed_in) {
                (Some(rule), _) => format!("the work of rule {rule}"),
                (None, ObservedInOutput::Load) => "the definition's load".to_owned(),
                (None, ObservedInOutput::Run) => "work of no rule (the initial state's \
                                                  normalization, a step's remainder or a leaf's \
                                                  constraints)"
                    .to_owned(),
            };
            format!("in {place}, k-rust found {what} {outcome}")
        })
        .collect::<Vec<_>>()
        .join("; ");
    if readings.len() > DETAIL_CAUSES {
        text.push_str(&format!(
            "; and {} more reading(s)",
            readings.len() - DETAIL_CAUSES
        ));
    }
    text
}

/// The rule of a reading as text: its label, else its id, then its source position; `None` for
/// work of no rule.
fn reading_rule(reading: &ShortCircuitReadingOutput<Pattern>) -> Option<String> {
    let name = reading
        .rewrite_rule_label
        .clone()
        .or_else(|| reading.rewrite_rule_id.clone())?;
    let origin = reading.rewrite_rule_origin.as_ref();
    let position = match (
        origin.and_then(|o| o.source.as_deref()),
        origin.and_then(|o| o.location.as_deref()),
    ) {
        (Some(source), Some(location)) => Some(format!("{source}:{location}")),
        (Some(source), None) => Some(source.to_owned()),
        (None, Some(location)) => Some(location.to_owned()),
        (None, None) => None,
    };
    Some(match position {
        Some(position) => format!("{name} ({position})"),
        None => name,
    })
}

/// The operand of a reading as KORE text cut at `cap` characters, and whether it was cut.
fn operand_text(reading: &ShortCircuitReadingOutput<Pattern>, cap: usize) -> (String, bool) {
    let text = reading.operand.to_string();
    if text.chars().count() > cap {
        (text.chars().take(cap).collect(), true)
    } else {
        (text, false)
    }
}

const fn outcome_name(outcome: ReadingOutcomeOutput) -> &'static str {
    match outcome {
        ReadingOutcomeOutput::Undefined => "undefined",
        ReadingOutcomeOutput::Undecided => "undecided",
    }
}

const fn observed_name(observed: ObservedInOutput) -> &'static str {
    match observed {
        ObservedInOutput::Run => "run",
        ObservedInOutput::Load => "load",
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
                 such an operator itself, which the definition leaves to the backend, and the \
                 list of short-circuit readings of its normalization holds one that counts, or \
                 the backend lists none ({})",
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

/// How the data names a compiled sentence: with the baseline sentences it was compiled from.
struct Links<'s> {
    spec: &'s AdmittedSpec,
    authors: &'s RuleAuthors,
}

impl Links<'_> {
    /// The sentence a list of `facts` names `name`, as data; `{name}` alone when the facts hold
    /// no link for it.
    fn named(&self, facts: &DefinitionExclusions, name: &str) -> Value {
        facts
            .sentences
            .get(name)
            .map_or_else(|| json!({"name": name}), |link| self.sentence(link))
    }

    /// A compiled sentence as data ([`definition_exclusion`]).
    fn sentence(&self, link: &SentenceLink) -> Value {
        let authors = match link.id.as_deref().and_then(|id| self.authors.get(id)) {
            Some(Authorship::Sentences(sentences)) => sentences
                .iter()
                .map(|at| crate::results::sentence_value(self.spec, at))
                .collect(),
            Some(Authorship::Unmapped(_)) | None => Vec::new(),
        };
        json!({
            "name": link.name,
            "module": link.module,
            "label": link.label,
            "id": link.id,
            "source": link.source,
            "location": location_value(link.location),
            "authors": authors,
        })
    }
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
fn cause_value(cause: &ShortCircuitCause, names: &Links<'_>, reader: &EndReader) -> Value {
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
                "equation": names.sentence(equation),
                "part": part_value(part, reader),
            }),
            CauseLink::Operator(operator) => operator_value(operator, reader),
        })
        .collect::<Vec<_>>();
    json!({
        "rule": names.sentence(&cause.rule),
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
