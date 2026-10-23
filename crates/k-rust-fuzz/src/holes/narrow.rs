//! Generation bounds narrowed to what the program's syntax can hold at a hole (FZ-INTGEN).
//!
//! A span hole replaces a literal of the program text with each case's value printed as K
//! text, and a case counts only when that text parses back, at the hole's position, to the
//! value intended (the round-trip check, ARCHITECTURE 2.3). The values a span hole can denote
//! are therefore exactly the values whose printed text the grammar reads back as that value at
//! that position, a property of the grammar at the position, not of the hole's sort.
//!
//! For an `Int` hole the property splits by sign. A non-negative integer prints as its digits,
//! and the anchor, which is written there, already showed that digits are read back as an
//! integer at the position. A negative integer prints as `-` followed by the digits of its
//! magnitude. A signed integer token (`INT-SYNTAX`'s `[\+\-]?[0-9]+`) reads that text as the
//! negative integer; under unsigned literals (`UNSIGNED-INT-SYNTAX`) it reads as a unary minus
//! applied to the magnitude, an application rather than the domain value, or does not parse.
//! Under unsigned literals no negative value can ever give a case that runs, so drawing one only
//! spends budget on a `rejected` case.
//!
//! Each `Int` span hole whose bounds admit a negative value, and whose anchor is not itself
//! negative (a negative anchor already round-tripped at the position), is probed at campaign
//! construction with two admissible negative values of different digit strings: the one nearest
//! zero (`-1`, or the range's maximum), and the one of greatest magnitude with at most three
//! digits (`-999`, or the range's minimum; the minimum itself when no such value is admissible).
//! Each probe assembles the program with the value at the hole and every other hole at its
//! anchor, and runs the same round-trip check every case runs, at the same position. Only when
//! every probe is refused do the hole's generation bounds start at 0.
//!
//! What the probes establish is exact for the probed values only: each is refused at this
//! position. They do not establish that every other negative value is refused. A grammar may
//! spell some negative literals as terminals of their own (a production `"-1"` beside signed
//! literals), or read a sign only before some digit strings; two probes of different lengths
//! make such a collision unlikely to decide a narrowing, but no finite set of probes rules it
//! out without reading the token definitions, which this module does not do. Narrowing is
//! therefore an economy of the generators, not a judgement: the declared constraints and the
//! per-case round-trip check stay the judges of every case (an explicit negative value is still
//! run), and the report records every narrowing with its probes and what the grammar made of
//! them.
//!
//! Not narrowed: configuration-variable holes, whose value replaces a whole binding parsed at
//! the variable's sort rather than a literal inside program text; KORE-template holes, whose
//! values are substituted as KORE and never printed into a text; holes with a choice set, whose
//! values the author listed one by one. Other printed sorts (`MInt`, `String`, `Bytes`) are not
//! probed: their printed forms vary in more than one way (width suffixes, escapes), so a few
//! probes would not decide a whole class of values.

use num_bigint::{BigInt, Sign};
use num_traits::Zero;

use super::{
    HoleSite, PrintedValue, ResolvedHole, ResolvedHoles, RoundTripCheck, instantiate,
    position::{anchor_printed, printed},
};
use crate::{
    assemble::ProgramAssembly,
    error::CampaignError,
    report::{DefinitionRole, EffectiveConstraints, NarrowingProbe, NarrowingReason, ProbeOutcome},
    spec::{CompiledDefinition, ProgramInput},
    values::{Constraints, IntRange, TextSyntax, Value, ValueSort},
};

/// The longest parser message a warning quotes.
const MESSAGE_LIMIT: usize = 200;

/// Why a hole's generation bounds are narrower than its declared constraints: every probe was
/// refused.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Narrowing {
    /// The definition whose grammar refused the probes.
    pub(crate) side: DefinitionRole,
    /// Every probe, in the order tried.
    pub(crate) probes: Vec<Probe>,
}

/// One refused probe.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Probe {
    /// The value written at the hole, as K text (`-1`).
    pub(crate) text: String,
    /// What the grammar made of it.
    pub(crate) refusal: Refusal,
}

/// How the grammar refused a probe.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Refusal {
    /// The program parsed, and the hole's position held this term instead: K text when the
    /// definition prints it, otherwise its KORE (cut at 200 bytes).
    ReadsAs(String),
    /// The program did not parse; the parser's message, for the warning only (its text may
    /// depend on the process environment, so the report's identity does not hold it).
    DoesNotParse(String),
}

impl Narrowing {
    /// The report's record of this narrowing of `hole`: a function of the campaign's inputs.
    pub(crate) fn record(&self, hole: &ResolvedHole) -> EffectiveConstraints {
        EffectiveConstraints {
            hole: hole.decl.name.clone(),
            declared: hole.decl.constraints.clone(),
            effective: hole.constraints.clone(),
            reason: NarrowingReason::NegativeNotReadBack,
            side: self.side,
            probes: self
                .probes
                .iter()
                .map(|probe| match &probe.refusal {
                    Refusal::ReadsAs(term) => NarrowingProbe {
                        value: probe.text.clone(),
                        outcome: ProbeOutcome::ReadsAs,
                        reads_as: Some(term.clone()),
                    },
                    Refusal::DoesNotParse(_) => NarrowingProbe {
                        value: probe.text.clone(),
                        outcome: ProbeOutcome::DoesNotParse,
                        reads_as: None,
                    },
                })
                .collect(),
        }
    }

    /// What the probes showed, as one clause: "on the baseline, `-1` reads as `- 1` and `-999`
    /// reads as `- 999`".
    fn evidence(&self) -> String {
        let side = match self.side {
            DefinitionRole::Baseline => "baseline",
            DefinitionRole::Mutant => "mutant",
        };
        let probes = self
            .probes
            .iter()
            .map(|probe| match &probe.refusal {
                Refusal::ReadsAs(term) => format!("`{}` reads as `{term}`", probe.text),
                Refusal::DoesNotParse(message) => {
                    format!("`{}` does not parse ({message})", probe.text)
                }
            })
            .collect::<Vec<_>>()
            .join(" and ");
        format!("on the {side}, {probes}")
    }

    /// The report's warning for `hole`, narrowed by this: what happened, why, and what to do.
    pub(crate) fn warning(&self, hole: &ResolvedHole) -> String {
        let declared = hole
            .decl
            .constraints
            .range
            .as_ref()
            .and_then(|range| range.min.as_ref())
            .map_or_else(|| "no minimum".to_owned(), |min| format!("minimum {min}"));
        format!(
            "hole `{}`: values are generated from 0 (declared: {declared}), since no negative \
             integer probed at the hole reads back as itself ({}). To fuzz negative values, \
             write the program with a unary minus before the literal (`- 5`) if the language \
             has one, and keep the hole on the digits; to silence this warning, declare \
             `range = {{ min = 0 }}`.",
            hole.decl.name,
            self.evidence()
        )
    }

    /// The refusal of a hole whose declared range holds only negative values.
    fn refusal(&self, hole: &ResolvedHole) -> CampaignError {
        CampaignError::InvalidConstraints {
            hole: hole.decl.name.clone(),
            message: format!(
                "every value of its range is negative, and no negative integer probed at the \
                 hole reads back as itself ({}). If the language has a unary minus, write the \
                 program with it before the literal (`- 5`), keep the hole on the digits and \
                 declare the range of the magnitude.",
                self.evidence()
            ),
        }
    }
}

/// The negative values a hole is probed with, empty when it is not probed (see the module
/// documentation): an `Int` span hole without choices whose anchor is not negative and whose
/// constraints admit a negative value. The first is the admissible negative value nearest zero;
/// the second, when it differs, the admissible negative value of greatest magnitude with at most
/// three digits, or the range's minimum when no such value is admissible.
fn probe_values(hole: &ResolvedHole) -> Vec<BigInt> {
    if !matches!(hole.site, HoleSite::Span { .. })
        || hole.sort != ValueSort::Int
        || hole.constraints.choices.is_some()
        || hole.narrowing.is_some()
    {
        return Vec::new();
    }
    if let Some(Value::Int(anchor)) = &hole.anchor
        && anchor.sign() == Sign::Minus
    {
        return Vec::new();
    }
    let range = hole.constraints.range.clone().unwrap_or_default();
    let admitted = |value: &BigInt| {
        *value < BigInt::zero()
            && range.min.as_ref().is_none_or(|min| min <= value)
            && range.max.as_ref().is_none_or(|max| value <= max)
    };
    let nearest = match &range.max {
        Some(max) if *max < BigInt::from(-1) => max.clone(),
        _ => BigInt::from(-1),
    };
    if !admitted(&nearest) {
        return Vec::new();
    }
    let short = match &range.min {
        Some(min) if *min > BigInt::from(-999) => min.clone(),
        _ => BigInt::from(-999),
    };
    let far = if admitted(&short) {
        short
    } else {
        // Every admissible value has more than three digits: the range's minimum, or one past
        // the nearest value when the range has none.
        range.min.clone().unwrap_or_else(|| &nearest - 1u8)
    };
    let mut values = vec![nearest];
    if far != values[0] {
        values.push(far);
    }
    values
}

/// Probe every hole of `holes` that [`probe_values`] selects against `side`'s grammar: assemble
/// `program` with each probe at the hole and every other hole at its anchor, then round-trip
/// check the configuration with `check`, the side's own check. `text` is the side's K-text
/// syntax, which prints what the position held instead. Returns, in the order of the holes, the
/// narrowing of each hole whose probes were all refused.
///
/// # Errors
///
/// [`CampaignError::AnchorDoesNotParse`] when an anchor has no printed form (which
/// [`RoundTripCheck::new`] already refused, so this does not happen after it).
pub(crate) fn probe(
    holes: &ResolvedHoles,
    text: Option<&TextSyntax>,
    check: &RoundTripCheck,
    assembly: &ProgramAssembly,
    definition: &CompiledDefinition,
    program: &ProgramInput,
    side: DefinitionRole,
) -> Result<Vec<Option<Narrowing>>, CampaignError> {
    let probes: Vec<Vec<BigInt>> = holes.holes.iter().map(probe_values).collect();
    if probes.iter().all(Vec::is_empty) {
        return Ok(vec![None; holes.holes.len()]);
    }
    let anchors = holes
        .holes
        .iter()
        .map(anchor_printed)
        .collect::<Result<Vec<PrintedValue>, _>>()?;
    let mut assembler = assembly.assembler(definition);
    let mut narrowings = Vec::with_capacity(holes.holes.len());
    for (index, (hole, values)) in holes.holes.iter().zip(probes).enumerate() {
        let mut refused = Vec::new();
        for value in &values {
            let Ok(printed) = printed(&Value::Int(value.clone()), hole) else {
                // An `Int` always prints; a value without a printed form is not a refusal of
                // the syntax.
                break;
            };
            let written = printed.k_text.clone().unwrap_or_default();
            let mut case = anchors.clone();
            case[index] = printed;
            let refusal = match assembler.assemble(&instantiate(program, holes, &case)) {
                Err(error) => Some(Refusal::DoesNotParse(first_line(&error.message))),
                Ok(configuration) => check.check(&configuration, &case).err().map(|failure| {
                    let shown = failure
                        .held
                        .as_ref()
                        .and_then(|term| text.and_then(|text| text.show(term)));
                    Refusal::ReadsAs(shown.unwrap_or(failure.found))
                }),
            };
            match refusal {
                Some(refusal) => refused.push(Probe {
                    text: written,
                    refusal,
                }),
                None => break,
            }
        }
        let all_refused = !values.is_empty() && refused.len() == values.len();
        narrowings.push(all_refused.then_some(Narrowing {
            side,
            probes: refused,
        }));
    }
    Ok(narrowings)
}

/// The first line of `message`, cut at [`MESSAGE_LIMIT`] bytes.
fn first_line(message: &str) -> String {
    let line = message.lines().next().unwrap_or_default();
    if line.len() <= MESSAGE_LIMIT {
        return line.to_owned();
    }
    let mut cut = MESSAGE_LIMIT;
    while !line.is_char_boundary(cut) {
        cut -= 1;
    }
    format!("{}…", &line[..cut])
}

impl ResolvedHoles {
    /// Narrow the generation bounds of each hole that `narrowings` (from [`probe`], in the order
    /// of the holes) gives a narrowing: its range starts at 0. A hole already narrowed keeps its
    /// first narrowing.
    ///
    /// # Errors
    ///
    /// [`CampaignError::InvalidConstraints`] for a hole whose declared range holds only negative
    /// values, each probe of which was refused.
    pub(crate) fn narrow(
        &mut self,
        narrowings: Vec<Option<Narrowing>>,
    ) -> Result<(), CampaignError> {
        for (hole, narrowing) in self.holes.iter_mut().zip(narrowings) {
            let Some(narrowing) = narrowing else {
                continue;
            };
            if hole.narrowing.is_some() {
                continue;
            }
            let range = hole.constraints.range.clone().unwrap_or_default();
            if range.max.as_ref().is_some_and(|max| *max < BigInt::zero()) {
                return Err(narrowing.refusal(hole));
            }
            hole.constraints = Constraints {
                range: Some(IntRange {
                    min: Some(BigInt::zero()),
                    max: range.max,
                }),
                ..hole.constraints.clone()
            };
            hole.narrowing = Some(narrowing);
        }
        Ok(())
    }
}
