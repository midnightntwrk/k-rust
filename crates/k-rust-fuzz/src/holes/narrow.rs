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
//! magnitude, and whether that reads back as the negative integer depends on how the grammar
//! reads a leading `-` there: a signed integer token (`INT-SYNTAX`'s `-3`) reads it as part of
//! the literal; a grammar of unsigned literals (`UNSIGNED-INT-SYNTAX`) either reads it as a
//! unary minus applied to the magnitude, an application rather than the domain value, or does
//! not parse it at all. In both of the latter cases no negative value can ever give a case that
//! runs, so drawing one only spends budget on a `rejected` case.
//!
//! Each `Int` span hole whose bounds admit a negative value, and whose anchor is not itself
//! negative (a negative anchor already round-tripped at the position), is probed once, at
//! campaign construction, with the admissible negative value nearest zero: the program is
//! assembled with that value at the hole and every other hole at its anchor, and checked by the
//! same round-trip check every case runs, at the same position. When the probe is refused, the
//! hole's generation bounds start at 0. The probe is the per-case judgement itself, so it is
//! exact for the probed value at this position; that the other negative values share its fate
//! rests on the grammar reading the leading `-` alike before every digit string, which holds
//! for every token or production that reads a sign. A grammar whose reading of `-` depended on
//! the digits that follow would need a probe per magnitude; the report records every narrowing
//! (with the probe's text and what the configuration held instead) so that a reader sees why a
//! range narrowed.
//!
//! Not narrowed: configuration-variable holes, whose value replaces a whole binding parsed at
//! the variable's sort rather than a literal inside program text; KORE-template holes, whose
//! values are substituted as KORE and never printed into a text; holes with a choice set, whose
//! values the author listed one by one. Other printed sorts (`MInt`, `String`, `Bytes`) are not
//! probed: their printed forms vary in more than one way (width suffixes, escapes), so one probe
//! would not decide a whole class of values.

use num_bigint::{BigInt, Sign};
use num_traits::Zero;

use super::{
    HoleSite, PrintedValue, ResolvedHoles, RoundTripCheck, instantiate,
    position::{anchor_printed, printed},
};
use crate::{
    assemble::ProgramAssembly,
    error::CampaignError,
    spec::{CompiledDefinition, ProgramInput},
    values::{Constraints, IntRange, Value, ValueSort},
};

/// Why a hole's generation bounds are narrower than its declared constraints.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Narrowing {
    /// The probed value, as K text (`-1`).
    pub(crate) probe: String,
    /// The definition whose grammar refused the probe: `baseline` or `mutant`.
    pub(crate) side: &'static str,
    /// What refused it: the subterm the configuration held at the hole's position instead, as
    /// KORE text, or why the program did not assemble.
    pub(crate) found: String,
}

impl Narrowing {
    /// The narrowing as one sentence, for the report and its warning.
    pub(crate) fn reason(&self) -> String {
        format!(
            "a negative value written at the hole's position does not parse back to itself on \
             the {}: `{}` gives {}",
            self.side, self.probe, self.found
        )
    }
}

/// The negative value a hole is probed with, or `None` when it is not probed (see the module
/// documentation): an `Int` span hole without choices whose anchor is not negative and whose
/// constraints admit a negative value. The probe is the admissible negative value nearest zero.
fn probe_value(hole: &super::ResolvedHole) -> Option<BigInt> {
    if !matches!(hole.site, HoleSite::Span { .. })
        || hole.sort != ValueSort::Int
        || hole.constraints.choices.is_some()
        || hole.narrowing.is_some()
    {
        return None;
    }
    if let Some(Value::Int(anchor)) = &hole.anchor
        && anchor.sign() == Sign::Minus
    {
        return None;
    }
    let range = hole.constraints.range.clone().unwrap_or_default();
    let probe = match &range.max {
        Some(max) if *max < BigInt::from(-1) => max.clone(),
        _ => BigInt::from(-1),
    };
    let admitted = range.min.as_ref().is_none_or(|min| *min <= probe)
        && range.max.as_ref().is_none_or(|max| probe <= *max);
    admitted.then_some(probe)
}

/// Probe every hole of `holes` that [`probe_value`] selects against `side`'s grammar: assemble
/// `program` with the probe at the hole and every other hole at its anchor, then round-trip
/// check the configuration with `check`, the side's own check. Returns, in the order of the
/// holes, the narrowing of each hole whose probe was refused.
///
/// # Errors
///
/// [`CampaignError::AnchorDoesNotParse`] when an anchor has no printed form (which
/// [`RoundTripCheck::new`] already refused, so this does not happen after it).
pub(crate) fn probe(
    holes: &ResolvedHoles,
    check: &RoundTripCheck,
    assembly: &ProgramAssembly,
    definition: &CompiledDefinition,
    program: &ProgramInput,
    side: &'static str,
) -> Result<Vec<Option<Narrowing>>, CampaignError> {
    let probes: Vec<Option<BigInt>> = holes.holes.iter().map(probe_value).collect();
    if probes.iter().all(Option::is_none) {
        return Ok(vec![None; holes.holes.len()]);
    }
    let anchors = holes
        .holes
        .iter()
        .map(anchor_printed)
        .collect::<Result<Vec<PrintedValue>, _>>()?;
    let mut assembler = assembly.assembler(definition);
    let mut narrowings = Vec::with_capacity(holes.holes.len());
    for (index, (hole, value)) in holes.holes.iter().zip(probes).enumerate() {
        let Some(value) = value else {
            narrowings.push(None);
            continue;
        };
        let value = Value::Int(value);
        let Ok(printed) = printed(&value, hole) else {
            // An `Int` always prints; a value without a printed form is not a refusal of the
            // syntax.
            narrowings.push(None);
            continue;
        };
        let text = printed.k_text.clone().unwrap_or_default();
        let mut values = anchors.clone();
        values[index] = printed;
        let found = match assembler.assemble(&instantiate(program, holes, &values)) {
            Err(error) => Some(format!("a program that does not parse: {}", error.message)),
            Ok(configuration) => check
                .check(&configuration, &values)
                .err()
                .map(|failure| format!("`{}` at the hole's position", failure.found)),
        };
        narrowings.push(found.map(|found| Narrowing {
            probe: text,
            side,
            found,
        }));
    }
    Ok(narrowings)
}

impl ResolvedHoles {
    /// Narrow the generation bounds of each hole that `narrowings` (from [`probe`], in the order
    /// of the holes) gives a narrowing: its range starts at 0. A hole already narrowed keeps its
    /// first narrowing.
    ///
    /// # Errors
    ///
    /// [`CampaignError::InvalidConstraints`] for a hole whose declared range holds only negative
    /// values: no value of it can be written at the hole.
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
                return Err(CampaignError::InvalidConstraints {
                    hole: hole.decl.name.clone(),
                    message: format!(
                        "every value of its range is negative, and {}",
                        narrowing.reason()
                    ),
                });
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
