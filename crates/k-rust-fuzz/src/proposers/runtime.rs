//! The run-time dictionary: literals from the values the guards compared at run time
//! (ARCHITECTURE 8.3, amended by FZ-16). Owner: FZ-16.
//!
//! # Why the static harvest is not enough
//!
//! The dictionary's static harvest (`super::dictionary`) reads the literals written in the
//! guards. A guard that compares an input with a value the run computed has no such literal: in
//! a ledger, `A ==Int B` compares a transaction's amount `A` with the running balance `B`, which
//! depends on every earlier transaction of the same case. The value the guard needs is known
//! only once the case has run, and only for that case: the condition records
//! (`collectConditions`, G-7) hold it as the atom's other operand.
//!
//! # The pool
//!
//! The pool of a case is its comparisons ([`Compared`], `crate::score::records::comparisons`):
//! every comparison atom of a refuted record of a recorded rule whose decided truth refuted the
//! guard (false where the guard needed it true, true under a negation), with its two ground
//! `Int` or `String` operands, keyed by the rule whose guard it is, each once, the first
//! [`MAX_COMPARISONS`] in the run's order. Only refuted records are read: an atom of a guard
//! that held needs no other value.
//!
//! The pool belongs to the case that produced it, not to the campaign. Its values are relative
//! to that case's state (the balance after this case's transactions), so they are proposed only
//! as changes of that case: a value from another case's run would be another state's.
//!
//! # From a comparison to a change of the case
//!
//! Where a hole's value reaches a guard unchanged (matched into the rule and compared as it
//! is), it is one of the atom's operands; in K this correspondence is exact, since rewriting
//! moves values without re-encoding them (input-to-state correspondence, as in Redqueen,
//! ARCHITECTURE 10.2). So for a comparison `x op y` and each side, say `x`, every occurrence of
//! `x`'s value in the case's hole values, at any depth (a collection's elements, keys and map
//! values, a data value's arguments), is a candidate position, and the candidate value there is
//! the value nearest the other operand that makes the comparison hold ([`satisfying`]): `y` for
//! `==`, `<=` and `>=`, `y - 1` for `<`, `y + 1` for `>` and `=/=`, mirrored for the right side.
//! These are the pool's `±` variants: a strict comparison is passed by the neighbour of the
//! other operand, never by the operand itself. A `String` equality takes the other string; a
//! `String` disequality proposes nothing.
//!
//! A change is one candidate drawn uniformly: one position of one hole takes the value. A set
//! stays sorted and distinct and a map's keys distinct (a change that would merge two is not
//! proposed), and the proposer checks the hole's sort, constraints and size rules
//! (`values::admissible`) and draws again, up to [`MAX_ATTEMPTS`] times. An occurrence that is
//! equal by coincidence (a `0` elsewhere in the case) gives a wrong change, which costs one case
//! and is judged like any other.
//!
//! # Who draws
//!
//! The climb (`super::climb`) proposes a change of its incumbent, and the corpus
//! (`super::corpus`) a change of a kept case or of its own last case. The dictionary does not:
//! it builds each case from nothing, so it has no case whose state the values belong to.
//! Every choice is drawn from a `ChaCha20` stream of the drawing proposer's own (`climb-runtime`,
//! `corpus-runtime`), drawn from only when a pool is not empty, so a campaign whose cases record
//! no conditions proposes exactly the cases it proposed before.

use num_bigint::BigInt;
use rand::Rng as _;
use rand_chacha::ChaCha20Rng;

use crate::{
    score::{Operand, distance::Comparison, records::Compared},
    values::Value,
};

/// The most comparisons the pool of one case holds.
pub(crate) const MAX_COMPARISONS: usize = 64;

/// The most candidate changes of one case that are enumerated.
pub(crate) const MAX_CANDIDATES: usize = 256;

/// The most candidates drawn for one proposal before it is given up.
pub(crate) const MAX_ATTEMPTS: usize = 16;

/// One candidate change: occurrence `occurrence` (in [`occurrences`]'s order) of `from` in hole
/// `hole`'s value takes `to`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Candidate {
    pub(crate) hole: usize,
    pub(crate) from: Value,
    pub(crate) occurrence: usize,
    pub(crate) to: Value,
}

/// Which operand of a comparison a change replaces.
#[derive(Clone, Copy)]
enum Side {
    Left,
    Right,
}

/// The candidate changes of a case with `values` and the pool `comparisons`, in order: for each
/// comparison, each side, each hole, each occurrence; at most [`MAX_CANDIDATES`], each once.
pub(crate) fn candidates(values: &[Value], comparisons: &[Compared]) -> Vec<Candidate> {
    let mut found: Vec<Candidate> = Vec::new();
    for compared in comparisons {
        for side in [Side::Left, Side::Right] {
            let Some((from, to)) = satisfying(compared, side) else {
                continue;
            };
            for (hole, value) in values.iter().enumerate() {
                for occurrence in 0..occurrences(value, &from) {
                    if found.len() >= MAX_CANDIDATES {
                        return found;
                    }
                    let candidate = Candidate {
                        hole,
                        from: from.clone(),
                        occurrence,
                        to: to.clone(),
                    };
                    if !found.contains(&candidate) {
                        found.push(candidate);
                    }
                }
            }
        }
    }
    found
}

/// A change of `values` drawn from the pool `comparisons`: candidates drawn uniformly without
/// replacement until one gives a value that `admits` (hole index, new value) and differs from
/// the hole's value, up to [`MAX_ATTEMPTS`]; `None` when none does. Draws from `rng` only when
/// there is a candidate.
pub(crate) fn propose(
    values: &[Value],
    comparisons: &[Compared],
    rng: &mut ChaCha20Rng,
    mut admits: impl FnMut(usize, &Value) -> bool,
) -> Option<Vec<Value>> {
    let mut candidates = candidates(values, comparisons);
    for _ in 0..MAX_ATTEMPTS {
        if candidates.is_empty() {
            return None;
        }
        let candidate = candidates.swap_remove(rng.random_range(0..candidates.len()));
        let mut seen = 0;
        let Some(changed) = replace(
            &values[candidate.hole],
            &candidate.from,
            candidate.occurrence,
            &candidate.to,
            &mut seen,
        ) else {
            continue;
        };
        if changed != values[candidate.hole] && admits(candidate.hole, &changed) {
            let mut proposal = values.to_vec();
            proposal[candidate.hole] = changed;
            return Some(proposal);
        }
    }
    None
}

/// The value of `side` of `compared`, and the value nearest the other operand that makes the
/// comparison hold when it replaces that side; `None` for a `String` disequality.
fn satisfying(compared: &Compared, side: Side) -> Option<(Value, Value)> {
    use Comparison as C;
    let value = |operand: &Operand| match operand {
        Operand::Int(number) => Value::Int(number.clone()),
        Operand::Str(text) => Value::String(text.clone()),
    };
    let shifted = |operand: &Operand, offset: i8| match operand {
        Operand::Int(number) => Some(Value::Int(number + BigInt::from(offset))),
        Operand::Str(_) => None,
    };
    let (own, other) = match side {
        Side::Left => (&compared.left, &compared.right),
        Side::Right => (&compared.right, &compared.left),
    };
    // Replacing the left side solves `v op other`; replacing the right side solves `other op v`,
    // so the order comparisons turn around.
    let to = match (compared.comparison, side) {
        (C::IntEq | C::IntLe | C::IntGe | C::StrEq, _) => Some(value(other)),
        (C::IntNe, _) | (C::IntGt, Side::Left) | (C::IntLt, Side::Right) => shifted(other, 1),
        (C::IntLt, Side::Left) | (C::IntGt, Side::Right) => shifted(other, -1),
        (C::StrNe, _) => None,
    }?;
    Some((value(own), to))
}

/// How many times `needle` (an `Int` or a `String`) occurs as a value in `value`, at any depth.
pub(crate) fn occurrences(value: &Value, needle: &Value) -> usize {
    if value == needle && matches!(value, Value::Int(_) | Value::String(_)) {
        return 1;
    }
    match value {
        Value::List(items) | Value::Set(items) => {
            items.iter().map(|item| occurrences(item, needle)).sum()
        }
        Value::Map(entries) => entries
            .iter()
            .map(|(key, value)| occurrences(key, needle) + occurrences(value, needle))
            .sum(),
        Value::Apply { arguments, .. } => arguments
            .iter()
            .map(|argument| occurrences(argument, needle))
            .sum(),
        _ => 0,
    }
}

/// `value` with occurrence `target` of `needle` (counting from `*seen`, in [`occurrences`]'s
/// order) replaced by `to`; `None` when the change would merge two elements of a set or two keys
/// of a map.
fn replace(
    value: &Value,
    needle: &Value,
    target: usize,
    to: &Value,
    seen: &mut usize,
) -> Option<Value> {
    if value == needle && matches!(value, Value::Int(_) | Value::String(_)) {
        let hit = *seen == target;
        *seen += 1;
        return Some(if hit { to.clone() } else { value.clone() });
    }
    let mut each = |item: &Value| replace(item, needle, target, to, seen);
    Some(match value {
        Value::List(items) => Value::List(items.iter().map(&mut each).collect::<Option<_>>()?),
        Value::Set(items) => {
            let mut items: Vec<Value> = items.iter().map(&mut each).collect::<Option<_>>()?;
            items.sort();
            if items.windows(2).any(|pair| pair[0] == pair[1]) {
                return None;
            }
            Value::Set(items)
        }
        Value::Map(entries) => {
            let mut changed = Vec::with_capacity(entries.len());
            for (key, entry) in entries {
                let key = replace(key, needle, target, to, seen)?;
                let entry = replace(entry, needle, target, to, seen)?;
                changed.push((key, entry));
            }
            changed.sort_by(|a, b| a.0.cmp(&b.0));
            if changed.windows(2).any(|pair| pair[0].0 == pair[1].0) {
                return None;
            }
            Value::Map(changed)
        }
        Value::Apply { symbol, arguments } => Value::Apply {
            symbol: symbol.clone(),
            arguments: arguments.iter().map(&mut each).collect::<Option<_>>()?,
        },
        other => other.clone(),
    })
}

#[cfg(test)]
#[path = "runtime_tests.rs"]
mod tests;
