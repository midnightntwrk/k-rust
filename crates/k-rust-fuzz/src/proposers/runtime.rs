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
//! for each recorded rule whose records are complete, the comparison atoms of its last refuted
//! entry that lie below nodes that refuted the guard and whose own decided truth refuted it
//! (false where the guard needed it true, true under a negation), with their two ground `Int`
//! or `String` operands, keyed by the rule whose guard it is. [`pool`] orders them by the rule's
//! rule-graph distance to the target, so that the target's own comparisons come first, keeps
//! each comparison of the same operands once and at most [`MAX_COMPARISONS`]. Only refuted
//! records are read: an atom of a guard that held needs no other value.
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
//! A change is drawn by a side of a comparison (uniformly among the sides with a candidate),
//! then by occurrence: one position of one hole takes the value. Each side of a comparison is
//! one change (`x` takes the value that passes, or `y` does), so the two sides of `D ==Int C`
//! weigh as much as two comparisons with one applicable side each. Drawing by side first, with
//! at most [`MAX_OCCURRENCES`] occurrences per side, keeps a value that is common in the case (a
//! `0` in a list of records) from crowding out the other comparisons. A set stays sorted and distinct and a map's keys
//! distinct (a change that would merge two is not proposed), and the proposer checks the hole's
//! sort, constraints and size rules (`values::admissible`) and draws again, up to
//! [`MAX_ATTEMPTS`] times. The climb's incumbent remembers the candidates drawn from its pool,
//! so a change that scored worse (or was refused) is not proposed again from the same
//! incumbent; when none is left the climb makes its ordinary move. The corpus keeps no such
//! memory: a change of a kept case that reached nothing new is not kept, and only a follow-up
//! of it can finish what it started (`super::corpus`), so drawing it again is another chance. An occurrence that is equal by coincidence
//! (a `0` elsewhere in the case) gives a wrong change, which costs one case and is judged like
//! any other.
//!
//! # Who draws
//!
//! The climb (`super::climb`) proposes a change of its incumbent, and the corpus
//! (`super::corpus`) a change of a kept case or of its own last case. The dictionary does not:
//! it builds each case from nothing, so it has no case whose state the values belong to.
//! Every choice is drawn from a `ChaCha20` stream of the drawing proposer's own (`climb-runtime`,
//! `corpus-runtime`), drawn from only when a pool is not empty, so a campaign whose cases record
//! no conditions proposes exactly the cases it proposed before.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use rand::Rng as _;
use rand_chacha::ChaCha20Rng;

use crate::{
    score::{Operand, distance::Comparison, records::Compared},
    values::Value,
};

/// The most comparisons the pool of one case holds.
pub(crate) const MAX_COMPARISONS: usize = 64;

/// The most occurrences of one side of one comparison that are candidates: a value common in
/// the case (a `0` in a list of records) cannot crowd out the other comparisons, which are
/// drawn first ([`propose`]).
pub(crate) const MAX_OCCURRENCES: usize = 64;

/// The most candidates drawn for one proposal before it is given up.
pub(crate) const MAX_ATTEMPTS: usize = 16;

/// One candidate change: occurrence `occurrence` (in [`occurrences`]'s order) of `from` in hole
/// `hole`'s value takes `to`.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
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

/// The pool of a case from the comparisons its recorded guards gave
/// (`crate::score::records::comparisons`): ordered by the rank of their rule (`rank`, the
/// rule-graph distance to the target, so the target's own comparisons come first; an unranked
/// rule last), then by rule id, each comparison of the same operands once (the first, nearest
/// the target), at most [`MAX_COMPARISONS`].
pub(crate) fn pool(comparisons: &[Compared], rank: &BTreeMap<String, u64>) -> Vec<Compared> {
    let mut ordered: Vec<&Compared> = comparisons.iter().collect();
    ordered.sort_by_key(|compared| {
        (
            rank.get(&compared.rule).copied().unwrap_or(u64::MAX),
            compared.rule.as_str(),
        )
    });
    let mut pool: Vec<Compared> = Vec::new();
    for compared in ordered {
        if pool.len() >= MAX_COMPARISONS {
            break;
        }
        let same = |other: &Compared| {
            other.comparison == compared.comparison
                && other.left == compared.left
                && other.right == compared.right
        };
        if !pool.iter().any(same) {
            pool.push(compared.clone());
        }
    }
    pool
}

/// The candidate changes of a case with `values` from the pool `comparisons`, grouped by side
/// of a comparison, in the pool's order: per side, every occurrence of its value in every hole,
/// at most [`MAX_OCCURRENCES`], without those in `tried`.
fn groups(
    values: &[Value],
    comparisons: &[Compared],
    tried: &BTreeSet<Candidate>,
) -> Vec<Vec<Candidate>> {
    comparisons
        .iter()
        .flat_map(|compared| {
            [Side::Left, Side::Right]
                .into_iter()
                .filter_map(|side| satisfying(compared, side))
                .map(|(from, to)| {
                    let mut found = Vec::new();
                    'holes: for (hole, value) in values.iter().enumerate() {
                        for occurrence in 0..occurrences(value, &from) {
                            if found.len() >= MAX_OCCURRENCES {
                                break 'holes;
                            }
                            let candidate = Candidate {
                                hole,
                                from: from.clone(),
                                occurrence,
                                to: to.clone(),
                            };
                            if !tried.contains(&candidate) {
                                found.push(candidate);
                            }
                        }
                    }
                    found
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Every candidate change of a case with `values` from the pool `comparisons`, in the order of
/// [`groups`], each once.
#[cfg(test)]
pub(crate) fn candidates(values: &[Value], comparisons: &[Compared]) -> Vec<Candidate> {
    let mut found: Vec<Candidate> = Vec::new();
    for candidate in groups(values, comparisons, &BTreeSet::new())
        .into_iter()
        .flatten()
    {
        if !found.contains(&candidate) {
            found.push(candidate);
        }
    }
    found
}

/// A change of `values` drawn from the pool `comparisons`, skipping the candidates in `tried`:
/// a side of a comparison drawn uniformly among those with a candidate left, then one
/// occurrence, without replacement, until one gives a value that `admits` (hole index, new
/// value) and differs from the hole's value, up to [`MAX_ATTEMPTS`]; `None` when none does.
/// Every candidate drawn joins `tried`, so a case's pool does not propose the same change twice.
/// Draws from `rng` only when there is a candidate.
pub(crate) fn propose(
    values: &[Value],
    comparisons: &[Compared],
    tried: &mut BTreeSet<Candidate>,
    rng: &mut ChaCha20Rng,
    mut admits: impl FnMut(usize, &Value) -> bool,
) -> Option<Vec<Value>> {
    let mut groups = groups(values, comparisons, tried);
    for _ in 0..MAX_ATTEMPTS {
        groups.retain(|occurrences| !occurrences.is_empty());
        if groups.is_empty() {
            return None;
        }
        let index = rng.random_range(0..groups.len());
        let occurrences = &mut groups[index];
        let index = rng.random_range(0..occurrences.len());
        let candidate = occurrences.swap_remove(index);
        tried.insert(candidate.clone());
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
