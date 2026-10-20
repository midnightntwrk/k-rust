//! Shrinking a confirmed witness (ARCHITECTURE 7). Owner: FZ-06.
//!
//! Blindly generated values shrink along their proptest value trees, which stay inside the
//! hole's sort and constraints. Other values (anchors, explicit assignments) shrink by integer
//! moves towards the admissible value nearest zero and by length moves towards the shortest
//! admissible prefix, each a bisection between the last candidate that still hit and the
//! target. Every candidate goes through the caller's test, which confirms it; a candidate is
//! kept only when the test says it still hits.

use num_bigint::{BigInt, BigUint};
use num_traits::{Signed as _, Zero as _};

use super::proposer::ValueShrinker;
use crate::values::{Constraints, Value};

/// The test's verdict on one shrink candidate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Verdict {
    /// The candidate was confirmed to hit; it becomes the current witness.
    Hit,
    /// The candidate does not hit (or was not confirmed); it is dropped.
    Miss,
    /// Stop shrinking (budget spent, cancellation, candidate cap).
    Stop,
}

/// Shrink `values` (in hole order). `trees[i]` is hole `i`'s value tree when it has one;
/// `constraints[i]` bounds the moves of a hole without one. Returns the smallest assignment
/// the test confirmed, which is `values` itself when nothing smaller hit.
pub(crate) fn shrink(
    values: &[Value],
    trees: Vec<Option<Box<dyn ValueShrinker>>>,
    constraints: &[Constraints],
    test: &mut dyn FnMut(&[Value]) -> Verdict,
) -> Vec<Value> {
    let mut shrinker = Shrinker {
        current: values.to_vec(),
        test,
        stopped: false,
    };
    let mut moved: Vec<bool> = vec![false; values.len()];
    for (hole, tree) in trees.into_iter().enumerate() {
        if let Some(tree) = tree {
            moved[hole] = true;
            shrinker.along_tree(hole, tree);
        }
    }
    // Moves of one hole can let another shrink further, so passes repeat until none progresses.
    loop {
        let mut progressed = false;
        for (hole, has_tree) in moved.iter().enumerate() {
            if *has_tree {
                continue;
            }
            let default = Constraints::default();
            let bounds = constraints.get(hole).unwrap_or(&default);
            progressed |= shrinker.by_moves(hole, bounds);
        }
        if !progressed || shrinker.stopped {
            break;
        }
    }
    shrinker.current
}

struct Shrinker<'t> {
    current: Vec<Value>,
    test: &'t mut dyn FnMut(&[Value]) -> Verdict,
    stopped: bool,
}

impl Shrinker<'_> {
    /// Test `current` with hole `hole` set to `value`; keep it on a hit.
    fn try_value(&mut self, hole: usize, value: Value) -> bool {
        if self.stopped {
            return false;
        }
        let mut candidate = self.current.clone();
        candidate[hole] = value;
        match (self.test)(&candidate) {
            Verdict::Hit => {
                self.current = candidate;
                true
            }
            Verdict::Miss => false,
            Verdict::Stop => {
                self.stopped = true;
                false
            }
        }
    }

    /// proptest's shrinking loop: simplify after a hit, complicate after a miss.
    fn along_tree(&mut self, hole: usize, mut tree: Box<dyn ValueShrinker>) {
        if !tree.simplify() {
            return;
        }
        loop {
            if self.stopped {
                return;
            }
            let hit = self.try_value(hole, tree.current());
            let more = if hit {
                tree.simplify()
            } else {
                tree.complicate()
            };
            if !more {
                return;
            }
        }
    }

    /// Integer or length moves of one hole; whether any candidate was kept.
    fn by_moves(&mut self, hole: usize, constraints: &Constraints) -> bool {
        match self.current[hole].clone() {
            Value::Int(value) => {
                let target = int_target(constraints);
                self.bisect(hole, &value, &target, Value::Int)
            }
            Value::MInt { width, value } => {
                let target = int_target(constraints).max(BigInt::zero());
                self.bisect(hole, &BigInt::from(value), &target, |n| Value::MInt {
                    width,
                    value: n.to_biguint().unwrap_or_else(BigUint::zero),
                })
            }
            value => {
                let Some(length) = length_of(&value) else {
                    return false;
                };
                let target = constraints
                    .length
                    .and_then(|range| range.min)
                    .map_or(0, |min| usize::try_from(min).unwrap_or(usize::MAX))
                    .min(length);
                self.bisect(hole, &BigInt::from(length), &BigInt::from(target), |n| {
                    let n = usize::try_from(n).unwrap_or(usize::MAX);
                    prefix(&value, n)
                })
            }
        }
    }

    /// Bisect between `target` and `from` (which hits): test `target` first, then halve the
    /// interval between the nearest point known not to hit and the nearest known to hit.
    fn bisect(
        &mut self,
        hole: usize,
        from: &BigInt,
        target: &BigInt,
        make: impl Fn(BigInt) -> Value,
    ) -> bool {
        if from == target {
            return false;
        }
        if self.try_value(hole, make(target.clone())) {
            return true;
        }
        let mut miss = target.clone();
        let mut hit = from.clone();
        let mut kept = false;
        loop {
            let gap: BigInt = &hit - &miss;
            if gap.abs() <= BigInt::from(1) || self.stopped {
                return kept;
            }
            let middle: BigInt = &miss + gap / 2;
            if self.try_value(hole, make(middle.clone())) {
                hit = middle;
                kept = true;
            } else {
                miss = middle;
            }
        }
    }
}

/// The admissible integer nearest zero: zero clamped into the hole's range.
fn int_target(constraints: &Constraints) -> BigInt {
    let mut target = BigInt::zero();
    if let Some(range) = &constraints.range {
        if let Some(min) = &range.min
            && &target < min
        {
            target = min.clone();
        }
        if let Some(max) = &range.max
            && &target > max
        {
            target = max.clone();
        }
    }
    target
}

/// The length a length move shortens, for values that have one.
fn length_of(value: &Value) -> Option<usize> {
    match value {
        Value::String(text) => Some(text.chars().count()),
        Value::Bytes(bytes) => Some(bytes.len()),
        Value::List(items) | Value::Set(items) => Some(items.len()),
        Value::Map(entries) => Some(entries.len()),
        _ => None,
    }
}

/// The first `length` elements (characters, bytes, items, entries) of `value`. A prefix of a
/// sorted set or map is sorted, so it stays canonical.
fn prefix(value: &Value, length: usize) -> Value {
    match value {
        Value::String(text) => Value::String(text.chars().take(length).collect()),
        Value::Bytes(bytes) => Value::Bytes(bytes.iter().copied().take(length).collect()),
        Value::List(items) => Value::List(items.iter().take(length).cloned().collect()),
        Value::Set(items) => Value::Set(items.iter().take(length).cloned().collect()),
        Value::Map(entries) => Value::Map(entries.iter().take(length).cloned().collect()),
        other => other.clone(),
    }
}
