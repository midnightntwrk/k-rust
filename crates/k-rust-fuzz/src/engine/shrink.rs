//! Shrinking a confirmed witness (ARCHITECTURE 7). Owner: FZ-06.
//!
//! Every hole first tries its least value: the admissible integer nearest zero (0, or the
//! range's bound nearest it), or the shortest admissible prefix. A hole the witness does not
//! need then ends there, whatever its value tree would have done: a tree shrinks by bisection,
//! which stops early when the hit is not monotone in the hole (a kill that needs the value at
//! 1 but not at 4).
//!
//! Blindly generated values then shrink along their proptest value trees, which stay inside the
//! hole's sort and constraints. After that every hole, with a tree or not, shrinks by integer
//! moves towards its least value and by length moves towards its shortest prefix, each a
//! bisection between the last candidate that still hit and the target, in passes that repeat
//! while one makes progress: a hole whose smaller values miss while another hole is large (a
//! loop bound below its start) may shrink once the other has (TRIAL2 item 5).
//!
//! Each move changes one hole. A witness that needs a relation between holes (`X * 2 == Y +
//! 1000`) keeps it only through values where one hole alone can move, so it may end larger
//! than the smallest assignment that keeps the relation; joint moves are not tried.
//!
//! Every candidate goes through the caller's test, which confirms it; a candidate is kept only
//! when the test says it still hits.

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
    let default = Constraints::default();
    let bounds = |hole: usize| constraints.get(hole).unwrap_or(&default);
    for (hole, tree) in trees.into_iter().enumerate() {
        if let Some(tree) = tree
            && !shrinker.try_least(hole, bounds(hole))
        {
            shrinker.along_tree(hole, tree);
        }
    }
    // Moves of one hole can let another shrink further, so passes over every hole repeat until
    // none progresses.
    loop {
        let mut progressed = false;
        for hole in 0..shrinker.current.len() {
            progressed |= shrinker.by_moves(hole, bounds(hole));
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

    /// Try hole `hole` at its least value ([`least`]), when that is another value; whether it
    /// was kept.
    fn try_least(&mut self, hole: usize, constraints: &Constraints) -> bool {
        match least(&self.current[hole], constraints) {
            Some(value) if value != self.current[hole] => self.try_value(hole, value),
            _ => false,
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

/// The least value [`Shrinker::by_moves`] moves `value` towards: for an integer, the
/// admissible integer nearest zero; for a value with a length, its shortest admissible prefix;
/// `None` for any other value.
fn least(value: &Value, constraints: &Constraints) -> Option<Value> {
    match value {
        Value::Int(_) => Some(Value::Int(int_target(constraints))),
        Value::MInt { width, .. } => Some(Value::MInt {
            width: *width,
            value: int_target(constraints)
                .max(BigInt::zero())
                .to_biguint()
                .unwrap_or_else(BigUint::zero),
        }),
        value => {
            let length = length_of(value)?;
            let target = constraints
                .length
                .and_then(|range| range.min)
                .map_or(0, |min| usize::try_from(min).unwrap_or(usize::MAX))
                .min(length);
            Some(prefix(value, target))
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
            target.clone_from(min);
        }
        if let Some(max) = &range.max
            && &target > max
        {
            target.clone_from(max);
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
