//! Generators, value trees and the seeded proptest RNG (ARCHITECTURE 3). Owner: FZ-03.
//!
//! proptest is driven through `Strategy::new_tree` and `ValueTree::simplify` without its test
//! macros and without `TestRunner::run`; every `Config` field the engine reads is set
//! explicitly, so nothing is read from `PROPTEST_*` variables or files (ARCHITECTURE 3, T-2).
//! No proptest type leaves this crate's internals.
//!
//! The strategies never reject a draw (no `prop_filter`, no `prop_flat_map`), so
//! `Strategy::new_tree` cannot fail and the rejection limits of the `Config` are never reached.

use core::fmt;

use num_bigint::{BigInt, BigUint};
use num_traits::Zero as _;
use proptest::{
    collection::{SizeRange, vec},
    strategy::{BoxedStrategy, NewTree, Strategy, ValueTree},
    test_runner::{Config, RngAlgorithm, RngSeed, TestRng, TestRunner, noop_result_cache},
};
use rand::RngCore as _;

use super::{
    Constraints, GenerationBounds, IntRange, LengthRange, Value, ValueSort, mint_bounds,
    validate_constraints,
};

/// The `Config` of every runner: each field that strategies, value trees or the runner's
/// constructors read is set here, independently of the environment. `..Config::default()`
/// fills only the feature-gated fields (`fork`, `timeout`, `max_shrink_time`, `verbose`), which
/// only `TestRunner::run` reads and which exist or not depending on proptest's features (T-2).
fn engine_config(seed: &[u8; 32]) -> Config {
    let mut first = [0u8; 8];
    first.copy_from_slice(&seed[..8]);
    Config {
        cases: 1,
        max_local_rejects: 1024,
        max_global_rejects: 1024,
        max_flat_map_regens: 1024,
        failure_persistence: None,
        source_file: None,
        test_name: None,
        max_shrink_iters: u32::MAX,
        max_default_size_range: 100,
        result_cache: noop_result_cache,
        rng_algorithm: RngAlgorithm::ChaCha,
        // Not read: the runner's RNG is built from the whole seed. Set so that no
        // environment-derived seed is ever recorded in the runner.
        rng_seed: RngSeed::Fixed(u64::from_le_bytes(first)),
        ..Config::default()
    }
}

/// The proptest runner every generator draws from, seeded from the campaign seed with
/// `RngAlgorithm::ChaCha` and an explicit `Config` (ARCHITECTURE 3, 5.4).
pub(crate) struct ValueRng {
    runner: TestRunner,
}

impl fmt::Debug for ValueRng {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("ValueRng")
    }
}

impl ValueRng {
    /// A runner whose RNG is `TestRng::from_seed(RngAlgorithm::ChaCha, &seed)` and whose
    /// `Config` sets every field the engine reads (`max_local_rejects`, `max_global_rejects`,
    /// `max_flat_map_regens`, `max_shrink_iters`, `max_default_size_range`,
    /// `failure_persistence = None`, `rng_algorithm`, `rng_seed`, `source_file`, `test_name`,
    /// `result_cache`), with `..Config::default()` only for feature-gated fields the engine
    /// never reads. Equal seeds give equal draws whatever the environment.
    pub(crate) fn from_seed(seed: [u8; 32]) -> Self {
        let rng = TestRng::from_seed(RngAlgorithm::ChaCha, &seed);
        Self {
            runner: TestRunner::new_with_rng(engine_config(&seed), rng),
        }
    }
}

/// A generator of one hole's values: a proptest strategy built from its [`ValueSort`],
/// [`Constraints`] and the campaign's [`GenerationBounds`] (ARCHITECTURE 3).
pub(crate) struct Generator {
    strategy: BoxedStrategy<Value>,
}

impl fmt::Debug for Generator {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("Generator")
    }
}

impl Generator {
    /// The generator of `sort` under `constraints` and `bounds`. Every value it produces, and
    /// every value its trees shrink to, satisfies [`super::check_constraints`].
    ///
    /// - A choice set draws only its members, and shrinks towards the first.
    /// - `Int` and `MInt` draw a boundary of the admissible interval (its ends, the value
    ///   nearest zero and its neighbours, and for `MInt` the signed boundaries `2^(W-1) - 1`
    ///   and `2^(W-1)`) one time in eight, and otherwise a value at a uniformly chosen bit
    ///   length of distance from the value nearest zero, so that small and large magnitudes are
    ///   both common. They shrink by bisection towards the value nearest zero.
    /// - `String` draws code points with proptest's character biases; `Bytes` draws bytes.
    ///   Both shrink by removing and simplifying elements, never below the minimum length.
    /// - Token, collection and data sorts have no generator in this milestone (FZ-09); they
    ///   need a choice set.
    ///
    /// # Errors
    ///
    /// A message when the constraints do not suit the sort or admit no value
    /// ([`super::validate_constraints`]), or when the sort has no generator and no choice set;
    /// the caller reports it as [`crate::CampaignError::InvalidConstraints`].
    pub(crate) fn new(
        sort: &ValueSort,
        constraints: &Constraints,
        bounds: &GenerationBounds,
    ) -> Result<Self, String> {
        validate_constraints(sort, constraints)?;
        if let Some(choices) = &constraints.choices {
            return Ok(Self {
                strategy: proptest::sample::select(choices.clone()).boxed(),
            });
        }
        let strategy = match sort {
            ValueSort::Int => IntStrategy::int(constraints.range.as_ref(), bounds.int_bits).boxed(),
            ValueSort::MInt { width } => {
                IntStrategy::mint(*width, constraints.range.as_ref())?.boxed()
            }
            ValueSort::Bool => proptest::bool::ANY.prop_map(Value::Bool).boxed(),
            ValueSort::String => vec(proptest::char::any(), size_range(constraints, bounds)?)
                .prop_map(|characters| Value::String(characters.into_iter().collect()))
                .boxed(),
            ValueSort::Bytes => vec(proptest::num::u8::ANY, size_range(constraints, bounds)?)
                .prop_map(Value::Bytes)
                .boxed(),
            ValueSort::Token { sort } => {
                return Err(format!(
                    "the token sort {sort} has no generator; give the hole a choice set"
                ));
            }
            ValueSort::List { sort, .. }
            | ValueSort::Set { sort, .. }
            | ValueSort::Map { sort, .. } => {
                return Err(format!(
                    "collection holes ({sort}) have no generator before FZ-09 (M3); give the \
                     hole a choice set"
                ));
            }
            ValueSort::Data { sort, .. } => {
                return Err(format!(
                    "data-sort holes ({sort}) have no generator before FZ-09 (M3); give the \
                     hole a choice set"
                ));
            }
        };
        Ok(Self { strategy })
    }

    /// Draw one value, with the value tree that shrinks it inside its sort and constraints.
    pub(crate) fn generate(&self, rng: &mut ValueRng) -> ShrinkableValue {
        let tree = self
            .strategy
            .new_tree(&mut rng.runner)
            .unwrap_or_else(|reason| unreachable!("a generator strategy rejected: {reason}"));
        ShrinkableValue { tree }
    }
}

/// The length range of a `String` or `Bytes` hole under `bounds` (see [`GenerationBounds`]).
fn size_range(constraints: &Constraints, bounds: &GenerationBounds) -> Result<SizeRange, String> {
    let LengthRange { min, max } = constraints.length.unwrap_or_default();
    let min = min.unwrap_or(0);
    let max = max.unwrap_or_else(|| min.max(bounds.length));
    let usize_of =
        |length: u64| usize::try_from(length).map_err(|_| format!("length {length} is too large"));
    Ok(SizeRange::from(usize_of(min)?..=usize_of(max)?))
}

/// A generated value and the proptest value tree that shrinks it (ARCHITECTURE 3, 7).
///
/// The engine drives shrinking itself, as proptest's runner would: [`Self::simplify`] proposes
/// a simpler value; when the engine's confirmation accepts it, the engine calls `simplify`
/// again, and when it rejects it, [`Self::complicate`] steps back towards the last accepted
/// value. `complicate` is meaningful only after a `simplify` that returned `true`. Every value
/// the tree reaches satisfies the hole's constraints, so it needs no constraint check.
///
/// It is an owned, `'static` handle (neither `Clone` nor `Send`), so a proposal can keep it
/// until the engine shrinks the confirmed witness (FZ-01 review S7).
pub(crate) struct ShrinkableValue {
    tree: Box<dyn ValueTree<Value = Value>>,
}

impl fmt::Debug for ShrinkableValue {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ShrinkableValue")
            .field("current", &self.tree.current())
            .finish()
    }
}

impl ShrinkableValue {
    /// The tree's current value.
    pub(crate) fn current(&self) -> Value {
        self.tree.current()
    }

    /// Move to a simpler value; `false` when none remains.
    pub(crate) fn simplify(&mut self) -> bool {
        self.tree.simplify()
    }

    /// Undo part of the last simplification after it was rejected; `false` when none remains.
    pub(crate) fn complicate(&mut self) -> bool {
        self.tree.complicate()
    }
}

// ------------------------------------------------------------------------------------------
// Integers of unbounded size.

/// What an integer strategy's values are.
#[derive(Clone, Copy, Debug)]
enum IntKind {
    Int,
    MInt(u32),
}

/// Integers in `[lo, hi]`, around `origin`, the value of the interval nearest zero.
#[derive(Clone, Debug)]
struct IntStrategy {
    kind: IntKind,
    origin: BigInt,
    lo: BigInt,
    hi: BigInt,
    /// Boundary values inside `[lo, hi]`, distinct and in increasing order; never empty.
    edges: Vec<BigInt>,
}

impl IntStrategy {
    /// `Int` values in `range`; an unbounded end lies `2^bits - 1` from the value nearest zero.
    fn int(range: Option<&IntRange>, bits: u32) -> Self {
        let window = (BigInt::from(1u8) << bits) - 1u8;
        let min = range.and_then(|range| range.min.clone());
        let max = range.and_then(|range| range.max.clone());
        let mut origin = BigInt::zero();
        if let Some(min) = &min {
            origin = origin.max(min.clone());
        }
        if let Some(max) = &max {
            origin = origin.min(max.clone());
        }
        let lo = min.unwrap_or_else(|| &origin - &window);
        let hi = max.unwrap_or_else(|| &origin + &window);
        Self::new(IntKind::Int, origin, lo, hi, &[])
    }

    /// `MInt{width}` values (unsigned, below `2^width`) in `range`.
    fn mint(width: u32, range: Option<&IntRange>) -> Result<Self, String> {
        let (lo, hi) = mint_bounds(width, range.unwrap_or(&IntRange::default()))
            .ok_or_else(|| format!("no MInt{{{width}}} value lies in the range"))?;
        let signed = match width.checked_sub(1) {
            None => Vec::new(),
            Some(below) => {
                let half = BigInt::from(1u8) << below;
                vec![&half - 1u8, half]
            }
        };
        let (lo, hi) = (BigInt::from(lo), BigInt::from(hi));
        Ok(Self::new(IntKind::MInt(width), lo.clone(), lo, hi, &signed))
    }

    fn new(kind: IntKind, origin: BigInt, lo: BigInt, hi: BigInt, extra: &[BigInt]) -> Self {
        let mut edges: Vec<BigInt> = [lo.clone(), hi.clone(), origin.clone()]
            .into_iter()
            .chain([&origin - 1u8, &origin + 1u8])
            .chain(extra.iter().cloned())
            .filter(|edge| lo <= *edge && *edge <= hi)
            .collect();
        edges.sort();
        edges.dedup();
        Self {
            kind,
            origin,
            lo,
            hi,
            edges,
        }
    }
}

impl Strategy for IntStrategy {
    type Tree = IntTree;
    type Value = Value;

    fn new_tree(&self, runner: &mut TestRunner) -> NewTree<Self> {
        let rng = runner.rng();
        let value = if rng.next_u32().is_multiple_of(8) {
            let last = u64::try_from(self.edges.len() - 1).expect("a length fits in u64");
            let index = usize::try_from(uniform_u64(rng, last)).expect("an index of the edges");
            self.edges[index].clone()
        } else {
            let up = BigUint::try_from(&self.hi - &self.origin).unwrap_or_default();
            let down = BigUint::try_from(&self.origin - &self.lo).unwrap_or_default();
            let go_up = match (up.is_zero(), down.is_zero()) {
                (_, true) => true,
                (true, false) => false,
                (false, false) => rng.next_u32() & 1 == 0,
            };
            if go_up {
                &self.origin + BigInt::from(biased_magnitude(rng, &up))
            } else {
                &self.origin - BigInt::from(biased_magnitude(rng, &down))
            }
        };
        Ok(IntTree::new(self.kind, self.origin.clone(), &value))
    }
}

/// A uniformly chosen bit length `k` in `0..=bits(room)`, then a uniform magnitude of exactly
/// `k` bits no greater than `room`.
fn biased_magnitude(rng: &mut TestRng, room: &BigUint) -> BigUint {
    let bits = uniform_u64(rng, room.bits());
    if bits == 0 {
        return BigUint::zero();
    }
    let low = BigUint::from(1u8) << (bits - 1);
    let high = ((BigUint::from(1u8) << bits) - 1u8).min(room.clone());
    let span = &high - &low;
    low + uniform_big(rng, &span)
}

/// A uniform integer in `0..=n`.
fn uniform_u64(rng: &mut TestRng, n: u64) -> u64 {
    let Some(modulus) = n.checked_add(1) else {
        return rng.next_u64();
    };
    // Draws at or above the largest multiple of the modulus are rejected, so that every
    // residue is equally likely.
    let limit = u64::MAX - u64::MAX % modulus;
    loop {
        let draw = rng.next_u64();
        if draw < limit {
            return draw % modulus;
        }
    }
}

/// A uniform integer in `0..=n`, by rejection of `bits(n)`-bit draws (each accepted with
/// probability above one half).
fn uniform_big(rng: &mut TestRng, n: &BigUint) -> BigUint {
    let bits = n.bits();
    if bits == 0 {
        return BigUint::zero();
    }
    let words = bits.div_ceil(64);
    loop {
        let mut bytes = Vec::new();
        for _ in 0..words {
            bytes.extend_from_slice(&rng.next_u64().to_le_bytes());
        }
        let draw = BigUint::from_bytes_le(&bytes) >> (64 * words - bits);
        if draw <= *n {
            return draw;
        }
    }
}

/// The value tree of an integer: `origin ± distance`, where the distance shrinks by bisection
/// towards zero, as proptest's `BinarySearch` does for machine integers. Every value lies
/// between `origin` and the drawn value, hence in the interval.
#[derive(Clone, Debug)]
struct IntTree {
    kind: IntKind,
    origin: BigInt,
    up: bool,
    lo: BigUint,
    curr: BigUint,
    hi: BigUint,
}

impl IntTree {
    fn new(kind: IntKind, origin: BigInt, value: &BigInt) -> Self {
        let up = *value >= origin;
        let distance = BigUint::try_from(if up { value - &origin } else { &origin - value })
            .expect("a distance is non-negative");
        Self {
            kind,
            origin,
            up,
            lo: BigUint::zero(),
            curr: distance.clone(),
            hi: distance,
        }
    }

    fn reposition(&mut self) -> bool {
        let middle = &self.lo + (&self.hi - &self.lo) / 2u8;
        if middle == self.curr {
            false
        } else {
            self.curr = middle;
            true
        }
    }
}

impl ValueTree for IntTree {
    type Value = Value;

    fn current(&self) -> Value {
        let distance = BigInt::from(self.curr.clone());
        let number = if self.up {
            &self.origin + distance
        } else {
            &self.origin - distance
        };
        match self.kind {
            IntKind::Int => Value::Int(number),
            IntKind::MInt(width) => Value::MInt {
                width,
                value: BigUint::try_from(number).expect("an MInt value is non-negative"),
            },
        }
    }

    fn simplify(&mut self) -> bool {
        if self.hi <= self.lo {
            return false;
        }
        self.hi = self.curr.clone();
        self.reposition()
    }

    fn complicate(&mut self) -> bool {
        if self.hi <= self.lo {
            return false;
        }
        self.lo = &self.curr + 1u8;
        self.reposition()
    }
}
