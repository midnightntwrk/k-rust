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
    collection::{SizeRange, btree_map, btree_set, vec},
    sample::subsequence,
    strategy::{BoxedStrategy, Just, NewTree, Strategy, Union, ValueTree},
    test_runner::{Config, RngAlgorithm, RngSeed, TestRng, TestRunner, noop_result_cache},
};
use rand::RngCore as _;

use super::{
    ArgumentSort, CollectionKind, Constraints, DataSorts, GenerationBounds, IntRange, LengthRange,
    MAX_GENERATED_LENGTH, Value, ValueSort, mint_bounds, validate_bounds, validate_constraints,
};

/// The `Config` of every runner: each field that strategies, value trees or the runner's
/// constructors read is set here, independently of the environment. `..Config::default()`
/// fills only the feature-gated fields (`fork`, `timeout`, `max_shrink_time`, `verbose`), which
/// only `TestRunner::run` reads and which exist or not depending on proptest's features (T-2).
pub(super) fn engine_config(seed: &[u8; 32]) -> Config {
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
    /// - A renamed builtin draws its base's values.
    /// - `List` draws a vector of elements; `Set` and `Map` draw distinct elements (keys), from
    ///   the whole universe of the element (key) sort when it has at most
    ///   [`ENUMERATION_LIMIT`] values (a subsequence of it, so a draw never fails), and by
    ///   proptest's `btree_set`/`btree_map` otherwise. Elements are drawn without constraints
    ///   under `bounds`. Collections shrink by removing elements, never below the minimum
    ///   length, and by shrinking elements.
    /// - A data sort draws, at remaining depth `d`, uniformly among the alternatives of its
    ///   table entry whose least height is at most `d` (its non-data subsorts, then its
    ///   constructors, lowest first), and draws a constructor's data arguments at depth
    ///   `d - 1`, starting from `bounds.depth`; so every term is at most `bounds.depth`
    ///   applications deep, and recursion terminates (`values/data.rs`). It shrinks towards
    ///   earlier (lower) alternatives and by shrinking arguments, so every step stays a value of
    ///   the sort within the depth bound.
    /// - Token sorts have no generator; they need a choice set.
    ///
    /// # Errors
    ///
    /// A message when the bounds exceed their caps ([`super::validate_bounds`]), the constraints
    /// do not suit the sort or admit no value ([`super::validate_constraints`]), the sort has no
    /// generator and no choice set, a data sort has no value within the depth bound, or a set or
    /// map asks for more distinct elements than its element sort reliably gives; the caller
    /// reports it as [`crate::CampaignError::InvalidConstraints`].
    pub(crate) fn new(
        sort: &ValueSort,
        constraints: &Constraints,
        bounds: &GenerationBounds,
    ) -> Result<Self, String> {
        validate_bounds(bounds)?;
        validate_constraints(sort, constraints)?;
        if let Some(choices) = &constraints.choices {
            return Ok(Self {
                strategy: proptest::sample::select(choices.clone()).boxed(),
            });
        }
        let strategy = match sort.generated() {
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
            ValueSort::List { element, .. } => {
                let element = Self::new(element, &Constraints::default(), bounds)?.strategy;
                vec(element, size_range(constraints, bounds)?)
                    .prop_map(Value::List)
                    .boxed()
            }
            ValueSort::Set { sort, element, .. } => {
                let size = distinct_size(sort, element, constraints, bounds)?;
                if let Some(universe) = enumerate(element, bounds) {
                    subsequence(universe, size)
                        .prop_map(|mut items| {
                            items.sort();
                            Value::Set(items)
                        })
                        .boxed()
                } else {
                    let element = Self::new(element, &Constraints::default(), bounds)?.strategy;
                    btree_set(element, size)
                        .prop_map(|items| Value::Set(items.into_iter().collect()))
                        .boxed()
                }
            }
            ValueSort::Map {
                sort, key, value, ..
            } => {
                let size = distinct_size(sort, key, constraints, bounds)?;
                let value = Self::new(value, &Constraints::default(), bounds)?.strategy;
                if let Some(universe) = enumerate(key, bounds) {
                    let most = size.end_incl();
                    (subsequence(universe, size), vec(value, most..=most))
                        .prop_map(|(mut keys, values)| {
                            keys.sort();
                            Value::Map(keys.into_iter().zip(values).collect())
                        })
                        .boxed()
                } else {
                    let key = Self::new(key, &Constraints::default(), bounds)?.strategy;
                    btree_map(key, value, size)
                        .prop_map(|entries| Value::Map(entries.into_iter().collect()))
                        .boxed()
                }
            }
            ValueSort::Data { sort, table, .. } => data_strategy(sort, table, bounds)?,
            ValueSort::Renamed { .. } => unreachable!("generated() unwraps a renamed sort"),
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

/// The length range of a `String`, `Bytes` or collection hole under `bounds` (see
/// [`GenerationBounds`]), with its maximum clamped to [`MAX_GENERATED_LENGTH`].
fn size_range(constraints: &Constraints, bounds: &GenerationBounds) -> Result<SizeRange, String> {
    let LengthRange { min, max } = constraints.length.unwrap_or_default();
    let min = min.unwrap_or(0);
    let max = max
        .unwrap_or_else(|| min.max(bounds.length))
        .min(MAX_GENERATED_LENGTH)
        .max(min);
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
// Sets, maps and data sorts.

/// The largest universe a set's elements or a map's keys are drawn from as a subsequence; a
/// larger element sort is drawn from by proptest's `btree_set` and `btree_map`.
pub const ENUMERATION_LIMIT: u64 = 1 << 16;

/// The length range of a `Set` or `Map` hole (named `sort`) whose elements or keys are of
/// `element`: [`size_range`], with the maximum clamped to the number of distinct elements.
///
/// When the element sort has more than [`ENUMERATION_LIMIT`] values, but finitely many (`c`),
/// the minimum must satisfy `min^2 <= 4c`: then `min` independent draws are all distinct with
/// probability above `e^-2`, so proptest's `btree_set` finds a large enough set well within its
/// rejection limit.
fn distinct_size(
    sort: &str,
    element: &ValueSort,
    constraints: &Constraints,
    bounds: &GenerationBounds,
) -> Result<SizeRange, String> {
    let size = size_range(constraints, bounds)?;
    let (min, max) = (size.start(), size.end_incl());
    let Some(count) = cardinality(element, bounds) else {
        return Ok(size);
    };
    let min_wide = u128::try_from(min).unwrap_or(u128::MAX);
    if min_wide > count {
        return Err(format!(
            "{sort} asks for at least {min} distinct elements, and its element sort has {count}"
        ));
    }
    if count > u128::from(ENUMERATION_LIMIT) && min_wide.saturating_mul(min_wide) > count * 4 {
        return Err(format!(
            "{sort} asks for at least {min} distinct elements out of {count}, more than distinct \
             draws reliably give (at most 2 * sqrt({count}))"
        ));
    }
    let max = usize::try_from(count).map_or(max, |count| max.min(count));
    Ok(SizeRange::from(min..=max))
}

/// The number of values `sort` generates under `bounds`, when finite and below `2^128`:
/// `Bool`, `MInt`, and data sorts whose terms within the depth bound are finitely many.
/// `None` for the others, which have too many values for a collision to matter.
fn cardinality(sort: &ValueSort, bounds: &GenerationBounds) -> Option<u128> {
    match sort.generated() {
        ValueSort::Bool => Some(2),
        ValueSort::MInt { width } => 1u128.checked_shl(*width),
        ValueSort::Data { table, .. } => {
            let mut memo = std::collections::BTreeMap::new();
            data_cardinality(table, 0, bounds.depth, bounds, &mut memo)
        }
        _ => None,
    }
}

fn data_cardinality(
    table: &DataSorts,
    index: usize,
    depth: u32,
    bounds: &GenerationBounds,
    memo: &mut std::collections::BTreeMap<(usize, u32), Option<u128>>,
) -> Option<u128> {
    if let Some(known) = memo.get(&(index, depth)) {
        return *known;
    }
    let entry = &table.sorts[index];
    let mut total = 0u128;
    let mut finite = true;
    for subsort in &entry.subsorts {
        match argument_cardinality(subsort, table, depth, bounds, memo) {
            Some(count) => total = total.checked_add(count)?,
            None => finite = false,
        }
    }
    for constructor in &entry.constructors {
        if constructor.height.is_none_or(|height| height > depth) {
            continue;
        }
        let mut product = 1u128;
        for argument in &constructor.arguments {
            match argument_cardinality(argument, table, depth - 1, bounds, memo) {
                Some(count) => product = product.checked_mul(count)?,
                None => finite = false,
            }
        }
        total = total.checked_add(product)?;
    }
    let result = finite.then_some(total);
    memo.insert((index, depth), result);
    result
}

fn argument_cardinality(
    sort: &ArgumentSort,
    table: &DataSorts,
    depth: u32,
    bounds: &GenerationBounds,
    memo: &mut std::collections::BTreeMap<(usize, u32), Option<u128>>,
) -> Option<u128> {
    match sort {
        ArgumentSort::Value(sort) => cardinality(sort, bounds),
        ArgumentSort::Empty(_) => Some(1),
        ArgumentSort::Data(index) => data_cardinality(table, *index, depth, bounds, memo),
    }
}

/// Every value `sort` generates under `bounds`, in a fixed order, when they are at most
/// [`ENUMERATION_LIMIT`] (see [`cardinality`]).
fn enumerate(sort: &ValueSort, bounds: &GenerationBounds) -> Option<Vec<Value>> {
    let count = cardinality(sort, bounds)?;
    if count > u128::from(ENUMERATION_LIMIT) {
        return None;
    }
    Some(match sort.generated() {
        ValueSort::Bool => vec![Value::Bool(false), Value::Bool(true)],
        ValueSort::MInt { width } => (0..count)
            .map(|value| Value::MInt {
                width: *width,
                value: BigUint::from(value),
            })
            .collect(),
        ValueSort::Data { table, .. } => enumerate_data(table, 0, bounds.depth),
        _ => return None,
    })
}

fn enumerate_data(table: &DataSorts, index: usize, depth: u32) -> Vec<Value> {
    let entry = &table.sorts[index];
    let mut values = Vec::new();
    for subsort in &entry.subsorts {
        values.extend(enumerate_argument(subsort, table, depth));
    }
    for constructor in &entry.constructors {
        if constructor.height.is_none_or(|height| height > depth) {
            continue;
        }
        let mut tuples = vec![Vec::new()];
        for argument in &constructor.arguments {
            let choices = enumerate_argument(argument, table, depth - 1);
            tuples = tuples
                .into_iter()
                .flat_map(|tuple: Vec<Value>| {
                    choices.iter().map(move |choice| {
                        let mut tuple = tuple.clone();
                        tuple.push(choice.clone());
                        tuple
                    })
                })
                .collect();
        }
        values.extend(tuples.into_iter().map(|arguments| Value::Apply {
            symbol: constructor.symbol.clone(),
            arguments,
        }));
    }
    values
}

fn enumerate_argument(sort: &ArgumentSort, table: &DataSorts, depth: u32) -> Vec<Value> {
    match sort {
        ArgumentSort::Value(sort) => match sort.generated() {
            ValueSort::Bool => vec![Value::Bool(false), Value::Bool(true)],
            ValueSort::MInt { width } => (0..(1u64 << width))
                .map(|value| Value::MInt {
                    width: *width,
                    value: BigUint::from(value),
                })
                .collect(),
            _ => unreachable!("an enumerated data sort has only finite leaves"),
        },
        ArgumentSort::Empty(empty) => vec![empty_collection(empty.kind)],
        ArgumentSort::Data(index) => enumerate_data(table, *index, depth),
    }
}

fn empty_collection(kind: CollectionKind) -> Value {
    match kind {
        CollectionKind::List => Value::List(Vec::new()),
        CollectionKind::Set => Value::Set(Vec::new()),
        CollectionKind::Map => Value::Map(Vec::new()),
    }
}

/// The strategy of the data sort `sort` with table `table` (see [`Generator::new`]).
fn data_strategy(
    sort: &str,
    table: &DataSorts,
    bounds: &GenerationBounds,
) -> Result<BoxedStrategy<Value>, String> {
    let Some(root) = table.sorts.first() else {
        return Err(format!(
            "the data sort {sort} was resolved without its constructor table; give the hole a \
             choice set"
        ));
    };
    let height = root
        .height
        .ok_or_else(|| format!("no value of the data sort {sort} can be built"))?;
    if height > bounds.depth {
        return Err(format!(
            "the least value of the data sort {sort} is {height} constructors deep, above the \
             depth bound {}",
            bounds.depth
        ));
    }
    let leaf = |sort: &ArgumentSort| -> Result<BoxedStrategy<Value>, String> {
        match sort {
            ArgumentSort::Value(sort) => {
                Ok(Generator::new(sort, &Constraints::default(), bounds)?.strategy)
            }
            ArgumentSort::Empty(empty) => Ok(Just(empty_collection(empty.kind)).boxed()),
            ArgumentSort::Data(_) => unreachable!("a leaf is not data"),
        }
    };
    // levels[d][i]: the values of entry i at most d applications deep.
    let mut levels: Vec<Vec<Option<BoxedStrategy<Value>>>> = Vec::new();
    for depth in 0..=bounds.depth {
        let mut level = Vec::with_capacity(table.sorts.len());
        for entry in &table.sorts {
            let mut alternatives = entry
                .subsorts
                .iter()
                .map(leaf)
                .collect::<Result<Vec<_>, _>>()?;
            for constructor in &entry.constructors {
                if constructor.height.is_none_or(|height| height > depth) {
                    continue;
                }
                let arguments = constructor
                    .arguments
                    .iter()
                    .map(|argument| match argument {
                        ArgumentSort::Data(index) => Ok(levels[depth as usize - 1][*index]
                            .clone()
                            .expect("a constructor's data arguments are lower than it")),
                        other => leaf(other),
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                let symbol = constructor.symbol.clone();
                alternatives.push(
                    arguments
                        .prop_map(move |arguments| Value::Apply {
                            symbol: symbol.clone(),
                            arguments,
                        })
                        .boxed(),
                );
            }
            level.push((!alternatives.is_empty()).then(|| Union::new(alternatives).boxed()));
        }
        levels.push(level);
    }
    Ok(levels
        .pop()
        .and_then(|mut level| level.swap_remove(0))
        .expect("the root has a value within the depth bound"))
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
        // Before any simplification `hi` is the drawn distance, so there is nothing above it to
        // step back to.
        if self.lo > self.hi {
            return false;
        }
        self.reposition()
    }
}
