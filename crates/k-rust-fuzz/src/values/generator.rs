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
use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::Zero as _;
use proptest::{
    collection::{SizeRange, vec},
    sample::subsequence,
    strategy::{BoxedStrategy, Just, NewTree, Strategy, Union, ValueTree},
    test_runner::{Config, RngAlgorithm, RngSeed, TestRng, TestRunner, noop_result_cache},
};
use rand::RngCore as _;

use super::{
    ArgumentSort, CollectionKind, Constraints, DataSorts, GenerationBounds, IntRange, LengthRange,
    MAX_GENERATED_LENGTH, MAX_VALUE_SIZE, Value, ValueSort, mint_bounds, validate_bounds,
    validate_constraints,
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
    /// - `List` draws a vector of elements; `Set` and `Map` draw distinct elements (keys) by
    ///   construction, never by rejection: as a subsequence of the whole universe of the element
    ///   (key) sort when it has at most [`ENUMERATION_LIMIT`] values, and otherwise as a vector
    ///   whose repeated items are replaced by unused canonical values ([`distinct`]). Lengths are
    ///   clamped to the number of distinct values the element sort has under `bounds`, and a
    ///   minimum above it is refused. Elements are drawn without constraints under `bounds`.
    ///   Collections shrink by removing elements, never below the minimum length, and by
    ///   shrinking elements.
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
            ValueSort::List { sort, element, .. } => {
                let size = within_budget(
                    sort,
                    &size_range(constraints, bounds)?,
                    value_size(element, bounds),
                )?;
                let element = Self::new(element, &Constraints::default(), bounds)?.strategy;
                vec(element, size).prop_map(Value::List).boxed()
            }
            ValueSort::Set { sort, element, .. } => {
                set_strategy(sort, element, constraints, bounds)?
            }
            ValueSort::Map {
                sort, key, value, ..
            } => map_strategy(sort, key, value, constraints, bounds)?,
            ValueSort::Data { sort, table, .. } => data_strategy(sort, table, bounds)?,
            ValueSort::Renamed { .. } => unreachable!("generated() unwraps a renamed sort"),
        };
        Ok(Self { strategy })
    }

    /// Draw one value, with the value tree that shrinks it inside its sort and constraints.
    ///
    /// # Errors
    ///
    /// A message when the strategy rejects the draw. No strategy of this module rejects (there
    /// is no `prop_filter`, `prop_flat_map` or filtering collection, and sets and maps are
    /// distinct by construction), so this does not happen; the engine still counts a failed draw
    /// as a `rejected` case (`generation`).
    pub(crate) fn try_generate(&self, rng: &mut ValueRng) -> Result<ShrinkableValue, String> {
        self.strategy
            .new_tree(&mut rng.runner)
            .map(|tree| ShrinkableValue { tree })
            .map_err(|reason| format!("the generator rejected a draw: {reason}"))
    }

    /// [`Self::try_generate`] for tests, where a failed draw is a bug. It cannot fail, since no
    /// strategy of this module rejects a draw.
    #[cfg(test)]
    pub(crate) fn generate(&self, rng: &mut ValueRng) -> ShrinkableValue {
        self.try_generate(rng)
            .unwrap_or_else(|reason| unreachable!("no generator strategy rejects: {reason}"))
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

/// The largest universe a set's elements or a map's keys are drawn from as a subsequence; from
/// a larger element sort (and from `String` and `Bytes`), elements are drawn independently and
/// repeated ones replaced by canonical values ([`distinct`]).
pub const ENUMERATION_LIMIT: u64 = 1 << 16;

/// Every value of `sort` under `bounds`, in canonical order, when there are at most
/// [`ENUMERATION_LIMIT`] and `sort` is not `String` or `Bytes` (whose canonical values are a
/// two-letter subset, too narrow to draw from).
fn universe(sort: &ValueSort, bounds: &GenerationBounds) -> Option<Vec<Value>> {
    if matches!(sort.generated(), ValueSort::String | ValueSort::Bytes) {
        return None;
    }
    let count = cardinality(sort, bounds)?;
    let count = usize::try_from(count)
        .ok()
        .filter(|count| u64::try_from(*count).is_ok_and(|count| count <= ENUMERATION_LIMIT))?;
    Some(canonical(sort, count, bounds))
}

/// The length range of a `Set` or `Map` hole (named `sort`) whose elements or keys are of
/// `element`: [`size_range`], with the maximum clamped to the number of distinct values the
/// element sort generates under `bounds` ([`cardinality`]).
///
/// # Errors
///
/// A message when the minimum length exceeds that number (`Set<Bool>` of at least 3, `Set<Int>`
/// of at least 4 under `int_bits: 1`, `Set<String>` of at least 2 under `length: 0`).
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
    if u128::try_from(min).unwrap_or(u128::MAX) > count {
        return Err(format!(
            "{sort} asks for at least {min} distinct elements, and its element sort has {count} \
             values under the generation bounds"
        ));
    }
    let max = usize::try_from(count).map_or(max, |count| max.min(count));
    Ok(SizeRange::from(min..=max))
}

/// The number of values `sort` generates under `bounds`, which is also the number of values
/// [`canonical`] lists; `None` when it is at least `2^128` (or the sort generates nothing).
///
/// An unranged `Int` has the `2^(int_bits+1) - 1` values of its window; `String` and `Bytes`
/// count only the strings over a two-letter alphabet within the length bound, the values
/// [`canonical`] lists (a lower bound, which is all distinct drawing needs).
fn cardinality(sort: &ValueSort, bounds: &GenerationBounds) -> Option<u128> {
    let window = |bits: u32| 1u128.checked_shl(bits.checked_add(1)?).map(|n| n - 1);
    match sort.generated() {
        ValueSort::Bool => Some(2),
        ValueSort::Int => window(bounds.int_bits),
        ValueSort::MInt { width } => 1u128.checked_shl(*width),
        ValueSort::String | ValueSort::Bytes => {
            window(u32::try_from(bounds.length).unwrap_or(u32::MAX))
        }
        ValueSort::Data { table, .. } if !table.sorts.is_empty() => {
            let mut memo = BTreeMap::new();
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
    memo: &mut BTreeMap<(usize, u32), Option<u128>>,
) -> Option<u128> {
    if let Some(known) = memo.get(&(index, depth)) {
        return *known;
    }
    let entry = &table.sorts[index];
    let mut total = Some(0u128);
    for subsort in &entry.subsorts {
        let count = argument_cardinality(subsort, table, depth, bounds, memo);
        total = total
            .zip(count)
            .and_then(|(total, count)| total.checked_add(count));
    }
    for constructor in &entry.constructors {
        if constructor.height.is_none_or(|height| height > depth) {
            continue;
        }
        let mut product = Some(1u128);
        for argument in &constructor.arguments {
            let count = argument_cardinality(argument, table, depth - 1, bounds, memo);
            product = product
                .zip(count)
                .and_then(|(product, count)| product.checked_mul(count));
        }
        total = total
            .zip(product)
            .and_then(|(total, product)| total.checked_add(product));
    }
    memo.insert((index, depth), total);
    total
}

fn argument_cardinality(
    sort: &ArgumentSort,
    table: &DataSorts,
    depth: u32,
    bounds: &GenerationBounds,
    memo: &mut BTreeMap<(usize, u32), Option<u128>>,
) -> Option<u128> {
    match sort {
        ArgumentSort::Value(sort) => cardinality(sort, bounds),
        ArgumentSort::Empty(_) => Some(1),
        ArgumentSort::Data(index) => data_cardinality(table, *index, depth, bounds, memo),
    }
}

/// Up to `limit` distinct values of `sort` under `bounds`, in a fixed order: the canonical
/// values distinct drawing falls back on.
///
/// - `Int`: `0, 1, -1, 2, -2, ...` inside the window of `int_bits`;
/// - `Bool`: `false, true`; `MInt{W}`: `0, 1, 2, ...`;
/// - `String` and `Bytes`: the strings over `a` and `b` in length-then-lexicographic order,
///   within the length bound;
/// - a data sort: its subsorts' values, then each constructor applied to argument tuples in
///   order, within the depth bound (the order [`data_cardinality`] counts).
fn canonical(sort: &ValueSort, limit: usize, bounds: &GenerationBounds) -> Vec<Value> {
    match sort.generated() {
        ValueSort::Bool => [false, true]
            .into_iter()
            .take(limit)
            .map(Value::Bool)
            .collect(),
        ValueSort::Int => {
            let edge = (BigInt::from(1u8) << bounds.int_bits) - 1u8;
            let mut values = vec![Value::Int(BigInt::zero())];
            let mut step = BigInt::from(1u8);
            while values.len() < limit && step <= edge {
                values.push(Value::Int(step.clone()));
                if values.len() < limit {
                    values.push(Value::Int(-step.clone()));
                }
                step += 1u8;
            }
            values.truncate(limit);
            values
        }
        ValueSort::MInt { width } => {
            let count = cardinality(sort, bounds).unwrap_or(u128::MAX);
            (0..count.min(u128::try_from(limit).unwrap_or(u128::MAX)))
                .map(|value| Value::MInt {
                    width: *width,
                    value: BigUint::from(value),
                })
                .collect()
        }
        ValueSort::String => two_letter_words(limit, bounds.length)
            .into_iter()
            .map(|word| Value::String(word.into_iter().map(char::from).collect()))
            .collect(),
        ValueSort::Bytes => two_letter_words(limit, bounds.length)
            .into_iter()
            .map(Value::Bytes)
            .collect(),
        ValueSort::Data { table, .. } if !table.sorts.is_empty() => {
            let mut memo = BTreeMap::new();
            canonical_data(table, 0, bounds.depth, limit, bounds, &mut memo)
        }
        _ => Vec::new(),
    }
}

/// Up to `limit` words over `a` and `b` of at most `length` letters, shortest first.
fn two_letter_words(limit: usize, length: u64) -> Vec<Vec<u8>> {
    let mut words = vec![Vec::new()];
    let mut start = 0;
    while words.len() < limit {
        let end = words.len();
        if start == end || u64::try_from(words[start].len()).unwrap_or(u64::MAX) >= length {
            break;
        }
        for index in start..end {
            for letter in *b"ab" {
                if words.len() < limit {
                    let mut word = words[index].clone();
                    word.push(letter);
                    words.push(word);
                }
            }
        }
        start = end;
    }
    words.truncate(limit);
    words
}

fn canonical_data(
    table: &DataSorts,
    index: usize,
    depth: u32,
    limit: usize,
    bounds: &GenerationBounds,
    memo: &mut BTreeMap<(usize, u32), Vec<Value>>,
) -> Vec<Value> {
    if let Some(known) = memo.get(&(index, depth)) {
        return known.clone();
    }
    let entry = &table.sorts[index];
    let mut values = Vec::new();
    for subsort in &entry.subsorts {
        let room = limit - values.len();
        values.extend(
            canonical_argument(subsort, table, depth, limit, bounds, memo)
                .into_iter()
                .take(room),
        );
    }
    for constructor in &entry.constructors {
        if values.len() >= limit {
            break;
        }
        if constructor.height.is_none_or(|height| height > depth) {
            continue;
        }
        let room = limit - values.len();
        let mut tuples = vec![Vec::new()];
        for argument in &constructor.arguments {
            let choices = canonical_argument(argument, table, depth - 1, limit, bounds, memo);
            let mut next = Vec::new();
            'tuples: for tuple in &tuples {
                for choice in &choices {
                    if next.len() >= room {
                        break 'tuples;
                    }
                    let mut tuple: Vec<Value> = tuple.clone();
                    tuple.push(choice.clone());
                    next.push(tuple);
                }
            }
            tuples = next;
        }
        values.extend(tuples.into_iter().map(|arguments| Value::Apply {
            symbol: constructor.symbol.clone(),
            arguments,
        }));
    }
    values.truncate(limit);
    memo.insert((index, depth), values.clone());
    values
}

fn canonical_argument(
    sort: &ArgumentSort,
    table: &DataSorts,
    depth: u32,
    limit: usize,
    bounds: &GenerationBounds,
    memo: &mut BTreeMap<(usize, u32), Vec<Value>>,
) -> Vec<Value> {
    match sort {
        ArgumentSort::Value(sort) => canonical(sort, limit, bounds),
        ArgumentSort::Empty(empty) => vec![empty_collection(empty.kind)],
        ArgumentSort::Data(index) => canonical_data(table, *index, depth, limit, bounds, memo),
    }
}

/// `items` with every repeated item replaced by the first canonical value of `sort` not yet
/// used, so that the result has as many distinct items as `items` has entries. `key` reads the
/// item a duplicate is judged by (a map entry's key), and `replace` puts a new one in place.
///
/// The caller draws at most [`cardinality`] items, so the first `items.len()` canonical values
/// always hold one unused value per repeated item.
fn distinct<T: Clone>(
    mut items: Vec<T>,
    sort: &ValueSort,
    bounds: &GenerationBounds,
    key: impl Fn(&T) -> &Value,
    replace: impl Fn(&mut T, Value),
) -> Vec<T> {
    let mut used = BTreeSet::new();
    let mut repeated = Vec::new();
    for (index, item) in items.iter().enumerate() {
        if !used.insert(key(item).clone()) {
            repeated.push(index);
        }
    }
    if !repeated.is_empty() {
        let mut fresh = canonical(sort, items.len(), bounds)
            .into_iter()
            .filter(|value| !used.contains(value));
        for index in repeated {
            let value = fresh
                .next()
                .expect("the canonical values hold one unused value per repeated item");
            replace(&mut items[index], value);
        }
    }
    items
}

fn empty_collection(kind: CollectionKind) -> Value {
    match kind {
        CollectionKind::List => Value::List(Vec::new()),
        CollectionKind::Set => Value::Set(Vec::new()),
        CollectionKind::Map => Value::Map(Vec::new()),
    }
}

/// The strategy of a `Set` hole (see [`Generator::new`]).
fn set_strategy(
    sort: &str,
    element: &ValueSort,
    constraints: &Constraints,
    bounds: &GenerationBounds,
) -> Result<BoxedStrategy<Value>, String> {
    let size = within_budget(
        sort,
        &distinct_size(sort, element, constraints, bounds)?,
        value_size(element, bounds),
    )?;
    let strategy = if let Some(universe) = universe(element, bounds) {
        subsequence(universe, size)
            .prop_map(|mut items| {
                items.sort();
                Value::Set(items)
            })
            .boxed()
    } else {
        let strategy = Generator::new(element, &Constraints::default(), bounds)?.strategy;
        let (element, bounds) = (element.clone(), *bounds);
        vec(strategy, size)
            .prop_map(move |items| {
                let mut items = distinct(
                    items,
                    &element,
                    &bounds,
                    |item| item,
                    |item, new| {
                        *item = new;
                    },
                );
                items.sort();
                Value::Set(items)
            })
            .boxed()
    };
    Ok(strategy)
}

/// The strategy of a `Map` hole (see [`Generator::new`]).
fn map_strategy(
    sort: &str,
    key: &ValueSort,
    value: &ValueSort,
    constraints: &Constraints,
    bounds: &GenerationBounds,
) -> Result<BoxedStrategy<Value>, String> {
    let size = within_budget(
        sort,
        &distinct_size(sort, key, constraints, bounds)?,
        value_size(key, bounds).saturating_add(value_size(value, bounds)),
    )?;
    let value = Generator::new(value, &Constraints::default(), bounds)?.strategy;
    let strategy = if let Some(universe) = universe(key, bounds) {
        let most = size.end_incl();
        (subsequence(universe, size), vec(value, most..=most))
            .prop_map(|(mut keys, values)| {
                keys.sort();
                Value::Map(keys.into_iter().zip(values).collect())
            })
            .boxed()
    } else {
        let strategy = Generator::new(key, &Constraints::default(), bounds)?.strategy;
        let (key, bounds) = (key.clone(), *bounds);
        vec((strategy, value), size)
            .prop_map(move |entries| {
                let mut entries = distinct(
                    entries,
                    &key,
                    &bounds,
                    |entry| &entry.0,
                    |entry, new| entry.0 = new,
                );
                entries.sort_by(|left, right| left.0.cmp(&right.0));
                Value::Map(entries)
            })
            .boxed()
    };
    Ok(strategy)
}

/// The size of the largest value `sort` generates under `bounds`, in [`MAX_VALUE_SIZE`]'s units:
/// one per constructor application or leaf, plus one per 64 bits of an integer and one per
/// character or byte of a string (saturating).
fn value_size(sort: &ValueSort, bounds: &GenerationBounds) -> u128 {
    let words = |bits: u32| 1 + u128::from(bits / 64);
    match sort.generated() {
        ValueSort::Int => words(bounds.int_bits),
        ValueSort::MInt { width } => words(*width),
        ValueSort::String | ValueSort::Bytes => 1 + u128::from(bounds.length),
        ValueSort::Data { table, .. } if !table.sorts.is_empty() => {
            data_size(table, 0, bounds.depth, bounds, &mut BTreeMap::new())
        }
        _ => 1,
    }
}

fn data_size(
    table: &DataSorts,
    index: usize,
    depth: u32,
    bounds: &GenerationBounds,
    memo: &mut BTreeMap<(usize, u32), u128>,
) -> u128 {
    if let Some(known) = memo.get(&(index, depth)) {
        return *known;
    }
    let entry = &table.sorts[index];
    let mut size = entry
        .subsorts
        .iter()
        .map(|subsort| match subsort {
            ArgumentSort::Value(sort) => value_size(sort, bounds),
            _ => 1,
        })
        .max()
        .unwrap_or(0);
    for constructor in &entry.constructors {
        if constructor.height.is_none_or(|height| height > depth) {
            continue;
        }
        let arguments = constructor
            .arguments
            .iter()
            .map(|argument| match argument {
                ArgumentSort::Value(sort) => value_size(sort, bounds),
                ArgumentSort::Empty(_) => 1,
                ArgumentSort::Data(child) => data_size(table, *child, depth - 1, bounds, memo),
            })
            .fold(1u128, u128::saturating_add);
        size = size.max(arguments);
    }
    memo.insert((index, depth), size);
    size
}

/// `size` with its maximum lowered so that a collection of elements of `element` size stays
/// within [`MAX_VALUE_SIZE`].
///
/// # Errors
///
/// A message when even the minimum length exceeds the budget.
fn within_budget(sort: &str, size: &SizeRange, element: u128) -> Result<SizeRange, String> {
    let most = usize::try_from(MAX_VALUE_SIZE / element.max(1)).unwrap_or(usize::MAX);
    if size.start() > most {
        return Err(format!(
            "{sort} asks for at least {} elements of size up to {element}, above the size \
             budget of a value ({MAX_VALUE_SIZE})",
            size.start()
        ));
    }
    Ok(SizeRange::from(size.start()..=size.end_incl().min(most)))
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
    let mut memo = BTreeMap::new();
    if data_size(table, 0, bounds.depth, bounds, &mut memo) > MAX_VALUE_SIZE {
        let fits = (height..bounds.depth)
            .rev()
            .find(|depth| data_size(table, 0, *depth, bounds, &mut memo) <= MAX_VALUE_SIZE);
        return Err(match fits {
            Some(depth) => format!(
                "values of the data sort {sort} at depth {} can exceed the size budget of a \
                 value ({MAX_VALUE_SIZE}); depth {depth} fits",
                bounds.depth
            ),
            None => format!(
                "even the least values of the data sort {sort} can exceed the size budget of a \
                 value ({MAX_VALUE_SIZE})"
            ),
        });
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
        // Before any simplification `hi` is the drawn distance, so there is nothing above it to
        // step back to; the tree is left as it was.
        if self.curr >= self.hi {
            return false;
        }
        self.lo = &self.curr + 1u8;
        self.reposition()
    }
}
