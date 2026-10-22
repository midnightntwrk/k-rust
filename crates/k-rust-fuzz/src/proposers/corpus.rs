//! The corpus proposer: coverage-guided mutation of kept cases (ARCHITECTURE 8.5). Owner:
//! FZ-14.
//!
//! # Why a corpus works
//!
//! A sequence-shaped hole, such as a `List` of transactions, reaches a deep rule only when
//! several of its elements are right at once, in order: blind sampling draws them all
//! independently, so its chance is the product of the chances of each. A case that gets the
//! first element right already reaches something no earlier case reached (the rule that
//! consumed it fired, and the next one's condition was entered), so keeping it and changing
//! its other elements turns a product of chances into a sum of them, one step per element.
//! The rule graph does not see that progress when the state lives in a cell and every step
//! keeps the same head on `<k>` (a loop over a list), and the climb's score is the distance of
//! whichever guard refuted the case last, which may grow when a case gets further; coverage
//! sees it.
//!
//! # The corpus
//!
//! The proposer observes every case, whichever proposer made it. A `miss` case enters the
//! corpus when its coverage holds a rule, in `applied` or `matched`, that no earlier `miss`
//! case's did (the engine's coverage feedback, ARCHITECTURE 6.2), or, in a campaign that
//! scores its cases (one with the climb), when its score is strictly better than every earlier
//! case's. Only `miss` cases count, as for the score: a bounded or unclean case's coverage
//! stops early (R-18). The corpus holds at most [`MAX_ENTRIES`] cases; beyond that a new entry
//! replaces the oldest one that entered for its score alone, or the oldest when every entry
//! entered for coverage. Until the corpus has an entry the proposer is not drawn
//! ([`Proposer::ready`]); the anchor case is usually the first entry.
//!
//! # Mutations
//!
//! A proposal takes the newest entry with probability [`NEWEST_PROBABILITY`], since the newest
//! is the case that got furthest most recently, and otherwise an entry chosen uniformly. It
//! applies one mutation to one hole, and a second with probability
//! [`SECOND_MUTATION_PROBABILITY`], each on a hole chosen uniformly among those with more than
//! one admissible value (two distinct holes, when there are two). Each mutation keeps the hole's sort:
//!
//! - a collection (`List`, `Set`, `Map`) changes one element (entry): replace one with a new
//!   value, insert one, delete one, keep only a prefix (a list), append one (a list), or cross
//!   over with the same hole of another entry (a list keeps a prefix of its own and a suffix of
//!   the other's; a set or map takes one element or entry of the other's), with the weights
//!   [`COLLECTION_WEIGHTS`];
//! - any other hole, and every new element, key or map value, takes a new value from one of
//!   four sources, with the weights [`SOURCE_WEIGHTS`]: a harvested literal of its sort (the
//!   dictionary's harvest, ARCHITECTURE 8.3: a literal of the target's guards and of those near
//!   it, itself or plus or minus 1 to 3 or negated, by the dictionary's weights), a fresh draw
//!   from its generator, a nudge of the current value (an integer by `±2^e` with `e` below
//!   [`NUDGE_EXPONENTS`], a Boolean negated, a string or byte string by one character edit), or
//!   a splice (the same hole's value in another entry; for an element, an element of the same
//!   hole in any entry);
//! - a hole with a choice set takes another member.
//!
//! The harvest is the dictionary's whether or not the dictionary has a weight, and it also
//! fills the elements, keys and values of collection holes, which the dictionary itself leaves
//! to blind generation. Every mutated hole value must be admissible (`values::admissible`, the
//! rule the dictionary and the climb use): a value of the hole's sort that satisfies its
//! constraints and the generator's size rules. A mutation that gives an inadmissible value, or
//! the value it started from, is drawn again, up to [`MAX_ATTEMPTS`] times; the proposal then
//! goes through the per-case round-trip check like any other, and is `rejected` when the
//! program's grammar refuses it.
//!
//! # Budget
//!
//! The corpus spends at most [`BUDGET_SHARE`] of the campaign's cases over every prefix, and
//! its work is held to the same share before each corpus case (`engine::schedule`), as the
//! climb's is. A campaign that weighs the corpus must also weigh blind sampling or the
//! dictionary.
//!
//! Every choice is drawn from a `ChaCha20` stream and a proptest runner seeded from the campaign
//! seed under purposes of their own (`corpus`, `corpus-values`), so the corpus's draws never
//! shift another proposer's streams. The parameters are recorded in the report
//! ([`crate::report::CorpusParameters`]).

use std::{collections::BTreeSet, sync::Arc};

use num_bigint::BigInt;
use num_traits::Zero as _;
use rand::{Rng as _, SeedableRng as _};
use rand_chacha::ChaCha20Rng;

use crate::{
    engine::proposer::{Observation, Origin, Proposal, ProposalContext, Proposer},
    exec::OutcomeClass,
    proposers::dictionary::{Harvest, HolePool},
    report::CorpusParameters,
    score::Score,
    spec::ProposerKind,
    values::{self, Constraints, GenerationBounds, Generator, Value, ValueRng, ValueSort},
};

/// The most share of the campaign's cases and work the corpus may spend, as (numerator,
/// denominator).
pub(crate) const BUDGET_SHARE: (u32, u32) = (1, 2);

/// The probability, as (numerator, denominator), that a proposal mutates the newest entry.
pub(crate) const NEWEST_PROBABILITY: (u32, u32) = (3, 4);

/// The probability, as (numerator, denominator), that a proposal applies a second mutation.
pub(crate) const SECOND_MUTATION_PROBABILITY: (u32, u32) = (1, 4);

/// The weights of a new value's sources: a harvested literal, a fresh draw, a nudge of the
/// current value, a splice from another entry. A source that does not apply (an empty pool, no
/// current value, a sort without nudges, no other entry) is left out of the draw.
pub(crate) const SOURCE_WEIGHTS: [u32; 4] = [3, 1, 1, 1];

/// The weights of a collection mutation: replace, insert, delete, keep a prefix, append, cross
/// over. Keeping a prefix and appending apply to lists only.
pub(crate) const COLLECTION_WEIGHTS: [u32; 6] = [4, 2, 1, 1, 1, 1];

/// A nudge of an integer moves it by `±2^e` with `e` uniform below this bound.
pub(crate) const NUDGE_EXPONENTS: u32 = 16;

/// The most cases the corpus keeps.
pub(crate) const MAX_ENTRIES: usize = 256;

/// The most draws of a mutation before it is given up.
pub(crate) const MAX_ATTEMPTS: u32 = 64;

/// The corpus's parameters as the report records them ([`CorpusParameters`]).
pub(crate) fn parameters() -> CorpusParameters {
    CorpusParameters {
        budget_share: [BUDGET_SHARE.0, BUDGET_SHARE.1],
        newest_probability: [NEWEST_PROBABILITY.0, NEWEST_PROBABILITY.1],
        second_mutation_probability: [SECOND_MUTATION_PROBABILITY.0, SECOND_MUTATION_PROBABILITY.1],
        source_weights: SOURCE_WEIGHTS,
        collection_weights: COLLECTION_WEIGHTS,
        nudge_exponents: NUDGE_EXPONENTS,
        max_entries: u32::try_from(MAX_ENTRIES).unwrap_or(u32::MAX),
        max_attempts: MAX_ATTEMPTS,
        harvest: crate::proposers::dictionary::parameters(),
    }
}

/// What the corpus needs of one hole.
pub(crate) struct CorpusHole {
    /// The hole's sort.
    pub(crate) sort: ValueSort,
    /// The hole's constraints.
    pub(crate) constraints: Constraints,
    /// The hole's generator.
    pub(crate) generator: Generator,
}

/// The sources of one kind of value: a whole hole's, or a collection's elements, keys or map
/// values.
struct Source {
    sort: ValueSort,
    generator: Option<Generator>,
    pool: HolePool,
}

impl Source {
    fn new(
        sort: &ValueSort,
        constraints: &Constraints,
        generator: Option<Generator>,
        harvest: &Harvest,
        bounds: &GenerationBounds,
    ) -> Self {
        Self {
            sort: sort.clone(),
            generator,
            pool: HolePool::new(harvest, sort, constraints, bounds),
        }
    }

    /// The sources of the elements (keys) and of a map's values of a hole of `sort`, drawn
    /// without constraints, as the generators draw nested values.
    fn nested(
        sort: &ValueSort,
        harvest: &Harvest,
        bounds: &GenerationBounds,
    ) -> (Option<Self>, Option<Self>) {
        let source = |sort: &ValueSort| {
            let constraints = Constraints::default();
            let generator = Generator::new(sort, &constraints, bounds).ok();
            Self::new(sort, &constraints, generator, harvest, bounds)
        };
        match sort.generated() {
            ValueSort::List { element, .. } | ValueSort::Set { element, .. } => {
                (Some(source(element)), None)
            }
            ValueSort::Map { key, value, .. } => (Some(source(key)), Some(source(value))),
            _ => (None, None),
        }
    }
}

/// One hole's sources.
struct HoleSources {
    whole: Source,
    elements: Option<Source>,
    values: Option<Source>,
}

/// Where a new value goes: a whole hole, or a collection's element, key or map value; a splice
/// reads the same place in other entries.
#[derive(Clone, Copy)]
enum Place {
    Whole,
    Element,
    Key,
    MapValue,
}

/// A kept case.
struct Entry {
    values: Vec<Value>,
    /// It entered for its score alone, not for coverage.
    score_only: bool,
}

/// The corpus proposer (module documentation).
pub(crate) struct CorpusProposer {
    holes: Vec<CorpusHole>,
    sources: Vec<HoleSources>,
    bounds: GenerationBounds,
    /// The holes a mutation can change: those with more than one admissible value.
    movable: Vec<usize>,
    rng: ChaCha20Rng,
    values: ValueRng,
    entries: Vec<Entry>,
    applied: BTreeSet<String>,
    matched: BTreeSet<String>,
    best: Option<Score>,
}

impl CorpusProposer {
    /// A corpus proposer over `holes`, in hole order, drawing literals from `harvest`, under
    /// `bounds`, seeded from the campaign seed `seed`.
    pub(crate) fn new(
        holes: Vec<CorpusHole>,
        harvest: &Arc<Harvest>,
        bounds: GenerationBounds,
        seed: u64,
    ) -> Self {
        let sources = holes
            .iter()
            .map(|hole| {
                let (elements, values) = Source::nested(&hole.sort, harvest, &bounds);
                HoleSources {
                    whole: Source::new(&hole.sort, &hole.constraints, None, harvest, &bounds),
                    elements,
                    values,
                }
            })
            .collect();
        let movable = holes
            .iter()
            .enumerate()
            .filter(|(_, hole)| match &hole.constraints.choices {
                Some(choices) => choices.len() > 1,
                None => !matches!(hole.sort.generated(), ValueSort::Token { .. }),
            })
            .map(|(index, _)| index)
            .collect();
        Self {
            holes,
            sources,
            bounds,
            movable,
            rng: ChaCha20Rng::from_seed(crate::engine::derive_seed(seed, "corpus")),
            values: ValueRng::from_seed(crate::engine::derive_seed(seed, "corpus-values")),
            entries: Vec::new(),
            applied: BTreeSet::new(),
            matched: BTreeSet::new(),
            best: None,
        }
    }

    /// The kept cases' values, oldest first, for tests.
    #[cfg(test)]
    pub(crate) fn entries(&self) -> Vec<&[Value]> {
        self.entries
            .iter()
            .map(|entry| entry.values.as_slice())
            .collect()
    }

    /// Keep `values`, which entered for its score alone when `score_only`.
    fn keep(&mut self, values: Vec<Value>, score_only: bool) {
        if self.entries.len() >= MAX_ENTRIES {
            let index = self
                .entries
                .iter()
                .position(|entry| entry.score_only)
                .unwrap_or(0);
            self.entries.remove(index);
        }
        self.entries.push(Entry { values, score_only });
    }

    /// `true` with probability `numerator / denominator`.
    fn ratio(&mut self, (numerator, denominator): (u32, u32)) -> bool {
        self.rng.random_ratio(numerator, denominator)
    }

    /// An index drawn by `weights`, among those `allowed`; `None` when none is allowed.
    fn pick(&mut self, weights: &[u32], allowed: &[bool]) -> Option<usize> {
        let total: u32 = weights
            .iter()
            .zip(allowed)
            .filter(|(_, allowed)| **allowed)
            .map(|(weight, _)| weight)
            .sum();
        if total == 0 {
            return None;
        }
        let mut draw = self.rng.random_range(0..total);
        weights.iter().zip(allowed).position(|(weight, allowed)| {
            if !allowed {
                return false;
            }
            if draw < *weight {
                true
            } else {
                draw -= weight;
                false
            }
        })
    }

    /// The source of `place` of hole `hole`.
    fn source(&self, hole: usize, place: Place) -> Option<&Source> {
        let sources = &self.sources[hole];
        match place {
            Place::Whole => Some(&sources.whole),
            Place::Element | Place::Key => sources.elements.as_ref(),
            Place::MapValue => sources.values.as_ref(),
        }
    }

    /// The values at `place` of hole `hole` in the other entries than `current` (an element:
    /// every element of the hole there).
    fn splices(&self, hole: usize, place: Place, current: usize) -> Vec<Value> {
        let mut found = Vec::new();
        for (index, entry) in self.entries.iter().enumerate() {
            let value = &entry.values[hole];
            match (place, value) {
                (Place::Whole, _) if index != current => found.push(value.clone()),
                (Place::Element, Value::List(items) | Value::Set(items)) => {
                    found.extend(items.iter().cloned());
                }
                (Place::Key, Value::Map(entries)) => {
                    found.extend(entries.iter().map(|(key, _)| key.clone()));
                }
                (Place::MapValue, Value::Map(entries)) => {
                    found.extend(entries.iter().map(|(_, value)| value.clone()));
                }
                _ => {}
            }
        }
        found
    }

    /// A new value for `place` of hole `hole`, from one of the sources ([`SOURCE_WEIGHTS`]);
    /// `current` is the value it replaces, if any; `entry` is the entry being mutated.
    fn new_value(
        &mut self,
        hole: usize,
        place: Place,
        current: Option<&Value>,
        entry: usize,
    ) -> Option<Value> {
        let source = self.source(hole, place)?;
        let sort = source.sort.clone();
        let nudgeable = current.is_some()
            && matches!(
                sort.generated(),
                ValueSort::Int
                    | ValueSort::MInt { .. }
                    | ValueSort::Bool
                    | ValueSort::String
                    | ValueSort::Bytes
            );
        let splices = self.splices(hole, place, entry);
        let allowed = [
            !source.pool.is_empty(),
            source.generator.is_some() || matches!(place, Place::Whole),
            nudgeable,
            !splices.is_empty(),
        ];
        match self.pick(&SOURCE_WEIGHTS, &allowed)? {
            0 => {
                let pool = &self.sources[hole];
                let pool = match place {
                    Place::Whole => &pool.whole.pool,
                    Place::Element | Place::Key => &pool.elements.as_ref()?.pool,
                    Place::MapValue => &pool.values.as_ref()?.pool,
                };
                pool.draw(&mut self.rng)
            }
            1 => {
                let sources = &self.sources[hole];
                let generator = match place {
                    Place::Whole => &self.holes[hole].generator,
                    Place::Element | Place::Key => sources.elements.as_ref()?.generator.as_ref()?,
                    Place::MapValue => sources.values.as_ref()?.generator.as_ref()?,
                };
                generator
                    .try_generate(&mut self.values)
                    .ok()
                    .map(|tree| tree.current())
            }
            2 => self.nudge(current?, &sort),
            _ => Some(splices[self.rng.random_range(0..splices.len())].clone()),
        }
    }

    /// A small change of `value` of `sort`: an integer by `±2^e` ([`NUDGE_EXPONENTS`]), a
    /// Boolean negated, a string or byte string by one character (byte) deleted, inserted or
    /// replaced.
    fn nudge(&mut self, value: &Value, sort: &ValueSort) -> Option<Value> {
        match (value, sort.generated()) {
            (Value::Int(number), ValueSort::Int) => {
                let step = BigInt::from(1u8) << self.rng.random_range(0..NUDGE_EXPONENTS);
                Some(Value::Int(if self.rng.random() {
                    number + step
                } else {
                    number - step
                }))
            }
            (Value::MInt { width, value }, ValueSort::MInt { .. }) => {
                let step = BigInt::from(1u8) << self.rng.random_range(0..NUDGE_EXPONENTS);
                let number = BigInt::from(value.clone());
                let moved = if self.rng.random() {
                    number + step
                } else {
                    number - step
                };
                let top = (BigInt::from(1u8) << *width) - 1u8;
                Some(Value::MInt {
                    width: *width,
                    value: moved.clamp(BigInt::zero(), top).to_biguint()?,
                })
            }
            (Value::Bool(flag), ValueSort::Bool) => Some(Value::Bool(!flag)),
            (Value::String(text), ValueSort::String) => {
                let mut characters: Vec<char> = text.chars().collect();
                let character = char::from(self.rng.random_range(0x20u8..=0x7e));
                self.edit(&mut characters, character);
                Some(Value::String(characters.into_iter().collect()))
            }
            (Value::Bytes(bytes), ValueSort::Bytes) => {
                let mut bytes = bytes.clone();
                let byte = self.rng.random::<u8>();
                self.edit(&mut bytes, byte);
                Some(Value::Bytes(bytes))
            }
            _ => None,
        }
    }

    /// Delete, insert or replace one item of `items`.
    fn edit<T>(&mut self, items: &mut Vec<T>, fresh: T) {
        let choice = if items.is_empty() {
            1
        } else {
            self.rng.random_range(0..3)
        };
        match choice {
            0 => {
                let index = self.rng.random_range(0..items.len());
                items.remove(index);
            }
            1 => {
                let index = self.rng.random_range(0..=items.len());
                items.insert(index, fresh);
            }
            _ => {
                let index = self.rng.random_range(0..items.len());
                items[index] = fresh;
            }
        }
    }

    /// One mutation of hole `hole`'s value `value` in entry `entry`, or `None` when the drawn
    /// mutation does not apply.
    fn mutate(&mut self, hole: usize, value: &Value, entry: usize) -> Option<Value> {
        if let Some(choices) = &self.holes[hole].constraints.choices {
            return Some(choices[self.rng.random_range(0..choices.len())].clone());
        }
        match value {
            Value::List(items) => self.mutate_list(hole, items, entry).map(Value::List),
            Value::Set(items) => self.mutate_set(hole, items, entry).map(Value::Set),
            Value::Map(entries) => self.mutate_map(hole, entries, entry).map(Value::Map),
            _ => self.new_value(hole, Place::Whole, Some(value), entry),
        }
    }

    /// The other entries' lists, sets or maps of hole `hole`, for a crossover.
    fn partners(&self, hole: usize, entry: usize) -> Vec<Value> {
        self.entries
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != entry)
            .map(|(_, other)| other.values[hole].clone())
            .collect()
    }

    fn mutate_list(&mut self, hole: usize, items: &[Value], entry: usize) -> Option<Vec<Value>> {
        let partners = self.partners(hole, entry);
        let nonempty = !items.is_empty();
        let allowed = [
            nonempty,
            true,
            nonempty,
            nonempty,
            true,
            !partners.is_empty(),
        ];
        let mut items = items.to_vec();
        match self.pick(&COLLECTION_WEIGHTS, &allowed)? {
            0 => {
                let index = self.rng.random_range(0..items.len());
                items[index] = self.new_value(hole, Place::Element, Some(&items[index]), entry)?;
            }
            1 => {
                let index = self.rng.random_range(0..=items.len());
                let value = self.new_value(hole, Place::Element, None, entry)?;
                items.insert(index, value);
            }
            2 => {
                let index = self.rng.random_range(0..items.len());
                items.remove(index);
            }
            3 => {
                let length = self.rng.random_range(0..items.len());
                items.truncate(length);
            }
            4 => {
                let value = self.new_value(hole, Place::Element, None, entry)?;
                items.push(value);
            }
            _ => {
                let Value::List(other) = &partners[self.rng.random_range(0..partners.len())] else {
                    return None;
                };
                let cut = self.rng.random_range(0..=items.len());
                let from = self.rng.random_range(0..=other.len());
                items.truncate(cut);
                items.extend_from_slice(&other[from..]);
            }
        }
        Some(items)
    }

    fn mutate_set(&mut self, hole: usize, items: &[Value], entry: usize) -> Option<Vec<Value>> {
        let partners = self.partners(hole, entry);
        let nonempty = !items.is_empty();
        let allowed = [nonempty, true, nonempty, false, false, !partners.is_empty()];
        let mut items = items.to_vec();
        match self.pick(&COLLECTION_WEIGHTS, &allowed)? {
            0 => {
                let index = self.rng.random_range(0..items.len());
                items[index] = self.new_value(hole, Place::Element, Some(&items[index]), entry)?;
            }
            1 => items.push(self.new_value(hole, Place::Element, None, entry)?),
            2 => {
                let index = self.rng.random_range(0..items.len());
                items.remove(index);
            }
            _ => {
                let Value::Set(other) = &partners[self.rng.random_range(0..partners.len())] else {
                    return None;
                };
                if other.is_empty() {
                    return None;
                }
                items.push(other[self.rng.random_range(0..other.len())].clone());
            }
        }
        sorted_distinct(items)
    }

    fn mutate_map(
        &mut self,
        hole: usize,
        entries: &[(Value, Value)],
        entry: usize,
    ) -> Option<Vec<(Value, Value)>> {
        let partners = self.partners(hole, entry);
        let nonempty = !entries.is_empty();
        let allowed = [nonempty, true, nonempty, false, false, !partners.is_empty()];
        let mut entries = entries.to_vec();
        match self.pick(&COLLECTION_WEIGHTS, &allowed)? {
            0 => {
                // Replace an entry's value, or its key half of the time.
                let index = self.rng.random_range(0..entries.len());
                if self.rng.random() {
                    let key = self.new_value(hole, Place::Key, Some(&entries[index].0), entry)?;
                    entries[index].0 = key;
                } else {
                    let value =
                        self.new_value(hole, Place::MapValue, Some(&entries[index].1), entry)?;
                    entries[index].1 = value;
                }
            }
            1 => {
                let key = self.new_value(hole, Place::Key, None, entry)?;
                let value = self.new_value(hole, Place::MapValue, None, entry)?;
                entries.push((key, value));
            }
            2 => {
                let index = self.rng.random_range(0..entries.len());
                entries.remove(index);
            }
            _ => {
                let Value::Map(other) = &partners[self.rng.random_range(0..partners.len())] else {
                    return None;
                };
                if other.is_empty() {
                    return None;
                }
                let taken = other[self.rng.random_range(0..other.len())].clone();
                entries.retain(|(key, _)| *key != taken.0);
                entries.push(taken);
            }
        }
        entries.sort_by(|a, b| a.0.cmp(&b.0));
        entries
            .windows(2)
            .all(|pair| pair[0].0 != pair[1].0)
            .then_some(entries)
    }

    /// One admissible mutation of hole `hole` from `value`, or `None` when none was drawn in
    /// [`MAX_ATTEMPTS`].
    fn mutate_hole(&mut self, hole: usize, value: &Value, entry: usize) -> Option<Value> {
        for _ in 0..MAX_ATTEMPTS {
            if let Some(candidate) = self.mutate(hole, value, entry)
                && candidate != *value
                && values::admissible(
                    &candidate,
                    &self.holes[hole].sort,
                    &self.holes[hole].constraints,
                    &self.bounds,
                )
            {
                return Some(candidate);
            }
        }
        None
    }
}

impl Proposer for CorpusProposer {
    fn kind(&self) -> ProposerKind {
        ProposerKind::Corpus
    }

    fn ready(&self) -> bool {
        !self.entries.is_empty() && !self.movable.is_empty()
    }

    fn budget_share(&self) -> Option<(u32, u32)> {
        Some(BUDGET_SHARE)
    }

    fn propose(&mut self, _context: &mut ProposalContext<'_>) -> Option<Proposal> {
        let last = self.entries.len().checked_sub(1)?;
        let entry = if self.ratio(NEWEST_PROBABILITY) {
            last
        } else {
            self.rng.random_range(0..=last)
        };
        let mut values = self.entries[entry].values.clone();
        let count = if self.ratio(SECOND_MUTATION_PROBABILITY) {
            2
        } else {
            1
        };
        // Distinct holes, so that a second mutation never undoes the first.
        let mut holes = self.movable.clone();
        let mut moved = false;
        for _ in 0..count.min(holes.len()) {
            let hole = holes.swap_remove(self.rng.random_range(0..holes.len()));
            let current = values[hole].clone();
            if let Some(value) = self.mutate_hole(hole, &current, entry) {
                values[hole] = value;
                moved = true;
            }
        }
        // No admissible mutation of the drawn holes: try every movable hole in order rather
        // than spend a case on the entry's own values.
        if !moved {
            for hole in self.movable.clone() {
                let current = values[hole].clone();
                if let Some(value) = self.mutate_hole(hole, &current, entry) {
                    values[hole] = value;
                    break;
                }
            }
        }
        Some(Proposal::plain(
            Origin::Scheduled(ProposerKind::Corpus),
            values,
        ))
    }

    fn observe(&mut self, _proposal: &Proposal, _observation: &Observation, _interesting: bool) {}

    fn observe_all(&mut self, proposal: &Proposal, observation: &Observation) {
        if observation.class != OutcomeClass::Miss {
            return;
        }
        let mut new = false;
        for rule in &observation.applied {
            new |= self.applied.insert(rule.clone());
        }
        for rule in &observation.matched {
            new |= self.matched.insert(rule.clone());
        }
        let better = observation
            .score
            .as_ref()
            .is_some_and(|score| self.best.as_ref().is_none_or(|best| score < best));
        if better {
            self.best.clone_from(&observation.score);
        }
        if new || better {
            self.keep(proposal.values.clone(), !new);
        }
    }
}

/// `items` sorted, or `None` when two are equal (a set's elements are distinct).
fn sorted_distinct(mut items: Vec<Value>) -> Option<Vec<Value>> {
    items.sort();
    items
        .windows(2)
        .all(|pair| pair[0] != pair[1])
        .then_some(items)
}

#[cfg(test)]
#[path = "corpus_tests.rs"]
mod tests;
