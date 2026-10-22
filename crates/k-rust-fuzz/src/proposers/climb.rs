//! The climb proposer: targeted hill climbing over typed holes (ARCHITECTURE 8.4). Owner:
//! FZ-12.
//!
//! # Why climbing works
//!
//! A guard such as `1000 <Int D andBool D <Int 1100` holds on a set of values blind sampling
//! almost never draws, but its guard distance (`crate::score`) falls as `D` approaches the
//! window, so a sequence of small changes that each keep the distance from rising walks `D`
//! into it. The proposer keeps the best-scored `miss` case of the campaign and proposes small
//! typed changes of it, as Hypothesis's `target()` does: the holes have sorts, so a neighbour
//! of a value is a value of the same sort.
//!
//! # The incumbent
//!
//! The incumbent is the best-scored case so far ([`crate::score::Score`], smaller is better).
//! A case another proposer made (explicit, blind, dictionary) replaces it only when it scores
//! strictly better; a case the climb proposed replaces it when it scores no worse
//! ([`ACCEPT_EQUAL`]): accepting equal scores lets the climb cross plateaus where one hole's
//! change does not move the distance until another's does (`C <Int -1 andBool D ==Int C` moves
//! `C` and then `D`). A case without a score (any class but `miss`, or a run whose signals give
//! none) never replaces it. Until a case is scored the proposer has nothing to climb from and
//! is not drawn ([`Proposer::ready`]).
//!
//! # Moves
//!
//! A proposal changes one hole of the incumbent, or two with probability
//! [`SECOND_HOLE_PROBABILITY`], each by one typed move. A hole is picked, with probability
//! [`READ_PROBABILITY`], among those whose value the incumbent's scored guard read: the
//! condition records bind the guard's variables, and a hole whose value reaches the guard
//! unchanged appears among those bindings (input-to-state correspondence, as in Redqueen; in K
//! it is exact for a value matched into the rule unchanged). Otherwise any hole is picked, so a
//! hole that reaches the guard only through a computation still moves.
//!
//! - `Int` and `MInt`: `v + 2^e` or `v - 2^e`. Each hole has its own exponent `e`, starting at
//!   [`INITIAL_EXPONENT`]: it grows by one after a move of the hole that improved the score and
//!   shrinks by one after a move that was rejected, so that steps accelerate along a slope and
//!   refine near the goal; each hole also remembers the direction of its last improvement and
//!   turns around after a rejection. With probability [`JUMP_PROBABILITY`] the exponent of one
//!   move is drawn uniformly up to the hole's bit bound instead, which escapes a step size that
//!   shrank too far. A move past a range's end lands on the end.
//! - `Bool`: the negation.
//! - `String` and `Bytes`: delete, insert or replace one character or byte.
//! - `List`, `Set` and `Map`: remove one element (entry), insert one freshly generated
//!   element (entry), or change one element (a map entry's value or key) by a move of its sort.
//! - a data sort: swap the constructor for another of the same entry with the same argument
//!   sorts, keeping the arguments; change one argument by a move of its sort; or draw the whole
//!   value afresh from the hole's generator.
//! - a hole with a choice set: another member.
//!
//! Every candidate value must be admissible before it is proposed (`values::admissible`, the
//! rule the dictionary also uses): a value of
//! the hole's sort that satisfies its constraints (`values::check_constraints`) and the
//! generator's size rules (the integer bit bound, the length bound, the data depth bound, the
//! value-size budget). A move that gives an inadmissible value is drawn again, up to
//! [`MAX_ATTEMPTS`] times; the proposal then goes through the per-case round-trip check like
//! any other, and is `rejected` when the program's grammar refuses it.
//!
//! # Budget
//!
//! The climb spends at most [`BUDGET_SHARE`] of the campaign's cases, over every prefix of the
//! campaign: the schedule draws it only while its cases, counting the one it would add, stay
//! within the share. Its work is held to the same share before each climb case: the schedule
//! draws it only while the work it has spent is at most half of all work so far. A case's work
//! is known only after it runs, so the climb's work can exceed half by the work of its last case
//! (at most the case's `max_work`), and no more ([`Proposer::budget_share`],
//! `engine::schedule`). A campaign that enables
//! the climb must also give blind sampling or the dictionary a weight, which make the cases it
//! climbs from and spend the rest.
//!
//! Every choice is drawn from `ChaCha20` streams and a proptest runner seeded from the campaign
//! seed under purposes of their own (`climb`, `climb-values`), so the climb's draws never shift
//! another proposer's streams. The parameters are recorded in the report
//! ([`crate::report::ClimbParameters`]).

use num_bigint::BigInt;
use num_traits::Zero as _;
use rand::{Rng as _, SeedableRng as _};
use rand_chacha::ChaCha20Rng;

use crate::{
    engine::proposer::{Observation, Origin, Proposal, ProposalContext, Proposer},
    report::ClimbParameters,
    score::{Operand, Score},
    spec::ProposerKind,
    values::{
        self, ArgumentSort, Constraints, DataAlternative, DataSorts, GenerationBounds, Generator,
        Value, ValueRng, ValueSort,
    },
};

/// The exponent of a hole's first integer move: a step of `2^0 = 1`.
pub(crate) const INITIAL_EXPONENT: u32 = 0;

/// The probability, as (numerator, denominator), that a proposal changes a second hole.
pub(crate) const SECOND_HOLE_PROBABILITY: (u32, u32) = (1, 4);

/// The probability, as (numerator, denominator), that an integer move draws its exponent
/// uniformly up to the hole's bit bound instead of using the hole's adaptive exponent.
pub(crate) const JUMP_PROBABILITY: (u32, u32) = (1, 8);

/// The probability, as (numerator, denominator), that an integer move goes in the direction of
/// the hole's last improvement.
pub(crate) const KEEP_DIRECTION_PROBABILITY: (u32, u32) = (3, 4);

/// The most share of the campaign's cases and work the climb may spend, as (numerator,
/// denominator) (ARCHITECTURE 8.4: at most half).
pub(crate) const BUDGET_SHARE: (u32, u32) = (1, 2);

/// The probability, as (numerator, denominator), that a move picks a hole whose value the
/// incumbent's scored guard read, when there is one.
pub(crate) const READ_PROBABILITY: (u32, u32) = (3, 4);

/// A climb case that scores equal to the incumbent replaces it (module documentation).
pub(crate) const ACCEPT_EQUAL: bool = true;

/// The most draws of a move per proposal before the proposer gives up on admissibility and
/// proposes the incumbent's values changed in whichever holes did move.
pub(crate) const MAX_ATTEMPTS: u32 = 64;

/// The climb's parameters as the report records them ([`ClimbParameters`]).
pub(crate) fn parameters() -> ClimbParameters {
    ClimbParameters {
        budget_share: [BUDGET_SHARE.0, BUDGET_SHARE.1],
        initial_exponent: INITIAL_EXPONENT,
        jump_probability: [JUMP_PROBABILITY.0, JUMP_PROBABILITY.1],
        keep_direction_probability: [KEEP_DIRECTION_PROBABILITY.0, KEEP_DIRECTION_PROBABILITY.1],
        second_hole_probability: [SECOND_HOLE_PROBABILITY.0, SECOND_HOLE_PROBABILITY.1],
        read_probability: [READ_PROBABILITY.0, READ_PROBABILITY.1],
        accept_equal: ACCEPT_EQUAL,
        max_attempts: MAX_ATTEMPTS,
        condition_rules: "target-and-keyed-predecessors".into(),
        condition_limit: u64::try_from(k_rust::k_rust_backend::coverage::DEFAULT_CONDITION_LIMIT)
            .unwrap_or(u64::MAX),
        condition_value_size: u64::try_from(
            k_rust::k_rust_backend::coverage::DEFAULT_MAX_VALUE_SIZE,
        )
        .unwrap_or(u64::MAX),
    }
}

/// What the climb needs of one hole.
pub(crate) struct ClimbHole {
    /// The hole's sort.
    pub(crate) sort: ValueSort,
    /// The hole's constraints.
    pub(crate) constraints: Constraints,
    /// The hole's generator, for data values drawn afresh.
    pub(crate) generator: Generator,
}

/// Generators of the elements a collection move inserts: the element (or key) and, for a map,
/// the value.
struct Elements {
    element: Option<Generator>,
    value: Option<Generator>,
}

/// An integer move of one hole, remembered until its case is observed.
#[derive(Clone, Copy, Debug)]
struct Step {
    hole: usize,
    exponent: u32,
    up: bool,
}

/// The best-scored case so far, and the values its scored guard read.
#[derive(Clone, Debug)]
pub(crate) struct Incumbent {
    pub(crate) score: Score,
    pub(crate) values: Vec<Value>,
    reads: Vec<Operand>,
}

impl Incumbent {
    fn of(proposal: &Proposal, observation: &Observation) -> Option<Self> {
        Some(Self {
            score: observation.score.clone()?,
            values: proposal.values.clone(),
            reads: observation.reads.clone(),
        })
    }
}

/// The climb proposer (module documentation).
pub(crate) struct ClimbProposer {
    holes: Vec<ClimbHole>,
    elements: Vec<Elements>,
    bounds: GenerationBounds,
    /// The holes a move can change: those with more than one admissible value.
    movable: Vec<usize>,
    rng: ChaCha20Rng,
    values: ValueRng,
    incumbent: Option<Incumbent>,
    /// Per hole, the exponent of its next integer move and the direction of its last
    /// improvement (`true`: up).
    exponents: Vec<u32>,
    directions: Vec<bool>,
    /// The integer moves of the last proposal.
    pending: Vec<Step>,
}

impl ClimbProposer {
    /// A climb proposer over `holes`, in hole order, under `bounds`, seeded from the campaign
    /// seed `seed`.
    pub(crate) fn new(holes: Vec<ClimbHole>, bounds: GenerationBounds, seed: u64) -> Self {
        let elements = holes
            .iter()
            .map(|hole| {
                let generator =
                    |sort: &ValueSort| Generator::new(sort, &Constraints::default(), &bounds).ok();
                match hole.sort.generated() {
                    ValueSort::List { element, .. } | ValueSort::Set { element, .. } => Elements {
                        element: generator(element),
                        value: None,
                    },
                    ValueSort::Map { key, value, .. } => Elements {
                        element: generator(key),
                        value: generator(value),
                    },
                    _ => Elements {
                        element: None,
                        value: None,
                    },
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
        let count = holes.len();
        Self {
            holes,
            elements,
            bounds,
            movable,
            rng: ChaCha20Rng::from_seed(crate::engine::derive_seed(seed, "climb")),
            values: ValueRng::from_seed(crate::engine::derive_seed(seed, "climb-values")),
            incumbent: None,
            exponents: vec![INITIAL_EXPONENT; count],
            directions: vec![true; count],
            pending: Vec::new(),
        }
    }

    /// The incumbent, for tests.
    #[cfg(test)]
    pub(crate) fn incumbent(&self) -> Option<&Incumbent> {
        self.incumbent.as_ref()
    }

    /// A hole to move, other than `except`: with probability [`READ_PROBABILITY`] one whose
    /// incumbent value the scored guard read, when there is one, and otherwise any movable hole.
    fn pick_hole(&mut self, except: Option<usize>) -> Option<usize> {
        let incumbent = self.incumbent.as_ref()?;
        let read: Vec<usize> = self
            .movable
            .iter()
            .copied()
            .filter(|hole| {
                Some(*hole) != except && was_read(&incumbent.values[*hole], &incumbent.reads)
            })
            .collect();
        let candidates = if !read.is_empty()
            && self
                .rng
                .random_ratio(READ_PROBABILITY.0, READ_PROBABILITY.1)
        {
            read
        } else {
            self.movable
                .iter()
                .copied()
                .filter(|hole| Some(*hole) != except)
                .collect()
        };
        (!candidates.is_empty()).then(|| candidates[self.rng.random_range(0..candidates.len())])
    }

    /// The largest exponent of an integer move of `hole`: a step below the hole's bit bound.
    fn max_exponent(&self, hole: usize) -> u32 {
        match self.holes[hole].sort.generated() {
            ValueSort::MInt { width } => width.saturating_sub(1),
            _ => self.bounds.int_bits.saturating_sub(1),
        }
    }

    /// One admissible move of hole `hole` from `value`, with the integer step it took, or
    /// `None` when no admissible move was drawn.
    fn move_hole(&mut self, hole: usize, value: &Value) -> Option<(Value, Option<Step>)> {
        for _ in 0..MAX_ATTEMPTS {
            let (candidate, step) = self.draw_move(hole, value);
            if let Some(candidate) = candidate
                && candidate != *value
                && values::admissible(
                    &candidate,
                    &self.holes[hole].sort,
                    &self.holes[hole].constraints,
                    &self.bounds,
                )
            {
                return Some((candidate, step));
            }
        }
        None
    }

    fn draw_move(&mut self, hole: usize, value: &Value) -> (Option<Value>, Option<Step>) {
        if let Some(choices) = &self.holes[hole].constraints.choices {
            let choice = choices[self.rng.random_range(0..choices.len())].clone();
            return (Some(choice), None);
        }
        let sort = self.holes[hole].sort.generated().clone();
        match (&sort, value) {
            (ValueSort::Int | ValueSort::MInt { .. }, Value::Int(_) | Value::MInt { .. }) => {
                let jump = self
                    .rng
                    .random_ratio(JUMP_PROBABILITY.0, JUMP_PROBABILITY.1);
                let exponent = if jump {
                    self.rng.random_range(0..=self.max_exponent(hole))
                } else {
                    self.exponents[hole].min(self.max_exponent(hole))
                };
                let keep = self
                    .rng
                    .random_ratio(KEEP_DIRECTION_PROBABILITY.0, KEEP_DIRECTION_PROBABILITY.1);
                let up = self.directions[hole] == keep;
                let candidate = step_int(value, exponent, up, &self.holes[hole].constraints);
                (candidate, Some(Step { hole, exponent, up }))
            }
            (ValueSort::Data { table, .. }, _) => {
                // One move in three draws the value afresh from the hole's generator.
                if self.rng.random_ratio(1, 3) {
                    let fresh = self.holes[hole]
                        .generator
                        .try_generate(&mut self.values)
                        .ok()
                        .map(|tree| tree.current());
                    (fresh, None)
                } else {
                    let table = table.clone();
                    (self.move_data(value, &table, 0), None)
                }
            }
            (ValueSort::List { .. } | ValueSort::Set { .. } | ValueSort::Map { .. }, _) => {
                (self.move_collection(hole, value, &sort), None)
            }
            _ => (self.move_value(value, &sort), None),
        }
    }

    /// A move of a value of `sort` nested in a hole (an element, an argument): integer moves
    /// draw their exponent uniformly, and collections insert no fresh elements.
    fn move_value(&mut self, value: &Value, sort: &ValueSort) -> Option<Value> {
        match (value, sort.generated()) {
            (Value::Int(_), ValueSort::Int) => {
                let exponent = self.rng.random_range(0..self.bounds.int_bits.max(1));
                step_int(value, exponent, self.rng.random(), &Constraints::default())
            }
            (Value::MInt { .. }, ValueSort::MInt { width }) => {
                let exponent = self.rng.random_range(0..(*width).max(1));
                step_int(value, exponent, self.rng.random(), &Constraints::default())
            }
            (Value::Bool(flag), ValueSort::Bool) => Some(Value::Bool(!flag)),
            (Value::String(text), ValueSort::String) => {
                let mut characters: Vec<char> = text.chars().collect();
                let character = self.character();
                self.edit(&mut characters, character);
                Some(Value::String(characters.into_iter().collect()))
            }
            (Value::Bytes(bytes), ValueSort::Bytes) => {
                let mut bytes = bytes.clone();
                let byte = self.rng.random::<u8>();
                self.edit(&mut bytes, byte);
                Some(Value::Bytes(bytes))
            }
            (Value::List(items), ValueSort::List { element, .. }) if !items.is_empty() => {
                let mut items = items.clone();
                let index = self.rng.random_range(0..items.len());
                if self.rng.random() {
                    items.remove(index);
                } else {
                    items[index] = self.move_value(&items[index], element)?;
                }
                Some(Value::List(items))
            }
            (Value::Set(items), ValueSort::Set { element, .. }) if !items.is_empty() => {
                let mut items = items.clone();
                let index = self.rng.random_range(0..items.len());
                if self.rng.random() {
                    items.remove(index);
                } else {
                    items[index] = self.move_value(&items[index], element)?;
                }
                sorted_distinct(items).map(Value::Set)
            }
            (
                Value::Map(entries),
                ValueSort::Map {
                    key, value: sort, ..
                },
            ) if !entries.is_empty() => {
                let mut entries = entries.clone();
                let index = self.rng.random_range(0..entries.len());
                match self.rng.random_range(0..3) {
                    0 => {
                        entries.remove(index);
                    }
                    1 => entries[index].1 = self.move_value(&entries[index].1, sort)?,
                    _ => {
                        // A moved key must stay distinct from the others.
                        let moved = self.move_value(&entries[index].0, key)?;
                        if entries.iter().any(|(other, _)| *other == moved) {
                            return None;
                        }
                        entries[index].0 = moved;
                        entries.sort_by(|a, b| a.0.cmp(&b.0));
                    }
                }
                Some(Value::Map(entries))
            }
            (_, ValueSort::Data { table, .. }) => {
                let table = table.clone();
                self.move_data(value, &table, 0)
            }
            _ => None,
        }
    }

    /// A move of a collection hole: remove, insert a fresh element (entry), or change one.
    fn move_collection(&mut self, hole: usize, value: &Value, sort: &ValueSort) -> Option<Value> {
        let insert = self.rng.random_ratio(1, 3);
        if !insert {
            return self.move_value(value, sort);
        }
        let element = self.elements[hole]
            .element
            .as_ref()?
            .try_generate(&mut self.values)
            .ok()?
            .current();
        match value {
            Value::List(items) => {
                let mut items = items.clone();
                let index = self.rng.random_range(0..=items.len());
                items.insert(index, element);
                Some(Value::List(items))
            }
            Value::Set(items) => {
                let mut items = items.clone();
                items.push(element);
                sorted_distinct(items).map(Value::Set)
            }
            Value::Map(entries) => {
                let entry = self.elements[hole]
                    .value
                    .as_ref()?
                    .try_generate(&mut self.values)
                    .ok()?
                    .current();
                if entries.iter().any(|(key, _)| *key == element) {
                    return None;
                }
                let mut entries = entries.clone();
                entries.push((element, entry));
                entries.sort_by(|a, b| a.0.cmp(&b.0));
                Some(Value::Map(entries))
            }
            _ => None,
        }
    }

    /// A move of a value of entry `index` of the data-sort table `table`: another constructor
    /// with the same argument sorts, or a move of one argument.
    fn move_data(&mut self, value: &Value, table: &DataSorts, index: usize) -> Option<Value> {
        match values::data_alternative(value, table, index).ok()? {
            DataAlternative::Subsort(ArgumentSort::Value(sort)) => self.move_value(value, sort),
            DataAlternative::Subsort(_) => None,
            DataAlternative::Constructor(constructor) => {
                let Value::Apply { symbol, arguments } = value else {
                    return None;
                };
                let swaps: Vec<&str> = table.sorts[index]
                    .constructors
                    .iter()
                    .filter(|other| {
                        other.symbol != *symbol && other.arguments == constructor.arguments
                    })
                    .map(|other| other.symbol.as_str())
                    .collect();
                if arguments.is_empty() || (!swaps.is_empty() && self.rng.random()) {
                    let swap = *swaps.get(self.rng.random_range(0..swaps.len().max(1)))?;
                    return Some(Value::Apply {
                        symbol: swap.to_owned(),
                        arguments: arguments.clone(),
                    });
                }
                let position = self.rng.random_range(0..arguments.len());
                let moved = match &constructor.arguments[position] {
                    ArgumentSort::Value(sort) => self.move_value(&arguments[position], sort)?,
                    ArgumentSort::Data(child) => {
                        self.move_data(&arguments[position], table, *child)?
                    }
                    ArgumentSort::Empty(_) => return None,
                };
                let mut arguments = arguments.clone();
                arguments[position] = moved;
                Some(Value::Apply {
                    symbol: symbol.clone(),
                    arguments,
                })
            }
        }
    }

    /// Delete, insert or replace one item of `items`; `fresh` is the item an insertion or a
    /// replacement writes.
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

    /// A character for a string move: printable ASCII three times in four, otherwise any
    /// Unicode scalar value.
    fn character(&mut self) -> char {
        if self.rng.random_ratio(3, 4) {
            char::from(self.rng.random_range(0x20u8..=0x7e))
        } else {
            loop {
                if let Some(character) = char::from_u32(self.rng.random_range(0..0x11_0000)) {
                    return character;
                }
            }
        }
    }

    /// Adapt the exponents and directions of the last proposal's integer moves to its verdict:
    /// `Some(true)` an improvement, `Some(false)` an equal score, `None` a rejection.
    fn adapt(&mut self, improved: Option<bool>) {
        for step in std::mem::take(&mut self.pending) {
            match improved {
                Some(true) => {
                    self.exponents[step.hole] =
                        (step.exponent + 1).min(self.max_exponent(step.hole));
                    self.directions[step.hole] = step.up;
                }
                Some(false) => {}
                None => {
                    self.exponents[step.hole] = self.exponents[step.hole].saturating_sub(1);
                    self.directions[step.hole] = !step.up;
                }
            }
        }
    }
}

impl Proposer for ClimbProposer {
    fn kind(&self) -> ProposerKind {
        ProposerKind::Climb
    }

    fn ready(&self) -> bool {
        self.incumbent.is_some() && !self.movable.is_empty()
    }

    fn budget_share(&self) -> Option<(u32, u32)> {
        Some(BUDGET_SHARE)
    }

    fn propose(&mut self, _context: &mut ProposalContext<'_>) -> Option<Proposal> {
        let mut values = self.incumbent.as_ref()?.values.clone();
        let first = self.pick_hole(None)?;
        let mut holes = vec![first];
        if self
            .rng
            .random_ratio(SECOND_HOLE_PROBABILITY.0, SECOND_HOLE_PROBABILITY.1)
        {
            holes.extend(self.pick_hole(Some(first)));
        }
        self.pending.clear();
        let mut moved = false;
        for hole in holes {
            if let Some((value, step)) = self.move_hole(hole, &values[hole]) {
                values[hole] = value;
                self.pending.extend(step);
                moved = true;
            }
        }
        // No admissible move of the picked holes: try every movable hole in order rather than
        // spend a case on the incumbent's own values.
        if !moved {
            for hole in self.movable.clone() {
                if let Some((value, step)) = self.move_hole(hole, &values[hole]) {
                    values[hole] = value;
                    self.pending.extend(step);
                    break;
                }
            }
        }
        Some(Proposal::plain(
            Origin::Scheduled(ProposerKind::Climb),
            values,
        ))
    }

    fn observe(&mut self, proposal: &Proposal, observation: &Observation, _interesting: bool) {
        let best = self.incumbent.as_ref().map(|incumbent| &incumbent.score);
        let verdict = match (&observation.score, best) {
            (Some(score), Some(best)) if score < best => Some(true),
            (Some(score), Some(best)) if ACCEPT_EQUAL && score == best => Some(false),
            (Some(_), None) => Some(true),
            _ => None,
        };
        if verdict.is_some() {
            self.incumbent = Incumbent::of(proposal, observation);
        }
        self.adapt(verdict);
    }

    fn observe_all(&mut self, proposal: &Proposal, observation: &Observation) {
        if proposal.origin == Origin::Scheduled(ProposerKind::Climb) {
            return;
        }
        if let Some(score) = &observation.score
            && self
                .incumbent
                .as_ref()
                .is_none_or(|incumbent| *score < incumbent.score)
        {
            self.incumbent = Incumbent::of(proposal, observation);
        }
    }
}

/// Whether `value` is among the values a scored guard read (an `Int` or `String` hole whose
/// value reached the guard unchanged).
fn was_read(value: &Value, reads: &[Operand]) -> bool {
    reads.iter().any(|read| match (value, read) {
        (Value::Int(number), Operand::Int(read)) => number == read,
        (Value::String(text), Operand::Str(read)) => text == read,
        _ => false,
    })
}

/// `value` moved by `2^exponent` up or down, landing on a range's end when it would pass it;
/// an `MInt` stays within `0 .. 2^width`.
fn step_int(value: &Value, exponent: u32, up: bool, constraints: &Constraints) -> Option<Value> {
    let step = BigInt::from(1u8) << exponent;
    let (current, width) = match value {
        Value::Int(number) => (number.clone(), None),
        Value::MInt { width, value } => (BigInt::from(value.clone()), Some(*width)),
        _ => return None,
    };
    let mut moved = if up { current + step } else { current - step };
    if let Some(range) = &constraints.range {
        if let Some(min) = &range.min
            && moved < *min
        {
            moved.clone_from(min);
        }
        if let Some(max) = &range.max
            && moved > *max
        {
            moved.clone_from(max);
        }
    }
    match width {
        None => Some(Value::Int(moved)),
        Some(width) => {
            let top = (BigInt::from(1u8) << width) - 1u8;
            let moved = moved.clamp(BigInt::zero(), top);
            Some(Value::MInt {
                width,
                value: moved.to_biguint()?,
            })
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
#[path = "climb_tests.rs"]
mod tests;
