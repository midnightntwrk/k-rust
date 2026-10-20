//! The internal proposer interface and the M1 proposers (ARCHITECTURE 8, 10.1). Owner: FZ-06.
//!
//! It is shaped like `LibAFL`'s decomposition so that the corpus proposer can move onto `LibAFL` at
//! M5 if the adoption criterion of ARCHITECTURE 10.1 is met: the *input* is a [`Proposal`], the
//! *observer* output is an [`Observation`], [`Feedback`] decides whether an observation is
//! interesting, a [`Score`] ranks it, and each proposer is a *stage* that proposes the next
//! input. No `LibAFL` type appears here.
//!
//! M1 has two proposers: the explicit one (anchors, then the author's assignments), which the
//! schedule runs first and which is not weighted ([`super::schedule::Schedule`]), and
//! [`BlindProposer`], proptest generation from each hole's generator (ARCHITECTURE 8.1, 8.2).

use std::collections::BTreeSet;

use rand_chacha::ChaCha20Rng;

use crate::{
    exec::OutcomeClass,
    spec::ProposerKind,
    values::{Generator, ShrinkableValue, Value, ValueRng},
};

/// A score: compared lexicographically, smaller being better (ARCHITECTURE 6.4).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct Score(pub(crate) Vec<u64>);

/// Which proposer made a proposal.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum Origin {
    /// The explicit proposer: the anchors or an author's assignment (ARCHITECTURE 8.1).
    Explicit,
    /// A scheduled proposer.
    Scheduled(ProposerKind),
}

/// A value tree the shrinker drives (ARCHITECTURE 7): proptest's value tree for a blindly
/// generated value. A trait, so that the engine's shrinking is tested without proptest.
pub(crate) trait ValueShrinker {
    /// The tree's current value.
    fn current(&self) -> Value;
    /// Move to a simpler value; `false` when none remains.
    fn simplify(&mut self) -> bool;
    /// Undo part of the last simplification after it was rejected; `false` when none remains.
    fn complicate(&mut self) -> bool;
}

impl ValueShrinker for ShrinkableValue {
    fn current(&self) -> Value {
        ShrinkableValue::current(self)
    }

    fn simplify(&mut self) -> bool {
        ShrinkableValue::simplify(self)
    }

    fn complicate(&mut self) -> bool {
        ShrinkableValue::complicate(self)
    }
}

/// One proposed assignment (the `LibAFL` *input*): a value per hole, in hole order.
pub(crate) struct Proposal {
    /// The proposer that made it.
    pub(crate) origin: Origin,
    /// The values, in the order of the campaign's holes.
    pub(crate) values: Vec<Value>,
    /// For blindly generated values, the value trees that shrink them; `None` per hole
    /// otherwise.
    pub(crate) trees: Vec<Option<Box<dyn ValueShrinker>>>,
    /// Why no complete assignment was drawn: a hole's generator failed
    /// (`Generator::try_generate`). `values` then holds the values drawn before that hole, and
    /// the engine counts the proposal as a `rejected` case (`generation`) without running it.
    pub(crate) failure: Option<String>,
}

impl Proposal {
    /// A proposal without value trees.
    pub(crate) fn plain(origin: Origin, values: Vec<Value>) -> Self {
        let trees = values.iter().map(|_| None).collect();
        Self {
            origin,
            values,
            trees,
            failure: None,
        }
    }
}

/// What the engine observed of one case (the `LibAFL` *observer* output; ARCHITECTURE 6.1).
///
/// The M1 feedback reads the class and the coverage; the case number, the work and the score
/// are for the corpus and climb proposers (ARCHITECTURE 6.4, 8.4, 8.5).
#[derive(Clone, Debug)]
#[expect(
    dead_code,
    reason = "`case`, `work` and `score` are read by the guidance proposers, which M1 does not \
              provide"
)]
pub(crate) struct Observation {
    /// The case number.
    pub(crate) case: u64,
    /// The case's class.
    pub(crate) class: OutcomeClass,
    /// Rule ids in coverage `applied`.
    pub(crate) applied: Vec<String>,
    /// Rule ids in coverage `matched`.
    pub(crate) matched: Vec<String>,
    /// The case's work.
    pub(crate) work: u64,
    /// The case's score, when the target kind scores (M4).
    pub(crate) score: Option<Score>,
}

/// Decides whether an observation is interesting (the `LibAFL` *feedback*): new coverage or a
/// better score (ARCHITECTURE 6.2). Only `miss` cases are scored (R-18).
pub(crate) trait Feedback {
    /// Whether `observation` adds coverage or improves the best score; updates the feedback's
    /// state.
    fn is_interesting(&mut self, observation: &Observation) -> bool;
}

/// The M1 feedback: a `miss` case is interesting when it reaches a rule, in `applied` or
/// `matched`, that no earlier `miss` case reached (ARCHITECTURE 6.2, R-18). No M1 proposer
/// learns from it; the corpus proposer will (M5).
#[derive(Debug, Default)]
pub(crate) struct CoverageFeedback {
    applied: BTreeSet<String>,
    matched: BTreeSet<String>,
}

impl Feedback for CoverageFeedback {
    fn is_interesting(&mut self, observation: &Observation) -> bool {
        if observation.class != OutcomeClass::Miss {
            return false;
        }
        let mut new = false;
        for rule in &observation.applied {
            new |= self.applied.insert(rule.clone());
        }
        for rule in &observation.matched {
            new |= self.matched.insert(rule.clone());
        }
        new
    }
}

/// What a proposer may draw from when proposing.
#[expect(
    dead_code,
    reason = "the guidance proposers draw their non-value choices from `rng`; blind sampling \
              makes none"
)]
pub(crate) struct ProposalContext<'a> {
    /// The schedule's RNG for every choice that is not a value draw, seeded from the campaign
    /// seed.
    pub(crate) rng: &'a mut ChaCha20Rng,
}

/// A proposer (a `LibAFL` *stage*): proposes assignments and learns from their observations
/// (ARCHITECTURE 8). Every choice it makes derives from the campaign seed.
pub(crate) trait Proposer {
    /// Which proposer this is.
    fn kind(&self) -> ProposerKind;

    /// The next assignment, or `None` when this proposer has nothing left to propose.
    fn propose(&mut self, context: &mut ProposalContext<'_>) -> Option<Proposal>;

    /// Learn from the observation of a case this proposer proposed; `interesting` is the
    /// feedback's verdict.
    fn observe(&mut self, proposal: &Proposal, observation: &Observation, interesting: bool);
}

/// Blind sampling (ARCHITECTURE 8.2): one draw from every hole's generator, in hole order, from
/// a proptest runner seeded from the campaign seed. It never runs out and ignores feedback. A
/// draw a generator fails ([`Generator::try_generate`]) ends the proposal there, with the
/// generator's message as its [`Proposal::failure`]: a `rejected` case, never a crash.
pub(crate) struct BlindProposer {
    generators: Vec<Generator>,
    values: ValueRng,
}

impl BlindProposer {
    /// A blind proposer over one generator per hole, in hole order.
    pub(crate) fn new(generators: Vec<Generator>, values: ValueRng) -> Self {
        Self { generators, values }
    }
}

impl Proposer for BlindProposer {
    fn kind(&self) -> ProposerKind {
        ProposerKind::Blind
    }

    fn propose(&mut self, _context: &mut ProposalContext<'_>) -> Option<Proposal> {
        let mut values = Vec::with_capacity(self.generators.len());
        let mut trees: Vec<Option<Box<dyn ValueShrinker>>> =
            Vec::with_capacity(self.generators.len());
        let mut failure = None;
        for (hole, generator) in self.generators.iter().enumerate() {
            match generator.try_generate(&mut self.values) {
                Ok(tree) => {
                    values.push(tree.current());
                    trees.push(Some(Box::new(tree)));
                }
                Err(message) => {
                    failure = Some(format!("hole {hole}: {message}"));
                    break;
                }
            }
        }
        Some(Proposal {
            origin: Origin::Scheduled(ProposerKind::Blind),
            values,
            trees,
            failure,
        })
    }

    fn observe(&mut self, _proposal: &Proposal, _observation: &Observation, _interesting: bool) {}
}
