//! The internal proposer interface (ARCHITECTURE 8, 10.1). Owner: FZ-06.
//!
//! It is shaped like LibAFL's decomposition so that the corpus proposer can move onto LibAFL at
//! M5 if the adoption criterion of ARCHITECTURE 10.1 is met: the *input* is a [`Proposal`], the
//! *observer* output is an [`Observation`], [`Feedback`] decides whether an observation is
//! interesting, a [`Score`] ranks it, and each proposer is a *stage* that proposes the next
//! input. No LibAFL type appears here.

use rand_chacha::ChaCha20Rng;

use crate::{
    exec::OutcomeClass,
    holes::ResolvedHoles,
    spec::ProposerKind,
    values::{Generator, ShrinkableValue, Value, ValueRng},
};

/// A score: compared lexicographically, smaller being better (ARCHITECTURE 6.4).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct Score(pub(crate) Vec<u64>);

/// One proposed assignment (the LibAFL *input*): a value per hole, in hole order.
pub(crate) struct Proposal {
    /// The proposer that made it.
    pub(crate) origin: ProposerKind,
    /// The values, in the order of [`ResolvedHoles::holes`].
    pub(crate) values: Vec<Value>,
    /// For blindly generated values, the value trees that shrink them; `None` per hole
    /// otherwise.
    pub(crate) trees: Vec<Option<ShrinkableValue>>,
}

/// What the engine observed of one case (the LibAFL *observer* output; ARCHITECTURE 6.1).
#[derive(Clone, Debug)]
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

/// Decides whether an observation is interesting (the LibAFL *feedback*): new coverage or a
/// better score (ARCHITECTURE 6.2). Only `miss` cases are scored (R-18).
pub(crate) trait Feedback {
    /// Whether `observation` adds coverage or improves the best score; updates the feedback's
    /// state.
    fn is_interesting(&mut self, observation: &Observation) -> bool;
}

/// What a proposer may read and draw from when proposing.
pub(crate) struct ProposalContext<'a> {
    /// The campaign's holes.
    pub(crate) holes: &'a ResolvedHoles,
    /// One generator per hole, in hole order.
    pub(crate) generators: &'a [Generator],
    /// The proptest runner values are drawn from.
    pub(crate) values: &'a mut ValueRng,
    /// The schedule's RNG for every other choice, seeded from the campaign seed.
    pub(crate) rng: &'a mut ChaCha20Rng,
}

/// A proposer (a LibAFL *stage*): proposes assignments and learns from their observations
/// (ARCHITECTURE 8). Every choice it makes derives from the context's seeded RNGs.
pub(crate) trait Proposer {
    /// Which proposer this is.
    fn kind(&self) -> ProposerKind;

    /// The next assignment, or `None` when this proposer has nothing left to propose (the
    /// explicit proposer after its list).
    fn propose(&mut self, context: &mut ProposalContext<'_>) -> Option<Proposal>;

    /// Learn from the observation of a case this proposer proposed; `interesting` is the
    /// feedback's verdict.
    fn observe(&mut self, proposal: &Proposal, observation: &Observation, interesting: bool);
}
