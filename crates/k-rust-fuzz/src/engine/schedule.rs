//! The deterministic proposer schedule (ARCHITECTURE 8). Owner: FZ-06.
//!
//! The explicit proposals (the anchors, then the author's assignments) come first, in order,
//! each exactly once (ARCHITECTURE 8.1). After them, each case's proposer is drawn from the
//! scheduled proposers with probability proportional to its weight, by one draw from a `ChaCha20`
//! generator seeded from the campaign seed. A proposer that has nothing left to propose leaves
//! the schedule; when every proposer has left, the schedule is exhausted.
//!
//! Only the proposers that may propose now take part in a draw: a proposer that is not ready
//! ([`Proposer::ready`]) and one whose budget share is spent ([`Proposer::budget_share`]) wait
//! for a later case. The case share is kept over every prefix of the campaign: the proposer is
//! drawn only while its cases, counting the one it would add, are at most the share of all
//! cases so far counting that one. The work share is checked before each case it would add
//! (its work at most the share of all work so far): a case's work is known only after it runs,
//! so the proposer's work can exceed the share by the work of its last case, and no more. Since a draw that
//! no slot limits draws exactly as before, a schedule without such a proposer is unchanged.
//!
//! The proposers that declare a share are the guided ones (the climb, the corpus), which work
//! from cases others make. Together they are held to [`GUIDED_SHARE`] by the same rule, counting
//! all their cases and work as one: a guided proposer is drawn only while the guided cases,
//! counting the one it would add, are at most that share of all cases, and the guided work so
//! far is at most that share of all work. So the unguided proposers (blind sampling, the
//! dictionary) keep at least half of the cases over every prefix, however the weights are set.
//! With one guided proposer whose own share is [`GUIDED_SHARE`] the joint bound is its own, so a
//! campaign with only the climb (or only the corpus) draws exactly as without the joint bound.

use std::collections::VecDeque;

use rand::{Rng as _, SeedableRng as _};
use rand_chacha::ChaCha20Rng;
use sha2::{Digest as _, Sha256};

use super::proposer::{Observation, Origin, Proposal, ProposalContext, Proposer};
use crate::values::Value;

/// A 32-byte seed for one purpose, derived from the campaign seed: SHA-256 of a purpose label
/// and the seed's little-endian bytes. Distinct purposes (the schedule, value generation) draw
/// from independent streams, so adding draws to one never shifts the other.
pub(crate) fn derive_seed(seed: u64, purpose: &str) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"krust-fuzz/");
    hasher.update(purpose.as_bytes());
    hasher.update([0]);
    hasher.update(seed.to_le_bytes());
    hasher.finalize().into()
}

/// The most share of the campaign's cases and work that the guided proposers (those with a
/// [`Proposer::budget_share`]) spend together, as (numerator, denominator) (module
/// documentation).
pub(crate) const GUIDED_SHARE: (u32, u32) = (1, 2);

/// Whether `cases` cases (counting the one to add, so `cases + 1`) and `work` of a proposer or
/// group stay within `share` of the campaign's `total_cases` (counting the one to add) and
/// `total_work`.
fn within(
    (numerator, denominator): (u32, u32),
    cases: u64,
    work: u64,
    total_cases: u64,
    total_work: u64,
) -> bool {
    let (numerator, denominator) = (u128::from(numerator), u128::from(denominator));
    (u128::from(cases) + 1) * denominator <= (u128::from(total_cases) + 1) * numerator
        && u128::from(work) * denominator <= u128::from(total_work) * numerator
}

/// One scheduled proposer and its weight.
struct Slot {
    weight: u32,
    proposer: Box<dyn Proposer>,
    exhausted: bool,
    /// The cases this proposer proposed and their work, as observed.
    cases: u64,
    work: u64,
}

impl Slot {
    /// Whether the slot may be drawn for the next case, given the campaign's observed `cases`
    /// and `work`.
    /// `guided` is the guided proposers' cases and work together.
    fn eligible(&self, cases: u64, work: u64, guided: (u64, u64)) -> bool {
        !self.exhausted
            && self.proposer.ready()
            && self.proposer.budget_share().is_none_or(|share| {
                within(share, self.cases, self.work, cases, work)
                    && within(GUIDED_SHARE, guided.0, guided.1, cases, work)
            })
    }
}

/// The schedule of one campaign run.
pub(crate) struct Schedule {
    explicit: VecDeque<Vec<Value>>,
    slots: Vec<Slot>,
    rng: ChaCha20Rng,
    /// Every observed case and its work, explicit proposals included.
    cases: u64,
    work: u64,
}

impl Schedule {
    /// A schedule that proposes `explicit` first, in order, then draws among `proposers` by
    /// weight with an RNG seeded from `seed`. Proposers of weight 0 never run. The order of
    /// `proposers` is part of the schedule; the engine passes them in [`crate::spec::ProposerKind`]
    /// order.
    pub(crate) fn new(
        seed: u64,
        explicit: Vec<Vec<Value>>,
        proposers: Vec<(u32, Box<dyn Proposer>)>,
    ) -> Self {
        Self {
            explicit: explicit.into(),
            slots: proposers
                .into_iter()
                .filter(|(weight, _)| *weight > 0)
                .map(|(weight, proposer)| Slot {
                    weight,
                    proposer,
                    exhausted: false,
                    cases: 0,
                    work: 0,
                })
                .collect(),
            rng: ChaCha20Rng::from_seed(derive_seed(seed, "schedule")),
            cases: 0,
            work: 0,
        }
    }

    /// The next proposal, or `None` when the explicit proposals are spent and no scheduled
    /// proposer may propose: every one is exhausted, or the others wait (not ready, or their
    /// share spent).
    pub(crate) fn next(&mut self) -> Option<Proposal> {
        if let Some(values) = self.explicit.pop_front() {
            return Some(Proposal::plain(Origin::Explicit, values));
        }
        let (cases, work) = (self.cases, self.work);
        let guided = self
            .slots
            .iter()
            .filter(|slot| slot.proposer.budget_share().is_some())
            .fold((0u64, 0u64), |(cases, work), slot| {
                (cases + slot.cases, work.saturating_add(slot.work))
            });
        loop {
            let total: u64 = self
                .slots
                .iter()
                .filter(|slot| slot.eligible(cases, work, guided))
                .map(|slot| u64::from(slot.weight))
                .sum();
            if total == 0 {
                return None;
            }
            let mut draw = self.rng.random_range(0..total);
            let index = self
                .slots
                .iter()
                .position(|slot| {
                    if !slot.eligible(cases, work, guided) {
                        return false;
                    }
                    let weight = u64::from(slot.weight);
                    if draw < weight {
                        true
                    } else {
                        draw -= weight;
                        false
                    }
                })
                .expect("the draw is below the total weight of the eligible slots");
            let slot = &mut self.slots[index];
            let mut context = ProposalContext { rng: &mut self.rng };
            match slot.proposer.propose(&mut context) {
                Some(proposal) => return Some(proposal),
                None => slot.exhausted = true,
            }
        }
    }

    /// Pass a case's observation to the proposer that proposed it, then to every proposer
    /// ([`Proposer::observe_all`]), and count the case and its work.
    pub(crate) fn observe(
        &mut self,
        proposal: &Proposal,
        observation: &Observation,
        interesting: bool,
    ) {
        self.cases += 1;
        // As the budget charges them: every case at least 1 (`Budget::Work`).
        let work = observation.work.max(1);
        self.work = self.work.saturating_add(work);
        if let Origin::Scheduled(kind) = proposal.origin
            && let Some(slot) = self
                .slots
                .iter_mut()
                .find(|slot| slot.proposer.kind() == kind)
        {
            slot.cases += 1;
            slot.work = slot.work.saturating_add(work);
            slot.proposer.observe(proposal, observation, interesting);
        }
        for slot in &mut self.slots {
            slot.proposer.observe_all(proposal, observation);
        }
    }
}
