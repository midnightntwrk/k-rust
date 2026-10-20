//! The deterministic proposer schedule (ARCHITECTURE 8). Owner: FZ-06.
//!
//! The explicit proposals (the anchors, then the author's assignments) come first, in order,
//! each exactly once (ARCHITECTURE 8.1). After them, each case's proposer is drawn from the
//! scheduled proposers with probability proportional to its weight, by one draw from a `ChaCha20`
//! generator seeded from the campaign seed. A proposer that has nothing left to propose leaves
//! the schedule; when every proposer has left, the schedule is exhausted.

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

/// One scheduled proposer and its weight.
struct Slot {
    weight: u32,
    proposer: Box<dyn Proposer>,
    exhausted: bool,
}

/// The schedule of one campaign run.
pub(crate) struct Schedule {
    explicit: VecDeque<Vec<Value>>,
    slots: Vec<Slot>,
    rng: ChaCha20Rng,
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
                })
                .collect(),
            rng: ChaCha20Rng::from_seed(derive_seed(seed, "schedule")),
        }
    }

    /// The next proposal, or `None` when the explicit proposals are spent and every scheduled
    /// proposer is exhausted.
    pub(crate) fn next(&mut self) -> Option<Proposal> {
        if let Some(values) = self.explicit.pop_front() {
            return Some(Proposal::plain(Origin::Explicit, values));
        }
        loop {
            let total: u64 = self
                .slots
                .iter()
                .filter(|slot| !slot.exhausted)
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
                    if slot.exhausted {
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
                .expect("the draw is below the total weight of the live slots");
            let slot = &mut self.slots[index];
            let mut context = ProposalContext { rng: &mut self.rng };
            match slot.proposer.propose(&mut context) {
                Some(proposal) => return Some(proposal),
                None => slot.exhausted = true,
            }
        }
    }

    /// Pass a case's observation to the proposer that proposed it.
    pub(crate) fn observe(
        &mut self,
        proposal: &Proposal,
        observation: &Observation,
        interesting: bool,
    ) {
        if let Origin::Scheduled(kind) = proposal.origin
            && let Some(slot) = self
                .slots
                .iter_mut()
                .find(|slot| slot.proposer.kind() == kind)
        {
            slot.proposer.observe(proposal, observation, interesting);
        }
    }
}
