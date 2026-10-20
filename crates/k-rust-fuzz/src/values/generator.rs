//! Generators, value trees and the seeded proptest RNG (ARCHITECTURE 3). Owner: FZ-03.
//!
//! proptest is driven through `Strategy::new_tree` and `ValueTree::simplify` without its test
//! macros and without `TestRunner::run`; every `Config` field the engine reads is set
//! explicitly, so nothing is read from `PROPTEST_*` variables or files (ARCHITECTURE 3, T-2).
//! No proptest type leaves this crate's internals.

use proptest::{
    strategy::{BoxedStrategy, ValueTree},
    test_runner::TestRunner,
};

use super::{Constraints, GenerationBounds, Value, ValueSort};

/// The proptest runner every generator draws from, seeded from the campaign seed with
/// `RngAlgorithm::ChaCha` and an explicit `Config` (ARCHITECTURE 3, 5.4).
pub(crate) struct ValueRng {
    runner: TestRunner,
}

impl ValueRng {
    /// A runner whose RNG is `TestRng::from_seed(RngAlgorithm::ChaCha, &seed)` and whose
    /// `Config` sets every field the engine reads (`max_local_rejects`, `max_global_rejects`,
    /// `max_flat_map_regens`, `max_shrink_iters`, `max_default_size_range`,
    /// `failure_persistence = None`, `rng_algorithm`, `rng_seed`, `source_file`, `test_name`,
    /// `result_cache`), with `..Config::default()` only for feature-gated fields the engine
    /// never reads. Equal seeds give equal draws whatever the environment.
    pub(crate) fn from_seed(seed: [u8; 32]) -> Self {
        unimplemented!("FZ-03")
    }
}

/// A generator of one hole's values: a proptest strategy built from its [`ValueSort`],
/// [`Constraints`] and the campaign's [`GenerationBounds`] (ARCHITECTURE 3).
pub(crate) struct Generator {
    strategy: BoxedStrategy<Value>,
}

impl Generator {
    /// The generator of `sort` under `constraints` and `bounds`. Every value it produces
    /// satisfies [`super::check_constraints`]; a choice set draws only its members.
    ///
    /// # Errors
    ///
    /// A message when the constraints admit no value of the sort (an empty range, say); the
    /// caller reports it as [`crate::CampaignError::InvalidConstraints`].
    pub(crate) fn new(
        sort: &ValueSort,
        constraints: &Constraints,
        bounds: &GenerationBounds,
    ) -> Result<Self, String> {
        unimplemented!("FZ-03")
    }

    /// Draw one value, with the value tree that shrinks it inside its sort and constraints.
    pub(crate) fn generate(&self, rng: &mut ValueRng) -> ShrinkableValue {
        unimplemented!("FZ-03")
    }
}

/// A generated value and the proptest value tree that shrinks it (ARCHITECTURE 3, 7).
///
/// The engine drives shrinking itself: [`Self::simplify`] proposes a simpler value, and after
/// the engine's confirmation rejects it, [`Self::complicate`] steps back towards the last
/// accepted one.
pub(crate) struct ShrinkableValue {
    tree: Box<dyn ValueTree<Value = Value>>,
}

impl ShrinkableValue {
    /// The tree's current value.
    pub(crate) fn current(&self) -> Value {
        unimplemented!("FZ-03")
    }

    /// Move to a simpler value; `false` when none remains.
    pub(crate) fn simplify(&mut self) -> bool {
        unimplemented!("FZ-03")
    }

    /// Undo part of the last simplification after it was rejected; `false` when none remains.
    pub(crate) fn complicate(&mut self) -> bool {
        unimplemented!("FZ-03")
    }
}
