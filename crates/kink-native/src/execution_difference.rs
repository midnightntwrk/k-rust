//! A pattern-slot kill requires a proved difference in the state sequences of the two runs, unless a state slot distinguishes on the same test. An unproved pattern disagreement becomes Unknown.
//!
//! Each sequence records the before state of every committed Rewrite transition and the leaf state. Remainder entries add no position; rule identities, effects, and halt depth are not difference evidence.

use k_rust::kore::ast::Pattern;

use crate::{execution::HaltClass, feasibility::LeafFeasibility};

/// One path's states; its rewrite length is `states.len() - 1`, never its halt depth.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StateSequence {
    /// The leaf's halt class.
    pub halt: HaltClass,
    /// Rewrite before states in order, followed by the leaf state.
    pub states: Vec<Pattern>,
    /// Whether the leaf has a proved instance.
    pub feasibility: LeafFeasibility,
}

/// State sequences of all leaves, in backend leaf order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StateSequences {
    /// One sequence for each path-set leaf.
    pub leaves: Vec<StateSequence>,
}

/// The side supplying a difference witness.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CertifiedSide {
    /// The baseline definition.
    Baseline,
    /// The mutant-side definition that ran.
    Mutant,
}

/// A reason a covering path cannot equal the witness path.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Exclusion {
    /// The covering leaf has no feasible instance.
    Vacuous,
    /// Complete path lengths rule out equality.
    Length,
    /// Generalized states have a proved constructor clash.
    Clash,
    /// Stable-variable path conditions are provably disjoint.
    Disjoint,
}

/// Why a difference was not proved; none of these reasons permits a kill.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NotProvedReason {
    /// The two definitions' signature projections differ.
    SignatureDiffers,
    /// Neither side has a covering set of leaves.
    NotCovering,
    /// No feasible path excludes every path on the other side.
    NoWitness,
    /// A state could not be internalized for proof.
    Internalization,
    /// A transition was unexpected or a committed rewrite was not reported.
    Unobservable,
    /// The sequence run's branch identities differ from the primary run.
    BranchMismatch,
    /// The sequence run's watchdog fired.
    Timeout,
    /// The backend failed, returned an inadmissible halt, or could not decode a state.
    Backend,
}

/// A proved difference or the reason the proof failed closed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DifferenceCertificate {
    /// This feasible leaf differs from every leaf on the other side.
    Proved {
        /// The side supplying the witness.
        witness_side: CertifiedSide,
        /// The witness index in leaf order.
        witness_leaf: usize,
        /// One exclusion for each leaf of the covering side, in leaf order.
        exclusions: Vec<Exclusion>,
    },
    /// No execution difference was proved.
    NotProved(NotProvedReason),
}
