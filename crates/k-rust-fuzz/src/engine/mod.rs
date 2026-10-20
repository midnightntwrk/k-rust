//! The engine: campaign validation, the loop over cases, the proposer schedule, the budget,
//! confirmation, shrinking and the report (ARCHITECTURE 1, 7, 8, 9.2, 9.3). Owner: FZ-06.

pub(crate) mod proposer;

use k_rust::backend::CancellationToken;

use crate::{
    error::CampaignError,
    exec::CaseResult,
    report::FuzzReport,
    spec::{Assignment, Budget, CampaignSpec},
    target::Judgement,
};

/// A validated campaign (ARCHITECTURE 9.2).
///
/// [`Campaign::new`] resolves the holes, the target and the definitions once; [`Campaign::run`]
/// runs cases on the calling thread until the budget is spent, a witness is confirmed, the
/// rejection cap is reached or the caller cancels.
pub struct Campaign {
    spec: CampaignSpec,
}

impl Campaign {
    /// Validate `spec` (ARCHITECTURE 9.2): build each definition's backend on its route and its
    /// program assembly, resolve the holes ([`crate::holes`]) and their generators
    /// ([`crate::values`]), resolve the target ([`crate::target`]), check the explicit
    /// assignments against the holes' constraints, refuse a proposer this build or milestone
    /// does not provide, and assemble and run-check the program with its anchor values.
    ///
    /// # Errors
    ///
    /// [`CampaignError`] for every refusal ARCHITECTURE 9.2 lists: a hole whose `find` or
    /// `literal` does not occur exactly once, overlapping spans, an anchor that does not parse
    /// back, a refused hole sort, explicit assignments that violate their constraints, an
    /// unknown, ambiguous or refused target, a hole sort missing on one side of a differential,
    /// and a program that does not assemble or is refused with its anchor values.
    pub fn new(spec: CampaignSpec) -> Result<Campaign, CampaignError> {
        unimplemented!("FZ-06")
    }

    /// The specification this campaign was built from.
    #[must_use]
    pub fn spec(&self) -> &CampaignSpec {
        &self.spec
    }

    /// Run cases until `budget` is spent, a witness is confirmed and shrunk, the rejection cap
    /// is reached, or `cancel` is cancelled (ARCHITECTURE 9.2).
    ///
    /// Every case runs on the calling thread. `Budget::Work` charges every execution:
    /// confirmation, shrinking and both sides of a differential case included. The proposers
    /// are mixed by a deterministic schedule seeded from the campaign seed; the explicit
    /// proposer tries the anchors first (ARCHITECTURE 8.1). A candidate hit becomes a witness
    /// only after [`confirm`] agrees; a disagreement is an engine defect (ARCHITECTURE 7). The
    /// report is a function of the specification, the budget, the k-rust revision and
    /// [`crate::ENGINE_VERSION`], outside the determinism exclusions it counts
    /// (ARCHITECTURE 5.4).
    pub fn run(&mut self, budget: Budget, cancel: Option<CancellationToken>) -> FuzzReport {
        unimplemented!("FZ-06")
    }
}

/// A confirmation's verdict on a candidate (ARCHITECTURE 7).
pub(crate) struct Confirmation {
    /// The confirmation's own execution result (both sides' mutant result for a differential).
    pub(crate) result: CaseResult,
    /// The confirmation's judgement.
    pub(crate) judgement: Judgement,
    /// The confirmation agrees with the case: it is a hit too, with an equal reaching leaf.
    pub(crate) agrees: bool,
    /// The work the confirmation spent, charged to the budget.
    pub(crate) work: u64,
}

/// Confirm `candidate` independently of the path that found it (ARCHITECTURE 7, R-4):
/// instantiate the overlay on the original program text, assemble with a fresh
/// [`crate::assemble::ProgramAssembly`], run on a fresh backend through the public
/// `Backend::execute` with the campaign's options, re-resolve the target for that backend,
/// reclassify and check the target again; for a differential target, re-run both sides.
///
/// # Errors
///
/// A message when the fresh backend or assembly cannot be built, or the run aborts; the engine
/// reports it as an engine defect, never as a hit.
pub(crate) fn confirm(spec: &CampaignSpec, candidate: &Assignment) -> Result<Confirmation, String> {
    unimplemented!("FZ-06")
}

/// Shrink a confirmed witness (ARCHITECTURE 7): propose smaller assignments (proptest value
/// trees for blindly generated values; integer and collection-length moves for others), confirm
/// each with `confirm_candidate`, and keep a candidate only if it still hits. Returns the
/// smallest confirmed assignment, or `None` when nothing smaller hits. `confirm_candidate`
/// charges its work to the budget and returns `None` when the budget is spent.
pub(crate) fn shrink(
    witness: &Assignment,
    confirm_candidate: &mut dyn FnMut(&Assignment) -> Option<bool>,
) -> Option<Assignment> {
    unimplemented!("FZ-06")
}
