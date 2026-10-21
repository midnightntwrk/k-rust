//! Branch-local execution states retained by the execution adapter.

use k_rust::backend::{TraceEntry, TransitionIdOutput};
use serde_json::Value;

/// One branch-local adapted execution state.
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedBranch {
    pub identity: Vec<TransitionIdOutput>,
    pub state: Value,
    pub depth: u64,
    pub trace: Vec<TraceEntry>,
}

/// Observation-erased state. The semantic state, branch identity, depth, and trace remain.
#[derive(Clone, Debug, PartialEq)]
pub struct ErasedBranch {
    pub identity: Vec<TransitionIdOutput>,
    pub state: Value,
    pub depth: u64,
    pub trace: Vec<TraceEntry>,
}

impl AdaptedBranch {
    /// Retains the execution state in the observation-erased representation.
    #[must_use]
    pub fn erase_observations(&self) -> ErasedBranch {
        ErasedBranch {
            identity: self.identity.clone(),
            state: self.state.clone(),
            depth: self.depth,
            trace: self.trace.clone(),
        }
    }
}
