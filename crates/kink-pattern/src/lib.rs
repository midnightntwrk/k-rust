//! Finite pattern and supplied-binding candidate layer.
//!
//! This crate evaluates only normalized finite plans and folds discovery
//! tuples already supplied by K. It deliberately contains no K parser,
//! discovery implementation, solver, or native-conformance claim.

mod candidate;
mod pattern;

pub use candidate::{
    Candidate, CandidateFailure, CandidateFailureKind, CandidateGeneration, DiscoveryAuthority,
    DiscoveryEvidence, DiscoveryRegistry, DiscoveryTuple, EditOriginReceipt, EditReceiptSource,
    PatchOrigin, PatchTemplateRole, ReceiptAuthority, SelectionPolicy, Site, SuppliedPatch,
    ValidatedDiscoveryRegistry, canonical_binding_digest, derive_candidate_id, derive_instance_id,
    derive_mutant_id, derive_site_id, select, validate_edit_receipts,
};
pub use pattern::{
    ArtifactRef, Atom, Binding, CollectionEvidence, CollectionStop, Constructor, Evaluation,
    EvaluationAuthority, EvaluationOptions, Event, EventOrigin, EventVocabulary, ExecutionBounds,
    ExecutionStop, ExecutionTerminal, ExecutionTerminalKind, MatchMode, NamedQuery, OriginMode,
    PathInput, PathStop, PatternArm, PatternFailure, PatternFailureKind, PatternOutcome,
    PatternPlan, PayloadClause, Relation, SearchPolicy, SemanticSiteOrigin, SideCondition,
    SideConditionResult, SideConditionRow, SideConditionTable, TermRelation, TermSignature,
    TerminalAuthority, Witness, aggregate_existential, derive_path_identity, derive_trace_digest,
    evaluate,
};
