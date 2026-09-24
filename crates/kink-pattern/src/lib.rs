//! Finite execution-pattern layer.
//!
//! This crate evaluates only normalized finite plans over supplied paths. It
//! deliberately contains no K parser, solver, or native-conformance claim.
//! Mutation sites and candidate selection live in kink-patch.

mod pattern;

pub use pattern::{
    ArtifactRef, Atom, Binding, CollectionEvidence, CollectionStop, Constructor, CorpusComponent,
    CorpusDecision, CorpusSkip, Evaluation, EvaluationAuthority, EvaluationOptions, Event,
    EventOrigin, EventVocabulary, ExecutionBounds, ExecutionStop, ExecutionTerminal,
    ExecutionTerminalKind, MatchMode, NamedQuery, OriginMode, PathInput, PathStop, PatternArm,
    PatternFailure, PatternFailureKind, PatternOutcome, PatternPlan, PayloadClause, Relation,
    SearchPolicy, SemanticSiteOrigin, SideCondition, SideConditionResult, SideConditionRow,
    SideConditionTable, TermRelation, TermSignature, TerminalAuthority, Witness, aggregate_corpus,
    aggregate_existential, derive_path_identity, derive_trace_digest, evaluate,
};
