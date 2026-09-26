//! Finite execution-pattern layer.
//!
//! This crate evaluates only validated finite plans over supplied paths whose payloads are
//! KORE patterns. It deliberately contains no K parser or solver; kink-native builds its
//! paths from k-rust executions. Mutation sites and candidate selection live
//! in kink-patch.

mod pattern;

pub use pattern::{
    Atom, AttributionUnknownReason, Binding, CollectionEvidence, CollectionStop, Constructor,
    EmptySearchDecision, Evaluation, EvaluationContext, EvaluationOptions, Event, EventAttribution,
    EventOrigin, EventVocabulary, ExecutionBounds, ExecutionStop, ExecutionTerminal,
    ExecutionTerminalKind, Feasibility, MatchMode, PathInput, PathStop, PatternArm, PatternFailure,
    PatternFailureKind, PatternOutcome, PatternPlan, PayloadClause, Relation, RelationDecider,
    RelationDecision, SearchPolicy, SideCondition, SideConditionResult, SideConditionRow,
    SideConditionTable, StructuralDecider, SymbolSorts, TermRelation, Witness, evaluate,
    evaluate_with,
};
