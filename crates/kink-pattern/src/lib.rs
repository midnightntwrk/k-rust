//! Finite execution-pattern layer.
//!
//! This crate evaluates only validated finite plans over supplied paths whose payloads are
//! KORE patterns. It deliberately contains no K parser or solver; kink-native builds its
//! paths from k-rust executions and searches. Mutation sites and candidate selection live
//! in kink-patch.

mod pattern;

pub use pattern::{
    Atom, Binding, CollectionEvidence, CollectionStop, Constructor, CorpusComponent,
    CorpusDecision, CorpusSkip, EmptySearchDecision, Evaluation, EvaluationContext,
    EvaluationOptions, Event, EventOrigin, EventVocabulary, ExecutionBounds, ExecutionStop,
    ExecutionTerminal, ExecutionTerminalKind, MatchMode, OriginMode, PathInput, PathStop,
    PatternArm, PatternFailure, PatternFailureKind, PatternOutcome, PatternPlan, PayloadClause,
    Relation, SearchPolicy, SemanticSite, SideCondition, SideConditionResult, SideConditionRow,
    SideConditionTable, SymbolSorts, TermRelation, TransitionKey, Witness, aggregate_corpus,
    aggregate_existential, evaluate,
};
