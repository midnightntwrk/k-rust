//! Versioned JSON wire contracts for persistent search and observation.

use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::{
    BackendError, ExecutionLeaf, ExecutionResult, TraceEntry, encode_pattern, halt_reason,
    trace_entry,
};
use k_rust_backend::{
    builtin::{BuiltinEffect, BuiltinError},
    externalize,
    rewrite::IndeterminateReason,
    search::{
        IncompleteSearch, PathSearchResult as BackendPathSearchResult, PathWitness,
        PatternPathSearchResult as BackendPatternPathSearchResult,
        PatternSearchResult as BackendPatternSearchResult, SearchResult as BackendSearchResult,
        SearchState,
    },
    simplify::{DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationError},
    smt::{Satisfiability, SmtError, TranslationError},
    substitution::Substitution,
    term::{Sort, Term},
    transition::{
        ObservationEvent, TransitionClass, TransitionId, TransitionObservation,
        UncommittedObservation, UncommittedReason,
    },
};

pub const BACKEND_SCHEMA_VERSION: u32 = 1;

fn validate_schema_version(schema_version: u32) -> Result<(), BackendError> {
    if schema_version == BACKEND_SCHEMA_VERSION {
        Ok(())
    } else {
        Err(BackendError(format!(
            "unsupported backend schema version {schema_version}; supported version 1"
        )))
    }
}

#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum SearchTypeArg {
    #[default]
    Final,
    All,
    OneStep,
    OneOrMoreSteps,
}

#[derive(Clone, Debug, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields, rename_all = "camelCase")]
pub struct SearchRequest {
    pub state: Value,
    pub module_name: Option<String>,
    pub search_type: SearchTypeArg,
    pub max_depth: Option<u64>,
    pub max_breadth: Option<usize>,
    pub max_results: Option<usize>,
    pub max_simplification_iterations: usize,
    pub schema_version: u32,
}

impl SearchRequest {
    pub fn validate_schema(&self) -> Result<(), BackendError> {
        validate_schema_version(self.schema_version)
    }
}

impl Default for SearchRequest {
    fn default() -> Self {
        Self {
            state: Value::Null,
            module_name: None,
            search_type: SearchTypeArg::Final,
            max_depth: None,
            max_breadth: None,
            max_results: None,
            max_simplification_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            schema_version: BACKEND_SCHEMA_VERSION,
        }
    }
}

#[derive(Clone, Debug, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields, rename_all = "camelCase")]
pub struct SearchPatternRequest {
    pub state: Value,
    pub pattern: Value,
    pub module_name: Option<String>,
    pub search_type: SearchTypeArg,
    pub max_depth: Option<u64>,
    pub max_breadth: Option<usize>,
    pub max_results: Option<usize>,
    pub max_simplification_iterations: usize,
    pub schema_version: u32,
}

impl SearchPatternRequest {
    pub fn validate_schema(&self) -> Result<(), BackendError> {
        validate_schema_version(self.schema_version)
    }
}

impl Default for SearchPatternRequest {
    fn default() -> Self {
        let search = SearchRequest::default();
        Self {
            state: search.state,
            pattern: Value::Null,
            module_name: search.module_name,
            search_type: search.search_type,
            max_depth: search.max_depth,
            max_breadth: search.max_breadth,
            max_results: search.max_results,
            max_simplification_iterations: search.max_simplification_iterations,
            schema_version: search.schema_version,
        }
    }
}

/// An opt-in observed operation and its atomic rule filter.
#[derive(Clone, Debug, Deserialize, PartialEq)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct ObservedRequest<T> {
    pub request: T,
    #[serde(default)]
    pub rules: Option<Vec<String>>,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ResultModalityOutput {
    StateSet,
    PathSet,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct TransitionIdOutput {
    pub rule: String,
    pub target: String,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct SearchStateOutput {
    pub state: Value,
    pub depth: u64,
    pub trace: Vec<TraceEntry>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub branch: Vec<TransitionIdOutput>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub observations: Vec<ObservationEventOutput>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct PathWitnessOutput {
    pub id: Vec<TransitionIdOutput>,
    pub state: Value,
    pub depth: u64,
    pub trace: Vec<TraceEntry>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub observations: Vec<ObservationEventOutput>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct BindingOutput {
    pub variable: Value,
    pub value: Value,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct TermPairOutput {
    pub left: Value,
    pub right: Value,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "kebab-case")]
pub enum EffectOutput {
    UserLog { message: String },
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "kebab-case")]
pub enum BuiltinFailureOutput {
    Interrupted,
    WrongArity {
        hook: String,
        expected: usize,
        actual: usize,
    },
    UnexpectedSort {
        hook: String,
        expected: String,
        actual: String,
    },
    AlternativeSortsDiffer {
        then_sort: String,
        else_sort: String,
    },
    IncompatibleMapSorts {
        left: String,
        right: String,
    },
    InvalidFloatToken {
        hook: String,
        token: String,
    },
    UnsupportedFloatFormat {
        hook: String,
        precision: u32,
        exponent_bits: u32,
    },
    UnsupportedFloatFormatParameters {
        hook: String,
        precision: String,
        exponent_bits: String,
    },
    MismatchedFloatFormats {
        hook: String,
        left_precision: u32,
        left_exponent_bits: u32,
        right_precision: u32,
        right_exponent_bits: u32,
    },
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "kebab-case")]
pub enum TranslationFailureOutput {
    NonBooleanAnd {
        term: Value,
    },
    PlaceholderOutOfBounds {
        placeholder: usize,
        arguments: usize,
    },
    UnsupportedPredicate {
        predicate: String,
    },
    ParametricSort {
        sort: String,
    },
    SmtLemmaSurplusMappings {
        rule: String,
        terms: Vec<Value>,
    },
    SmtLemmaSurplusPredicates {
        rule: String,
        predicates: Vec<Value>,
    },
    MissingSmtLemmaVariable {
        rule: String,
        variable: Value,
    },
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "kebab-case")]
pub enum SmtFailureOutput {
    Translation { error: TranslationFailureOutput },
    Unavailable,
    InconsistentPrelude,
    UnknownPrelude { reason: String },
    Unknown { reason: String },
    InconsistentGroundTruth,
    MissingModel,
    MissingModelValue { variable: Value },
    InvalidModelValue { variable: Value, value: String },
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "kebab-case")]
pub enum SatisfiabilityOutput {
    Sat,
    Unsat,
    Unknown { reason: String },
    Error { error: SmtFailureOutput },
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "kebab-case")]
pub enum SearchFailureOutput {
    Cancelled,
    Builtin {
        error: BuiltinFailureOutput,
    },
    ConflictingResults {
        rules: Vec<String>,
    },
    Smt {
        #[serde(skip_serializing_if = "Option::is_none")]
        rule: Option<String>,
        error: SmtFailureOutput,
    },
    SmtPredicate {
        predicate: Value,
        error: SmtFailureOutput,
    },
    InconsistentGroundTruth {
        #[serde(skip_serializing_if = "Option::is_none")]
        rule: Option<String>,
    },
    IterationLimit {
        limit: usize,
        term: Option<Value>,
    },
    PredicateIterationLimit {
        limit: usize,
        predicate: Option<Value>,
    },
    InvalidBuiltinResultSymbol {
        hook: String,
        symbol: String,
    },
    Match {
        rule: String,
        bindings: Vec<BindingOutput>,
        remainder: Vec<TermPairOutput>,
    },
    Requires {
        rule: String,
        predicates: Vec<Value>,
    },
    Concreteness {
        rule: String,
        variable: Value,
    },
    Remainder {
        rules: Vec<String>,
        predicates: Vec<Value>,
        satisfiability: SatisfiabilityOutput,
    },
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "kebab-case")]
pub enum IncompleteSearchOutput {
    ResultBound,
    DepthBound {
        state: SearchStateOutput,
    },
    BreadthBound {
        states: Vec<SearchStateOutput>,
    },
    Indeterminate {
        state: SearchStateOutput,
        reason: SearchFailureOutput,
    },
    Cancelled {
        state: SearchStateOutput,
    },
    Simplification {
        state: SearchStateOutput,
        error: SearchFailureOutput,
    },
    Match {
        state: SearchStateOutput,
        bindings: Vec<BindingOutput>,
        remainder: Vec<TermPairOutput>,
    },
    Smt {
        state: SearchStateOutput,
        error: SmtFailureOutput,
    },
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum TransitionClassOutput {
    Rewrite,
    Remainder,
    FunctionEquation,
    Simplification,
    Builtin,
    Claim,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum UncommittedReasonOutput {
    RolledBack,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "kebab-case")]
pub enum ObservationEventOutput {
    Transition {
        id: TransitionIdOutput,
        class: TransitionClassOutput,
        #[serde(skip_serializing_if = "Option::is_none")]
        rule_label: Option<String>,
        bindings: Vec<BindingOutput>,
        introduced_predicates: Vec<Value>,
        before: Value,
        after: Value,
        effects: Vec<EffectOutput>,
    },
    Uncommitted {
        id: TransitionIdOutput,
        #[serde(skip_serializing_if = "Option::is_none")]
        rule_label: Option<String>,
        effects: Vec<EffectOutput>,
        reason: UncommittedReasonOutput,
    },
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct SearchResponse {
    pub schema_version: u32,
    pub modality: ResultModalityOutput,
    pub states: Vec<SearchStateOutput>,
    pub effects: Vec<EffectOutput>,
    pub incomplete: Vec<IncompleteSearchOutput>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct PathSearchResponse {
    pub schema_version: u32,
    pub modality: ResultModalityOutput,
    pub witnesses: Vec<PathWitnessOutput>,
    pub effects: Vec<EffectOutput>,
    pub incomplete: Vec<IncompleteSearchOutput>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct SearchMatchOutput {
    pub bindings: Vec<BindingOutput>,
    pub constraints: Vec<Value>,
    pub state: SearchStateOutput,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct PatternSearchResponse {
    pub schema_version: u32,
    pub modality: ResultModalityOutput,
    pub matches: Vec<SearchMatchOutput>,
    pub effects: Vec<EffectOutput>,
    pub incomplete: Vec<IncompleteSearchOutput>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct PathSearchMatchOutput {
    pub bindings: Vec<BindingOutput>,
    pub constraints: Vec<Value>,
    pub witness: PathWitnessOutput,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct PathPatternSearchResponse {
    pub schema_version: u32,
    pub modality: ResultModalityOutput,
    pub matches: Vec<PathSearchMatchOutput>,
    pub effects: Vec<EffectOutput>,
    pub incomplete: Vec<IncompleteSearchOutput>,
}

fn encode_term(term: &Term) -> Result<Value, BackendError> {
    encode_pattern(&externalize::term(term))
}

fn encode_variable(variable: &k_rust_backend::term::Variable) -> Result<Value, BackendError> {
    encode_term(&Term::variable(variable.clone()))
}

fn encode_predicate(
    predicate: &k_rust_backend::rule::Predicate,
    result_sort: &Sort,
) -> Result<Value, BackendError> {
    encode_pattern(&externalize::predicate_pattern(predicate, result_sort))
}

fn bindings_output(bindings: Substitution) -> Result<Vec<BindingOutput>, BackendError> {
    bindings
        .into_iter()
        .map(|(variable, value)| {
            Ok(BindingOutput {
                variable: encode_variable(&variable)?,
                value: encode_term(&value)?,
            })
        })
        .collect()
}

fn term_pairs_output(pairs: Vec<(Term, Term)>) -> Result<Vec<TermPairOutput>, BackendError> {
    pairs
        .into_iter()
        .map(|(left, right)| {
            Ok(TermPairOutput {
                left: encode_term(&left)?,
                right: encode_term(&right)?,
            })
        })
        .collect()
}

fn predicates_output(
    predicates: Vec<k_rust_backend::rule::Predicate>,
    result_sort: &Sort,
) -> Result<Vec<Value>, BackendError> {
    predicates
        .iter()
        .map(|predicate| encode_predicate(predicate, result_sort))
        .collect()
}

fn effect_output(effect: BuiltinEffect) -> EffectOutput {
    match effect {
        BuiltinEffect::UserLog(message) => EffectOutput::UserLog { message },
    }
}

fn effects_output(effects: Vec<BuiltinEffect>) -> Vec<EffectOutput> {
    effects.into_iter().map(effect_output).collect()
}

fn transition_id_output(id: TransitionId) -> TransitionIdOutput {
    TransitionIdOutput {
        rule: id.rule,
        target: id.target.to_string(),
    }
}

fn transition_class_output(class: TransitionClass) -> TransitionClassOutput {
    match class {
        TransitionClass::Rewrite => TransitionClassOutput::Rewrite,
        TransitionClass::Remainder => TransitionClassOutput::Remainder,
        TransitionClass::FunctionEquation => TransitionClassOutput::FunctionEquation,
        TransitionClass::Simplification => TransitionClassOutput::Simplification,
        TransitionClass::Builtin => TransitionClassOutput::Builtin,
        TransitionClass::Claim => TransitionClassOutput::Claim,
    }
}

fn transition_observation_output(
    observation: TransitionObservation,
) -> Result<ObservationEventOutput, BackendError> {
    let result_sort = observation.after.term.sort();
    Ok(ObservationEventOutput::Transition {
        id: transition_id_output(observation.id),
        class: transition_class_output(observation.class),
        rule_label: observation.rule_label,
        bindings: bindings_output(observation.bindings)?,
        introduced_predicates: predicates_output(observation.introduced_predicates, &result_sort)?,
        before: encode_pattern(&externalize::constrained_pattern(&observation.before))?,
        after: encode_pattern(&externalize::constrained_pattern(&observation.after))?,
        effects: effects_output(observation.effects),
    })
}

fn uncommitted_observation_output(observation: UncommittedObservation) -> ObservationEventOutput {
    ObservationEventOutput::Uncommitted {
        id: transition_id_output(observation.id),
        rule_label: observation.rule_label,
        effects: effects_output(observation.effects),
        reason: match observation.reason {
            UncommittedReason::RolledBack => UncommittedReasonOutput::RolledBack,
        },
    }
}

fn observation_event_output(
    event: ObservationEvent,
) -> Result<ObservationEventOutput, BackendError> {
    match event {
        ObservationEvent::Transition(observation) => transition_observation_output(observation),
        ObservationEvent::Uncommitted(observation) => {
            Ok(uncommitted_observation_output(observation))
        }
    }
}

fn observations_output(
    observations: Vec<ObservationEvent>,
) -> Result<Vec<ObservationEventOutput>, BackendError> {
    observations
        .into_iter()
        .map(observation_event_output)
        .collect()
}

fn search_state_output(state: SearchState) -> Result<SearchStateOutput, BackendError> {
    Ok(SearchStateOutput {
        state: encode_pattern(&externalize::constrained_pattern(&state.pattern))?,
        depth: state.depth,
        trace: state.trace.into_iter().map(trace_entry).collect(),
        branch: state.branch.into_iter().map(transition_id_output).collect(),
        observations: observations_output(state.observations)?,
    })
}

fn path_witness_output(witness: PathWitness) -> Result<PathWitnessOutput, BackendError> {
    Ok(PathWitnessOutput {
        id: witness.id.into_iter().map(transition_id_output).collect(),
        state: encode_pattern(&externalize::constrained_pattern(&witness.pattern))?,
        depth: witness.depth,
        trace: witness.trace.into_iter().map(trace_entry).collect(),
        observations: observations_output(witness.observations)?,
    })
}

fn builtin_failure_output(error: BuiltinError) -> BuiltinFailureOutput {
    match error {
        BuiltinError::Interrupted => BuiltinFailureOutput::Interrupted,
        BuiltinError::WrongArity {
            hook,
            expected,
            actual,
        } => BuiltinFailureOutput::WrongArity {
            hook,
            expected,
            actual,
        },
        BuiltinError::UnexpectedSort {
            hook,
            expected,
            actual,
        } => BuiltinFailureOutput::UnexpectedSort {
            hook,
            expected: externalize::sort(&expected).to_string(),
            actual: externalize::sort(&actual).to_string(),
        },
        BuiltinError::AlternativeSortsDiffer {
            then_sort,
            else_sort,
        } => BuiltinFailureOutput::AlternativeSortsDiffer {
            then_sort: externalize::sort(&then_sort).to_string(),
            else_sort: externalize::sort(&else_sort).to_string(),
        },
        BuiltinError::IncompatibleMapSorts { left, right } => {
            BuiltinFailureOutput::IncompatibleMapSorts {
                left: externalize::sort(&left).to_string(),
                right: externalize::sort(&right).to_string(),
            }
        }
        BuiltinError::InvalidFloatToken { hook, token } => {
            BuiltinFailureOutput::InvalidFloatToken { hook, token }
        }
        BuiltinError::UnsupportedFloatFormat {
            hook,
            precision,
            exponent_bits,
        } => BuiltinFailureOutput::UnsupportedFloatFormat {
            hook,
            precision,
            exponent_bits,
        },
        BuiltinError::UnsupportedFloatFormatParameters {
            hook,
            precision,
            exponent_bits,
        } => BuiltinFailureOutput::UnsupportedFloatFormatParameters {
            hook,
            precision,
            exponent_bits,
        },
        BuiltinError::MismatchedFloatFormats {
            hook,
            left_precision,
            left_exponent_bits,
            right_precision,
            right_exponent_bits,
        } => BuiltinFailureOutput::MismatchedFloatFormats {
            hook,
            left_precision,
            left_exponent_bits,
            right_precision,
            right_exponent_bits,
        },
    }
}

fn translation_failure_output(
    error: TranslationError,
    result_sort: &Sort,
) -> Result<TranslationFailureOutput, BackendError> {
    Ok(match error {
        TranslationError::NonBooleanAnd(term) => TranslationFailureOutput::NonBooleanAnd {
            term: encode_term(&term)?,
        },
        TranslationError::PlaceholderOutOfBounds {
            placeholder,
            arguments,
        } => TranslationFailureOutput::PlaceholderOutOfBounds {
            placeholder,
            arguments,
        },
        TranslationError::UnsupportedPredicate(predicate) => {
            TranslationFailureOutput::UnsupportedPredicate {
                predicate: predicate.into(),
            }
        }
        TranslationError::ParametricSort(sort) => TranslationFailureOutput::ParametricSort {
            sort: externalize::sort(&sort).to_string(),
        },
        TranslationError::SmtLemmaSurplusMappings { rule_id, terms } => {
            TranslationFailureOutput::SmtLemmaSurplusMappings {
                rule: rule_id,
                terms: terms.iter().map(encode_term).collect::<Result<_, _>>()?,
            }
        }
        TranslationError::SmtLemmaSurplusPredicates {
            rule_id,
            predicates,
        } => TranslationFailureOutput::SmtLemmaSurplusPredicates {
            rule: rule_id,
            predicates: predicates_output(predicates, result_sort)?,
        },
        TranslationError::MissingSmtLemmaVariable { rule_id, variable } => {
            TranslationFailureOutput::MissingSmtLemmaVariable {
                rule: rule_id,
                variable: encode_variable(&variable)?,
            }
        }
    })
}

fn smt_failure_output(
    error: SmtError,
    result_sort: &Sort,
) -> Result<SmtFailureOutput, BackendError> {
    Ok(match error {
        SmtError::Translation(error) => SmtFailureOutput::Translation {
            error: translation_failure_output(error, result_sort)?,
        },
        SmtError::Unavailable => SmtFailureOutput::Unavailable,
        SmtError::InconsistentPrelude => SmtFailureOutput::InconsistentPrelude,
        SmtError::UnknownPrelude(reason) => SmtFailureOutput::UnknownPrelude { reason },
        SmtError::Unknown(reason) => SmtFailureOutput::Unknown { reason },
        SmtError::InconsistentGroundTruth => SmtFailureOutput::InconsistentGroundTruth,
        SmtError::MissingModel => SmtFailureOutput::MissingModel,
        SmtError::MissingModelValue(variable) => SmtFailureOutput::MissingModelValue {
            variable: encode_variable(&variable)?,
        },
        SmtError::InvalidModelValue { variable, value } => SmtFailureOutput::InvalidModelValue {
            variable: encode_variable(&variable)?,
            value,
        },
    })
}

fn satisfiability_output(
    satisfiability: Result<Satisfiability, SmtError>,
    result_sort: &Sort,
) -> Result<SatisfiabilityOutput, BackendError> {
    Ok(match satisfiability {
        Ok(Satisfiability::Sat) => SatisfiabilityOutput::Sat,
        Ok(Satisfiability::Unsat) => SatisfiabilityOutput::Unsat,
        Ok(Satisfiability::Unknown(reason)) => SatisfiabilityOutput::Unknown { reason },
        Err(error) => SatisfiabilityOutput::Error {
            error: smt_failure_output(error, result_sort)?,
        },
    })
}

fn simplification_failure_output(
    error: SimplificationError,
    result_sort: &Sort,
) -> Result<SearchFailureOutput, BackendError> {
    Ok(match error {
        SimplificationError::Cancelled => SearchFailureOutput::Cancelled,
        SimplificationError::Builtin(error) => SearchFailureOutput::Builtin {
            error: builtin_failure_output(error),
        },
        SimplificationError::ConflictingResults { rule_ids } => {
            SearchFailureOutput::ConflictingResults { rules: rule_ids }
        }
        SimplificationError::Smt { rule_id, error } => SearchFailureOutput::Smt {
            rule: Some(rule_id),
            error: smt_failure_output(error, result_sort)?,
        },
        SimplificationError::SmtPredicate { predicate, error } => {
            SearchFailureOutput::SmtPredicate {
                predicate: encode_predicate(&predicate, result_sort)?,
                error: smt_failure_output(error, result_sort)?,
            }
        }
        SimplificationError::InconsistentGroundTruth { rule_id } => {
            SearchFailureOutput::InconsistentGroundTruth {
                rule: Some(rule_id),
            }
        }
        SimplificationError::IterationLimit { limit, term } => {
            SearchFailureOutput::IterationLimit {
                limit,
                term: Some(encode_term(&term)?),
            }
        }
        SimplificationError::PredicateIterationLimit { limit, predicate } => {
            SearchFailureOutput::PredicateIterationLimit {
                limit,
                predicate: Some(encode_predicate(&predicate, result_sort)?),
            }
        }
        SimplificationError::InvalidBuiltinResultSymbol { hook, symbol } => {
            SearchFailureOutput::InvalidBuiltinResultSymbol {
                hook: hook.into(),
                symbol: symbol.into(),
            }
        }
    })
}

fn indeterminate_failure_output(
    reason: IndeterminateReason,
    result_sort: &Sort,
) -> Result<SearchFailureOutput, BackendError> {
    Ok(match reason {
        IndeterminateReason::Simplification { rule_id, error } => {
            let failure = simplification_failure_output(error, result_sort)?;
            match (rule_id, failure) {
                (Some(rule), SearchFailureOutput::Smt { error, .. }) => SearchFailureOutput::Smt {
                    rule: Some(rule),
                    error,
                },
                (_, failure) => failure,
            }
        }
        IndeterminateReason::Match {
            rule_id,
            substitution,
            remainder,
        } => SearchFailureOutput::Match {
            rule: rule_id,
            bindings: bindings_output(substitution)?,
            remainder: term_pairs_output(remainder)?,
        },
        IndeterminateReason::Requires {
            rule_id,
            predicates,
        } => SearchFailureOutput::Requires {
            rule: rule_id,
            predicates: predicates_output(predicates, result_sort)?,
        },
        IndeterminateReason::Concreteness { rule_id, variable } => {
            SearchFailureOutput::Concreteness {
                rule: rule_id,
                variable: encode_variable(&variable)?,
            }
        }
        IndeterminateReason::Smt { rule_id, error } => SearchFailureOutput::Smt {
            rule: Some(rule_id),
            error: smt_failure_output(error, result_sort)?,
        },
        IndeterminateReason::Remainder {
            rule_ids,
            predicates,
            satisfiability,
        } => SearchFailureOutput::Remainder {
            rules: rule_ids,
            predicates: predicates_output(predicates, result_sort)?,
            satisfiability: satisfiability_output(satisfiability, result_sort)?,
        },
    })
}

fn incomplete_search_output(
    incomplete: IncompleteSearch,
) -> Result<IncompleteSearchOutput, BackendError> {
    Ok(match incomplete {
        IncompleteSearch::ResultBound => IncompleteSearchOutput::ResultBound,
        IncompleteSearch::DepthBound(state) => IncompleteSearchOutput::DepthBound {
            state: search_state_output(state)?,
        },
        IncompleteSearch::BreadthBound(states) => IncompleteSearchOutput::BreadthBound {
            states: states
                .into_iter()
                .map(search_state_output)
                .collect::<Result<_, _>>()?,
        },
        IncompleteSearch::Indeterminate { state, reason } => {
            let result_sort = state.pattern.term.sort();
            IncompleteSearchOutput::Indeterminate {
                state: search_state_output(state)?,
                reason: indeterminate_failure_output(reason, &result_sort)?,
            }
        }
        IncompleteSearch::Cancelled(state) => IncompleteSearchOutput::Cancelled {
            state: search_state_output(state)?,
        },
        IncompleteSearch::Simplification { state, error } => {
            let result_sort = state.pattern.term.sort();
            IncompleteSearchOutput::Simplification {
                state: search_state_output(state)?,
                error: simplification_failure_output(error, &result_sort)?,
            }
        }
        IncompleteSearch::Match {
            state,
            substitution,
            remainder,
        } => IncompleteSearchOutput::Match {
            state: search_state_output(state)?,
            bindings: bindings_output(substitution)?,
            remainder: term_pairs_output(remainder)?,
        },
        IncompleteSearch::Smt { state, error } => {
            let result_sort = state.pattern.term.sort();
            IncompleteSearchOutput::Smt {
                state: search_state_output(state)?,
                error: smt_failure_output(error, &result_sort)?,
            }
        }
    })
}

fn incomplete_searches_output(
    incomplete: Vec<IncompleteSearch>,
) -> Result<Vec<IncompleteSearchOutput>, BackendError> {
    incomplete
        .into_iter()
        .map(incomplete_search_output)
        .collect()
}

pub(super) fn execution_response(
    result: k_rust_backend::rewrite::ExecutionResult,
) -> Result<ExecutionResult, BackendError> {
    Ok(ExecutionResult {
        leaves: result
            .leaves
            .into_iter()
            .map(|leaf| {
                let (reason, detail) = halt_reason(&leaf.halt_reason);
                Ok(ExecutionLeaf {
                    state: encode_pattern(&externalize::constrained_pattern(&leaf.pattern))?,
                    depth: leaf.depth,
                    reason: reason.into(),
                    detail,
                    trace: leaf.trace.into_iter().map(trace_entry).collect(),
                    branch: leaf.branch.into_iter().map(transition_id_output).collect(),
                    observations: observations_output(leaf.observations)?,
                })
            })
            .collect::<Result<_, BackendError>>()?,
        effects: effects_output(result.effects),
        discarded: result
            .discarded
            .into_iter()
            .map(uncommitted_observation_output)
            .collect(),
    })
}

pub(super) fn search_response(
    result: BackendSearchResult,
    schema_version: u32,
) -> Result<SearchResponse, BackendError> {
    Ok(SearchResponse {
        schema_version,
        modality: ResultModalityOutput::StateSet,
        states: result
            .states
            .into_iter()
            .map(search_state_output)
            .collect::<Result<_, _>>()?,
        effects: effects_output(result.effects),
        incomplete: incomplete_searches_output(result.incomplete)?,
    })
}

pub(super) fn path_search_response(
    result: BackendPathSearchResult,
    schema_version: u32,
) -> Result<PathSearchResponse, BackendError> {
    Ok(PathSearchResponse {
        schema_version,
        modality: ResultModalityOutput::PathSet,
        witnesses: result
            .witnesses
            .into_iter()
            .map(path_witness_output)
            .collect::<Result<_, _>>()?,
        effects: effects_output(result.effects),
        incomplete: incomplete_searches_output(result.incomplete)?,
    })
}

pub(super) fn pattern_search_response(
    result: BackendPatternSearchResult,
    schema_version: u32,
) -> Result<PatternSearchResponse, BackendError> {
    Ok(PatternSearchResponse {
        schema_version,
        modality: ResultModalityOutput::StateSet,
        matches: result
            .matches
            .into_iter()
            .map(|found| {
                let result_sort = found.state.pattern.term.sort();
                Ok(SearchMatchOutput {
                    bindings: bindings_output(found.substitution)?,
                    constraints: predicates_output(found.constraints, &result_sort)?,
                    state: search_state_output(found.state)?,
                })
            })
            .collect::<Result<_, BackendError>>()?,
        effects: effects_output(result.effects),
        incomplete: incomplete_searches_output(result.incomplete)?,
    })
}

pub(super) fn path_pattern_search_response(
    result: BackendPatternPathSearchResult,
    schema_version: u32,
) -> Result<PathPatternSearchResponse, BackendError> {
    Ok(PathPatternSearchResponse {
        schema_version,
        modality: ResultModalityOutput::PathSet,
        matches: result
            .matches
            .into_iter()
            .map(|found| {
                let result_sort = found.witness.pattern.term.sort();
                Ok(PathSearchMatchOutput {
                    bindings: bindings_output(found.substitution)?,
                    constraints: predicates_output(found.constraints, &result_sort)?,
                    witness: path_witness_output(found.witness)?,
                })
            })
            .collect::<Result<_, BackendError>>()?,
        effects: effects_output(result.effects),
        incomplete: incomplete_searches_output(result.incomplete)?,
    })
}
