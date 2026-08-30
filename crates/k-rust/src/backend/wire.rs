//! Versioned JSON wire contracts for persistent search and observation.

use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::{BackendError, TraceEntry};
use k_rust_backend::simplify::DEFAULT_MAX_SIMPLIFICATION_ITERATIONS;

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
    NonBooleanAnd,
    PlaceholderOutOfBounds {
        placeholder: usize,
        arguments: usize,
    },
    UnsupportedPredicate {
        predicate: String,
    },
    ParametricSort,
    SmtLemmaSurplusMappings {
        rule: String,
    },
    SmtLemmaSurplusPredicates {
        rule: String,
    },
    MissingSmtLemmaVariable {
        rule: String,
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
    MissingModelValue,
    InvalidModelValue { value: String },
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
        error: SmtFailureOutput,
    },
    InconsistentGroundTruth {
        #[serde(skip_serializing_if = "Option::is_none")]
        rule: Option<String>,
    },
    IterationLimit {
        limit: usize,
    },
    PredicateIterationLimit {
        limit: usize,
    },
    InvalidBuiltinResultSymbol {
        hook: String,
        symbol: String,
    },
    Match {
        rule: String,
    },
    Requires {
        rule: String,
    },
    Concreteness {
        rule: String,
    },
    Remainder {
        rules: Vec<String>,
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
