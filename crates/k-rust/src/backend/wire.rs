//! Versioned JSON wire contracts v1 for the JavaScript hosts; converters only.

use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::{
    BackendError, ExecutionCandidateOutput, ExecutionLeaf, ExecutionRemainderOutput,
    ExecutionResult, TraceEntry, encode_pattern as encode_pattern_value, halt_reason, trace_entry,
};
use crate::kore::ast::Pattern as KorePattern;
use k_rust_backend::{
    builtin::{BuiltinEffect, BuiltinError},
    diagnostic::BackendDiagnostic,
    externalize,
    rewrite::{AppliedRule, HaltReason, IndeterminateReason, RemainderBranch},
    search::{
        IncompleteSearch, PathSearchResult as BackendPathSearchResult, PathWitness,
        PatternPathSearchResult as BackendPatternPathSearchResult,
        PatternSearchResult as BackendPatternSearchResult, ResultModality,
        SearchResult as BackendSearchResult, SearchState,
    },
    simplify::{
        BudgetSubject, ConditionIndeterminacy, ContradictedTotal,
        DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationError,
    },
    smt::{Satisfiability, SmtError, TranslationError},
    substitution::Substitution,
    term::{Sort, Term},
    transition::{
        EvaluationClass, EvaluationObservation, ObservationEvent, TransitionClass, TransitionId,
        TransitionObservation, UncommittedObservation, UncommittedReason,
    },
};
#[cfg(feature = "measure")]
use k_rust_kore::measure::{self, Counter};

pub const BACKEND_SCHEMA_VERSION: u32 = 1;

/// The backend classification of a compiled axiom.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum CompiledRuleKind {
    Rewrite,
    FunctionEquation,
    Simplification,
    Definedness,
}

/// A written KORE axiom's source and location attributes, when present.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct CompiledRuleOriginOutput {
    pub source: Option<String>,
    pub location: Option<String>,
}

/// An application of a symbol declared `total` (or `functional`) that one of its equations
/// reduced to bottom (`k_rust_backend::simplify::ContradictedTotal`).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct ContradictedTotalOutput {
    /// The KORE name of the symbol whose attribute is contradicted.
    pub symbol: String,
    /// The K label that name encodes (`tDiv(_)_M_Int_Int`, or the `symbol(...)` name), as the
    /// CLI prints it; absent when the KORE name is not a label encoding.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub k_label: Option<String>,
    /// The equation's compiled id, as in the rule catalog.
    pub rule_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rule_label: Option<String>,
    /// Where the equation is written, when the KORE carries it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub origin: Option<CompiledRuleOriginOutput>,
    /// The application the equation rewrote (KORE JSON).
    pub application: Value,
    /// The undefined term the equation's result reached (KORE JSON).
    pub undefined: Value,
}

fn contradicted_total_output(
    contradicted: &ContradictedTotal,
) -> Result<ContradictedTotalOutput, BackendError> {
    Ok(ContradictedTotalOutput {
        symbol: contradicted.symbol().to_owned(),
        k_label: crate::kast::identifier::decode_label(contradicted.symbol())
            .ok()
            .filter(|label| label != contradicted.symbol()),
        rule_id: contradicted.rule_id.clone(),
        rule_label: contradicted.label.clone(),
        origin: contradicted
            .origin
            .as_ref()
            .map(|origin| CompiledRuleOriginOutput {
                source: origin.source.clone(),
                location: origin.location.clone(),
            }),
        application: encode_term(&contradicted.application)?,
        undefined: encode_term(&contradicted.undefined_term)?,
    })
}

/// One compiled rule, after equivalent written axioms have been collapsed.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct CompiledRuleOutput {
    pub id: String,
    pub kind: CompiledRuleKind,
    pub executable: bool,
    pub label: Option<String>,
    pub priority: u8,
    pub origins: Vec<CompiledRuleOriginOutput>,
    pub shared_identity: bool,
}

pub(super) fn validate_schema_version(schema_version: u32) -> Result<(), BackendError> {
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
    /// An optional event allowlist; an empty list emits no events but retains every branch identity.
    #[serde(default)]
    pub rules: Option<Vec<String>>,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ResultModalityOutput {
    StateSet,
    PathSet,
}

impl From<ResultModality> for ResultModalityOutput {
    fn from(modality: ResultModality) -> Self {
        match modality {
            ResultModality::StateSet => Self::StateSet,
            ResultModality::PathSet => Self::PathSet,
        }
    }
}

impl From<ResultModalityOutput> for ResultModality {
    fn from(modality: ResultModalityOutput) -> Self {
        match modality {
            ResultModalityOutput::StateSet => Self::StateSet,
            ResultModalityOutput::PathSet => Self::PathSet,
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct TransitionIdOutput {
    pub rule: String,
    pub target: String,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct SearchStateOutput {
    pub state: Value,
    /// The backend diagnostics of the path in `trace`, each distinct diagnostic once, in the
    /// order the path first met them; omitted when the path emitted none.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<BackendDiagnosticOutput>,
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
    /// The backend diagnostics of this witness's path, as for `SearchStateOutput::diagnostics`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<BackendDiagnosticOutput>,
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
#[serde(
    tag = "kind",
    deny_unknown_fields,
    rename_all = "kebab-case",
    rename_all_fields = "camelCase"
)]
pub enum BuiltinFailureOutput {
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
pub enum ConditionIndeterminacyOutput {
    NoSolver,
    ImplicationIndeterminate,
    SmtUnknown { reason: String },
    InconsistentPathCondition,
    Untranslatable { error: TranslationFailureOutput },
    NonFunctionalBinding,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum BudgetSubjectOutput {
    Term,
    Predicates,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "kebab-case")]
pub enum BackendDiagnosticOutput {
    UndecidedCondition {
        #[serde(rename = "ruleId")]
        rule_id: String,
        reason: ConditionIndeterminacyOutput,
        predicates: Vec<Value>,
    },
    UndecidedPredicate {
        predicate: Value,
        reason: ConditionIndeterminacyOutput,
    },
    SimplificationBudgetExhausted {
        limit: usize,
        subject: BudgetSubjectOutput,
    },
    RuleConditionUnsimplified {
        #[serde(rename = "ruleId")]
        rule_id: String,
        limit: usize,
    },
    UnsupportedHookUnevaluated {
        hook: String,
        reason: String,
    },
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "kebab-case")]
pub enum SmtFailureOutput {
    Translation {
        error: TranslationFailureOutput,
    },
    /// The query needed an SMT solver, but this build has none.
    Unavailable,
    InconsistentPrelude,
    UnknownPrelude {
        reason: String,
    },
    Unknown {
        reason: String,
    },
    InconsistentGroundTruth,
    MissingModel,
    MissingModelValue {
        variable: Value,
    },
    InvalidModelValue {
        variable: Value,
        value: String,
    },
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
#[serde(
    tag = "kind",
    deny_unknown_fields,
    rename_all = "kebab-case",
    rename_all_fields = "camelCase"
)]
pub enum SearchFailureOutput {
    StackExhausted,
    /// A macro or alias survived preprocessing, so the state is not executable.
    SurvivingMacroOrAlias {
        symbol: String,
    },
    Builtin {
        error: BuiltinFailureOutput,
    },
    ConflictingResults {
        rules: Vec<String>,
    },
    /// A rule's satisfiability or validity query could not be decided.
    /// `Unavailable` means the build has no solver for that query.
    Smt {
        #[serde(skip_serializing_if = "Option::is_none")]
        rule: Option<String>,
        error: SmtFailureOutput,
    },
    /// A standalone predicate query could not be decided.
    /// `Unavailable` means the build has no solver for that query.
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
    UnsupportedHook {
        hook: String,
        reason: String,
        term: Value,
    },
    /// Matching a rule left-hand side left an unsupported unification remainder.
    /// This does not itself report a solver query; a prior undecided equation can still be relevant.
    Match {
        rule: String,
        bindings: Vec<BindingOutput>,
        remainder: Vec<TermPairOutput>,
    },
    /// A rule's right-hand side needs variables that matching did not bind.
    /// This does not report a missing solver.
    Instantiation {
        rule: String,
        missing_variables: Vec<Value>,
    },
    /// A rule's `requires` could not be decided because this build has no SMT solver.
    /// A solver-enabled build would attempt to decide or branch on this condition.
    Requires {
        rule: String,
        predicates: Vec<Value>,
    },
    /// No longer emitted; retained so older concreteness-check outputs still deserialize.
    Concreteness {
        rule: String,
        variable: Value,
    },
    /// A priority group's remaining path could not be classified as satisfiable or unsatisfiable.
    /// An `Error` containing `Unavailable` means this build has no solver for that query.
    Remainder {
        rules: Vec<String>,
        predicates: Vec<Value>,
        satisfiability: SatisfiabilityOutput,
    },
}

impl SearchFailureOutput {
    /// Whether the stopped step needed an SMT solver that this build lacks.
    ///
    /// This is sufficient, not necessary, for a solver-enabled build to decide the path:
    /// without a solver, an undecided equation condition may leave a function unevaluated,
    /// which can later surface as `Match` instead.
    pub fn solver_unavailable(&self) -> bool {
        matches!(
            self,
            Self::Requires { .. }
                | Self::Smt {
                    error: SmtFailureOutput::Unavailable,
                    ..
                }
                | Self::SmtPredicate {
                    error: SmtFailureOutput::Unavailable,
                    ..
                }
                | Self::Remainder {
                    satisfiability: SatisfiabilityOutput::Error {
                        error: SmtFailureOutput::Unavailable,
                    },
                    ..
                }
        )
    }
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
    /// Reserved for a circularity or trusted claim applied inside an observable proof.
    /// No operation emits this class yet.
    Claim,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum EvaluationClassOutput {
    FunctionEquation,
    Simplification,
    Builtin,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum UncommittedReasonOutput {
    RolledBack,
}

/// One observation event of a branch.
///
/// A `transition` event names, by `id`, an element of the branch it is reported on that the rule
/// filter admits, in branch order. An `evaluation` event records an equation, simplification, or builtin application that
/// normalized a state of the branch; `anchor` is the number of branch entries that precede it, so
/// the normalized state is the one reached by the first `anchor` transitions. Evaluation events
/// are diagnostics whose presence, multiplicity, and order depend on the simplifier's strategy
/// (`k_rust_backend::transition::EvaluationObservation`).
#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(
    tag = "kind",
    deny_unknown_fields,
    rename_all = "kebab-case",
    rename_all_fields = "camelCase"
)]
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
        /// Attributes the leaf's committed effects to this observed transition.
        effects: Vec<EffectOutput>,
    },
    Evaluation {
        rule: String,
        class: EvaluationClassOutput,
        #[serde(skip_serializing_if = "Option::is_none")]
        rule_label: Option<String>,
        anchor: usize,
        before: Value,
        after: Value,
        effects: Vec<EffectOutput>,
    },
    Uncommitted {
        id: TransitionIdOutput,
        #[serde(skip_serializing_if = "Option::is_none")]
        rule_label: Option<String>,
        /// Effects attempted by this rolled-back transition; no leaf commits them.
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
    /// The backend diagnostics of matching `state` against the target pattern, apart from the
    /// state's own path diagnostics (`state.diagnostics`); omitted when the match emitted none.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<BackendDiagnosticOutput>,
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
    /// The backend diagnostics of matching `witness` against the target pattern, apart from the
    /// witness path's own (`witness.diagnostics`); omitted when the match emitted none.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<BackendDiagnosticOutput>,
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

fn encode_pattern_source<'a, S: k_rust_kore::kore::node::PatternSource<'a>>(
    pattern: &KorePattern,
    source: S,
) -> Result<Value, BackendError> {
    let value = encode_pattern_value(pattern)?;
    #[cfg(feature = "measure")]
    if measure::output_counting_enabled() {
        let (nodes, distinct) = k_rust_kore::kore::node::measure_nodes(source);
        measure::add(Counter::ObservationJsonNodesWritten, nodes);
        measure::add(Counter::ObservationJsonDistinctNodes, distinct);
        if let Ok(bytes) = serde_json::to_vec(&value) {
            measure::add(Counter::ObservationJsonBytesWritten, bytes.len() as u64);
        }
    }
    #[cfg(not(feature = "measure"))]
    let _ = source;
    Ok(value)
}

fn encode_term(term: &Term) -> Result<Value, BackendError> {
    encode_pattern_source(&externalize::term(term), externalize::External::Term(term))
}

fn encode_variable(variable: &k_rust_backend::term::Variable) -> Result<Value, BackendError> {
    encode_term(&Term::variable(variable.clone()))
}

fn encode_predicate(
    predicate: &k_rust_backend::rule::Predicate,
    result_sort: &Sort,
) -> Result<Value, BackendError> {
    encode_pattern_source(
        &externalize::predicate_pattern(predicate, result_sort),
        externalize::External::Predicate {
            predicate,
            sort: externalize::ResultSort::Given(result_sort),
            preserve_terms: false,
        },
    )
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
        TransitionClass::Claim => TransitionClassOutput::Claim,
    }
}

fn evaluation_class_output(class: EvaluationClass) -> EvaluationClassOutput {
    match class {
        EvaluationClass::FunctionEquation => EvaluationClassOutput::FunctionEquation,
        EvaluationClass::Simplification => EvaluationClassOutput::Simplification,
        EvaluationClass::Builtin => EvaluationClassOutput::Builtin,
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
        before: encode_pattern_source(
            &externalize::constrained_pattern(&observation.before),
            externalize::External::Constrained(&observation.before),
        )?,
        after: encode_pattern_source(
            &externalize::constrained_pattern(&observation.after),
            externalize::External::Constrained(&observation.after),
        )?,
        effects: effects_output(observation.effects),
    })
}

fn evaluation_observation_output(
    observation: EvaluationObservation,
) -> Result<ObservationEventOutput, BackendError> {
    Ok(ObservationEventOutput::Evaluation {
        rule: observation.rule,
        class: evaluation_class_output(observation.class),
        rule_label: observation.rule_label,
        anchor: observation.anchor,
        before: encode_pattern_source(
            &externalize::constrained_pattern(&observation.before),
            externalize::External::Constrained(&observation.before),
        )?,
        after: encode_pattern_source(
            &externalize::constrained_pattern(&observation.after),
            externalize::External::Constrained(&observation.after),
        )?,
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
        ObservationEvent::Evaluation(observation) => evaluation_observation_output(observation),
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
    let result_sort = state.pattern.term.sort();
    Ok(SearchStateOutput {
        state: encode_pattern_source(
            &externalize::constrained_pattern(&state.pattern),
            externalize::External::Constrained(&state.pattern),
        )?,
        diagnostics: diagnostics_output(state.diagnostics, &result_sort)?,
        depth: state.depth,
        trace: state.trace.into_iter().map(trace_entry).collect(),
        branch: state.branch.into_iter().map(transition_id_output).collect(),
        observations: observations_output(state.observations)?,
    })
}

fn path_witness_output(witness: PathWitness) -> Result<PathWitnessOutput, BackendError> {
    let result_sort = witness.pattern.term.sort();
    Ok(PathWitnessOutput {
        id: witness.id.into_iter().map(transition_id_output).collect(),
        state: encode_pattern_source(
            &externalize::constrained_pattern(&witness.pattern),
            externalize::External::Constrained(&witness.pattern),
        )?,
        diagnostics: diagnostics_output(witness.diagnostics, &result_sort)?,
        depth: witness.depth,
        trace: witness.trace.into_iter().map(trace_entry).collect(),
        observations: observations_output(witness.observations)?,
    })
}

/// Search publishes builtin failures only inside a simplification failure, and it reports a
/// hook's interruption as its `cancelled` entry, so an interruption reaching here is an
/// invariant breach rather than a published kind.
fn builtin_failure_output(error: BuiltinError) -> Result<BuiltinFailureOutput, BackendError> {
    Ok(match error {
        BuiltinError::Interrupted => return Err(interruption_published_as_failure()),
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
    })
}

/// Search arms no step deadline, so request cancellation is its only interruption source, and it
/// reports every interruption signal (the simplifier's `Cancelled` and `Interrupted`, and a
/// hook's `Interrupted`) as the state's `cancelled` incomplete entry, never as a failure reason.
/// An interruption signal inside a failure therefore means search produced an outcome its
/// contract cannot produce.
fn interruption_published_as_failure() -> BackendError {
    BackendError(
        "search reported an interruption as a failure, but search reports every interruption \
         as a cancelled entry"
            .into(),
    )
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

fn condition_indeterminacy_output(
    reason: ConditionIndeterminacy,
    result_sort: &Sort,
) -> Result<ConditionIndeterminacyOutput, BackendError> {
    Ok(match reason {
        ConditionIndeterminacy::NoSolver => ConditionIndeterminacyOutput::NoSolver,
        ConditionIndeterminacy::ImplicationIndeterminate => {
            ConditionIndeterminacyOutput::ImplicationIndeterminate
        }
        ConditionIndeterminacy::SmtUnknown(reason) => {
            ConditionIndeterminacyOutput::SmtUnknown { reason }
        }
        ConditionIndeterminacy::InconsistentPathCondition => {
            ConditionIndeterminacyOutput::InconsistentPathCondition
        }
        ConditionIndeterminacy::Untranslatable(error) => {
            ConditionIndeterminacyOutput::Untranslatable {
                error: translation_failure_output(error, result_sort)?,
            }
        }
        ConditionIndeterminacy::NonFunctionalBinding => {
            ConditionIndeterminacyOutput::NonFunctionalBinding
        }
    })
}

fn diagnostic_output(
    diagnostic: BackendDiagnostic,
    result_sort: &Sort,
) -> Result<BackendDiagnosticOutput, BackendError> {
    Ok(match diagnostic {
        BackendDiagnostic::UndecidedCondition {
            rule_id,
            reason,
            predicates,
        } => BackendDiagnosticOutput::UndecidedCondition {
            rule_id,
            reason: condition_indeterminacy_output(reason, result_sort)?,
            predicates: predicates_output(predicates, result_sort)?,
        },
        BackendDiagnostic::UndecidedPredicate { predicate, reason } => {
            BackendDiagnosticOutput::UndecidedPredicate {
                predicate: encode_predicate(&predicate, result_sort)?,
                reason: condition_indeterminacy_output(reason, result_sort)?,
            }
        }
        BackendDiagnostic::SimplificationBudgetExhausted { limit, subject } => {
            BackendDiagnosticOutput::SimplificationBudgetExhausted {
                limit,
                subject: match subject {
                    BudgetSubject::Term => BudgetSubjectOutput::Term,
                    BudgetSubject::Predicates => BudgetSubjectOutput::Predicates,
                },
            }
        }
        BackendDiagnostic::RuleConditionUnsimplified { rule_id, limit } => {
            BackendDiagnosticOutput::RuleConditionUnsimplified { rule_id, limit }
        }
        BackendDiagnostic::UnsupportedHookUnevaluated { hook, reason } => {
            BackendDiagnosticOutput::UnsupportedHookUnevaluated {
                hook,
                reason: reason.to_string(),
            }
        }
    })
}

fn diagnostics_output(
    diagnostics: Vec<BackendDiagnostic>,
    result_sort: &Sort,
) -> Result<Vec<BackendDiagnosticOutput>, BackendError> {
    diagnostics
        .into_iter()
        .map(|diagnostic| diagnostic_output(diagnostic, result_sort))
        .collect()
}

fn candidate_output(candidate: AppliedRule) -> Result<ExecutionCandidateOutput, BackendError> {
    let result_sort = candidate.pattern.term.sort();
    Ok(ExecutionCandidateOutput {
        state: encode_pattern_source(
            &externalize::constrained_pattern(&candidate.pattern),
            externalize::External::Constrained(&candidate.pattern),
        )?,
        unique_id: candidate.unique_id,
        label: candidate.label,
        diagnostics: diagnostics_output(candidate.diagnostics, &result_sort)?,
    })
}

fn remainder_output(remainder: RemainderBranch) -> Result<ExecutionRemainderOutput, BackendError> {
    let result_sort = remainder.pattern.term.sort();
    Ok(ExecutionRemainderOutput {
        state: encode_pattern_source(
            &externalize::constrained_pattern(&remainder.pattern),
            externalize::External::Constrained(&remainder.pattern),
        )?,
        rule_ids: remainder.rule_ids,
        diagnostics: diagnostics_output(remainder.diagnostics, &result_sort)?,
    })
}

fn execution_candidates_output(
    reason: HaltReason,
) -> Result<
    (
        Option<Vec<ExecutionCandidateOutput>>,
        Option<ExecutionRemainderOutput>,
    ),
    BackendError,
> {
    match reason {
        HaltReason::Branch {
            branches,
            remainder,
        } => Ok((
            Some(
                branches
                    .into_iter()
                    .map(candidate_output)
                    .collect::<Result<_, _>>()?,
            ),
            remainder.map(remainder_output).transpose()?,
        )),
        HaltReason::CutPointRule { next_states, .. } => Ok((
            Some(
                next_states
                    .into_iter()
                    .map(candidate_output)
                    .collect::<Result<_, _>>()?,
            ),
            None,
        )),
        _ => Ok((None, None)),
    }
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
        SimplificationError::Cancelled | SimplificationError::Interrupted => {
            return Err(interruption_published_as_failure());
        }
        SimplificationError::StackExhausted => SearchFailureOutput::StackExhausted,
        SimplificationError::Builtin(error) => SearchFailureOutput::Builtin {
            error: builtin_failure_output(error)?,
        },
        SimplificationError::DisjunctiveResult {
            rule_id,
            alternatives,
        } => SearchFailureOutput::ConflictingResults {
            rules: vec![rule_id; alternatives],
        },
        SimplificationError::TopEquationOutsideConjunction { rule_id } => {
            SearchFailureOutput::ConflictingResults {
                rules: vec![rule_id],
            }
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
        SimplificationError::UnsupportedHook { hook, reason, term } => {
            SearchFailureOutput::UnsupportedHook {
                hook,
                reason: reason.to_string(),
                term: encode_term(&term)?,
            }
        }
    })
}

fn indeterminate_failure_output(
    reason: IndeterminateReason,
    result_sort: &Sort,
) -> Result<SearchFailureOutput, BackendError> {
    Ok(match reason {
        IndeterminateReason::SurvivingMacroOrAlias { symbol } => {
            SearchFailureOutput::SurvivingMacroOrAlias {
                symbol: symbol.to_string(),
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
        IndeterminateReason::Instantiation {
            rule_id,
            missing_variables,
        } => SearchFailureOutput::Instantiation {
            rule: rule_id,
            missing_variables: missing_variables
                .iter()
                .map(encode_variable)
                .collect::<Result<_, _>>()?,
        },
        IndeterminateReason::Requires {
            rule_id,
            predicates,
        } => SearchFailureOutput::Requires {
            rule: rule_id,
            predicates: predicates_output(predicates, result_sort)?,
        },
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
        modality: result.modality.into(),
        leaves: result
            .leaves
            .into_iter()
            .map(|leaf| {
                let (reason, detail) = halt_reason(&leaf.halt_reason);
                let (rule_id, rule_label) = match &leaf.halt_reason {
                    HaltReason::Trivial { rule_id, label, .. } => (rule_id.clone(), label.clone()),
                    _ => (None, None),
                };
                let contradicted_total = match &leaf.halt_reason {
                    HaltReason::Trivial {
                        contradicted_total: Some(contradicted),
                        ..
                    }
                    | HaltReason::Vacuous {
                        contradicted_total: Some(contradicted),
                        ..
                    } => Some(contradicted_total_output(contradicted)?),
                    _ => None,
                };
                let result_sort = leaf.pattern.term.sort();
                let cause = match &leaf.halt_reason {
                    HaltReason::Indeterminate(reason) => {
                        Some(indeterminate_failure_output(reason.clone(), &result_sort)?)
                    }
                    _ => None,
                };
                let (candidates, remainder) = execution_candidates_output(leaf.halt_reason)?;
                Ok(ExecutionLeaf {
                    state: encode_pattern_source(
                        &externalize::constrained_pattern(&leaf.pattern),
                        externalize::External::Constrained(&leaf.pattern),
                    )?,
                    diagnostics: diagnostics_output(leaf.diagnostics, &result_sort)?,
                    candidates,
                    remainder,
                    depth: leaf.depth,
                    reason,
                    rule_id,
                    rule_label,
                    contradicted_total,
                    cause,
                    detail,
                    trace: leaf.trace.into_iter().map(trace_entry).collect(),
                    branch: leaf.branch.into_iter().map(transition_id_output).collect(),
                    effects: effects_output(leaf.effects),
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
                    diagnostics: diagnostics_output(found.diagnostics, &result_sort)?,
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
                    diagnostics: diagnostics_output(found.diagnostics, &result_sort)?,
                })
            })
            .collect::<Result<_, BackendError>>()?,
        effects: effects_output(result.effects),
        incomplete: incomplete_searches_output(result.incomplete)?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_search_failure_has_a_solver_availability_projection() {
        let cases = [
            (SearchFailureOutput::StackExhausted, false),
            (
                SearchFailureOutput::SurvivingMacroOrAlias { symbol: "m".into() },
                false,
            ),
            (
                SearchFailureOutput::Builtin {
                    error: BuiltinFailureOutput::AlternativeSortsDiffer {
                        then_sort: "A".into(),
                        else_sort: "B".into(),
                    },
                },
                false,
            ),
            (
                SearchFailureOutput::ConflictingResults { rules: vec![] },
                false,
            ),
            (
                SearchFailureOutput::Smt {
                    rule: Some("r".into()),
                    error: SmtFailureOutput::Unavailable,
                },
                true,
            ),
            (
                SearchFailureOutput::Smt {
                    rule: None,
                    error: SmtFailureOutput::Unknown {
                        reason: "unknown".into(),
                    },
                },
                false,
            ),
            (
                SearchFailureOutput::SmtPredicate {
                    predicate: Value::Null,
                    error: SmtFailureOutput::Unavailable,
                },
                true,
            ),
            (
                SearchFailureOutput::SmtPredicate {
                    predicate: Value::Null,
                    error: SmtFailureOutput::Unknown {
                        reason: "unknown".into(),
                    },
                },
                false,
            ),
            (
                SearchFailureOutput::InconsistentGroundTruth { rule: None },
                false,
            ),
            (
                SearchFailureOutput::IterationLimit {
                    limit: 1,
                    term: None,
                },
                false,
            ),
            (
                SearchFailureOutput::PredicateIterationLimit {
                    limit: 1,
                    predicate: None,
                },
                false,
            ),
            (
                SearchFailureOutput::InvalidBuiltinResultSymbol {
                    hook: "h".into(),
                    symbol: "s".into(),
                },
                false,
            ),
            (
                SearchFailureOutput::UnsupportedHook {
                    hook: "h".into(),
                    reason: "unsupported".into(),
                    term: Value::Null,
                },
                false,
            ),
            (
                SearchFailureOutput::Match {
                    rule: "r".into(),
                    bindings: vec![],
                    remainder: vec![],
                },
                false,
            ),
            (
                SearchFailureOutput::Instantiation {
                    rule: "r".into(),
                    missing_variables: vec![],
                },
                false,
            ),
            (
                SearchFailureOutput::Requires {
                    rule: "r".into(),
                    predicates: vec![],
                },
                true,
            ),
            (
                SearchFailureOutput::Concreteness {
                    rule: "r".into(),
                    variable: Value::Null,
                },
                false,
            ),
            (
                SearchFailureOutput::Remainder {
                    rules: vec![],
                    predicates: vec![],
                    satisfiability: SatisfiabilityOutput::Error {
                        error: SmtFailureOutput::Unavailable,
                    },
                },
                true,
            ),
            (
                SearchFailureOutput::Remainder {
                    rules: vec![],
                    predicates: vec![],
                    satisfiability: SatisfiabilityOutput::Unknown {
                        reason: "unknown".into(),
                    },
                },
                false,
            ),
            (
                SearchFailureOutput::Remainder {
                    rules: vec![],
                    predicates: vec![],
                    satisfiability: SatisfiabilityOutput::Error {
                        error: SmtFailureOutput::Unknown {
                            reason: "unknown".into(),
                        },
                    },
                },
                false,
            ),
        ];
        for (failure, expected) in cases {
            assert_eq!(failure.solver_unavailable(), expected, "{failure:?}");
        }
    }

    fn assert_typescript_variant_fields(union: &str, kind: &str, fields: &[&str]) {
        for source in [
            include_str!("../../../k-rust-napi/typescript/index.ts"),
            include_str!("../../../k-rust-wasm/typescript/index.ts"),
        ] {
            let declaration = source
                .split_once(&format!("export type {union} ="))
                .unwrap()
                .1
                .split("\nexport type ")
                .next()
                .unwrap();
            let variant = declaration
                .split("  | {")
                .find(|part| part.contains(&format!("kind: '{kind}'")))
                .unwrap_or_else(|| panic!("{union} has no {kind} variant"));
            let compact: String = variant.split_whitespace().collect();
            for field in fields {
                assert!(
                    compact.contains(&format!("{field}:")),
                    "{union}.{kind} is missing {field} in a TypeScript declaration"
                );
            }
        }
    }

    #[test]
    fn builtin_failure_field_names_match_both_typescript_declarations() {
        let cases = [
            (
                BuiltinFailureOutput::AlternativeSortsDiffer {
                    then_sort: "A".into(),
                    else_sort: "B".into(),
                },
                serde_json::json!({"kind": "alternative-sorts-differ", "thenSort": "A", "elseSort": "B"}),
            ),
            (
                BuiltinFailureOutput::UnsupportedFloatFormat {
                    hook: "FLOAT".into(),
                    precision: 53,
                    exponent_bits: 11,
                },
                serde_json::json!({"kind": "unsupported-float-format", "hook": "FLOAT", "precision": 53, "exponentBits": 11}),
            ),
            (
                BuiltinFailureOutput::UnsupportedFloatFormatParameters {
                    hook: "FLOAT".into(),
                    precision: "p".into(),
                    exponent_bits: "e".into(),
                },
                serde_json::json!({"kind": "unsupported-float-format-parameters", "hook": "FLOAT", "precision": "p", "exponentBits": "e"}),
            ),
            (
                BuiltinFailureOutput::MismatchedFloatFormats {
                    hook: "FLOAT".into(),
                    left_precision: 53,
                    left_exponent_bits: 11,
                    right_precision: 24,
                    right_exponent_bits: 8,
                },
                serde_json::json!({"kind": "mismatched-float-formats", "hook": "FLOAT", "leftPrecision": 53, "leftExponentBits": 11, "rightPrecision": 24, "rightExponentBits": 8}),
            ),
        ];
        for (failure, expected) in cases {
            let value = serde_json::to_value(&failure).unwrap();
            assert_eq!(value, expected);
            let kind = value["kind"].as_str().unwrap();
            let fields: Vec<_> = value
                .as_object()
                .unwrap()
                .keys()
                .map(String::as_str)
                .collect();
            assert_typescript_variant_fields("BuiltinFailure", kind, &fields);
            assert_eq!(
                serde_json::from_value::<BuiltinFailureOutput>(value).unwrap(),
                failure
            );
        }
    }

    #[test]
    fn branch_remainder_keeps_its_own_typed_diagnostics() {
        let remainder = RemainderBranch {
            pattern: k_rust_backend::rewrite::Pattern {
                term: Term::variable(k_rust_backend::term::Variable::new(
                    "X",
                    Sort::simple("SortS"),
                )),
                constraints: Vec::new(),
            },
            rule_ids: vec!["r".into()],
            effects: Vec::new(),
            simplifications: Vec::new(),
            indeterminate: None,
            diagnostics: vec![BackendDiagnostic::SimplificationBudgetExhausted {
                limit: 3,
                subject: BudgetSubject::Predicates,
            }],
            observations: Vec::new(),
        };
        let (candidates, remainder) = execution_candidates_output(HaltReason::Branch {
            branches: Vec::new(),
            remainder: Some(remainder),
        })
        .unwrap();
        assert!(candidates.unwrap().is_empty());
        let value = serde_json::to_value(remainder.unwrap()).unwrap();
        assert_eq!(value["ruleIds"], serde_json::json!(["r"]));
        assert_eq!(value["state"]["format"], "KORE");
        assert_eq!(
            value["diagnostics"],
            serde_json::json!([{
                "kind": "simplification-budget-exhausted",
                "limit": 3,
                "subject": "predicates"
            }])
        );
    }

    #[test]
    fn diagnostic_wire_variants_round_trip_and_reject_unknown_fields() {
        let predicate = serde_json::json!({"format":"KORE","version":1,"term":{"tag":"Top","sort":{"tag":"SortApp","name":"SortS","args":[]}}});
        let reasons = [
            serde_json::json!({"kind":"no-solver"}),
            serde_json::json!({"kind":"implication-indeterminate"}),
            serde_json::json!({"kind":"smt-unknown","reason":"timeout"}),
            serde_json::json!({"kind":"inconsistent-path-condition"}),
            serde_json::json!({"kind":"untranslatable","error":{"kind":"unsupported-predicate","predicate":"p"}}),
            serde_json::json!({"kind":"non-functional-binding"}),
        ];
        let mut variants = vec![
            serde_json::json!({"kind":"simplification-budget-exhausted","limit":3,"subject":"term"}),
            serde_json::json!({"kind":"simplification-budget-exhausted","limit":3,"subject":"predicates"}),
            serde_json::json!({"kind":"rule-condition-unsimplified","ruleId":"r","limit":3}),
            serde_json::json!({"kind":"unsupported-hook-unevaluated","hook":"H.f","reason":"no evaluator"}),
        ];
        for reason in reasons {
            variants.push(serde_json::json!({"kind":"undecided-condition","ruleId":"r","reason":reason,"predicates":[predicate]}));
            variants.push(serde_json::json!({"kind":"undecided-predicate","reason":reason,"predicate":predicate}));
        }
        for expected in variants {
            let decoded: BackendDiagnosticOutput =
                serde_json::from_value(expected.clone()).unwrap();
            assert_eq!(serde_json::to_value(decoded).unwrap(), expected);
        }
        assert!(
            serde_json::from_value::<BackendDiagnosticOutput>(serde_json::json!({
                "kind":"simplification-budget-exhausted","limit":3,"subject":"term","extra":true
            }))
            .is_err()
        );
    }

    #[test]
    fn diagnostic_predicates_use_kore_json_patterns() {
        use k_rust_backend::rule::Predicate;

        let sort = Sort::simple("SortS");
        let expected = encode_predicate(&Predicate::True, &sort).unwrap();
        let condition = diagnostic_output(
            BackendDiagnostic::UndecidedCondition {
                rule_id: "r".into(),
                reason: ConditionIndeterminacy::NoSolver,
                predicates: vec![Predicate::True],
            },
            &sort,
        )
        .unwrap();
        let predicate = diagnostic_output(
            BackendDiagnostic::UndecidedPredicate {
                predicate: Predicate::True,
                reason: ConditionIndeterminacy::NoSolver,
            },
            &sort,
        )
        .unwrap();
        assert_eq!(
            serde_json::to_value(condition).unwrap()["predicates"][0],
            expected
        );
        assert_eq!(
            serde_json::to_value(predicate).unwrap()["predicate"],
            expected
        );
        assert_eq!(expected["format"], "KORE");
        assert_eq!(expected["term"]["tag"], "Top");
    }

    #[test]
    fn instantiation_failure_preserves_rule_and_missing_variables_on_the_wire() {
        let sort = Sort::simple("SortS");
        let variable = k_rust_backend::term::Variable::new("Rule#E", sort.clone());
        let failure = indeterminate_failure_output(
            IndeterminateReason::Instantiation {
                rule_id: "heat".into(),
                missing_variables: [variable.clone()].into_iter().collect(),
            },
            &sort,
        )
        .unwrap();
        let value = serde_json::to_value(&failure).unwrap();
        assert_eq!(value["kind"], "instantiation");
        assert_eq!(value["rule"], "heat");
        assert_eq!(
            value["missingVariables"],
            serde_json::json!([encode_variable(&variable).unwrap()])
        );
        assert!(value.get("missing_variables").is_none());
        assert_typescript_variant_fields(
            "SearchFailure",
            "instantiation",
            &["rule", "missingVariables"],
        );
        assert_eq!(
            serde_json::from_value::<SearchFailureOutput>(value).unwrap(),
            failure
        );
    }

    /// Answers every condition query as undecided, cancelling the request while it answers.
    struct CancellingSolver(k_rust_backend::cancellation::CancellationToken);

    impl k_rust_backend::smt::SmtSolver for CancellingSolver {
        fn is_sat(
            &self,
            _predicates: &[k_rust_backend::rule::Predicate],
            _substitution: &Substitution,
        ) -> Result<Satisfiability, SmtError> {
            self.0.cancel();
            Ok(Satisfiability::Sat)
        }

        fn check_predicates(
            &self,
            _known: &[k_rust_backend::rule::Predicate],
            _substitution: &Substitution,
            _checked: &[k_rust_backend::rule::Predicate],
        ) -> Result<k_rust_backend::smt::Validity, SmtError> {
            self.0.cancel();
            Ok(k_rust_backend::smt::Validity::Indeterminate)
        }
    }

    #[test]
    fn search_reports_a_cancellation_observed_by_a_hook_as_cancelled_on_the_wire() {
        // Simplifying `checked(X)` asks the solver about `0 <Int X`; the solver cancels the
        // request, and the enclosing `add` hook is the first point that observes it.
        let syntax = k_rust_kore::kore::parser::parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortS{} []
                symbol pair{}(SortInt{}, SortInt{}) : SortS{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                symbol checked{}(SortInt{}) : SortInt{} [function{}(), total{}()]
                hooked-symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.lt"), smt-hook{}("<")]
                hooked-symbol add{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
                axiom{R} \implies{R}(
                    \and{R}(
                        \equals{SortBool{}, R}(
                            lt{}(\dv{SortInt{}}("0"), X:SortInt{}),
                            \dv{SortBool{}}("true")
                        ),
                        \and{R}(\in{SortInt{}, R}(X0:SortInt{}, X:SortInt{}), \top{R}())
                    ),
                    \equals{SortInt{}, R}(
                        checked{}(X0:SortInt{}),
                        \and{SortInt{}}(X:SortInt{}, \top{SortInt{}}())
                    )
                ) [label{}("checked")]
            endmodule []"#,
        )
        .unwrap();
        let definition =
            k_rust_backend::definition::BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let initial = definition
            .internalize_pattern(
                &k_rust_kore::kore::parser::parse_pattern(
                    r#"pair{}(add{}(checked{}(X:SortInt{}), \dv{SortInt{}}("1")), \dv{SortInt{}}("0"))"#,
                )
                .unwrap(),
                &[],
            )
            .unwrap();
        let token = k_rust_backend::cancellation::CancellationToken::new();
        let solver = CancellingSolver(token.clone());

        let result = token.scope(|| {
            k_rust_backend::search::search_graph_with_solver(
                &definition,
                initial,
                k_rust_backend::search::SearchOptions::default(),
                &solver,
            )
        });
        let response =
            serde_json::to_value(search_response(result, BACKEND_SCHEMA_VERSION).unwrap()).unwrap();

        assert_eq!(response["states"], serde_json::json!([]), "{response:#}");
        let incomplete = response["incomplete"].as_array().unwrap();
        assert_eq!(incomplete.len(), 1, "{response:#}");
        assert_eq!(incomplete[0]["kind"], "cancelled", "{response:#}");
    }

    /// Cancels the request during its first query and, as a solver interrupted by the
    /// cancellation does, answers that query and every later one as unknown.
    struct CancelledSolver(k_rust_backend::cancellation::CancellationToken);

    impl k_rust_backend::smt::SmtSolver for CancelledSolver {
        fn is_sat(
            &self,
            _predicates: &[k_rust_backend::rule::Predicate],
            _substitution: &Substitution,
        ) -> Result<Satisfiability, SmtError> {
            self.0.cancel();
            Ok(Satisfiability::Unknown("request cancelled".into()))
        }

        fn check_predicates(
            &self,
            _known: &[k_rust_backend::rule::Predicate],
            _substitution: &Substitution,
            _checked: &[k_rust_backend::rule::Predicate],
        ) -> Result<k_rust_backend::smt::Validity, SmtError> {
            self.0.cancel();
            Ok(k_rust_backend::smt::Validity::Unknown(
                "request cancelled".into(),
            ))
        }
    }

    #[test]
    fn search_reports_a_cancellation_observed_by_the_solver_as_cancelled_on_the_wire() {
        // `wrap(Y)` meets the condition `Y == "expected"`; the solver deciding it is the first
        // point that observes the cancellation, so the condition is undecided only because of it.
        let syntax = k_rust_kore::kore::parser::parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol wrap{}(SortS{}) : SortS{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        wrap{}(X:SortS{}),
                        \equals{SortS{}, SortS{}}(X:SortS{}, \dv{SortS{}}("expected"))
                    ),
                    \dv{SortS{}}("done")
                ) [label{}("guarded")]
            endmodule []"#,
        )
        .unwrap();
        let definition =
            k_rust_backend::definition::BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let initial = definition
            .internalize_pattern(
                &k_rust_kore::kore::parser::parse_pattern("wrap{}(Y:SortS{})").unwrap(),
                &[],
            )
            .unwrap();
        let token = k_rust_backend::cancellation::CancellationToken::new();
        let solver = CancelledSolver(token.clone());

        let result = token.scope(|| {
            k_rust_backend::search::search_graph_with_solver(
                &definition,
                initial,
                k_rust_backend::search::SearchOptions::default(),
                &solver,
            )
        });
        let response =
            serde_json::to_value(search_response(result, BACKEND_SCHEMA_VERSION).unwrap()).unwrap();

        assert_eq!(response["states"], serde_json::json!([]), "{response:#}");
        let incomplete = response["incomplete"].as_array().unwrap();
        assert_eq!(incomplete.len(), 1, "{response:#}");
        assert_eq!(incomplete[0]["kind"], "cancelled", "{response:#}");
    }

    #[test]
    fn no_interruption_signal_is_a_published_search_failure() {
        let sort = Sort::simple("SortS");
        for error in [
            SimplificationError::Cancelled,
            SimplificationError::Interrupted,
            SimplificationError::Builtin(BuiltinError::Interrupted),
        ] {
            let described = format!("{error:?}");
            let failure = simplification_failure_output(error, &sort).expect_err(&described);
            assert!(
                failure.0.contains("as a cancelled entry"),
                "{described}: {failure}"
            );
        }
    }

    #[test]
    fn interruption_kinds_are_not_search_failure_wire_kinds() {
        for failure in [
            serde_json::json!({ "kind": "cancelled" }),
            serde_json::json!({ "kind": "builtin", "error": { "kind": "interrupted" } }),
        ] {
            assert!(
                serde_json::from_value::<SearchFailureOutput>(failure.clone()).is_err(),
                "{failure}"
            );
        }
    }
}
