//! Positive-bounded adaptation of the public k-rust search facade.

use k_rust::backend::{
    BACKEND_SCHEMA_VERSION, Backend, BackendError, BindingOutput, BuiltinFailureOutput,
    EffectOutput, IncompleteSearchOutput, ObservedRequest, PathPatternSearchResponse,
    PathSearchResponse, PatternSearchResponse, ResultModalityOutput, SatisfiabilityOutput,
    SearchFailureOutput, SearchPatternRequest, SearchRequest, SearchResponse, SmtFailureOutput,
    TermPairOutput, TranslationFailureOutput,
};

use crate::ProvenanceStatus;
use crate::observation::{
    AdaptedBranch, InstalledObservationManifest, ObservationFailure, adapt_branch,
};

/// Exact solver feature/profile selected by kink-native.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SolverProfile {
    /// `k-rust` with `default-features=false`; `NoSolver`; no Z3 inference.
    StructuredNoZ3Inference,
    /// A later profile that must be independently qualified before solver-relative evidence.
    QualifiedZ3InferenceRequired,
}

impl SolverProfile {
    /// Exact feature spelling bound by this adapter.
    #[must_use]
    pub const fn feature_profile(self) -> &'static str {
        match self {
            Self::StructuredNoZ3Inference => {
                "k-rust=0.4.0,default-features=false,no-z3-inference,solver=NoSolver"
            }
            Self::QualifiedZ3InferenceRequired => {
                "later-required:k-rust=0.4.0,z3-inference,solver-profile-and-conformance-receipt"
            }
        }
    }
}

/// Positive existence or explicitly not-proven absence. Exhaustive absence is unrepresentable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PositiveBoundedOutcome {
    Positive,
    UnknownNotProven,
}

/// Adapter-wide authority boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AdapterAuthority {
    provenance: ProvenanceStatus,
    native_authority: bool,
    exhaustive_absence: bool,
    production_receipt: bool,
}

impl AdapterAuthority {
    const NONE: Self = Self {
        provenance: ProvenanceStatus::SidecarOnlyMissingBridge,
        native_authority: false,
        exhaustive_absence: false,
        production_receipt: false,
    };

    #[must_use]
    pub const fn provenance(self) -> ProvenanceStatus {
        self.provenance
    }

    #[must_use]
    pub const fn grants_native_authority(self) -> bool {
        self.native_authority
    }

    #[must_use]
    pub const fn proves_exhaustive_absence(self) -> bool {
        self.exhaustive_absence
    }

    #[must_use]
    pub const fn has_production_receipt(self) -> bool {
        self.production_receipt
    }
}

/// A state-set response preserving facade order and branch-local structure.
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedStateSearch {
    pub outcome: PositiveBoundedOutcome,
    pub states: Vec<AdaptedBranch>,
    pub effects: Vec<EffectOutput>,
    pub incomplete: Vec<AdaptedIncomplete>,
    pub authority: AdapterAuthority,
}

/// A path-set response preserving path witness order.
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedPathSearch {
    pub outcome: PositiveBoundedOutcome,
    pub witnesses: Vec<AdaptedBranch>,
    pub effects: Vec<EffectOutput>,
    pub incomplete: Vec<AdaptedIncomplete>,
    pub authority: AdapterAuthority,
}

/// One pattern match with exact binding and residual-constraint order.
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedPatternMatch {
    pub bindings: Vec<BindingOutput>,
    pub constraints: Vec<serde_json::Value>,
    pub branch: AdaptedBranch,
}

/// A pattern state-set response.
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedPatternSearch {
    pub outcome: PositiveBoundedOutcome,
    pub matches: Vec<AdaptedPatternMatch>,
    pub effects: Vec<EffectOutput>,
    pub incomplete: Vec<AdaptedIncomplete>,
    pub authority: AdapterAuthority,
}

/// A pattern path-set response.
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedPatternPathSearch {
    pub outcome: PositiveBoundedOutcome,
    pub matches: Vec<AdaptedPatternMatch>,
    pub effects: Vec<EffectOutput>,
    pub incomplete: Vec<AdaptedIncomplete>,
    pub authority: AdapterAuthority,
}

/// Decision-bearing class for each of the eight public incomplete variants.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IncompleteClass {
    ResultBound,
    DepthBound,
    BreadthBound,
    Indeterminate,
    Cancelled,
    Simplification,
    MatchIndeterminate,
    SolverDeferred,
}

/// Closed adaptation of all public `IncompleteSearchOutput` variants.
#[derive(Clone, Debug, PartialEq)]
pub enum AdaptedIncomplete {
    ResultBound,
    DepthBound {
        state: AdaptedBranch,
    },
    BreadthBound {
        states: Vec<AdaptedBranch>,
    },
    Indeterminate {
        state: AdaptedBranch,
        reason: SearchFailureOutput,
        class: IncompleteClass,
    },
    Cancelled {
        state: AdaptedBranch,
    },
    Simplification {
        state: AdaptedBranch,
        error: SearchFailureOutput,
        class: IncompleteClass,
    },
    MatchIndeterminate {
        state: AdaptedBranch,
        bindings: Vec<BindingOutput>,
        remainder: Vec<TermPairOutput>,
    },
    SolverDeferred {
        state: AdaptedBranch,
        error: SmtFailureOutput,
        required_profile: SolverProfile,
    },
}

impl AdaptedIncomplete {
    /// Stable absence/stop classification.
    #[must_use]
    pub const fn class(&self) -> IncompleteClass {
        match self {
            Self::ResultBound => IncompleteClass::ResultBound,
            Self::DepthBound { .. } => IncompleteClass::DepthBound,
            Self::BreadthBound { .. } => IncompleteClass::BreadthBound,
            Self::Indeterminate { class, .. } | Self::Simplification { class, .. } => *class,
            Self::Cancelled { .. } => IncompleteClass::Cancelled,
            Self::MatchIndeterminate { .. } => IncompleteClass::MatchIndeterminate,
            Self::SolverDeferred { .. } => IncompleteClass::SolverDeferred,
        }
    }
}

/// Exact-profile observed-search adapter.
#[derive(Clone, Debug, PartialEq)]
pub struct SearchAdapter {
    manifest: InstalledObservationManifest,
    profile: SolverProfile,
}

impl SearchAdapter {
    /// Binds the only locally qualified solver feature/profile.
    pub fn new(
        profile: SolverProfile,
        manifest: InstalledObservationManifest,
    ) -> Result<Self, SearchAdapterFailure> {
        if profile != SolverProfile::StructuredNoZ3Inference {
            return Err(SearchAdapterFailure::SolverProfileMismatch {
                expected: SolverProfile::StructuredNoZ3Inference,
                actual: profile,
            });
        }
        Ok(Self { manifest, profile })
    }

    /// Executes public observed state search and publishes an adapter DTO only on success.
    pub fn search(
        &self,
        backend: &mut Backend,
        request: SearchRequest,
    ) -> Result<AdaptedStateSearch, SearchAdapterFailure> {
        let response = backend
            .search_observed(ObservedRequest {
                request,
                rules: Some(self.manifest.backend_rule_ids()),
            })
            .map_err(SearchAdapterFailure::backend)?;
        adapt_state_response(&self.manifest, response)
    }

    /// Executes public observed path search.
    pub fn search_paths(
        &self,
        backend: &mut Backend,
        request: SearchRequest,
    ) -> Result<AdaptedPathSearch, SearchAdapterFailure> {
        let response = backend
            .search_paths_observed(ObservedRequest {
                request,
                rules: Some(self.manifest.backend_rule_ids()),
            })
            .map_err(SearchAdapterFailure::backend)?;
        adapt_path_response(&self.manifest, response)
    }

    /// Executes public observed pattern state search.
    pub fn search_pattern(
        &self,
        backend: &mut Backend,
        request: SearchPatternRequest,
    ) -> Result<AdaptedPatternSearch, SearchAdapterFailure> {
        let response = backend
            .search_pattern_observed(ObservedRequest {
                request,
                rules: Some(self.manifest.backend_rule_ids()),
            })
            .map_err(SearchAdapterFailure::backend)?;
        adapt_pattern_response(&self.manifest, response)
    }

    /// Executes public observed pattern path search.
    pub fn search_pattern_paths(
        &self,
        backend: &mut Backend,
        request: SearchPatternRequest,
    ) -> Result<AdaptedPatternPathSearch, SearchAdapterFailure> {
        let response = backend
            .search_pattern_paths_observed(ObservedRequest {
                request,
                rules: Some(self.manifest.backend_rule_ids()),
            })
            .map_err(SearchAdapterFailure::backend)?;
        adapt_pattern_path_response(&self.manifest, response)
    }

    /// Exact selected profile.
    #[must_use]
    pub const fn solver_profile(&self) -> SolverProfile {
        self.profile
    }
}

fn outcome(count: usize) -> PositiveBoundedOutcome {
    if count == 0 {
        PositiveBoundedOutcome::UnknownNotProven
    } else {
        PositiveBoundedOutcome::Positive
    }
}

fn check_header(
    schema_version: u32,
    actual: ResultModalityOutput,
    expected: ResultModalityOutput,
) -> Result<(), SearchAdapterFailure> {
    if schema_version != BACKEND_SCHEMA_VERSION {
        return Err(SearchAdapterFailure::UnsupportedSchema(schema_version));
    }
    if actual != expected {
        return Err(SearchAdapterFailure::WrongModality { expected, actual });
    }
    Ok(())
}

fn adapt_state_response(
    manifest: &InstalledObservationManifest,
    response: SearchResponse,
) -> Result<AdaptedStateSearch, SearchAdapterFailure> {
    inventory_effects(&response.effects);
    check_header(
        response.schema_version,
        response.modality,
        ResultModalityOutput::StateSet,
    )?;
    let states = response
        .states
        .into_iter()
        .map(|state| {
            adapt_branch(
                Some(manifest),
                state.branch,
                state.state,
                state.depth,
                state.trace,
                state.observations,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let incomplete = adapt_incomplete(manifest, response.incomplete)?;
    Ok(AdaptedStateSearch {
        outcome: outcome(states.len()),
        states,
        effects: response.effects,
        incomplete,
        authority: AdapterAuthority::NONE,
    })
}

fn adapt_path_response(
    manifest: &InstalledObservationManifest,
    response: PathSearchResponse,
) -> Result<AdaptedPathSearch, SearchAdapterFailure> {
    inventory_effects(&response.effects);
    check_header(
        response.schema_version,
        response.modality,
        ResultModalityOutput::PathSet,
    )?;
    let witnesses = response
        .witnesses
        .into_iter()
        .map(|witness| {
            adapt_branch(
                Some(manifest),
                witness.id,
                witness.state,
                witness.depth,
                witness.trace,
                witness.observations,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let incomplete = adapt_incomplete(manifest, response.incomplete)?;
    Ok(AdaptedPathSearch {
        outcome: outcome(witnesses.len()),
        witnesses,
        effects: response.effects,
        incomplete,
        authority: AdapterAuthority::NONE,
    })
}

fn adapt_pattern_response(
    manifest: &InstalledObservationManifest,
    response: PatternSearchResponse,
) -> Result<AdaptedPatternSearch, SearchAdapterFailure> {
    inventory_effects(&response.effects);
    check_header(
        response.schema_version,
        response.modality,
        ResultModalityOutput::StateSet,
    )?;
    let matches = response
        .matches
        .into_iter()
        .map(|found| {
            Ok(AdaptedPatternMatch {
                bindings: found.bindings,
                constraints: found.constraints,
                branch: adapt_branch(
                    Some(manifest),
                    found.state.branch,
                    found.state.state,
                    found.state.depth,
                    found.state.trace,
                    found.state.observations,
                )?,
            })
        })
        .collect::<Result<Vec<_>, ObservationFailure>>()?;
    let incomplete = adapt_incomplete(manifest, response.incomplete)?;
    Ok(AdaptedPatternSearch {
        outcome: outcome(matches.len()),
        matches,
        effects: response.effects,
        incomplete,
        authority: AdapterAuthority::NONE,
    })
}

fn adapt_pattern_path_response(
    manifest: &InstalledObservationManifest,
    response: PathPatternSearchResponse,
) -> Result<AdaptedPatternPathSearch, SearchAdapterFailure> {
    inventory_effects(&response.effects);
    check_header(
        response.schema_version,
        response.modality,
        ResultModalityOutput::PathSet,
    )?;
    let matches = response
        .matches
        .into_iter()
        .map(|found| {
            Ok(AdaptedPatternMatch {
                bindings: found.bindings,
                constraints: found.constraints,
                branch: adapt_branch(
                    Some(manifest),
                    found.witness.id,
                    found.witness.state,
                    found.witness.depth,
                    found.witness.trace,
                    found.witness.observations,
                )?,
            })
        })
        .collect::<Result<Vec<_>, ObservationFailure>>()?;
    let incomplete = adapt_incomplete(manifest, response.incomplete)?;
    Ok(AdaptedPatternPathSearch {
        outcome: outcome(matches.len()),
        matches,
        effects: response.effects,
        incomplete,
        authority: AdapterAuthority::NONE,
    })
}

fn adapt_incomplete(
    manifest: &InstalledObservationManifest,
    items: Vec<IncompleteSearchOutput>,
) -> Result<Vec<AdaptedIncomplete>, ObservationFailure> {
    items
        .into_iter()
        .map(|item| {
            Ok(match item {
                IncompleteSearchOutput::ResultBound => AdaptedIncomplete::ResultBound,
                IncompleteSearchOutput::DepthBound { state } => AdaptedIncomplete::DepthBound {
                    state: adapt_search_state(manifest, state)?,
                },
                IncompleteSearchOutput::BreadthBound { states } => {
                    AdaptedIncomplete::BreadthBound {
                        states: states
                            .into_iter()
                            .map(|state| adapt_search_state(manifest, state))
                            .collect::<Result<_, _>>()?,
                    }
                }
                IncompleteSearchOutput::Indeterminate { state, reason } => {
                    let class = failure_class(&reason);
                    AdaptedIncomplete::Indeterminate {
                        state: adapt_search_state(manifest, state)?,
                        reason,
                        class,
                    }
                }
                IncompleteSearchOutput::Cancelled { state } => AdaptedIncomplete::Cancelled {
                    state: adapt_search_state(manifest, state)?,
                },
                IncompleteSearchOutput::Simplification { state, error } => {
                    let class = failure_class(&error);
                    AdaptedIncomplete::Simplification {
                        state: adapt_search_state(manifest, state)?,
                        error,
                        class,
                    }
                }
                IncompleteSearchOutput::Match {
                    state,
                    bindings,
                    remainder,
                } => AdaptedIncomplete::MatchIndeterminate {
                    state: adapt_search_state(manifest, state)?,
                    bindings,
                    remainder,
                },
                IncompleteSearchOutput::Smt { state, error } => {
                    inventory_smt(&error);
                    AdaptedIncomplete::SolverDeferred {
                        state: adapt_search_state(manifest, state)?,
                        error,
                        required_profile: SolverProfile::QualifiedZ3InferenceRequired,
                    }
                }
            })
        })
        .collect()
}

fn adapt_search_state(
    manifest: &InstalledObservationManifest,
    state: k_rust::backend::SearchStateOutput,
) -> Result<AdaptedBranch, ObservationFailure> {
    adapt_branch(
        Some(manifest),
        state.branch,
        state.state,
        state.depth,
        state.trace,
        state.observations,
    )
}

fn failure_class(failure: &SearchFailureOutput) -> IncompleteClass {
    match failure {
        SearchFailureOutput::Cancelled => IncompleteClass::Cancelled,
        SearchFailureOutput::Smt { error, .. }
        | SearchFailureOutput::SmtPredicate { error, .. } => {
            inventory_smt(error);
            IncompleteClass::SolverDeferred
        }
        SearchFailureOutput::Remainder { satisfiability, .. } => {
            inventory_satisfiability(satisfiability);
            IncompleteClass::SolverDeferred
        }
        SearchFailureOutput::InconsistentGroundTruth { .. } => IncompleteClass::SolverDeferred,
        SearchFailureOutput::Builtin { error } => {
            inventory_builtin(error);
            IncompleteClass::Indeterminate
        }
        SearchFailureOutput::ConflictingResults { .. }
        | SearchFailureOutput::IterationLimit { .. }
        | SearchFailureOutput::PredicateIterationLimit { .. }
        | SearchFailureOutput::InvalidBuiltinResultSymbol { .. }
        | SearchFailureOutput::Match { .. }
        | SearchFailureOutput::Requires { .. }
        | SearchFailureOutput::Concreteness { .. }
        | SearchFailureOutput::SurvivingMacroOrAlias { .. }
        | SearchFailureOutput::UnsupportedHook { .. }
        | SearchFailureOutput::Instantiation { .. } => IncompleteClass::Indeterminate,
    }
}

fn inventory_satisfiability(value: &SatisfiabilityOutput) {
    match value {
        SatisfiabilityOutput::Sat | SatisfiabilityOutput::Unsat => {}
        SatisfiabilityOutput::Unknown { .. } => {}
        SatisfiabilityOutput::Error { error } => inventory_smt(error),
    }
}

fn inventory_smt(value: &SmtFailureOutput) {
    match value {
        SmtFailureOutput::Translation { error } => inventory_translation(error),
        SmtFailureOutput::Unavailable
        | SmtFailureOutput::InconsistentPrelude
        | SmtFailureOutput::UnknownPrelude { .. }
        | SmtFailureOutput::Unknown { .. }
        | SmtFailureOutput::InconsistentGroundTruth
        | SmtFailureOutput::MissingModel
        | SmtFailureOutput::MissingModelValue { .. }
        | SmtFailureOutput::InvalidModelValue { .. } => {}
    }
}

fn inventory_translation(value: &TranslationFailureOutput) {
    match value {
        TranslationFailureOutput::NonBooleanAnd { .. }
        | TranslationFailureOutput::PlaceholderOutOfBounds { .. }
        | TranslationFailureOutput::UnsupportedPredicate { .. }
        | TranslationFailureOutput::ParametricSort { .. }
        | TranslationFailureOutput::SmtLemmaSurplusMappings { .. }
        | TranslationFailureOutput::SmtLemmaSurplusPredicates { .. }
        | TranslationFailureOutput::MissingSmtLemmaVariable { .. } => {}
    }
}

fn inventory_builtin(value: &BuiltinFailureOutput) {
    match value {
        BuiltinFailureOutput::Interrupted
        | BuiltinFailureOutput::WrongArity { .. }
        | BuiltinFailureOutput::UnexpectedSort { .. }
        | BuiltinFailureOutput::AlternativeSortsDiffer { .. }
        | BuiltinFailureOutput::IncompatibleMapSorts { .. }
        | BuiltinFailureOutput::InvalidFloatToken { .. }
        | BuiltinFailureOutput::UnsupportedFloatFormat { .. }
        | BuiltinFailureOutput::UnsupportedFloatFormatParameters { .. }
        | BuiltinFailureOutput::MismatchedFloatFormats { .. } => {}
    }
}

fn inventory_effects(effects: &[EffectOutput]) {
    for effect in effects {
        match effect {
            EffectOutput::UserLog { .. } => {}
        }
    }
}

/// Search adapter failure. No adapted response is returned or published.
#[derive(Clone, Debug, PartialEq)]
pub enum SearchAdapterFailure {
    SolverProfileMismatch {
        expected: SolverProfile,
        actual: SolverProfile,
    },
    BackendRejected(String),
    UnsupportedSchema(u32),
    WrongModality {
        expected: ResultModalityOutput,
        actual: ResultModalityOutput,
    },
    Observation(ObservationFailure),
}

impl SearchAdapterFailure {
    fn backend(error: BackendError) -> Self {
        Self::BackendRejected(error.to_string())
    }
}

impl From<ObservationFailure> for SearchAdapterFailure {
    fn from(value: ObservationFailure) -> Self {
        Self::Observation(value)
    }
}

/// Replayable adapted response union.
#[derive(Clone, Debug, PartialEq)]
pub enum ReplaySearch {
    State(AdaptedStateSearch),
    Path(AdaptedPathSearch),
    Pattern(AdaptedPatternSearch),
    PatternPath(AdaptedPatternPathSearch),
}

/// Deterministic replay agreement. It grants no publication or authority.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReplayAgreement;

/// Compares only adapted branch/witness/event structures. Mismatch returns no result payload.
pub fn compare_replay(
    expected: &ReplaySearch,
    actual: &ReplaySearch,
) -> Result<ReplayAgreement, ReplayMismatch> {
    if expected == actual {
        Ok(ReplayAgreement)
    } else {
        Err(ReplayMismatch)
    }
}

/// Closed replay mismatch with no publishable candidate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReplayMismatch;

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::backend::{
        BackendOptions, PathSearchMatchOutput, PathWitnessOutput, SearchMatchOutput,
        SearchStateOutput, TransitionIdOutput,
    };
    use k_rust::kore::{json as kore_json, parser::parse_pattern};
    use serde_json::{Value, json};

    use crate::observation::{NativeEvent, RuleObservationSpec};

    const DEFINITION: &str = r#"[]
module HIDDEN
  sort SortHidden{} []
  symbol hidden{}() : SortHidden{} [constructor{}()]
  axiom{} \rewrites{SortHidden{}}(
    \and{SortHidden{}}(hidden{}(), \top{SortHidden{}}()),
    \and{SortHidden{}}(hidden{}(), \top{SortHidden{}}())
  )
    [label{}("hidden-label"), UNIQUE'Unds'ID{}("hidden-id")]
endmodule []
module MAIN
  sort SortS{} []
  symbol a{}() : SortS{} [constructor{}()]
  symbol b{}() : SortS{} [constructor{}()]
  symbol c{}() : SortS{} [constructor{}()]
  symbol d{}() : SortS{} [constructor{}()]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(a{}(), \top{SortS{}}()),
    \and{SortS{}}(b{}(), \top{SortS{}}())
  )
    [label{}("step"), UNIQUE'Unds'ID{}("step-id")]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(c{}(), \top{SortS{}}()),
    \and{SortS{}}(d{}(), \top{SortS{}}())
  )
    [label{}("ambiguous-one"), UNIQUE'Unds'ID{}("duplicate-id")]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(d{}(), \top{SortS{}}()),
    \and{SortS{}}(c{}(), \top{SortS{}}())
  )
    [label{}("ambiguous-two"), UNIQUE'Unds'ID{}("duplicate-id")]
endmodule []"#;

    fn kore(source: &str) -> Value {
        kore_json::to_value(&parse_pattern(source).unwrap()).unwrap()
    }

    fn empty_manifest() -> InstalledObservationManifest {
        InstalledObservationManifest::install(Vec::new()).unwrap()
    }

    fn observed_manifest(identity: &str) -> InstalledObservationManifest {
        InstalledObservationManifest::install(vec![RuleObservationSpec {
            label: if identity == "step-id" {
                "step".into()
            } else {
                identity.into()
            },
            backend_rule_identity: identity.into(),
            emit_rule_applied: true,
            domain_events: Vec::new(),
        }])
        .unwrap()
    }

    fn state(marker: i64) -> SearchStateOutput {
        SearchStateOutput {
            state: json!({ "marker": marker }),
            depth: marker.unsigned_abs(),
            trace: Vec::new(),
            branch: vec![TransitionIdOutput {
                rule: format!("rule-{marker}"),
                target: format!("target-{marker}"),
            }],
            observations: Vec::new(),
        }
    }

    fn state_response(
        states: Vec<SearchStateOutput>,
        incomplete: Vec<IncompleteSearchOutput>,
    ) -> SearchResponse {
        SearchResponse {
            schema_version: BACKEND_SCHEMA_VERSION,
            modality: ResultModalityOutput::StateSet,
            states,
            effects: Vec::new(),
            incomplete,
        }
    }

    #[test]
    fn exact_no_z3_profile_is_required() {
        let mismatch = SearchAdapter::new(
            SolverProfile::QualifiedZ3InferenceRequired,
            empty_manifest(),
        );
        assert!(matches!(
            mismatch,
            Err(SearchAdapterFailure::SolverProfileMismatch { .. })
        ));
        let adapter =
            SearchAdapter::new(SolverProfile::StructuredNoZ3Inference, empty_manifest()).unwrap();
        assert_eq!(
            adapter.solver_profile().feature_profile(),
            "k-rust=0.4.0,default-features=false,no-z3-inference,solver=NoSolver"
        );
    }

    #[test]
    fn public_facade_rejects_unknown_and_invisible_selectors_before_a_result() {
        let request = SearchRequest {
            state: kore("a{}()"),
            ..SearchRequest::default()
        };
        for identity in ["unknown-id", "hidden-id"] {
            let mut backend = Backend::new(DEFINITION, "MAIN", BackendOptions::default()).unwrap();
            let adapter = SearchAdapter::new(
                SolverProfile::StructuredNoZ3Inference,
                observed_manifest(identity),
            )
            .unwrap();
            let error = adapter.search(&mut backend, request.clone()).unwrap_err();
            assert!(matches!(error, SearchAdapterFailure::BackendRejected(_)));
        }
    }

    #[test]
    fn public_facade_rejects_an_ambiguous_backend_identity_before_a_result() {
        let mut backend = Backend::new(DEFINITION, "MAIN", BackendOptions::default()).unwrap();
        let adapter = SearchAdapter::new(
            SolverProfile::StructuredNoZ3Inference,
            InstalledObservationManifest::install(vec![RuleObservationSpec {
                label: "ambiguous-one".into(),
                backend_rule_identity: "duplicate-id".into(),
                emit_rule_applied: true,
                domain_events: Vec::new(),
            }])
            .unwrap(),
        )
        .unwrap();
        let error = adapter
            .search(
                &mut backend,
                SearchRequest {
                    state: kore("a{}()"),
                    ..SearchRequest::default()
                },
            )
            .unwrap_err();
        assert!(matches!(error, SearchAdapterFailure::BackendRejected(_)));
    }

    #[test]
    fn public_facade_commits_only_selected_branch_local_observations() {
        let mut backend = Backend::new(DEFINITION, "MAIN", BackendOptions::default()).unwrap();
        let adapter = SearchAdapter::new(
            SolverProfile::StructuredNoZ3Inference,
            observed_manifest("step-id"),
        )
        .unwrap();
        let result = adapter
            .search(
                &mut backend,
                SearchRequest {
                    state: kore("a{}()"),
                    ..SearchRequest::default()
                },
            )
            .unwrap();
        assert_eq!(result.outcome, PositiveBoundedOutcome::Positive);
        assert!(matches!(
            result.states[0].events.as_slice(),
            [NativeEvent::RuleApplied(event)] if event.rule_label == "step"
        ));
    }

    /// How an O1 selection row must end: installed with this many committed events, refused
    /// by local installation, or refused by the public facade before any result.
    #[derive(Debug)]
    enum SelectionExpectation {
        Committed(usize),
        InstallRejected(ObservationFailure),
        BackendRejected,
    }

    #[test]
    fn selection_rows_over_a_real_definition_install_atomically() {
        use SelectionExpectation::{BackendRejected, Committed, InstallRejected};
        // Each selector is a (label, backend rule identity) pair.
        type Selectors = &'static [(&'static str, &'static str)];
        let rows: [(&str, Selectors, SelectionExpectation); 5] = [
            (
                "exact-identity-selects-one-rule",
                &[("step", "step-id")],
                Committed(1),
            ),
            (
                "identity-selecting-no-rule-is-a-cardinality-mismatch",
                &[("missing", "unknown-id")],
                BackendRejected,
            ),
            (
                "identity-selecting-two-rules-is-a-cardinality-mismatch",
                &[("ambiguous-one", "duplicate-id")],
                BackendRejected,
            ),
            (
                "stale-allowlist-member-rejects-the-whole-manifest",
                &[("step", "step-id"), ("missing", "unknown-id")],
                BackendRejected,
            ),
            (
                "two-selectors-for-one-site-are-a-duplicate-site",
                &[("step", "step-id"), ("step-alias", "step-id")],
                InstallRejected(ObservationFailure::DuplicateRuleIdentity("step-id".into())),
            ),
        ];
        for (id, selectors, expected) in rows {
            let specs = selectors
                .iter()
                .map(|(label, identity)| RuleObservationSpec {
                    label: (*label).into(),
                    backend_rule_identity: (*identity).into(),
                    emit_rule_applied: true,
                    domain_events: Vec::new(),
                })
                .collect();
            let manifest = match (InstalledObservationManifest::install(specs), &expected) {
                (Err(failure), InstallRejected(kind)) => {
                    assert_eq!(&failure, kind, "{id}");
                    continue;
                }
                (Ok(manifest), Committed(_) | BackendRejected) => manifest,
                (actual, _) => panic!("{id}: expected {expected:?}, installed {actual:?}"),
            };
            let mut backend = Backend::new(DEFINITION, "MAIN", BackendOptions::default()).unwrap();
            let adapter =
                SearchAdapter::new(SolverProfile::StructuredNoZ3Inference, manifest).unwrap();
            let result = adapter.search(
                &mut backend,
                SearchRequest {
                    state: kore("a{}()"),
                    ..SearchRequest::default()
                },
            );
            match (result, expected) {
                (Ok(result), Committed(count)) => {
                    let events = result
                        .states
                        .iter()
                        .map(|state| state.events.len())
                        .sum::<usize>();
                    assert_eq!(events, count, "{id}");
                }
                (Err(SearchAdapterFailure::BackendRejected(_)), BackendRejected) => {}
                (actual, expected) => panic!("{id}: expected {expected:?}, got {actual:?}"),
            }
        }
    }

    #[test]
    fn erasing_observation_preserves_the_baseline_result() {
        // (id, depth bound). The bounded row keeps its bound as an explicit incomplete item.
        let rows = [
            ("observer-erasure-is-identity", None),
            ("bounded-erasure-is-identity", Some(0)),
        ];
        for (id, max_depth) in rows {
            let request = SearchRequest {
                state: kore("a{}()"),
                max_depth,
                ..SearchRequest::default()
            };
            let mut backend = Backend::new(DEFINITION, "MAIN", BackendOptions::default()).unwrap();
            let baseline =
                adapt_state_response(&empty_manifest(), backend.search(request.clone()).unwrap())
                    .unwrap();
            let observed = SearchAdapter::new(
                SolverProfile::StructuredNoZ3Inference,
                observed_manifest("step-id"),
            )
            .unwrap()
            .search(&mut backend, request)
            .unwrap();
            // The unobserved facade reports no branch identities, so erasure is compared on
            // the semantic content: final state, depth and rule trace.
            let semantic = |states: &[AdaptedBranch]| {
                states
                    .iter()
                    .map(|state| {
                        let erased = state.erase_observations();
                        (erased.state, erased.depth, erased.trace)
                    })
                    .collect::<Vec<_>>()
            };
            assert_eq!(
                semantic(&observed.states),
                semantic(&baseline.states),
                "{id}"
            );
            assert_eq!(observed.outcome, baseline.outcome, "{id}");
            let classes = |search: &AdaptedStateSearch| {
                search
                    .incomplete
                    .iter()
                    .map(AdaptedIncomplete::class)
                    .collect::<Vec<_>>()
            };
            assert_eq!(classes(&observed), classes(&baseline), "{id}");
            assert_eq!(
                classes(&observed).contains(&IncompleteClass::DepthBound),
                max_depth.is_some(),
                "{id}"
            );
            assert!(!observed.authority.proves_exhaustive_absence(), "{id}");
        }
    }

    #[test]
    fn all_eight_incomplete_variants_are_closed_and_ordered() {
        let base = state(1);
        let items = vec![
            IncompleteSearchOutput::ResultBound,
            IncompleteSearchOutput::DepthBound {
                state: base.clone(),
            },
            IncompleteSearchOutput::BreadthBound {
                states: vec![base.clone(), state(2)],
            },
            IncompleteSearchOutput::Indeterminate {
                state: base.clone(),
                reason: SearchFailureOutput::Requires {
                    rule: "r".into(),
                    predicates: vec![json!(true)],
                },
            },
            IncompleteSearchOutput::Cancelled {
                state: base.clone(),
            },
            IncompleteSearchOutput::Simplification {
                state: base.clone(),
                error: SearchFailureOutput::IterationLimit {
                    limit: 4,
                    term: Some(json!("term")),
                },
            },
            IncompleteSearchOutput::Match {
                state: base.clone(),
                bindings: Vec::new(),
                remainder: Vec::new(),
            },
            IncompleteSearchOutput::Smt {
                state: base,
                error: SmtFailureOutput::Unavailable,
            },
        ];
        let result =
            adapt_state_response(&empty_manifest(), state_response(Vec::new(), items)).unwrap();
        assert_eq!(result.outcome, PositiveBoundedOutcome::UnknownNotProven);
        assert_eq!(
            result
                .incomplete
                .iter()
                .map(AdaptedIncomplete::class)
                .collect::<Vec<_>>(),
            [
                IncompleteClass::ResultBound,
                IncompleteClass::DepthBound,
                IncompleteClass::BreadthBound,
                IncompleteClass::Indeterminate,
                IncompleteClass::Cancelled,
                IncompleteClass::Indeterminate,
                IncompleteClass::MatchIndeterminate,
                IncompleteClass::SolverDeferred,
            ]
        );
    }

    #[test]
    fn result_bound_and_empty_success_are_always_unknown() {
        for incomplete in [Vec::new(), vec![IncompleteSearchOutput::ResultBound]] {
            let result =
                adapt_state_response(&empty_manifest(), state_response(Vec::new(), incomplete))
                    .unwrap();
            assert_eq!(result.outcome, PositiveBoundedOutcome::UnknownNotProven);
            assert!(!result.authority.proves_exhaustive_absence());
        }
    }

    #[test]
    fn positive_witness_survives_a_truncated_sibling() {
        let result = adapt_state_response(
            &empty_manifest(),
            state_response(
                vec![state(7)],
                vec![IncompleteSearchOutput::BreadthBound {
                    states: vec![state(8)],
                }],
            ),
        )
        .unwrap();
        assert_eq!(result.outcome, PositiveBoundedOutcome::Positive);
        assert_eq!(result.states[0].state, json!({ "marker": 7 }));
        assert_eq!(result.incomplete[0].class(), IncompleteClass::BreadthBound);
    }

    #[test]
    fn solver_failures_defer_to_the_exact_later_profile() {
        let result = adapt_state_response(
            &empty_manifest(),
            state_response(
                Vec::new(),
                vec![IncompleteSearchOutput::Smt {
                    state: state(1),
                    error: SmtFailureOutput::Unknown {
                        reason: "solver said unknown".into(),
                    },
                }],
            ),
        )
        .unwrap();
        assert!(matches!(
            &result.incomplete[0],
            AdaptedIncomplete::SolverDeferred {
                required_profile: SolverProfile::QualifiedZ3InferenceRequired,
                ..
            }
        ));
    }

    #[test]
    fn state_path_pattern_and_pattern_path_results_preserve_source_order() {
        let manifest = empty_manifest();
        let state_result = adapt_state_response(
            &manifest,
            state_response(vec![state(2), state(1)], Vec::new()),
        )
        .unwrap();
        assert_eq!(state_result.states[0].state, json!({ "marker": 2 }));

        let witness = |marker| PathWitnessOutput {
            id: state(marker).branch,
            state: json!({ "marker": marker }),
            depth: 1,
            trace: Vec::new(),
            observations: Vec::new(),
        };
        let path_result = adapt_path_response(
            &manifest,
            PathSearchResponse {
                schema_version: BACKEND_SCHEMA_VERSION,
                modality: ResultModalityOutput::PathSet,
                witnesses: vec![witness(2), witness(1)],
                effects: Vec::new(),
                incomplete: Vec::new(),
            },
        )
        .unwrap();
        assert_eq!(path_result.witnesses[0].state, json!({ "marker": 2 }));

        let pattern_result = adapt_pattern_response(
            &manifest,
            PatternSearchResponse {
                schema_version: BACKEND_SCHEMA_VERSION,
                modality: ResultModalityOutput::StateSet,
                matches: vec![SearchMatchOutput {
                    bindings: Vec::new(),
                    constraints: vec![json!("constraint")],
                    state: state(2),
                }],
                effects: Vec::new(),
                incomplete: Vec::new(),
            },
        )
        .unwrap();
        assert_eq!(pattern_result.outcome, PositiveBoundedOutcome::Positive);
        assert_eq!(pattern_result.matches[0].constraints, [json!("constraint")]);

        let pattern_path_result = adapt_pattern_path_response(
            &manifest,
            PathPatternSearchResponse {
                schema_version: BACKEND_SCHEMA_VERSION,
                modality: ResultModalityOutput::PathSet,
                matches: vec![PathSearchMatchOutput {
                    bindings: Vec::new(),
                    constraints: Vec::new(),
                    witness: witness(3),
                }],
                effects: Vec::new(),
                incomplete: Vec::new(),
            },
        )
        .unwrap();
        assert_eq!(
            pattern_path_result.matches[0].branch.state,
            json!({ "marker": 3 })
        );
    }

    #[test]
    fn replay_equality_accepts_and_mismatch_publishes_nothing() {
        let result = ReplaySearch::State(
            adapt_state_response(
                &empty_manifest(),
                state_response(vec![state(1)], Vec::new()),
            )
            .unwrap(),
        );
        assert_eq!(compare_replay(&result, &result), Ok(ReplayAgreement));
        let other = ReplaySearch::State(
            adapt_state_response(
                &empty_manifest(),
                state_response(vec![state(2)], Vec::new()),
            )
            .unwrap(),
        );
        assert_eq!(compare_replay(&result, &other), Err(ReplayMismatch));
    }

    #[test]
    fn no_result_promotes_authority_or_provenance() {
        let result = adapt_state_response(
            &empty_manifest(),
            state_response(vec![state(1)], Vec::new()),
        )
        .unwrap();
        assert_eq!(
            result.authority.provenance(),
            ProvenanceStatus::SidecarOnlyMissingBridge
        );
        assert!(!result.authority.grants_native_authority());
        assert!(!result.authority.has_production_receipt());
        assert!(!result.authority.proves_exhaustive_absence());
    }
}
