//! Existential adaptation of the public k-rust search facade.
//!
//! Every response is read against its [`QueryShape`]. A response can witness members of the
//! requested result set; it can never show that the set is complete or empty. k-rust has no
//! exhaustion record (`upstream/k-rust.toml` `search-completeness`), and an empty upstream
//! incomplete list is not evidence of exhaustion: a `Final` search whose result bound is filled
//! by a depth-bounded frontier state reports no incomplete item at all. Therefore no adapter
//! response may map to `kink_patch::Completeness::CompleteFinite` until upstream provides an
//! exhaustion record. A bridge maps a response to `Incomplete` when its frontier or incomplete
//! list is non-empty, and to `Unknown` otherwise.

use k_rust::backend::{
    BACKEND_SCHEMA_VERSION, Backend, BackendError, BindingOutput, BuiltinFailureOutput,
    EffectOutput, IncompleteSearchOutput, ObservedRequest, PathPatternSearchResponse,
    PathSearchResponse, PatternSearchResponse, ResultModalityOutput, SatisfiabilityOutput,
    SearchFailureOutput, SearchPatternRequest, SearchRequest, SearchResponse, SearchTypeArg,
    SmtFailureOutput, TermPairOutput, TranslationFailureOutput,
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

/// Search type and depth bound that a response's witnesses are members of.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct QueryShape {
    search_type: SearchTypeArg,
    max_depth: Option<u64>,
}

impl QueryShape {
    fn of_state(request: &SearchRequest) -> Self {
        Self {
            search_type: request.search_type,
            max_depth: request.max_depth,
        }
    }

    fn of_pattern(request: &SearchPatternRequest) -> Self {
        Self {
            search_type: request.search_type,
            max_depth: request.max_depth,
        }
    }

    #[must_use]
    pub const fn search_type(self) -> SearchTypeArg {
        self.search_type
    }

    #[must_use]
    pub const fn max_depth(self) -> Option<u64> {
        self.max_depth
    }

    /// k-rust returns every `Final` state that reaches the depth bound as a result without
    /// checking whether it can still rewrite. Such a result is unexplored frontier, not a final
    /// state. The rule never over-claims but can under-report: result deduplication may keep a
    /// frontier copy of a state and drop a shallower stuck copy of it.
    fn is_frontier(self, depth: u64) -> bool {
        self.search_type == SearchTypeArg::Final
            && self.max_depth.is_some_and(|bound| depth >= bound)
    }
}

/// Members of the query's result set in facade order; non-empty by construction.
#[derive(Clone, Debug, PartialEq)]
pub struct Witnesses<T> {
    first: T,
    rest: Vec<T>,
}

impl<T> Witnesses<T> {
    #[must_use]
    pub const fn first(&self) -> &T {
        &self.first
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        std::iter::once(&self.first).chain(&self.rest)
    }
}

/// Existential outcome only. There is deliberately no complete, exhausted, or absent variant;
/// adding one is gated on the upstream `search-completeness` request.
///
/// Under the no-Z3 profile a state or path witness is a result whose path condition was not
/// refuted; pattern matches send an unknown condition to an incomplete item instead.
#[derive(Clone, Debug, PartialEq)]
pub enum ExistentialOutcome<T> {
    /// At least one result is a member of the set named by the query's search type.
    Witnessed(Witnesses<T>),
    /// No member was witnessed. This says nothing about absence.
    NotWitnessed,
}

impl<T> ExistentialOutcome<T> {
    fn from_members(members: Vec<T>) -> Self {
        let mut members = members.into_iter();
        match members.next() {
            Some(first) => Self::Witnessed(Witnesses {
                first,
                rest: members.collect(),
            }),
            None => Self::NotWitnessed,
        }
    }

    /// The witnesses, when the outcome is `Witnessed`.
    #[must_use]
    pub const fn witnesses(&self) -> Option<&Witnesses<T>> {
        match self {
            Self::Witnessed(witnesses) => Some(witnesses),
            Self::NotWitnessed => None,
        }
    }
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

/// Declares one adapted response. See the module documentation for why none of them may be
/// read as a complete result set.
macro_rules! adapted_search {
    ($(#[$doc:meta])* $name:ident, $item:ty) => {
        $(#[$doc])*
        #[derive(Clone, Debug, PartialEq)]
        pub struct $name {
            query: QueryShape,
            outcome: ExistentialOutcome<$item>,
            frontier: Vec<$item>,
            effects: Vec<EffectOutput>,
            incomplete: Vec<AdaptedIncomplete>,
            authority: AdapterAuthority,
        }

        impl $name {
            #[must_use]
            pub const fn query(&self) -> QueryShape {
                self.query
            }

            #[must_use]
            pub const fn outcome(&self) -> &ExistentialOutcome<$item> {
                &self.outcome
            }

            /// `Final` results at or beyond the depth bound: unexplored work, never members.
            /// Kept even when upstream reported no `DepthBound` item for them. An empty
            /// frontier does not mean the search was exhaustive.
            #[must_use]
            pub fn frontier(&self) -> &[$item] {
                &self.frontier
            }

            #[must_use]
            pub fn effects(&self) -> &[EffectOutput] {
                &self.effects
            }

            /// Upstream incomplete items in facade order. An empty list does not mean the
            /// search was exhaustive.
            #[must_use]
            pub fn incomplete(&self) -> &[AdaptedIncomplete] {
                &self.incomplete
            }

            #[must_use]
            pub const fn authority(&self) -> AdapterAuthority {
                self.authority
            }
        }
    };
}

adapted_search!(
    /// A state-set response preserving facade order and branch-local structure.
    AdaptedStateSearch,
    AdaptedBranch
);

adapted_search!(
    /// A path-set response preserving path witness order.
    AdaptedPathSearch,
    AdaptedBranch
);

adapted_search!(
    /// A pattern state-set response.
    AdaptedPatternSearch,
    AdaptedPatternMatch
);

adapted_search!(
    /// A pattern path-set response.
    AdaptedPatternPathSearch,
    AdaptedPatternMatch
);

/// One pattern match with exact binding and residual-constraint order.
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedPatternMatch {
    pub bindings: Vec<BindingOutput>,
    pub constraints: Vec<serde_json::Value>,
    pub branch: AdaptedBranch,
}

/// Decision-bearing class of the eight public incomplete variants. A simplification failure
/// takes the class of its error.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IncompleteClass {
    ResultBound,
    DepthBound,
    BreadthBound,
    Indeterminate,
    Cancelled,
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
        let query = QueryShape::of_state(&request);
        let response = backend
            .search_observed(ObservedRequest {
                request,
                rules: Some(self.manifest.backend_rule_ids()),
            })
            .map_err(SearchAdapterFailure::backend)?;
        adapt_state_response(&self.manifest, query, response)
    }

    /// Executes public observed path search.
    pub fn search_paths(
        &self,
        backend: &mut Backend,
        request: SearchRequest,
    ) -> Result<AdaptedPathSearch, SearchAdapterFailure> {
        let query = QueryShape::of_state(&request);
        let response = backend
            .search_paths_observed(ObservedRequest {
                request,
                rules: Some(self.manifest.backend_rule_ids()),
            })
            .map_err(SearchAdapterFailure::backend)?;
        adapt_path_response(&self.manifest, query, response)
    }

    /// Executes public observed pattern state search.
    pub fn search_pattern(
        &self,
        backend: &mut Backend,
        request: SearchPatternRequest,
    ) -> Result<AdaptedPatternSearch, SearchAdapterFailure> {
        let query = QueryShape::of_pattern(&request);
        let response = backend
            .search_pattern_observed(ObservedRequest {
                request,
                rules: Some(self.manifest.backend_rule_ids()),
            })
            .map_err(SearchAdapterFailure::backend)?;
        adapt_pattern_response(&self.manifest, query, response)
    }

    /// Executes public observed pattern path search.
    pub fn search_pattern_paths(
        &self,
        backend: &mut Backend,
        request: SearchPatternRequest,
    ) -> Result<AdaptedPatternPathSearch, SearchAdapterFailure> {
        let query = QueryShape::of_pattern(&request);
        let response = backend
            .search_pattern_paths_observed(ObservedRequest {
                request,
                rules: Some(self.manifest.backend_rule_ids()),
            })
            .map_err(SearchAdapterFailure::backend)?;
        adapt_pattern_path_response(&self.manifest, query, response)
    }

    /// Exact selected profile.
    #[must_use]
    pub const fn solver_profile(&self) -> SolverProfile {
        self.profile
    }
}

/// Splits facade results into witnessed members and depth-bounded frontier, keeping order.
fn partition<T>(
    query: QueryShape,
    results: Vec<T>,
    depth: impl Fn(&T) -> u64,
) -> (ExistentialOutcome<T>, Vec<T>) {
    let (frontier, members) = results
        .into_iter()
        .partition(|result| query.is_frontier(depth(result)));
    (ExistentialOutcome::from_members(members), frontier)
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
    query: QueryShape,
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
    let (outcome, frontier) = partition(query, states, |state| state.depth);
    Ok(AdaptedStateSearch {
        query,
        outcome,
        frontier,
        effects: response.effects,
        incomplete,
        authority: AdapterAuthority::NONE,
    })
}

fn adapt_path_response(
    manifest: &InstalledObservationManifest,
    query: QueryShape,
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
    let (outcome, frontier) = partition(query, witnesses, |witness| witness.depth);
    Ok(AdaptedPathSearch {
        query,
        outcome,
        frontier,
        effects: response.effects,
        incomplete,
        authority: AdapterAuthority::NONE,
    })
}

fn adapt_pattern_response(
    manifest: &InstalledObservationManifest,
    query: QueryShape,
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
    let (outcome, frontier) = partition(query, matches, |found| found.branch.depth);
    Ok(AdaptedPatternSearch {
        query,
        outcome,
        frontier,
        effects: response.effects,
        incomplete,
        authority: AdapterAuthority::NONE,
    })
}

fn adapt_pattern_path_response(
    manifest: &InstalledObservationManifest,
    query: QueryShape,
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
    let (outcome, frontier) = partition(query, matches, |found| found.branch.depth);
    Ok(AdaptedPatternPathSearch {
        query,
        outcome,
        frontier,
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

    use crate::observation::{ErasedBranch, NativeEvent, RuleObservationSpec};

    const UNBOUNDED_FINAL: QueryShape = QueryShape {
        search_type: SearchTypeArg::Final,
        max_depth: None,
    };

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
        let witnesses = result
            .outcome()
            .witnesses()
            .expect("the stuck state is a witness");
        assert!(matches!(
            witnesses.first().events.as_slice(),
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
                        .outcome()
                        .witnesses()
                        .into_iter()
                        .flat_map(Witnesses::iter)
                        .map(|state| state.events.len())
                        .sum::<usize>();
                    assert_eq!(events, count, "{id}");
                }
                (Err(SearchAdapterFailure::BackendRejected(_)), BackendRejected) => {}
                (actual, expected) => panic!("{id}: expected {expected:?}, got {actual:?}"),
            }
        }
    }

    /// Which facade entry point an O5 row drives.
    #[derive(Clone, Copy, Debug)]
    enum SearchKind {
        State,
        /// Pattern search for the initial state `a{}()`.
        Pattern,
        Path,
    }

    /// Observation-independent content of one adapted response. The unobserved facade reports
    /// no branch identities, so branches keep only final state, depth and rule trace.
    #[derive(Debug, PartialEq)]
    struct ErasedSearch {
        witnesses: Vec<ErasedBranch>,
        frontier: Vec<ErasedBranch>,
        incomplete: Vec<IncompleteClass>,
        depth_bound: Vec<ErasedBranch>,
        proves_exhaustive_absence: bool,
    }

    fn erase_semantics(branch: &AdaptedBranch) -> ErasedBranch {
        ErasedBranch {
            identity: Vec::new(),
            ..branch.erase_observations()
        }
    }

    fn erased_search<'a>(
        witnesses: impl Iterator<Item = &'a AdaptedBranch>,
        frontier: impl Iterator<Item = &'a AdaptedBranch>,
        incomplete: &[AdaptedIncomplete],
        authority: AdapterAuthority,
    ) -> ErasedSearch {
        ErasedSearch {
            witnesses: witnesses.map(erase_semantics).collect(),
            frontier: frontier.map(erase_semantics).collect(),
            incomplete: incomplete.iter().map(AdaptedIncomplete::class).collect(),
            depth_bound: incomplete
                .iter()
                .filter_map(|item| match item {
                    AdaptedIncomplete::DepthBound { state } => Some(erase_semantics(state)),
                    _ => None,
                })
                .collect(),
            proves_exhaustive_absence: authority.proves_exhaustive_absence(),
        }
    }

    /// Runs one row unobserved through the raw facade, or observed through the adapter.
    fn run_o5_row(
        kind: SearchKind,
        observed: bool,
        search_type: SearchTypeArg,
        max_depth: Option<u64>,
        max_results: Option<usize>,
    ) -> ErasedSearch {
        let mut backend = Backend::new(DEFINITION, "MAIN", BackendOptions::default()).unwrap();
        let adapter = SearchAdapter::new(
            SolverProfile::StructuredNoZ3Inference,
            observed_manifest("step-id"),
        )
        .unwrap();
        let request = SearchRequest {
            state: kore("a{}()"),
            search_type,
            max_depth,
            max_results,
            ..SearchRequest::default()
        };
        let query = QueryShape::of_state(&request);
        match kind {
            SearchKind::State => {
                let result = if observed {
                    adapter.search(&mut backend, request).unwrap()
                } else {
                    let response = backend.search(request).unwrap();
                    adapt_state_response(&empty_manifest(), query, response).unwrap()
                };
                erased_search(
                    result
                        .outcome()
                        .witnesses()
                        .into_iter()
                        .flat_map(Witnesses::iter),
                    result.frontier().iter(),
                    result.incomplete(),
                    result.authority(),
                )
            }
            SearchKind::Path => {
                let result = if observed {
                    adapter.search_paths(&mut backend, request).unwrap()
                } else {
                    let response = backend.search_paths(request).unwrap();
                    adapt_path_response(&empty_manifest(), query, response).unwrap()
                };
                erased_search(
                    result
                        .outcome()
                        .witnesses()
                        .into_iter()
                        .flat_map(Witnesses::iter),
                    result.frontier().iter(),
                    result.incomplete(),
                    result.authority(),
                )
            }
            SearchKind::Pattern => {
                let request = SearchPatternRequest {
                    state: request.state,
                    pattern: kore("a{}()"),
                    search_type,
                    max_depth,
                    max_results,
                    ..SearchPatternRequest::default()
                };
                let result = if observed {
                    adapter.search_pattern(&mut backend, request).unwrap()
                } else {
                    let response = backend.search_pattern(request).unwrap();
                    adapt_pattern_response(&empty_manifest(), query, response).unwrap()
                };
                erased_search(
                    result
                        .outcome()
                        .witnesses()
                        .into_iter()
                        .flat_map(Witnesses::iter)
                        .map(|found| &found.branch),
                    result.frontier().iter().map(|found| &found.branch),
                    result.incomplete(),
                    result.authority(),
                )
            }
        }
    }

    /// O5: a depth-bounded `Final` result is unexplored frontier, never a final-state witness,
    /// and observation erasure agrees with the unobserved baseline within the bound. Agreement
    /// within a bound is not identity of the unbounded searches.
    #[test]
    fn bounded_final_results_are_frontier_and_erasure_agrees_within_the_bound() {
        use IncompleteClass::DepthBound;
        use SearchKind::{Path, Pattern, State};
        use SearchTypeArg::{All, Final};
        // `a => b` and `b` is stuck, so every path from `a{}()` ends after one step.
        const LONGEST_PATH: u64 = 1;
        // (id, kind, search type, max_depth, max_results, witness depths, frontier depths,
        //  upstream incomplete classes). An empty witness list means `NotWitnessed`.
        type Row = (
            &'static str,
            SearchKind,
            SearchTypeArg,
            Option<u64>,
            Option<usize>,
            &'static [u64],
            &'static [u64],
            &'static [IncompleteClass],
        );
        let rows: [Row; 10] = [
            (
                "unbounded-final-witnesses-the-stuck-state",
                State,
                Final,
                None,
                None,
                &[1],
                &[],
                &[],
            ),
            (
                "final-frontier-at-depth-zero-is-not-a-witness",
                State,
                Final,
                Some(0),
                None,
                &[],
                &[0],
                &[DepthBound],
            ),
            // `b` is in fact stuck, but k-rust never checks stuckness at the bound.
            (
                "final-at-the-bound-is-frontier-even-if-stuck",
                State,
                Final,
                Some(1),
                None,
                &[],
                &[1],
                &[DepthBound],
            ),
            (
                "final-below-the-bound-is-a-witness",
                State,
                Final,
                Some(2),
                None,
                &[1],
                &[],
                &[],
            ),
            (
                "bounded-reachability-witness-is-sound",
                State,
                All,
                Some(0),
                None,
                &[0],
                &[],
                &[DepthBound],
            ),
            // Pins the upstream gap: the result bound breaks before the frontier is recorded,
            // so the empty upstream list is not evidence of a complete search.
            (
                "frontier-hidden-by-result-bound-is-still-frontier",
                State,
                Final,
                Some(0),
                Some(1),
                &[],
                &[0],
                &[],
            ),
            (
                "stuck-at-bound-hidden-by-result-bound",
                State,
                Final,
                Some(1),
                Some(1),
                &[],
                &[1],
                &[],
            ),
            (
                "final-pattern-frontier-is-not-a-match",
                Pattern,
                Final,
                Some(0),
                None,
                &[],
                &[0],
                &[DepthBound],
            ),
            (
                "reachability-pattern-at-bound-matches",
                Pattern,
                All,
                Some(0),
                None,
                &[0],
                &[],
                &[DepthBound],
            ),
            (
                "final-path-frontier-is-not-a-witness",
                Path,
                Final,
                Some(0),
                None,
                &[],
                &[0],
                &[DepthBound],
            ),
        ];
        for (id, kind, search_type, max_depth, max_results, witnesses, frontier, incomplete) in rows
        {
            let baseline = run_o5_row(kind, false, search_type, max_depth, max_results);
            let observed = run_o5_row(kind, true, search_type, max_depth, max_results);
            assert_eq!(observed, baseline, "{id}");
            let depths = |branches: &[ErasedBranch]| {
                branches
                    .iter()
                    .map(|branch| branch.depth)
                    .collect::<Vec<_>>()
            };
            assert_eq!(depths(&observed.witnesses), witnesses, "{id}");
            assert_eq!(depths(&observed.frontier), frontier, "{id}");
            assert_eq!(observed.incomplete, incomplete, "{id}");
            if max_depth.is_some_and(|bound| bound <= LONGEST_PATH) {
                assert!(
                    !observed.frontier.is_empty() || !observed.incomplete.is_empty(),
                    "{id}: a reached depth bound must leave a frontier or incomplete record"
                );
            }
            assert!(!observed.proves_exhaustive_absence, "{id}");
        }
    }

    #[test]
    fn final_states_at_the_depth_bound_are_frontier_not_witnesses() {
        let manifest = empty_manifest();
        let depths = |branches: Vec<&AdaptedBranch>| {
            branches
                .iter()
                .map(|branch| branch.depth)
                .collect::<Vec<_>>()
        };
        let path_witness = |marker: i64| PathWitnessOutput {
            id: state(marker).branch,
            state: json!({ "marker": marker }),
            depth: marker.unsigned_abs(),
            trace: Vec::new(),
            observations: Vec::new(),
        };
        let found = |marker| SearchMatchOutput {
            bindings: Vec::new(),
            constraints: Vec::new(),
            state: state(marker),
        };
        let found_path = |marker| PathSearchMatchOutput {
            bindings: Vec::new(),
            constraints: Vec::new(),
            witness: path_witness(marker),
        };
        // (id, query, witness depths, frontier depths) over results at depths [2, 3] and no
        // DepthBound item: a result-bound break leaves exactly this upstream shape.
        let bound = |search_type| QueryShape {
            search_type,
            max_depth: Some(3),
        };
        let rows: [(&str, QueryShape, &[u64], &[u64]); 3] = [
            ("final-at-bound", bound(SearchTypeArg::Final), &[2], &[3]),
            (
                "reachability-at-bound",
                bound(SearchTypeArg::All),
                &[2, 3],
                &[],
            ),
            ("unbounded-final", UNBOUNDED_FINAL, &[2, 3], &[]),
        ];
        for (id, query, witnesses, frontier) in rows {
            let members = |outcome: &ExistentialOutcome<AdaptedBranch>| {
                depths(
                    outcome
                        .witnesses()
                        .into_iter()
                        .flat_map(Witnesses::iter)
                        .collect(),
                )
            };
            let match_members = |outcome: &ExistentialOutcome<AdaptedPatternMatch>| {
                depths(
                    outcome
                        .witnesses()
                        .into_iter()
                        .flat_map(Witnesses::iter)
                        .map(|found| &found.branch)
                        .collect(),
                )
            };
            let state_result = adapt_state_response(
                &manifest,
                query,
                state_response(vec![state(2), state(3)], Vec::new()),
            )
            .unwrap();
            assert_eq!(members(state_result.outcome()), witnesses, "{id} state");
            assert_eq!(
                depths(state_result.frontier().iter().collect()),
                frontier,
                "{id} state"
            );
            assert!(state_result.incomplete().is_empty(), "{id} state");

            let path_result = adapt_path_response(
                &manifest,
                query,
                PathSearchResponse {
                    schema_version: BACKEND_SCHEMA_VERSION,
                    modality: ResultModalityOutput::PathSet,
                    witnesses: vec![path_witness(2), path_witness(3)],
                    effects: Vec::new(),
                    incomplete: Vec::new(),
                },
            )
            .unwrap();
            assert_eq!(members(path_result.outcome()), witnesses, "{id} path");
            assert_eq!(
                depths(path_result.frontier().iter().collect()),
                frontier,
                "{id} path"
            );

            let pattern_result = adapt_pattern_response(
                &manifest,
                query,
                PatternSearchResponse {
                    schema_version: BACKEND_SCHEMA_VERSION,
                    modality: ResultModalityOutput::StateSet,
                    matches: vec![found(2), found(3)],
                    effects: Vec::new(),
                    incomplete: Vec::new(),
                },
            )
            .unwrap();
            assert_eq!(
                match_members(pattern_result.outcome()),
                witnesses,
                "{id} pattern"
            );
            assert_eq!(
                depths(
                    pattern_result
                        .frontier()
                        .iter()
                        .map(|found| &found.branch)
                        .collect()
                ),
                frontier,
                "{id} pattern"
            );

            let pattern_path_result = adapt_pattern_path_response(
                &manifest,
                query,
                PathPatternSearchResponse {
                    schema_version: BACKEND_SCHEMA_VERSION,
                    modality: ResultModalityOutput::PathSet,
                    matches: vec![found_path(2), found_path(3)],
                    effects: Vec::new(),
                    incomplete: Vec::new(),
                },
            )
            .unwrap();
            assert_eq!(
                match_members(pattern_path_result.outcome()),
                witnesses,
                "{id} pattern path"
            );
            assert_eq!(
                depths(
                    pattern_path_result
                        .frontier()
                        .iter()
                        .map(|found| &found.branch)
                        .collect()
                ),
                frontier,
                "{id} pattern path"
            );
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
        let result = adapt_state_response(
            &empty_manifest(),
            UNBOUNDED_FINAL,
            state_response(Vec::new(), items),
        )
        .unwrap();
        assert_eq!(result.outcome(), &ExistentialOutcome::NotWitnessed);
        assert_eq!(
            result
                .incomplete()
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
            let result = adapt_state_response(
                &empty_manifest(),
                UNBOUNDED_FINAL,
                state_response(Vec::new(), incomplete),
            )
            .unwrap();
            assert_eq!(result.outcome(), &ExistentialOutcome::NotWitnessed);
            assert!(!result.authority().proves_exhaustive_absence());
        }
    }

    #[test]
    fn witness_survives_a_truncated_sibling() {
        let result = adapt_state_response(
            &empty_manifest(),
            UNBOUNDED_FINAL,
            state_response(
                vec![state(7)],
                vec![IncompleteSearchOutput::BreadthBound {
                    states: vec![state(8)],
                }],
            ),
        )
        .unwrap();
        let witnesses = result.outcome().witnesses().expect("a member is a witness");
        assert_eq!(witnesses.first().state, json!({ "marker": 7 }));
        assert_eq!(witnesses.iter().count(), 1);
        assert_eq!(
            result.incomplete()[0].class(),
            IncompleteClass::BreadthBound
        );
    }

    #[test]
    fn solver_failures_defer_to_the_exact_later_profile() {
        let result = adapt_state_response(
            &empty_manifest(),
            UNBOUNDED_FINAL,
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
            &result.incomplete()[0],
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
            UNBOUNDED_FINAL,
            state_response(vec![state(2), state(1)], Vec::new()),
        )
        .unwrap();
        let first = |outcome: &ExistentialOutcome<AdaptedBranch>| {
            outcome.witnesses().unwrap().first().state.clone()
        };
        assert_eq!(first(state_result.outcome()), json!({ "marker": 2 }));

        let witness = |marker| PathWitnessOutput {
            id: state(marker).branch,
            state: json!({ "marker": marker }),
            depth: 1,
            trace: Vec::new(),
            observations: Vec::new(),
        };
        let path_result = adapt_path_response(
            &manifest,
            UNBOUNDED_FINAL,
            PathSearchResponse {
                schema_version: BACKEND_SCHEMA_VERSION,
                modality: ResultModalityOutput::PathSet,
                witnesses: vec![witness(2), witness(1)],
                effects: Vec::new(),
                incomplete: Vec::new(),
            },
        )
        .unwrap();
        assert_eq!(first(path_result.outcome()), json!({ "marker": 2 }));

        let pattern_result = adapt_pattern_response(
            &manifest,
            UNBOUNDED_FINAL,
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
        let found = pattern_result.outcome().witnesses().unwrap().first();
        assert_eq!(found.constraints, [json!("constraint")]);

        let pattern_path_result = adapt_pattern_path_response(
            &manifest,
            UNBOUNDED_FINAL,
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
            pattern_path_result
                .outcome()
                .witnesses()
                .unwrap()
                .first()
                .branch
                .state,
            json!({ "marker": 3 })
        );
    }

    #[test]
    fn replay_equality_accepts_and_mismatch_publishes_nothing() {
        let result = ReplaySearch::State(
            adapt_state_response(
                &empty_manifest(),
                UNBOUNDED_FINAL,
                state_response(vec![state(1)], Vec::new()),
            )
            .unwrap(),
        );
        assert_eq!(compare_replay(&result, &result), Ok(ReplayAgreement));
        let other = ReplaySearch::State(
            adapt_state_response(
                &empty_manifest(),
                UNBOUNDED_FINAL,
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
            UNBOUNDED_FINAL,
            state_response(vec![state(1)], Vec::new()),
        )
        .unwrap();
        assert_eq!(
            result.authority().provenance(),
            ProvenanceStatus::SidecarOnlyMissingBridge
        );
        assert!(!result.authority().grants_native_authority());
        assert!(!result.authority().has_production_receipt());
        assert!(!result.authority().proves_exhaustive_absence());
    }
}
