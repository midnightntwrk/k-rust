//! Deterministic declaration and artifact identities, without executing a campaign.

use crate::{Campaign, CrashPolicy, Projection, ScheduleMode, StateProjection};
use k_rust::{backend::BackendOptions, kompile::CompileOptions, kore::codec::to_value};
use kink_native::{K_RUST_REVISION, MutantRejection, execution::SolverProfile};
use kink_patch::{
    CAMPAIGN_MANIFEST_DOMAIN, CANONICAL_PATCH_DOMAIN, COMPILED_KORE_DOMAIN, CandidateDisposition,
    CandidateGeneration, ClaimSupport, Completeness, FINGERPRINT_DOMAIN, OBSERVATION_DOMAIN,
    OperatorSpec, ResolvedUniverse, SelectionPolicy, SemanticInput, Sha256Digest,
    TEST_MANIFEST_DOMAIN, apply, canonical_json, payload_digest, structure_sha256,
};
use kink_pattern::{MatchMode, PatternPlan, Relation};
use serde_json::{Value, json};

pub struct OperatorId<'a> {
    pub id: &'a str,
    pub version: u32,
    pub policy: SelectionPolicy,
}

pub enum ManifestOperator<'a> {
    Code(OperatorId<'a>),
    Spec(&'a OperatorSpec),
}
impl ManifestOperator<'_> {
    fn name(&self) -> String {
        match self {
            Self::Code(id) => id.id.to_owned(),
            Self::Spec(spec) => spec.name(),
        }
    }
}

pub struct MultiManifestInput<'a> {
    pub campaign: &'a Campaign<'a>,
    pub generations: &'a [CandidateGeneration<'a>],
    pub schedule: ScheduleMode,
    pub selection: crate::SelectionPolicy,
    pub operators: &'a [ManifestOperator<'a>],
    pub classifier: &'a str,
    pub universe: Option<&'a ResolvedUniverse>,
}

pub struct ManifestInput<'a> {
    pub campaign: &'a Campaign<'a>,
    pub generation: &'a CandidateGeneration<'a>,
    pub schedule: ScheduleMode,
    pub selection: crate::SelectionPolicy,
    pub operators: &'a [ManifestOperator<'a>],
    pub classifier: &'a str,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CampaignManifest {
    value: Value,
    baseline_input: SemanticInput,
}
impl CampaignManifest {
    pub const fn value(&self) -> &Value {
        &self.value
    }
    pub fn text(&self) -> String {
        canonical_json(&self.value)
    }
    pub fn digest(&self) -> Sha256Digest {
        payload_digest(CAMPAIGN_MANIFEST_DOMAIN, self.text().as_bytes())
    }
    pub const fn baseline_input(&self) -> &SemanticInput {
        &self.baseline_input
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ManifestError {
    ForeignGeneration,
    OperatorMismatch,
    Unpinned,
    NonDefaultCompileOptions,
    BaselineCompile(String),
    Census(String),
    Encode(String),
}
impl std::fmt::Display for ManifestError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for ManifestError {}
fn encode(e: impl std::fmt::Display) -> ManifestError {
    ManifestError::Encode(e.to_string())
}
fn digest_value(domain: &str, value: &Value) -> String {
    payload_digest(domain, canonical_json(value).as_bytes()).to_string()
}

pub fn campaign_manifest(input: &ManifestInput<'_>) -> Result<CampaignManifest, ManifestError> {
    let universe = input
        .operators
        .iter()
        .any(|op| matches!(op, ManifestOperator::Spec(_)))
        .then(|| {
            kink_patch::resolve_universe(
                input.campaign.validator.baseline(),
                &kink_patch::Universe::v1(),
            )
        });
    campaign_manifest_multi(&MultiManifestInput {
        campaign: input.campaign,
        generations: std::slice::from_ref(input.generation),
        schedule: input.schedule,
        selection: input.selection,
        operators: input.operators,
        classifier: input.classifier,
        universe: universe.as_ref(),
    })
}

pub fn campaign_manifest_multi(
    input: &MultiManifestInput<'_>,
) -> Result<CampaignManifest, ManifestError> {
    let campaign = input.campaign;
    let validator = campaign.validator;
    let baseline = validator.baseline();
    if input.generations.iter().any(|g| !g.derived_from(baseline)) {
        return Err(ManifestError::ForeignGeneration);
    }
    let compiled = validator
        .compile_baseline()
        .map_err(|e| ManifestError::BaselineCompile(e.to_string()))?;
    if compiled.compile_options() != &CompileOptions::default() {
        return Err(ManifestError::NonDefaultCompileOptions);
    }
    if input.generations.is_empty() || input.generations.len() != input.operators.len() {
        return Err(ManifestError::OperatorMismatch);
    }
    if input
        .operators
        .iter()
        .any(|op| matches!(op, ManifestOperator::Spec(_)))
        != input.universe.is_some()
    {
        return Err(ManifestError::OperatorMismatch);
    }
    if input.universe.is_some_and(|u| {
        u.value() != kink_patch::resolve_universe(baseline, &kink_patch::Universe::v1()).value()
    }) {
        return Err(ManifestError::OperatorMismatch);
    }
    let declarations = kink_native::declaration_census(&compiled)
        .map_err(|e| ManifestError::Census(e.to_string()))?;
    let representation = match kink_native::representation::validate_representation(&compiled) {
        Ok(()) => json!("admitted"),
        Err(kink_native::representation::RepresentationError::Finding(f)) => {
            json!({"refused":f.clause.to_string()})
        }
        Err(e) => return Err(encode(e)),
    };
    let support = campaign
        .tests
        .iter()
        .any(|t| !t.initial_state.variable_occurrences().is_empty())
        .then(|| ClaimSupport::new(baseline));
    let baseline_input = SemanticInput::of(baseline).map_err(encode)?;
    let baseline_digest = baseline_input.digest().to_string();
    let tests = Value::Array(campaign.tests.iter().map(|test| Ok(json!({
        "id":test.id, "initial_state":to_value(&test.initial_state).map_err(encode)?,
        "oracles":test.oracles.iter().map(|oracle| json!({
            "crash_policy":match oracle.crash_policy() { CrashPolicy::Reject => "reject", CrashPolicy::CompareIdentity => "compare-identity", CrashPolicy::Distinguish => "distinguish" },
            "projection": projection(oracle.projection()),
        })).collect::<Vec<_>>(),
    }))).collect::<Result<Vec<_>, ManifestError>>()?);
    let observation = Value::Array(campaign.observation.iter().map(|spec| Ok(json!({
        "constructor":spec.constructor,"pre":to_value(&spec.pre).map_err(encode)?,"post":spec.post.as_ref().map(to_value).transpose().map_err(encode)?,"payload":spec.payload,
    }))).collect::<Result<Vec<_>, ManifestError>>()?);
    let mut mutants = Vec::new();
    let mut operators = Vec::new();
    let mut differs = false;
    let mut identities: Vec<Option<(Sha256Digest, kink_patch::Withdrawal)>> = Vec::new();
    for (operator_index, (generation, operator)) in
        input.generations.iter().zip(input.operators).enumerate()
    {
        let generation_value = json!({"origins":generation.selected_origins().len(),"rejected_origins":generation.dispositions().iter().filter(|d| matches!(d, CandidateDisposition::Rejected(_))).count(),"completeness":match generation.completeness() { Completeness::CompleteFinite => "complete-finite", Completeness::Incomplete => "incomplete" },"failure":generation.failure().map(|f| enum_name(&format!("{f:?}"))),"scored":generation.scored()});
        operators.push(match operator {
            ManifestOperator::Code(id) => json!({"kind":"code","id":id.id,"version":id.version,"policy":policy(id.policy),"generation":generation_value}),
            ManifestOperator::Spec(spec) => json!({"kind":"spec","spec":spec.canonical_value(),"spec_sha256":spec.digest().to_string(),"generation":generation_value}),
        });
        for candidate in generation.candidates() {
            let index = mutants.len();
            if candidate.operator != operator.name() {
                return Err(ManifestError::OperatorMismatch);
            }
            if !candidate.patch.is_pinned() {
                return Err(ManifestError::Unpinned);
            }
            let identity =
                crate::runner::mutant_identity(baseline, &candidate.patch, support.as_ref());
            let same_as = identity.as_ref().and_then(|identity| {
                identities
                    .iter()
                    .position(|earlier| earlier.as_ref() == Some(identity))
            });
            identities.push(identity);
            let patch_digest = candidate.patch.digest().map_err(encode)?.to_string();
            let (semantic_digest, structure_digest) = match apply(baseline, &candidate.patch) {
                Ok(mutant) => (
                    Some(
                        SemanticInput::of_definition(
                            mutant.definition(),
                            baseline.loaded().source_table(),
                        )
                        .map_err(encode)?
                        .digest()
                        .to_string(),
                    ),
                    Some(
                        structure_sha256(mutant.definition())
                            .map_err(encode)?
                            .to_string(),
                    ),
                ),
                Err(_) => (None, None),
            };
            let mut census = Value::Null;
            let (kore_digest, validation) = match validator.validate(&candidate.patch) {
                Ok(side) => {
                    let mut equal = kink_native::declaration_census(&side)
                        .map_err(|e| ManifestError::Census(e.to_string()))?
                        == declarations;
                    if kink_native::representation::validate_representation(&side).is_ok()
                        && matches!(
                            kink_native::equivalent_compilation(&compiled, &side),
                            Ok(false)
                        )
                        && let Some(support) = &support
                    {
                        let claims = support
                            .withdraw(baseline, &candidate.patch)
                            .map_err(encode)?;
                        if claims.trusted()
                            && let Some(patch) = claims.patch()
                            && let Ok(withdrawn) = validator.validate(patch)
                        {
                            equal &= kink_native::declaration_census(&withdrawn)
                                .map_err(|e| ManifestError::Census(e.to_string()))?
                                == declarations;
                        }
                    }
                    differs |= !equal;
                    census = json!(if equal { "baseline" } else { "differs" });
                    (
                        Some(side.kore_sha256().to_string()),
                        json!({"outcome":"compiled","stage":null,"detail":null}),
                    )
                }
                Err(MutantRejection::Patch(f)) => (
                    None,
                    json!({"outcome":"rejected","stage":"patch","detail":f.kind().as_str()}),
                ),
                Err(MutantRejection::Relink(_)) => (
                    None,
                    json!({"outcome":"rejected","stage":"relink","detail":null}),
                ),
                Err(MutantRejection::Compilation(e)) => (
                    None,
                    json!({"outcome":"rejected","stage":"compilation","detail":e.stage}),
                ),
            };
            mutants.push(json!({"mutant_id":index,"same_as":same_as,"operator":operator_index,"census":census,"patch_sha256":patch_digest,"semantic_input_sha256":semantic_digest,"structure_sha256":structure_digest,"kore_sha256":kore_digest,"validation":validation}));
        }
    }
    let backend = BackendOptions::default();
    let value = json!({
        "schema":"kink-campaign-manifest","version":4,
        "k_rust":{"revision":K_RUST_REVISION,"provenance_format":k_rust::definition::json::PROVENANCE_FORMAT,"provenance_version":k_rust::definition::json::PROVENANCE_VERSION},
        "kink":{"fingerprint":FINGERPRINT_DOMAIN,"canonical_patch":CANONICAL_PATCH_DOMAIN,"compiled_kore":COMPILED_KORE_DOMAIN},
        "profile":SolverProfile::BUILD.name(), "compile_options":"default",
        "backend_options":{"smt_timeout_ms":backend.smt_timeout_ms,"smt_retry_limit":backend.smt_retry_limit},
        "budget":{"time_ms":u64::try_from(campaign.budget.time.as_millis()).unwrap_or(u64::MAX),"max_simplification_iterations":campaign.budget.max_simplification_iterations,"max_depth":campaign.budget.max_depth,"max_breadth":campaign.budget.max_breadth.map(|v| v.get())},
        "schedule":match input.schedule { ScheduleMode::Full => "full", ScheduleMode::FirstKill => "first-kill" },
        "module":campaign.module,"classifier":input.classifier,
        "selection":input.selection.value(),
        "operators":operators,
        "universe":input.universe.map(ResolvedUniverse::value),
        "admission":{"representation":representation,"declarations":declarations.value(),"verdict":if declarations.verdict() == kink_native::CensusVerdict::Natural && !differs { "natural" } else { "flagged" }},
        "baseline":{"semantic_input_sha256":baseline_digest,"artifact":format!("semantic-input/{baseline_digest}.json"),"structure_sha256":structure_sha256(baseline.definition()).map_err(encode)?.to_string(),"kore_sha256":compiled.kore_sha256().to_string()},
        "tests":{"count":campaign.tests.len(),"sha256":digest_value(TEST_MANIFEST_DOMAIN, &tests)},
        "observation_sha256":digest_value(OBSERVATION_DOMAIN, &observation),
        "mutants":mutants,
    });
    Ok(CampaignManifest {
        value,
        baseline_input,
    })
}

fn policy(policy: SelectionPolicy) -> Value {
    match policy {
        SelectionPolicy::Exact {
            expected_tuple_count,
            expected_tuple_arity,
        } => json!({"exact":{"tuples":expected_tuple_count,"arity":expected_tuple_arity}}),
        SelectionPolicy::Each => json!("each"),
        SelectionPolicy::TupleEach => json!("tuple-each"),
        SelectionPolicy::AllMatches => json!("all-matches"),
    }
}
fn enum_name(name: &str) -> String {
    let mut result = String::new();
    for (index, ch) in name.chars().enumerate() {
        if index > 0 && ch.is_uppercase() {
            result.push('-');
        }
        result.extend(ch.to_lowercase());
    }
    result
}
fn projection(projection: &Projection) -> Value {
    match projection {
        Projection::State(StateProjection::ExitStop { exit_code_cell }) => {
            json!({"exit-stop":{"exit_code_cell":exit_code_cell}})
        }
        Projection::State(StateProjection::WholeTerm) => json!("whole-term"),
        Projection::State(StateProjection::TermPaths(paths)) => json!({"term-paths":paths}),
        Projection::Pattern {
            plan,
            with_bindings,
        } => json!({"pattern":{"plan":plan_value(plan),"with_bindings":with_bindings}}),
    }
}
fn plan_value(plan: &PatternPlan) -> Value {
    json!({"variables":plan.variables.iter().map(|(name, sort)| json!({"name":name,"sort":sort.to_string()})).collect::<Vec<_>>(),
        "arms":plan.arms.iter().map(|arm| json!({
            "atoms":arm.atoms.iter().map(|atom| json!({"constructor":atom.constructor,"payload":atom.payload.iter().map(|clause| json!({"position":clause.position,"mode":match clause.mode { MatchMode::Bind => "bind", MatchMode::Use => "use" },"variable":clause.variable})).collect::<Vec<_>>()})).collect::<Vec<_>>(),
            "relations":arm.relations.iter().map(|r| match r { Relation::NextEvent => "next-event", Relation::EventuallyAfter => "eventually-after" }).collect::<Vec<_>>(),
        })).collect::<Vec<_>>(),
        "side_condition":plan.side_condition.as_ref().map(|c| json!({"name":c.name,"input_variables":c.input_variables})),
    })
}
