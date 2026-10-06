//! Deterministic declaration and artifact identities, without executing a campaign.

use crate::{Campaign, CrashPolicy, Projection, ScheduleMode, StateProjection};
use k_rust::{backend::BackendOptions, kompile::CompileOptions, kore::codec::to_value};
use kink_native::{K_RUST_REVISION, MutantRejection, execution::SolverProfile};
use kink_patch::{
    CAMPAIGN_MANIFEST_DOMAIN, CANONICAL_PATCH_DOMAIN, COMPILED_KORE_DOMAIN, CandidateDisposition,
    CandidateGeneration, Completeness, FINGERPRINT_DOMAIN, OBSERVATION_DOMAIN, SelectionPolicy,
    SemanticInput, Sha256Digest, TEST_MANIFEST_DOMAIN, apply, canonical_json, payload_digest,
    structure_sha256,
};
use kink_pattern::{MatchMode, PatternPlan, Relation};
use serde_json::{Value, json};

pub struct OperatorId<'a> {
    pub id: &'a str,
    pub version: u32,
    pub policy: SelectionPolicy,
}

pub struct ManifestInput<'a> {
    pub campaign: &'a Campaign<'a>,
    pub generation: &'a CandidateGeneration<'a>,
    pub schedule: ScheduleMode,
    pub operator: OperatorId<'a>,
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
    let campaign = input.campaign;
    let validator = campaign.validator;
    let baseline = validator.baseline();
    let generation = input.generation;
    if !generation.derived_from(baseline) {
        return Err(ManifestError::ForeignGeneration);
    }
    let compiled = validator
        .compile_baseline()
        .map_err(|e| ManifestError::BaselineCompile(e.to_string()))?;
    if compiled.compile_options() != &CompileOptions::default() {
        return Err(ManifestError::NonDefaultCompileOptions);
    }
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
    for (index, candidate) in generation.candidates().iter().enumerate() {
        if candidate.operator != input.operator.id {
            return Err(ManifestError::OperatorMismatch);
        }
        if !candidate.patch.is_pinned() {
            return Err(ManifestError::Unpinned);
        }
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
        let (kore_digest, validation) = match validator.validate(&candidate.patch) {
            Ok(compiled) => (
                Some(compiled.kore_sha256().to_string()),
                json!({"outcome":"compiled","stage":null,"detail":null}),
            ),
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
        mutants.push(json!({"mutant_id":index,"patch_sha256":patch_digest,"semantic_input_sha256":semantic_digest,"structure_sha256":structure_digest,"kore_sha256":kore_digest,"validation":validation}));
    }
    let backend = BackendOptions::default();
    let value = json!({
        "schema":"kink-campaign-manifest","version":1,
        "k_rust":{"revision":K_RUST_REVISION,"provenance_format":k_rust::definition::json::PROVENANCE_FORMAT,"provenance_version":k_rust::definition::json::PROVENANCE_VERSION},
        "kink":{"fingerprint":FINGERPRINT_DOMAIN,"canonical_patch":CANONICAL_PATCH_DOMAIN,"compiled_kore":COMPILED_KORE_DOMAIN},
        "profile":SolverProfile::BUILD.name(), "compile_options":"default",
        "backend_options":{"smt_timeout_ms":backend.smt_timeout_ms,"smt_retry_limit":backend.smt_retry_limit},
        "budget":{"time_ms":u64::try_from(campaign.budget.time.as_millis()).unwrap_or(u64::MAX),"max_simplification_iterations":campaign.budget.max_simplification_iterations,"max_depth":campaign.budget.max_depth,"max_breadth":campaign.budget.max_breadth.map(|v| v.get())},
        "schedule":match input.schedule { ScheduleMode::Full => "full", ScheduleMode::FirstKill => "first-kill" },
        "module":campaign.module,"classifier":input.classifier,
        "operator":{"id":input.operator.id,"version":input.operator.version,"policy":policy(input.operator.policy)},
        "baseline":{"semantic_input_sha256":baseline_digest,"artifact":format!("semantic-input/{baseline_digest}.json"),"structure_sha256":structure_sha256(baseline.definition()).map_err(encode)?.to_string(),"kore_sha256":compiled.kore_sha256().to_string()},
        "tests":{"count":campaign.tests.len(),"sha256":digest_value(TEST_MANIFEST_DOMAIN, &tests)},
        "observation_sha256":digest_value(OBSERVATION_DOMAIN, &observation),
        "generation":{"origins":generation.selected_origins().len(),"rejected_origins":generation.dispositions().iter().filter(|d| matches!(d, CandidateDisposition::Rejected(_))).count(),"completeness":match generation.completeness() { Completeness::CompleteFinite => "complete-finite", Completeness::Incomplete => "incomplete" },"failure":generation.failure().map(|f| enum_name(&format!("{f:?}"))),"scored":generation.scored()},
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
