//! Discovery and structural cost planning without a compiler or validator.

use kink_patch::{
    Baseline, CandidateDisposition, ClaimSupport, OperatorSpec, ResolvedUniverse, canonical_json,
};
use serde_json::{Value, json};

/// A declared hash-rank budget. The seed is serialized as lowercase hexadecimal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BudgetMutants {
    pub per_spec_max: u64,
    pub total_max: u64,
    pub seed: Vec<u8>,
}

impl BudgetMutants {
    pub(crate) fn limits(&self) -> (u64, u64, &[u8]) {
        (self.per_spec_max, self.total_max, &self.seed)
    }

    pub(crate) fn seed_hex(&self) -> String {
        use std::fmt::Write;
        let mut text = String::with_capacity(self.seed.len() * 2);
        for byte in &self.seed {
            write!(text, "{byte:02x}").expect("writing to a string");
        }
        text
    }

    pub(crate) fn value(&self) -> Value {
        json!({"per_spec_max":self.per_spec_max,"total_max":self.total_max,"seed":self.seed_hex()})
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CampaignPlanError(pub String);

/// A plan or a refusal to produce one. Failures never publish a partial plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CampaignPlan {
    value: Result<Value, CampaignPlanError>,
}

impl CampaignPlan {
    pub fn value(&self) -> Result<&Value, &CampaignPlanError> {
        self.value.as_ref()
    }

    pub fn text(&self) -> Result<String, &CampaignPlanError> {
        self.value().map(canonical_json)
    }
}

/// Builds the complete discovery/fold/apply plan, compiling nothing.
pub fn campaign_plan(
    baseline: &Baseline,
    universe: &ResolvedUniverse,
    specs: &[OperatorSpec],
    budget: Option<&BudgetMutants>,
) -> CampaignPlan {
    CampaignPlan {
        value: plan_value(baseline, universe, specs, budget).map_err(CampaignPlanError),
    }
}

fn plan_value(
    baseline: &Baseline,
    universe: &ResolvedUniverse,
    specs: &[OperatorSpec],
    budget: Option<&BudgetMutants>,
) -> Result<Value, String> {
    let inputs = specs
        .iter()
        .map(|spec| (spec, usize::MAX))
        .collect::<Vec<_>>();
    let generations = OperatorSpec::generate_all(
        baseline,
        universe,
        &inputs,
        budget.map(BudgetMutants::limits),
    )
    .map_err(|e| e.to_string())?;
    let mut operators = Vec::new();
    // Plan for the general (including symbolic) campaign: E2 includes the full
    // withdrawal value, just as the manifest and runner do.
    let support = ClaimSupport::new(baseline);
    let mut structures = Vec::new();
    for (spec, generation) in specs.iter().zip(&generations) {
        let (population, population_sha256) = spec
            .population(baseline, universe)
            .map_err(|e| e.to_string())?;
        let mut distinct = Vec::new();
        for candidate in generation.candidates() {
            let identity =
                crate::runner::mutant_identity(baseline, &candidate.patch, Some(&support))
                    .ok_or_else(|| {
                        "cannot compute the E2 structure/withdrawal identity".to_owned()
                    })?;
            if !distinct.contains(&identity) {
                distinct.push(identity);
            }
        }
        for identity in &distinct {
            if !structures.contains(identity) {
                structures.push(identity.clone());
            }
        }
        operators.push(json!({"spec_sha256":spec.digest().to_string(),
            "population":population,"population_sha256":population_sha256.to_string(),
            "origins":generation.selected_origins().len(),
            "rejected_origins":generation.dispositions().iter().filter(|d| matches!(d,CandidateDisposition::Rejected(_))).count(),
            "candidates":generation.candidates().len(),"distinct_structures":distinct.len()}));
    }
    Ok(
        json!({"schema":"kink-campaign-plan","version":1,"operators":operators,"compilations":structures.len()}),
    )
}
