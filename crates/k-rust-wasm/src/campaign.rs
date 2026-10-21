//! The campaign specification of a binding call, read into the fuzz library's types and run.
//!
//! This file is shared: `k-rust-wasm` declares it as its `campaign` module, and `k-rust-napi`
//! includes the same file (`#[path]`), so that the library-equality tests of `k-rust-wasm`
//! (`src/fuzz.rs`) pin the reading both packages use. It refers to nothing outside itself.
//!
//! The specification is the fuzz library's own JSON (kebab-case), whose types refuse unknown
//! fields, apart from the parts a call supplies differently: the definitions are compiled by
//! the binding from in-memory sources, `options`, `proposers` and `bounds` are partial, and the
//! seed and the rejection cap are canonical decimal strings, as the report writes them.

use std::sync::Arc;

use k_rust::kore::parser::parse_pattern;
use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, CompiledDefinition, Definitions,
    HoleDecl, ProgramInput, ProgramSource, ProposerConfig, Target, spec::DEFAULT_REJECTION_CAP,
    values::GenerationBounds,
};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use serde_json::{Map, Value};

/// The campaign specification in the fuzz library's JSON. `options`, `proposers` and `bounds`
/// are partial: each field given replaces the library default, and an unknown field is refused.
#[derive(Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub(crate) struct CampaignJson {
    #[serde(default)]
    pub(crate) program: Option<ProgramSource>,
    /// A KORE initial configuration whose free element variables are the holes, as KORE text.
    #[serde(default)]
    pub(crate) kore_template: Option<String>,
    #[serde(default)]
    pub(crate) holes: Vec<HoleDecl>,
    pub(crate) target: Target,
    #[serde(default)]
    pub(crate) options: Map<String, Value>,
    #[serde(default)]
    pub(crate) proposers: Map<String, Value>,
    #[serde(default)]
    pub(crate) bounds: Map<String, Value>,
    #[serde(default)]
    pub(crate) rejection_cap: Option<String>,
    pub(crate) seed: String,
    /// `None`: the binding's build identity, with no stack size ([`CampaignJson::parts`]).
    #[serde(default)]
    pub(crate) identity: Option<CallerIdentity>,
    pub(crate) budget: Budget,
}

/// [`CampaignJson`] read into the library's types.
pub(crate) struct CampaignParts {
    pub(crate) program: ProgramInput,
    pub(crate) holes: Vec<HoleDecl>,
    pub(crate) target: Target,
    pub(crate) options: CaseOptions,
    pub(crate) proposers: ProposerConfig,
    pub(crate) bounds: GenerationBounds,
    pub(crate) rejection_cap: u64,
    pub(crate) seed: u64,
    pub(crate) identity: CallerIdentity,
    pub(crate) budget: Budget,
}

impl CampaignJson {
    /// Read the specification. Without an `identity`, the report records `build` as the k-rust
    /// revision: an empty revision would make every cache key and replay check that starts
    /// with it vacuous.
    pub(crate) fn parts(self, build: &str) -> Result<CampaignParts, String> {
        let program = match (self.program, self.kore_template) {
            (Some(program), None) => ProgramInput::Source(program),
            (None, Some(template)) => ProgramInput::KoreTemplate(
                parse_pattern(&template)
                    .map_err(|error| format!("campaign.kore-template: {error}"))?,
            ),
            _ => {
                return Err(
                    "campaign: give exactly one of `program` and `kore-template`".to_owned(),
                );
            }
        };
        Ok(CampaignParts {
            program,
            holes: self.holes,
            target: self.target,
            options: with_defaults(CaseOptions::default(), self.options, "campaign.options")?,
            proposers: with_defaults(
                ProposerConfig::default(),
                self.proposers,
                "campaign.proposers",
            )?,
            bounds: with_defaults(GenerationBounds::default(), self.bounds, "campaign.bounds")?,
            rejection_cap: match self.rejection_cap {
                Some(text) => decimal_u64(&text, "campaign.rejection-cap")?,
                None => DEFAULT_REJECTION_CAP,
            },
            seed: decimal_u64(&self.seed, "campaign.seed")?,
            identity: self.identity.unwrap_or_else(|| CallerIdentity {
                k_rust_revision: build.to_owned(),
                thread_stack_size: None,
            }),
            budget: self.budget,
        })
    }
}

impl CampaignParts {
    /// The library's specification of this campaign over `baseline` and `mutant`, and its
    /// budget.
    pub(crate) fn spec(
        self,
        baseline: CompiledDefinition,
        mutant: Option<CompiledDefinition>,
    ) -> (CampaignSpec, Budget) {
        let spec = CampaignSpec {
            definitions: Definitions {
                baseline: Arc::new(baseline),
                mutant: mutant.map(Arc::new),
            },
            program: self.program,
            holes: self.holes,
            target: self.target,
            options: self.options,
            proposers: self.proposers,
            bounds: self.bounds,
            rejection_cap: self.rejection_cap,
            seed: self.seed,
            identity: self.identity,
        };
        (spec, self.budget)
    }

    /// Run the campaign to its end on the calling thread and return the report's canonical
    /// JSON.
    pub(crate) fn run(
        self,
        baseline: CompiledDefinition,
        mutant: Option<CompiledDefinition>,
    ) -> Result<String, String> {
        let (spec, budget) = self.spec(baseline, mutant);
        let mut campaign = Campaign::new(spec).map_err(|error| error.to_string())?;
        Ok(campaign.run(budget, None).to_canonical_json())
    }
}

/// `defaults` with each field of `given` in place of its own. A field the defaults do not have
/// is refused, so that a misspelt option is an error rather than a silent default.
fn with_defaults<T: Serialize + DeserializeOwned>(
    defaults: T,
    given: Map<String, Value>,
    what: &str,
) -> Result<T, String> {
    let Value::Object(mut fields) =
        serde_json::to_value(defaults).map_err(|error| error.to_string())?
    else {
        return Err(format!("{what}: the defaults are not a JSON object"));
    };
    for (name, value) in given {
        if !fields.contains_key(&name) {
            let known: Vec<&str> = fields.keys().map(String::as_str).collect();
            return Err(format!(
                "{what}: unknown field `{name}`, expected one of {}",
                known.join(", ")
            ));
        }
        fields.insert(name, value);
    }
    serde_json::from_value(Value::Object(fields)).map_err(|error| format!("{what}: {error}"))
}

/// A `u64` written as a canonical decimal string (no sign, no leading zero), as the report
/// writes the seed and the rejection cap.
fn decimal_u64(text: &str, what: &str) -> Result<u64, String> {
    match text.parse::<u64>() {
        Ok(value) if value.to_string() == text => Ok(value),
        _ => Err(format!(
            "{what}: `{text}` is not a canonical decimal integer between 0 and 2^64 - 1"
        )),
    }
}
