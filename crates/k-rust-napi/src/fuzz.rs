//! One `krust fuzz` campaign per call: the definition sources and the campaign specification in,
//! the canonical `krust-fuzz-report` JSON out (`k_rust_fuzz`, whose README documents the
//! campaign and the report).
//!
//! The addon's calls are synchronous, so a campaign runs to its end inside one call, on the
//! calling thread; a stepwise API would hold the campaign's backends across calls for nothing.
//! The specification is the fuzz library's own JSON (kebab-case), apart from the parts a call
//! supplies differently: the definitions are compiled here from in-memory sources, on krun's
//! route, and the seed and the rejection cap are canonical decimal strings, as the report writes
//! them.

use std::sync::Arc;

use k_rust::{
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::parser::parse_pattern,
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};
use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, CompiledDefinition, Definitions,
    HoleDecl, ProgramInput, ProgramSource, ProposerConfig, Target, spec::DEFAULT_REJECTION_CAP,
    values::GenerationBounds,
};
use napi::{Error, Result};
use napi_derive::napi;
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use serde_json::{Map, Value};

use crate::{NativeSource, VirtualResolver, compile_error, napi_error};

/// One definition's sources, loaded and compiled for the Rust backend as `krust kcompile` does.
#[napi(object)]
pub struct NativeFuzzDefinition {
    pub definition: String,
    pub module_name: String,
    /// The module whose grammar parses the program; selected as `kcompile` does when absent.
    pub syntax_module: Option<String>,
    pub source_name: Option<String>,
    pub sources: Option<Vec<NativeSource>>,
    pub markdown_selector: Option<String>,
    pub include_prelude: Option<bool>,
}

#[napi(object)]
pub struct NativeFuzzCampaignOptions {
    pub definition: String,
    pub module_name: String,
    pub syntax_module: Option<String>,
    pub source_name: Option<String>,
    pub sources: Option<Vec<NativeSource>>,
    pub markdown_selector: Option<String>,
    pub include_prelude: Option<bool>,
    /// The mutant of a differential target.
    pub mutant: Option<NativeFuzzDefinition>,
    /// The campaign specification as JSON, in the fuzz library's kebab-case fields.
    pub campaign: String,
}

/// Run one `krust fuzz` campaign on in-memory definitions and return its report's canonical
/// JSON. A campaign that runs returns its report, whatever its outcome; a malformed
/// specification, a definition that does not compile, and every refusal of `Campaign::new`
/// throw.
#[napi]
pub fn run_fuzz_campaign_native(options: NativeFuzzCampaignOptions) -> Result<String> {
    let campaign: CampaignJson = serde_json::from_str(&options.campaign)
        .map_err(|error| Error::from_reason(format!("campaign: {error}")))?;
    let campaign = campaign.parts().map_err(Error::from_reason)?;
    let baseline = compile(NativeFuzzDefinition {
        definition: options.definition,
        module_name: options.module_name,
        syntax_module: options.syntax_module,
        source_name: options.source_name,
        sources: options.sources,
        markdown_selector: options.markdown_selector,
        include_prelude: options.include_prelude,
    })?;
    let mutant = options.mutant.map(compile).transpose()?;
    campaign.run(baseline, mutant).map_err(Error::from_reason)
}

/// The campaign specification in the fuzz library's JSON. `options`, `proposers` and `bounds`
/// are partial: each field given replaces the library default, and an unknown field is refused.
#[derive(Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
struct CampaignJson {
    #[serde(default)]
    program: Option<ProgramSource>,
    /// A KORE initial configuration whose free element variables are the holes, as KORE text.
    #[serde(default)]
    kore_template: Option<String>,
    #[serde(default)]
    holes: Vec<HoleDecl>,
    target: Target,
    #[serde(default)]
    options: Map<String, Value>,
    #[serde(default)]
    proposers: Map<String, Value>,
    #[serde(default)]
    bounds: Map<String, Value>,
    #[serde(default)]
    rejection_cap: Option<String>,
    seed: String,
    #[serde(default)]
    identity: CallerIdentity,
    budget: Budget,
}

/// [`CampaignJson`] read into the library's types.
struct CampaignParts {
    program: ProgramInput,
    holes: Vec<HoleDecl>,
    target: Target,
    options: CaseOptions,
    proposers: ProposerConfig,
    bounds: GenerationBounds,
    rejection_cap: u64,
    seed: u64,
    identity: CallerIdentity,
    budget: Budget,
}

impl CampaignJson {
    fn parts(self) -> std::result::Result<CampaignParts, String> {
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
            identity: self.identity,
            budget: self.budget,
        })
    }
}

impl CampaignParts {
    fn run(
        self,
        baseline: CompiledDefinition,
        mutant: Option<CompiledDefinition>,
    ) -> std::result::Result<String, String> {
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
        let mut campaign = Campaign::new(spec).map_err(|error| error.to_string())?;
        Ok(campaign.run(self.budget, None).to_canonical_json())
    }
}

/// `defaults` with each field of `given` in place of its own. A field the defaults do not have
/// is refused, so that a misspelt option is an error rather than a silent default.
fn with_defaults<T: Serialize + DeserializeOwned>(
    defaults: T,
    given: Map<String, Value>,
    what: &str,
) -> std::result::Result<T, String> {
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
fn decimal_u64(text: &str, what: &str) -> std::result::Result<u64, String> {
    match text.parse::<u64>() {
        Ok(value) if value.to_string() == text => Ok(value),
        _ => Err(format!(
            "{what}: `{text}` is not a canonical decimal integer between 0 and 2^64 - 1"
        )),
    }
}

/// Load and compile one definition for the Rust backend, as `krust kcompile` does, and keep
/// what a campaign reads from it, on krun's route.
fn compile(options: NativeFuzzDefinition) -> Result<CompiledDefinition> {
    let source_name = options
        .source_name
        .unwrap_or_else(|| "definition.k".to_owned());
    let mut resolver = VirtualResolver::new(options.sources.unwrap_or_default());
    let implicit_sources = if options.include_prelude.unwrap_or(true) {
        vec![
            embedded("prelude.md")
                .ok_or_else(|| Error::from_reason("embedded prelude is unavailable"))?,
        ]
    } else {
        Vec::new()
    };
    let load_options = LoadOptions {
        markdown_selector: options.markdown_selector.unwrap_or_else(|| "k".to_owned()),
        implicit_sources,
        ..CompilationBackend::Rust.load_options()
    };
    let (loaded, syntax_module) = load_for_compilation(
        ResolvedSource::new(source_name, options.definition),
        options.module_name.as_str(),
        options.syntax_module.as_deref(),
        &mut resolver,
        &load_options,
    )
    .map_err(napi_error)?;
    let artifacts =
        compile_loaded_definition(&loaded, CompileOptions::default()).map_err(compile_error)?;
    CompiledDefinition::from_artifacts(
        options.module_name,
        syntax_module,
        loaded.into_definition(),
        artifacts,
    )
    .map_err(napi_error)
}
