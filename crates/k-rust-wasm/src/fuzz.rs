//! One `krust fuzz` campaign per call: the definition sources and the campaign specification in,
//! the canonical `krust-fuzz-report` JSON out (`k_rust_fuzz`, whose README documents the
//! campaign and the report).
//!
//! The specification is the fuzz library's own JSON (kebab-case), apart from the parts a call
//! supplies differently: the definitions are compiled here from in-memory sources, on krun's
//! route, and the seed and the rejection cap are canonical decimal strings, as the report writes
//! them. This WebAssembly build refuses the two options it cannot honour, before compiling
//! anything ([`refuse_unavailable_options`]).

use std::sync::Arc;

use k_rust::{
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::parser::parse_pattern,
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};
use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, CompiledDefinition, Definitions,
    HoleDecl, ProgramInput, ProgramSource, ProposerConfig, Target,
    spec::{DEFAULT_REJECTION_CAP, ProposerKind},
    values::GenerationBounds,
};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use serde_json::{Map, Value};

use crate::{Source, VirtualResolver, display_error, format_compile_error, implicit_sources};

/// The options of `runFuzzCampaignWasm`: the baseline definition's sources, the mutant's for a
/// differential target, and the campaign.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct FuzzCampaignOptions {
    #[serde(flatten)]
    baseline: FuzzDefinitionOptions,
    mutant: Option<FuzzDefinitionOptions>,
    campaign: CampaignJson,
}

/// One definition's sources, loaded and compiled for the Rust backend as `krust kcompile` does.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct FuzzDefinitionOptions {
    definition: String,
    module_name: String,
    /// The module whose grammar parses the program; `None` selects it as `kcompile` does.
    syntax_module: Option<String>,
    source_name: Option<String>,
    sources: Option<Vec<Source>>,
    markdown_selector: Option<String>,
    include_prelude: Option<bool>,
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

/// Run one campaign to its end and return the report's canonical JSON.
///
/// # Errors
///
/// A message for a malformed specification, an option this build refuses, a definition that
/// does not load or compile, and every refusal of `Campaign::new`. A campaign that runs returns
/// its report, whatever its outcome.
pub(crate) fn run_fuzz_campaign(options: &str) -> Result<String, String> {
    let options: FuzzCampaignOptions = serde_json::from_str(options).map_err(display_error)?;
    let campaign = options.campaign.parts()?;
    refuse_unavailable_options(&campaign)?;
    let baseline = compile(options.baseline)?;
    let mutant = options.mutant.map(compile).transpose()?;
    campaign.run(baseline, mutant)
}

/// Refuse the options this build cannot honour (ARCHITECTURE 9.4 of the fz26 programme: WASM
/// runs every proposer except solve, on one thread, without step timeouts).
///
/// - The per-case safety limit stops a case at a wall-clock deadline. `wasm32-unknown-unknown`
///   has no host clock to read the deadline from and no second thread to cancel the case at it.
///   `Campaign::new` also refuses a limit on wasm32, but only after the definitions are compiled;
///   this refusal names the option and comes first. Cases are bounded by `max-work` or
///   `max-depth`, which count steps.
/// - The solve proposer asks Z3 for hole values, and this build links no solver.
fn refuse_unavailable_options(campaign: &CampaignParts) -> Result<(), String> {
    if campaign.options.safety_limit_ms.is_some() {
        return Err(
            "campaign.options.safety-limit-ms: the per-case safety limit is not \
                    available in WebAssembly, which has no clock to read a deadline from and no \
                    thread to stop a case at it; bound every case with max-work or max-depth"
                .to_owned(),
        );
    }
    if campaign
        .proposers
        .weights
        .get(&ProposerKind::Solve)
        .is_some_and(|weight| *weight > 0)
    {
        return Err(
            "campaign.proposers.weights.solve: the solve proposer is not available in \
                    WebAssembly: it asks Z3 for hole values, and this build links no solver"
                .to_owned(),
        );
    }
    Ok(())
}

impl CampaignJson {
    fn parts(self) -> Result<CampaignParts, String> {
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
    ) -> Result<String, String> {
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
        let mut campaign = Campaign::new(spec).map_err(display_error)?;
        Ok(campaign.run(self.budget, None).to_canonical_json())
    }
}

/// `defaults` with each field of `given` in place of its own. A field the defaults do not have
/// is refused, so that a misspelt option is an error rather than a silent default.
fn with_defaults<T: Serialize + DeserializeOwned>(
    defaults: T,
    given: Map<String, Value>,
    what: &str,
) -> Result<T, String> {
    let Value::Object(mut fields) = serde_json::to_value(defaults).map_err(display_error)? else {
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

/// Load and compile one definition for the Rust backend, as `krust kcompile` does, and keep
/// what a campaign reads from it, on krun's route.
fn compile(options: FuzzDefinitionOptions) -> Result<CompiledDefinition, String> {
    let source_name = options
        .source_name
        .unwrap_or_else(|| "definition.k".to_owned());
    let mut resolver =
        VirtualResolver::new(options.sources.unwrap_or_default(), options.include_prelude);
    let load_options = LoadOptions {
        markdown_selector: options.markdown_selector.unwrap_or_else(|| "k".to_owned()),
        implicit_sources: implicit_sources(options.include_prelude)?,
        ..CompilationBackend::Rust.load_options()
    };
    let (loaded, syntax_module) = load_for_compilation(
        ResolvedSource::new(source_name, options.definition),
        options.module_name.as_str(),
        options.syntax_module.as_deref(),
        &mut resolver,
        &load_options,
    )
    .map_err(display_error)?;
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .map_err(format_compile_error)?;
    CompiledDefinition::from_artifacts(
        options.module_name,
        syntax_module,
        loaded.into_definition(),
        artifacts,
    )
    .map_err(display_error)
}

#[cfg(test)]
mod tests {
    use k_rust_fuzz::{FuzzReport, report::REPORT_VERSION};
    use serde_json::json;

    use super::*;

    const IMP: &str = include_str!("../../k-rust-fuzz/tests/data/imp/imp.k");
    const LE: &str = include_str!("../../k-rust-fuzz/tests/data/imp/le.imp");

    /// `r` of `le.imp` is not 1 at a clean natural end: the program's claim that the anchors'
    /// `x <= y` branch is taken fails, which any `x > y` shows.
    const LE_VIOLATION: &str =
        r#"<k> .K </k> <state> (#token("r", "Id") |-> R:Int) _:Map </state> requires R =/=Int 1"#;

    fn hole(name: &str, find: &str, literal: &str) -> Value {
        json!({
            "name": name,
            "sort": "Int",
            "location": { "kind": "span", "program": "le.imp", "find": find, "literal": literal },
        })
    }

    /// The IMP campaign the package tests run (`test/bindings.test.mjs`): blind values for `x`
    /// and `y` of `le.imp` until one falsifies the claim that `r` ends as 1.
    fn imp_campaign(campaign: Value) -> Value {
        let mut spec = json!({
            "program": {
                "program": { "name": "le.imp", "text": LE, "start-sort": "Pgm" },
                "config-vars": [],
            },
            "holes": [hole("X", "x = 3;", "3"), hole("Y", "y = 5;", "5")],
            "target": {
                "kind": { "kind": "pattern", "pattern": LE_VIOLATION, "at": "final" },
                "run-to-completion": false,
                "negated-property": true,
            },
            "seed": "24301",
            "identity": { "k-rust-revision": "k-rust-wasm-test" },
            "budget": { "cases": "64" },
        });
        for (name, value) in campaign.as_object().expect("an object") {
            spec[name] = value.clone();
        }
        json!({
            "definition": IMP,
            "moduleName": "IMP",
            "sourceName": "imp.k",
            "includePrelude": true,
            "campaign": spec,
        })
    }

    fn int(value: &k_rust_fuzz::Value) -> i128 {
        match value {
            k_rust_fuzz::Value::Int(n) => n.to_string().parse().expect("a small integer"),
            other => panic!("not an Int: {other:?}"),
        }
    }

    /// The call returns the report the library returns for the same specification, built by
    /// hand: the JSON is read into exactly that specification, with the library defaults for
    /// everything it leaves out.
    #[test]
    fn runs_an_imp_campaign_to_the_report_the_library_returns() {
        let json = run_fuzz_campaign(&imp_campaign(json!({})).to_string()).unwrap();
        let report = FuzzReport::from_json(&json).unwrap();
        assert_eq!(report.schema, "krust-fuzz-report");
        assert_eq!(report.version, REPORT_VERSION);
        let witness = report.witness().expect("a witness falsifies the claim");
        let case = witness.shrunk.as_ref().unwrap_or(&witness.first);
        let values: Vec<i128> = case.holes.iter().map(|hole| int(&hole.value)).collect();
        assert!(values[0] > values[1], "{values:?}");

        let options: FuzzCampaignOptions = serde_json::from_value(imp_campaign(json!({}))).unwrap();
        let CampaignJson {
            program,
            holes,
            target,
            identity,
            budget,
            ..
        } = options.campaign;
        let spec = CampaignSpec {
            definitions: Definitions {
                baseline: Arc::new(compile(options.baseline).unwrap()),
                mutant: None,
            },
            program: ProgramInput::Source(program.unwrap()),
            holes,
            target,
            options: CaseOptions::default(),
            proposers: ProposerConfig::default(),
            bounds: GenerationBounds::default(),
            rejection_cap: DEFAULT_REJECTION_CAP,
            seed: 24301,
            identity,
        };
        let library = Campaign::new(spec).unwrap().run(budget, None);
        assert_eq!(json, library.to_canonical_json());
    }

    /// Neither option can be honoured here, and each is refused before the definition is read:
    /// the definition below does not even parse.
    #[test]
    fn refuses_the_safety_limit_and_the_solve_proposer() {
        for (campaign, expected) in [
            (
                json!({ "options": { "safety-limit-ms": 1000 } }),
                "campaign.options.safety-limit-ms: the per-case safety limit is not available \
                 in WebAssembly",
            ),
            (
                json!({ "proposers": { "weights": { "blind": 1, "solve": 1 } } }),
                "campaign.proposers.weights.solve: the solve proposer is not available in \
                 WebAssembly",
            ),
        ] {
            let mut options = imp_campaign(campaign);
            options["definition"] = json!("not a definition");
            let error = run_fuzz_campaign(&options.to_string()).unwrap_err();
            assert!(error.starts_with(expected), "{error}");
        }
        // A zero weight disables the proposer, and a null limit is no limit: both are accepted.
        let options = imp_campaign(json!({
            "options": { "safety-limit-ms": null },
            "proposers": { "weights": { "blind": 1, "solve": 0 } },
            "budget": { "cases": "1" },
        }));
        run_fuzz_campaign(&options.to_string()).unwrap();
    }

    #[test]
    fn refuses_unknown_option_fields_and_noncanonical_seeds() {
        for (campaign, expected) in [
            (
                json!({ "options": { "max-dept": 3 } }),
                "campaign.options: unknown field `max-dept`",
            ),
            (
                json!({ "seed": "007" }),
                "campaign.seed: `007` is not a canonical",
            ),
            (
                json!({ "budget": { "time": "1" } }),
                "unknown variant `time`",
            ),
        ] {
            let error = run_fuzz_campaign(&imp_campaign(campaign).to_string()).unwrap_err();
            assert!(error.contains(expected), "{error}");
        }
    }
}
