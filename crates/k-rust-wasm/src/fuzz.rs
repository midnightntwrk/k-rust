//! One `krust fuzz` campaign per call: the definition sources and the campaign specification in,
//! the canonical `krust-fuzz-report` JSON out (`k_rust_fuzz`, whose README documents the
//! campaign and the report).
//!
//! The specification is read by [`crate::campaign`], which `k-rust-napi` shares. This module
//! compiles the definitions from in-memory sources, on krun's route, and refuses the two options
//! this WebAssembly build cannot honour, before compiling anything
//! ([`refuse_unavailable_options`]).
//!
//! A panic inside a campaign traps the WebAssembly instance (`RuntimeError: unreachable` in
//! JavaScript): the call throws rather than ending the host process, but the instance's memory
//! may be inconsistent afterwards, and the package README tells callers to initialize a fresh
//! one.

use k_rust::{
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};
use k_rust_fuzz::{CompiledDefinition, spec::ProposerKind};
use serde::Deserialize;

use crate::{
    Source, VirtualResolver,
    campaign::{CampaignJson, CampaignParts},
    display_error, format_compile_error, implicit_sources,
};

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

/// The k-rust revision a report records when the caller gives no identity: the build identity
/// of the k-rust this binding links (`k_rust::build_identity`), which `krust fuzz` records too,
/// so a binding report and a CLI report of one k-rust source name the same revision.
fn build() -> String {
    k_rust::build_identity()
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
    let campaign = options.campaign.parts(&build())?;
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
            "campaign.options.safety-limit-ms: the per-case safety limit is not available in \
             WebAssembly, which has no clock to read a deadline from and no thread to stop a \
             case at it; bound every case with max-work or max-depth"
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
    use std::{collections::BTreeMap, sync::Arc};

    use k_rust_fuzz::{
        Campaign, CampaignSpec, CaseOptions, Definitions, FuzzReport, ProgramInput, ProposerConfig,
        report::{KillKind, REPORT_VERSION},
        spec::DEFAULT_REJECTION_CAP,
        values::GenerationBounds,
    };
    use serde_json::{Value, json};

    use super::*;

    const IMP: &str = include_str!("../../k-rust-fuzz/tests/data/imp/imp.k");
    const LE: &str = include_str!("../../k-rust-fuzz/tests/data/imp/le.imp");
    const COIN: &str = include_str!("../../k-rust-fuzz/tests/data/coin/coin.k");
    const COIN_KILL: &str = include_str!("../../k-rust-fuzz/tests/data/coin/coin-kill.k");
    const FLIP: &str = include_str!("../../k-rust-fuzz/tests/data/coin/flip.pgm");

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

    /// The differential campaign of the fuzz crate's `campaign_differential` test, which the
    /// package tests also run: COIN against COIN-KILL, which adds the end N + 2 for N > 10,
    /// over the `3` of `flip(3)`, with 10 as an explicit assignment.
    fn coin_campaign() -> Value {
        json!({
            "definition": COIN,
            "moduleName": "COIN",
            "sourceName": "coin.k",
            "includePrelude": true,
            "mutant": {
                "definition": COIN_KILL,
                "moduleName": "COIN",
                "sourceName": "coin-kill.k",
                "includePrelude": true,
            },
            "campaign": {
                "program": {
                    "program": { "name": "flip.pgm", "text": FLIP, "start-sort": "Pgm" },
                    "config-vars": [],
                },
                "holes": [{
                    "name": "N",
                    "sort": "Int",
                    "location": {
                        "kind": "span", "program": "flip.pgm", "find": "3", "literal": "3",
                    },
                }],
                "target": {
                    "kind": { "kind": "differential" },
                    "run-to-completion": false,
                    "negated-property": false,
                },
                "proposers": { "explicit": [{ "N": { "int": "10" } }] },
                "seed": "7",
                "identity": { "k-rust-revision": "k-rust-wasm-test" },
                "budget": { "cases": "64" },
            },
        })
    }

    fn int(value: &k_rust_fuzz::Value) -> i128 {
        match value {
            k_rust_fuzz::Value::Int(n) => n.to_string().parse().expect("a small integer"),
            other => panic!("not an Int: {other:?}"),
        }
    }

    /// The library's report for `options`, with the specification built by hand from the
    /// JSON's typed parts, `proposers` and `seed`, and the library defaults for the rest.
    fn library_report(options: Value, proposers: ProposerConfig, seed: u64) -> FuzzReport {
        let options: FuzzCampaignOptions = serde_json::from_value(options).unwrap();
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
                mutant: options
                    .mutant
                    .map(|mutant| Arc::new(compile(mutant).unwrap())),
            },
            program: ProgramInput::Source(program.unwrap()),
            holes,
            target,
            options: CaseOptions::default(),
            proposers,
            bounds: GenerationBounds::default(),
            rejection_cap: DEFAULT_REJECTION_CAP,
            seed,
            identity: identity.unwrap(),
        };
        Campaign::new(spec).unwrap().run(budget, None)
    }

    /// The call returns the report the library returns for the same specification, built by
    /// hand: the JSON is read into exactly that specification. `k-rust-napi` reads it with the
    /// same code ([`crate::campaign`]).
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

        let library = library_report(imp_campaign(json!({})), ProposerConfig::default(), 24301);
        assert_eq!(json, library.to_canonical_json());
    }

    /// The mutant reaches the campaign: COIN-KILL is killed by an N above 10, with the report
    /// the library gives for the same pair.
    #[test]
    fn runs_a_differential_campaign_to_the_report_the_library_returns() {
        let json = run_fuzz_campaign(&coin_campaign().to_string()).unwrap();
        let report = FuzzReport::from_json(&json).unwrap();
        assert_eq!(report.identity.definitions.len(), 2);
        let witness = report.witness().expect("COIN-KILL is killed");
        let case = witness.shrunk.as_ref().unwrap_or(&witness.first);
        assert_eq!(case.kill, Some(KillKind::AddedEnd));
        assert!(int(&case.holes[0].value) > 10);

        let ten = serde_json::from_value(json!({ "int": "10" })).unwrap();
        let proposers = ProposerConfig {
            explicit: vec![BTreeMap::from([("N".to_owned(), ten)])],
            ..ProposerConfig::default()
        };
        let library = library_report(coin_campaign(), proposers, 7);
        assert_eq!(json, library.to_canonical_json());
    }

    /// Without an `identity`, the report names this build rather than an empty revision.
    #[test]
    fn a_missing_identity_records_the_build() {
        let mut options = imp_campaign(json!({ "budget": { "cases": "1" } }));
        options["campaign"]
            .as_object_mut()
            .expect("an object")
            .remove("identity");
        let json = run_fuzz_campaign(&options.to_string()).unwrap();
        let report = FuzzReport::from_json(&json).unwrap();
        assert_eq!(report.identity.k_rust_revision, k_rust::build_identity());
        assert!(
            k_rust::is_verified_build(&report.identity.k_rust_revision),
            "a workspace build names its source digest: {}",
            report.identity.k_rust_revision
        );
        assert_eq!(report.identity.thread_stack_size, None);
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

    /// A misspelt field anywhere in the specification is refused, also inside a hole, where it
    /// would otherwise drop a constraint and widen the search (BIND review S1).
    #[test]
    fn refuses_unknown_fields_and_noncanonical_seeds() {
        let location =
            json!({ "kind": "span", "program": "le.imp", "find": "x = 3;", "literal": "3" });
        let zero = json!({ "range": { "min": "0", "max": "0" } });
        let misspelt_constraints =
            json!({ "name": "X", "sort": "Int", "location": location, "constraint": zero });
        let misspelt_range = json!({
            "name": "X",
            "sort": "Int",
            "location": location,
            "constraints": { "rnage": { "min": "0", "max": "0" } },
        });
        for (campaign, expected) in [
            (
                json!({ "options": { "max-dept": 3 } }),
                "campaign.options: unknown field `max-dept`",
            ),
            (
                json!({ "holes": [misspelt_constraints] }),
                "unknown field `constraint`",
            ),
            (
                json!({ "holes": [misspelt_range] }),
                "unknown field `rnage`",
            ),
            (
                json!({ "identity": { "k-rust-revison": "r" } }),
                "unknown field `k-rust-revison`",
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
