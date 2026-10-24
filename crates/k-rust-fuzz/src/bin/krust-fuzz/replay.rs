//! Witness files and `--replay` (ARCHITECTURE 9.4).
//!
//! A witness file holds the resolved campaign and the report that found the witness. Replaying
//! it rebuilds the campaign's specification from the recorded inputs, checks that the replay's
//! identity is the witness's (every field of the report's identity but the five that only
//! choose cases or that the replay sets itself; [`identity_mismatches`]), refuses on a mismatch
//! unless forced, and runs each recorded witness case as the campaign's only explicit
//! assignment. A case reproduces when the replay confirms a hit whose witness case,
//! with its class and final configurations, equals the recorded one.

use std::path::Path;

use k_rust_fuzz::{
    Budget, Campaign, ProposerConfig,
    report::{FuzzReport, REPORT_SCHEMA, REPORT_VERSION, ReportIdentity, WitnessCase},
};
use serde::{Deserialize, Serialize};

use crate::campaign::{LoadedCampaign, ResolvedCampaign};

/// The witness file's `schema` field.
pub const WITNESS_SCHEMA: &str = "krust-fuzz-witness";

/// The witness file's `version` field.
pub const WITNESS_VERSION: u32 = 1;

/// A witness file: the campaign as resolved and the report that found the witness.
#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct WitnessFile {
    /// Always [`WITNESS_SCHEMA`].
    pub schema: String,
    /// Always [`WITNESS_VERSION`] for files this build writes.
    pub version: u32,
    /// The campaign's inputs.
    pub campaign: ResolvedCampaign,
    /// The campaign's report; its outcome carries the witness.
    pub report: FuzzReport,
}

/// Deserialize `text`. The report's hole values nest up to `values::MAX_VALUE_DEPTH` levels,
/// deeper than `serde_json`'s recursion limit: read as `FuzzReport::from_json` reads, on a stack
/// that grows on the heap.
fn read_deep<'de, T: Deserialize<'de>>(text: &'de str) -> Result<T, serde_json::Error> {
    let mut reader = serde_json::Deserializer::from_str(text);
    reader.disable_recursion_limit();
    let value = T::deserialize(serde_stacker::Deserializer::new(&mut reader))?;
    reader.end()?;
    Ok(value)
}

/// The fields of a witness file that say what it is, read before the rest
/// ([`WitnessFile::read`]); every other field is skipped.
#[derive(Deserialize)]
struct WitnessHead {
    schema: String,
    version: u32,
    report: DocumentHead,
}

/// A report's `schema` and `version`; its other fields are skipped.
#[derive(Deserialize)]
struct DocumentHead {
    schema: String,
    version: u32,
}

impl WitnessFile {
    /// Read and check a witness file.
    pub fn read(path: &Path) -> Result<Self, String> {
        let text = std::fs::read_to_string(path)
            .map_err(|error| format!("cannot read the witness `{}`: {error}", path.display()))?;
        let not_a_witness = |error: serde_json::Error| {
            format!(
                "`{}` is not a krust-fuzz witness file: {error}",
                path.display()
            )
        };
        // The schemas and versions first, of the file and of its report: a document of another
        // version may lack fields this version requires or hold fields it does not know, and
        // its version is what explains the refusal.
        let head: WitnessHead = read_deep(&text).map_err(not_a_witness)?;
        if head.schema != WITNESS_SCHEMA || head.version != WITNESS_VERSION {
            return Err(format!(
                "`{}` is a {} version {} document; this krust-fuzz reads {WITNESS_SCHEMA} \
                 version {WITNESS_VERSION}",
                path.display(),
                head.schema,
                head.version
            ));
        }
        if head.report.schema != REPORT_SCHEMA || head.report.version != REPORT_VERSION {
            return Err(format!(
                "`{}` holds a {} version {} report; this krust-fuzz reads {REPORT_SCHEMA} \
                 version {REPORT_VERSION}",
                path.display(),
                head.report.schema,
                head.report.version
            ));
        }
        let file: WitnessFile = read_deep(&text).map_err(not_a_witness)?;
        if file.report.witness().is_none() {
            return Err(format!(
                "`{}` records a campaign that found no witness",
                path.display()
            ));
        }
        Ok(file)
    }

    /// Write `campaign` and `report` as a witness file.
    pub fn write(
        path: &Path,
        campaign: &ResolvedCampaign,
        report: &FuzzReport,
    ) -> Result<(), String> {
        let file = WitnessFile {
            schema: WITNESS_SCHEMA.into(),
            version: WITNESS_VERSION,
            campaign: campaign.clone(),
            report: report.clone(),
        };
        let mut bytes = Vec::new();
        file.serialize(serde_stacker::Serializer::new(
            &mut serde_json::Serializer::new(&mut bytes),
        ))
        .map_err(|error| format!("cannot encode the witness file: {error}"))?;
        let text = String::from_utf8(bytes).expect("serde_json writes UTF-8");
        std::fs::write(path, text + "\n")
            .map_err(|error| format!("cannot write the witness `{}`: {error}", path.display()))
    }
}

/// The identity fields of `recorded` that `now` does not have, one sentence each, named by
/// their path in the report (`definitions[0].syntax-definition-digest`).
///
/// Every field of the report's identity is compared except nine, and `target-rule`'s name: the
/// proposers and the budget, which the replay sets itself (one explicit assignment, one case),
/// `options.shrink` (a replay does not shrink), the engine version, which covers the proposer and
/// generator code that chooses cases, `dictionary`, the dictionary proposer's parameters, which
/// only weigh its draws, `climb`, the climb proposer's parameters, which only choose its moves (the
/// condition records a climbing campaign asks for change no other field of a result),
/// `corpus`, the corpus proposer's parameters, which only choose its mutations, and `solve`,
/// the solve proposer's parameters, which only decide its queries, and `effective-constraints`,
/// the generation bounds narrowed to the program's syntax, which only bound what is drawn (each
/// case is still checked against the declared constraints, and the definitions, program and
/// overlay they derive from are compared). None of the code the last six describe runs when a
/// fixed assignment is replayed, so they cannot
/// change the replayed case. Of `target-rule`, only the id is compared: the rule is a function
/// of the definitions and the target, which are compared, and its name is read from the
/// catalog, whose source paths say where the definition was compiled (a definition compiled
/// again elsewhere names the same rule by the same id). (Replaying with the recorded proposers
/// instead would record a dictionary that chose nothing, and still no draw would differ.) Every
/// other field is an input of the replayed case's execution or of its assembly, so a difference
/// makes the replay another campaign.
pub fn identity_mismatches(recorded: &ReportIdentity, now: &ReportIdentity) -> Vec<String> {
    let comparable = |identity: &ReportIdentity| {
        let mut identity = identity.clone();
        identity.proposers = ProposerConfig::default();
        identity.budget = Budget::Cases(0);
        identity.options.shrink = true;
        identity.engine_version = 0;
        identity.dictionary = None;
        identity.climb = None;
        identity.corpus = None;
        identity.solve = None;
        identity.effective_constraints = Vec::new();
        let mut value = serde_json::to_value(identity).unwrap_or(serde_json::Value::Null);
        // Of `target-rule`, only the id: its name (kind, label, source paths and references)
        // is read from the definition's catalog, whose source paths name where the definition
        // was compiled, not what it is.
        if let Some(rule) = value
            .get_mut("target-rule")
            .and_then(serde_json::Value::as_object_mut)
        {
            rule.remove("name");
        }
        value
    };
    let mut mismatches = Vec::new();
    differ(&comparable(recorded), &comparable(now), "", &mut mismatches);
    mismatches
}

/// Append to `out` every leaf at which `recorded` and `now` differ, under `path`.
fn differ(
    recorded: &serde_json::Value,
    now: &serde_json::Value,
    path: &str,
    out: &mut Vec<String>,
) {
    use serde_json::Value;
    match (recorded, now) {
        (Value::Object(recorded), Value::Object(now)) => {
            let keys: std::collections::BTreeSet<&String> =
                recorded.keys().chain(now.keys()).collect();
            for key in keys {
                let child = if path.is_empty() {
                    key.clone()
                } else {
                    format!("{path}.{key}")
                };
                differ(
                    recorded.get(key).unwrap_or(&Value::Null),
                    now.get(key).unwrap_or(&Value::Null),
                    &child,
                    out,
                );
            }
        }
        (Value::Array(recorded_items), Value::Array(now_items))
            if recorded_items.len() == now_items.len() =>
        {
            for (index, (recorded, now)) in recorded_items.iter().zip(now_items).enumerate() {
                differ(recorded, now, &format!("{path}[{index}]"), out);
            }
        }
        _ if recorded != now => {
            out.push(format!(
                "{path}: the witness has {recorded}, the replay {now}"
            ));
        }
        _ => {}
    }
}

/// The result of replaying one recorded witness case.
pub struct CaseReplay {
    /// `first` or `shrunk`.
    pub which: &'static str,
    /// The differences from the recorded case; empty when it reproduced.
    pub differences: Vec<String>,
    /// The replay's report.
    pub report: FuzzReport,
}

/// The result of a replay.
pub struct Replay {
    /// The identity mismatches, which a forced replay ran despite.
    pub mismatches: Vec<String>,
    /// One entry per recorded witness case; empty when the replay was refused.
    pub cases: Vec<CaseReplay>,
}

/// Replay `file`'s witness cases on `loaded` (ARCHITECTURE 9.4).
pub fn replay(
    file: &WitnessFile,
    loaded: &LoadedCampaign,
    force: bool,
    thread_stack_size: u64,
) -> Result<Replay, String> {
    let witness = file
        .report
        .witness()
        .ok_or("the witness file records no witness")?;
    let recorded = [
        ("first", Some(&witness.first)),
        ("shrunk", witness.shrunk.as_ref()),
    ];
    let mut options = loaded.resolved.options.clone();
    options.shrink = false;
    let mut cases = Vec::new();
    let mut mismatches = None;
    for (which, case) in recorded {
        let Some(case) = case else { continue };
        let proposers = ProposerConfig {
            anchors_first: false,
            explicit: vec![
                case.holes
                    .iter()
                    .map(|hole| (hole.name.clone(), hole.value.clone()))
                    .collect(),
            ],
            weights: std::collections::BTreeMap::new(),
        };
        let spec = loaded.spec(proposers, options.clone(), thread_stack_size);
        let mut campaign = Campaign::new(spec)
            .map_err(|error| format!("the replayed campaign is refused: {error}"))?;
        if mismatches.is_none() {
            // A campaign with no case reports the identity without running anything.
            let identity = campaign.run(Budget::Cases(0), None).identity;
            let found = identity_mismatches(&file.report.identity, &identity);
            if !found.is_empty() && !force {
                return Ok(Replay {
                    mismatches: found,
                    cases: Vec::new(),
                });
            }
            mismatches = Some(found);
        }
        let report = campaign.run(Budget::Cases(1), None);
        let differences = differences(case, &report);
        cases.push(CaseReplay {
            which,
            differences,
            report,
        });
    }
    Ok(Replay {
        mismatches: mismatches.unwrap_or_default(),
        cases,
    })
}

/// How the replay's report differs from the recorded witness case.
fn differences(recorded: &WitnessCase, report: &FuzzReport) -> Vec<String> {
    let Some(witness) = report.witness() else {
        let classes = report
            .totals
            .classes
            .keys()
            .map(crate::serde_name)
            .collect::<Vec<_>>()
            .join(", ");
        return vec![format!(
            "the replay found no witness: its case was {}",
            if classes.is_empty() {
                "not run"
            } else {
                &classes
            }
        )];
    };
    let replayed = &witness.first;
    let mut differences = Vec::new();
    if replayed.class != recorded.class {
        differences.push("the class differs".to_owned());
    }
    if replayed.holes != recorded.holes {
        differences.push("the hole values differ".to_owned());
    }
    for (index, (now, then)) in replayed.sides.iter().zip(&recorded.sides).enumerate() {
        if now.initial_configuration != then.initial_configuration {
            differences.push(format!("the initial configuration of side {index} differs"));
        }
        if now.final_configurations != then.final_configurations {
            differences.push(format!("the final configurations of side {index} differ"));
        }
        // A differential kill rests on how each leaf ended (an undefined step is no end), so
        // the halts are part of the reproduction.
        if now.halts != then.halts {
            differences.push(format!("the halts of side {index} differ"));
        }
    }
    if replayed.sides.len() != recorded.sides.len() {
        differences.push("the number of sides differs".to_owned());
    }
    if replayed.reaching != recorded.reaching
        || replayed.kill != recorded.kill
        || replayed.steps != recorded.steps
    {
        differences.push("where or how the target was reached differs".to_owned());
    }
    // Whether the program's run of every path is comparable is a fact of the witness case too
    // (FZ-COMPARABLE-A); absent from a witness recorded before it existed, which is not compared.
    if recorded.comparable.is_some() && replayed.comparable != recorded.comparable {
        differences.push("whether the run of every path is comparable differs".to_owned());
    }
    differences
}
