//! Witness files and `--replay` (ARCHITECTURE 9.4).
//!
//! A witness file holds the resolved campaign and the report that found the witness. Replaying
//! it rebuilds the campaign's specification from the recorded inputs, checks that the replay's
//! identity is the witness's (the k-rust revision, each definition's execution digest and
//! rewrite order, the program digest, the path mode, the target and the hole overlay), refuses
//! on a mismatch unless forced, and runs each recorded witness case as the campaign's only
//! explicit assignment. A case reproduces when the replay confirms a hit whose witness case,
//! with its class and final configurations, equals the recorded one.

use std::path::Path;

use k_rust_fuzz::{
    Budget, Campaign, ProposerConfig,
    report::{DefinitionRole, FuzzReport, ReportIdentity, WitnessCase},
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

impl WitnessFile {
    /// Read and check a witness file.
    pub fn read(path: &Path) -> Result<Self, String> {
        let text = std::fs::read_to_string(path)
            .map_err(|error| format!("cannot read the witness `{}`: {error}", path.display()))?;
        let file: WitnessFile = serde_json::from_str(&text).map_err(|error| {
            format!(
                "`{}` is not a krust-fuzz witness file: {error}",
                path.display()
            )
        })?;
        if file.schema != WITNESS_SCHEMA || file.version != WITNESS_VERSION {
            return Err(format!(
                "`{}` is a {} version {} document; this krust-fuzz reads {WITNESS_SCHEMA} \
                 version {WITNESS_VERSION}",
                path.display(),
                file.schema,
                file.version
            ));
        }
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
        let text = serde_json::to_string(&file)
            .map_err(|error| format!("cannot encode the witness file: {error}"))?;
        std::fs::write(path, text + "\n")
            .map_err(|error| format!("cannot write the witness `{}`: {error}", path.display()))
    }
}

fn role(role: DefinitionRole) -> &'static str {
    match role {
        DefinitionRole::Baseline => "baseline",
        DefinitionRole::Mutant => "mutant",
    }
}

/// The identity fields of `recorded` that `now` does not have, one sentence each.
pub fn identity_mismatches(recorded: &ReportIdentity, now: &ReportIdentity) -> Vec<String> {
    let mut mismatches = Vec::new();
    let mut compare = |what: &str, recorded: &str, now: &str| {
        if recorded != now {
            mismatches.push(format!(
                "{what}: the witness has `{recorded}`, the replay `{now}`"
            ));
        }
    };
    compare(
        "k-rust revision",
        &recorded.k_rust_revision,
        &now.k_rust_revision,
    );
    let roles = |identity: &ReportIdentity| {
        identity
            .definitions
            .iter()
            .map(|definition| role(definition.role))
            .collect::<Vec<_>>()
            .join(", ")
    };
    compare("definitions", &roles(recorded), &roles(now));
    for (recorded, now) in recorded.definitions.iter().zip(&now.definitions) {
        let name = role(recorded.role);
        compare(
            &format!("execution digest of the {name}"),
            &recorded.execution_digest,
            &now.execution_digest,
        );
        compare(
            &format!("backend route of the {name}"),
            &recorded.route,
            &now.route,
        );
        compare(
            &format!("rewrite order of the {name}"),
            recorded
                .execution_rewrite_order_digest
                .as_deref()
                .unwrap_or("none"),
            now.execution_rewrite_order_digest
                .as_deref()
                .unwrap_or("none"),
        );
    }
    compare(
        "program digest",
        &recorded.program_digest,
        &now.program_digest,
    );
    let paths = |identity: &ReportIdentity| match identity.options.paths {
        k_rust_fuzz::PathMode::OnePath => "one-path",
        k_rust_fuzz::PathMode::AllPaths => "all-paths",
    };
    compare("path mode", paths(recorded), paths(now));
    compare("target digest", &recorded.target_digest, &now.target_digest);
    compare(
        "hole overlay digest",
        &recorded.overlay_digest,
        &now.overlay_digest,
    );
    mismatches
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
    differences
}
