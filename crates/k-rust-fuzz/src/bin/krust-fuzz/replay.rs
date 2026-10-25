//! Witness files and `--replay` (ARCHITECTURE 9.4).
//!
//! A witness file holds the resolved campaign and the report that found the witness, or the
//! report of a campaign whose cases crashed (FZ-CRASH). Replaying it rebuilds the campaign's
//! specification from the recorded inputs, checks that the replay's identity is the witness's
//! (every field of the report's identity but the five that only choose cases or that the replay
//! sets itself; [`identity_mismatches`]), refuses on a mismatch unless forced, and runs each
//! recorded witness case, and each crash's first and shrunk values, as the campaign's only
//! explicit assignment. A witness case reproduces when the replay confirms a hit whose witness
//! case, with its class and final configurations, equals the recorded one. A crash reproduces
//! when the replay reports a crash of the same kind, side and stage, from a build with the same
//! debug assertions, at the same site when both sites are locations ([`crash_reproduced`]); a
//! crash of a confirmation or a comparability run re-enters through its own path, since the
//! replay of its values confirms them and judges their comparability as the campaign did.

use std::path::Path;

use k_rust_fuzz::{
    Budget, Campaign, ProposerConfig,
    report::{
        Comparability, CrashFinding, CrashHole, FuzzReport, REPORT_SCHEMA, REPORT_VERSION,
        ReportIdentity, SiteKind, WitnessCase,
    },
};
use serde::{Deserialize, Serialize};

use crate::campaign::{LoadedCampaign, ResolvedCampaign};

/// The witness file's `schema` field.
pub const WITNESS_SCHEMA: &str = "krust-fuzz-witness";

/// The witness file's `version` field. Version 2 (FZ-CRASH) holds a version-8 report, and is also
/// written for a campaign that found no witness but whose cases crashed.
pub const WITNESS_VERSION: u32 = 2;

/// A witness file: the campaign as resolved and the report that found the witness or the
/// crashes.
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
        if file.report.witness().is_none() && file.report.crashes.is_empty() {
            return Err(format!(
                "`{}` records a campaign that found no witness and no crash",
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

/// The result of replaying one recorded witness case or crash.
pub struct CaseReplay {
    /// `first witness`, `shrunk witness`, `crash 0 (first)`, `crash 0 (shrunk)`, ...
    pub which: String,
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
    let mut recorded: Vec<(String, Recorded<'_>, Assignment)> = Vec::new();
    let named = |holes: &[k_rust_fuzz::report::HoleValue]| {
        holes
            .iter()
            .map(|hole| (hole.name.clone(), hole.value.clone()))
            .collect::<Vec<_>>()
    };
    let crash_named = |holes: &[CrashHole]| {
        holes
            .iter()
            .map(|hole| (hole.name.clone(), hole.value.clone()))
            .collect::<Vec<_>>()
    };
    if let Some(witness) = file.report.witness() {
        recorded.push((
            "first witness".into(),
            Recorded::Witness(&witness.first),
            named(&witness.first.holes),
        ));
        if let Some(shrunk) = &witness.shrunk {
            recorded.push((
                "shrunk witness".into(),
                Recorded::Witness(shrunk),
                named(&shrunk.holes),
            ));
        }
    }
    for (index, crash) in file.report.crashes.0.iter().enumerate() {
        recorded.push((
            format!("crash {index} (first)"),
            Recorded::Crash(crash),
            crash_named(&crash.holes),
        ));
        if let Some(shrunk) = &crash.shrunk_holes {
            recorded.push((
                format!("crash {index} (shrunk)"),
                Recorded::Crash(crash),
                crash_named(shrunk),
            ));
        }
    }
    if recorded.is_empty() {
        return Err("the witness file records no witness and no crash".into());
    }
    let mut options = loaded.resolved.options.clone();
    options.shrink = false;
    let mut cases = Vec::new();
    let mut mismatches = None;
    for (which, case, values) in recorded {
        let proposers = ProposerConfig {
            anchors_first: false,
            explicit: vec![values.into_iter().collect()],
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
        let differences = match case {
            Recorded::Witness(case) => differences(case, &report),
            Recorded::Crash(crash) => crash_differences(crash, &report),
        };
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

/// The hole values of one replayed case, by hole name.
type Assignment = Vec<(String, k_rust_fuzz::Value)>;

/// What a replayed assignment was recorded as.
#[derive(Clone, Copy)]
enum Recorded<'a> {
    /// A witness case.
    Witness(&'a WitnessCase),
    /// A crash's first or shrunk values.
    Crash(&'a CrashFinding),
}

/// Whether the replay's crash `now` reproduces the recorded `then`: the same kind, side and
/// stage, from a build with the same debug assertions (whose panics a release build does not
/// raise), and the same site when both sites are locations (a site that is a message class
/// depends on no location, and a location the hook did not see falls back to one).
pub fn crash_reproduced(then: &CrashFinding, now: &CrashFinding) -> bool {
    let (then_signature, now_signature) = (&then.signature, &now.signature);
    then_signature.kind == now_signature.kind
        && then_signature.side == now_signature.side
        && then_signature.stage == now_signature.stage
        && then.debug_assertions == now.debug_assertions
        && (then_signature.site_kind != SiteKind::Location
            || now_signature.site_kind != SiteKind::Location
            || then_signature.site == now_signature.site)
}

/// How the replay's report differs from the recorded crash: empty when one of its crashes
/// reproduces it ([`crash_reproduced`]). The words blame no one: a crash that does not repeat
/// may have been decided by the host.
fn crash_differences(recorded: &CrashFinding, report: &FuzzReport) -> Vec<String> {
    crash_difference(recorded, &report.crashes.0)
}

/// [`crash_differences`] against the replay's crashes `now`. A crash that differs from the
/// recorded one only in the build's debug assertions is said to be the build profile's
/// difference, which a debug assertion's panic depends on.
fn crash_difference(recorded: &CrashFinding, now: &[CrashFinding]) -> Vec<String> {
    if now.iter().any(|crash| crash_reproduced(recorded, crash)) {
        return Vec::new();
    }
    let profile_only = now.iter().any(|crash| {
        crash.debug_assertions != recorded.debug_assertions
            && crash_reproduced(
                recorded,
                &CrashFinding {
                    debug_assertions: recorded.debug_assertions,
                    ..crash.clone()
                },
            )
    });
    if profile_only {
        return vec![format!(
            "the replay's build {} debug assertions and the recorded one {}: the crash repeated, \
             but a debug assertion's panic depends on the build profile, so the replay is not \
             comparable",
            if recorded.debug_assertions {
                "has no"
            } else {
                "has"
            },
            if recorded.debug_assertions {
                "had"
            } else {
                "had none"
            }
        )];
    }
    let found = if now.is_empty() {
        "the replay reported no crash".to_owned()
    } else {
        format!(
            "the replay reported other crashes ({})",
            now.iter()
                .map(|crash| crash.signature.site.clone())
                .collect::<Vec<_>>()
                .join("; ")
        )
    };
    vec![format!(
        "{found}: the crash did not repeat here; its determinism is unknown: a solver timeout \
         or a stack stop may have decided it"
    )]
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
    if !comparable_reproduced(recorded.comparable.as_ref(), replayed.comparable.as_ref()) {
        differences.push("whether the run of every path is comparable differs".to_owned());
    }
    differences
}

/// Whether the replayed comparable judgement reproduces the recorded one (FZ-COMPARABLE-A).
/// Only a judgement whose run was inside the determinism contract repeats
/// ([`Comparability::reproducible`]), so two such judgements must be equal; when either names a
/// clock, a solver `unknown`, a stop for lack of stack, an allowance refusal or a failed run, both
/// were made by a run that may end otherwise on another attempt (without `comparable-end`, the judgement
/// of a one-path witness is made outside the case, whose determinism does not cover it), and
/// they are not compared. A witness without the judgement (a differential or observer witness)
/// compares nothing.
fn comparable_reproduced(
    recorded: Option<&Comparability>,
    replayed: Option<&Comparability>,
) -> bool {
    match (recorded, replayed) {
        (None, _) => true,
        (Some(recorded), Some(replayed))
            if !recorded.reproducible() || !replayed.reproducible() =>
        {
            true
        }
        (Some(recorded), replayed) => replayed == Some(recorded),
    }
}

#[cfg(test)]
mod tests {
    use k_rust_fuzz::{
        exec::ComparableCondition as C,
        report::{
            Comparability, CrashDeterminism, CrashFinding, CrashKind, CrashPhase, CrashSide,
            CrashSignature, CrashStage, SiteKind,
        },
    };

    use super::{comparable_reproduced, crash_reproduced};

    fn crash(site_kind: SiteKind, site: &str) -> CrashFinding {
        CrashFinding {
            signature: CrashSignature {
                kind: CrashKind::Panic,
                side: CrashSide::Baseline,
                stage: CrashStage::Execute,
                site_kind,
                site: site.into(),
            },
            phase: CrashPhase::Case,
            message: "boom".into(),
            case: 3,
            holes: Vec::new(),
            shrunk_holes: None,
            count: 1,
            reproduced: Some(true),
            shrunk_reproduced: None,
            determinism: CrashDeterminism::Unknown,
            clock: false,
            debug_assertions: true,
            krun_command: None,
            program: None,
            config_vars: std::collections::BTreeMap::new(),
        }
    }

    /// (Fix round) A crash that differs from the recorded one in the build's debug assertions
    /// alone is said to be the profile's difference; one that does not repeat is said so without
    /// blame.
    #[test]
    fn a_debug_assertions_only_difference_names_the_profile() {
        let recorded = crash(SiteKind::Location, "k-rust/src/a.rs:1:2");
        let mut release = recorded.clone();
        release.debug_assertions = false;
        let said = super::crash_difference(&recorded, &[release]);
        assert_eq!(said.len(), 1);
        assert!(said[0].contains("debug assertions"), "{said:?}");
        assert!(said[0].contains("build profile"), "{said:?}");
        let none = super::crash_difference(&recorded, &[]);
        assert!(
            none[0].starts_with("the replay reported no crash"),
            "{none:?}"
        );
        assert!(super::crash_difference(&recorded, std::slice::from_ref(&recorded)).is_empty());
    }

    /// A replayed crash reproduces a recorded one with the same kind, side, stage and debug
    /// assertions; the sites are compared only when both are locations.
    #[test]
    fn a_crash_reproduces_by_kind_side_stage_and_located_site() {
        let located = crash(SiteKind::Location, "k-rust/src/a.rs:1:2");
        assert!(crash_reproduced(&located, &located.clone()));
        let moved = crash(SiteKind::Location, "k-rust/src/a.rs:9:2");
        assert!(!crash_reproduced(&located, &moved));
        let message = crash(SiteKind::Message, "boom");
        assert!(crash_reproduced(&located, &message));
        assert!(crash_reproduced(&message, &located));
        let mut mutant = located.clone();
        mutant.signature.side = CrashSide::Mutant;
        assert!(!crash_reproduced(&located, &mutant));
        let mut judged = located.clone();
        judged.signature.stage = CrashStage::Judge;
        assert!(!crash_reproduced(&located, &judged));
        let mut release = located.clone();
        release.debug_assertions = false;
        assert!(!crash_reproduced(&located, &release));
        let mut error = located.clone();
        error.signature.kind = CrashKind::InternalError;
        assert!(!crash_reproduced(&located, &error));
    }

    fn judged(reasons: &[C]) -> Comparability {
        Comparability {
            holds: reasons.is_empty(),
            reasons: reasons.to_vec(),
        }
    }

    /// Judgements made inside the determinism contract must be equal; one that names a fact
    /// breaking determinism (a clock, a solver `unknown`, ...) is not compared, on either side
    /// (INT9 review S2).
    #[test]
    fn only_reproducible_comparable_judgements_are_compared() {
        let holds = judged(&[]);
        let bound = judged(&[C::WorkBound]);
        let clock = judged(&[C::Clock, C::WorkBound]);
        let unknown = judged(&[C::SmtUnknowns]);
        let failed = judged(&[C::RunFailed]);
        assert!(comparable_reproduced(Some(&holds), Some(&holds)));
        assert!(comparable_reproduced(Some(&bound), Some(&bound)));
        assert!(!comparable_reproduced(Some(&holds), Some(&bound)));
        assert!(!comparable_reproduced(Some(&bound), None));
        assert!(comparable_reproduced(Some(&clock), Some(&bound)));
        assert!(comparable_reproduced(Some(&holds), Some(&clock)));
        assert!(comparable_reproduced(Some(&unknown), Some(&holds)));
        assert!(comparable_reproduced(None, Some(&holds)));
        assert!(comparable_reproduced(Some(&failed), Some(&holds)));
        assert!(comparable_reproduced(Some(&holds), Some(&failed)));
    }
}
