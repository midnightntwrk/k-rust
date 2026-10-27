//! Witness files and `--replay` (ARCHITECTURE 9.4).
//!
//! A witness file holds the resolved campaign and the report that found the witness, or the
//! report of a campaign whose cases crashed (FZ-CRASH). Replaying it rebuilds the campaign's
//! specification from the recorded inputs, checks that the replay's identity is the witness's
//! (every field of the report's identity but those of [`IDENTITY_EXCLUSIONS`], which only choose
//! cases or which the replay sets itself; [`identity_mismatches`]), refuses on a mismatch unless
//! forced, and runs each recorded witness case, and each crash's first and shrunk values, as the
//! campaign's only explicit assignment. A witness case reproduces when the replay confirms a hit
//! whose witness, compared whole but for a documented few fields ([`differences`]), equals the
//! recorded one. A crash reproduces
//! when the replay reports a crash of the same kind, side and stage, from a build with the same
//! debug assertions, at the same site when both sites are locations ([`crash_reproduced`]); a
//! crash of a confirmation or a comparability run re-enters through its own path, since the
//! replay of its values confirms them and judges their comparability as the campaign did.

use std::path::Path;

use k_rust_fuzz::{
    Budget, Campaign, ProposerConfig,
    report::{
        Comparability, CrashFinding, CrashHole, FuzzReport, REPORT_SCHEMA, REPORT_VERSION,
        ReportIdentity, SiteKind, Witness, WitnessCase, WitnessSide,
    },
};
use serde::{Deserialize, Serialize};

use crate::campaign::{LoadedCampaign, ResolvedCampaign};

/// The witness file's `schema` field.
pub const WITNESS_SCHEMA: &str = "krust-fuzz-witness";

/// The witness file's `version` field. Version 2 (FZ-CRASH) holds a report of
/// [`REPORT_VERSION`] (8 when it came in, 9 since FZ-STATESET, 10 since FZ-REPLAY-WHOLE; the
/// report's own version refuses an older one), and is also written for a campaign that found no
/// witness but whose cases crashed.
pub const WITNESS_VERSION: u32 = 2;

/// Why a report older than version 9 is not replayed (FZ-STATESET): appended to its refusal.
/// It names only the runs version 9 moved to state sets, since the witness's own kind is not
/// read before the refusal: a differential case's sides were state sets before version 9 too.
const MODALITY_CHANGE: &str = concat!(
    " (since version 9 an all-paths rule or pattern target and the program's run of every ",
    "path that judges comparability run as state sets, which keep one leaf per distinct ",
    "configuration of a depth, where earlier versions ran them as path sets, and an ",
    "`at: any-state` pattern is matched against every reached state inside the run; so such a ",
    "witness's final configurations, steps and reaching leaf or configuration need not be what ",
    "this build reports; run the campaign again for a witness of this build)",
);

/// Why a version-9 report is not replayed (FZ-REPLAY-WHOLE): appended to its refusal.
const SOURCE_NAMES_CHANGE: &str = concat!(
    " (since version 10 the identity names the main module's file by its own name and records ",
    "the k-rust-fuzz build, and the report names every source location relative to that file, ",
    "so a version-9 witness's identity and rule names cannot be compared with this build's; run ",
    "the campaign again for a witness of this build)",
);

/// What a change of `identity.fuzz-revision` means (FZ-REPLAY-WHOLE fix round), appended to its
/// mismatch: the revision digests the sources byte for byte.
const FUZZ_REVISION_MISMATCH: &str = concat!(
    " (the sources of k-rust-fuzz or krs-unparse differ between the build that found the witness ",
    "and this one, a comment included, and their classification may differ: replay with the build ",
    "that found it, or pass --force, which exits 3 when every case reproduces)",
);

/// What a change of `identity.execution-modality` means for a replay (FZ-STATESET), appended
/// to that field's mismatch. Within version 9 the field is a function of the target and the
/// path mode, whose own mismatches come first, so it explains a mismatch only when a later
/// change re-derives a modality within one report version.
const MODALITY_MISMATCH: &str = concat!(
    " (the witness's runs reported their paths otherwise: a state set keeps one leaf per ",
    "distinct configuration of a depth and merges converging paths, a path set one leaf per ",
    "path, so the replayed case's leaves, steps and final configurations may differ)",
);

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
                 version {REPORT_VERSION}{}",
                path.display(),
                head.report.schema,
                head.report.version,
                match (head.report.schema == REPORT_SCHEMA, head.report.version) {
                    (true, ..9) => MODALITY_CHANGE,
                    (true, 9) => SOURCE_NAMES_CHANGE,
                    _ => "",
                }
            ));
        }
        let file: WitnessFile = read_deep(&text).map_err(not_a_witness)?;
        if file.report.witness().is_none() && file.report.crashes.is_empty() {
            return Err(format!(
                "`{}` records a campaign that found no witness and no crash",
                path.display()
            ));
        }
        if let Some(problem) = file.inconsistency() {
            return Err(format!(
                "`{}` is not a witness file this build wrote: {problem}",
                path.display()
            ));
        }
        Ok(file)
    }

    /// The first fact of the file that no campaign writes (FZ-REPLAY-WHOLE fix round X1, X2,
    /// S-B): a judgement that breaks its own invariant, a repaired witness without a filter, a
    /// crash's shrunk re-run without its shrunk values, or a campaign whose k-rust revision is not
    /// its report's. Such a file was edited, and no replay can certify what it says.
    fn inconsistency(&self) -> Option<String> {
        if self.campaign.k_rust_revision != self.report.identity.k_rust_revision {
            return Some(format!(
                "its campaign names k-rust {} and its report k-rust {}",
                self.campaign.k_rust_revision, self.report.identity.k_rust_revision
            ));
        }
        if let Some(witness) = self.report.witness() {
            if witness.repaired_from.is_some() && self.report.identity.filter.is_none() {
                return Some(
                    "its witness was repaired from a refused hit, but the campaign ran no \
                     witness filter, and only a filter repairs"
                        .to_owned(),
                );
            }
            let cases = std::iter::once(("first", &witness.first))
                .chain(witness.shrunk.iter().map(|shrunk| ("shrunk", shrunk)));
            for (which, case) in cases {
                if let Some(problem) = case.comparable.as_ref().and_then(judgement_problem) {
                    return Some(format!("its {which} case's `comparable` {problem}"));
                }
            }
        }
        for (index, crash) in self.report.crashes.0.iter().enumerate() {
            if crash.shrunk_reproduced.is_some() && crash.shrunk_holes.is_none() {
                return Some(format!(
                    "its crash {index} records a re-run of shrunk values it does not hold"
                ));
            }
        }
        None
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

/// The fields of the report's identity a replay does not compare, by their path in the report,
/// each with why it cannot change the replayed case ([`identity_mismatches`]). Every other field
/// is an input of the replayed case's execution, of its assembly or of its judgement, so a
/// difference makes the replay another campaign.
pub const IDENTITY_EXCLUSIONS: [(&str, &str); 10] = [
    (
        "proposers",
        "the replay sets its own: one explicit assignment",
    ),
    ("budget", "the replay sets its own: one case"),
    ("options.shrink", "a replay does not shrink"),
    (
        "dictionary",
        "the dictionary proposer's parameters only weigh its draws",
    ),
    (
        "climb",
        "the climb proposer's parameters only choose its moves (the condition records a climbing \
         campaign asks for change no other field of a result)",
    ),
    (
        "corpus",
        "the corpus proposer's parameters only choose its mutations",
    ),
    (
        "solve",
        "the solve proposer's parameters only decide its queries",
    ),
    (
        "effective-constraints",
        "the generation bounds narrowed to the program's syntax only bound what is drawn (each \
         case is still checked against the declared constraints, and the definitions, program and \
         overlay they derive from are compared)",
    ),
    (
        "parse-diagnostic-work",
        "the parser's diagnostic work limit changes only the text of parse diagnostics, which no \
         witness case or crash signature holds",
    ),
    (
        "filter",
        "the client's witness filter only chose which cases became witnesses: a confirmed witness \
         hits without it, and the replay runs none (the command notes a recorded one)",
    ),
];

/// The identity fields of `recorded` that `now` does not have, one sentence each, named by
/// their path in the report (`definitions[0].syntax-definition-digest`).
///
/// Every field is compared except those of [`IDENTITY_EXCLUSIONS`]: none of the code they
/// describe runs when a fixed assignment is replayed, so they cannot change the replayed case.
/// (Replaying with the recorded proposers instead would record a dictionary that chose nothing,
/// and still no draw would differ.) The identity is destructured field by field, so a field added
/// to it must be decided here. `target-rule` is compared whole: its name is a function of the
/// definitions and the target, its sources named relative to the main module's file
/// (FZ-REPLAY-WHOLE S1). `execution-modality` is compared too (FZ-STATESET): its mismatch also
/// says what a modality change means for the replayed case.
pub fn identity_mismatches(recorded: &ReportIdentity, now: &ReportIdentity) -> Vec<String> {
    let comparable = |identity: &ReportIdentity| {
        // Every field is named, so that a new one must be put on one side or the other.
        let ReportIdentity {
            // Compared: inputs of the replayed case's execution, assembly or judgement.
            k_rust_revision: _,
            fuzz_revision: _,
            definitions: _,
            program_digest: _,
            overlay_digest: _,
            target_digest: _,
            target_rule: _,
            options: _,
            execution_modality: _,
            bounds: _,
            caps: _,
            rejection_cap: _,
            seed: _,
            thread_stack_size: _,
            solver: _,
            // The engine version names the code that chose the cases; a replay runs a fixed
            // assignment, but a witness of another engine version is another build's (S-B).
            engine_version: _,
            // Not compared: IDENTITY_EXCLUSIONS.
            parse_diagnostic_work: _,
            proposers: _,
            budget: _,
            dictionary: _,
            climb: _,
            corpus: _,
            solve: _,
            effective_constraints: _,
            filter: _,
        } = identity;
        let mut value = serde_json::to_value(identity).unwrap_or(serde_json::Value::Null);
        for (path, _) in IDENTITY_EXCLUSIONS {
            let mut parent = &mut value;
            let mut keys = path.split('.').peekable();
            while let Some(key) = keys.next() {
                if keys.peek().is_none() {
                    if let Some(object) = parent.as_object_mut() {
                        object.remove(key);
                    }
                } else if let Some(child) = parent.get_mut(key) {
                    parent = child;
                } else {
                    break;
                }
            }
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
            let meaning = if path.starts_with("execution-modality") {
                MODALITY_MISMATCH
            } else if path == "fuzz-revision" {
                FUZZ_REVISION_MISMATCH
            } else {
                ""
            };
            out.push(format!(
                "{path}: the witness has {recorded}, the replay {now}{meaning}"
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
    /// What the replay did not compare, and why (a judgement made outside the determinism
    /// contract).
    pub notes: Vec<String>,
    /// The replay's report.
    pub report: FuzzReport,
}

/// The result of a replay.
pub struct Replay {
    /// The identity mismatches, which a forced replay ran despite.
    pub mismatches: Vec<String>,
    /// One entry per recorded witness case; empty when the replay was refused.
    pub cases: Vec<CaseReplay>,
    /// How the report's fields fixed before any case differ from the replay's
    /// ([`static_differences`]); empty when they reproduced.
    pub static_differences: Vec<String>,
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
            Recorded::Witness(WhichCase::First),
            named(&witness.first.holes),
        ));
        if let Some(shrunk) = &witness.shrunk {
            recorded.push((
                "shrunk witness".into(),
                Recorded::Witness(WhichCase::Shrunk),
                named(&shrunk.holes),
            ));
        }
    }
    for (index, crash) in file.report.crashes.0.iter().enumerate() {
        recorded.push((
            format!("crash {index} (first)"),
            Recorded::Crash(crash, WhichCase::First),
            crash_named(&crash.holes),
        ));
        if let Some(shrunk) = &crash.shrunk_holes {
            recorded.push((
                format!("crash {index} (shrunk)"),
                Recorded::Crash(crash, WhichCase::Shrunk),
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
    let mut setup: Option<FuzzReport> = None;
    let mut static_differences_found: Option<Vec<String>> = None;
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
            // A campaign with no case reports the identity, and the fields fixed before any
            // case, without running anything.
            let before_any_case = campaign.run(Budget::Cases(0), None);
            let found = identity_mismatches(&file.report.identity, &before_any_case.identity)
                .into_iter()
                .map(|mismatch| explained(mismatch, file, loaded))
                .collect::<Vec<_>>();
            if !found.is_empty() && !force {
                return Ok(Replay {
                    mismatches: found,
                    cases: Vec::new(),
                    static_differences: Vec::new(),
                });
            }
            mismatches = Some(found);
            setup = Some(before_any_case);
        }
        let report = campaign.run(Budget::Cases(1), None);
        let mut notes = Vec::new();
        let differences = match case {
            Recorded::Witness(which) => {
                let witness = file
                    .report
                    .witness()
                    .ok_or("the witness file records no witness")?;
                differences(witness, which, &report, &mut notes)
            }
            Recorded::Crash(crash, which) => crash_differences(crash, which, &report),
        };
        if static_differences_found.is_none()
            && let Some(setup) = &setup
        {
            static_differences_found = Some(static_differences(&file.report, setup, &report));
        }
        cases.push(CaseReplay {
            which,
            differences,
            notes,
            report,
        });
    }
    Ok(Replay {
        mismatches: mismatches.unwrap_or_default(),
        cases,
        static_differences: static_differences_found.unwrap_or_default(),
    })
}

/// How the recorded report's fields that are fixed before any case differ from the replay's
/// (FZ-REPLAY-WHOLE fix round S-B): `definition-findings`, `sort-overrides` and `normal-end`, a
/// function of the definitions, the holes and the options, which the identity compares; the
/// warnings the campaign starts with (`setup`'s: narrowed holes, the rule graph's, the findings'),
/// which must open the recorded warnings in order; and `load-records`, the records of the
/// definitions' loads, which every case run reports alike (`first`'s, a replayed case's report).
///
/// Every other field of the report depends on the whole campaign (its cases, their order, the
/// budget), which a replay of the recorded cases does not repeat, so it is not certified: the
/// totals, the statement, the warnings the cases added, `incidental`, `client-refusals`,
/// `engine-defects`, `crashes-omitted`, and the outcome beyond its witness cases and crashes.
/// The report is destructured, so that a new field must be decided here.
fn static_differences(
    recorded: &FuzzReport,
    setup: &FuzzReport,
    first: &FuzzReport,
) -> Vec<String> {
    let FuzzReport {
        // Compared before any case ran (`identity_mismatches`), or replayed case by case.
        schema: _,
        version: _,
        identity: _,
        outcome: _,
        crashes: _,
        // Compared here.
        definition_findings,
        sort_overrides,
        normal_end,
        warnings,
        load_records,
        // Facts of the whole campaign, which a replay of its recorded cases does not repeat.
        totals: _,
        incidental: _,
        crashes_omitted: _,
        client_refusals: _,
        engine_defects: _,
    } = recorded;
    let mut differences = Vec::new();
    if *definition_findings != setup.definition_findings {
        differences.push("the definition findings differ".to_owned());
    }
    if *sort_overrides != setup.sort_overrides {
        differences.push("the sort overrides differ".to_owned());
    }
    if *normal_end != first.normal_end {
        differences.push("the normal ends differ".to_owned());
    }
    if !warnings.starts_with(&setup.warnings) {
        differences.push(
            "the warnings do not open with the ones the campaign starts with (narrowed holes, the \
             rule graph's, the definition findings')"
                .to_owned(),
        );
    }
    fn set(
        records: &[k_rust_fuzz::report::LoadRecord],
    ) -> std::collections::BTreeSet<&k_rust_fuzz::report::LoadRecord> {
        records.iter().collect()
    }
    if set(load_records) != set(&first.load_records) {
        differences.push("the load records differ".to_owned());
    }
    differences
}

/// `mismatch` with what a digest's difference means where only the replay knows it: a program
/// digest covers the program's name, start sort and text and the configuration-variable
/// bindings, which two hexadecimal digests do not show (FZ-REPLAY-WHOLE N3).
fn explained(mismatch: String, file: &WitnessFile, loaded: &LoadedCampaign) -> String {
    if !mismatch.starts_with("program-digest:") {
        return mismatch;
    }
    let program = |campaign: &ResolvedCampaign| {
        campaign.program.as_ref().map_or_else(
            || "no program file".to_owned(),
            |program| {
                format!(
                    "`{}` (start sort {}, read from `{}`)",
                    program.name,
                    program.sort,
                    program.path.display()
                )
            },
        )
    };
    format!(
        "{mismatch}: the program's name, start sort, text or configuration-variable bindings are \
         not the recorded ones; the witness ran {}, the replay runs {}",
        program(&file.campaign),
        program(&loaded.resolved)
    )
}

/// The hole values of one replayed case, by hole name.
type Assignment = Vec<(String, k_rust_fuzz::Value)>;

/// What a replayed assignment was recorded as.
#[derive(Clone, Copy)]
enum Recorded<'a> {
    /// A witness case.
    Witness(WhichCase),
    /// A crash's first or shrunk values.
    Crash(&'a CrashFinding, WhichCase),
}

/// Whether the replay's crash `now` reproduces the recorded `then`: the same kind, side and
/// stage, from a build with the same debug assertions (whose panics a release build does not
/// raise), and the same site when both sites are locations or both are causes (a site that is a
/// message class depends on no location, and a location the hook did not see falls back to one;
/// an internal halt's cause is typed, so it is compared).
pub fn crash_reproduced(then: &CrashFinding, now: &CrashFinding) -> bool {
    let (then_signature, now_signature) = (&then.signature, &now.signature);
    let sites_compared = then_signature.site_kind == now_signature.site_kind
        && matches!(
            then_signature.site_kind,
            SiteKind::Location | SiteKind::Cause
        );
    then_signature.kind == now_signature.kind
        && then_signature.side == now_signature.side
        && then_signature.stage == now_signature.stage
        && then.debug_assertions == now.debug_assertions
        && (!sites_compared || then_signature.site == now_signature.site)
}

/// How the replay's report differs from the recorded crash, replayed on its `which` values:
/// empty when one of its crashes reproduces it ([`crash_reproduced`]) and holds what the record
/// says the values give (FZ-REPLAY-WHOLE fix round X1). The words blame no one: a crash that does
/// not repeat may have been decided by the host.
///
/// The record is destructured, so that a field added to it must be decided here:
/// - `signature` and `debug-assertions` decide whether the crash repeated;
/// - on the replay of the first values, `holes`, the instantiated `program` and `config-vars`
///   and the `krun-command` that re-enters the crash are compared with the reproducing crash's:
///   they are functions of the values, the definition and the options, which the identity
///   compares, so only an edit makes them differ; and so is `message` when the site is a
///   location or a cause (the typed failure's text of the same run); on the replay of the shrunk
///   values, their `holes` are compared, the others describing the first values;
/// - `phase`, `case`, `count`, `reproduced`, `shrunk-reproduced`, `determinism` and `clock`
///   record the campaign's search (where it met the crash, how often, its own re-runs and its
///   clock), which a replay of the values does not repeat, and `shrunk-holes` is the result of
///   the campaign's shrinking, which a replay does not run: none is certified, and the shrunk
///   values are re-run when present.
fn crash_differences(
    recorded: &CrashFinding,
    which: WhichCase,
    report: &FuzzReport,
) -> Vec<String> {
    let mut differences = crash_difference(recorded, &report.crashes.0);
    if !differences.is_empty() {
        return differences;
    }
    let Some(now) = report
        .crashes
        .0
        .iter()
        .find(|crash| crash_reproduced(recorded, crash))
    else {
        return differences;
    };
    let CrashFinding {
        signature,
        debug_assertions: _,
        holes,
        shrunk_holes,
        program,
        config_vars,
        krun_command,
        message,
        phase: _,
        case: _,
        count: _,
        reproduced: _,
        shrunk_reproduced: _,
        determinism: _,
        clock: _,
    } = recorded;
    let mut differ = |differs: bool, what: &str| {
        if differs {
            differences.push(what.to_owned());
        }
    };
    match which {
        WhichCase::First => {
            differ(now.holes != *holes, "the hole values differ");
            differ(
                now.program != *program,
                "the instantiated program differs from the one the hole values give",
            );
            differ(
                now.config_vars != *config_vars,
                "the instantiated configuration variables differ from the ones the hole values \
                 give",
            );
            differ(
                now.krun_command != *krun_command,
                "the krun line (`krun-command`) differs from the one the replayed crash gives",
            );
            differ(
                matches!(signature.site_kind, SiteKind::Location | SiteKind::Cause)
                    && now.message != *message,
                "the message differs from the replayed crash's",
            );
        }
        WhichCase::Shrunk => {
            differ(
                shrunk_holes.as_ref() != Some(&now.holes),
                "the shrunk hole values differ",
            );
        }
    }
    differences
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

/// How the replay's report differs from the recorded witness case `which` of `recorded`: empty
/// when it reproduced.
///
/// The whole witness is compared, every field of [`Witness`], [`WitnessCase`] and
/// [`WitnessSide`] being destructured, so that a field added to any of them must be decided here
/// (FZ-REPLAY-WHOLE). A witness file is evidence, and a field a person or a program edited is one
/// the replay must not certify. Every field is a function of the recorded inputs, which the
/// identity check compares, and of the replayed case's own runs, with these exceptions:
/// - `shrunk` is the second recorded case, which has its own replay;
/// - `repaired-from` is the refused hit a client's witness filter repaired `first` from: it
///   records the campaign's search, and the replay runs no filter ([`identity_mismatches`]), so
///   nothing it runs can give it;
/// - `krun-command` and `mutant-krun-command` re-run the shrunk case when there is one, so they
///   are compared in the replay of the case they re-run;
/// - `comparable` is compared only when both judgements were made inside the determinism
///   contract ([`comparable_reproduced`]).
///
/// `undefined-rules` is compared whether or not the witness records it: an absent list is one
/// whose every entry is `null`, which is how the report writes it.
fn differences(
    recorded: &Witness,
    which: WhichCase,
    report: &FuzzReport,
    notes: &mut Vec<String>,
) -> Vec<String> {
    let Witness {
        label,
        first,
        shrunk,
        clean_leaf_facts,
        krun_command,
        mutant_krun_command,
        repaired_from: _,
    } = recorded;
    let (case, krun_lines_compared) = match (which, shrunk) {
        (WhichCase::Shrunk, Some(shrunk)) => (shrunk, true),
        (WhichCase::Shrunk, None) => {
            return vec!["the witness records no shrunk case".to_owned()];
        }
        (WhichCase::First, shrunk) => (first, shrunk.is_none()),
    };
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
    let mut differences = Vec::new();
    let mut differ = |differs: bool, what: String| {
        if differs {
            differences.push(what);
        }
    };
    differ(
        witness.label != *label,
        format!(
            "the label differs: the witness has `{}`, the replay `{}`",
            crate::serde_name(label),
            crate::serde_name(&witness.label)
        ),
    );
    differ(
        witness.clean_leaf_facts != *clean_leaf_facts,
        "the clean-leaf facts differ".to_owned(),
    );
    if krun_lines_compared {
        differ(
            witness.krun_command != *krun_command,
            "the krun line (`krun-command`) differs from the one the replayed case gives"
                .to_owned(),
        );
        differ(
            witness.mutant_krun_command != *mutant_krun_command,
            "the mutant's krun line (`mutant-krun-command`) differs from the one the replayed \
             case gives"
                .to_owned(),
        );
    }
    differences.extend(case_differences(case, &witness.first, notes));
    differences
}

/// Which recorded witness case a replay re-runs.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum WhichCase {
    /// The first confirmed witness case.
    First,
    /// The shrunk witness case.
    Shrunk,
}

/// How the replayed witness case `replayed` differs from the recorded `recorded` ([`differences`]).
fn case_differences(
    recorded: &WitnessCase,
    replayed: &WitnessCase,
    notes: &mut Vec<String>,
) -> Vec<String> {
    let WitnessCase {
        holes,
        program,
        config_vars,
        class,
        sides,
        reaching,
        kill,
        steps,
        comparable,
    } = recorded;
    let mut differences = Vec::new();
    let mut differ = |differs: bool, what: String| {
        if differs {
            differences.push(what);
        }
    };
    differ(replayed.class != *class, "the class differs".to_owned());
    differ(
        replayed.holes != *holes,
        "the hole values differ".to_owned(),
    );
    differ(
        replayed.program != *program,
        "the instantiated program differs from the one the hole values give".to_owned(),
    );
    differ(
        replayed.config_vars != *config_vars,
        "the instantiated configuration variables differ from the ones the hole values give"
            .to_owned(),
    );
    differ(
        replayed.sides.len() != sides.len(),
        "the number of sides differs".to_owned(),
    );
    for (index, (then, now)) in sides.iter().zip(&replayed.sides).enumerate() {
        let WitnessSide {
            role,
            initial_configuration,
            final_configurations,
            halts,
            undefined_rules,
            work,
        } = then;
        differ(
            now.role != *role,
            format!("the role of side {index} differs"),
        );
        differ(
            now.initial_configuration != *initial_configuration,
            format!("the initial configuration of side {index} differs"),
        );
        differ(
            now.final_configurations != *final_configurations,
            format!("the final configurations of side {index} differ"),
        );
        // A differential kill rests on how each leaf ended (an undefined step is no end), so
        // the halts are part of the reproduction.
        differ(
            now.halts != *halts,
            format!("the halts of side {index} differ"),
        );
        // A client judges an undefined step by its rule (FZ-COMPARABLE-B). The report leaves the
        // list out when no leaf names a rule, so an absent list reads as all `null`.
        let named = |rules: &[Option<String>]| rules.iter().any(Option::is_some);
        differ(
            (named(undefined_rules) || named(&now.undefined_rules))
                && now.undefined_rules != *undefined_rules,
            format!("the undefined-step rules of side {index} differ"),
        );
        // The states the side's run visited: a function of the run inside the determinism
        // contract, which a client's work budget reads.
        differ(
            now.work != *work,
            format!(
                "the work of side {index} differs: the witness has {}, the replay {}",
                shown(*work),
                shown(now.work)
            ),
        );
    }
    differ(
        replayed.reaching != *reaching,
        "where the target was reached differs (the reaching side, leaf, step or configuration)"
            .to_owned(),
    );
    differ(
        replayed.kill != *kill,
        "the kind of kill differs".to_owned(),
    );
    differ(
        replayed.steps != *steps,
        format!(
            "the step count differs: the witness has {}, the replay {}",
            shown(*steps),
            shown(replayed.steps)
        ),
    );
    match comparable_reproduced(comparable.as_ref(), replayed.comparable.as_ref()) {
        Judgement::Equal => {}
        Judgement::Differs => {
            differences.push("whether the run of every path is comparable differs".to_owned());
        }
        Judgement::NotCompared => notes.push(
            "the `comparable` judgement was not compared: one of the two names a fact outside \
             the determinism contract (a clock, a solver `unknown`, a stack stop, an allowance \
             refusal, a failed run or a crash), so another run may judge otherwise"
                .to_owned(),
        ),
    }
    differences
}

/// A count of the witness for a message: the number, or `none`.
fn shown(count: Option<u64>) -> String {
    count.map_or_else(|| "none".to_owned(), |count| count.to_string())
}

/// How a replayed comparable judgement stands against the recorded one.
#[derive(Debug, PartialEq, Eq)]
enum Judgement {
    /// Equal, or neither case has one.
    Equal,
    /// One case has a judgement the other lacks, or two reproducible judgements differ.
    Differs,
    /// Not compared: one of the two names a fact outside the determinism contract.
    NotCompared,
}

/// Whether the replayed comparable judgement reproduces the recorded one (FZ-COMPARABLE-A).
/// Whether a judgement exists is a function of the target kind (a rule or pattern witness has
/// one, a differential or observer witness none), which the identity compares, so a judgement
/// on one side only is a difference (FZ-REPLAY-WHOLE fix round X2). Only a judgement whose run
/// was inside the determinism contract repeats ([`Comparability::reproducible`]), so two such
/// judgements must be equal; when either names a clock, a solver `unknown`, a stop for lack of
/// stack, an allowance refusal, a failed run or a crash, it was made by a run that may end
/// otherwise on another attempt (without `comparable-end`, the judgement of a one-path witness
/// is made outside the case, whose determinism does not cover it), and they are not compared,
/// which the replay says. A recorded judgement that breaks its own invariant is refused when the
/// file is read ([`judgement_problem`]). Every field is compared, the hooks the conditions name
/// (UNNAMED-HOOK) included: they are a function of the same run, and an absent map is an empty
/// one. The destructuring is exhaustive, so a field added to [`Comparability`] must be decided
/// here.
fn comparable_reproduced(
    recorded: Option<&Comparability>,
    replayed: Option<&Comparability>,
) -> Judgement {
    match (recorded, replayed) {
        (None, None) => Judgement::Equal,
        (None, Some(_)) | (Some(_), None) => Judgement::Differs,
        (Some(recorded), Some(replayed))
            if !recorded.reproducible() || !replayed.reproducible() =>
        {
            Judgement::NotCompared
        }
        (Some(recorded), Some(replayed)) => {
            let Comparability {
                holds,
                reasons,
                hooks,
            } = recorded;
            if *holds == replayed.holds && *reasons == replayed.reasons && *hooks == replayed.hooks
            {
                Judgement::Equal
            } else {
                Judgement::Differs
            }
        }
    }
}

/// What makes `judgement` one no campaign writes, if anything: it holds exactly when it names no
/// condition, names its conditions in their order, each once, and names hooks only for conditions
/// it names (`report::Comparability`'s invariant).
fn judgement_problem(judgement: &Comparability) -> Option<String> {
    let Comparability {
        holds,
        reasons,
        hooks,
    } = judgement;
    if *holds != reasons.is_empty() {
        return Some(format!(
            "says it holds ({holds}) while naming {} failed {}",
            reasons.len(),
            if reasons.len() == 1 {
                "condition"
            } else {
                "conditions"
            }
        ));
    }
    if !reasons.windows(2).all(|pair| pair[0] < pair[1]) {
        return Some("names its conditions out of their order or twice".to_owned());
    }
    if let Some(condition) = hooks.keys().find(|condition| !reasons.contains(condition)) {
        return Some(format!(
            "names hooks for `{}`, a condition it does not name",
            condition.name()
        ));
    }
    None
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
            hooks: std::collections::BTreeMap::new(),
        }
    }

    /// Judgements made inside the determinism contract must be equal; one that names a fact
    /// breaking determinism (a clock, a solver `unknown`, ...) is not compared, on either side
    /// (INT9 review S2), and the replay says so; a judgement on one side only differs, since the
    /// target kind decides whether one exists (FZ-REPLAY-WHOLE fix round X2).
    #[test]
    fn only_reproducible_comparable_judgements_are_compared() {
        use super::Judgement::{Differs, Equal, NotCompared};
        let holds = judged(&[]);
        let bound = judged(&[C::WorkBound]);
        let clock = judged(&[C::Clock, C::WorkBound]);
        let unknown = judged(&[C::SmtUnknowns]);
        let failed = judged(&[C::RunFailed]);
        for (recorded, replayed, expected) in [
            (Some(&holds), Some(&holds), Equal),
            (Some(&bound), Some(&bound), Equal),
            (None, None, Equal),
            (Some(&holds), Some(&bound), Differs),
            (Some(&bound), None, Differs),
            (None, Some(&holds), Differs),
            (Some(&clock), Some(&bound), NotCompared),
            (Some(&holds), Some(&clock), NotCompared),
            (Some(&unknown), Some(&holds), NotCompared),
            (Some(&failed), Some(&holds), NotCompared),
            (Some(&holds), Some(&failed), NotCompared),
        ] {
            assert_eq!(
                comparable_reproduced(recorded, replayed),
                expected,
                "{recorded:?} {replayed:?}"
            );
        }
    }

    /// A judgement that breaks its own invariant is no campaign's (X2).
    #[test]
    fn a_judgement_that_breaks_its_invariant_is_refused() {
        use super::judgement_problem;
        assert_eq!(judgement_problem(&judged(&[C::WorkBound])), None);
        let mut forged = judged(&[C::Clock]);
        forged.holds = true;
        assert!(judgement_problem(&forged).is_some());
        let mut empty = judged(&[]);
        empty.holds = false;
        assert!(judgement_problem(&empty).is_some());
        assert!(judgement_problem(&judged(&[C::WorkBound, C::Clock])).is_some());
    }

    /// (UNNAMED-HOOK, review S3) A reproducible judgement's hooks are compared exactly: a replay
    /// that names other hooks, or names some where the recorded one named none, differs.
    #[test]
    fn a_changed_set_of_hooks_does_not_reproduce() {
        use k_rust_fuzz::report::{ReasonHook, ReasonHooks};
        let named = |hooks: &[ReasonHook]| {
            let mut judged = judged(&[C::Halt]);
            if let Some(hooks) = ReasonHooks::of(&hooks.iter().cloned().collect()) {
                judged.hooks.insert(C::Halt, hooks);
            }
            judged
        };
        let none = named(&[]);
        let shl = named(&[ReasonHook::unsupported("INT.shl")]);
        let pow = named(&[ReasonHook::unsupported("INT.pow")]);
        use super::Judgement::{Differs, Equal};
        assert_eq!(comparable_reproduced(Some(&shl), Some(&shl)), Equal);
        assert_eq!(comparable_reproduced(Some(&none), Some(&none)), Equal);
        assert_eq!(comparable_reproduced(Some(&shl), Some(&pow)), Differs);
        assert_eq!(comparable_reproduced(Some(&none), Some(&shl)), Differs);
        assert_eq!(comparable_reproduced(Some(&shl), Some(&none)), Differs);
    }
}
