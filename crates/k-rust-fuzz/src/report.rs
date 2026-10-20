//! The campaign report: one canonical JSON document with `schema: "krust-fuzz-report"` and a
//! `version` (ARCHITECTURE 9.3).
//!
//! The report is canonical: its fields serialize in declaration order, every map is ordered,
//! integers and byte strings in values are text, and no float occurs, so equal reports are equal
//! bytes ([`FuzzReport::to_canonical_json`]). A campaign's report is a function of its
//! specification, budget, seed, the k-rust revision and [`crate::ENGINE_VERSION`]
//! (ARCHITECTURE 5.4).

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

use crate::{
    exec::OutcomeClass,
    holes::HoleLocation,
    spec::{Budget, CaseOptions, PathMode, ProposerConfig},
    values::{GenerationBounds, Value},
};

/// The report's `schema` field.
pub const REPORT_SCHEMA: &str = "krust-fuzz-report";

/// The report's `version` field: bumped when the report's shape or the meaning of a field
/// changes (FZ-SCHEMA lists it among the format versions of `docs/compatibility.md`).
pub const REPORT_VERSION: u32 = 1;

/// A campaign's report (ARCHITECTURE 9.3).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct FuzzReport {
    /// Always [`REPORT_SCHEMA`].
    pub schema: String,
    /// Always [`REPORT_VERSION`] for reports this crate writes.
    pub version: u32,
    /// Everything the report is a function of.
    pub identity: ReportIdentity,
    /// How the campaign ended.
    pub outcome: CampaignOutcome,
    /// Counts over every case.
    pub totals: Totals,
    /// The confirmed witness, when one was found.
    pub witness: Option<Witness>,
    /// The bounded statement of a campaign that found no witness.
    pub no_witness: Option<NoWitness>,
    /// Records the definitions' loads observed, reported once per campaign; they taint no leaf
    /// (T-5).
    pub load_records: Vec<LoadRecord>,
    /// Holes whose refused sort an override admitted (ARCHITECTURE 2.4).
    pub sort_overrides: Vec<SortOverride>,
    /// Warnings such as `statically-unreachable` (ARCHITECTURE 6.3).
    pub warnings: Vec<String>,
    /// Engine defects: a case and its confirmation disagreeing, a halt the request never asks
    /// for, a rule applied outside the rule graph. Never reported as hits (ARCHITECTURE 7).
    pub engine_defects: Vec<EngineDefect>,
}

impl FuzzReport {
    /// The report as canonical JSON: compact, fields in declaration order, maps ordered. Equal
    /// reports give equal bytes.
    #[must_use]
    pub fn to_canonical_json(&self) -> String {
        serde_json::to_string(self).expect("a report has string map keys and no floats")
    }

    /// Read a report written by [`Self::to_canonical_json`].
    ///
    /// # Errors
    ///
    /// The JSON error, including for an unknown field.
    pub fn from_json(text: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(text)
    }
}

/// Everything a report is a function of (ARCHITECTURE 5.4, 9.3).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct ReportIdentity {
    /// [`crate::ENGINE_VERSION`].
    pub engine_version: u32,
    /// The k-rust revision, as the caller gave it.
    pub k_rust_revision: String,
    /// The baseline, then the mutant of a differential campaign.
    pub definitions: Vec<DefinitionIdentity>,
    /// [`digest_hex`] of the program: its name, start sort and text, the configuration-variable
    /// bindings, or the printed KORE template.
    pub program_digest: String,
    /// [`digest_hex`] of the canonical JSON of the hole declarations.
    pub overlay_digest: String,
    /// [`digest_hex`] of the canonical JSON of the target.
    pub target_digest: String,
    /// The case options as given, with [`CaseOptions::effective_max_work`] applied.
    pub options: CaseOptions,
    /// The proposer configuration.
    pub proposers: ProposerConfig,
    /// The generation bounds used.
    pub bounds: GenerationBounds,
    /// The rejection cap.
    pub rejection_cap: u64,
    /// The campaign seed.
    pub seed: u64,
    /// The budget [`crate::Campaign::run`] was given.
    pub budget: Budget,
    /// The executing thread's stack size, as the caller gave it.
    pub thread_stack_size: Option<u64>,
}

/// Which definition of the campaign.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum DefinitionRole {
    /// The definition every case runs on; the baseline of a differential campaign.
    Baseline,
    /// The mutant of a differential campaign.
    Mutant,
}

/// One definition's identity (ARCHITECTURE 5.4).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct DefinitionIdentity {
    /// Baseline or mutant.
    pub role: DefinitionRole,
    /// The execution digest of its KORE definition, as text.
    pub execution_digest: String,
    /// `"source-execution"` or `"from-definition"` ([`crate::BackendRoute`]).
    pub route: String,
    /// [`digest_hex`] of the rewrite order (ids joined by newlines) on the source-execution
    /// route; the order selects the one path `strategy: any` follows.
    pub execution_rewrite_order_digest: Option<String>,
}

/// How a campaign ended.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "status", rename_all = "kebab-case")]
pub enum CampaignOutcome {
    /// A witness was found and confirmed.
    WitnessFound,
    /// The budget ran out without a confirmed witness.
    NoWitnessFound,
    /// Differential: equal execution digests (and rewrite orders) ended the campaign before any
    /// case (ARCHITECTURE 4.3).
    Equivalent,
    /// The rejection cap was reached (ARCHITECTURE 9.2).
    RejectedOut,
    /// The caller's cancellation token stopped the campaign.
    Cancelled,
    /// A failure every case would repeat ended the campaign (a failed solver prelude).
    Aborted {
        /// Why.
        reason: String,
    },
}

/// Counts over every case (ARCHITECTURE 9.3).
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct Totals {
    /// Cases run, rejected cases included; confirmation and shrink runs excluded.
    pub cases: u64,
    /// Backend work over every execution, confirmation and shrinking included.
    pub work: u64,
    /// Cases per class; classes with no case are omitted.
    pub classes: BTreeMap<OutcomeClass, u64>,
    /// Rejected cases per thousand cases, rounded down.
    pub rejection_rate_permille: u64,
    /// Rules some case reached.
    pub coverage: CoverageTotals,
    /// Cases in which the target rule was blocked (ARCHITECTURE 6.2).
    pub target_blocked: u64,
    /// The best score any case reached, compared lexicographically, smaller being better
    /// (ARCHITECTURE 6.4); `None` when no proposer scores.
    pub best_score: Option<Vec<u64>>,
    /// Cases outside the determinism contract (ARCHITECTURE 5.4).
    pub outside_determinism: u64,
}

/// The rules some scored case reached (ARCHITECTURE 6.1).
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct CoverageTotals {
    /// Rule ids in some case's coverage `applied`.
    pub applied: BTreeSet<String>,
    /// Rule ids in some case's coverage `matched`.
    pub matched: BTreeSet<String>,
}

/// How a hit is labelled (ARCHITECTURE 4, 5.3).
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum HitLabel {
    /// The target was reached.
    Hit,
    /// The target of a negated property was reached: the property fails.
    PropertyFailure,
}

/// A confirmed witness (ARCHITECTURE 2.6, 7, 9.3).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct Witness {
    /// Hit or property failure.
    pub label: HitLabel,
    /// The first confirmed witness.
    pub first: WitnessCase,
    /// The shrunk witness, each step of which was confirmed; `None` when nothing shrank.
    pub shrunk: Option<WitnessCase>,
    /// The clean-leaf facts that were checked (ARCHITECTURE 5.2).
    pub clean_leaf_facts: Vec<String>,
    /// The equivalent `krun` command line.
    pub krun_command: String,
}

/// One confirmed witness case (ARCHITECTURE 2.6).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct WitnessCase {
    /// The hole overlay with values, in declaration order.
    pub holes: Vec<HoleValue>,
    /// The concrete initial configuration, as KORE text.
    pub initial_configuration: String,
    /// The class confirmation gave (`hit`).
    pub class: OutcomeClass,
    /// The final configuration or configurations, as KORE text.
    pub final_configurations: Vec<String>,
    /// The step count of the reaching leaf.
    pub steps: u64,
}

/// One hole of a witness: its location and its value as K text, KORE and value
/// (ARCHITECTURE 2.6). In kink's terms, a span hole is a `find`/`replace` edit.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct HoleValue {
    /// The hole's name.
    pub name: String,
    /// The hole's location as declared.
    pub location: HoleLocation,
    /// The value as K text.
    pub k_text: String,
    /// The value as KORE text.
    pub kore: String,
    /// The value.
    pub value: Value,
}

/// The bounded statement of a campaign without a witness (ARCHITECTURE 9.3). It is never a
/// claim that no witness exists.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct NoWitness {
    /// The sentence: the cases run, the path mode explored, and the bound to raise.
    pub statement: String,
    /// The path mode the cases ran in.
    pub path_mode: PathMode,
    /// Some one-path case had an alternative candidate, so the all-paths mode may find more
    /// (R-15).
    pub alternatives_seen: bool,
}

/// A record a definition's load observed (`observedIn: load`): a fact about the definition,
/// on no leaf (T-5).
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct LoadRecord {
    /// The record's kind (`contradicted-claim`, `allowance-refusal`, `unsupported-hook`,
    /// `stack-stop`).
    pub kind: String,
    /// Its detail, as the backend reports it.
    pub detail: String,
}

/// A hole whose refused sort an override admitted (ARCHITECTURE 2.4).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct SortOverride {
    /// The hole's name.
    pub hole: String,
    /// Its sort.
    pub sort: String,
    /// The refusal the override admitted.
    pub refusal: String,
}

/// An engine defect: a fact that contradicts the engine's own invariants (ARCHITECTURE 5.3,
/// 6.3, 7). It is reported, never counted as a hit.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct EngineDefect {
    /// The case number, when the defect belongs to one.
    pub case: Option<u64>,
    /// What happened.
    pub description: String,
}

/// The lowercase hex SHA-256 of `bytes`, the digest every report identity field uses.
#[must_use]
pub fn digest_hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let digest = Sha256::digest(bytes);
    let mut text = String::with_capacity(64);
    for byte in digest {
        write!(text, "{byte:02x}").expect("writing to a String does not fail");
    }
    text
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;

    use super::*;
    use crate::{
        holes::SpanAddress,
        spec::{CaseOptions, ProposerConfig},
    };

    /// A report with every optional part present and every collection non-empty, so that a
    /// change to any field's serialization changes the bytes below.
    fn fixed_report() -> FuzzReport {
        let hole = HoleValue {
            name: "AMOUNT".into(),
            location: HoleLocation::Span(SpanAddress {
                program: "transfer.imp".into(),
                line: Some(4),
                find: "amount = 250;".into(),
                literal: "250".into(),
            }),
            k_text: "-7".into(),
            kore: r#"\dv{SortInt{}}("-7")"#.into(),
            value: Value::Int(BigInt::from(-7)),
        };
        let case = WitnessCase {
            holes: vec![hole],
            initial_configuration: "Lbl'-LT-'generatedTop'-GT-'{}()".into(),
            class: OutcomeClass::Hit,
            final_configurations: vec!["Lbl'-LT-'generatedTop'-GT-'{}()".into()],
            steps: 12,
        };
        FuzzReport {
            schema: REPORT_SCHEMA.into(),
            version: REPORT_VERSION,
            identity: ReportIdentity {
                engine_version: crate::ENGINE_VERSION,
                k_rust_revision: "b322de1ab".into(),
                definitions: vec![DefinitionIdentity {
                    role: DefinitionRole::Baseline,
                    execution_digest: "0123".into(),
                    route: "source-execution".into(),
                    execution_rewrite_order_digest: Some(digest_hex(b"rule-1\nrule-2")),
                }],
                program_digest: digest_hex(b"program"),
                overlay_digest: digest_hex(b"overlay"),
                target_digest: digest_hex(b"target"),
                options: CaseOptions {
                    max_work: Some(100_000),
                    ..CaseOptions::default()
                },
                proposers: ProposerConfig {
                    explicit: vec![BTreeMap::from([(
                        "AMOUNT".to_owned(),
                        Value::Bytes(vec![0, 0xab]),
                    )])],
                    ..ProposerConfig::default()
                },
                bounds: GenerationBounds::default(),
                rejection_cap: 10,
                seed: 0x5eed,
                budget: Budget::Cases(5000),
                thread_stack_size: Some(64 << 20),
            },
            outcome: CampaignOutcome::WitnessFound,
            totals: Totals {
                cases: 40,
                work: 1234,
                classes: BTreeMap::from([
                    (OutcomeClass::Miss, 37),
                    (OutcomeClass::Rejected, 2),
                    (OutcomeClass::Hit, 1),
                ]),
                rejection_rate_permille: 50,
                coverage: CoverageTotals {
                    applied: BTreeSet::from(["b".to_owned(), "a".to_owned()]),
                    matched: BTreeSet::from(["c".to_owned()]),
                },
                target_blocked: 3,
                best_score: Some(vec![0, 2]),
                outside_determinism: 0,
            },
            witness: Some(Witness {
                label: HitLabel::PropertyFailure,
                first: case.clone(),
                shrunk: Some(case),
                clean_leaf_facts: vec!["ceil-free".into()],
                krun_command: "krust krun transfer.imp".into(),
            }),
            no_witness: Some(NoWitness {
                statement: "No witness in 40 cases.".into(),
                path_mode: PathMode::OnePath,
                alternatives_seen: false,
            }),
            load_records: vec![LoadRecord {
                kind: "contradicted-claim".into(),
                detail: "total".into(),
            }],
            sort_overrides: vec![SortOverride {
                hole: "X".into(),
                sort: "Id".into(),
                refusal: "Token".into(),
            }],
            warnings: vec!["statically-unreachable".into()],
            engine_defects: vec![EngineDefect {
                case: Some(7),
                description: "confirmation disagreed".into(),
            }],
        }
    }

    #[test]
    fn report_round_trips_through_canonical_json() {
        let report = fixed_report();
        let text = report.to_canonical_json();
        let read = FuzzReport::from_json(&text).expect("the report reads back");
        assert_eq!(read, report);
        assert_eq!(read.to_canonical_json(), text);
    }

    #[test]
    fn report_bytes_are_stable_for_a_fixed_value() {
        let text = fixed_report().to_canonical_json();
        let expected = concat!(
            r#"{"schema":"krust-fuzz-report","version":1,"identity":{"engine-version":1,"#,
            r#""k-rust-revision":"b322de1ab","definitions":[{"role":"baseline","#,
            r#""execution-digest":"0123","route":"source-execution","#,
            r#""execution-rewrite-order-digest":"#,
            r#""ORDER"}],"#,
            r#""program-digest":"PROGRAM","overlay-digest":"OVERLAY","target-digest":"TARGET","#,
            r#""options":{"paths":"one-path","max-depth":null,"max-work":100000,"#,
            r#""max-simplification-iterations":ITER,"normal-end-pattern":null,"#,
            r#""safety-limit-ms":null},"proposers":{"anchors-first":true,"explicit":"#,
            r#"[{"AMOUNT":{"bytes":"00ab"}}],"weights":{"blind":1}},"#,
            r#""bounds":{"int-bits":64,"length":16,"depth":4},"rejection-cap":10,"#,
            r#""seed":24301,"budget":{"cases":5000},"thread-stack-size":67108864},"#,
            r#""outcome":{"status":"witness-found"},"totals":{"cases":40,"work":1234,"#,
            r#""classes":{"hit":1,"miss":37,"rejected":2},"rejection-rate-permille":50,"#,
            r#""coverage":{"applied":["a","b"],"matched":["c"]},"target-blocked":3,"#,
            r#""best-score":[0,2],"outside-determinism":0},"witness":{"label":"property-failure","#,
            r#""first":CASE,"shrunk":CASE,"clean-leaf-facts":["ceil-free"],"#,
            r#""krun-command":"krust krun transfer.imp"},"no-witness":{"#,
            r#""statement":"No witness in 40 cases.","path-mode":"one-path","#,
            r#""alternatives-seen":false},"load-records":[{"kind":"contradicted-claim","#,
            r#""detail":"total"}],"sort-overrides":[{"hole":"X","sort":"Id","#,
            r#""refusal":"Token"}],"warnings":["statically-unreachable"],"#,
            r#""engine-defects":[{"case":7,"description":"confirmation disagreed"}]}"#,
        );
        let case = concat!(
            r#"{"holes":[{"name":"AMOUNT","location":{"kind":"span","#,
            r#""program":"transfer.imp","line":4,"find":"amount = 250;","literal":"250"},"#,
            r#""k-text":"-7","kore":"\\dv{SortInt{}}(\"-7\")","#,
            r#""value":{"int":"-7"}}],"#,
            r#""initial-configuration":"Lbl'-LT-'generatedTop'-GT-'{}()","class":"hit","#,
            r#""final-configurations":["Lbl'-LT-'generatedTop'-GT-'{}()"],"steps":12}"#,
        );
        let expected = expected
            .replace("ORDER", &digest_hex(b"rule-1\nrule-2"))
            .replace("PROGRAM", &digest_hex(b"program"))
            .replace("OVERLAY", &digest_hex(b"overlay"))
            .replace("TARGET", &digest_hex(b"target"))
            .replace(
                "ITER",
                &CaseOptions::default()
                    .max_simplification_iterations
                    .to_string(),
            )
            .replace("CASE", case);
        assert_eq!(text, expected);
    }

    #[test]
    fn digest_is_lowercase_hex_sha256() {
        assert_eq!(
            digest_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }
}
