//! The campaign report: one canonical JSON document with `schema: "krust-fuzz-report"` and a
//! `version` (ARCHITECTURE 9.3).
//!
//! The report is canonical: its fields serialize in declaration order, every map is ordered,
//! integers and byte strings in values are text, and no float occurs, so equal reports are equal
//! bytes ([`FuzzReport::to_canonical_json`]). The seed, the budget, the rejection cap and the
//! thread stack size, which a caller may draw at random or set to an extreme, are canonical
//! decimal strings; every other integer is a count, or a case bound in the options, that a
//! JavaScript client reads exactly as long as it stays below 2^53. A campaign's report is a function of its
//! specification, budget, seed, the k-rust revision and [`crate::ENGINE_VERSION`]
//! (ARCHITECTURE 5.4).

use std::collections::{BTreeMap, BTreeSet};

use k_rust::backend::HaltReasonOutput;
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

use crate::{
    exec::{ComparableCondition, NormalEndKind, OutcomeClass, UnjudgedReason},
    holes::HoleLocation,
    spec::{Budget, CaseOptions, PathMode, ProposerConfig},
    target::RuleName,
    values::{Constraints, GenerationBounds, Value},
};

/// The report's `schema` field.
pub const REPORT_SCHEMA: &str = "krust-fuzz-report";

/// The report's `version` field: bumped when the report's shape or the meaning of a field
/// changes (FZ-SCHEMA lists it among the format versions of `docs/compatibility.md`).
///
/// Version 2 adds `reaching.step` to an observer target's witness cases and
/// `identity.dictionary` to a campaign whose dictionary proposer has a positive weight; a
/// version-1 reader, which refuses unknown fields, refuses both.
///
/// Version 3 adds the corpus's and the solve proposer's parameters, `identity.corpus` and
/// `identity.solve`, and the solve proposer's `totals.solve`, each present exactly when its
/// proposer has a positive weight; a version-2 reader refuses them as unknown fields. The
/// climb's `identity.climb` came in under version 2 without a bump.
///
/// Version 4 adds the run-time literals' parameters (FZ-16), `runtime-probability`,
/// `max-comparisons`, `runtime-condition-rules` and `runtime-guard-radius` to `identity.climb`
/// and `runtime-probability`, `follow-probability`, `follow-depth`, `max-comparisons` and
/// `runtime-condition-rules` to `identity.corpus`, and the corpus's count buckets (FZ-17),
/// `count-exact-below` in `identity.corpus`; a version-3 reader refuses them as unknown fields.
///
/// Version 5 (phase 5) adds `identity.effective-constraints`, `identity.target-rule`,
/// `totals.coverage.names`, `totals.unsupported-reasons`, `totals.baseline-incomplete-reasons`,
/// the top-level `normal-end` and a witness side's `halts`, renames the clean-leaf facts of ends
/// (`*-end-final`, `*-data`), and changes the meaning of the definition digests and of the
/// differential classes; the campaign specification's `Target`, versioned with the report, gains
/// `data-end` (`docs/compatibility.md`, "Format
/// versions").
///
/// Version 6 (phase 6) adds the top-level `incidental` (FZ-INCIDENTAL: the first `stuck` and
/// the first `undefined` case, each with `baseline-run` for a differential baseline's run), the
/// outcome `not-comparable` and the top-level `definition-findings` (FZ-POLISH),
/// `identity.options.assume-joined`, `totals.pattern-body-matches`, a witness case's `program`
/// and the witness's `mutant-krun-command`, and a span hole's `column`; `totals.best-score` gets
/// its shape (`scored-cases`, `best`), and a differential witness now has a `krun-command`
/// (`docs/compatibility.md`, "Format versions"). A version-5 reader refuses the new outcome and
/// fields.
///
/// Version 7 (phase 8) widens a finding's `genuine` verdict and adds `instance.stuck` (S2B-T3);
/// accepts a pattern target's `at: any-state`, so a witness's `reaching.step` may be 0
/// (FZ-ANYSTATE); adds a rule or pattern witness case's `comparable`, the target keys
/// `comparable` and `query-confirmable`, the clean-leaf facts `comparable-end` and
/// `query-confirmable` and the reasons `end-not-comparable:*` and `query-not-confirmable:*`
/// (FZ-COMPARABLE-AQ); and adds a witness case's `config-vars`, the
/// instantiated bindings (KF-T3b). A version-6 reader refuses the new fields, key values and
/// reasons.
///
/// Version 8 (FZ-CRASH) adds the top-level `crashes` and `crashes-omitted` (a k-rust or engine
/// panic or internal error during a case is a finding with its input), `totals.crash-work`,
/// `totals.solve.panicked`, an aborted outcome's `kind` (and, for a panicking observer, its
/// `case`, `holes` and `panic`), the reasons `panic`, `internal-error`, `too-deep` and
/// `stack-mapping-refused` in place of `backend-error`, and the comparable condition `crash`
/// (`docs/compatibility.md`, "Format versions"). A version-7 reader refuses the new fields,
/// reasons and condition.
///
/// Version 9 (FZ-STATESET and FZ-STATESET-MATCH, round 3) judges all-paths rule and pattern
/// targets and the program's run of every path that judges comparability on k-rust state sets,
/// which report each distinct configuration of a depth once: a witness's `final-configurations`
/// and `halts` list distinct ends, `totals.pattern-body-matches` counts distinct ends, condition
/// records and applied counts are per distinct state, and cases a path set left `work-bound` are
/// judged complete. An `at: any-state` pattern is matched against every reached state inside the
/// run, and its witness carries the reaching configuration (`reaching.configuration`). All-paths
/// `fired` reads the run's committed transitions. It adds `identity.execution-modality`
/// ([`ExecutionModality`]), `reaching.configuration` and the reasons `fired-off-trace` and
/// `any-state-unattributed`. A version-8 reader refuses the new fields and reasons, and
/// `--replay` refuses a version-8 witness by its version.
///
/// Within version 9 (FZ-COMPARABLE-B, the same round-3 wave): a campaign run with a client's
/// witness filter ([`crate::filter`]) records `identity.filter`, the top-level `client-refusals`,
/// `totals.filter`, a repaired witness's `repaired-from`, the reason `client-refused`, the abort
/// kind `client-defect` and the crash phase `repair`; every witness side records its run's `work`
/// and, for undefined steps, `undefined-rules`. A reader of the round's earlier version-9 reports
/// refuses the new fields.
///
/// Within version 9 (UNNAMED-HOOK, the same wave): `totals.unsupported-hooks`,
/// `totals.baseline-incomplete-hooks` and a witness case's `comparable.hooks` name the hooks
/// behind each reason or condition that rests on one ([`ReasonHooks`]), and
/// `totals.pattern-body-judged` counts the cases whose ends were judged against a final pattern.
/// A reader of the round's earlier version-9 reports refuses the new fields.
///
/// Version 10 (round 4, FZ-REPLAY-WHOLE, D41) names every source location relative to the
/// directory of the main module's file, as the identity's digests name sources (`imp.k`,
/// `lib/x.k`, `../lib/y.k`), where version 9 wrote the path the definition was compiled at: in
/// `totals.coverage.names` and `identity.target-rule` (each location's `source`, and its
/// `reference`, now a suffix of that relative path) and in `definition-findings` (each equation's
/// position, and the reasons that quote it); the digests name the main module's file by its own
/// name where version 9 wrote `<main>`, so a report is a function of its identity wherever the
/// definition was compiled (S1). It adds `identity.fuzz-revision`, the k-rust-fuzz build
/// ([`crate::build_identity`], S4), `identity.parse-diagnostic-work`, the parser's diagnostic
/// work limit (N4), `identity.debug-assertions`, the build profile's fact that decides which
/// crashes occur (fix round S-E), and `totals.first-outside-determinism`, the first case a re-run may differ
/// at (S3). A version-9 reader refuses the new fields, and `--replay` refuses a version-9
/// witness by its version.
pub const REPORT_VERSION: u32 = 10;

/// How many hooks a reason or condition names at most ([`ReasonHooks`]); the rest are counted.
pub const LISTED_HOOKS: usize = 8;

/// A hook that a fact behind an unjudged reason or a failed comparable condition names
/// (UNNAMED-HOOK), read from k-rust's typed records, never from their text: the hook of an
/// `implementation-chosen-value` mark with the `class` of the value the definition leaves open
/// (`order`, `item`, ...), or the hook of an application left unevaluated as an unsupported hook
/// (an `unsupported-hook` halt's cause, an `unsupported-hook-unevaluated` diagnostic, a run's or
/// a load's `unsupportedHooks` record), with no class. Ordered by hook, then class.
#[derive(Clone, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct ReasonHook {
    /// The hook, as the definition's `hook` attribute names it (`MAP.keys_list`).
    pub hook: String,
    /// For an implementation-chosen value, what the definition leaves open; absent for an
    /// unsupported hook.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub class: Option<String>,
}

impl ReasonHook {
    /// An unsupported hook.
    #[must_use]
    pub fn unsupported(hook: &str) -> Self {
        Self {
            hook: hook.to_owned(),
            class: None,
        }
    }

    /// A hook that read an implementation-chosen value of `class`.
    #[must_use]
    pub fn chosen(hook: &str, class: &str) -> Self {
        Self {
            hook: hook.to_owned(),
            class: Some(class.to_owned()),
        }
    }
}

impl std::fmt::Display for ReasonHook {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.class {
            Some(class) => write!(f, "{} [{class}]", self.hook),
            None => f.write_str(&self.hook),
        }
    }
}

/// The hooks behind one reason or condition (UNNAMED-HOOK): over the cases counted under the
/// reason ([`Totals::unsupported_hooks`]), or the run a witness's comparable judgement read
/// ([`Comparability::hooks`]). The first [`LISTED_HOOKS`] distinct hooks in [`ReasonHook`]'s
/// order, so the list is a function of the set of hooks, not of the order cases ran in, and how
/// many more there are.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct ReasonHooks {
    /// The listed hooks, sorted, each once.
    pub hooks: Vec<ReasonHook>,
    /// Distinct hooks beyond the listed ones; absent when 0.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub omitted: u64,
    /// In [`Totals::unsupported_hooks`] and [`Totals::baseline_incomplete_hooks`], how many of
    /// the cases counted under the reason named a hook: a reason may also stand for facts that
    /// name none (a contradicted claim off the leaves, conflicting equations), so the hooks need
    /// not be behind every case. Absent (0) in [`Comparability::hooks`], which is one run's.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub cases: u64,
}

impl ReasonHooks {
    /// The first [`LISTED_HOOKS`] of `hooks` and the count of the rest; `None` when `hooks` is
    /// empty.
    #[must_use]
    pub fn of(hooks: &BTreeSet<ReasonHook>) -> Option<Self> {
        if hooks.is_empty() {
            return None;
        }
        Some(Self {
            hooks: hooks.iter().take(LISTED_HOOKS).cloned().collect(),
            omitted: u64::try_from(hooks.len().saturating_sub(LISTED_HOOKS)).unwrap_or(u64::MAX),
            cases: 0,
        })
    }

    /// The hooks as a reader sees them in a sentence: `hook MAP.keys_list [order]`, `hooks A, B`,
    /// `hooks A, B and 3 more`.
    #[must_use]
    pub fn describe(&self) -> String {
        let listed: Vec<String> = self.hooks.iter().map(ToString::to_string).collect();
        let noun = if listed.len() == 1 && self.omitted == 0 {
            "hook"
        } else {
            "hooks"
        };
        let more = if self.omitted > 0 {
            format!(" and {} more", self.omitted)
        } else {
            String::new()
        };
        format!("{noun} {}{more}", listed.join(", "))
    }
}

/// `count` cases of `reason` as the reports' sentences name them, with the hooks the reason's
/// cases named and how many of them named one ([`ReasonHooks::cases`]): `4
/// implementation-chosen-value (hook MAP.keys_list [order] named in 4 of them)`, `5
/// run-fact-off-leaves (hook MAP.keys_list [order] named in 1 of them)`.
#[must_use]
pub fn describe_reason(reason: UnjudgedReason, count: u64, hooks: Option<&ReasonHooks>) -> String {
    match hooks {
        Some(hooks) => format!(
            "{count} {} ({} named in {} of them)",
            reason.name(),
            hooks.describe(),
            hooks.cases
        ),
        None => format!("{count} {}", reason.name()),
    }
}

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
    /// How the campaign ended, with the witness or the bounded no-witness statement.
    pub outcome: CampaignOutcome,
    /// Counts over every case.
    pub totals: Totals,
    /// Which normal end each definition's classes rest on (ARCHITECTURE 5.2); absent from a
    /// report that ran no case.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub normal_end: Option<NormalEnds>,
    /// The first `stuck` and the first `undefined` case of the campaign, kept as information
    /// about the semantics, not as a failure ([`Incidentals`]); absent when no case had either
    /// class.
    #[serde(default, skip_serializing_if = "Incidentals::is_empty")]
    pub incidental: Incidentals,
    /// The first case of each crash signature: a panic or internal error of k-rust or of the
    /// engine during a case, kept with its input ([`CrashFindings`]); absent when no case
    /// crashed.
    #[serde(default, skip_serializing_if = "CrashFindings::is_empty")]
    pub crashes: CrashFindings,
    /// The crashed cases whose signature was not kept, beyond the first
    /// [`crate::crash::MAX_CRASH_SIGNATURES`] signatures; absent when 0.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub crashes_omitted: u64,
    /// The first refused hit of each cause the client's witness filter gave
    /// ([`ClientRefusal`], [`crate::filter`]), at most [`crate::filter::MAX_CLIENT_REFUSALS`];
    /// absent when no hit was refused.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub client_refusals: Vec<ClientRefusal>,
    /// Records the definitions' loads observed, reported once per campaign; they taint no leaf
    /// (T-5).
    pub load_records: Vec<LoadRecord>,
    /// Holes whose refused sort an override admitted (ARCHITECTURE 2.4).
    pub sort_overrides: Vec<SortOverride>,
    /// Warnings such as `statically-unreachable` (ARCHITECTURE 6.3).
    pub warnings: Vec<String>,
    /// The findings of each definition's full critical-pair check, when the campaign's
    /// judgement reads data ends (a differential target, or a rule or pattern target with
    /// `run-to-completion` and `data-end`) and the check reports something: every finding, the
    /// assumed ones marked, each with its verdict (ARCHITECTURE 4.3). Absent from the JSON when
    /// empty.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub definition_findings: Vec<DefinitionFinding>,
    /// Engine defects: a case and its confirmation disagreeing, a halt the request never asks
    /// for, a rule applied outside the rule graph. Never reported as hits (ARCHITECTURE 7).
    pub engine_defects: Vec<EngineDefect>,
}

impl FuzzReport {
    /// The report as canonical JSON: compact, fields in declaration order, maps ordered. Equal
    /// reports give equal bytes.
    ///
    /// A hole value may be nested up to [`crate::values::MAX_VALUE_DEPTH`] levels, and writing
    /// recurses once per level of the JSON, so outside WebAssembly the writer runs on a stack
    /// that grows on the heap (`serde_stacker`) whenever the thread's runs low; on WebAssembly,
    /// which cannot switch stacks, a report deeper than its stack allows traps (stack
    /// exhaustion is a trap there: the stack lies below every other datum).
    ///
    /// # Panics
    ///
    /// Never: every map of a report has string keys and no field is a float, which are the only
    /// ways `serde_json` serialization fails.
    #[must_use]
    pub fn to_canonical_json(&self) -> String {
        let mut bytes = Vec::new();
        let mut writer = serde_json::Serializer::new(&mut bytes);
        #[cfg(not(target_family = "wasm"))]
        let written = self.serialize(serde_stacker::Serializer::new(&mut writer));
        #[cfg(target_family = "wasm")]
        let written = self.serialize(&mut writer);
        written.expect("a report has string map keys and no floats");
        String::from_utf8(bytes).expect("serde_json writes UTF-8")
    }

    /// The confirmed witness, when the campaign found one.
    #[must_use]
    pub fn witness(&self) -> Option<&Witness> {
        match &self.outcome {
            CampaignOutcome::WitnessFound { witness } => Some(witness),
            _ => None,
        }
    }

    /// The bounded no-witness statement, when the campaign ended without a witness for a
    /// reason other than equivalence.
    #[must_use]
    pub fn no_witness(&self) -> Option<&NoWitness> {
        match &self.outcome {
            CampaignOutcome::NoWitnessFound { no_witness }
            | CampaignOutcome::RejectedOut { no_witness }
            | CampaignOutcome::Cancelled { no_witness }
            | CampaignOutcome::Aborted { no_witness, .. } => Some(no_witness),
            CampaignOutcome::WitnessFound { .. }
            | CampaignOutcome::Equivalent
            | CampaignOutcome::NotComparable { .. } => None,
        }
    }

    /// Read a report written by [`Self::to_canonical_json`].
    ///
    /// It checks no `version`: fields added since an older version default, so an older report
    /// may read back with its own `version`. A caller that needs this version's meaning checks
    /// `schema` and `version` against [`REPORT_SCHEMA`] and [`REPORT_VERSION`] first, as
    /// `krust fuzz --replay` does.
    ///
    /// Every report this crate writes reads back, whatever the depth of its hole values (HARD-B
    /// review S3): outside WebAssembly, `serde_json`'s recursion limit of 128 nested arrays and
    /// objects is lifted and the reader runs on a stack that grows on the heap
    /// (`serde_stacker`), so its depth is bounded by memory, not by the calling thread. On
    /// WebAssembly, which cannot switch stacks, the limit stays: a report nested deeper (a hole
    /// value of about 40 levels or more) is refused with `serde_json`'s recursion-limit error.
    ///
    /// # Errors
    ///
    /// The JSON error, including for an unknown field.
    pub fn from_json(text: &str) -> Result<Self, serde_json::Error> {
        let mut reader = serde_json::Deserializer::from_str(text);
        #[cfg(not(target_family = "wasm"))]
        let report = {
            reader.disable_recursion_limit();
            Self::deserialize(serde_stacker::Deserializer::new(&mut reader))?
        };
        #[cfg(target_family = "wasm")]
        let report = Self::deserialize(&mut reader)?;
        reader.end()?;
        Ok(report)
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
    /// This build of k-rust-fuzz ([`crate::build_identity`]): the code that classifies, judges
    /// and reports, which the k-rust revision does not cover (FZ-REPLAY-WHOLE S4). Recorded by
    /// the library itself; no caller can name another.
    pub fuzz_revision: String,
    /// The baseline, then the mutant of a differential campaign.
    pub definitions: Vec<DefinitionIdentity>,
    /// [`digest_hex`] of the program: its name, start sort and text, the configuration-variable
    /// bindings, or the printed KORE template.
    pub program_digest: String,
    /// [`digest_hex`] of the canonical JSON of the hole declarations.
    pub overlay_digest: String,
    /// [`digest_hex`] of the canonical JSON of the target.
    pub target_digest: String,
    /// For a rule target, the catalog entry its reference resolved to (ARCHITECTURE 4.2): the
    /// id the campaign judges by, with its names, so that a reader can check which rule a
    /// label, a unique id or a source line named. Absent from the JSON for other targets.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub target_rule: Option<TargetRule>,
    /// The case options as given, with [`CaseOptions::effective_max_work`] applied; they carry
    /// the backend's solver options.
    pub options: CaseOptions,
    /// The result modality of each kind of run the campaign makes ([`ExecutionModality`]):
    /// whether its paths are reported one leaf per path or one leaf per distinct state. Always
    /// present in reports of version 9; absent (`None`) only when an older report is read back.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub execution_modality: Option<ExecutionModality>,
    /// The proposer configuration.
    pub proposers: ProposerConfig,
    /// The generation bounds used.
    pub bounds: GenerationBounds,
    /// The hard caps of this build's generators, which bound every value whatever the bounds
    /// and constraints ask for.
    pub caps: GenerationCaps,
    /// The rejection cap, as a decimal string.
    #[serde(with = "decimal_u64")]
    pub rejection_cap: u64,
    /// The campaign seed, as a decimal string.
    #[serde(with = "decimal_u64")]
    pub seed: u64,
    /// The budget [`crate::Campaign::run`] was given.
    pub budget: Budget,
    /// The executing thread's stack size, as the caller gave it, as a decimal string.
    #[serde(with = "decimal_u64_option")]
    pub thread_stack_size: Option<u64>,
    /// `"z3"` when k-rust was built with its solver (`k_rust::Z3_INFERENCE`, whatever enabled
    /// it), `"none"` otherwise: a build without a solver leaves undecided some conditions a
    /// solver decides.
    pub solver: String,
    /// Whether this build of k-rust-fuzz has debug assertions (`cfg!(debug_assertions)`): a
    /// debug assertion's panic is a crash a release build does not raise, so the build profile
    /// decides which crashes a report holds (FZ-REPLAY-WHOLE fix round S-E).
    pub debug_assertions: bool,
    /// The parser's diagnostic work limit this process read
    /// (`k_rust::inner::DiagnosticWork::from_environment`, the `KRUST_PARSE_DIAGNOSTIC_WORK`
    /// variable): `unlimited`, or the floor in chart steps as a decimal string. It changes the
    /// text of parse diagnostics, which reach the warnings (a narrowed hole's probe that does not
    /// parse), so the report is a function of it (FZ-REPLAY-WHOLE N4).
    pub parse_diagnostic_work: String,
    /// The dictionary proposer's parameters (ARCHITECTURE 8.3), present exactly when the
    /// dictionary has a positive weight; absent from the JSON otherwise.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dictionary: Option<DictionaryParameters>,
    /// The climb proposer's parameters (ARCHITECTURE 8.4), present exactly when the climb has
    /// a positive weight; absent from the JSON otherwise.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub climb: Option<ClimbParameters>,
    /// The corpus proposer's parameters (ARCHITECTURE 8.5), present exactly when the corpus
    /// has a positive weight; absent from the JSON otherwise.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub corpus: Option<CorpusParameters>,
    /// The solve proposer's parameters (ARCHITECTURE 8.6), present exactly when the solve
    /// proposer has a positive weight; absent from the JSON otherwise.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub solve: Option<SolveParameters>,
    /// The holes whose values are generated under narrower constraints than they declare,
    /// because the program's syntax cannot hold the values left out at the hole (an `Int`
    /// literal position that reads no negative integer back): one entry per such hole, in the
    /// order of the holes, with both constraints and the reason. Absent from the JSON when no
    /// hole was narrowed. The declared constraints stay the ones every case is checked against.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub effective_constraints: Vec<EffectiveConstraints>,
    /// The identity of the client's witness filter the campaign ran with
    /// ([`crate::filter::WitnessFilter::id`]): the filter chooses which cases become witnesses, so
    /// the report is a function of it too. Absent for a campaign without a filter. Replay
    /// ignores it: a confirmed witness reproduces without the filter.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub filter: Option<String>,
}

/// How a run reports its paths: k-rust's `ExecuteRequest::result_modality`
/// (`docs/compatibility.md`, "Search results").
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ResultModality {
    /// One leaf per path, with that path's trace and facts.
    PathSet,
    /// One leaf per distinct configuration of a depth: an arrival at a configuration another
    /// path reached at the same depth is merged into it (its facts on the result's lists, its
    /// trace dropped), so converging paths are explored once.
    StateSet,
}

/// The result modality of each kind of run a campaign makes (ARCHITECTURE 5.1, 5.4; FZ-STATESET).
/// A change of modality changes what a case's leaves are (one per path, or one per distinct
/// state) and so its final configurations, steps and reaching leaf, which `--replay` explains.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct ExecutionModality {
    /// Each case's run: a state set for an all-paths rule target, pattern `at: final` or
    /// differential case (both sides, and the mutant's re-run of every path); a path set for
    /// one path (except the differential's sides), observers and `at: any-state`.
    pub cases: ResultModality,
    /// The program's run of every path that judges a rule or pattern hit's comparability
    /// (`crate::Target::comparable`): a state set. Present for every rule and pattern target,
    /// whether or not a case makes that run separately (an all-paths case with no terminal rule
    /// on a state set is that run itself, and a campaign without `comparable` may never make
    /// it), since its modality is that of whichever run judges comparability. Absent for the
    /// differential and observer targets, which judge none.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub every_path: Option<ResultModality>,
    /// The observed run whose configurations a pattern `at: any-state` is judged on: a path set.
    /// Absent for every other target.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub any_state: Option<ResultModality>,
}

/// A hole whose generation constraints are narrower than its declared ones (see
/// [`ReportIdentity::effective_constraints`]). Every field is a function of the campaign's
/// inputs; the human explanation, with any parser message, is the report's warning.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct EffectiveConstraints {
    /// The hole's name.
    pub hole: String,
    /// The constraints the hole declares.
    pub declared: Constraints,
    /// The constraints its values are generated under.
    pub effective: Constraints,
    /// Why they differ.
    pub reason: NarrowingReason,
    /// The definition whose grammar refused every probe.
    pub side: DefinitionRole,
    /// Every probe, in the order tried; each was refused.
    pub probes: Vec<NarrowingProbe>,
}

/// Why a hole's generation constraints were narrowed.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NarrowingReason {
    /// No probed negative integer, written at the hole, read back as itself: values are
    /// generated from 0.
    NegativeNotReadBack,
}

/// One refused probe of a narrowed hole.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct NarrowingProbe {
    /// The value written at the hole, as K text (`-1`).
    pub value: String,
    /// What the program's syntax made of it.
    pub outcome: ProbeOutcome,
    /// For [`ProbeOutcome::ReadsAs`], the term the configuration held at the hole's position
    /// instead, as K text (`- 1`), or as KORE (cut at 200 bytes) when it has no K text. Absent
    /// otherwise.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reads_as: Option<String>,
    /// For [`ProbeOutcome::ReadsAs`], the K label of that term's head symbol (below
    /// injections) when it is an application, since its K text alone can look like the value
    /// (`-1` printed from a unary minus applied to `1`). Absent otherwise.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub head: Option<String>,
}

/// How the program's syntax refused a probe.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ProbeOutcome {
    /// The program parsed, but the hole's position held another term than the value.
    ReadsAs,
    /// The program did not parse with the value at the hole.
    DoesNotParse,
}

/// The fixed parameters of the solve proposer (ARCHITECTURE 8.6), which with the definitions,
/// the target and the other proposers' cases decide when it runs and what it asks. They are
/// constants of this build; a change of any of them changes the case sequence of a solving
/// campaign.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct SolveParameters {
    /// The most share of the campaign's cases and of its work (its symbolic runs and model
    /// queries included) the solve proposer spends, as `[numerator, denominator]`.
    pub budget_share: [u32; 2],
    /// The stall that triggers a symbolic run: this many consecutive cases without a better
    /// score.
    pub stall_cases: u64,
    /// A symbolic run's work bound is `work-factor` times the blocked case's work plus
    /// `work-slack` states, and the case options' depth bound.
    pub work_factor: u64,
    /// See `work-factor`.
    pub work_slack: u64,
    /// The most model queries per symbolic run, one per leaf whose path applied the blocked rule.
    pub max_model_queries: u32,
    /// The Z3 resource units (`BackendOptions::smt_resource_limit`, the clock-free mode) of the
    /// first attempt of each solver decision of a symbolic run, doubled on each of
    /// `run-retries`: a decision Z3 has not made within them is undecided, and the run handles it as the backend handles any undecided answer.
    pub run_resource_units: u32,
    /// The retries of an undecided decision of a run, each with twice the units.
    pub run_retries: u32,
    /// The Z3 resource units of the first attempt of each model query (clock-free), doubled on
    /// each of `model-retries`: a query not decided within them answers unknown, which gives no
    /// candidate.
    pub model_resource_units: u32,
    /// The retries of an undecided model query, each with twice the units.
    pub model_retries: u32,
    /// The Z3 library whose search counts those units (`k_rust::backend::z3_version`): a
    /// different version may decide a query within other units.
    pub z3_version: String,
    /// The most unsettled queries kept, one per query key: the best-ranked blocked case of each;
    /// beyond it the worst-ranked is dropped.
    pub pending_limit: u64,
    /// The settled queries without a candidate after which a blocked rule and set of symbolic
    /// holes is given up for the campaign.
    pub futile_limit: u64,
    /// The hole sorts that are made symbolic: `Int` and `Bool`, which translate exactly to SMT.
    pub symbolic_sorts: Vec<String>,
    /// Which rules' condition entries the cases record: `target-and-keyed-chain`, the target,
    /// its direct predecessors as the climb reads them (`ClimbParameters::condition_rules`), and
    /// the chain of predecessors that key the head of `<k>` (or all, where none does) up to
    /// `chain-radius` edges before the target, on which the proposer looks for a refuted guard.
    pub condition_rules: String,
    /// See `condition-rules`.
    pub chain_radius: u64,
}

impl SolveParameters {
    /// The parameters of this build.
    #[must_use]
    pub fn current() -> Self {
        Self {
            budget_share: [SOLVE_BUDGET_SHARE.0, SOLVE_BUDGET_SHARE.1],
            stall_cases: SOLVE_STALL_CASES,
            work_factor: SOLVE_WORK_FACTOR,
            work_slack: SOLVE_WORK_SLACK,
            max_model_queries: SOLVE_MAX_MODEL_QUERIES,
            run_resource_units: SOLVE_RUN_RESOURCE_UNITS,
            run_retries: SOLVE_RUN_RETRIES,
            model_resource_units: SOLVE_MODEL_RESOURCE_UNITS,
            model_retries: SOLVE_MODEL_RETRIES,
            z3_version: k_rust::backend::z3_version().unwrap_or("none").to_owned(),
            pending_limit: SOLVE_PENDING_LIMIT,
            futile_limit: SOLVE_FUTILE_LIMIT,
            symbolic_sorts: vec!["Int".into(), "Bool".into()],
            condition_rules: "target-and-keyed-chain".into(),
            chain_radius: SOLVE_CHAIN_RADIUS,
        }
    }
}

/// The solve proposer's share of cases and work (ARCHITECTURE 8.6; [`SolveParameters`]).
pub(crate) const SOLVE_BUDGET_SHARE: (u32, u32) = (1, 4);
/// The stall, in cases, that triggers a symbolic run ([`SolveParameters::stall_cases`]).
pub(crate) const SOLVE_STALL_CASES: u64 = 8;
/// [`SolveParameters::work_factor`].
pub(crate) const SOLVE_WORK_FACTOR: u64 = 4;
/// [`SolveParameters::work_slack`].
pub(crate) const SOLVE_WORK_SLACK: u64 = 64;
/// [`SolveParameters::run_resource_units`].
pub(crate) const SOLVE_RUN_RESOURCE_UNITS: u32 = 250_000;
/// [`SolveParameters::run_retries`].
pub(crate) const SOLVE_RUN_RETRIES: u32 = 2;
/// [`SolveParameters::model_retries`].
pub(crate) const SOLVE_MODEL_RETRIES: u32 = 2;
/// [`SolveParameters::model_resource_units`].
pub(crate) const SOLVE_MODEL_RESOURCE_UNITS: u32 = 2_000_000;
/// [`SolveParameters::futile_limit`].
pub(crate) const SOLVE_FUTILE_LIMIT: u64 = 4;
/// [`SolveParameters::pending_limit`].
pub(crate) const SOLVE_PENDING_LIMIT: u64 = 64;
/// [`SolveParameters::chain_radius`].
pub(crate) const SOLVE_CHAIN_RADIUS: u64 = 8;
/// [`SolveParameters::max_model_queries`].
pub(crate) const SOLVE_MAX_MODEL_QUERIES: u32 = 4;

/// What the solve proposer did (ARCHITECTURE 8.6): its symbolic runs and what each gave.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct SolveTotals {
    /// Symbolic runs started.
    pub attempts: u64,
    /// Runs whose model gave admissible hole values, proposed as a case (counted in `cases`).
    pub candidates: u64,
    /// Runs in which no leaf's path applied the blocked rule within the bounds.
    pub no_path: u64,
    /// Runs in which every leaf's model query answered unsatisfiable.
    pub unsatisfiable: u64,
    /// Runs in which some model query answered unknown and none satisfiable.
    pub unknown: u64,
    /// Runs whose model gave a value its hole does not admit (its generation bounds).
    pub inadmissible: u64,
    /// Runs that failed: the symbolic configuration did not build, the backend refused it or
    /// answered an error, or a stop ended it.
    pub failed: u64,
    /// The work of the symbolic runs (states visited) and their model queries (1 each), which
    /// [`Totals::work`] includes.
    pub work: u64,
    /// Runs outside the determinism contract (ARCHITECTURE 5.4): a stack stop, or a stop by the
    /// per-case safety limit or a cancellation, whose occurrence decides whether the run gives a
    /// candidate, so the case sequence after it may differ in a re-run. Unknown solver answers
    /// do not count: the proposer's solver is clock-free, so they are a function of the query
    /// and the Z3 version.
    pub outside_determinism: u64,
    /// The message of the first failed run, if any.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_failure: Option<String>,
    /// Of the failed runs, those whose query panicked: a k-rust defect, which gives no finding
    /// because the query has no concrete input. Absent when 0.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub panicked: u64,
}

/// The fixed parameters of the corpus proposer (ARCHITECTURE 8.5), which with the definitions,
/// the target, the dictionary's harvest and the other proposers' cases decide its mutations.
/// They are constants of this build; a change of any of them changes the case sequence of a
/// campaign that weighs the corpus.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct CorpusParameters {
    /// The most share of the campaign's cases and of its work the corpus spends, as
    /// `[numerator, denominator]`.
    pub budget_share: [u32; 2],
    /// The probability, as `[numerator, denominator]`, that a proposal mutates the newest kept
    /// case rather than one chosen uniformly.
    pub newest_probability: [u32; 2],
    /// The probability, as `[numerator, denominator]`, that a proposal applies a second
    /// mutation.
    pub second_mutation_probability: [u32; 2],
    /// The weights of a new value's sources: a harvested literal, a fresh draw, a nudge of the
    /// current value, a splice from another kept case.
    pub source_weights: [u32; 4],
    /// The weights of a collection mutation: replace, insert, delete, keep a prefix, append,
    /// cross over.
    pub collection_weights: [u32; 6],
    /// An integer nudge moves by `±2^e` with `e` below this bound.
    pub nudge_exponents: u32,
    /// The most cases the corpus keeps.
    pub max_entries: u32,
    /// The most draws of a mutation before it is given up.
    pub max_attempts: u32,
    /// The buckets of a rule's applied count: each count below this bound is a bucket of its
    /// own, and from it on the counts of one power of two share one; a case that applies a rule
    /// a number of times in a bucket no earlier case applied it in is kept.
    pub count_exact_below: u64,
    /// The harvest the literals come from: the dictionary's radius, expansion, distance
    /// weights and exact-value probability (its draw probability does not apply).
    pub harvest: DictionaryParameters,
    /// The probability, as `[numerator, denominator]`, that a proposal from a kept case whose
    /// pool of run-time literals is not empty is a change from that pool (ARCHITECTURE 8.3,
    /// 8.5).
    pub runtime_probability: [u32; 2],
    /// The probability, as `[numerator, denominator]`, that the proposal after a corpus case
    /// that was a `miss` with a pool of run-time literals is a change of that case.
    pub follow_probability: [u32; 2],
    /// The most such follow-up changes chained after one mutation.
    pub follow_depth: u32,
    /// The most comparisons the pool of run-time literals of one case holds.
    pub max_comparisons: u32,
    /// Which rules' condition entries the cases record for the pools of run-time literals:
    /// `dictionary-guard-rules` for a rule target (the rules whose guards the dictionary's
    /// harvest reads: those at most `harvest.radius` rule-graph edges before the target and the
    /// higher-priority rules they compete with; a campaign that also climbs or solves records
    /// the union with the score's rules), `none` for another target, whose cases then carry no
    /// pool.
    pub runtime_condition_rules: String,
}

impl CorpusParameters {
    /// The parameters of this build for a campaign whose target is `target`.
    #[must_use]
    pub fn for_target(target: &crate::target::TargetKind) -> Self {
        crate::proposers::corpus::parameters(target)
    }
}

/// The fixed parameters of the climb proposer (ARCHITECTURE 8.4), which with the definitions,
/// the target and the other proposers' cases decide its moves. They are constants of this
/// build; a change of any of them changes the case sequence of a climbing campaign.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct ClimbParameters {
    /// The most share of the campaign's cases and of its work the climb spends, as
    /// `[numerator, denominator]`.
    pub budget_share: [u32; 2],
    /// The exponent `e` of a hole's first integer move `v ± 2^e`; it grows by one after an
    /// improving move of the hole and shrinks by one after a rejected one.
    pub initial_exponent: u32,
    /// The probability, as `[numerator, denominator]`, that an integer move draws its exponent
    /// uniformly up to the hole's bit bound instead.
    pub jump_probability: [u32; 2],
    /// The probability, as `[numerator, denominator]`, that an integer move goes in the
    /// direction of the hole's last improvement.
    pub keep_direction_probability: [u32; 2],
    /// The probability, as `[numerator, denominator]`, that a proposal changes a second hole.
    pub second_hole_probability: [u32; 2],
    /// The probability, as `[numerator, denominator]`, that a move picks a hole whose value the
    /// best case's scored guard read, when there is one.
    pub read_probability: [u32; 2],
    /// Whether a climb case that scores equal to the best case replaces it (a case of another
    /// proposer replaces it only when strictly better).
    pub accept_equal: bool,
    /// The most draws of a move per changed hole before an inadmissible move is given up.
    pub max_attempts: u32,
    /// Which rules' condition entries the cases record for the score:
    /// `target-and-keyed-predecessors` for a rule target (the target and its direct
    /// predecessors in the rule graph whose right-hand side keys the head of `<k>`, or all of
    /// them when none does), `none` for an observer target, whose score reads the observer's
    /// progress instead.
    pub condition_rules: String,
    /// The most condition entries recorded per rule and run (no rule is recorded under
    /// `condition-rules` `none`).
    pub condition_limit: u64,
    /// The largest recorded value, in term nodes; a larger one gives no signal.
    pub condition_value_size: u64,
    /// The probability, as `[numerator, denominator]`, that a proposal from a best case whose
    /// pool of run-time literals is not empty is a change from that pool (ARCHITECTURE 8.3,
    /// 8.4).
    pub runtime_probability: [u32; 2],
    /// The most comparisons the pool of run-time literals of one case holds.
    pub max_comparisons: u32,
    /// Which rules' condition entries the cases also record for the pools of run-time literals
    /// (`CorpusParameters::runtime_condition_rules`): `dictionary-guard-rules` for a rule
    /// target, `none` for an observer target.
    pub runtime_condition_rules: String,
    /// The rule-graph radius of `dictionary-guard-rules`: the rules at most this many edges
    /// before the target (and their higher-priority competitors) are recorded for the pools.
    pub runtime_guard_radius: u32,
}

impl ClimbParameters {
    /// The parameters of this build for a campaign whose target is `target`.
    #[must_use]
    pub fn for_target(target: &crate::target::TargetKind) -> Self {
        crate::proposers::climb::parameters(target)
    }
}

/// The fixed parameters of the dictionary proposer (ARCHITECTURE 8.3), which with the
/// definitions and the target decide its pool and its draws. They are constants of this build;
/// a change of any of them changes the case sequence and bumps [`crate::ENGINE_VERSION`].
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct DictionaryParameters {
    /// The harvest radius, in rule-graph edges before the target.
    pub radius: u32,
    /// The probability, as `[numerator, denominator]`, with which a hole whose pool is not
    /// empty takes a harvested value rather than a blind one.
    pub draw_probability: [u32; 2],
    /// The largest offset of an integer variant: a constant `v` also yields `v - expansion` ..
    /// `v + expansion` and `-v`.
    pub expansion: u32,
    /// A harvested constant's weight is `distance-weight-base ^ (radius - distance)`.
    pub distance_weight_base: u32,
    /// The probability, as `[numerator, denominator]`, with which a pool draw takes the
    /// harvested constant itself rather than one of its variants.
    pub exact_probability: [u32; 2],
}

impl DictionaryParameters {
    /// The parameters of this build.
    #[must_use]
    pub fn current() -> Self {
        crate::proposers::dictionary::parameters()
    }
}

/// The hard caps of the value generators (`crate::values`).
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct GenerationCaps {
    /// The largest bit length of any generated integer (`values::MAX_INT_BITS`).
    pub int_bits: u32,
    /// The largest generated length (`values::MAX_GENERATED_LENGTH`).
    pub length: u64,
    /// The largest depth of a generated data-sort term (`values::MAX_DEPTH`).
    pub depth: u32,
    /// The most values a generator enumerates (`values::generator::ENUMERATION_LIMIT`).
    pub enumeration: u64,
    /// The size budget of one generated value (`values::MAX_VALUE_SIZE`): one unit per
    /// constructor application or leaf, plus one per 64 bits of an integer and one per
    /// character or byte of a string.
    pub value_size: u64,
}

impl GenerationCaps {
    /// The caps of this build.
    #[must_use]
    pub fn current() -> Self {
        Self {
            int_bits: crate::values::MAX_INT_BITS,
            length: crate::values::MAX_GENERATED_LENGTH,
            depth: crate::values::MAX_DEPTH,
            enumeration: crate::values::generator::ENUMERATION_LIMIT,
            // 2^17: it fits.
            value_size: u64::try_from(crate::values::MAX_VALUE_SIZE).unwrap_or(u64::MAX),
        }
    }
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
    /// The main module, which the execution digest does not cover.
    pub main_module: String,
    /// The module whose grammar parses the program.
    pub syntax_module: String,
    /// The execution digest of its KORE definition, as text.
    pub execution_digest: String,
    /// `"source-execution"` or `"from-definition"` ([`crate::BackendRoute`]).
    pub route: String,
    /// [`digest_hex`] of the canonical provenance JSON of the frontend definition the program
    /// grammar is resolved from, with its source table, every source named relative to the
    /// main module's file ([`crate::CompiledDefinition::frontend_digest`]): the same sources
    /// compiled in another directory, or in process under another entry name, give the same
    /// digest, and a change of any byte of a source (a comment included) gives another. The
    /// execution digest does not cover it: two definitions with equal KORE can parse one
    /// program into different initial configurations.
    pub frontend_digest: String,
    /// The same digest of the execution definition that pattern targets and the
    /// normal-termination pattern are compiled in
    /// ([`crate::CompiledDefinition::execution_definition_digest`]).
    pub execution_definition_digest: String,
    /// [`digest_hex`] of `syntaxDefinition.kore` and of `macros.kore`, joined by a newline,
    /// with sources named as in [`Self::frontend_digest`] and the layout normalized
    /// ([`crate::CompiledDefinition::syntax_definition_digest`]): collection and data-sort
    /// values are printed from the one and read back through the other, so they decide which
    /// values round-trip (D19).
    pub syntax_definition_digest: String,
    /// [`digest_hex`] of this definition's initial configuration, as printed KORE, assembled
    /// by its own grammar with every hole at its anchor (or, when some hole has no anchor, at
    /// the first explicit assignment's values): it pins the grammar, the configuration-variable
    /// bindings and the stream defaults exactly. `None` when no complete assignment is known
    /// before the campaign runs; the frontend digest still covers the grammar.
    pub initial_configuration_digest: Option<String>,
    /// [`digest_hex`] of the rewrite order (ids joined by newlines) on the source-execution
    /// route; the order selects the one path `strategy: any` follows.
    pub execution_rewrite_order_digest: Option<String>,
}

/// How a campaign ended, with what it found. Every ending without a witness except
/// equivalence carries the bounded statement, so that no report of a campaign that stopped
/// early reads as a pass.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[expect(
    clippy::large_enum_variant,
    reason = "one outcome per campaign report; boxing the witness would change the public field"
)]
#[serde(
    tag = "status",
    rename_all = "kebab-case",
    rename_all_fields = "kebab-case",
    deny_unknown_fields
)]
pub enum CampaignOutcome {
    /// A witness was found and confirmed. A cancellation or abort during shrinking keeps this
    /// outcome: the witness was confirmed before it.
    WitnessFound {
        /// The witness.
        witness: Witness,
    },
    /// The budget ran out, or every proposer was exhausted, without a confirmed witness.
    NoWitnessFound {
        /// The bounded statement.
        no_witness: NoWitness,
    },
    /// Differential: equal execution digests (and rewrite orders) ended the campaign before any
    /// case (ARCHITECTURE 4.3).
    Equivalent,
    /// The campaign's judgement reads data ends (a differential target, or a rule or pattern
    /// target with `run-to-completion` and `data-end`), and the full critical-pair check of
    /// a definition it reads reports findings that are not assumed joined: no end of that
    /// definition is data, so no case could give a witness. Decided before any case
    /// (ARCHITECTURE 4.3); the findings are the report's `definition-findings`.
    NotComparable {
        /// The definitions without data: the baseline, the mutant, or both.
        sides: Vec<DefinitionRole>,
        /// The sentence: why no witness can be established, and what can change that.
        statement: String,
    },
    /// The rejection cap was reached (ARCHITECTURE 9.2).
    RejectedOut {
        /// The bounded statement.
        no_witness: NoWitness,
    },
    /// The caller's cancellation token stopped the campaign.
    Cancelled {
        /// The bounded statement.
        no_witness: NoWitness,
    },
    /// A failure every case would repeat ended the campaign (a failed solver prelude, a solver
    /// that does not start), the client's observer panicked, or the campaign's backends did not
    /// rebuild.
    Aborted {
        /// What kind of failure.
        kind: AbortKind,
        /// Why.
        reason: String,
        /// For a panicking observer, the case it panicked in.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        case: Option<u64>,
        /// For a panicking observer, the case's hole values, in declaration order.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        holes: Vec<CrashHole>,
        /// For a panicking observer, what panicked.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        panic: Option<PanicRecord>,
        /// The bounded statement.
        no_witness: NoWitness,
    },
}

/// One finding of a definition's full critical-pair check (`k_rust_backend::data_term`), as the
/// campaign's data judgement read it (ARCHITECTURE 4.3). Terms are written as K text where the
/// definition's syntax prints them, and otherwise as applications of K labels; variables by the
/// names the equations give them, a variable the check introduced with a `'` and a number.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct DefinitionFinding {
    /// Which definition's check reports it.
    pub side: DefinitionRole,
    /// `genuine` when a ground instance is exhibited at which both equations apply and the input
    /// has two different results, two normal forms or a normal form and an undefined value
    /// ([`FindingInstance::stuck`]), so k-rust's result for that input depends on the order in
    /// which it tries the equations; `decided` for a precondition row that an equation is headed by a
    /// constructor or an injection or indexed at a collection or a bare variable, or an equation
    /// whose right-hand side leaves a variable unbound (a fact about the definition as written, which no assumption
    /// removes); `undecided` otherwise: not shown to join, which may
    /// be a limit of the check as well as an input with two different results.
    pub verdict: FindingVerdict,
    /// A pair of equations, one equation, or a precondition row.
    pub kind: FindingKind,
    /// The name `assume-joined` takes: `FIRST,SECOND@POSITION` for a pair, `hook:EQUATION` or
    /// `equation:EQUATION` for a finding about one equation, `precondition:EQUATION` (or
    /// `precondition:KIND:LABELS`) for a precondition row. `assume-joined` refuses the name of a
    /// `decided` finding.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    /// The equations, each by its written position `FILE:LINE:COLUMN` (else its label, its
    /// unique id, or the overloaded pair of a compiler-generated overload axiom): the one whose
    /// left-hand side holds the overlap, then the one applied at the position.
    pub equations: Vec<String>,
    /// For a pair, the position in the first equation's left-hand side: `root`, or the argument
    /// indexes joined by `.`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub position: Option<String>,
    /// What the check found, in words.
    pub reason: String,
    /// The overlapped term both equations rewrite, when the check reached one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub overlap: Option<String>,
    /// The two one-step reducts of the overlap (the first equation's, then the second's), when
    /// the check computed them; `\bottom` for an undefined one.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub reducts: Vec<String>,
    /// The conjunction of both equations' `requires` at the overlap, as the check simplified
    /// it, when it is not `true`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub conditions: Option<String>,
    /// For a genuine finding, the ground instance that shows it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub instance: Option<FindingInstance>,
    /// Whether the campaign assumed this finding resolved (`assume-joined`).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub assumed: bool,
}

/// [`DefinitionFinding::verdict`].
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum FindingVerdict {
    /// A ground instance shows the two equations giving two different normal forms, or a normal
    /// form and an undefined value (`FindingInstance::stuck`).
    Genuine,
    /// Not shown to join; possibly a limit of the check.
    Undecided,
    /// A fact the check decides about the definition as written, not a limit of it: an
    /// equation is headed by a constructor or an injection (it rewrites such terms) or indexed at
    /// a collection or a bare variable (its axiom equates the collection terms it describes with
    /// its right-hand side, or it is offered at every subject), terms the data judgement reads
    /// as free, so they are not distinct normal forms (a precondition row); or an equation's
    /// right-hand side leaves a variable unbound by its left-hand side,
    /// so read as written it equates every value of that sort. No end of the definition is
    /// data. It cannot be assumed (`assume-joined`): fix the equation.
    Decided,
}

/// [`DefinitionFinding::kind`].
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum FindingKind {
    /// Two equations whose overlap the check does not join.
    Pair,
    /// One equation the evaluator does not apply to every subject it describes.
    Equation,
    /// A violated precondition of the check.
    Precondition,
}

/// The ground instance of a genuine finding.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct FindingInstance {
    /// Each variable's value, `NAME = VALUE`.
    pub assignment: Vec<String>,
    /// The overlap under the assignment.
    pub overlap: String,
    /// What each reduct evaluates to under the assignment: two different normal forms, or a
    /// normal form and an undefined value.
    pub values: Vec<String>,
    /// For each of `values`, in order, the stuck application it holds: `null` when it is built
    /// from data only, `total` when it is a normal form holding an application of a declared
    /// total function that no equation rewrites, `partial` when it holds an application of a
    /// declared partial function that no equation rewrites, and is undefined in the normal-form
    /// reading (k-rust returns the stuck term). At most one side is `partial`.
    pub stuck: Vec<Option<FindingStuck>>,
}

/// [`FindingInstance::stuck`].
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum FindingStuck {
    /// A normal form holding a stuck application of a declared total function.
    Total,
    /// An undefined value: a stuck application of a declared partial function.
    Partial,
}

/// The rule a rule target resolved to: its unique id and its names.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct TargetRule {
    /// The unique id the campaign judges coverage and traces by.
    pub id: String,
    /// Its kind, label and source locations.
    pub name: RuleName,
}

/// Counts over every case (ARCHITECTURE 9.3).
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct Totals {
    /// Cases run, rejected cases included; confirmation and shrink runs excluded.
    pub cases: u64,
    /// Backend work over every execution, confirmation and shrinking included, with every case
    /// charged at least 1 ([`Budget::Work`]).
    pub work: u64,
    /// Cases per class; classes with no case are omitted.
    pub classes: BTreeMap<OutcomeClass, u64>,
    /// Rejected cases per thousand cases, rounded down.
    pub rejection_rate_permille: u64,
    /// Rejected cases per reason; reasons with no case are omitted. The counts sum to the
    /// `rejected` entry of [`Self::classes`].
    pub rejections: BTreeMap<RejectionReason, u64>,
    /// `unsupported` cases per reason ([`UnjudgedReason`]); reasons with no case are omitted.
    /// Each case is counted once, under the first of its reasons in [`UnjudgedReason`]'s order,
    /// so the counts sum to the `unsupported` entry of [`Self::classes`].
    #[serde(default)]
    pub unsupported_reasons: BTreeMap<UnjudgedReason, u64>,
    /// `baseline-incomplete` cases per reason, counted as [`Self::unsupported_reasons`] are;
    /// the counts sum to the `baseline-incomplete` entry of [`Self::classes`].
    #[serde(default)]
    pub baseline_incomplete_reasons: BTreeMap<UnjudgedReason, u64>,
    /// For each reason of [`Self::unsupported_reasons`] whose facts name a hook, the hooks they
    /// name over the cases counted under it (UNNAMED-HOOK, [`ReasonHooks`]): the hooks that read
    /// an implementation-chosen value for `implementation-chosen-value`, `run-fact-off-leaves`
    /// and `kill-without-evidence`, the unsupported hooks for `halt-unsupported-hook`,
    /// `halt-unsupported-construct` and `unsupported-hook`, and for `end-not-comparable:*` and
    /// `query-not-confirmable:*` those of the condition (as [`Comparability::hooks`], except
    /// that `query-not-confirmable:unsupported-hook` reads the run's records only, as the query
    /// condition does, never the load's). Each
    /// case's hooks are read from the run its reason was read from. Reasons whose cases name no
    /// hook are omitted; absent when empty.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub unsupported_hooks: BTreeMap<UnjudgedReason, ReasonHooks>,
    /// The same for [`Self::baseline_incomplete_reasons`]; absent when empty.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub baseline_incomplete_hooks: BTreeMap<UnjudgedReason, ReasonHooks>,
    /// Rules the cases reached (see [`CoverageTotals`]).
    pub coverage: CoverageTotals,
    /// Cases in which the target rule was blocked (ARCHITECTURE 6.2).
    pub target_blocked: u64,
    /// For a pattern target (a negated property included), how many end leaves (`stuck`,
    /// `trivial` or `terminal`) of the cases inside the determinism contract matched the
    /// pattern's configuration without its `requires`, whatever the `requires` gave there
    /// (true, false or undecided); a leaf counts when it is clean apart from the target's own
    /// undecided verdict, so a leaf unclean for another reason (a chosen value, a contradicted
    /// claim, a state that is not ceil-free) is left out even when its configuration matched. 0 means no end's configuration matched the pattern's (a misspelled
    /// key, a cell no end holds), so a negated property held vacuously, and a warning says so when some case had an end clean enough to be judged (it counts only those cases: a case whose every end is unclean judged nothing, and its `unsupported` reason says why). Information, not a class: each leaf is matched on its own. Absent for
    /// every other target, and when no case inside the determinism contract was executed.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub pattern_body_matches: Option<u64>,
    /// For a pattern target at `final`, how many cases inside the determinism contract had an
    /// end clean enough to be judged against the pattern's configuration (each such end is one
    /// [`Self::pattern_body_matches`] would count if it matched): with it, a 0 there tells a
    /// pattern no judged end holds (a misspelled key) from a campaign that judged no end at all.
    /// Present exactly when [`Self::pattern_body_matches`] is.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub pattern_body_judged: Option<u64>,
    /// The best score the scored cases reached (ARCHITECTURE 6.4): present exactly when a
    /// proposer scores the campaign's cases (the climb or the solve proposer), so that a reader
    /// sees whether the guided search came near the target; `None` when no proposer scores.
    pub best_score: Option<BestScore>,
    /// Cases outside the determinism contract (ARCHITECTURE 5.4): a clock, a solver `unknown`, a
    /// stop for lack of stack or an allowance refusal decided them, so another run may end them
    /// otherwise. The schedule, the guided proposers and the budget observe every case, so a
    /// re-run with the same inputs may differ from the first of them on.
    pub outside_determinism: u64,
    /// The first case a re-run with the same inputs may differ at, counted from 0: the first
    /// case outside the determinism contract, or the first case proposed after a solve run
    /// outside it ([`SolveTotals::outside_determinism`], which decides what the solve proposer
    /// proposes), whichever comes first; absent when there is neither. A re-run reproduces this
    /// report's cases before it, and may differ from it on (FZ-REPLAY-WHOLE S3, fix round S-C).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_outside_determinism: Option<u64>,
    /// Candidates that reached the target but were not confirmed: the confirmation failed,
    /// disagreed (an engine defect) or was cancelled. One of them may be a real witness.
    pub unconfirmed: u64,
    /// [`digest_hex`] chained over the proposed values of every case, in order (each step
    /// hashes the previous digest and the canonical JSON of the case's values; the empty
    /// campaign has the digest of the empty input). It pins the case sequence itself, so a
    /// client can detect two runs that diverged even when every case had the same class.
    pub case_sequence_digest: String,
    /// The solve proposer's counts, present exactly when it has a positive weight; absent from
    /// the JSON otherwise.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub solve: Option<SolveTotals>,
    /// The backend work of the runs that examined crashes: each new crash signature's
    /// confirmation, its shrinking and the shrunk case's confirmation. Charged to no budget and
    /// not part of [`Self::work`], so crash findings move no case of the campaign. Absent
    /// when 0.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub crash_work: u64,
    /// What the client's witness filter refused and what its repairs cost ([`FilterTotals`]);
    /// absent when it refused nothing.
    #[serde(default, skip_serializing_if = "FilterTotals::is_empty")]
    pub filter: FilterTotals,
    /// The holes' finite domain ([`DomainTotals`]): present exactly when every hole has finitely
    /// many values and their assignments are few enough for the campaign to end once each has
    /// run (at most 4096), so that a reader need not read the statement to learn that more
    /// cases of this program cannot help (final review ux S6).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub domain: Option<DomainTotals>,
    /// The differential `work-bound` cases in which the work bound stopped the mutant while the
    /// baseline reached all its ends ([`DivergingTotals`]): the mutant may not terminate on this
    /// program, which no bound decides. Absent when there is none.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub diverging: Option<DivergingTotals>,
    /// The last case (counted from 0) whose run added a rule to [`Self::coverage`] (`applied` or
    /// `matched`); absent when no case added one. A value far below [`Self::cases`] says the
    /// cases stopped reaching new rules long ago, so more cases of this program and these holes
    /// are unlikely to reach a new rule; it is no proof that none can (GUIDE-USABILITY 3). The
    /// no-witness statement says so only when at least 30 cases followed it, and at least as
    /// many as came up to it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub coverage_last_grew: Option<u64>,
}

/// The holes' finite domain ([`Totals::domain`]).
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct DomainTotals {
    /// How many assignments of the holes the domain has: the product of each hole's number of
    /// values, as generated.
    pub assignments: u64,
    /// How many distinct assignments of the domain the cases ran (rejected before running
    /// included).
    pub tried: u64,
    /// Every assignment ran, so the campaign ended without spending its budget (`Domain
    /// exhausted`): more cases would only repeat them.
    pub exhausted: bool,
}

/// The differential cases in which the mutant may not terminate ([`Totals::diverging`]).
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct DivergingTotals {
    /// How many `work-bound` cases stopped the mutant at the work bound while no bound and no
    /// clock cut the baseline.
    pub cases: u64,
    /// The largest work the baseline spent in one of them, to reach all its ends.
    pub baseline_work: u64,
}

/// What a campaign's witness filter refused and what its repairs cost ([`Totals::filter`],
/// [`crate::filter`]).
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct FilterTotals {
    /// Refused hits per cause; each is a case counted `unsupported` with the reason
    /// `client-refused`.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub refused: BTreeMap<String, u64>,
    /// Shrink candidates that hit, refused before or after their confirmation (no case).
    #[serde(default, skip_serializing_if = "is_zero")]
    pub refused_shrink_candidates: u64,
    /// Refused hits whose repair ran at least one candidate.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub repairs: u64,
    /// Refused hits left unrepaired because their cause's repairs had failed
    /// [`crate::filter::MAX_FAILED_REPAIRS`] times.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub repairs_skipped: u64,
    /// Repair candidates run (no case each).
    #[serde(default, skip_serializing_if = "is_zero")]
    pub repair_candidates: u64,
    /// The work of the repair candidates' runs and confirmations, included in [`Totals::work`].
    #[serde(default, skip_serializing_if = "is_zero")]
    pub repair_work: u64,
}

impl FilterTotals {
    /// Whether the filter refused nothing (so nothing was repaired).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        *self == Self::default()
    }
}

/// The first refused hit of one cause ([`FuzzReport::client_refusals`]).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct ClientRefusal {
    /// The refusal's cause token.
    pub cause: String,
    /// The refusal of this case, in the client's words.
    pub detail: String,
    /// What the client suggests.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub remedy: Option<String>,
    /// The case refused first with this cause.
    pub case: u64,
    /// Its hole values, in declaration order.
    pub holes: Vec<CrashHole>,
    /// The hits refused with this cause.
    pub count: u64,
    /// Whether this case (the cause's first refused hit, `case`) was repaired into the
    /// campaign's witness, whose `repaired-from` then names it; a later refused hit of the cause
    /// that was repaired leaves it `false`.
    pub repaired: bool,
}

/// The refused hit a repaired witness came from ([`Witness::repaired_from`]).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct RepairedFrom {
    /// The refused case.
    pub case: u64,
    /// Its hole values, in declaration order.
    pub holes: Vec<CrashHole>,
    /// The cause of its refusal.
    pub cause: String,
}

/// Whether a count is 0, for the counts a report leaves out when they are. (A `u64` is
/// "trivially copied" only where it is no wider than a pointer, so the lint fires on 64-bit
/// targets alone.)
#[cfg_attr(
    target_pointer_width = "64",
    expect(
        clippy::trivially_copy_pass_by_ref,
        reason = "serde's `skip_serializing_if` passes a reference"
    )
)]
fn is_zero(count: &u64) -> bool {
    *count == 0
}

/// The best score of a campaign whose proposers score its cases ([`Totals::best_score`];
/// ARCHITECTURE 6.4). Only `miss` cases are scored (R-18): a bounded or unclean case's signals
/// stop early, and a rejected case ran nothing.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct BestScore {
    /// The `miss` cases that were scored.
    pub scored_cases: u64,
    /// The best score among them, the earliest case on a tie; absent when no case was scored.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub best: Option<ScoreValue>,
}

/// One case's score, compared lexicographically, the level first, smaller being better
/// (ARCHITECTURE 6.4; the rustdoc of `crate::score`).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct ScoreValue {
    /// The case that reached it.
    pub case: u64,
    /// For a rule target, the rule-graph distance to the target: 0 when the case entered the
    /// target's `requires`, 1 when it entered a direct predecessor's that failed, and so on;
    /// absent when no rule the case applied or entered reaches the target in the rule graph.
    /// Always 0 for an observer target.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub level: Option<u64>,
    /// The guard distance at that level, an exact fraction `NUMERATOR/DENOMINATOR` in lowest
    /// terms: 0 when the guard holds, otherwise the sum (over a conjunction) or the least (over
    /// a disjunction) of its atoms' normalized distances `d / (d + 1)`, each below 1; absent
    /// when no instance gave a distance (no signal, worse than every distance).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub guard_distance: Option<String>,
}

/// Which normal end the classes of each definition of a campaign rest on (ARCHITECTURE 5.2):
/// the campaign's pattern, or the default on the one `<k>` cell or on every `<k>` cell.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct NormalEnds {
    /// The baseline's.
    pub baseline: NormalEndKind,
    /// The mutant's, for a differential campaign.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mutant: Option<NormalEndKind>,
}

/// The rules the campaign's cases reached (ARCHITECTURE 6.1, 9.3).
///
/// Every executed case inside the determinism contract contributes, whatever its class: a
/// bounded case's coverage is what it reached before the bound, which is deterministic. A
/// rejected case executes nothing, and a case outside the determinism contract (a timeout, say)
/// reached a clock- or thread-dependent set, so neither contributes. Confirmation and shrink
/// runs repeat or vary a case and do not contribute either. Only `miss` cases feed the
/// proposers' feedback (R-18); that restriction is about guidance, not about this total.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct CoverageTotals {
    /// Rule ids in some case's coverage `applied`.
    pub applied: BTreeSet<String>,
    /// Rule ids in some case's coverage `matched`.
    pub matched: BTreeSet<String>,
    /// The names of every id in [`Self::applied`] or [`Self::matched`] that the catalog of the
    /// definition whose coverage the cases record (the mutant's in a differential campaign)
    /// holds: kind, label and source locations ([`RuleName`]), so that an author reads which
    /// rules the campaign reached. One entry per reached id, so its size is bounded by the
    /// catalog's.
    pub names: BTreeMap<String, RuleName>,
}

/// Why a case was `rejected` (ARCHITECTURE 2.3, 5.3).
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum RejectionReason {
    /// A hole's generator failed to draw a value (`values::Generator::try_generate`); the case
    /// was not run.
    Generation,
    /// A value violates its hole's sort or constraints.
    Constraint,
    /// A value cannot be printed as K text or KORE at its hole's sort.
    Print,
    /// The instantiated program or a binding does not parse, or the configuration does not
    /// assemble.
    Assembly,
    /// A value did not parse back, at its hole's position, to the value intended.
    RoundTrip,
    /// The backend refused the initial state (`vacuous` at depth 0).
    BackendRefused,
}

impl RejectionReason {
    /// The reason's name in the report (`round-trip`, `backend-refused`).
    #[must_use]
    pub fn name(self) -> String {
        serde_json::to_value(self)
            .ok()
            .and_then(|name| name.as_str().map(str::to_owned))
            .unwrap_or_default()
    }
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
    /// The clean-leaf facts that were checked (ARCHITECTURE 5.2), and for a differential target
    /// the conditions of ARCHITECTURE 4.3.
    pub clean_leaf_facts: Vec<String>,
    /// The `krun` command line that re-runs the shrunk witness when there is one, otherwise the
    /// first, on the baseline: the instantiated program passed with `-e`, the configuration
    /// variables with `-c`, `--io off`, the strategy of the path mode (`all` for a differential
    /// baseline, which runs all paths), the depth bound and the solver options, with the
    /// compiled definition's directory left as `<definition-dir>`. `krun` has no work bound, so
    /// a campaign bounded by `max-work` says so in a trailing comment. For a pattern target
    /// `at: any-state` the line is the search `--search-all --pattern '<pattern>'` in place of
    /// the strategy, which explores every reachable configuration: with no depth bound it ends
    /// only when they are finitely many, and the trailing comment says that it may not terminate.
    /// `None` when no `krun` run is equivalent: a KORE-template program, a program without
    /// `$PGM`, or a backend on the `from-definition` route (krun orders rules by the compiler's
    /// rewrite order).
    pub krun_command: Option<String>,
    /// For a differential witness, the same command line on the mutant, whose compiled
    /// directory is left as `<mutant-dir>`: strategy `all` for a removed end (judged against
    /// the mutant's every path) or the all-paths mode, `any` for an added end in the one-path
    /// mode. Absent for every other target, and when no `krun` run is equivalent.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mutant_krun_command: Option<String>,
    /// For a witness the client's witness filter repaired ([`crate::filter`]): the refused hit
    /// its repair started from, which `first` replaces; absent otherwise.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub repaired_from: Option<RepairedFrom>,
}

/// One confirmed witness case (ARCHITECTURE 2.6).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct WitnessCase {
    /// The hole overlay with values, in declaration order.
    pub holes: Vec<HoleValue>,
    /// The instantiated program text: the program with each span hole's K text in its span,
    /// which re-enters the witness as a test with [`Self::config_vars`]. Absent for a KORE
    /// template and a campaign without a program text.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub program: Option<String>,
    /// The instantiated configuration-variable bindings, keyed by the name the campaign's
    /// program gives (`ProgramSource::config_vars`): each binding's text with every span hole's
    /// K text in its span, or a configuration-variable hole's K text as the whole binding. With
    /// [`Self::program`] it is the whole input the witness re-enters with (the `krun` lines carry
    /// the same texts quoted in `-c`). Empty, and absent from the JSON, for a KORE template and a
    /// program without bindings.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub config_vars: BTreeMap<String, String>,
    /// The class confirmation gave (`hit`).
    pub class: OutcomeClass,
    /// What each definition's run started from and ended in: the baseline, then for a
    /// differential witness the mutant, whose killing end is not among the baseline's ends
    /// (ARCHITECTURE 4.3).
    pub sides: Vec<WitnessSide>,
    /// Where the target was reached.
    pub reaching: Reaching,
    /// For a differential witness, whether the mutant added an end or removed one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kill: Option<KillKind>,
    /// The step count of the reaching leaf (the killing mutant leaf of a differential
    /// witness). Absent for a hit of the whole run, which names no leaf: a coverage-mode rule
    /// target over several leaves (ARCHITECTURE 5.3, D16), whose witness is the case with every
    /// leaf's configuration in `sides`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub steps: Option<u64>,
    /// For a rule or pattern witness, whether the program's run of every path is one kink can
    /// compare (`crate::Target::comparable`, P7-ADDENDUM section 4): with the `comparable-end`
    /// option it holds on every witness. Without the option, a case that ran one path or
    /// stopped at the target's rule is judged by one more run of every path, made outside the
    /// case after the campaign's search, so the judgement may name a fact that breaks
    /// determinism ([`Comparability::reproducible`]). Absent for every other target.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub comparable: Option<Comparability>,
}

/// Whether a witness program's run of every path is one kink can compare
/// ([`WitnessCase::comparable`]; `crate::exec::comparable::end_conditions`).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct Comparability {
    /// It is: no condition fails.
    pub holds: bool,
    /// The conditions that fail, in [`ComparableCondition`]'s order, each once; empty exactly
    /// when [`Self::holds`].
    pub reasons: Vec<ComparableCondition>,
    /// For each condition of [`Self::reasons`] whose facts name a hook, the hooks the judged run
    /// names (UNNAMED-HOOK, [`ReasonHooks`]): `implementation-chosen-value` the hooks of the
    /// leaves' marks, `run-fact-off-leaves` those of the run's marks no leaf carries,
    /// `unsupported-hook-unevaluated` the hooks of the leaves' diagnostics, `halt` the hook of
    /// each leaf that halted on an unsupported hook, and `unsupported-hook` the hooks of the
    /// run's and the load's records. Absent when empty.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub hooks: BTreeMap<ComparableCondition, ReasonHooks>,
}

impl Comparability {
    /// Whether the judgement repeats on every run of its case: it names no condition that
    /// breaks determinism ([`ComparableCondition::breaks_determinism`]), so its run was inside
    /// the determinism contract and every condition it names, and whether it holds, is a
    /// function of the case. A judgement that names a clock, a solver `unknown`, a stop for lack
    /// of stack or an allowance refusal may name other conditions, or hold, on another run.
    /// So may one that names `run-failed`: a run that fails to start (a solver prelude refused
    /// by the environment, outside the case for a judgement made after shrinking) says nothing
    /// about the case. One that holds is always reproducible.
    #[must_use]
    pub fn reproducible(&self) -> bool {
        !self.reasons.iter().any(|condition| {
            condition.breaks_determinism()
                || matches!(
                    condition,
                    ComparableCondition::RunFailed | ComparableCondition::Crash
                )
        })
    }
}

/// Where a witness case reached its target.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct Reaching {
    /// The side whose leaf reached it: the baseline for a rule or pattern target, the mutant
    /// for an added end, the baseline for a removed end (the baseline end the mutant cannot
    /// reach).
    pub role: DefinitionRole,
    /// The index of that leaf in the side's `final-configurations`; absent for a hit of the
    /// whole run (D16), which rests on every leaf, and for a pattern target `at: any-state`,
    /// whose reaching configuration names no leaf.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub leaf: Option<u64>,
    /// For an observer target, the step of that leaf's path at which the observer answered
    /// `Hit`: the number of committed rewrite steps from the initial configuration to the
    /// configuration that step reached, at least 1 and at most the case's `steps`, since the
    /// run continues to its end after the observer accepts (ARCHITECTURE 9.2). For a pattern
    /// target `at: any-state`, the depth of the reaching configuration ([`Self::configuration`]),
    /// counted the same way, 0 for the initial configuration: the first clean reach in the run's
    /// depth-first order, which may exceed every leaf's depth (a path a bound cut after the
    /// reach) and need not be the least depth at which some path reaches the target
    /// (ARCHITECTURE 4.1, FZ-STATESET-MATCH). Absent for every other target.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub step: Option<u64>,
    /// For a pattern target `at: any-state`, the configuration that reached it, as KORE text:
    /// a state the run reached at [`Self::step`] on a clean prefix, which the side's
    /// `final-configurations` need not hold (FZ-STATESET-MATCH). Absent for every other target.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub configuration: Option<String>,
}

/// How a differential witness kills the mutant (ARCHITECTURE 4.3).
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum KillKind {
    /// The mutant reaches an end the baseline cannot.
    AddedEnd,
    /// The baseline reaches an end the mutant cannot, judged against the mutant's all-paths
    /// run (the all-paths mode, or the one-path mode's re-run).
    RemovedEnd,
}

/// One definition's run of a witness case.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct WitnessSide {
    /// Baseline or mutant.
    pub role: DefinitionRole,
    /// The concrete initial configuration this definition's grammar assembled, as KORE text.
    pub initial_configuration: String,
    /// Every leaf's configuration, as KORE text, in the backend's order.
    /// [`WitnessCase::reaching`] indexes it. For a differential witness, a side's ends are the
    /// entries whose halt ([`Self::halts`]) is `stuck`: an undefined step's entry is a
    /// configuration that is not stuck and has no successor, whose outcome is undefinedness, no
    /// end (ARCHITECTURE 4.3).
    pub final_configurations: Vec<String>,
    /// The halt of each leaf of [`Self::final_configurations`], in the same order, as the
    /// backend names it (`stuck`; `trivial` for an undefined step; `depth-bound`, ...), for every
    /// witness kind. Replay compares it with the configurations.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub halts: Vec<HaltReasonOutput>,
    /// For each leaf of [`Self::final_configurations`], in the same order, the unique id of the
    /// rule whose step is undefined at a `trivial` leaf, when the backend names one, and `null`
    /// for every other leaf; absent when no leaf names one. Replay compares it when present.
    #[serde(default, skip_serializing_if = "no_rule")]
    pub undefined_rules: Vec<Option<String>>,
    /// The backend work of this side's run (`ExecutionResult::work`, the states it visited):
    /// for a differential witness, the run its ends come from (the mutant's run of every path for
    /// a removed end of the one-path mode).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub work: Option<u64>,
}

/// Whether no leaf names an undefined step's rule ([`WitnessSide::undefined_rules`]).
fn no_rule(rules: &[Option<String>]) -> bool {
    rules.iter().all(Option::is_none)
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
    /// The value as K text; omitted for a KORE-template hole whose value has no K text (the
    /// template needs only the KORE, so a definition without K-text syntax still runs it).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub k_text: Option<String>,
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
    /// The sentence: the cases run, the path mode explored, and the bound to raise. In
    /// one-path mode it always names the all-paths option: no execution result says whether a
    /// one-path run passed over another applicable rule (R-15), so the engine cannot restrict
    /// the suggestion to campaigns where one did.
    pub statement: String,
    /// The path mode the cases ran in.
    pub path_mode: PathMode,
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

/// One refusal that a hole's override admitted (ARCHITECTURE 2.4). A hole has one entry per
/// refused sort: its own sort's refusal first, then those of the sorts its values may contain.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct SortOverride {
    /// The hole's name.
    pub hole: String,
    /// The refused sort: the hole's own sort, or a sort its values may contain.
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

/// The first case of each of the classes `stuck` and `undefined` of the semantics under test
/// (FZ-INCIDENTAL).
///
/// A rule missing from the semantics, or a partiality its author did not intend, is invisible to
/// every target: no mutant of an absent rule exists, a baseline and its mutant get stuck alike,
/// and coverage lists the rules that exist. The cases a campaign runs anyway show it, so the
/// first case of each class is kept. It is information, not a failure: a K semantics often
/// leaves a program stuck on purpose (an ill-typed program, a division by zero that the
/// language leaves without meaning).
///
/// The classes are the classes of one run ([`OutcomeClass`]), with the meaning they have under
/// the normal end the report's [`NormalEnds`] names:
///
/// - `stuck`: some leaf is a clean, decided `stuck` leaf that is not a natural end (an abnormal
///   stop: no rule applies, and the configuration is not finished under the campaign's pattern,
///   the one `<k>` cell holding `.K`, or every `<k>` cell holding `.K`), and no leaf has a class
///   of higher precedence (an undefined step, a bound, a clock stop, an unsupported leaf).
/// - `undefined`: some leaf is a clean undefined step (halt `trivial`: a rule applied whose
///   result is undefined there, so the path ends in no configuration), and no leaf has a class
///   of higher precedence. An undefined step is not an end: its leaf is the configuration
///   before the step.
///
/// In a rule, pattern or observer campaign that run is the case's, so the finding's class is
/// the case's class, or, for a case that [`UnjudgedReason::FiredOffTrace`] made `unsupported`,
/// the class its leaves gave (that reason says the target cannot be judged, while the leaves
/// are the run's own). In a differential campaign the semantics under test is the baseline, so the
/// finding comes from the baseline's own run of the case (all paths), classed alone, whatever
/// the pair's class: a stop or undefined step only the mutant has is never a finding (it is a
/// kill, or under `run-to-completion` the pair's own disagreement, which its class reports). A
/// case that ends the campaign with a witness gives no finding; its witness shows its runs.
/// Only findings whose run is inside the determinism contract are kept, so a finding
/// reproduces; in a differential case that run is the baseline's, so a clock or stack fact of
/// the mutant's run alone (which puts the case outside the contract) keeps it. Keeping one
/// changes no class, no case and no budget: the case already ran, and nothing is re-run or
/// shrunk.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct Incidentals {
    /// The first `stuck` case; absent when no case was `stuck`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stuck: Option<IncidentalCase>,
    /// The first `undefined` case; absent when no case was `undefined`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub undefined: Option<IncidentalCase>,
}

impl Incidentals {
    /// Whether neither class had a case.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.stuck.is_none() && self.undefined.is_none()
    }

    /// One line per finding, `stuck` first, worded as information for a reader (the summary of
    /// `krust fuzz` prints them).
    #[must_use]
    pub fn lines(&self) -> Vec<String> {
        let mut lines = Vec::new();
        if let Some(case) = &self.stuck {
            let steps = plural(case.steps, "step");
            lines.push(case.line(
                &format!("got stuck before a natural end after {steps}"),
                "at",
                "no rule applies there: a missing rule, or a stop the semantics intends",
                "stuck",
            ));
        }
        if let Some(case) = &self.undefined {
            // The heads are the configuration the step rewrote, so the step is taken on them.
            lines.push(case.line(
                &format!(
                    "took an undefined step at step {}",
                    case.steps.saturating_add(1)
                ),
                "on",
                "a rule applied whose result is undefined there: a partiality the semantics may \
                 or may not intend",
                "undefined",
            ));
        }
        lines
    }
}

/// "1 step" or "N steps".
fn plural(count: u64, noun: &str) -> String {
    if count == 1 {
        format!("1 {noun}")
    } else {
        format!("{count} {noun}s")
    }
}

/// One incidental finding: a case whose run of the semantics under test was `stuck` or
/// `undefined` ([`Incidentals`]).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct IncidentalCase {
    /// The case's number, counted from 0 in the order the cases ran, as engine defects and
    /// warnings number cases.
    pub case: u64,
    /// The hole overlay with values, in declaration order.
    pub holes: Vec<HoleValue>,
    /// How many leaves the run has: the finding's leaf is one path's outcome among them.
    pub leaves: u64,
    /// The index of the finding's leaf among them, in the backend's order.
    pub leaf: u64,
    /// The leaf's depth (rewrite steps on its path); an undefined step is the step after it.
    pub steps: u64,
    /// The first item of each `<k>` cell of the leaf that holds one, in the configuration's
    /// order, as K text when the definition's unparser prints it, else as its head's K label.
    /// A stuck leaf is stuck in every thread, so each item is where a thread stopped (a thread
    /// waiting for another included); for an undefined step, whose leaf is the configuration
    /// before the step, the items the step may have rewritten. Absent when no `<k>` cell holds
    /// an item.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub k_heads: Vec<String>,
    /// The leaf's configuration, as KORE text.
    pub configuration: String,
    /// The `krun` command line that re-runs the case's run of the semantics under test (in a
    /// differential campaign the baseline, on all paths), written as [`Witness::krun_command`]
    /// is; `None` when no `krun` run is equivalent (a KORE-template program, the
    /// `from-definition` route, a program without `$PGM`). `krun` reports an undefined step only
    /// when every path of the run takes one; when another path does not, the line says so in a
    /// trailing comment, and the finding is leaf [`Self::leaf`] of [`Self::leaves`].
    pub krun_command: Option<String>,
    /// Whether the run is a differential campaign's baseline run of the case, on all paths and
    /// classed alone ([`Incidentals`]), so that its class need not be the case's (absent when
    /// `false`: the run is the case's own).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub baseline_run: bool,
}

impl IncidentalCase {
    /// The summary line: the case, its holes, which run (a differential baseline's says so),
    /// what happened (`what`), where (the `<k>` heads after the preposition `place`), why it
    /// may matter (`meaning`), and the report key (`key`) that holds the rest.
    fn line(&self, what: &str, place: &str, meaning: &str, key: &str) -> String {
        /// The longest hole value or `<k>` item a line prints in full, in characters.
        const SHOWN: usize = 80;
        /// The most `<k>` items a line prints.
        const HEADS: usize = 4;
        let cut = |text: &str| {
            if text.chars().count() <= SHOWN {
                text.to_owned()
            } else {
                format!("{}…", text.chars().take(SHOWN).collect::<String>())
            }
        };
        let holes = if self.holes.is_empty() {
            String::new()
        } else {
            let values = self
                .holes
                .iter()
                .map(|hole| {
                    format!(
                        "{} = {}",
                        hole.name,
                        cut(hole.k_text.as_deref().unwrap_or(&hole.kore))
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!(" ({values})")
        };
        let path = if self.leaves > 1 {
            format!(" on one of its {} paths", self.leaves)
        } else {
            String::new()
        };
        let at = if self.k_heads.is_empty() {
            String::new()
        } else {
            let heads = self
                .k_heads
                .iter()
                .take(HEADS)
                .map(|head| format!("`{}`", cut(head)))
                .collect::<Vec<_>>()
                .join(" | ");
            let more = self.k_heads.len().saturating_sub(HEADS);
            let more = if more > 0 {
                format!(" and {more} more")
            } else {
                String::new()
            };
            format!(" {place} {heads}{more}")
        };
        let run = if self.baseline_run {
            ", in the baseline's own run on all paths (not the pair's class),"
        } else {
            ""
        };
        format!(
            "incidental (information, not a failure): case {}{holes}{run}{path} {what}{at}; \
             {meaning}. The report's `incidental.{key}` holds its configuration and krun line.",
            self.case
        )
    }
}

/// What a panic left: its message and, when the campaign's panic hook saw it, its location
/// (`file:line:column`, as the compiler wrote it).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct PanicRecord {
    /// The panic's message (its payload's text).
    pub message: String,
    /// Where it was raised; absent when the hook did not run (a hook an embedder installed
    /// after the campaign's replaced it, or a re-raised panic whose hook was not the campaign's).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub location: Option<String>,
}

/// Why a campaign aborted ([`CampaignOutcome::Aborted`]).
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum AbortKind {
    /// The solver's prelude is unsatisfiable: the definition's SMT text, a user prelude, or
    /// k-rust's SMT translation of them.
    SolverPreludeInconsistent,
    /// The solver rejected the prelude's text: the definition's SMT text, a user prelude, or
    /// k-rust's SMT translation of them.
    SolverPreludeMalformed,
    /// The solver could not decide the prelude.
    SolverPreludeUnknown,
    /// The solver did not start for this definition: its SMT declarations, k-rust's translation
    /// of them, or the host.
    SolverInit,
    /// The client's observer or witness filter panicked: its state cannot be rebuilt, so no case
    /// can run after it.
    ClientPanic,
    /// The campaign's backends did not rebuild (after a crash, or for a second run).
    RebuildFailed,
    /// The client's witness filter broke its contract ([`crate::filter`]): it refused with a
    /// cause that is no cause token, or judged two equal witness cases differently.
    ClientDefect,
}

/// What crashed: a panic, an error k-rust or the engine answered that a correct build never
/// answers for its input (a request it built that its own schema refuses, a result it cannot
/// encode or decode), or a leaf whose halt's structured cause no correct k-rust gives
/// (FZ-CRASH-CAUSE).
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum CrashKind {
    /// A panic.
    Panic,
    /// An error without a typed kind that is not a stop or a refused state.
    InternalError,
    /// A leaf halted on a cause that is a defect of k-rust, or of a hook declaration k-rust should
    /// have refused (`crate::exec::InternalHalt`): a builtin hook applied at a signature it does
    /// not take, a builtin result symbol the definition lacks, a solver failure of k-rust's own
    /// making, a macro or alias at run time, or a failed simplification without its cause. The
    /// backend did not panic, so nothing is rebuilt.
    InternalHalt,
}

/// Where a crash happened: a definition's run (with its judgement), or the engine around it.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum CrashSide {
    /// The baseline's (the only definition's, outside a differential campaign) run.
    Baseline,
    /// A differential campaign's mutant's run.
    Mutant,
    /// The engine around the runs: assembly, the target's judgement of a whole case, the
    /// incidental findings, or a fresh confirmation's build.
    Engine,
}

/// The stage of a crash.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum CrashStage {
    /// `Backend::execute`.
    Execute,
    /// The judgement of the run's leaves (clean leaves, natural ends, leaf patterns, data ends).
    Judge,
    /// The engine around the runs ([`CrashSide::Engine`]).
    Engine,
}

/// What a crash signature's site is.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum SiteKind {
    /// The panic's location, normalized to start at its crate's directory.
    Location,
    /// The message's class: its first line before its first `:`, with quoted spans and digits
    /// masked (an internal error, or a panic without a usable location).
    Message,
    /// An internal halt's structured cause: its kind and the hook or symbol it names, never an
    /// input value (`builtin:wrong-arity:INT.add`, `smt:missing-model`).
    Cause,
}

/// The identity of a crash: crashes with equal signatures are counted as one finding.
#[derive(Clone, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct CrashSignature {
    /// A panic, an internal error or an internal halt.
    pub kind: CrashKind,
    /// Which run, or the engine.
    pub side: CrashSide,
    /// Which stage.
    pub stage: CrashStage,
    /// What [`Self::site`] is.
    pub site_kind: SiteKind,
    /// The normalized location, the message's class, or the internal halt's cause.
    pub site: String,
}

/// When a crash happened.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum CrashPhase {
    /// A case.
    Case,
    /// A candidate's confirmation on a fresh backend.
    Confirmation,
    /// The screening of a shrink candidate.
    Shrink,
    /// The run of every path that judged a witness case's comparability outside its case.
    Comparability,
    /// The screening of a repair candidate of a hit the client's witness filter refused.
    Repair,
}

/// Whether a crash repeats on every run of its input. It is never known to: after a panic or an
/// error the run's counts of solver `unknown`s, stack stops and allowance refusals are lost, so
/// whether one of them led to it is unknown.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum CrashDeterminism {
    /// Outside the determinism contract: the clock stopped the run (the safety limit, a
    /// cancellation), or the confirmation did not repeat the crash.
    Outside,
    /// Unknown: a solver timeout or a stack stop may have decided it.
    Unknown,
}

/// A hole and its value in a crash finding.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct CrashHole {
    /// The hole's name.
    pub name: String,
    /// Its value.
    pub value: Value,
}

/// The first case of one crash signature ([`CrashFindings`]).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct CrashFinding {
    /// What crashed, where.
    pub signature: CrashSignature,
    /// When it first crashed.
    pub phase: CrashPhase,
    /// The panic's or the error's message, at most 1 KiB.
    pub message: String,
    /// The number of the case it first crashed in (for a crash in a confirmation, a shrink
    /// candidate or a comparability run, the case whose candidate or witness that was).
    pub case: u64,
    /// The hole values it first crashed on (for a shrink candidate, the candidate's), in
    /// declaration order.
    pub holes: Vec<CrashHole>,
    /// The values the crash shrank to under the same signature, when shrinking moved them.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub shrunk_holes: Option<Vec<CrashHole>>,
    /// How many cases crashed with this signature (shrink candidates and confirmations not
    /// counted).
    pub count: u64,
    /// Whether a re-run on a fresh backend crashed with the same signature (for a crash of the
    /// comparability run, a re-run of that judgement on fresh cases); absent when no re-run was
    /// made: the clock stopped the run, so the crash says nothing about the input, or the
    /// fresh backend did not build, or the caller cancelled.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reproduced: Option<bool>,
    /// Whether the shrunk values' re-run on a fresh backend crashed with the same signature;
    /// absent without shrunk values.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub shrunk_reproduced: Option<bool>,
    /// Whether the crash repeats on every run of its input ([`CrashDeterminism`]).
    pub determinism: CrashDeterminism,
    /// The clock stopped the run: the per-case safety limit or a cancellation.
    pub clock: bool,
    /// The build that crashed has debug assertions, whose panics a release build does not
    /// raise (the build identity names the sources, not the profile).
    pub debug_assertions: bool,
    /// The `krun` command line equivalent to the crashed run, when the crash is in `execute`
    /// and one is: expected to reproduce it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub krun_command: Option<String>,
    /// The instantiated program text, when the case assembled one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub program: Option<String>,
    /// The instantiated configuration-variable bindings, when the case assembled them.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub config_vars: BTreeMap<String, String>,
}

/// The first case of each crash signature of a campaign (FZ-CRASH, D30, D32): a panic or an
/// internal error of k-rust or of the engine during a case, or a leaf of a run whose halt's
/// structured cause is a defect of k-rust or of a hook declaration (an internal halt,
/// FZ-CRASH-CAUSE). The case keeps its class (`unsupported`, or `baseline-incomplete` when a
/// differential baseline crashed) with the reason `panic`, `internal-error` or `internal-halt`;
/// the campaign goes on. A crash is a defect of k-rust or of
/// the engine: the definition may have triggered it, but k-rust should have rejected or reported
/// it. Crashes are incidental: no target looks for one, and keeping one moves no case, class or
/// budget. Environment refusals (a stack segment the host refused to map, a request deeper than
/// the backend's stack) are no crash.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct CrashFindings(pub Vec<CrashFinding>);

impl CrashFindings {
    /// Whether no case crashed.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// One line per finding, worded for a reader (the summary of `krust fuzz` prints them).
    #[must_use]
    pub fn lines(&self) -> Vec<String> {
        self.0
            .iter()
            .enumerate()
            .map(|(index, crash)| {
                let holes = if crash.holes.is_empty() {
                    String::new()
                } else {
                    let values = crash
                        .holes
                        .iter()
                        .map(|hole| {
                            format!(
                                "{} = {}",
                                hole.name,
                                serde_json::to_string(&hole.value).unwrap_or_default()
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!(" ({values})")
                };
                let what = match crash.signature.kind {
                    CrashKind::Panic => "panicked",
                    CrashKind::InternalError => "answered an internal error",
                    CrashKind::InternalHalt => "halted on an internal cause",
                };
                let count = if crash.count > 1 {
                    format!(", {} cases in all", crash.count)
                } else {
                    String::new()
                };
                let defect = if crash.signature.kind == CrashKind::InternalHalt
                    && crate::crash::blames_a_hook_declaration(&crash.signature.site)
                {
                    "a defect of the definition's hook declaration or of k-rust (terms are \
                     sort-checked, so a builtin hook applied where it does not apply means a hook \
                     declared at a signature or in a definition its builtin does not fit, which \
                     k-rust should have refused, or a k-rust defect)"
                } else {
                    "a k-rust defect (the definition may have triggered it, but k-rust should \
                     have rejected or reported it)"
                };
                format!(
                    "crash: case {}{holes} {what} at {} ({}{count}): k-rust crashed on this \
                     input: {defect}; please report it with the report's `crashes[{index}]`",
                    crash.case,
                    crash.signature.site,
                    serde_json::to_value(crash.signature.side)
                        .ok()
                        .and_then(|side| side.as_str().map(str::to_owned))
                        .unwrap_or_default(),
                )
            })
            .collect()
    }
}

/// Serialize a `u64` as a decimal string, which JavaScript reads exactly at any size.
pub(crate) mod decimal_u64 {
    use serde::{Deserialize, Deserializer, Serializer, de::Error};

    #[expect(
        clippy::trivially_copy_pass_by_ref,
        reason = "serde's `with` passes a reference to the field"
    )]
    pub(crate) fn serialize<S: Serializer>(value: &u64, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_str(value)
    }

    /// Only the canonical form is read (no sign, no leading zero), so that reading and
    /// re-writing a report gives the same bytes.
    pub(crate) fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<u64, D::Error> {
        parse(&String::deserialize(deserializer)?).map_err(D::Error::custom)
    }

    pub(crate) fn parse(text: &str) -> Result<u64, String> {
        let value: u64 = text
            .parse()
            .map_err(|error| format!("not a decimal u64 `{text}`: {error}"))?;
        if value.to_string() == text {
            Ok(value)
        } else {
            Err(format!(
                "`{text}` is not the canonical decimal form of {value}"
            ))
        }
    }
}

/// Serialize an optional `u64` as an optional canonical decimal string.
pub(crate) mod decimal_u64_option {
    use serde::{Deserialize, Deserializer, Serializer, de::Error};

    #[expect(
        clippy::ref_option,
        reason = "serde's `with` passes a reference to the field"
    )]
    pub(crate) fn serialize<S: Serializer>(
        value: &Option<u64>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        match value {
            Some(value) => serializer.collect_str(value),
            None => serializer.serialize_none(),
        }
    }

    pub(crate) fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Option<u64>, D::Error> {
        Option::<String>::deserialize(deserializer)?
            .map(|text| super::decimal_u64::parse(&text).map_err(D::Error::custom))
            .transpose()
    }
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
        spec::{CaseOptions, ProposerConfig, ProposerKind},
    };

    /// A report with every optional part present and every collection non-empty, so that a
    /// change to any field's serialization changes the bytes below.
    #[expect(clippy::too_many_lines, reason = "one report literal with every field")]
    fn fixed_report() -> FuzzReport {
        let hole = HoleValue {
            name: "AMOUNT".into(),
            location: HoleLocation::Span(SpanAddress {
                program: "transfer.imp".into(),
                line: Some(4),
                column: Some(10),
                find: "amount = 250;".into(),
                literal: "250".into(),
            }),
            k_text: Some("-7".into()),
            kore: r#"\dv{SortInt{}}("-7")"#.into(),
            value: Value::Int(BigInt::from(-7)),
        };
        let case = WitnessCase {
            holes: vec![hole],
            program: Some("amount = -7;".into()),
            config_vars: BTreeMap::new(),
            class: OutcomeClass::Hit,
            sides: vec![WitnessSide {
                role: DefinitionRole::Baseline,
                initial_configuration: "Lbl'-LT-'generatedTop'-GT-'{}()".into(),
                final_configurations: vec!["Lbl'-LT-'generatedTop'-GT-'{}()".into()],
                halts: vec![HaltReasonOutput::Stuck],
                undefined_rules: Vec::new(),
                work: Some(12),
            }],
            reaching: Reaching {
                role: DefinitionRole::Baseline,
                leaf: Some(0),
                step: Some(4),
                configuration: None,
            },
            kill: None,
            steps: Some(12),
            comparable: None,
        };
        FuzzReport {
            schema: REPORT_SCHEMA.into(),
            version: REPORT_VERSION,
            identity: ReportIdentity {
                engine_version: crate::ENGINE_VERSION,
                k_rust_revision: "b322de1ab".into(),
                fuzz_revision: "0.8.0+src.0".into(),
                definitions: vec![DefinitionIdentity {
                    role: DefinitionRole::Baseline,
                    main_module: "IMP".into(),
                    syntax_module: "IMP-SYNTAX".into(),
                    frontend_digest: digest_hex(b"frontend"),
                    execution_definition_digest: digest_hex(b"execution"),
                    syntax_definition_digest: digest_hex(b"syntax"),
                    initial_configuration_digest: Some(digest_hex(b"initial")),
                    execution_digest: "0123".into(),
                    route: "source-execution".into(),
                    execution_rewrite_order_digest: Some(digest_hex(b"rule-1\nrule-2")),
                }],
                program_digest: digest_hex(b"program"),
                overlay_digest: digest_hex(b"overlay"),
                target_digest: digest_hex(b"target"),
                target_rule: Some(TargetRule {
                    id: "a".into(),
                    name: RuleName {
                        kind: k_rust::backend::CompiledRuleKind::Rewrite,
                        label: None,
                        locations: Vec::new(),
                    },
                }),
                options: CaseOptions {
                    max_work: Some(100_000),
                    ..CaseOptions::default()
                },
                execution_modality: Some(ExecutionModality {
                    cases: ResultModality::PathSet,
                    every_path: Some(ResultModality::StateSet),
                    any_state: None,
                }),
                proposers: ProposerConfig {
                    explicit: vec![BTreeMap::from([(
                        "AMOUNT".to_owned(),
                        Value::Bytes(vec![0, 0xab]),
                    )])],
                    ..ProposerConfig::default()
                },
                bounds: GenerationBounds::default(),
                caps: GenerationCaps {
                    int_bits: 4096,
                    length: 65536,
                    depth: 16,
                    enumeration: 65536,
                    value_size: 131_072,
                },
                rejection_cap: 10,
                seed: u64::MAX,
                budget: Budget::Cases(5000),
                thread_stack_size: Some(64 << 20),
                solver: "none".into(),
                debug_assertions: false,
                parse_diagnostic_work: "1048576".into(),
                dictionary: None,
                climb: None,
                corpus: None,
                solve: None,
                effective_constraints: Vec::new(),
                filter: None,
            },
            outcome: CampaignOutcome::WitnessFound {
                witness: Witness {
                    label: HitLabel::PropertyFailure,
                    first: case.clone(),
                    shrunk: Some(case),
                    clean_leaf_facts: vec!["ceil-free".into()],
                    krun_command: Some("krust krun transfer.imp".into()),
                    mutant_krun_command: Some("krust krun --definition <mutant-dir>".into()),
                    repaired_from: None,
                },
            },
            totals: Totals {
                cases: 40,
                work: 1234,
                classes: BTreeMap::from([
                    (OutcomeClass::Miss, 37),
                    (OutcomeClass::Rejected, 2),
                    (OutcomeClass::Hit, 1),
                ]),
                rejection_rate_permille: 50,
                rejections: BTreeMap::from([
                    (RejectionReason::RoundTrip, 1),
                    (RejectionReason::BackendRefused, 1),
                ]),
                unsupported_reasons: BTreeMap::from([(UnjudgedReason::NaturalEndUndecided, 2)]),
                baseline_incomplete_reasons: BTreeMap::new(),
                unsupported_hooks: BTreeMap::new(),
                baseline_incomplete_hooks: BTreeMap::new(),
                coverage: CoverageTotals {
                    applied: BTreeSet::from(["b".to_owned(), "a".to_owned()]),
                    matched: BTreeSet::from(["c".to_owned()]),
                    names: BTreeMap::from([(
                        "a".to_owned(),
                        RuleName {
                            kind: k_rust::backend::CompiledRuleKind::Rewrite,
                            label: Some("IMP.a".into()),
                            locations: vec![crate::target::RuleLocation {
                                source: "imp.k".into(),
                                reference: "imp.k".into(),
                                line: 3,
                                end_line: 4,
                            }],
                        },
                    )]),
                },
                target_blocked: 3,
                pattern_body_matches: Some(4),
                pattern_body_judged: Some(3),
                best_score: Some(BestScore {
                    scored_cases: 3,
                    best: Some(ScoreValue {
                        case: 1,
                        level: Some(0),
                        guard_distance: Some("2/3".into()),
                    }),
                }),
                outside_determinism: 0,
                first_outside_determinism: None,
                unconfirmed: 1,
                case_sequence_digest: digest_hex(b"cases"),
                solve: None,
                crash_work: 0,
                filter: FilterTotals::default(),
                domain: Some(DomainTotals {
                    assignments: 64,
                    tried: 40,
                    exhausted: false,
                }),
                diverging: Some(DivergingTotals {
                    cases: 2,
                    baseline_work: 161,
                }),
                coverage_last_grew: Some(7),
            },
            normal_end: Some(NormalEnds {
                baseline: NormalEndKind::EveryK,
                mutant: None,
            }),
            incidental: Incidentals::default(),
            crashes: CrashFindings::default(),
            crashes_omitted: 0,
            client_refusals: Vec::new(),
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
            definition_findings: Vec::new(),
            engine_defects: vec![EngineDefect {
                case: Some(7),
                description: "confirmation disagreed".into(),
            }],
        }
    }

    /// Both bindings declare what version 10 adds (FZ-REPLAY-WHOLE): the identity's k-rust-fuzz
    /// build and parse diagnostic limit, and the first case a re-run may differ at.
    #[test]
    fn typescript_declarations_name_the_version_10_fields() {
        for path in ["k-rust-napi", "k-rust-wasm"] {
            let declarations = std::fs::read_to_string(format!(
                "{}/../{path}/typescript/index.ts",
                env!("CARGO_MANIFEST_DIR")
            ))
            .expect("the declarations read");
            for key in [
                "'fuzz-revision': string",
                "'parse-diagnostic-work': string",
                "'first-outside-determinism'?: number",
                "'debug-assertions': boolean",
                "domain?: { assignments: number; tried: number; exhausted: boolean }",
                "diverging?: { cases: number; 'baseline-work': number }",
                "'coverage-last-grew'?: number",
            ] {
                assert!(declarations.contains(key), "{path}: {key} is not declared");
            }
        }
    }

    /// Both bindings declare what a version-8 report holds (FZ-CRASH): every unjudged reason and
    /// comparable condition by its serde name, every abort kind, and every key of a crash
    /// finding; and no longer `backend-error`.
    #[test]
    fn typescript_declarations_name_the_crash_keys_and_reasons() {
        let finding = CrashFinding {
            signature: CrashSignature {
                kind: CrashKind::Panic,
                side: CrashSide::Engine,
                stage: CrashStage::Engine,
                site_kind: SiteKind::Message,
                site: "s".into(),
            },
            phase: CrashPhase::Case,
            message: "m".into(),
            case: 0,
            holes: Vec::new(),
            shrunk_holes: Some(Vec::new()),
            count: 1,
            reproduced: Some(true),
            shrunk_reproduced: Some(true),
            determinism: CrashDeterminism::Unknown,
            clock: false,
            debug_assertions: false,
            krun_command: Some("k".into()),
            program: Some("p".into()),
            config_vars: BTreeMap::from([("A".into(), "1".into())]),
        };
        let json = serde_json::to_value(&finding).expect("a finding is JSON");
        let keys: Vec<String> = json
            .as_object()
            .expect("an object")
            .keys()
            .chain(json["signature"].as_object().expect("an object").keys())
            .cloned()
            .collect();
        for declarations in [
            include_str!("../../k-rust-napi/typescript/index.ts"),
            include_str!("../../k-rust-wasm/typescript/index.ts"),
        ] {
            for key in &keys {
                let quoted = format!("'{key}'");
                let bare = format!("  {key}");
                assert!(
                    declarations.contains(&quoted) || declarations.contains(&bare),
                    "the crash finding key `{key}` is not declared"
                );
            }
            let names = UnjudgedReason::ALL
                .iter()
                .map(|reason| reason.name())
                .chain(
                    ComparableCondition::ALL
                        .iter()
                        .map(|condition| condition.name()),
                )
                .chain(
                    [
                        AbortKind::SolverPreludeInconsistent,
                        AbortKind::SolverPreludeMalformed,
                        AbortKind::SolverPreludeUnknown,
                        AbortKind::SolverInit,
                        AbortKind::ClientPanic,
                        AbortKind::RebuildFailed,
                        AbortKind::ClientDefect,
                    ]
                    .iter()
                    .map(|kind| {
                        serde_json::to_value(kind)
                            .ok()
                            .and_then(|kind| kind.as_str().map(str::to_owned))
                            .unwrap_or_default()
                    }),
                );
            for name in names {
                assert!(
                    declarations.contains(&format!("| '{name}'")),
                    "`{name}` is not declared"
                );
            }
            for key in [
                "'crash-work'",
                "'crashes-omitted'",
                "crashes?:",
                "panicked?:",
            ] {
                assert!(declarations.contains(key), "{key} is not declared");
            }
            assert!(!declarations.contains("'backend-error'"));
            assert!(declarations.contains("version 10 (docs/compatibility.md)"));
            for key in [
                "'execution-modality'",
                "'every-path'?:",
                "'any-state'?:",
                "'state-set'",
                "'path-set'",
                // FZ-STATESET-MATCH: an any-state witness's reaching configuration.
                "step?: number; configuration?: string }",
            ] {
                assert!(declarations.contains(key), "{key} is not declared");
            }
        }
    }

    /// (FZ-COMPARABLE-B) Both bindings declare the witness filter's keys, its reason, abort kind
    /// and crash phase.
    #[test]
    fn typescript_declarations_name_the_witness_filters_keys() {
        for declarations in [
            include_str!("../../k-rust-napi/typescript/index.ts"),
            include_str!("../../k-rust-wasm/typescript/index.ts"),
        ] {
            for key in [
                "filter?: string",
                "'undefined-rules'?:",
                "work?: number",
                "'repaired-from'?:",
                "'client-refusals'?:",
                "'refused-shrink-candidates'?:",
                "'repairs-skipped'?:",
                "'repair-candidates'?:",
                "'repair-work'?:",
                "| 'repair'",
                "| 'client-refused'",
                "| 'client-defect'",
            ] {
                assert!(declarations.contains(key), "{key} is not declared");
            }
        }
    }

    /// (UNNAMED-HOOK) Both bindings declare the keys that name the hooks behind a reason or a
    /// comparable condition, with the shape `ReasonHooks` serializes to.
    #[test]
    fn typescript_declarations_name_the_reason_hooks() {
        let hooks = ReasonHooks::of(&BTreeSet::from([
            ReasonHook::chosen("MAP.keys_list", "order"),
            ReasonHook::unsupported("INT.shl"),
        ]))
        .expect("hooks");
        assert_eq!(
            serde_json::to_value(&hooks).expect("serializes"),
            serde_json::json!({"hooks": [{"hook": "INT.shl"}, {"hook": "MAP.keys_list", "class": "order"}]})
        );
        let totals = Totals {
            unsupported_hooks: BTreeMap::from([(
                UnjudgedReason::EndNotComparable(crate::exec::reasons::EndNotComparable(
                    ComparableCondition::UnsupportedHook,
                )),
                hooks.clone(),
            )]),
            ..Totals::default()
        };
        let text = serde_json::to_string(&totals).expect("serializes");
        assert!(text.contains(r#""unsupported-hooks":{"end-not-comparable:unsupported-hook":"#));
        assert_eq!(
            serde_json::from_str::<Totals>(&text).expect("reads back"),
            totals
        );
        for declarations in [
            include_str!("../../k-rust-napi/typescript/index.ts"),
            include_str!("../../k-rust-wasm/typescript/index.ts"),
        ] {
            for key in [
                "'unsupported-hooks'?: Partial<Record<FuzzUnjudgedReason, FuzzReasonHooks>>",
                "'baseline-incomplete-hooks'?: Partial<Record<FuzzUnjudgedReason, FuzzReasonHooks>>",
                "hooks?: Partial<Record<FuzzComparableCondition, FuzzReasonHooks>>",
                "hooks: { hook: string; class?: string }[]",
                "omitted?: number",
                "cases?: number",
                "'pattern-body-judged'?: number",
            ] {
                assert!(declarations.contains(key), "{key} is not declared");
            }
        }
    }

    /// (FZ-CRASH-CAUSE) Both bindings declare every crash kind and site kind, and no longer the
    /// reason `halt-simplification-error`, which the leaf's cause splits.
    #[test]
    fn typescript_declarations_name_the_crash_kinds_and_site_kinds() {
        let name_of = |value: serde_json::Value| value.as_str().unwrap_or_default().to_owned();
        let crash_kinds = [
            CrashKind::Panic,
            CrashKind::InternalError,
            CrashKind::InternalHalt,
        ]
        .map(|kind| name_of(serde_json::to_value(kind).unwrap_or_default()));
        let site_kinds = [SiteKind::Location, SiteKind::Message, SiteKind::Cause]
            .map(|kind| name_of(serde_json::to_value(kind).unwrap_or_default()));
        for declarations in [
            include_str!("../../k-rust-napi/typescript/index.ts"),
            include_str!("../../k-rust-wasm/typescript/index.ts"),
        ] {
            for name in crash_kinds.iter().chain(&site_kinds) {
                assert!(
                    declarations.contains(&format!("'{name}'")),
                    "`{name}` is not declared"
                );
            }
            assert!(!declarations.contains("'halt-simplification-error'"));
        }
    }

    #[test]
    fn report_round_trips_through_canonical_json() {
        let report = fixed_report();
        let text = report.to_canonical_json();
        let read = FuzzReport::from_json(&text).expect("the report reads back");
        assert_eq!(read, report);
        assert_eq!(read.to_canonical_json(), text);

        let mut cancelled = report;
        cancelled.outcome = CampaignOutcome::Aborted {
            kind: AbortKind::SolverPreludeInconsistent,
            reason: "prelude".into(),
            case: None,
            holes: Vec::new(),
            panic: None,
            no_witness: NoWitness {
                statement: "No witness.".into(),
                path_mode: PathMode::AllPaths,
            },
        };
        let text = cancelled.to_canonical_json();
        assert!(
            text.contains(concat!(
                r#""outcome":{"status":"aborted","kind":"solver-prelude-inconsistent","#,
                r#""reason":"prelude","no-witness":"#,
                r#"{"statement":"No witness.","path-mode":"all-paths"}}"#
            )),
            "{text}"
        );
        assert_eq!(FuzzReport::from_json(&text).expect("reads back"), cancelled);
        assert_eq!(cancelled.witness(), None);
        assert!(cancelled.no_witness().is_some());
    }

    #[test]
    fn an_incidental_finding_serializes_after_the_normal_end_and_reads_back() {
        let mut report = fixed_report();
        report.incidental.undefined = Some(IncidentalCase {
            case: 3,
            holes: Vec::new(),
            leaves: 1,
            leaf: 0,
            steps: 9,
            k_heads: vec!["100 / 0".into()],
            configuration: "Lbl'-LT-'generatedTop'-GT-'{}()".into(),
            krun_command: None,
            baseline_run: false,
        });
        let text = report.to_canonical_json();
        assert!(
            text.contains(concat!(
                r#""normal-end":{"baseline":"every-k"},"incidental":{"undefined":{"case":3,"#,
                r#""holes":[],"leaves":1,"leaf":0,"steps":9,"k-heads":["100 / 0"],"#,
                r#""configuration":"Lbl'-LT-'generatedTop'-GT-'{}()","krun-command":null}},"#,
                r#""load-records":"#
            )),
            "{text}"
        );
        assert_eq!(FuzzReport::from_json(&text).expect("reads back"), report);
        assert_eq!(
            report.incidental.lines(),
            vec![
                "incidental (information, not a failure): case 3 took an undefined step at step \
                 10 on `100 / 0`; a rule applied whose result is undefined there: a partiality \
                 the semantics may or may not intend. The report's `incidental.undefined` holds \
                 its configuration and krun line."
                    .to_owned()
            ]
        );
    }

    #[test]
    fn report_bytes_are_stable_for_a_fixed_value() {
        let text = fixed_report().to_canonical_json();
        let expected = concat!(
            r#"{"schema":"krust-fuzz-report","version":10,"identity":{"engine-version":8,"#,
            r#""k-rust-revision":"b322de1ab","fuzz-revision":"0.8.0+src.0","#,
            r#""definitions":[{"role":"baseline","#,
            r#""main-module":"IMP","syntax-module":"IMP-SYNTAX","#,
            r#""execution-digest":"0123","route":"source-execution","#,
            r#""frontend-digest":"FRONTEND","execution-definition-digest":"EXECUTION","#,
            r#""syntax-definition-digest":"SYNDEF","#,
            r#""initial-configuration-digest":"INITIAL","#,
            r#""execution-rewrite-order-digest":"#,
            r#""ORDER"}],"#,
            r#""program-digest":"PROGRAM","overlay-digest":"OVERLAY","target-digest":"TARGET","#,
            r#""target-rule":{"id":"a","name":{"kind":"rewrite","label":null,"locations":[]}},"#,
            r#""options":{"paths":"one-path","max-depth":null,"max-work":100000,"#,
            r#""max-simplification-iterations":ITER,"normal-end-pattern":null,"#,
            r#""safety-limit-ms":null,"backend":{"smt-timeout-ms":125,"smt-retry-limit":3},"#,
            r#""shrink":true},"#,
            r#""execution-modality":{"cases":"path-set","every-path":"state-set"},"#,
            r#""proposers":{"anchors-first":true,"explicit":"#,
            r#"[{"AMOUNT":{"bytes":"00ab"}}],"weights":{"blind":1}},"#,
            r#""bounds":{"int-bits":64,"length":16,"depth":4},"#,
            r#""caps":{"int-bits":4096,"length":65536,"depth":16,"enumeration":65536,"#,
            r#""value-size":131072},"#,
            r#""rejection-cap":"10","#,
            r#""seed":"18446744073709551615","budget":{"cases":"5000"},"#,
            r#""thread-stack-size":"67108864","solver":"none","debug-assertions":false,"#,
            r#""parse-diagnostic-work":"1048576"},"#,
            r#""outcome":{"status":"witness-found","witness":{"label":"property-failure","#,
            r#""first":CASE,"shrunk":CASE,"clean-leaf-facts":["ceil-free"],"#,
            r#""krun-command":"krust krun transfer.imp","#,
            r#""mutant-krun-command":"krust krun --definition <mutant-dir>"}},"#,
            r#""totals":{"cases":40,"work":1234,"#,
            r#""classes":{"hit":1,"miss":37,"rejected":2},"rejection-rate-permille":50,"#,
            r#""rejections":{"round-trip":1,"backend-refused":1},"#,
            r#""unsupported-reasons":{"natural-end-undecided":2},"#,
            r#""baseline-incomplete-reasons":{},"#,
            r#""coverage":{"applied":["a","b"],"matched":["c"],"names":{"a":{"kind":"rewrite","#,
            r#""label":"IMP.a","locations":[{"source":"imp.k","reference":"imp.k","line":3,"#,
            r#""end-line":4}]}}},"#,
            r#""target-blocked":3,"pattern-body-matches":4,"pattern-body-judged":3,"#,
            r#""best-score":{"scored-cases":3,"best":{"case":1,"level":0,"#,
            r#""guard-distance":"2/3"}},"outside-determinism":0,"unconfirmed":1,"#,
            r#""case-sequence-digest":"CASES","#,
            r#""domain":{"assignments":64,"tried":40,"exhausted":false},"#,
            r#""diverging":{"cases":2,"baseline-work":161},"coverage-last-grew":7},"#,
            r#""normal-end":{"baseline":"every-k"},"#,
            r#""load-records":[{"kind":"contradicted-claim","#,
            r#""detail":"total"}],"sort-overrides":[{"hole":"X","sort":"Id","#,
            r#""refusal":"Token"}],"warnings":["statically-unreachable"],"#,
            r#""engine-defects":[{"case":7,"description":"confirmation disagreed"}]}"#,
        );
        let case = concat!(
            r#"{"holes":[{"name":"AMOUNT","location":{"kind":"span","#,
            r#""program":"transfer.imp","line":4,"column":10,"find":"amount = 250;","#,
            r#""literal":"250"},"#,
            r#""k-text":"-7","kore":"\\dv{SortInt{}}(\"-7\")","#,
            r#""value":{"int":"-7"}}],"program":"amount = -7;","class":"hit","#,
            r#""sides":[{"role":"baseline","#,
            r#""initial-configuration":"Lbl'-LT-'generatedTop'-GT-'{}()","#,
            r#""final-configurations":["Lbl'-LT-'generatedTop'-GT-'{}()"],"#,
            r#""halts":["stuck"],"work":12}],"#,
            r#""reaching":{"role":"baseline","leaf":0,"step":4},"steps":12}"#,
        );
        let expected = expected
            .replace("ORDER", &digest_hex(b"rule-1\nrule-2"))
            .replace("PROGRAM", &digest_hex(b"program"))
            .replace("OVERLAY", &digest_hex(b"overlay"))
            .replace("TARGET", &digest_hex(b"target"))
            .replace("INITIAL", &digest_hex(b"initial"))
            .replace("FRONTEND", &digest_hex(b"frontend"))
            .replace("SYNDEF", &digest_hex(b"syntax"))
            .replace("EXECUTION", &digest_hex(b"execution"))
            .replace("CASES", &digest_hex(b"cases"))
            .replace(
                "ITER",
                &CaseOptions::default()
                    .max_simplification_iterations
                    .to_string(),
            )
            .replace("CASE", case);
        assert_eq!(text, expected);
    }

    /// Map keys serialize in the derived `Ord`, which is declaration order: reordering either
    /// enum would change report bytes without a `REPORT_VERSION` bump. This test freezes both
    /// orders; a precedence order belongs in a separate function.
    #[test]
    fn class_and_proposer_keys_serialize_in_a_frozen_order() {
        let classes: BTreeMap<OutcomeClass, u64> =
            OutcomeClass::ALL.iter().map(|class| (*class, 0)).collect();
        assert_eq!(
            serde_json::to_string(&classes).expect("serializes"),
            concat!(
                r#"{"hit":0,"miss":0,"stuck":0,"reached-unfinished":0,"depth-bound":0,"#,
                r#""work-bound":0,"timeout":0,"undefined":0,"unsupported":0,"rejected":0,"#,
                r#""baseline-incomplete":0}"#
            )
        );
        let weights = BTreeMap::from([
            (ProposerKind::Solve, 5),
            (ProposerKind::Corpus, 4),
            (ProposerKind::Climb, 3),
            (ProposerKind::Dictionary, 2),
            (ProposerKind::Blind, 1),
        ]);
        assert_eq!(
            serde_json::to_string(&weights).expect("serializes"),
            r#"{"blind":1,"dictionary":2,"climb":3,"corpus":4,"solve":5}"#
        );
        let reasons = BTreeMap::from([
            (RejectionReason::BackendRefused, 5),
            (RejectionReason::RoundTrip, 4),
            (RejectionReason::Assembly, 3),
            (RejectionReason::Print, 2),
            (RejectionReason::Constraint, 1),
            (RejectionReason::Generation, 6),
        ]);
        assert_eq!(
            serde_json::to_string(&reasons).expect("serializes"),
            concat!(
                r#"{"generation":6,"constraint":1,"print":2,"assembly":3,"round-trip":4,"#,
                r#""backend-refused":5}"#
            )
        );
    }

    #[test]
    fn decimal_strings_are_read_only_in_canonical_form() {
        assert_eq!(decimal_u64::parse("5"), Ok(5));
        assert_eq!(decimal_u64::parse("0"), Ok(0));
        assert_eq!(decimal_u64::parse("18446744073709551615"), Ok(u64::MAX));
        for text in ["+5", "05", "", "-1", " 5", "0x5", "18446744073709551616"] {
            assert!(decimal_u64::parse(text).is_err(), "{text:?}");
        }
        let text = fixed_report()
            .to_canonical_json()
            .replace(r#""seed":"18446744073709551615""#, r#""seed":"+5""#);
        assert!(FuzzReport::from_json(&text).is_err());
    }

    #[test]
    fn digest_is_lowercase_hex_sha256() {
        assert_eq!(
            digest_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    /// HARD-B review S3: every value a campaign admits reads back from its report. A value
    /// nested [`crate::values::MAX_VALUE_DEPTH`] levels deep, in the JSON shapes that nest most
    /// per level (an application's or a map entry's three arrays and objects), as a witness
    /// hole's value and as an explicit assignment, is written and read back on a thread of a
    /// 2 MiB stack, the size of a test thread: both directions grow the stack on the heap, and
    /// reading lifts `serde_json`'s recursion limit of 128 nested arrays and objects.
    #[cfg(not(target_family = "wasm"))]
    #[test]
    fn the_deepest_admitted_value_reads_back_from_a_report() {
        let chain = |levels: usize, map: bool| {
            let mut value = Value::MInt {
                width: 8,
                value: 1u32.into(),
            };
            for _ in 1..levels {
                value = if map {
                    Value::Map(vec![(Value::Int(BigInt::from(0)), value)])
                } else {
                    Value::Apply {
                        symbol: "s".into(),
                        arguments: vec![value],
                    }
                };
            }
            value
        };
        let with = |value: Value| {
            let mut report = fixed_report();
            if let CampaignOutcome::WitnessFound { witness } = &mut report.outcome {
                witness.first.holes[0].value = value.clone();
                if let Some(shrunk) = &mut witness.shrunk {
                    shrunk.holes[0].value = value.clone();
                }
            }
            report.identity.proposers.explicit[0].insert("AMOUNT".into(), value);
            report
        };
        let most = crate::values::MAX_VALUE_DEPTH;
        for map in [false, true] {
            let report = with(chain(most, map));
            let (read, report) = std::thread::Builder::new()
                .stack_size(2 << 20)
                .spawn(move || {
                    let text = report.to_canonical_json();
                    (FuzzReport::from_json(&text).ok(), report)
                })
                .expect("a thread")
                .join()
                .expect("no overflow");
            assert_eq!(read.as_ref(), Some(&report), "{most} levels, map {map}");
        }
    }
}
