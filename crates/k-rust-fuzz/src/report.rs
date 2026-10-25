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
pub const REPORT_VERSION: u32 = 7;

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
    /// A failure every case would repeat ended the campaign (a failed solver prelude).
    Aborted {
        /// Why.
        reason: String,
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
    /// key, a cell no end holds), so a negated property held vacuously, and a warning says so. Information, not a class: each leaf is matched on its own. Absent for
    /// every other target, and when no case inside the determinism contract was executed.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub pattern_body_matches: Option<u64>,
    /// The best score the scored cases reached (ARCHITECTURE 6.4): present exactly when a
    /// proposer scores the campaign's cases (the climb or the solve proposer), so that a reader
    /// sees whether the guided search came near the target; `None` when no proposer scores.
    pub best_score: Option<BestScore>,
    /// Cases outside the determinism contract (ARCHITECTURE 5.4).
    pub outside_determinism: u64,
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
    /// a campaign bounded by `max-work` says so in a trailing comment. `None` when no `krun` run
    /// is equivalent: a KORE-template program, a program without `$PGM`, or a backend on the
    /// `from-definition` route (krun orders rules by the compiler's rewrite order).
    pub krun_command: Option<String>,
    /// For a differential witness, the same command line on the mutant, whose compiled
    /// directory is left as `<mutant-dir>`: strategy `all` for a removed end (judged against
    /// the mutant's every path) or the all-paths mode, `any` for an added end in the one-path
    /// mode. Absent for every other target, and when no `krun` run is equivalent.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mutant_krun_command: Option<String>,
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
            condition.breaks_determinism() || *condition == ComparableCondition::RunFailed
        })
    }
}

/// Where a witness case reached its target.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct Reaching {
    /// The side whose leaf reached it: the baseline for a rule or pattern target, the mutant
    /// for an added end, the baseline for a removed end (the baseline end the mutant cannot
    /// reach).
    pub role: DefinitionRole,
    /// The index of that leaf in the side's `final-configurations`; absent for a hit of the
    /// whole run (D16), which rests on every leaf.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub leaf: Option<u64>,
    /// For an observer target, the step of that leaf's path at which the observer answered
    /// `Hit`: the number of committed rewrite steps from the initial configuration to the
    /// configuration that step reached, at least 1 and at most the case's `steps`, since the
    /// run continues to its end after the observer accepts (ARCHITECTURE 9.2). For a pattern
    /// target `at: any-state`, the step of the first configuration on that leaf's path that
    /// reaches the target, counted the same way: 0 for the initial configuration, at most the
    /// case's `steps` (ARCHITECTURE 4.1). Absent for every other target.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub step: Option<u64>,
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
/// the case's class. In a differential campaign the semantics under test is the baseline, so the
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
            }],
            reaching: Reaching {
                role: DefinitionRole::Baseline,
                leaf: Some(0),
                step: Some(4),
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
                dictionary: None,
                climb: None,
                corpus: None,
                solve: None,
                effective_constraints: Vec::new(),
            },
            outcome: CampaignOutcome::WitnessFound {
                witness: Witness {
                    label: HitLabel::PropertyFailure,
                    first: case.clone(),
                    shrunk: Some(case),
                    clean_leaf_facts: vec!["ceil-free".into()],
                    krun_command: Some("krust krun transfer.imp".into()),
                    mutant_krun_command: Some("krust krun --definition <mutant-dir>".into()),
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
                coverage: CoverageTotals {
                    applied: BTreeSet::from(["b".to_owned(), "a".to_owned()]),
                    matched: BTreeSet::from(["c".to_owned()]),
                    names: BTreeMap::from([(
                        "a".to_owned(),
                        RuleName {
                            kind: k_rust::backend::CompiledRuleKind::Rewrite,
                            label: Some("IMP.a".into()),
                            locations: vec![crate::target::RuleLocation {
                                source: "/w/imp.k".into(),
                                reference: "imp.k".into(),
                                line: 3,
                                end_line: 4,
                            }],
                        },
                    )]),
                },
                target_blocked: 3,
                pattern_body_matches: Some(4),
                best_score: Some(BestScore {
                    scored_cases: 3,
                    best: Some(ScoreValue {
                        case: 1,
                        level: Some(0),
                        guard_distance: Some("2/3".into()),
                    }),
                }),
                outside_determinism: 0,
                unconfirmed: 1,
                case_sequence_digest: digest_hex(b"cases"),
                solve: None,
            },
            normal_end: Some(NormalEnds {
                baseline: NormalEndKind::EveryK,
                mutant: None,
            }),
            incidental: Incidentals::default(),
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

    #[test]
    fn report_round_trips_through_canonical_json() {
        let report = fixed_report();
        let text = report.to_canonical_json();
        let read = FuzzReport::from_json(&text).expect("the report reads back");
        assert_eq!(read, report);
        assert_eq!(read.to_canonical_json(), text);

        let mut cancelled = report;
        cancelled.outcome = CampaignOutcome::Aborted {
            reason: "prelude".into(),
            no_witness: NoWitness {
                statement: "No witness.".into(),
                path_mode: PathMode::AllPaths,
            },
        };
        let text = cancelled.to_canonical_json();
        assert!(
            text.contains(concat!(
                r#""outcome":{"status":"aborted","reason":"prelude","no-witness":"#,
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
            r#"{"schema":"krust-fuzz-report","version":7,"identity":{"engine-version":6,"#,
            r#""k-rust-revision":"b322de1ab","definitions":[{"role":"baseline","#,
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
            r#""proposers":{"anchors-first":true,"explicit":"#,
            r#"[{"AMOUNT":{"bytes":"00ab"}}],"weights":{"blind":1}},"#,
            r#""bounds":{"int-bits":64,"length":16,"depth":4},"#,
            r#""caps":{"int-bits":4096,"length":65536,"depth":16,"enumeration":65536,"#,
            r#""value-size":131072},"#,
            r#""rejection-cap":"10","#,
            r#""seed":"18446744073709551615","budget":{"cases":"5000"},"#,
            r#""thread-stack-size":"67108864","solver":"none"},"#,
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
            r#""label":"IMP.a","locations":[{"source":"/w/imp.k","reference":"imp.k","line":3,"#,
            r#""end-line":4}]}}},"#,
            r#""target-blocked":3,"pattern-body-matches":4,"#,
            r#""best-score":{"scored-cases":3,"best":{"case":1,"level":0,"#,
            r#""guard-distance":"2/3"}},"outside-determinism":0,"unconfirmed":1,"#,
            r#""case-sequence-digest":"CASES"},"normal-end":{"baseline":"every-k"},"#,
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
            r#""halts":["stuck"]}],"#,
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
