//! `kink-flow fuzz`: a k-rust-fuzz campaign on kink's own sides (fz26 P7-KINKFLOW, tickets T3a
//! and T3b).
//!
//! The command takes a template, a program of the flow with some of its literals marked as holes
//! (`TEMPLATES.toml`, [`TemplateList`]), and one job ([`FuzzJob`]). T3a builds the kill job: look
//! for hole values that make the template kill one mutation of the flow's list, so that the
//! program can join the corpus and kink's own `run` proves the kill. T5 adds the rule jobs (a
//! program `coverage` would list in a rule's `matched_by`, `--matched`, or `fired_by`, `--fired`:
//! its all-paths run must be comparable, since kink counts only comparable programs) and the pattern job (a program
//! whose run reaches a configuration matching a pattern of `PATTERNS.toml`, as a `query` hit:
//! matched at any state, with the facts a complete search could stop at refused). Both run on
//! the baseline alone.
//!
//! **Sides.** The baseline is the admitted specification's compile, converted with
//! `k_rust_fuzz::CompiledDefinition::from_artifacts` with the loaded definition's source table,
//! on the route kink runs (`BackendRoute::FromDefinition`); it keeps its claims, as every kink
//! baseline run does. The mutant is the mutation's patch ([`crate::mutation::resolve`]) made
//! into the claim-free, consistency-checked mutant every kink test of that mutant runs on
//! (kink-campaign `claim_free_mutant`, admitted with the campaign's module and the flow's
//! `[spec] assume_joined`), converted with the baseline's source table: a mutant shares the
//! baseline's sources, and its provenance indexes them. A mutation kink would refuse
//! (`invalid-mutation`, `equivalent`, an invalid or inconsistent mutant, unsupported claims) ends
//! the command with kink's status and reason, and nothing is fuzzed. So does a mutation kink
//! decides from its edit alone (kink-patch `ClaimSupport::weakening`, on a baseline without an
//! unassumed finding, as `run` decides it): `unkillable` (reason `weakening`) or `equivalent`
//! (reason `valid-condition`) is a fact of the axioms, which no case can change, so the job is
//! refused at stage `mutation` with that status's reason and the row's action.
//!
//! **Comparability.** The campaign reads data ends strictly: a definition whose full critical-pair
//! check reports a finding no name assumes makes the campaign `not-comparable`, and the document
//! lists every finding with its side and verdict. Under such a finding the definition may
//! identify the two ends a kill compares, so a kill would hold in no model of it; kink's own run
//! refuses it as well (`baseline-findings`) unless the flow names the findings. A finding is read
//! as resolved only when the author names it: in the flow's `[spec] assume_joined`, which are
//! always passed, or with `--assume-joined NAME` for this command. Every assumed name is printed
//! beside the `[[program]]` fragment, genuine ones flagged, with the instruction to add each name
//! the flow lacks (kink counts no kill on the definition without it).
//!
//! **Guards** (T3b). kink's definition exclusions are read on both sides as kink's runner reads
//! them; one refuses the job with the status and reason kink's `run` gives the mutation (`unknown`
//! and the exclusion for the mutant's; `error`, `no-comparable-program` for the baseline's, which
//! excludes every program's baseline run). A side whose short-circuit analysis flags a rule has no
//! definition exclusion for it: kink's runner judges each run of it by k-rust's
//! `shortCircuitReadings` list of that run, so the job runs, and kink's confirmation of a witness
//! judges the witness's own runs (the witness filter keeps its stricter static reading). kink
//! assembles every test's input from the baseline's grammar for both sides, so a run of no case
//! first compares each side's initial configuration at the holes' anchors: a mutant that assembles
//! the template otherwise (a `[macro]` edit) is refused before any case, and so is a baseline that
//! assembles it otherwise than kink does. The campaign assembles a case as krun does, and krun
//! reads a configuration variable's text with the rule kink reads it with (k-rust
//! `variable_reading_modules`, applied by k-rust's `ConfigurationAssembler` for both), so one text
//! is one input to both. Each candidate's program is then assembled by kink exactly as a
//! `[[program]]` ([`check_assembly`]), and each side's initial configuration must be that
//! configuration, or the candidate is not offered (`assembly-mismatch`). The last `run` document,
//! only read, gives the template program's class and the mutation's `witnesses` (suggested
//! as templates), and the document warns about an unusable template, a template outside the
//! witnesses, and the scope of `--time-limit-ms`.
//!
//! **Witness filter** (fz26 FZ-COMPARABLE-B). Unless `--no-filter` is given
//! ([`FuzzOptions::filter`]), the campaign runs with kink's own rules as a k-rust-fuzz witness
//! filter ([`crate::fuzz_filter`]), built from the loads the definition exclusions were read
//! from: a candidate kink would refuse for a reason that depends on the input (a non-ASCII String
//! end) is refused inside the search, repaired when its String holes can be, and the search goes
//! on. A campaign whose every hit was refused stops `client-refused`, never `budget`. A template
//! whose own input the filter excludes, reading it as a route without a run's lists does, is
//! refused before any case (`initial-state-excluded`), since the filter would refuse every
//! candidate that keeps the template's text outside its holes. The
//! filter keeps each side's kink load for the whole campaign (about +90 MB of peak memory on
//! TRIAL3's SIMPLE job, not measurable on IMP); `--no-filter` drops them.
//!
//! **Budgets.** `--cases N` (default [`DEFAULT_CASES`]) or `--work W`, `--seed S` (default 0),
//! the library's default proposers. Every case runs with the flow's `max_depth`, a safety limit
//! of the flow's `time_ms` per execution, and `max_work` of `--max-work` (default
//! [`DEFAULT_MAX_WORK`], always set, since a depth bound alone would leave work unbounded). Kills
//! use all paths unless `--one-path`. `--time-limit-ms T` cancels the campaign's run (not its
//! setup) after `T` ms; a cancelled campaign is outside the determinism contract
//! (`stopped: time-limit`). The campaign runs on the caller's thread, which the command line
//! gives kink-corpus's definition stack allowance. A case whose run stopped for lack of native
//! stack (k-rust-fuzz's unjudged reason `stack-stops`) judges nothing, and no budget bounds the
//! stack: after `--stack-stops N` such cases in a row (default [`DEFAULT_STACK_STOPS`]) the search
//! ends (`stopped: stack-stops`), with the advice of kink's `stack-stop` reason in place of a
//! larger budget. A kill job whose mutation the last run left `unknown` with reason `stack-stop`
//! warns so before any case (`stack-stop`). Of a kill job, a case whose mutant run ends holding a
//! term not shown to exist (`not-ceil-free`: an application the mutant leaves open) judges nothing
//! either, whatever the budget: after `--open-stops N` such cases in a row (default
//! [`DEFAULT_OPEN_STOPS`]) the search ends (`stopped: open-stops`), with the advice of kink's
//! `open-application` reason, and a mutation the last run left `unknown` with that reason is
//! warned before any case (`open-application`). Each stop is a count of cases, never a clock.
//!
//! **A corpus with `[stop]`.** A stop is part of a case's meaning: a path of the case ends at its
//! last stop event, so a state past it is no state of the case, and a step past it is taken by
//! no run kink judges. The campaign therefore runs the system the corpus states: its stop
//! (k-rust-fuzz `CaseOptions::stop`, the stop's rules and the template's count) is on every
//! request of every job, so a case's coverage, reach, hit and kill are those of the truncated
//! system, and its confirmation runs the overlay with the same stop. The template's count is its
//! program's `stop_count`, else `[stop] count`; a `file` or `text` template may give its own
//! `stop_count`, which its fragment writes. A kill job's mutant must have a rewrite rule of every
//! label the stop names, as `run` requires, or the job is refused (status `not-admitted`, reason
//! `stop-unresolved`), and an edit the stop before its rule hides from the template is warned
//! (`stop-hides-edit`). A stop condition (`[stop] when`) is refused (stage `stop`, reason
//! `unsupported-verb`): k-rust-fuzz runs its cases on the wire route, which carries no callback to
//! ask a condition at each arrival.
//!
//! **A corpus with `[observe]`.** An observation channel compares two definitions' runs; it
//! changes neither which states a run reaches, which rules it fires, nor where it ends. So the
//! single-definition jobs (rule, coverage-gap and pattern jobs) admit the declaration and run
//! their cases as without it, saying why (`job.observe`). What it changes is which programs the
//! corpus counts: `coverage` counts a program a deterministic bound cuts (`comparable-prefix`,
//! by its channels) beside a `comparable` one. A fuzz goal is a program the corpus's own
//! judgement counts, so a rule or coverage-gap job's confirmation accepts exactly the classes
//! `coverage` counts, by its predicate (`ResultClass::can_kill`). The campaign still searches
//! for `comparable` witnesses only: k-rust-fuzz reads a rule or coverage goal at a leaf, and a
//! path a bound cut is no hit there, so a witness `coverage` counts only by its channels is
//! confirmed when given (`confirm_program`), not searched for. A kill job is refused (stage `observe`, reason
//! `unsupported-verb`): its campaign compares the two sides' ends only, while a kill of a corpus
//! with `[observe]` is a decided difference of an observation sequence, so a search judged by
//! ends would look for another kind of kill than the one `run` judges.
//!
//! **Output.** One document ([`FUZZ_SCHEMA`]): the fuzz report of the attempt, the candidate (the
//! shrunk witness case, else the first), and the `[[program]]` fragment, printed, never written.
//! **Confirmation** (T4). Unless `--no-confirm` is given ([`FuzzOptions::confirm`]), kink's own
//! code confirms the candidate on an overlay of the flow held in memory, with the fragment as its
//! only program and a scratch cache removed on every path (`confirm`): `run` for a kill,
//! `coverage` for a rule job, `query` for a pattern. When kink refuses the shrunk case and the first
//! is another program, the first is confirmed too; there is no seed retry. A candidate kink
//! refuses is not offered (`stopped: unconfirmed`). Nothing under the flow's directory or the
//! cache is written.

use crate::fuzz_filter::{FilterJob, FilterSide, KinkJudgement};
use crate::{
    admit::{AdmittedSpec, CaseInputs, InputSession, ProgramBinding, ProgramInputs, admit_spec},
    cli::{CommandSpelling, FrontEnd, Verb},
    digest::{program_digest, spec_digest},
    manifest::{FlowManifest, ManifestError, Program},
    mutation::{Expect, InvalidReason, MutationList, RuleText, resolve, rule_texts},
    pattern::{INVALID_PATTERN, Lowering, PatternList, Searcher},
    report::claims_value,
    results::kebab,
    search::status_name,
    search::{RunMode, RunOptions},
};
use k_rust::kore::{
    ast::{Pattern as KorePattern, Sentence},
    parser::{parse_definition, parse_pattern},
};
use k_rust::names::KoreAttribute;
use k_rust_fuzz::{
    BackendRoute, Budget, CallerIdentity, Campaign, CampaignSpec, CancellationToken, CaseOptions,
    CompiledDefinition, Definitions, HoleDecl, HoleLocation, PathMode, ProgramInput,
    ProposerConfig, Target, TargetKind,
    error::CampaignError,
    exec::ComparableCondition,
    holes::HoleFile,
    report::{
        AbortKind, CampaignOutcome, DefinitionFinding, FindingVerdict, FuzzReport, WitnessCase,
        digest_hex,
    },
    spec::{DEFAULT_REJECTION_CAP, ProgramSource as FuzzProgram, ProgramText},
    target::{
        CoverageTarget, DifferentialTarget, PatternAt, PatternTarget, RuleMode, RuleRef, RuleTarget,
    },
    values::GenerationBounds,
};
use kink_campaign::{MutantAdmission, claim_free_mutant};
use kink_corpus::{ProgramSource, cli::DEFINITION_STACK_BYTES};
use kink_native::{
    ValidatedDefinition,
    coverage::{RuleAuthors, coverage_domain},
    data::{DataEnds, data_ends},
    exclusion::{DefinitionExclusions, Exclusion, ValidatedLoad},
    execution::SolverProfile,
};
use kink_patch::SentenceRef;
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path, PathBuf},
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
        mpsc,
    },
    thread,
    time::Duration,
};
use toml::{Table, Value as Toml};

/// The document's `schema`.
pub const FUZZ_SCHEMA: &str = "kink-flow-fuzz";
/// The document's `version`. Version 3 (fz26 FZ-COMPARABLE-B) adds `job.filter`, the `stopped`
/// value `client-refused`, the warning `client-refused` and the refusal `initial-state-excluded`,
/// and embeds fuzz reports that carry the witness filter's fields. Version 4 (fz26 round 4,
/// FZ-REPLAY-WHOLE) embeds k-rust-fuzz reports of version 10: their identity records the
/// k-rust-fuzz build and the parser's diagnostic work limit, their totals the first case outside
/// the determinism contract, and every source location they name is relative to the main
/// module's file; it also adds the `stopped` value `domain-exhausted` and the warning
/// `witness-not-terminating` (FZ-ENGINE-R4), and the embedded totals' `domain`, `diverging` and
/// `coverage-last-grew`. Version 5 adds the warning `reaching-not-computed`: the last run's
/// `reaching` is null for a mutation whose compiled edit it neither computed nor found in the
/// outcome cache, and so is `template.last_run.mutation.reaching`. Version 6 (CF-40c2) names each
/// coverage predicate as every kink-flow document does: the rule jobs are `--matched RULE` and
/// `--fired RULE` (job kinds `matched` and `fired`, refusal stage `rule`) in place of `--reach RULE
/// [--fired]` (kind `reach`), whose `job.rule.mode` (k-rust-fuzz's goal name, `condition-reached`
/// or `covered`, which `job.kind` says again) is gone, a rule job's confirmation status is
/// `matched` or `not-matched` (`fired`, `not-fired`) for a comparable program and `not-comparable`
/// for any other, in place of `reached` or `unreached`, the last run's `mutation.reaching` is
/// `mutation.witnesses`, and the warnings `reaching-not-computed`, `no-reaching-program` and
/// `template-not-reaching` are `witnesses-not-computed`, `no-witness` and `template-not-a-witness`;
/// a version 5 document's names are the old ones. Version 7 adds the refusal at stage `stop`
/// (reason `unsupported-verb`) of a corpus with `[stop]`, with its `stopped` value `refused` and
/// its `action`. Version 8 adds `template.last_run.mutation.witnesses_global`, the last run row's
/// `witnesses_global`, and the warning `global-witnesses`: the mutation's edit is not site-local,
/// so every program is a witness by default, the template included, whatever its case reaches.
/// Version 9 refuses a kill job of a mutation kink decides from its edit (stage `mutation`, reason
/// `unkillable` or `equivalent`, with `job.status`, `job.reason` and `job.weakening`) in place of
/// the warning `unkillable`, adds the `stopped` value `stack-stops` (`--stack-stops N`
/// consecutive cases that stopped for lack of native stack), the warning `stack-stop` (the last
/// run's reason for the mutation) and the warning `not-ceil-free` (each function the campaign's
/// report names as held unevaluated in a leaf it could not judge).
/// Version 10 adds the `stopped` value `open-stops` (`--open-stops N` consecutive cases of a kill
/// job whose mutant run ends holding a term not shown to exist), the warnings `open-application`
/// (the last run's reason for the mutation) and `last-run-without-mutation` (the last run has no
/// row for it), gives `global-witnesses` only where the template's own program does not reach an
/// edited rule, and names the kill job's list and cache in every next step that runs `run`.
/// Version 11 adds the kill job of a condition flip the front end derives (`--kill FLIP` where no
/// list given holds the id, [`fuzz_derived`]): a kill job's `job.flip` says whether its mutation is
/// such a flip; a flip the front end's judge refused is refused at stage `mutation` with
/// `job.status` `refused` and the judge's reason; and a flip's next steps that would run `run`
/// run `coverage`, whose flips family judges it.
/// Version 12 names, under the Z3 profile, the Z3 build the confirmations were decided on (`z3`,
/// [`crate::with_z3_build`]): a confirmation is a kink run of the program found, whose classes and
/// kill are a function of the build that counts its solver queries' units.
/// Version 13 (CS-8) adds the coverage-gap jobs, `--refuted RULE` (job kind `refuted`, with
/// `job.rule`) and `--cover ITEM` (kind `cover`): each has `job.item`, the obligation it covers
/// (`{id, family, kind, file, line, facts}`), is refused at stage `item` (reasons
/// `unknown-item`, `mcdc-requirement`, `no-requirement`, `no-obligation`, `no-binder`,
/// `no-skeleton`, `no-syntax-facts`, `no-fact`), runs a k-rust-fuzz coverage target with the
/// climb beside blind sampling, and has the confirmation statuses `covered` and `not-covered`
/// (reason `listed`, `not-listed` or `unknown-item`) beside `not-comparable`. The other jobs'
/// documents are version 12's.
/// Version 14 adds `job.expect` to a kill job, the verdict its mutation states it expects
/// (`survive`, `kill` or null, [`crate::Expect`]), and the warning `expected-to-survive`: the
/// search of a mutation expected to survive is not refused, since it is the most direct attempt
/// to refute the claim, and a witness it finds is a finding when kink confirmed it and it needs no
/// premise the flow lacks ([`refutes_survival`], `crate::cli::fuzz_status`), whose action says
/// so; another witness of it is a candidate, and its action says what is left to decide. The
/// other jobs' documents are version 13's.
/// Version 15 runs a corpus with `[stop]` and one with `[observe]` (module documentation): the
/// refusals at stages `stop` and `observe` are narrowed to a stop condition and to a kill job
/// under observations; the document names the manifest's `stop` and `observe` (its declaration)
/// when it has them, `template.stop_count` is the count the template's runs end at, a
/// single-definition job under observations has `job.observe` (`{ignored}`, why it ignores
/// them), a kill job whose mutant the stop does not resolve is refused at stage `mutant`
/// (`job.status` `not-admitted`, reason `stop-unresolved`), the warning `stop-hides-edit` is
/// given, a template may give `stop_count`, and its fragment writes it; it embeds k-rust-fuzz
/// reports of version 11, whose identity records the stop.
/// `tests/formats.rs` ties the version to the document's shape.
/// 16 names each finding of the full critical-pair check by its kind, sentences and a digest of its
/// compiled sentences (`root:A,B#D`, k-rust-backend `data_term::names`) where it named it by
/// generated-K positions, gives each finding its `sentences` (`{part, at}`, `at` information only),
/// and refuses a `[spec] assume_joined` name with one of the reasons `malformed`, `position-name`,
/// `unnamed-sentence`, `no-digest`, `changed`, `no-finding`, `decided` or `ambiguous` where it
/// refused `name-refused` (KINK-FINDING-NAMES); the names it prints and reads (`assumed`,
/// `findings`, `--assume-joined`) are those names, and it embeds k-rust-fuzz reports of version 12.
/// 17 embeds k-rust-fuzz reports of version 13, whose identity bounds the solver by Z3 resource
/// units unless the campaign asks for the clock and names the Z3 build (CF-33).
pub const FUZZ_VERSION: u32 = 17;
/// The cases of a campaign that names neither `--cases` nor `--work`.
pub const DEFAULT_CASES: u64 = 1000;
/// The `max_work` of every case when `--max-work` is not given.
pub const DEFAULT_MAX_WORK: u64 = 100_000;
/// How many consecutive cases that stopped for lack of native stack end the search when
/// `--stack-stops` is not given ([`FuzzOptions::stack_stops`]). A case whose run stops for lack
/// of stack judges nothing, so it can be no witness, and no option of the campaign bounds the
/// stack; a template whose cases keep reaching a recursion that does not end spends each case to
/// that stop (seconds each on the introduction's story). The guide's trials killed every
/// killable mutation on a template whose run reached the edited rule and ended on both
/// definitions within 1 to 25 cases of blind sampling, so 25 cases in a row on which the run did
/// not end are as many as a template that can kill needed there, none of them a case that could.
/// The stop ends a search and decides no verdict: a search it ends has found no witness, as one
/// the budget ends.
pub const DEFAULT_STACK_STOPS: u64 = 25;
/// How many consecutive cases of a kill job whose mutant run ends holding a term not shown to
/// exist end the search when `--open-stops` is not given ([`FuzzOptions::open_stops`]). Such a
/// case is unjudged (k-rust-fuzz's `not-ceil-free`): where the mutant leaves an edited function's
/// value open (kink's reason `open-application`), every case that reaches the application ends so,
/// whatever the budget, and no case of them can be a witness. The count is the stack stop's, by
/// the same argument ([`DEFAULT_STACK_STOPS`]): 25 cases in a row none of which could be a witness
/// are as many as a template that can kill needed in the guide's trials. The stop ends a search
/// and decides no verdict.
pub const DEFAULT_OPEN_STOPS: u64 = 25;

// ---------------------------------------------------------------------------------------------
// TEMPLATES.toml
// ---------------------------------------------------------------------------------------------

/// A decoded `TEMPLATES.toml`. Paths are relative to [`TemplateList::directory`] and stay inside
/// it, by the rule `FLOW.toml`'s paths follow.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TemplateList {
    /// The directory holding the file.
    pub directory: PathBuf,
    pub templates: Vec<Template>,
}

/// One `[[template]]`: a program text and its holes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Template {
    pub id: String,
    pub source: TemplateSource,
    /// `start_sort`; absent: the corpus program's, else kink's default
    /// (`program_start_position` of `$PGM`'s sort).
    pub start_sort: Option<String>,
    /// Configuration variables, name (without `$`) to text, sorted by name.
    pub variables: Vec<(String, String)>,
    /// The holes, decoded with k-rust-fuzz's `[[hole]]` decoder; a span hole addresses the
    /// template's text, whose name in the campaign is the template's id.
    pub holes: Vec<HoleDecl>,
    /// `stop_count`: the stop event the template's runs end at, in place of `[stop] count`, as a
    /// `[[program]]`'s `stop_count`; absent: `[stop] count`. A template of a corpus program takes
    /// that program's.
    pub stop_count: Option<std::num::NonZeroU64>,
}

/// Where a template's text comes from.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TemplateSource {
    /// `program`: a `[[program]]` of the flow, with its text, start sort and variables.
    Program(String),
    /// `file`, relative to the templates' directory.
    File(String),
    /// `text`.
    Text(String),
}

impl TemplateList {
    /// Read and decode the file at `path`; its directory becomes the root of its paths.
    ///
    /// # Errors
    ///
    /// The file cannot be read, or does not decode ([`Self::decode`]).
    pub fn read(path: &Path) -> Result<Self, ManifestError> {
        let text = fs::read_to_string(path)
            .map_err(|e| ManifestError::new("", format!("cannot read the templates: {e}")))?;
        let directory = match path.parent() {
            Some(parent) if !parent.as_os_str().is_empty() => parent.to_path_buf(),
            _ => PathBuf::from("."),
        };
        Self::decode(&text, &directory)
    }

    /// Decode `text`, whose paths are relative to `directory`. Strict, as `FLOW.toml`: an unknown
    /// key, a value of the wrong type, a duplicate id, a template with not exactly one of
    /// `program`, `file` and `text`, or a path leaving the directory is an error naming the key.
    /// Each `[[template.hole]]` goes from its TOML value through k-rust-fuzz's serde decoder
    /// (`HoleFile`), whose messages are wrapped with the template and the hole's index; a TOML
    /// date or time anywhere in a hole is refused (it is no K value), and a hole's `program`
    /// may only name a binding (`"$NAME"`, a literal inside that variable's text): by default a
    /// hole addresses the template's text.
    ///
    /// # Errors
    ///
    /// The first problem found, naming its key.
    pub fn decode(text: &str, directory: &Path) -> Result<Self, ManifestError> {
        let top: Table = toml::from_str(text)
            .map_err(|e| ManifestError::new("", format!("invalid TOML: {e}")))?;
        if let Some(key) = top.keys().find(|key| key.as_str() != "template") {
            return Err(ManifestError::new(key.clone(), "unknown key"));
        }
        let templates = match top.get("template") {
            None => Vec::new(),
            Some(Toml::Array(entries)) => entries
                .iter()
                .enumerate()
                .map(|(index, entry)| template(index, entry))
                .collect::<Result<Vec<_>, _>>()?,
            Some(_) => {
                return Err(ManifestError::new(
                    "template",
                    "expected [[template]] tables",
                ));
            }
        };
        let mut ids = BTreeSet::new();
        for template in &templates {
            if !ids.insert(template.id.as_str()) {
                return Err(ManifestError::new(
                    template_key(&template.id),
                    "duplicate template id",
                ));
            }
        }
        Ok(Self {
            directory: directory.to_path_buf(),
            templates,
        })
    }

    /// The template with this id.
    #[must_use]
    pub fn get(&self, id: &str) -> Option<&Template> {
        self.templates.iter().find(|template| template.id == id)
    }
}

fn template_key(id: &str) -> String {
    format!("template {id:?}")
}

fn join(prefix: &str, key: &str) -> String {
    format!("{prefix}.{key}")
}

fn nonempty_string(value: &Toml, key: &str) -> Result<String, ManifestError> {
    match value.as_str() {
        Some(text) if !text.is_empty() => Ok(text.to_owned()),
        Some(_) => Err(ManifestError::new(key, "must not be empty")),
        None => Err(ManifestError::new(key, "expected a string")),
    }
}

/// A relative path that stays inside the templates' directory (`FLOW.toml`'s rule).
fn relative_path(value: &Toml, key: &str) -> Result<String, ManifestError> {
    let text = nonempty_string(value, key)?;
    let mut depth = 0usize;
    for component in Path::new(&text).components() {
        match component {
            Component::Normal(_) => depth += 1,
            Component::CurDir => {}
            Component::ParentDir if depth > 0 => depth -= 1,
            _ => {
                return Err(ManifestError::new(
                    key,
                    format!("path {text:?} leaves the templates' directory"),
                ));
            }
        }
    }
    Ok(text)
}

fn template(index: usize, value: &Toml) -> Result<Template, ManifestError> {
    let position = format!("template[{index}]");
    let entry = value
        .as_table()
        .ok_or_else(|| ManifestError::new(&position, "expected a table"))?;
    let id = nonempty_string(
        entry
            .get("id")
            .ok_or_else(|| ManifestError::new(join(&position, "id"), "missing required key"))?,
        &join(&position, "id"),
    )?;
    let key = template_key(&id);
    if let Some(unknown) = entry.keys().find(|name| {
        ![
            "id",
            "program",
            "file",
            "text",
            "start_sort",
            "variables",
            "hole",
            "stop_count",
        ]
        .contains(&name.as_str())
    }) {
        return Err(ManifestError::new(join(&key, unknown), "unknown key"));
    }
    let source = match (entry.get("program"), entry.get("file"), entry.get("text")) {
        (Some(program), None, None) => {
            TemplateSource::Program(nonempty_string(program, &join(&key, "program"))?)
        }
        (None, Some(file), None) => TemplateSource::File(relative_path(file, &join(&key, "file"))?),
        (None, None, Some(Toml::String(text))) => TemplateSource::Text(text.clone()),
        (None, None, Some(_)) => {
            return Err(ManifestError::new(join(&key, "text"), "expected a string"));
        }
        _ => {
            return Err(ManifestError::new(
                key,
                "give exactly one of program, file and text",
            ));
        }
    };
    let program_source = matches!(source, TemplateSource::Program(_));
    let start_sort = entry
        .get("start_sort")
        .map(|value| nonempty_string(value, &join(&key, "start_sort")))
        .transpose()?;
    let variables = match entry.get("variables") {
        None => Vec::new(),
        Some(Toml::Table(variables)) => variables
            .iter()
            .map(|(name, text)| {
                let variable_key = join(&join(&key, "variables"), name);
                if name.is_empty() {
                    return Err(ManifestError::new(variable_key, "empty variable name"));
                }
                match text {
                    Toml::String(text) => Ok((name.clone(), text.clone())),
                    _ => Err(ManifestError::new(variable_key, "expected a string")),
                }
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?
            .into_iter()
            .collect(),
        Some(_) => {
            return Err(ManifestError::new(
                join(&key, "variables"),
                "expected a table of strings",
            ));
        }
    };
    let stop_count = match entry.get("stop_count") {
        None => None,
        Some(Toml::Integer(count)) => Some(
            u64::try_from(*count)
                .ok()
                .and_then(std::num::NonZeroU64::new)
                .ok_or_else(|| {
                    ManifestError::new(join(&key, "stop_count"), "expected a positive integer")
                })?,
        ),
        Some(_) => {
            return Err(ManifestError::new(
                join(&key, "stop_count"),
                "expected a positive integer",
            ));
        }
    };
    if program_source && (start_sort.is_some() || !variables.is_empty() || stop_count.is_some()) {
        return Err(ManifestError::new(
            key,
            "a template of a corpus program takes that program's start_sort, variables and \
             stop_count; give the text as file or text to set others",
        ));
    }
    let holes = match entry.get("hole") {
        None => Vec::new(),
        Some(Toml::Array(holes)) => holes
            .iter()
            .enumerate()
            .map(|(index, hole)| template_hole(&id, &key, index, hole))
            .collect::<Result<Vec<_>, _>>()?,
        Some(_) => {
            return Err(ManifestError::new(
                join(&key, "hole"),
                "expected [[template.hole]] tables",
            ));
        }
    };
    Ok(Template {
        id,
        source,
        start_sort,
        variables,
        holes,
        stop_count,
    })
}

/// Whether a TOML value holds a date or time anywhere.
fn holds_datetime(value: &Toml) -> bool {
    match value {
        Toml::Datetime(_) => true,
        Toml::Array(values) => values.iter().any(holds_datetime),
        Toml::Table(table) => table.values().any(holds_datetime),
        _ => false,
    }
}

/// One `[[template.hole]]`: k-rust-fuzz's flat `[[hole]]` keys, decoded by its serde type.
fn template_hole(
    id: &str,
    key: &str,
    index: usize,
    value: &Toml,
) -> Result<HoleDecl, ManifestError> {
    let hole_key = format!("{key}.hole[{index}]");
    if !value.is_table() {
        return Err(ManifestError::new(hole_key, "expected a table"));
    }
    if holds_datetime(value) {
        // `toml::Value::try_into` would read a date as its text, a string choice `krust fuzz`
        // refuses: refuse it here, as no hole value is a date.
        return Err(ManifestError::new(
            hole_key,
            "a TOML date or time is not a hole value; write a string, an integer, a boolean or a \
             value table",
        ));
    }
    let file: HoleFile = value
        .clone()
        .try_into()
        .map_err(|error: toml::de::Error| ManifestError::new(&hole_key, error.message().trim()))?;
    if let Some(program) = file
        .program
        .as_deref()
        .filter(|program| !program.starts_with('$'))
    {
        return Err(ManifestError::new(
            join(&hole_key, "program"),
            format!(
                "{program:?}: a template's hole addresses the template's text (leave `program` \
                 out) or a binding's text (\"$NAME\")"
            ),
        ));
    }
    file.into_decl(Some(id))
        .map_err(|message| ManifestError::new(hole_key, message))
}

// ---------------------------------------------------------------------------------------------
// The kill job
// ---------------------------------------------------------------------------------------------

/// A front end's spelling with `run` replaced by the run of one mutation list and cache
/// ([`CommandSpelling::run_list`]).
struct ListRun<'a> {
    inner: &'a dyn CommandSpelling,
    run: String,
}

impl CommandSpelling for ListRun<'_> {
    fn command(&self, verb: Verb) -> String {
        if verb == Verb::Run {
            self.run.clone()
        } else {
            self.inner.command(verb)
        }
    }

    fn verb(&self, verb: Verb) -> String {
        if verb == Verb::Run {
            self.run.clone()
        } else {
            self.inner.verb(verb)
        }
    }

    fn run_list(&self, mutations: &Path, cache: Option<&Path>) -> String {
        self.inner.run_list(mutations, cache)
    }
}

/// Options of `kink-flow fuzz` (module docs, "Budgets").
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FuzzOptions {
    /// `--cases N` or `--work W`.
    pub budget: Budget,
    /// `--seed S`.
    pub seed: u64,
    /// `--max-work N`; `None`: [`DEFAULT_MAX_WORK`].
    pub max_work: Option<u64>,
    /// `--time-limit-ms T`: the watchdog that cancels the campaign's run.
    pub time_limit_ms: Option<u64>,
    /// `--assume-joined NAME`, in the order given (the flow's `[spec] assume_joined` are added).
    pub assume_joined: Vec<String>,
    /// All paths, or one with `--one-path`.
    pub paths: PathMode,
    /// `--cache DIR`: where the last `run` document is read from (default `.kink-flow` beside
    /// `FLOW.toml`); only read, for the template's class and the mutation's witnesses.
    pub cache: Option<PathBuf>,
    /// Confirm each candidate with kink's own code (KF-T4; the command line's default, off with
    /// `--no-confirm`). Off in [`FuzzOptions::default`], so a library caller asks for it.
    pub confirm: bool,
    /// Judge each candidate hit and shrink candidate inside the campaign by kink's own rules
    /// ([`crate::fuzz_filter`], fz26 FZ-COMPARABLE-B); on by default, off with `--no-filter`.
    pub filter: bool,
    /// `--stack-stops N`: how many consecutive cases that stopped for lack of native stack end
    /// the search (`stopped: stack-stops`); at least 1. Default [`DEFAULT_STACK_STOPS`].
    pub stack_stops: u64,
    /// `--open-stops N`: of a kill job, how many consecutive cases whose mutant run ends holding
    /// a term not shown to exist (not-ceil-free) end the search (`stopped: open-stops`); at least
    /// 1. Default [`DEFAULT_OPEN_STOPS`].
    pub open_stops: u64,
}

impl Default for FuzzOptions {
    fn default() -> Self {
        Self {
            budget: Budget::Cases(DEFAULT_CASES),
            seed: 0,
            max_work: None,
            time_limit_ms: None,
            assume_joined: Vec::new(),
            paths: PathMode::AllPaths,
            cache: None,
            confirm: false,
            filter: true,
            stack_stops: DEFAULT_STACK_STOPS,
            open_stops: DEFAULT_OPEN_STOPS,
        }
    }
}

/// Why the command fuzzed nothing.
struct Refusal {
    stage: &'static str,
    reason: String,
    detail: String,
}

impl Refusal {
    fn new(stage: &'static str, reason: impl Into<String>, detail: impl Into<String>) -> Self {
        Self {
            stage,
            reason: reason.into(),
            detail: detail.into(),
        }
    }

    fn value(&self) -> Value {
        json!({
            "outcome": "refused",
            "stage": self.stage,
            "reason": self.reason,
            "detail": self.detail,
        })
    }
}

/// The document's header and the parts every outcome fills; under the Z3 profile the header
/// names the Z3 build (`z3`, [`crate::with_z3_build`]).
fn document() -> Value {
    crate::with_z3_build(json!({
        "schema": FUZZ_SCHEMA,
        "version": FUZZ_VERSION,
        // k-rust's build identity, the one the embedded fuzz report records (GUIDE-USABILITY 5):
        // its version and a digest of its sources. `kink.k_rust_revision` is the identity
        // component, the version alone; `kink_build` pins the whole executable.
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "kink_build": kink_campaign::kink_build().map_or(Value::Null, |b| json!(b.to_string())),
        "kink": kink_campaign::kink_identity(),
        "spec": null,
        "template": null,
        "job": null,
        "sides": null,
        "assembly": null,
        "findings": [],
        "assumed": [],
        "attempts": [],
        "program": null,
        "stopped": null,
        "action": null,
        "warnings": [],
    }))
}

/// The document of a `FLOW.toml`, `TEMPLATES.toml` or `MUTATIONS.toml` that does not decode.
#[must_use]
pub fn input_refused(file: &str, error: &dyn std::fmt::Display) -> Value {
    let mut document = document();
    document["spec"] = Refusal::new("input", format!("invalid-{file}"), error.to_string()).value();
    document["stopped"] = json!("refused");
    document["action"] = json!(format!("fix {file}: the detail names the key"));
    document
}

/// Why a single-definition job ignores `[observe]` in its runs (module documentation):
/// `job.observe`'s `ignored`.
pub const OBSERVE_IGNORED: &str = "observation channels compare two definitions' runs: they \
     change neither which states one definition's run reaches, which rules it matches or fires, \
     nor where it ends, so this job's cases run as without them; they change only which programs \
     the corpus counts (a program a deterministic bound cuts counts as comparable-prefix by its \
     channels), which the confirmation reads with `coverage`'s own predicate";

/// Why a pattern job ignores `[observe]`: `job.observe`'s `ignored`, `query`'s reason.
const OBSERVE_IGNORED_PATTERN: &str = crate::query::OBSERVE_IGNORED;

/// The refusal of a job `fuzz` cannot run on `manifest`'s corpus, before anything is admitted:
/// a stop condition, which no case of the wire route can ask (stage `stop`), or a kill job under
/// observations, whose campaign compares ends only (stage `observe`); both reason
/// `unsupported-verb`, with the action. `None` for every other job.
fn corpus_refusal(manifest: &FlowManifest, job: &FuzzJob<'_>) -> Option<(Refusal, &'static str)> {
    if let Some(when) = manifest.stop.as_ref().and_then(|stop| stop.when.as_ref()) {
        return Some((
            Refusal::new(
                "stop",
                "unsupported-verb",
                format!(
                    "stop condition: [stop] when `{}` is asked at each arrival in the process \
                     that runs the case, and fuzz runs its cases on k-rust-fuzz's wire route, \
                     which carries no callback, so its cases would end at arrivals the corpus \
                     does not count; use `check`, `coverage`, `run` and `query`",
                    when.function
                ),
            ),
            "remove [stop] when to fuzz this corpus (its paths then end at every arrival)",
        ));
    }
    if manifest.observe.is_some() && matches!(job, FuzzJob::Kill { .. }) {
        return Some((
            Refusal::new(
                "observe",
                "unsupported-verb",
                "kill judgement: a kill of a corpus with [observe] is a decided difference of an \
                 observation channel, as `run` judges it, while the kill job's campaign compares \
                 the two definitions' ends only, so its search would look for another kill than \
                 the one `run` judges; the single-definition jobs run on this corpus, and `run` \
                 judges a program written by hand",
            ),
            "remove [observe] to fuzz kills by ends on this corpus",
        ));
    }
    None
}

/// The baseline or a mutant as a k-rust-fuzz definition: `side`'s loaded definition and compiled
/// artifacts with the baseline's source table (a mutant shares the baseline's sources), on the
/// route kink runs (`Backend::from_definition`).
///
/// # Errors
///
/// k-rust-fuzz's conversion error.
pub fn compiled_side(
    manifest: &FlowManifest,
    spec: &AdmittedSpec,
    side: &ValidatedDefinition,
) -> Result<CompiledDefinition, CampaignError> {
    let mut compiled = CompiledDefinition::from_artifacts(
        &manifest.spec.main_module,
        spec.loaded.syntax_module(),
        side.definition().clone(),
        spec.loaded.baseline.loaded().source_table().clone(),
        side.artifacts().clone(),
    )?;
    compiled.route = BackendRoute::FromDefinition;
    Ok(compiled)
}

fn side_value(side: &ValidatedDefinition, compiled: &CompiledDefinition) -> Value {
    let digest = |result: Result<String, CampaignError>| match result {
        Ok(digest) => json!(digest),
        Err(error) => json!({"error": error.to_string()}),
    };
    json!({
        "kore_sha256": side.kore_sha256().to_string(),
        "frontend_digest": digest(compiled.frontend_digest()),
        "execution_definition_digest": digest(compiled.execution_definition_digest()),
    })
}

/// A template made concrete against the flow: its text (none for a program-less case of a
/// definition without `$PGM`), start sort, variables, and where a file of the instantiated
/// program could go.
struct Instance {
    text: Option<String>,
    start_sort: String,
    start_sort_source: &'static str,
    /// The start sort a `[[program]]` of the witness writes (the template's or its program's).
    written_start_sort: Option<String>,
    variables: Vec<(String, String)>,
    file: Option<String>,
    /// The `stop_count` a `[[program]]` of the witness writes: its program's, or the template's.
    stop_count: Option<std::num::NonZeroU64>,
}

impl Instance {
    /// The campaign's stop ([`CaseOptions::stop`]): the corpus stop's rules, as the manifest
    /// names them (the exact labels kink stops at), and the count the template's runs end at;
    /// `None` without `[stop]`.
    fn case_stop(&self, manifest: &FlowManifest) -> Option<k_rust_fuzz::CaseStop> {
        let stop = manifest.stop.as_ref()?;
        Some(k_rust_fuzz::CaseStop {
            before: stop.before.clone(),
            after: stop.after.clone(),
            count: self.stop_count.unwrap_or(stop.count),
        })
    }
}

fn read_inside(root: &Path, name: &str) -> Result<Vec<u8>, String> {
    let root = fs::canonicalize(root).map_err(|_| "the templates' directory is unavailable")?;
    let path = fs::canonicalize(root.join(name)).map_err(|e| format!("cannot read {name}: {e}"))?;
    if !path.starts_with(&root) {
        return Err(format!("{name} escapes the templates' directory"));
    }
    fs::read(&path).map_err(|e| format!("cannot read {name}: {e}"))
}

/// The `$PGM` text of a template's own program, its file `name` or its inline text (`name` is
/// `None`), whose bytes are `bytes`: read as admission reads a program's
/// ([`crate::admit::InputDecoder::program`]), so that a template's text binds what the same text
/// as a `[[program]]` binds. A program the front end binds otherwise than as `$PGM` text, or
/// refuses, is refused: fuzz varies and replays `$PGM` text only.
fn template_text(
    manifest: &FlowManifest,
    name: Option<&str>,
    bytes: &[u8],
) -> Result<String, String> {
    let described = name.map_or_else(
        || "the template's text".to_owned(),
        |name| format!("the template's file {name}"),
    );
    match manifest
        .input_decoder
        .get()
        .and_then(|decoder| decoder.program(name, bytes))
    {
        None => {
            String::from_utf8(bytes.to_vec()).map_err(|e| format!("{described} is not UTF-8: {e}"))
        }
        Some(Err(message)) => Err(format!("{described}: {message}")),
        Some(Ok(ProgramBinding::Text { variable, text }))
            if variable.strip_prefix('$').unwrap_or(&variable) == "PGM" =>
        {
            Ok(text)
        }
        Some(Ok(ProgramBinding::Text { variable, .. } | ProgramBinding::Term { variable, .. })) => {
            Err(format!(
                "{described} binds ${} as the front end reads its program, which fuzz does not \
                 carry yet: fuzz varies $PGM text, so use a template that binds every input as \
                 K text under `variables`",
                variable.strip_prefix('$').unwrap_or(&variable)
            ))
        }
    }
}

fn instance(
    template: &Template,
    templates: &TemplateList,
    manifest: &FlowManifest,
    inputs: &ProgramInputs,
    spec: &AdmittedSpec,
) -> Result<Instance, Refusal> {
    let refused = |detail: String| Refusal::new("template", "template-refused", detail);
    if manifest.stop.is_none() && template.stop_count.is_some() {
        return Err(refused(
            "stop_count is the stop event a run ends at, and FLOW.toml has no [stop]: name the \
             rules to stop before or after, or remove stop_count"
                .to_owned(),
        ));
    }
    let (text, given_sort, variables, file, stop_count) = match &template.source {
        TemplateSource::Program(id) => {
            let program = manifest
                .programs
                .iter()
                .find(|program| &program.id == id)
                .ok_or_else(|| refused(format!("program {id:?}: FLOW.toml has no such program")))?;
            // A fuzz campaign varies and replays K text only: a typed input would be neither
            // carried into the campaign's input nor written back into a witness's fragment.
            if !program.inputs.is_empty() {
                return Err(refused(format!(
                    "program {id:?} has typed inputs (`inputs`), which fuzz does not carry yet: \
                     fuzz varies K text, so use a template that binds every input as K text \
                     under `variables`"
                )));
            }
            let read = inputs
                .read(program)
                .map_err(|refusal| refused(format!("program {id:?}: {}", refusal.detail)))?;
            // Likewise a program the front end binds otherwise than as `$PGM` text.
            if let Some(bound) = &read.bound {
                return Err(refused(format!(
                    "program {id:?} binds ${} as the front end reads its program, which fuzz \
                     does not carry yet: fuzz varies $PGM text, so use a template that binds \
                     every input as K text under `variables`",
                    bound.variable
                )));
            }
            let text = read.text;
            let file = match &program.source {
                Some(ProgramSource::File(name)) => Some(name.clone()),
                None | Some(ProgramSource::Text(_)) => None,
            };
            (
                text,
                program.start_sort.clone(),
                program.variables.clone(),
                file,
                program.stop_count,
            )
        }
        TemplateSource::File(name) => {
            let bytes = read_inside(&templates.directory, name).map_err(refused)?;
            (
                Some(template_text(manifest, Some(name), &bytes).map_err(refused)?),
                template.start_sort.clone(),
                template.variables.clone(),
                Some(name.clone()),
                template.stop_count,
            )
        }
        TemplateSource::Text(text) => (
            Some(template_text(manifest, None, text.as_bytes()).map_err(refused)?),
            template.start_sort.clone(),
            template.variables.clone(),
            None,
            template.stop_count,
        ),
    };
    let (start_sort, start_sort_source) = match &given_sort {
        Some(sort) => (
            sort.clone(),
            if matches!(template.source, TemplateSource::Program(_)) {
                "program"
            } else {
                "template"
            },
        ),
        None => {
            // kink's default (kink-corpus `assemble_input_with`): the program-start position of
            // `$PGM`'s declared sort.
            let variables = &spec.compiled.artifacts().configuration_variables;
            let pgm = variables
                .get("PGM")
                .cloned()
                .unwrap_or_else(|| k_rust::kast::Sort::new("KItem"));
            (
                k_rust::kompile::program_start_position(&pgm).to_string(),
                "default",
            )
        }
    };
    // A fuzz campaign varies and replays K text only: an input the template leaves to its
    // declared default would be bound by kink's assembly and not by the campaign's.
    let bound = text
        .as_ref()
        .map(|_| "PGM".to_owned())
        .into_iter()
        .chain(
            variables
                .iter()
                .map(|(name, _)| name.strip_prefix('$').unwrap_or(name).to_owned()),
        )
        .collect::<BTreeSet<_>>();
    let defaulted = inputs.defaults(&bound).map_err(refused)?;
    if !defaulted.is_empty() {
        return Err(refused(format!(
            "the template binds no value for {}, which take their declared defaults, and fuzz \
             does not carry a default yet: fuzz varies K text, so bind every input as K text \
             under `variables`",
            defaulted
                .iter()
                .map(|(name, _)| format!("${name}"))
                .collect::<Vec<_>>()
                .join(", ")
        )));
    }
    Ok(Instance {
        text,
        start_sort,
        start_sort_source,
        written_start_sort: given_sort,
        variables,
        file,
        stop_count,
    })
}

/// [`assumed_names`] in the K spelling (kink-native `SentenceNames::to_k`): the names the
/// campaign, the filter and the mutant's facts read.
fn assumed_names_k(manifest: &FlowManifest, options: &FuzzOptions) -> Vec<String> {
    assumed_names(manifest, options)
        .iter()
        .map(|name| manifest.sentence_names.to_k(name))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

/// The flow's names and the command line's, in the front end's spelling, sorted and without
/// repeats.
fn assumed_names(manifest: &FlowManifest, options: &FuzzOptions) -> Vec<String> {
    manifest
        .spec
        .assume_joined
        .iter()
        .chain(&options.assume_joined)
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn verdict_name(verdict: FindingVerdict) -> &'static str {
    match verdict {
        FindingVerdict::Genuine => "genuine",
        FindingVerdict::Undecided => "undecided",
        FindingVerdict::Decided => "decided",
    }
}

fn role_name(role: k_rust_fuzz::report::DefinitionRole) -> &'static str {
    match role {
        k_rust_fuzz::report::DefinitionRole::Baseline => "baseline",
        k_rust_fuzz::report::DefinitionRole::Mutant => "mutant",
    }
}

/// A finding of the fuzz report, its name (the K spelling) in the front end's spelling
/// `spelling`.
fn finding_value(
    finding: &DefinitionFinding,
    spelling: &kink_native::data::SentenceNames,
) -> Value {
    json!({
        "side": role_name(finding.side),
        "name": finding.name.as_deref().map(|name| spelling.spelled(name)),
        "verdict": verdict_name(finding.verdict),
        "assumed": finding.assumed,
        "reason": finding.reason,
    })
}

/// Whether the report's finding is the one `name` (in the K spelling) names: equal, or equal
/// after a side prefix that names its side.
fn names_finding(name: &str, finding: &DefinitionFinding) -> bool {
    let Some(own) = finding.name.as_deref() else {
        return false;
    };
    let side = role_name(finding.side);
    name == own
        || name
            .strip_prefix(side)
            .and_then(|rest| rest.strip_prefix(':'))
            .is_some_and(|rest| rest == own)
}

/// The assumed names, each with where it came from and the findings it assumed.
fn assumed_value(
    manifest: &FlowManifest,
    options: &FuzzOptions,
    report: Option<&FuzzReport>,
) -> Value {
    let findings = report.map_or(&[][..], |report| &report.definition_findings[..]);
    let names = assumed_names(manifest, options);
    Value::Array(
        names
            .iter()
            .map(|name| {
                let k = manifest.sentence_names.to_k(name);
                let matched = findings
                    .iter()
                    .filter(|finding| finding.assumed && names_finding(&k, finding))
                    .collect::<Vec<_>>();
                json!({
                    "name": name,
                    "in_flow": manifest.spec.assume_joined.contains(name),
                    "from_command_line": options.assume_joined.contains(name),
                    "genuine": matched.iter().any(|f| f.verdict == FindingVerdict::Genuine),
                    "findings": matched.iter().map(|f| json!({
                        "side": role_name(f.side),
                        "verdict": verdict_name(f.verdict),
                    })).collect::<Vec<_>>(),
                })
            })
            .collect(),
    )
}

/// Run `body` under a watchdog that cancels its token after `time` (when given); whether it
/// fired.
fn under_watchdog<T>(
    time: Option<Duration>,
    body: impl FnOnce(Option<CancellationToken>) -> T,
) -> (T, bool) {
    let Some(time) = time else {
        return (body(None), false);
    };
    let token = CancellationToken::new();
    let fired = Arc::new(AtomicBool::new(false));
    if time.is_zero() {
        fired.store(true, Ordering::Release);
        token.cancel();
    }
    let (done, finished) = mpsc::channel::<()>();
    let guard = {
        let token = token.clone();
        let fired = Arc::clone(&fired);
        thread::spawn(move || {
            if finished.recv_timeout(time) == Err(mpsc::RecvTimeoutError::Timeout) {
                fired.store(true, Ordering::Release);
                token.cancel();
            }
        })
    };
    let value = body(Some(token));
    drop(done);
    guard.join().expect("the watchdog thread does not panic");
    (value, fired.load(Ordering::Acquire))
}

/// The run of consecutive cases that stopped for lack of native stack, which ends the search at
/// `limit` ([`FuzzOptions::stack_stops`]): a case is counted when it could not be judged for that
/// reason (k-rust-fuzz's `stack-stops`, on either side), and any other case starts the run again.
/// Of a kill job, the run of consecutive cases whose mutant run ends holding a term not shown to
/// exist (k-rust-fuzz's `not-ceil-free`, on the mutant's side: an application the mutant leaves
/// open, which no budget decides) ends it at its own limit ([`FuzzOptions::open_stops`]).
struct StackStops {
    limit: u64,
    run: u64,
    /// Whether every case of the current run was `unsupported` (the mutant's run, or the only
    /// side's), not `baseline-incomplete`.
    unsupported: bool,
    /// The not-ceil-free run of a kill job: its limit (0 for another job, which counts none),
    /// its length, and whether every case observed so far was one.
    open_limit: u64,
    open_run: u64,
    all_open: bool,
}

impl StackStops {
    const fn new(limit: u64, open_limit: u64) -> Self {
        Self {
            limit,
            run: 0,
            unsupported: true,
            open_limit,
            open_run: 0,
            all_open: true,
        }
    }

    /// Count `note`; whether the search ends there.
    fn observe(&mut self, note: &k_rust_fuzz::CaseNote) -> bool {
        if note.unjudged == Some(k_rust_fuzz::exec::UnjudgedReason::StackStops) {
            if self.run == 0 {
                self.unsupported = true;
            }
            self.run += 1;
            self.unsupported &= note.class == k_rust_fuzz::OutcomeClass::Unsupported;
        } else {
            self.run = 0;
        }
        let open = note.class == k_rust_fuzz::OutcomeClass::Unsupported
            && note.unjudged == Some(k_rust_fuzz::exec::UnjudgedReason::NotCeilFree);
        if open {
            self.open_run += 1;
        } else {
            self.open_run = 0;
            self.all_open = false;
        }
        self.ended() || self.open_ended()
    }

    /// Whether the run reached the limit (the observer ended the search).
    const fn ended(&self) -> bool {
        self.limit > 0 && self.run >= self.limit
    }

    /// Whether the not-ceil-free run reached its limit (the observer ended the search).
    const fn open_ended(&self) -> bool {
        self.open_limit > 0 && self.open_run >= self.open_limit
    }

    const fn all_unsupported(&self) -> bool {
        self.unsupported
    }

    /// Whether every case observed was not-ceil-free on the mutant (and some case was).
    const fn all_open(&self) -> bool {
        self.all_open && self.open_run > 0
    }
}

/// The advice of a budget stop where every case's run ended holding a term not shown to exist:
/// a kill job (`kill`) judges a case on its mutant run, while a rule or pattern job has no mutant
/// and its one run is the template's own.
const fn all_open_hint(kill: bool) -> &'static str {
    if kill {
        "Every case's mutant run ended holding a term not shown to exist (not-ceil-free), which \
         no budget decides: rather than raising --cases or --work, choose a program or hole range \
         whose runs do not reach that application"
    } else {
        "Every case's run ended holding a term not shown to exist (not-ceil-free), which no \
         budget decides: rather than raising --cases or --work, choose a program or hole range \
         whose runs do not reach that application"
    }
}

/// The campaign's no-witness statement of a search kink-flow's observer ended (`flag`'s count):
/// k-rust-fuzz words every observer stop as its caller's cancellation, which kink-flow is, so the
/// sentence is replaced by the stop it was.
fn observer_stopped(statement: &str, flag: &str) -> String {
    statement.replace(
        " The caller cancelled the campaign.",
        &format!(" The search ended at its {flag} count."),
    )
}

/// The `[[program]]` a witness case re-enters the corpus as, and its printed fragment.
struct Fragment {
    /// The fragment, as TOML text.
    toml: String,
    /// Where a file of the program's text could go, beside the template's file.
    file: Option<String>,
    id: String,
    /// The program as kink's manifest decodes the fragment (its text inline).
    program: Program,
    /// The instantiated program's inputs: its text (none for a program-less template).
    inputs: CaseInputs,
}

/// The fragment of a witness case: the instantiated program text (the template's when the case
/// has none), the written start sort, and the template's variables with the case's instantiated
/// bindings over them (a span hole inside a binding, or a configuration-variable hole's whole
/// value).
fn fragment(template: &Template, instance: &Instance, case: &WitnessCase) -> Fragment {
    let text = case.program.clone().or_else(|| instance.text.clone());
    let mut variables = instance
        .variables
        .iter()
        .cloned()
        .collect::<BTreeMap<_, _>>();
    for (name, text) in &case.config_vars {
        let name = name.strip_prefix('$').unwrap_or(name);
        if !variables.contains_key(name) && KINK_STREAM_DEFAULTS.contains(&(name, text.as_str())) {
            // `campaign_variables`' binding, which kink's default gives the program anyway.
            continue;
        }
        variables.insert(name.to_owned(), text.clone());
    }
    for hole in &case.holes {
        if let (HoleLocation::ConfigVar { name }, Some(k_text)) = (&hole.location, &hole.k_text) {
            variables.insert(name.clone(), k_text.clone());
        }
    }
    let variables = variables.into_iter().collect::<Vec<_>>();
    let mut program = Program {
        id: String::new(),
        source: text.clone().map(ProgramSource::Text),
        start_sort: instance.written_start_sort.clone(),
        variables: variables.clone(),
        inputs: Table::new(),
        case: None,
        case_file: None,
        expect: None,
        stop_count: instance.stop_count,
    };
    let inputs = CaseInputs {
        text,
        typed: Vec::new(),
        bound: None,
        defaults: Vec::new(),
    };
    let digest = program_digest(&program, &inputs).to_string();
    let id = format!("{}-fz-{}", template.id, &digest[..8]);
    program.id.clone_from(&id);
    let file = instance.file.as_ref().map(|file| {
        let path = Path::new(file);
        let name = match path.extension().and_then(|e| e.to_str()) {
            Some(extension) => format!("{id}.{extension}"),
            None => id.clone(),
        };
        path.with_file_name(name).to_string_lossy().into_owned()
    });
    let mut table = Table::new();
    table.insert("id".into(), Toml::String(id.clone()));
    if let Some(text) = &inputs.text {
        table.insert("text".into(), Toml::String(text.clone()));
    }
    if let Some(sort) = &instance.written_start_sort {
        table.insert("start_sort".into(), Toml::String(sort.clone()));
    }
    if let Some(count) = instance.stop_count {
        table.insert(
            "stop_count".into(),
            Toml::Integer(i64::try_from(count.get()).unwrap_or(i64::MAX)),
        );
    }
    if !variables.is_empty() {
        table.insert(
            "variables".into(),
            Toml::Table(
                variables
                    .into_iter()
                    .map(|(name, text)| (name, Toml::String(text)))
                    .collect(),
            ),
        );
    }
    let mut top = Table::new();
    top.insert("program".into(), Toml::Array(vec![Toml::Table(table)]));
    let toml = toml::to_string(&top).expect("a table of strings encodes");
    Fragment {
        toml,
        file,
        id,
        program,
        inputs,
    }
}

/// The premises of a witness, as the fragment prints them: each assumed name, genuine ones
/// flagged, and whether the flow already names it.
fn premises(manifest: &FlowManifest, options: &FuzzOptions, report: &FuzzReport) -> Vec<Value> {
    let assumed = assumed_value(manifest, options, Some(report));
    assumed
        .as_array()
        .into_iter()
        .flatten()
        .map(|entry| {
            let name = entry["name"].as_str().unwrap_or_default();
            let genuine = entry["genuine"].as_bool().unwrap_or(false);
            let in_flow = entry["in_flow"].as_bool().unwrap_or(false);
            let mut note = String::new();
            if genuine {
                note.push_str(
                    "GENUINE: the check exhibits two normal forms for one input, so this \
                     premise is known to be false and every kill under it is vacuous; ",
                );
            }
            note.push_str(if in_flow {
                "already in FLOW.toml's [spec] assume_joined"
            } else {
                "add it to FLOW.toml's [spec] assume_joined, or kink counts no kill on this \
                 definition (baseline-findings)"
            });
            json!({"name": name, "genuine": genuine, "in_flow": in_flow, "note": note})
        })
        .collect()
}

/// Whether the `program` of a kill job's fuzz document (null without a witness) refutes the
/// expectation of a mutation expected to survive: kink's own run confirmed the kill
/// (`confirmed`), and the kill rests on no premise `FLOW.toml`'s `[spec] assume_joined` lacks
/// (every `premises` entry `in_flow`). A witness that `--no-confirm` left unconfirmed, or whose
/// kill needs a premise the flow does not state, is a candidate: the corpus as it stands has not
/// been shown to distinguish the mutant, so the claim is neither refuted nor confirmed.
#[must_use]
pub fn refutes_survival(program: &Value) -> bool {
    program["confirmed"] == true
        && program["premises"]
            .as_array()
            .into_iter()
            .flatten()
            .all(|premise| premise["in_flow"] != false)
}

// ---------------------------------------------------------------------------------------------
// Guards: definition exclusions, assembly, the last run's facts
// ---------------------------------------------------------------------------------------------

/// The definition exclusion of one side, if any, as kink-campaign's runner reads it for every
/// run on that side (kink-native `DefinitionExclusions::definition_exclusion`, which a rule the
/// short-circuit analysis flags is not): from the side's compiled KORE loaded for `module` on
/// this thread, with the load, which the witness filter keeps ([`crate::fuzz_filter`]). The load's
/// backend asks Z3 with `solver`, the options of the command's runs (`[budget]
/// smt_resource_limit`), so the filter judges a witness under the budget its runs had.
fn side_exclusion(
    side: &ValidatedDefinition,
    module: &str,
    solver: k_rust::backend::BackendOptions,
) -> Result<(ValidatedLoad, Option<(Exclusion, String)>), String> {
    let load = DefinitionExclusions::load_validated(side, module, solver)?;
    let excluded = load.exclusions.definition_exclusion().map(|exclusion| {
        // What makes it hold, as every kink-flow document says it (`crate::exclusion`).
        let detail = crate::exclusion::detail(
            &load.exclusions,
            exclusion,
            &crate::evidence::EndReader::of(side),
        );
        (exclusion, detail)
    });
    Ok((load, excluded))
}

/// What kink's own assembly makes of a witness's input, against each side's initial
/// configuration in the witness (design 3.2.5).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssemblyCheck {
    /// Each side's initial configuration is kink's assembly of the program.
    Match,
    /// These sides' initial configurations (`baseline`, `mutant`) are not kink's assembly of the
    /// program, or do not parse as KORE.
    Mismatch { sides: Vec<String>, detail: String },
    /// kink refuses the program's input: its admission stage's reason and detail.
    Refused { reason: String, detail: String },
}

impl AssemblyCheck {
    /// `{status, ...}` for the document.
    #[must_use]
    pub fn value(&self) -> Value {
        match self {
            Self::Match => json!({"status": "match"}),
            Self::Mismatch { sides, detail } => {
                json!({"status": "mismatch", "sides": sides, "detail": detail})
            }
            Self::Refused { reason, detail } => {
                json!({"status": "refused", "reason": reason, "detail": detail})
            }
        }
    }
}

/// The per-candidate assembly check (design 3.2.5): kink assembles `program` (with
/// `instantiated`, its instantiated inputs) exactly as it assembles a `[[program]]` of the
/// corpus, from the baseline's grammar for both sides of every test, with the program's start
/// sort (kink's default when it has none) and variables, then its concrete-state check, input
/// gate and value check (`InputSession::test_case`); each
/// side's `initial_configuration` in `case`, parsed as KORE, must equal that configuration.
/// A difference means the campaign judged another input than the one kink would run, so the
/// case is no witness for kink (`assembly-mismatch`). The hole values are covered, since the
/// check reads the instantiated program.
pub fn check_assembly(
    inputs: &mut InputSession<'_>,
    program: &Program,
    instantiated: &CaseInputs,
    case: &WitnessCase,
) -> AssemblyCheck {
    let kink = match inputs.test_case(program, instantiated) {
        Ok(test) => test.initial_state,
        Err(refusal) => {
            return AssemblyCheck::Refused {
                reason: refusal.reason,
                detail: format!("{}: {}", refusal.stage, refusal.detail),
            };
        }
    };
    let kink_digest = digest_hex(kink.to_string().as_bytes());
    let mut sides = Vec::new();
    let mut details = Vec::new();
    for side in &case.sides {
        let role = role_name(side.role);
        match parse_pattern(&side.initial_configuration) {
            Ok(pattern) if pattern == kink => {}
            Ok(_) => {
                sides.push(role.to_owned());
                details.push(format!(
                    "the {role}'s initial configuration (sha256 {}) is not kink's assembly of \
                     the program (sha256 {kink_digest})",
                    digest_hex(side.initial_configuration.as_bytes())
                ));
            }
            Err(error) => {
                sides.push(role.to_owned());
                details.push(format!(
                    "the {role}'s initial configuration does not parse as KORE: {error}"
                ));
            }
        }
    }
    if sides.is_empty() {
        AssemblyCheck::Match
    } else {
        AssemblyCheck::Mismatch {
            sides,
            detail: details.join("; "),
        }
    }
}

/// The stream defaults kink assembles a program with (kink-corpus `assemble_input_with`): `$IO`
/// off and `$STDIN` empty, each as K text.
const KINK_STREAM_DEFAULTS: [(&str, &str); 2] = [("IO", "\"off\""), ("STDIN", "\"\"")];

/// The configuration variables the campaign assembles the template with, in kink's binding
/// order: the template's, then kink's stream defaults for each stream variable the definition
/// declares and the template does not bind. k-rust-fuzz's own default binds `$STDIN` to krun's
/// buffered empty input (`"\n"`) where kink binds `""`, so without these bindings every template
/// on a definition with stream cells assembled differently from kink's program and the job was
/// refused (`template-assembly-differs`; INT9 review K2). The order matters as much as the
/// values: the initial configuration lists the bindings in the order they are made.
fn campaign_variables(spec: &AdmittedSpec, instance: &Instance) -> Vec<(String, String)> {
    let declared = &spec.compiled.artifacts().configuration_variables;
    let mut variables = instance.variables.clone();
    for (name, text) in KINK_STREAM_DEFAULTS {
        let bound = variables
            .iter()
            .any(|(bound, _)| bound.strip_prefix('$').unwrap_or(bound) == name);
        if declared.contains_key(name) && !bound {
            variables.push((name.to_owned(), text.to_owned()));
        }
    }
    variables
}

/// The template as a `[[program]]` of the flow (its text inline): what kink would assemble and
/// digest for it.
fn template_program(template: &Template, instance: &Instance) -> Program {
    Program {
        id: template.id.clone(),
        source: instance.text.clone().map(ProgramSource::Text),
        start_sort: instance.written_start_sort.clone(),
        variables: instance.variables.clone(),
        inputs: Table::new(),
        case: None,
        case_file: None,
        expect: None,
        stop_count: instance.stop_count,
    }
}

/// The inputs kink reads for the template's `[[program]]` ([`template_program`]).
fn template_inputs(instance: &Instance) -> CaseInputs {
    CaseInputs {
        text: instance.text.clone(),
        typed: Vec::new(),
        bound: None,
        defaults: Vec::new(),
    }
}

fn warning(kind: &str, detail: impl Into<String>) -> Value {
    json!({"kind": kind, "detail": detail.into()})
}

fn push_warning(document: &mut Value, warning: Value) {
    if let Some(warnings) = document["warnings"].as_array_mut() {
        warnings.push(warning);
    }
}

/// What the last `run` document (`report.json` in the cache directory, read as `report` reads
/// it: this build's, this kink identity's, of the current specification and of the corpus's
/// current programs) says about the template and the mutation: the template program's class
/// (found by its program digest), the mutation's status and its `witnesses`, each suggested as a
/// template; and the warnings these facts give. Nothing is run or written. `mutation` is `None`
/// for a derived flip, which no run document has a row of: only the template's class is read.
///
/// A row's status and `witnesses` are facts about the programs that run judged: a killer is one
/// of them, and a survivor survived exactly them. So the document is current only when its
/// programs are the corpus's, each id with its program digest; otherwise it is stale, as a
/// document of another specification is, and says nothing about the mutation.
#[allow(clippy::too_many_arguments)]
fn last_run(
    manifest: &FlowManifest,
    spec: &AdmittedSpec,
    inputs: &InputSession<'_>,
    options: &FuzzOptions,
    template: &Template,
    instance: &Instance,
    mutation: Option<&str>,
    spelling: &dyn CommandSpelling,
    warnings: &mut Vec<Value>,
) -> Value {
    let (document, found) = crate::report::report_spelled(
        manifest,
        &crate::report::ReportOptions {
            cache: options.cache.clone(),
        },
        spelling,
    );
    if !found {
        return json!({
            "found": false,
            "detail": document["detail"],
        });
    }
    let current = spec_digest(manifest, &spec.loaded.files).to_string();
    if document["spec"]["digest"] != json!(current) {
        warnings.push(warning(
            "stale-run-document",
            format!(
                "the last run document is of another specification (its digest differs): run \
                 `{}` again for the template's class and the mutation's witnesses",
                spelling.verb(Verb::Run)
            ),
        ));
        return json!({"found": true, "current": false});
    }
    // The stop is part of every program's meaning, and the specification's digest leaves it
    // out: a run under another stop (other rules, or other counts) judged other runs.
    if document["stop"] != manifest.stop_value().unwrap_or(Value::Null) {
        warnings.push(warning(
            "stale-run-document",
            format!(
                "the last run document is of another [stop] than FLOW.toml's (its rules or \
                 counts differ), so its classes, statuses and witnesses are of other runs: run \
                 `{}` again for the template's class and the mutation's witnesses",
                spelling.verb(Verb::Run)
            ),
        ));
        return json!({"found": true, "current": false});
    }
    // The corpus's programs as `run` keys them: each id with its program digest, null for a
    // program whose inputs are refused (as its row's).
    let corpus = manifest
        .programs
        .iter()
        .map(|program| {
            let digest = inputs
                .read(program)
                .ok()
                .map(|case| program_digest(program, &case).to_string());
            (program.id.clone(), digest)
        })
        .collect::<BTreeSet<_>>();
    let judged = document["programs"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|row| {
            (
                row["id"].as_str().unwrap_or_default().to_owned(),
                row["digest"].as_str().map(str::to_owned),
            )
        })
        .collect::<BTreeSet<_>>();
    if corpus != judged {
        type Keyed = BTreeSet<(String, Option<String>)>;
        let names = |set: &Keyed, other: &Keyed| {
            set.difference(other)
                .map(|(id, _)| id.clone())
                .collect::<BTreeSet<_>>()
        };
        let (now, then) = (names(&corpus, &judged), names(&judged, &corpus));
        let mut changes = Vec::new();
        let changed = now.intersection(&then).cloned().collect::<Vec<_>>();
        let added = now.difference(&then).cloned().collect::<Vec<_>>();
        let removed = then.difference(&now).cloned().collect::<Vec<_>>();
        for (what, ids) in [("added", added), ("removed", removed), ("changed", changed)] {
            if !ids.is_empty() {
                changes.push(format!("{what} {}", ids.join(", ")));
            }
        }
        warnings.push(warning(
            "stale-run-document",
            format!(
                "the last run document is of other programs than the corpus's ({} since): run \
                 `{}` again for the template's class and the mutation's status and witnesses",
                changes.join("; "),
                spelling.verb(Verb::Run)
            ),
        ));
        return json!({"found": true, "current": false});
    }
    let program = template_program(template, instance);
    let digest = program_digest(&program, &template_inputs(instance)).to_string();
    let rows = document["programs"].as_array().cloned().unwrap_or_default();
    // A row is the template's own program when it has the template's inputs and, under a stop,
    // its count (the program digest leaves the count out): one input under another count is
    // another case.
    let template_count = instance.case_stop(manifest).map(|stop| stop.count.get());
    let row_count = |row: &Value| {
        let stop = &document["stop"];
        row["id"]
            .as_str()
            .and_then(|id| stop["counts"][id].as_u64())
            .or_else(|| stop["count"].as_u64())
    };
    let row = rows
        .iter()
        .find(|row| row["digest"] == json!(digest) && row_count(row) == template_count);
    let template_row = row.map(|row| {
        json!({
            "program": row["id"],
            "class": row["class"],
            "cause": row["cause"],
        })
    });
    if let Some(row) = row
        && row["class"] != "comparable"
    {
        warnings.push(warning(
            "unusable-template",
            format!(
                "the template's own program ({}) is {} in the last run{}: kink compares only \
                 programs that end on a comparable value, so a witness from this template may \
                 be refused for the same reason; prefer a template whose program is comparable",
                row["id"].as_str().unwrap_or("?"),
                row["class"].as_str().unwrap_or("?"),
                row["cause"]
                    .as_str()
                    .map(|cause| format!(" ({cause})"))
                    .unwrap_or_default(),
            ),
        ));
    }
    // A derived flip has no row in any run document: the template's class is all it says.
    let Some(mutation) = mutation else {
        return json!({
            "found": true,
            "current": true,
            "template": template_row,
            "mutation": null,
        });
    };
    let mutations = document["mutations"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let Some(entry) = mutations.iter().find(|entry| entry["id"] == mutation) else {
        // The last run judged another list (or selected other mutations): it says nothing of
        // this mutation, so no witness is checked and no up-front warning can be given.
        warnings.push(warning(
            "last-run-without-mutation",
            format!(
                "the last run document has no row for this mutation (it judged another list or \
                 selection), so neither its status nor its witnesses are known here: run `{}` \
                 first",
                spelling.command(Verb::Run)
            ),
        ));
        return json!({
            "found": true,
            "current": true,
            "template": template_row,
            "mutation": null,
        });
    };
    // Null when the last run had no compiled edit for the row (it compiled no mutant for it and
    // the outcome cache kept none), so nothing says which programs witness it.
    let known = !entry["witnesses"].is_null();
    let witnesses = entry["witnesses"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .map(str::to_owned)
        .collect::<Vec<_>>();
    // The edit is not site-local (an equation's left-hand side or attribute, a declaration, ...):
    // every program is a witness, whatever its coverage reaches, since a changed pattern can match
    // terms no baseline run tried.
    let global = known && entry["witnesses_global"] == true;
    let template_id = row.and_then(|row| row["id"].as_str());
    let status = entry["status"].as_str().unwrap_or_default();
    if status == "unknown" && entry["reason"] == "stack-stop" {
        // Every program the last run left undecided stopped for lack of native stack on the
        // mutant: a case whose run recurses the same way judges nothing either.
        warnings.push(warning(
            "stack-stop",
            format!(
                "the last run left this mutation unknown with reason stack-stop: {}; a case that \
                 stops for lack of stack is no witness either, so the search ends after {} such \
                 cases in a row (--stack-stops)",
                crate::report::action_spelled(status, Some("stack-stop"), spelling)
                    .unwrap_or_default(),
                options.stack_stops,
            ),
        ));
    }
    if status == "unknown" && entry["reason"] == crate::report::WORK_BUDGET_REASON {
        // Every program the last run left undecided was cut by kink's work budget on the mutant
        // (FB45-KINK): a case whose run does that much work is no witness either. The fuzz's own
        // runs are not bounded by the budget, so a case that recurses without end stops for lack
        // of native stack, and the search ends after `--stack-stops` of them in a row.
        warnings.push(warning(
            crate::report::WORK_BUDGET_REASON,
            format!(
                "the last run left this mutation unknown with reason {}: {}; a case on which \
                 the mutant does not end is no witness either, and one that recurses without \
                 end stops for lack of stack, so the search ends after {} such cases in a row \
                 (--stack-stops)",
                crate::report::WORK_BUDGET_REASON,
                crate::report::action_spelled(
                    status,
                    Some(crate::report::WORK_BUDGET_REASON),
                    spelling
                )
                .unwrap_or_default(),
                options.stack_stops,
            ),
        ));
    }
    if status == "unknown" && entry["reason"] == crate::report::OPEN_APPLICATION_REASON {
        // Every program the last run left undecided holds an application of an edited function
        // that no equation of the mutant reduces: a case whose run reaches it is undecided too.
        warnings.push(warning(
            "open-application",
            format!(
                "the last run left this mutation unknown with reason open-application: {}; a \
                 case whose mutant run ends holding such an application is no witness either, so \
                 the search ends after {} such cases in a row (--open-stops)",
                crate::report::action_spelled(
                    status,
                    Some(crate::report::OPEN_APPLICATION_REASON),
                    spelling
                )
                .unwrap_or_default(),
                options.open_stops,
            ),
        ));
    }
    if status == "killed" {
        warnings.push(warning(
            "already-killed",
            format!(
                "the last run already killed this mutation (killer {})",
                entry["killer"].as_str().unwrap_or("?")
            ),
        ));
    } else if !known {
        if crate::report::SURVIVOR_STATUSES.contains(&status) {
            warnings.push(warning(
                "witnesses-not-computed",
                format!(
                    "the last run neither compiled this mutation's mutant nor found its compiled \
                     edit in the outcome cache (reason {}), so it names no program whose coverage \
                     witnesses the edit",
                    entry["reason"].as_str().unwrap_or("none")
                ),
            ));
        }
    } else if witnesses.is_empty() {
        if crate::report::SURVIVOR_STATUSES.contains(&status) {
            warnings.push(warning(
                "no-witness",
                "in the last run no comparable program's coverage witnesses the mutant's \
                 compiled edit: a template whose run matches or applies the edited rule is \
                 needed, or holes that make the run do so",
            ));
        }
    } else if global {
        // The warning's advice is to build on a program that reaches an edited rule: a template
        // whose own program's baseline coverage matches one already does.
        let reaches = template_id.is_some_and(|id| {
            template_reaches(manifest, spec, inputs, options, id, &entry["rules"])
        });
        if crate::report::SURVIVOR_STATUSES.contains(&status) && !reaches {
            warnings.push(warning(
                "global-witnesses",
                "the mutant's compiled edit is not confined to what its edited rules do once \
                 they apply (it edits an equation's left-hand side or an attribute, removes or \
                 inserts an equation, or changes a declaration), so in the last run every \
                 program is a witness by default, not because its coverage reaches an edited \
                 rule: a changed pattern can match terms no baseline run tried, so the template \
                 is a witness whatever it reaches; prefer one whose program reaches the edited \
                 rule, one that the `coverage` document lists in that rule's `matched_by`",
            ));
        }
    } else if template_id.is_none_or(|id| !witnesses.iter().any(|r| r == id)) {
        warnings.push(warning(
            "template-not-a-witness",
            format!(
                "the template's program is not among the programs whose coverage witnesses the \
                 mutant's compiled edit in the last run ({}); a template built on one of them is \
                 suggested",
                witnesses.join(", ")
            ),
        ));
    }
    let suggested = witnesses
        .iter()
        .map(|id| {
            json!({
                "program": id,
                "template": format!(
                    "[[template]]\nid = \"{id}-holes\"\nprogram = \"{id}\"\n# mark literals \
                     with [[template.hole]] tables\n"
                ),
            })
        })
        .collect::<Vec<_>>();
    json!({
        "found": true,
        "current": true,
        "template": template_row,
        "mutation": {
            "status": entry["status"],
            "reason": entry["reason"],
            "witnesses": if known { json!(witnesses) } else { Value::Null },
            "witnesses_global": if known { json!(global) } else { Value::Null },
        },
        "suggested_templates": suggested,
    })
}

// ---------------------------------------------------------------------------------------------
// Jobs: kill, matched, fired, pattern
// ---------------------------------------------------------------------------------------------

/// The job of one `kink-flow fuzz` command.
#[derive(Clone, Copy, Debug)]
pub enum FuzzJob<'a> {
    /// `--kill MUTATION --mutations MUTATIONS.toml`: hole values whose program kills the mutation.
    /// `path` is where the list was read from, which a next step that runs `run` names, so that
    /// the run judges this list; `None` for a list that is no file. `flip` says the mutation is a
    /// condition flip the front end derives ([`fuzz_derived`]): `run` never judges it, so a next
    /// step names `coverage`, whose flips family runs its kill search, and the last run document
    /// has no row for it.
    Kill {
        list: &'a MutationList,
        mutation: &'a str,
        path: Option<&'a Path>,
        flip: bool,
    },
    /// `--matched RULE` (`fired` false) or `--fired RULE`: hole values whose program's all-paths
    /// baseline run is comparable and matches the rule (begins to decide its condition: a rule's
    /// `matched_by`, k-rust `matched`), or with `fired` takes the rule's step on some path
    /// (`fired_by`, k-rust `committed`).
    Rule { rule: &'a str, fired: bool },
    /// `--pattern ID --patterns PATTERNS.toml`: hole values whose program reaches a configuration
    /// matching the pattern (a `hit` of kink's `query`).
    Pattern { list: &'a PatternList, id: &'a str },
    /// `--refuted RULE`: hole values whose program's all-paths baseline run is comparable and
    /// refutes the rule's condition on some entry, covering the requirement
    /// `requirement:<RULE's name>:refuted` (as [`Self::Cover`] of that id).
    Refuted { rule: &'a str },
    /// `--cover ITEM`: hole values whose program's all-paths baseline run is comparable and
    /// covers the coverage obligation `ITEM` (its id in the `coverage` document: a requirement,
    /// a production or field value of the syntax family, a rule or heating rule;
    /// [`crate::fuzz_goal`]).
    Cover { item: &'a str },
}

impl FuzzJob<'_> {
    const fn kind(&self) -> &'static str {
        match self {
            Self::Kill { .. } => "kill",
            Self::Rule { fired: false, .. } => "matched",
            Self::Rule { fired: true, .. } => "fired",
            Self::Pattern { .. } => "pattern",
            Self::Refuted { .. } => "refuted",
            Self::Cover { .. } => "cover",
        }
    }

    /// Whether the job's goal is a coverage obligation ([`crate::fuzz_goal`]).
    const fn covers(&self) -> bool {
        matches!(self, Self::Refuted { .. } | Self::Cover { .. })
    }
}

/// Whether the corpus program `id`'s current result record (its baseline run, read from the cache
/// without running anything) is `comparable` and matched a sentence of `rules`, a run row's
/// edited rules (`{module, index, ...}`): its coverage's `sentences`, k-rust's `matched`, or a
/// sentence whose condition its run entered ([`crate::guards::entered_sentences`]), the predicate
/// the `coverage` document's `matched_by` lists, which counts comparable records only.
/// False without a record or rules, or for a record of another class.
fn template_reaches(
    manifest: &FlowManifest,
    spec: &AdmittedSpec,
    inputs: &InputSession<'_>,
    options: &FuzzOptions,
    id: &str,
    rules: &Value,
) -> bool {
    let Some(program) = manifest.programs.iter().find(|program| program.id == id) else {
        return false;
    };
    let edited = rules
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|rule| Some((rule["module"].as_str()?, rule["index"].as_u64()?)))
        .collect::<BTreeSet<_>>();
    if edited.is_empty() {
        return false;
    }
    let cache = crate::results::cache_directory(manifest, options.cache.as_deref());
    let execution = crate::digest::execution_digest(manifest, spec);
    let Some(record) = inputs.read(program).ok().and_then(|case| {
        crate::results::current_record(manifest, execution, program, &case, &cache)
    }) else {
        return false;
    };
    if record["class"] != crate::results::ResultClass::Comparable.as_str() {
        return false;
    }
    record["coverage"]["sentences"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|sentence| sentence["module"].as_str().zip(sentence["index"].as_u64()))
        .chain(crate::guards::entered_sentences(&record))
        .any(|at| edited.contains(&at))
}

/// `kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID --kill MUTATION --mutations
/// MUTATIONS.toml`: the document and whether the job was done (a witness, or none within the
/// budget or the time limit); `false` when an input, the template or the mutation is refused, the
/// campaign is `not-comparable`, or a run failed.
pub fn kill(
    manifest: &FlowManifest,
    templates: &TemplateList,
    template: &str,
    list: &MutationList,
    mutation: &str,
    options: &FuzzOptions,
) -> (Value, bool) {
    fuzz_job(
        manifest,
        templates,
        template,
        FuzzJob::Kill {
            list,
            mutation,
            path: None,
            flip: false,
        },
        options,
    )
}

/// The document of one job ([`kill`] for the kill job) and whether the job was done.
pub fn fuzz_job(
    manifest: &FlowManifest,
    templates: &TemplateList,
    template: &str,
    job: FuzzJob<'_>,
    options: &FuzzOptions,
) -> (Value, bool) {
    fuzz_front(
        manifest,
        templates,
        template,
        job,
        options,
        &FrontEnd::default(),
    )
}

/// A kill job of the condition flip `mutation` the front end derives ([`FrontEnd::derived`],
/// [`crate::flips`]), named where no list given holds the id (`list` is the front end's list that
/// does not): an admitted flip is fuzzed as a kill job of its edits, as `coverage` runs it; a flip
/// the front end's judge refused is refused at stage `mutation` with the judge's reason and next
/// step, since no mutant stands for it; an id that is no derived flip either is refused as an
/// unknown mutation, naming what the list and the derived flips hold, and why the flip is not
/// generated where the list's `not_generated` names it. A flip that changes only sentences outside
/// the coverage scope is not generated ([`crate::flips::scoped`]), so it is refused as unknown
/// once the specification is admitted ([`fuzz_front`]).
pub fn fuzz_derived(
    manifest: &FlowManifest,
    templates: &TemplateList,
    template: &str,
    mutation: &str,
    list: Option<&Path>,
    options: &FuzzOptions,
    front: &FrontEnd<'_>,
) -> (Value, bool) {
    let derived = match front.derived {
        crate::flips::Derived::Flips(derived) => Ok(derived),
        crate::flips::Derived::None(reason) => Err(reason),
    };
    let entry = derived
        .ok()
        .and_then(|derived| derived.entries.iter().find(|entry| entry.id == mutation));
    let refuse = |refusal: Refusal, status: Option<&str>, action: String| {
        let mut document = document();
        document["job"] = json!({
            "kind": "kill",
            "outcome": "refused",
            "path_mode": match options.paths {
                PathMode::AllPaths => "all-paths",
                PathMode::OnePath => "one-path",
            },
            "mutation": mutation,
            "flip": entry.is_some(),
            "expect": null,
        });
        if let Some(status) = status {
            document["job"]["status"] = json!(status);
            document["job"]["reason"] = json!(refusal.reason);
            document["job"]["detail"] = json!(refusal.detail);
        }
        document["job"]["refusal"] = refusal.value();
        document["stopped"] = json!("refused");
        document["action"] = json!(action);
        (document, false)
    };
    let Some(entry) = entry else {
        let listed = list.map(|path| match MutationList::read(path) {
            Ok(read) => format!(
                "no mutation of {} has this id ({} mutation{})",
                path.display(),
                read.mutations.len(),
                if read.mutations.len() == 1 { "" } else { "s" }
            ),
            Err(_) => format!("{} does not decode", path.display()),
        });
        let flips = match derived {
            Ok(derived) => {
                let mut flips = format!(
                    "no condition flip the front end derives has this id ({} flip{})",
                    derived.entries.len(),
                    if derived.entries.len() == 1 { "" } else { "s" }
                );
                if let Some(not) = derived
                    .not_generated
                    .iter()
                    .find(|not| not["id"] == mutation)
                {
                    flips.push_str(&format!(
                        ": it is not generated ({}): {}",
                        not["reason"].as_str().unwrap_or_default(),
                        not["detail"].as_str().unwrap_or_default()
                    ));
                }
                flips
            }
            Err(reason) => format!("no flip has this id: {reason}"),
        };
        let detail = listed.map_or_else(|| flips.clone(), |listed| format!("{listed}; {flips}"));
        return refuse(
            Refusal::new("mutation", "unknown-mutation", detail),
            None,
            format!(
                "name a mutation of the list (--mutations names another), or a flip `{}` lists \
                 under its flips family",
                front.spelling.command(Verb::Coverage)
            ),
        );
    };
    match &entry.judged {
        crate::flips::Judged::Refused {
            reason,
            next,
            detail,
        } => refuse(
            Refusal::new("mutation", reason.clone(), detail.clone()),
            Some(crate::flips::REFUSED),
            format!(
                "no mutant stands for a refused flip (`{}` lists it refused){}",
                front.spelling.command(Verb::Coverage),
                next.as_ref()
                    .map(|next| format!(": {next}"))
                    .unwrap_or_default()
            ),
        ),
        crate::flips::Judged::Admitted { .. } => {
            let list = MutationList {
                mutations: entry.mutation().into_iter().collect(),
            };
            fuzz_front(
                manifest,
                templates,
                template,
                FuzzJob::Kill {
                    list: &list,
                    mutation,
                    path: None,
                    flip: true,
                },
                options,
                front,
            )
        }
    }
}

/// [`fuzz_job`] for a front end ([`FrontEnd`]): next steps take its spelling, and a kill job of
/// a mutation it refused ([`FrontEnd::refused`]) is refused as one of a mutation that does not
/// resolve, with the front end's reason.
#[allow(clippy::too_many_lines)]
pub fn fuzz_front(
    manifest: &FlowManifest,
    templates: &TemplateList,
    template: &str,
    job: FuzzJob<'_>,
    options: &FuzzOptions,
    front: &FrontEnd<'_>,
) -> (Value, bool) {
    // A kill job's next steps that run `run` name its list and its cache: a run of another list
    // would not judge the mutation, and one of another cache writes a document fuzz never reads.
    // A flip's next steps that would run `run` run `coverage`, the verb that judges flips.
    let list_run = match job {
        FuzzJob::Kill { flip: true, .. } => Some(ListRun {
            inner: front.spelling,
            run: front.spelling.command(Verb::Coverage),
        }),
        FuzzJob::Kill {
            path: Some(path), ..
        } => Some(ListRun {
            inner: front.spelling,
            run: front.spelling.run_list(path, options.cache.as_deref()),
        }),
        _ => None,
    };
    let spelling: &dyn CommandSpelling = match &list_run {
        Some(list_run) => list_run,
        None => front.spelling,
    };
    let mut document = document();
    document["job"] = json!({
        "kind": job.kind(),
        "outcome": "pending",
        "path_mode": match options.paths {
            PathMode::AllPaths => "all-paths",
            PathMode::OnePath => "one-path",
        },
    });
    if let FuzzJob::Kill { mutation, flip, .. } = job {
        document["job"]["mutation"] = json!(mutation);
        document["job"]["flip"] = json!(flip);
        document["job"]["expect"] = Value::Null;
    }
    // The corpus's stop and observation declaration, as every kink-flow document names them.
    if let Some(stop) = manifest.stop_value() {
        document["stop"] = stop;
    }
    if let Some(observe) = manifest.observe_value() {
        document["observe"] = observe;
    }
    if let Some((refusal, action)) = corpus_refusal(manifest, &job) {
        document["spec"] = refusal.value();
        document["stopped"] = json!("refused");
        document["action"] = json!(action);
        return (document, false);
    }
    if manifest.observe.is_some() {
        // Only a kill job compares two definitions, and it is refused above.
        document["job"]["observe"] = json!({"ignored": if matches!(job, FuzzJob::Pattern { .. }) {
            OBSERVE_IGNORED_PATTERN
        } else {
            OBSERVE_IGNORED
        }});
    }
    // A pattern target reads no data end, so the campaign takes no assumed name (k-rust-fuzz
    // refuses names on such a target), not even the flow's.
    let reads_data = !matches!(job, FuzzJob::Pattern { .. });
    document["assumed"] = if reads_data {
        assumed_value(manifest, options, None)
    } else {
        json!([])
    };
    let refuse = |mut document: Value, refusal: Refusal, action: &str| {
        document["job"]["outcome"] = json!("refused");
        document["job"]["refusal"] = refusal.value();
        document["stopped"] = json!("refused");
        document["action"] = json!(action);
        (document, false)
    };
    let Some(template) = templates.get(template) else {
        let refusal = Refusal::new(
            "template",
            "unknown-template",
            format!("no template {template:?}"),
        );
        return refuse(document, refusal, "name a template of TEMPLATES.toml");
    };
    let mutation_entry = match job {
        FuzzJob::Kill { list, mutation, .. } => {
            let Some(entry) = list.mutations.iter().find(|m| m.id == mutation) else {
                let refusal = Refusal::new(
                    "mutation",
                    "unknown-mutation",
                    format!("no mutation {mutation:?}"),
                );
                return refuse(document, refusal, "name a mutation of MUTATIONS.toml");
            };
            // The verdict the mutation expects: a witness of one expected to survive refutes it.
            document["job"]["expect"] = json!(entry.expect.map(Expect::as_str));
            Some(entry)
        }
        FuzzJob::Rule { .. }
        | FuzzJob::Pattern { .. }
        | FuzzJob::Refuted { .. }
        | FuzzJob::Cover { .. } => None,
    };
    let expects_survival =
        mutation_entry.is_some_and(|entry| entry.expect == Some(Expect::Survive));
    let pattern_entry = match job {
        FuzzJob::Pattern { list, id } => {
            let Some(entry) = list.patterns.iter().find(|p| p.id == id) else {
                let refusal =
                    Refusal::new("pattern", "unknown-pattern", format!("no pattern {id:?}"));
                return refuse(document, refusal, "name a pattern of PATTERNS.toml");
            };
            Some(entry)
        }
        FuzzJob::Kill { .. }
        | FuzzJob::Rule { .. }
        | FuzzJob::Refuted { .. }
        | FuzzJob::Cover { .. } => None,
    };
    let (record, admitted) = admit_spec(manifest);
    let Some((spec, mut inputs)) = admitted else {
        let refusal = record.refusal.as_ref().map_or_else(
            || Refusal::new("spec", "refused", ""),
            |r| Refusal {
                stage: "spec",
                reason: r.reason.clone(),
                detail: format!("{}: {}", r.stage, r.detail),
            },
        );
        document["spec"] = refusal.value();
        document["stopped"] = json!("refused");
        document["action"] = json!(format!(
            "fix the specification: `{}` gives the same refusal",
            spelling.verb(Verb::Check)
        ));
        return (document, false);
    };
    document["spec"] = json!({
        "outcome": "admitted",
        "assume_joined": manifest.spec.assume_joined,
        "has_data": spec.data.has_data(),
        "unnamed_findings": spec.data.unnamed().iter().map(|f| f.value()).collect::<Vec<_>>(),
    });
    // A front end's flip wholly outside the coverage scope is no derived flip: `coverage` moves
    // it to `not_generated` before anything reads the list, and so does a kill job of it.
    if let (
        FuzzJob::Kill {
            mutation,
            flip: true,
            ..
        },
        crate::flips::Derived::Flips(derived),
    ) = (job, front.derived)
        && let Some(not) = derived
            .entries
            .iter()
            .find(|entry| entry.id == mutation)
            .and_then(|entry| {
                let scope = crate::coverage::scope::Scope::of(&spec, manifest, front.invariants);
                crate::flips::outside_scope(entry, &spec, &scope)
            })
    {
        let refusal = Refusal::new(
            "mutation",
            "unknown-mutation",
            format!(
                "no condition flip the front end derives has this id: it is not generated ({}): \
                 {}",
                not["reason"].as_str().unwrap_or_default(),
                not["detail"].as_str().unwrap_or_default()
            ),
        );
        document["job"]["flip"] = json!(false);
        return refuse(
            document,
            refusal,
            &format!(
                "name a flip `{}` lists under its flips family",
                front.spelling.command(Verb::Coverage)
            ),
        );
    }
    let instance = match instance(template, templates, manifest, &inputs, &spec) {
        Ok(instance) => instance,
        Err(refusal) => return refuse(document, refusal, "fix the template"),
    };
    let mut inputs = inputs.session(&spec);
    document["template"] = json!({
        "id": template.id,
        "source": match &template.source {
            TemplateSource::Program(id) => json!({"program": id}),
            TemplateSource::File(file) => json!({"file": file}),
            TemplateSource::Text(_) => json!({"text": true}),
        },
        "start_sort": instance.start_sort,
        "start_sort_source": instance.start_sort_source,
        "variables": instance
            .variables
            .iter()
            .map(|(name, text)| json!({"name": name, "text": text}))
            .collect::<Vec<_>>(),
        "holes": serde_json::to_value(&template.holes).expect("hole declarations encode"),
        "stop_count": instance.case_stop(manifest).map(|stop| stop.count.get()),
        "last_run": null,
    });
    let mut warnings = Vec::new();
    if options.time_limit_ms.is_some() {
        warnings.push(warning(
            "time-limit-scope",
            "--time-limit-ms bounds the campaign's run only: kink's admission, the mutant's \
             preparation, the definition exclusions and the campaign's setup (k-rust-fuzz \
             Campaign::new: both grammars and backends, and both definitions' full critical-pair \
             checks) run before the watchdog starts, and the confirmation by kink's own code runs \
             after it (kink's `time_ms` bounds each of its runs); no time limit bounds them",
        ));
    }
    if let FuzzJob::Kill { mutation, flip, .. } = job {
        // The last run document is `run`'s, which judges no flip: its spelling, not the flip's.
        document["template"]["last_run"] = last_run(
            manifest,
            &spec,
            &inputs,
            options,
            template,
            &instance,
            (!flip).then_some(mutation),
            if flip { front.spelling } else { spelling },
            &mut warnings,
        );
    }
    if expects_survival {
        warnings.push(warning(
            "expected-to-survive",
            "the mutation states expect = \"survive\": no program of the corpus should \
             distinguish its mutant from the specification. This search is an attempt to refute \
             that claim: a witness kink confirms, needing no premise FLOW.toml lacks, is a \
             finding (exit status 1), a program on which what the edit changes is observable",
        ));
    }
    document["warnings"] = json!(warnings);

    // The job's own target, resolved against the baseline before any campaign; a rule job's
    // authored rule is the one whose `coverage` entry its confirmation reads.
    let mut rule_at = None;
    let mut goal_item = None;
    let kind = match job {
        FuzzJob::Kill { .. } => None,
        FuzzJob::Refuted { .. } | FuzzJob::Cover { .. } => {
            let goal = match job {
                FuzzJob::Refuted { rule } => match resolve_rule(manifest, &spec, rule) {
                    Ok(target) => {
                        document["job"]["rule"] = target.value();
                        crate::fuzz_goal::refuted_item(
                            &spec,
                            &record,
                            manifest,
                            front,
                            &target.at.at,
                        )
                    }
                    Err(refusal) => {
                        return refuse(
                            document,
                            refusal,
                            "name one authored rewrite rule of the specification: FILE:LINE (a \
                             line of the rule), its label (MODULE.x when the bare label is \
                             ambiguous), or its 64-hex id (the refusal's detail lists the rules \
                             nearest the reference, with their ids, when it finds any)",
                        );
                    }
                },
                FuzzJob::Cover { item } => {
                    crate::fuzz_goal::resolve(&spec, &record, manifest, front, item)
                }
                _ => unreachable!("a coverage job"),
            };
            match goal {
                Ok(goal) => {
                    document["job"]["item"] = goal.value.clone();
                    goal_item = Some(goal.item.clone());
                    Some(TargetKind::Coverage(CoverageTarget { facts: goal.facts }))
                }
                Err((reason, detail)) => {
                    return refuse(
                        document,
                        Refusal::new("item", reason, detail),
                        &format!(
                            "name an obligation of `{}` by its id (a target's `item`): a \
                             requirement, a production or field value, a rule or a heating rule",
                            spelling.verb(Verb::Coverage)
                        ),
                    );
                }
            }
        }
        FuzzJob::Rule { rule, fired } => match resolve_rule(manifest, &spec, rule) {
            Ok(target) => {
                document["job"]["rule"] = target.value();
                rule_at = Some(target.at.at.clone());
                Some(TargetKind::Rule(RuleTarget {
                    rule: RuleRef::UniqueId(target.id),
                    mode: if fired {
                        RuleMode::Covered
                    } else {
                        RuleMode::ConditionReached
                    },
                }))
            }
            Err(refusal) => {
                return refuse(
                    document,
                    refusal,
                    "name one authored rewrite rule of the specification: FILE:LINE (a line of the \
                     rule), its label (MODULE.x when the bare label is ambiguous), or its 64-hex \
                     id (the refusal's detail lists the rules nearest the reference, with their \
                     ids, when it finds any)",
                );
            }
        },
        FuzzJob::Pattern { .. } => {
            let entry = pattern_entry.expect("a pattern job has its entry");
            match lower_pattern(manifest, &spec, &entry.pattern) {
                Ok(kore) => {
                    document["job"]["pattern"] =
                        json!({"id": entry.id, "text": entry.pattern, "kore": kore});
                    Some(TargetKind::Pattern(PatternTarget {
                        pattern: entry.pattern.clone(),
                        at: PatternAt::AnyState,
                    }))
                }
                Err(refusal) => {
                    document["job"]["pattern"] = json!({"id": entry.id, "text": entry.pattern});
                    return refuse(
                        document,
                        refusal,
                        "fix the pattern: kink's `query` refuses it the same way (invalid-pattern)",
                    );
                }
            }
        }
    };

    // The mutant, exactly as kink's runner prepares it for every test of the mutation.
    let mutant = match mutation_entry {
        None => None,
        Some(mutation_entry) => {
            let resolution = match front.refused.get(&mutation_entry.id) {
                Some(refusal) => Err(refusal.clone()),
                None => resolve(manifest, &spec.loaded, mutation_entry),
            };
            let resolved = match resolution {
                Ok(resolved) => resolved,
                Err(invalid) => {
                    document["job"]["status"] = json!(invalid.reason.status());
                    document["job"]["reason"] = json!(invalid.reason.as_str());
                    document["job"]["detail"] = json!(invalid.to_string());
                    let refusal =
                        Refusal::new("mutation", invalid.reason.as_str(), invalid.to_string());
                    // A front end's refusal names its own next step; the job carries the
                    // reason and the detail, so the action names neither again.
                    let action = match invalid.reason {
                        InvalidReason::External { next, .. } => {
                            format!("fix the mutation: {next}")
                        }
                        _ => "fix the mutation: it does not resolve".to_owned(),
                    };
                    return refuse(
                        document,
                        refusal,
                        &format!(
                            "{action} ({} gives the same status)",
                            spelling.verb(Verb::Run)
                        ),
                    );
                }
            };
            let baseline = spec.validator.baseline();
            // kink27 R5-WEAKENING: a mutation whose edit only weakens the specification, or keeps
            // every axiom, is decided from the edit, as `run` decides it: after the baseline's
            // findings, since the argument reads the baseline's normal forms as a model. No case
            // can change a fact of the axioms, so there is nothing to search for.
            if data_ends(&spec.data) != DataEnds::None
                && let Some(weakening) =
                    kink_patch::ClaimSupport::new(baseline).weakening(baseline, &resolved.patch)
            {
                let value = crate::search::weakening_value(baseline, Some(&weakening));
                let (status, reason) = crate::search::weakening_status(&value);
                document["job"]["status"] = json!(status);
                document["job"]["reason"] = json!(reason);
                document["job"]["weakening"] = value;
                let action = crate::report::action_spelled(status, Some(reason), spelling)
                    .unwrap_or_default();
                return refuse(
                    document,
                    Refusal::new(
                        "mutation",
                        status,
                        format!(
                            "kink decides this mutation from its edit alone: {status} ({reason}), \
                             a fact of the axioms that no case can change"
                        ),
                    ),
                    &format!(
                        "no search can kill this mutation (`{}` gives it the same status): {action}",
                        spelling.verb(Verb::Run)
                    ),
                );
            }
            // An edit of a rule the stop stops before, on a template whose runs end at their first
            // arrival there, builds nothing any end of the template's runs holds when it changes
            // only the step's right-hand side or `ensures` (`check`'s `stop-hides-edit`, read for
            // the template as the only program).
            if manifest.stop.is_some() {
                let mut alone = manifest.clone();
                alone.programs = vec![template_program(template, &instance)];
                if let Some(hides) = crate::check::StopHides::of(&alone, None) {
                    for rule in &resolved.rules {
                        if let Some(label) = hides.hidden(rule.label.as_deref(), &rule.at)
                            && rule.after.is_some()
                        {
                            push_warning(
                                &mut document,
                                warning(
                                    "stop-hides-edit",
                                    format!("{}; {}", hides.detail(&label), hides.next(&label)),
                                ),
                            );
                        }
                    }
                }
            }
            // The names every later step judges under: the flow's and the command line's (the
            // campaign, the filter and the confirmation read the same set; final review N1).
            let admission = MutantAdmission::new(
                baseline,
                &spec.compiled,
                &k_rust::kast::identifier::encode(&manifest.spec.main_module),
                &assumed_names_k(manifest, options),
            )
            .with_solver(manifest.budget.backend_options());
            match claim_free_mutant(
                &spec.validator,
                &spec.compiled,
                &resolved.patch,
                &admission,
                &mut |_| {},
            ) {
                Ok(mutant) => {
                    document["job"]["claims"] = claims_value(baseline, &mutant.claims);
                    document["job"]["mutant_unnamed_findings"] =
                        Value::Array(mutant.data.unnamed().iter().map(|f| f.value()).collect());
                    Some(mutant)
                }
                Err(refusal) => {
                    let status = status_name(refusal.failure.status());
                    let reason = kebab(&format!("{:?}", refusal.failure));
                    document["job"]["status"] = json!(status);
                    document["job"]["reason"] = json!(reason);
                    document["job"]["claims"] = claims_value(baseline, &refusal.claims);
                    document["job"]["inconsistent_pairs"] = Value::Array(
                        refusal
                            .inconsistent_pairs
                            .iter()
                            .map(kink_native::consistency::UnjoinedEquations::value)
                            .collect(),
                    );
                    let detail = format!("kink's mutant preparation: {status} ({reason})");
                    return refuse(
                        document,
                        Refusal::new("mutant", reason, detail),
                        &format!(
                            "no mutant to fuzz: kink refuses this mutation the same way in `{}`",
                            spelling.verb(Verb::Run)
                        ),
                    );
                }
            }
        }
    };

    // kink's definition exclusions (design 3.2.4): one on the mutant makes every test of the
    // mutation unknown in kink's run; one on the baseline makes every program's baseline result
    // unknown (excluded), so no program is comparable and nothing can kill, reach or hit. Either
    // way no witness could be confirmed. A rule or pattern job has the baseline alone.
    let module = k_rust::kast::identifier::encode(&manifest.spec.main_module);
    let mut exclusions = serde_json::Map::new();
    let mut sides_to_check = vec![("baseline", &spec.compiled)];
    if let Some(mutant) = &mutant {
        sides_to_check.push(("mutant", &mutant.side));
    }
    // Each side's load, in side order, kept for the witness filter.
    let mut loads = Vec::new();
    for (role, side) in sides_to_check {
        let mut loaded = side_exclusion(side, &module, manifest.budget.backend_options());
        // The stop names one observation on the baseline (admission checked it there) and on
        // the mutant: a name that labels no rewrite rule of the mutant leaves the stop undefined
        // on it, and `run` does not admit the mutant rather than run it untruncated.
        if role == "mutant"
            && let (Ok((load, _)), Some(stop)) = (loaded.as_mut(), manifest.stop.as_ref())
        {
            let unresolved = match stop.rules().unresolved(&mut load.backend) {
                Ok(unresolved) => unresolved,
                Err(failure) => {
                    return refuse(
                        document,
                        Refusal::new(
                            "mutant",
                            "backend-error",
                            format!(
                                "the mutant's rewrite rules could not be read from its backend, \
                                 so the stop's names could not be checked: {failure:?}"
                            ),
                        ),
                        "report this: kink's mutant backend lists no rules",
                    );
                }
            };
            if !unresolved.is_empty() {
                document["job"]["status"] = json!("not-admitted");
                document["job"]["reason"] = json!("stop-unresolved");
                let detail = format!(
                    "[stop] names {}, which labels no rewrite rule of the mutant: the stop \
                     states no observation of it, so `run` reports the mutation not-admitted \
                     (stop-unresolved) rather than judging it",
                    unresolved
                        .iter()
                        .map(|name| format!("`{name}`"))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                return refuse(
                    document,
                    Refusal::new("mutant", "stop-unresolved", detail),
                    &format!(
                        "no search can kill a mutation the stop does not resolve on (`{}` gives \
                         the same status): edit the rule rather than deleting it or dropping its \
                         label, or stop at another rule",
                        spelling.verb(Verb::Run)
                    ),
                );
            }
        }
        match loaded {
            Ok((load, None)) => {
                exclusions.insert(role.into(), Value::Null);
                if options.filter {
                    loads.push(load);
                }
            }
            Ok((_, Some((exclusion, detail)))) => {
                exclusions.insert(
                    role.into(),
                    json!({"exclusion": exclusion.name(), "detail": detail}),
                );
                document["job"]["exclusions"] = Value::Object(exclusions);
                if mutant.is_some() {
                    // The status and reason kink's `run` gives the mutation.
                    let (status, reason) = if role == "baseline" {
                        ("error", "no-comparable-program")
                    } else {
                        ("unknown", exclusion.name())
                    };
                    document["job"]["status"] = json!(status);
                    document["job"]["reason"] = json!(reason);
                }
                let detail = format!(
                    "the {role}'s definition has kink's definition exclusion {}: {detail}",
                    exclusion.name()
                );
                let run = spelling.verb(Verb::Run);
                let action = if role == "baseline" {
                    format!(
                        "kink excludes every run on this specification, so every program's \
                         result is unknown and no witness could be confirmed (`{run}` gives each \
                         mutation status error, no-comparable-program, and each program the \
                         exclusion as its cause): fix the specification"
                    )
                } else {
                    format!(
                        "kink reports this mutation unknown with this reason (every test of the \
                         mutant is excluded), so no program can kill it: choose another mutation \
                         (`{run}` gives the same reason)"
                    )
                };
                return refuse(
                    document,
                    Refusal::new("exclusions", exclusion.name(), detail),
                    &action,
                );
            }
            Err(error) => {
                return refuse(
                    document,
                    Refusal::new(
                        "exclusions",
                        "exclusions-unavailable",
                        format!("the {role}'s definition exclusions: {error}"),
                    ),
                    "report this: kink's exclusions of the side could not be read",
                );
            }
        }
    }
    document["job"]["exclusions"] = Value::Object(exclusions);

    let sides = compiled_side(manifest, &spec, &spec.compiled).and_then(|baseline_side| {
        mutant
            .as_ref()
            .map(|mutant| compiled_side(manifest, &spec, &mutant.side))
            .transpose()
            .map(|mutant_side| (baseline_side, mutant_side))
    });
    let (baseline_side, mutant_side) = match sides {
        Ok(sides) => sides,
        Err(error) => {
            return refuse(
                document,
                Refusal::new("sides", "conversion-failed", error.to_string()),
                "report this: kink's sides do not convert into k-rust-fuzz definitions",
            );
        }
    };
    document["sides"] = json!({
        "baseline": side_value(&spec.compiled, &baseline_side),
    });
    if let (Some(mutant), Some(mutant_side)) = (&mutant, &mutant_side) {
        document["sides"]["mutant"] = side_value(&mutant.side, mutant_side);
    }

    let target = match kind {
        // Kill: the mutant's clean end outside the baseline's complete set of ends.
        None => Target {
            kind: TargetKind::Differential(DifferentialTarget::default()),
            run_to_completion: false,
            negated_property: false,
            data_end: true,
            // Both options judge rule and pattern hits only; a differential target ignores them.
            comparable: false,
            query_confirmable: false,
        },
        // A rule job: kink counts a program in `matched_by` (`fired_by`) only when its all-paths
        // baseline run is comparable, so the hit's run of every path must be (`comparable`),
        // which also needs data ends; so does a coverage goal, which kink counts the same way.
        // Under `[observe]` kink also counts a program a deterministic bound cuts
        // (`comparable-prefix`), which no setting of this target admits: k-rust-fuzz reads a
        // rule or coverage goal at a leaf, and a path a bound cut is no hit
        // (`reached-cut-path`), so such a witness is not searched for, only confirmed by
        // `coverage`'s own predicate when given (`confirm_program`).
        Some(kind @ (TargetKind::Rule(_) | TargetKind::Coverage(_))) => Target {
            kind,
            run_to_completion: true,
            negated_property: false,
            data_end: true,
            comparable: true,
            query_confirmable: false,
        },
        // Pattern: a query `hit` needs some reached configuration that matches, so the pattern
        // is matched at every configuration (`any-state`), with the facts a complete search
        // could stop at refused (`query-confirmable`).
        Some(kind) => Target {
            kind,
            run_to_completion: false,
            negated_property: false,
            data_end: false,
            comparable: false,
            query_confirmable: true,
        },
    };
    let budget = manifest.budget;
    let campaign_spec = CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(baseline_side),
            mutant: mutant_side.map(Arc::new),
        },
        program: ProgramInput::Source(FuzzProgram {
            program: instance.text.clone().map(|text| ProgramText {
                name: template.id.clone(),
                text,
                start_sort: instance.start_sort.clone(),
            }),
            config_vars: campaign_variables(&spec, &instance),
        }),
        holes: template.holes.clone(),
        target,
        options: CaseOptions {
            paths: options.paths,
            max_depth: Some(budget.max_depth),
            max_work: Some(options.max_work.unwrap_or(DEFAULT_MAX_WORK)),
            safety_limit_ms: Some(budget.time_ms),
            assume_joined: if reads_data {
                assumed_names_k(manifest, options)
            } else {
                Vec::new()
            },
            // The corpus's stop, on every request of the campaign: the system it fuzzes is the
            // truncated one every kink verb runs.
            stop: instance.case_stop(manifest),
            ..CaseOptions::default()
        },
        // A coverage goal's distance is how near the run's records come to its facts (the
        // guard's recorded truths, the binder's values; k-rust-fuzz's coverage score), which the
        // climb follows from blind cases; every other job samples blind, as it did.
        proposers: if job.covers() {
            coverage_proposers()
        } else {
            ProposerConfig::default()
        },
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: options.seed,
        identity: CallerIdentity {
            k_rust_revision: crate::k_rust_revision(),
            thread_stack_size: Some(DEFINITION_STACK_BYTES as u64),
        },
    };
    // kink's assembly of the template (`[[program]]`'s), which the campaign baseline's assembly
    // must equal (`template-assembly-differs`, below).
    let template_input = template_program(template, &instance);
    let kink_template = inputs.test_case(&template_input, &template_inputs(&instance));
    let mut campaign = match Campaign::new(campaign_spec) {
        Ok(campaign) => campaign,
        Err(error) => {
            return refuse(
                document,
                Refusal::new("campaign", "campaign-refused", error.to_string()),
                "fix the template's holes or the assumed names: the detail says which",
            );
        }
    };

    // The up-front assembly check (design 3.2.5): a run of no case gives each side's initial
    // configuration at the holes' anchors (the identity's digests). kink assembles both sides'
    // inputs from the baseline, so a mutant that assembles the template otherwise (an edit of a
    // `[macro]` rule) would judge an input kink never runs; and a baseline that assembles it
    // otherwise than kink would make every candidate an assembly mismatch.
    let zero = campaign.run(Budget::Cases(0), None);
    let anchor = |role| {
        zero.identity
            .definitions
            .iter()
            .find(|definition| definition.role == role)
            .and_then(|definition| definition.initial_configuration_digest.clone())
    };
    let (baseline_anchor, mutant_anchor) = (
        anchor(k_rust_fuzz::report::DefinitionRole::Baseline),
        anchor(k_rust_fuzz::report::DefinitionRole::Mutant),
    );
    let kink_digest = kink_template
        .as_ref()
        .ok()
        .map(|test| digest_hex(test.initial_state.to_string().as_bytes()));
    document["assembly"] = json!({
        "kink_template": match &kink_template {
            Ok(_) => json!({"sha256": kink_digest}),
            Err(refusal) => json!({
                "refused": {"stage": refusal.stage, "reason": refusal.reason, "detail": refusal.detail},
            }),
        },
        "baseline_anchor": baseline_anchor,
        "mutant_anchor": mutant_anchor,
    });
    if let Err(refusal) = &kink_template {
        push_warning(
            &mut document,
            warning(
                "unusable-template",
                format!(
                    "kink refuses the template's own input ({}: {}): a program from this \
                     template may be refused the same way",
                    refusal.reason, refusal.detail
                ),
            ),
        );
    }
    if let (Some(baseline), Some(mutant)) = (&baseline_anchor, &mutant_anchor)
        && baseline != mutant
    {
        return refuse(
            document,
            Refusal::new(
                "assembly",
                "mutant-assembly-differs",
                format!(
                    "the mutant parses the template differently from kink's input: at the \
                     holes' anchors its initial configuration (sha256 {mutant}) is not the \
                     baseline's (sha256 {baseline}), while kink assembles every test's input \
                     from the baseline (an edit of a [macro] rule, or of what the program's \
                     parse reads)"
                ),
            ),
            "no witness of this campaign could be kink's: the fuzz would run the mutant on \
             another input than kink does. Choose another mutation, or kill this one with a \
             program whose text does not reach the edited parse",
        );
    }
    if let (Some(baseline), Some(kink)) = (&baseline_anchor, &kink_digest)
        && baseline != kink
    {
        return refuse(
            document,
            Refusal::new(
                "assembly",
                "template-assembly-differs",
                format!(
                    "the campaign's baseline assembles the template at the holes' anchors \
                     (sha256 {baseline}) differently from kink's assembly of the template \
                     (sha256 {kink})"
                ),
            ),
            "report this: k-rust-fuzz and kink assemble the template into different initial \
             configurations (grammar, bindings or stream defaults), so every candidate would \
             be an assembly mismatch",
        );
    }

    // The witness filter (fz26 FZ-COMPARABLE-B): kink's rules judge each candidate inside the
    // campaign, on the loads the exclusions were read from, with the data facts of the names
    // kink's confirmation judges under (the flow's and the command line's).
    let mut filter = None;
    if options.filter {
        let mut loads = loads.into_iter();
        let job_kind = match job {
            FuzzJob::Kill { .. } => FilterJob::Kill,
            FuzzJob::Rule { .. } | FuzzJob::Refuted { .. } | FuzzJob::Cover { .. } => {
                FilterJob::Reach
            }
            FuzzJob::Pattern { .. } => FilterJob::Pattern,
        };
        let baseline = loads
            .next()
            .map(|load| FilterSide::new(load, spec.data.clone()));
        let mutant_side = mutant
            .as_ref()
            .and_then(|mutant| Some(FilterSide::new(loads.next()?, mutant.data.clone())));
        if let Some(mut baseline) = baseline {
            let mut mutant_side = mutant_side;
            let added = options
                .assume_joined
                .iter()
                .any(|name| !manifest.spec.assume_joined.contains(name));
            if reads_data && added {
                let names = assumed_names_k(manifest, options);
                for side in std::iter::once(&mut baseline).chain(mutant_side.as_mut()) {
                    if let Err(error) = side.recompute_data(&names, &manifest.sentence_names) {
                        return refuse(
                            document,
                            Refusal::new("filter", "filter-unavailable", error),
                            "report this: kink's data facts of a side could not be read for the \
                             witness filter (--no-filter runs without it)",
                        );
                    }
                }
            }
            let mut judgement =
                KinkJudgement::new(job_kind, baseline, mutant_side).with_spelling(spelling);
            // Every candidate keeps the template's text outside its holes, so the filter's state
            // exclusion of the template's input, read without a run's lists, is one of every
            // candidate whose holes do not replace the excluded application. A hole whose span
            // text holds that application could remove it; refusing then loses witnesses, never
            // admits one (final review N3).
            if let Ok(test) = &kink_template
                && let Some((role, exclusion)) = judgement.initial_exclusion(&test.initial_state)
            {
                document["job"]["filter"] = json!({"on": true, "id": null});
                return refuse(
                    document,
                    Refusal::new(
                        "filter",
                        "initial-state-excluded",
                        format!(
                            "kink's input of the template has the exclusion {exclusion} on the \
                             {role}'s definition, as the witness filter reads it without a run's \
                             lists; every candidate keeps the template's text outside its holes, \
                             so the filter refuses every candidate unless a hole's text replaces \
                             the excluded application, which the campaign does not look for \
                             (kink's own run of a candidate whose input applies a function whose \
                             value depends on the short-circuit reading is judged by its list of \
                             readings, which the filter does not see)"
                        ),
                    ),
                    &format!(
                        "choose a template whose input applies no implementation-chosen hook and \
                         no function whose value depends on the short-circuit reading, or, for \
                         the short-circuit reading, run with --no-filter so that kink's \
                         confirmation judges each witness by its runs' lists ({} names the \
                         exclusion as the cause of such a program it cannot judge)",
                        spelling.verb(Verb::Run)
                    ),
                );
            }
            filter = Some(judgement);
        }
    }
    // A case whose run stopped for lack of native stack judges nothing, and no budget bounds the
    // stack: `--stack-stops` of them in a row end the search ([`DEFAULT_STACK_STOPS`]).
    let mut stack_stops = StackStops::new(
        options.stack_stops,
        if matches!(job, FuzzJob::Kill { .. }) {
            options.open_stops
        } else {
            0
        },
    );
    let (report, fired) =
        under_watchdog(options.time_limit_ms.map(Duration::from_millis), |token| {
            let filter = filter
                .as_mut()
                .map(|filter| filter as &mut dyn k_rust_fuzz::WitnessFilter);
            campaign.run_observed(options.budget, token, filter, &mut |note| {
                stack_stops.observe(note)
            })
        });
    drop(filter);
    document["job"]["outcome"] = json!("fuzzed");
    document["job"]["filter"] = json!({"on": options.filter, "id": report.identity.filter});
    let refused = &report.totals.filter.refused;
    if !refused.is_empty() {
        let causes = refused
            .iter()
            .map(|(cause, count)| format!("{count} {cause}"))
            .collect::<Vec<_>>()
            .join(", ");
        push_warning(
            &mut document,
            warning(
                "client-refused",
                format!(
                    "kink's rules, as the witness filter reads them, refused candidate hits inside \
                     the campaign ({causes}), each judged before its confirmation (the filter is \
                     stricter than kink's own run only where the README says); the fuzz report's \
                     client-refusals give each cause's first case and kink's reason"
                ),
            ),
        );
    }
    document["findings"] = Value::Array(
        report
            .definition_findings
            .iter()
            .map(|finding| finding_value(finding, &manifest.sentence_names))
            .collect(),
    );
    if reads_data {
        document["assumed"] = assumed_value(manifest, options, Some(&report));
    }
    // A crash is no kill and moves no verdict: one warning per crash, for its report
    // (FZ-CRASH).
    for line in report.crashes.lines() {
        push_warning(&mut document, warning("crash", line));
    }
    // The campaign's statement of a `not-ceil-free` case says that a warning names the function
    // when it is known: each such warning of its report, here too (its text after the kind).
    for text in &report.warnings {
        if let Some(detail) = text.strip_prefix("not-ceil-free: ") {
            push_warning(&mut document, warning("not-ceil-free", detail));
        }
    }
    let fuzz =
        serde_json::from_str::<Value>(&report.to_canonical_json()).expect("a fuzz report is JSON");
    let mut attempt = json!({
        "seed": options.seed.to_string(),
        "fuzz": fuzz,
        "candidate": null,
        "confirmation": null,
    });
    // What the job looks for, for the actions below.
    let sought = match job {
        FuzzJob::Kill { .. } => {
            "choose a template whose run reaches the edited rule and ends on both sides"
        }
        FuzzJob::Rule { .. } => {
            "choose a template whose run comes near the rule, and ends on every path with values"
        }
        FuzzJob::Pattern { .. } => "choose a template whose run comes near the pattern",
        FuzzJob::Refuted { .. } | FuzzJob::Cover { .. } => {
            "choose a template whose run comes near the obligation (one of the programs its \
             target names), and ends on every path with values"
        }
    };
    let ok = match &report.outcome {
        CampaignOutcome::WitnessFound { witness } => {
            // The candidates, in order: the shrunk case (else the first), then the first when
            // kink refuses the shrunk one and the first is another program (KF-T4).
            let mut cases = vec![
                witness
                    .shrunk
                    .as_ref()
                    .map_or((&witness.first, "first"), |shrunk| (shrunk, "shrunk")),
            ];
            if witness.shrunk.is_some() && options.confirm {
                cases.push((&witness.first, "first"));
            }
            let premises = if reads_data {
                premises(manifest, options, &report)
            } else {
                Vec::new()
            };
            let mut refused = Vec::new();
            let mut offered = None;
            let mut offered_case = None;
            for (case, which) in cases {
                let fragment = fragment(template, &instance, case);
                if refused
                    .iter()
                    .any(|(id, _): &(String, Value)| id == &fragment.id)
                {
                    continue;
                }
                let mut candidate = serde_json::to_value(case).expect("a witness case encodes");
                candidate["case"] = json!(which);
                let assembly =
                    check_assembly(&mut inputs, &fragment.program, &fragment.inputs, case);
                candidate["assembly"] = assembly.value();
                if assembly != AssemblyCheck::Match {
                    if offered.is_none() && refused.is_empty() {
                        attempt["candidate"] = candidate;
                        document["stopped"] = json!("assembly-mismatch");
                        document["action"] = json!(format!(
                            "the witness is no kink witness: kink's assembly of its program does \
                             not give the input the campaign judged ({}); nothing is offered. \
                             Report it, or try another seed or template",
                            match &assembly {
                                AssemblyCheck::Mismatch { detail, .. } => detail.clone(),
                                AssemblyCheck::Refused { reason, detail } => {
                                    format!("kink refuses the program's input, {reason}: {detail}")
                                }
                                AssemblyCheck::Match => unreachable!(),
                            }
                        ));
                        document["attempts"] = json!([attempt]);
                        return (document, true);
                    }
                    continue;
                }
                if !options.confirm {
                    attempt["candidate"] = candidate;
                    offered = Some((fragment, false));
                    offered_case = Some(case);
                    break;
                }
                let mut confirmation = confirm(
                    manifest,
                    options,
                    job,
                    Confirming {
                        rule_at: rule_at.as_ref(),
                        item: goal_item.as_deref(),
                        front,
                    },
                    &fragment.program,
                );
                confirmation["case"] = json!(which);
                let confirmed = confirmation["confirmed"] == true;
                attempt["candidate"] = candidate;
                attempt["confirmation"] = confirmation.clone();
                if confirmed {
                    offered = Some((fragment, true));
                    offered_case = Some(case);
                    break;
                }
                refused.push((fragment.id.clone(), confirmation));
            }
            // The refused verdicts other than the one `confirmation` holds: with a witness
            // offered, every refused one; with none, `confirmation` is the last refused verdict,
            // so it is left out here rather than repeated (GUIDE-USABILITY nit).
            let shown = if offered.is_some() {
                refused.as_slice()
            } else {
                &refused[..refused.len().saturating_sub(1)]
            };
            if !shown.is_empty() {
                attempt["refused_confirmations"] =
                    Value::Array(shown.iter().map(|(_, c)| c.clone()).collect());
            }
            let Some((fragment, confirmed)) = offered else {
                // Every candidate kink was asked about was refused.
                let (_, last) = refused.last().expect("a refused candidate");
                document["stopped"] = json!("unconfirmed");
                document["action"] = json!(format!(
                    "kink's own {} does not confirm the witness ({}: {}); nothing is offered. \
                     Try another template, seed or hole range",
                    match job {
                        FuzzJob::Kill { .. } => "run",
                        FuzzJob::Rule { .. } | FuzzJob::Refuted { .. } | FuzzJob::Cover { .. } => {
                            "coverage"
                        }
                        FuzzJob::Pattern { .. } => "query",
                    },
                    last["status"].as_str().unwrap_or("refused"),
                    last["cause"]
                        .as_str()
                        .map_or_else(|| last["reason"].to_string(), str::to_owned),
                ));
                document["attempts"] = json!([attempt]);
                return (document, true);
            };
            // A witness whose run of every path a bound or a clock cut may not terminate: as a
            // corpus program it runs to the budget in every `run` and `coverage`, and is never
            // comparable (final review ux S8). Only a pattern witness can be one: a rule
            // job's witness's run is comparable, and a kill's two runs end.
            if let Some(comparable) = offered_case.and_then(|case| case.comparable.as_ref()) {
                let cuts = comparable
                    .reasons
                    .iter()
                    .filter(|reason| {
                        matches!(
                            reason,
                            ComparableCondition::WorkBound
                                | ComparableCondition::DepthBound
                                | ComparableCondition::Clock
                        )
                    })
                    .map(|reason| reason.name())
                    .collect::<Vec<_>>();
                if !cuts.is_empty() {
                    push_warning(
                        &mut document,
                        warning(
                            "witness-not-terminating",
                            format!(
                                "the witness program's run of every path did not end within \
                                 the bounds ({}): it reaches the target, but as a test it may \
                                 not terminate, so every `run` and `coverage` would run it to \
                                 the budget and kink would {}; prefer hole values or a template \
                                 whose run ends",
                                cuts.join(", "),
                                if manifest.observe.is_some() {
                                    "count it only by its observation channels \
                                     (comparable-prefix)"
                                } else {
                                    "never count it comparable"
                                }
                            ),
                        ),
                    );
                }
            }
            let (id, file) = (fragment.id.clone(), fragment.file.clone());
            document["program"] = json!({
                "id": id,
                "fragment": fragment.toml,
                "file": file,
                "premises": premises,
                "confirmed": confirmed,
            });
            let missing = premises
                .iter()
                .filter(|p| p["in_flow"] == false)
                .filter_map(|p| p["name"].as_str())
                .collect::<Vec<_>>();
            let append = format!(
                "append the [[program]] fragment to FLOW.toml (as text, or write the text to {} \
                 and give it as file)",
                file.as_deref().unwrap_or("a file")
            );
            let mut action = if confirmed {
                format!(
                    "{append}: kink's own {} confirmed it on the flow with this program alone",
                    match job {
                        FuzzJob::Kill { .. } => "run (killed, with the fragment as killer)",
                        FuzzJob::Rule { .. } => "coverage (counted, and listed for the rule)",
                        FuzzJob::Pattern { .. } => "query (the claim is confirmed)",
                        FuzzJob::Refuted { .. } | FuzzJob::Cover { .. } => {
                            "coverage (counted, and listed as covering the obligation)"
                        }
                    }
                )
            } else {
                let mut action = match job {
                    FuzzJob::Kill { flip: true, .. } => format!(
                        "{append}, then run `{}`: its flips family runs the flip's kill search, \
                         which decides whether the program distinguishes it",
                        spelling.command(Verb::Run)
                    ),
                    FuzzJob::Kill { mutation, .. } => format!(
                        "{append}, then run `{} --only {mutation}`: kink's own run decides \
                         whether it kills, and a run that judges the whole list records it as \
                         the mutation's killer in its lock",
                        spelling.command(Verb::Run)
                    ),
                    FuzzJob::Rule { fired, .. } => format!(
                        "{append}, then run `{}`: the rule's {} lists the program once kink's \
                         own run of it is comparable",
                        spelling.command(Verb::Coverage),
                        if fired { "fired_by" } else { "matched_by" }
                    ),
                    FuzzJob::Pattern { id: pattern, .. } => format!(
                        "{append}, add {id:?} to the `programs` of pattern {pattern:?} in \
                         PATTERNS.toml, then run `{} --only {pattern}`: kink's own search \
                         confirms the claim",
                        spelling.command(Verb::Query)
                    ),
                    FuzzJob::Refuted { .. } | FuzzJob::Cover { .. } => format!(
                        "{append}, then run `{}`: the obligation {} is covered once kink's own \
                         run of the program is comparable",
                        spelling.command(Verb::Coverage),
                        goal_item.as_deref().unwrap_or_default()
                    ),
                };
                action.push_str(". This command did not confirm it (--no-confirm)");
                action
            };
            if !missing.is_empty() {
                action.push_str(&format!(
                    "; first add to [spec] assume_joined the premises FLOW.toml lacks: {}",
                    missing.join(", ")
                ));
            }
            if expects_survival && refutes_survival(&document["program"]) {
                // The witness refutes the mutation's expectation: it is the finding, and the
                // program what shows it.
                action = format!(
                    "the mutation expects to survive, and this program distinguishes its mutant \
                     from the specification: what the edit changes is observable on it. Fix the \
                     specification, or the mutation's expectation; to keep the program as a \
                     test, {action}"
                );
            } else if expects_survival {
                // A candidate only: the corpus as it stands has not been shown to kill.
                let mut open = Vec::new();
                if !confirmed {
                    open.push("kink's own run did not confirm the kill (--no-confirm)".to_owned());
                }
                if !missing.is_empty() {
                    open.push(format!(
                        "the kill rests on premises FLOW.toml's [spec] assume_joined lacks ({})",
                        missing.join(", ")
                    ));
                }
                action = format!(
                    "the mutation expects to survive, and this program may distinguish its mutant \
                     from the specification, but it does not refute the expectation yet: {}. To \
                     decide it, {action}",
                    open.join(", and ")
                );
            }
            document["action"] = json!(action);
            true
        }
        CampaignOutcome::NoWitnessFound { no_witness }
            if !report.totals.filter.refused.is_empty() && report.totals.unconfirmed == 0 =>
        {
            // Every hit was one kink's rules refuse (none the filter accepted was lost to its
            // confirmation): no witness kink accepts, which is no sign of survival
            // (FZ-COMPARABLE-B review M5).
            document["stopped"] = json!("client-refused");
            document["action"] = json!(format!(
                "no witness kink accepts: {} Mark other literals as holes, narrow the holes to \
                 values kink compares, or {sought}",
                no_witness.statement
            ));
            true
        }
        CampaignOutcome::NoWitnessFound { no_witness }
            if report.totals.domain.is_some_and(|domain| domain.exhausted) =>
        {
            // Every assignment of the holes ran: no budget was spent, and more cases would only
            // repeat them (final review ux S6).
            document["stopped"] = json!("domain-exhausted");
            document["action"] = json!(format!(
                "no witness: {} Every assignment of the holes ran, so this campaign has no other \
                 case to run: mark more literals as holes, widen their ranges, or {sought}",
                no_witness.statement
            ));
            true
        }
        CampaignOutcome::NoWitnessFound { no_witness } => {
            // The budget was spent: k-rust-fuzz's other ending without a witness, every proposer
            // exhausted (`Ending::Exhausted`), cannot occur here, since kink-flow runs the
            // library's default proposers, the blind proposer alone, which proposes a case
            // whenever asked (a finite domain ends `domain-exhausted`, above).
            document["stopped"] = json!("budget");
            // The advice follows the statement (final review ux S5). Where the statement says
            // coverage stopped growing long ago, it says more cases of this program and these
            // holes are unlikely to reach a new rule, so advising more cases would contradict it.
            // Where it says the mutant may not terminate on this program (one `work-bound` case
            // of that kind or more, `totals.diverging`), more cases with other hole values may
            // still find a witness; but whether a run terminates cannot be decided, each such case
            // spends `max-work` on the mutant, and the statement suggests no bound, so the action
            // points at the template and its holes instead of the budget (KINK-R4 review N5: a
            // choice of advice, not a claim that more cases cannot help).
            // Where every case's run ended holding a term not shown to exist, more cases of this
            // template would end so too, whatever the budget. A kill job's case is judged on its
            // mutant run; a rule or pattern job has no mutant, and its one run is the template's
            // own.
            let hint = if stack_stops.all_open() {
                all_open_hint(matches!(job, FuzzJob::Kill { .. }))
            } else if report.totals.coverage_stalled_since().is_some()
                || report.totals.diverging.is_some()
            {
                "Rather than raising --cases or --work, mark other literals as holes"
            } else {
                "Raise --cases or --work, mark more literals as holes"
            };
            document["action"] = json!(format!(
                "no witness: {} {hint}, or {sought}",
                no_witness.statement
            ));
            true
        }
        CampaignOutcome::RejectedOut { no_witness } => {
            document["stopped"] = json!("rejected-out");
            document["action"] = json!(format!(
                "no witness: {} Most generated values were rejected: narrow the holes' ranges or \
                 choices",
                no_witness.statement
            ));
            true
        }
        CampaignOutcome::Cancelled { no_witness } if stack_stops.ended() => {
            // The observer ended the search: the last cases each stopped for lack of native
            // stack, and no budget bounds it, so more cases or work would only repeat them. The
            // advice is that of kink's `stack-stop` reason for a kill, which can be written as a
            // mutant that ends; a rule or pattern job's template recurses on the baseline itself.
            document["stopped"] = json!("stack-stops");
            let advice = match job {
                FuzzJob::Kill { .. } if stack_stops.all_unsupported() => {
                    "every one of them recursed on the mutant, so a case of this template that \
                     reaches the edit is unlikely to end on it: write a case on an input the \
                     mutant ends on; when it recurses without end on every input that reaches \
                     the edit, no case kills it: write the misunderstanding as a mutant that \
                     ends, or as a replacement whose result differs, or drop the mutation"
                }
                _ => &format!("their runs recursed until the stack stopped them: {sought}"),
            };
            document["action"] = json!(format!(
                "no witness: the last {} cases in a row each stopped for lack of native stack \
                 (unjudged reason stack-stops), which no budget bounds, so no such case can be a \
                 witness and the search ended there (--stack-stops); {advice}. {}",
                stack_stops.limit,
                observer_stopped(&no_witness.statement, "--stack-stops")
            ));
            true
        }
        CampaignOutcome::Cancelled { no_witness } if stack_stops.open_ended() => {
            // The observer ended the search: the last cases' mutant runs each ended holding a term
            // not shown to exist, which no budget decides. The advice is that of kink's
            // `open-application` reason.
            document["stopped"] = json!("open-stops");
            document["action"] = json!(format!(
                "no witness: the last {} cases in a row each ended, on the mutant, holding a term \
                 not shown to exist (unjudged reason not-ceil-free; a warning names the function \
                 when it is known), which no budget decides, so no such case can be a witness and \
                 the search ended there (--open-stops); choose a program or hole range whose runs \
                 do not reach that application, and when the edit leaves the function's value \
                 open on every input that reaches it, no case kills it: write the \
                 misunderstanding as a replacement whose result differs, or drop the mutation. {}",
                stack_stops.open_limit,
                observer_stopped(&no_witness.statement, "--open-stops")
            ));
            true
        }
        CampaignOutcome::Cancelled { no_witness } => {
            document["stopped"] = json!(if fired { "time-limit" } else { "cancelled" });
            document["action"] = json!(format!(
                "no witness before the time limit (outside the determinism contract): {} Raise \
                 --time-limit-ms or lower the budget",
                no_witness.statement
            ));
            true
        }
        CampaignOutcome::Equivalent => {
            document["stopped"] = json!("equivalent");
            document["action"] = json!(
                "the two definitions denote one theory (equal execution digests, and equal \
                 program assembly): no input can kill this mutation; drop or change it"
            );
            true
        }
        CampaignOutcome::NotComparable { .. } => {
            document["stopped"] = json!("not-comparable");
            let names = report
                .definition_findings
                .iter()
                .filter(|f| !f.assumed)
                .map(|f| {
                    format!(
                        "{} ({}, {})",
                        f.name.as_deref().map_or_else(
                            || "unnamed".to_owned(),
                            |name| { manifest.sentence_names.spelled(name) }
                        ),
                        role_name(f.side),
                        verdict_name(f.verdict)
                    )
                })
                .collect::<Vec<_>>();
            document["action"] = json!(format!(
                "not comparable (the fuzz report's outcome explains the verdicts); findings no \
                 name assumes: {}. Under such a finding the definition may identify the ends a \
                 test compares, so a kill would hold in no model and a matching program would be \
                 no comparable test; kink refuses kills too (baseline-findings) unless FLOW.toml's \
                 [spec] assume_joined names them. Fix the definition, or name each finding you \
                 accept as a premise with --assume-joined NAME and in [spec] assume_joined (a \
                 decided finding cannot be named; a genuine one is known false)",
                names.join("; ")
            ));
            false
        }
        CampaignOutcome::Aborted { kind, reason, .. } => {
            document["stopped"] = json!("aborted");
            let what = match kind {
                AbortKind::SolverPreludeInconsistent | AbortKind::SolverPreludeMalformed => {
                    "the solver's prelude failed (the definition's SMT text, a user prelude, or \
                     k-rust's SMT translation of them): check the definition's smtlib and \
                     smt-hook attributes, or report it"
                }
                AbortKind::SolverPreludeUnknown => {
                    "the solver could not decide the prelude: try again, or report it"
                }
                AbortKind::SolverInit => {
                    "the solver did not start for this definition (its SMT declarations, \
                     k-rust's translation of them, or the host): report it"
                }
                AbortKind::ClientPanic => {
                    "the campaign's observer panicked (a defect of its client): report it"
                }
                AbortKind::RebuildFailed => {
                    "the campaign's backends did not rebuild after a crash: report it with the \
                     fuzz report's crashes"
                }
                AbortKind::ClientDefect => {
                    "kink-flow's witness filter broke its contract (a defect of kink-flow): \
                     report it, and run with --no-filter meanwhile"
                }
            };
            document["action"] = json!(format!("the campaign aborted: {what}. {reason}"));
            false
        }
    };
    document["attempts"] = json!([attempt]);
    (document, ok)
}

/// One rule job's rule, resolved on the baseline.
struct TargetRule {
    /// The targeted rewrite id.
    id: String,
    /// The authored rule the id belongs to: `coverage` lists programs under authored rules only.
    at: RuleText,
    /// Equation ids of the same sentence, which the target does not read.
    untargeted: Vec<String>,
}

impl TargetRule {
    fn value(&self) -> Value {
        json!({
            "module": self.at.at.module,
            "index": self.at.at.index,
            "file": self.at.file,
            "start_line": self.at.start_line,
            "label": self.at.label,
            "id": self.id,
            "untargeted_ids": self.untargeted,
        })
    }
}

/// The most rules a rule job's refusal lists as the ones the reference may have meant.
const NEAREST_RULES: usize = 5;

/// Whether `text` is a compiled rule id (64 lowercase hex digits).
fn is_rule_id(text: &str) -> bool {
    text.len() == 64
        && text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// The ids of the baseline's rewrite axioms: a rewrite axiom is a `\rewrites` (k-rust
/// classifies every other `UNIQUE_ID` axiom as an equation of some kind).
pub(crate) fn rewrite_ids(validated: &ValidatedDefinition) -> BTreeSet<String> {
    let Ok(definition) = parse_definition(&validated.artifacts().definition_kore) else {
        return BTreeSet::new();
    };
    definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            Sentence::Axiom {
                pattern,
                attributes,
                ..
            } if matches!(**pattern, KorePattern::Rewrites { .. }) => {
                attributes.0.iter().find_map(|attribute| match attribute {
                    KorePattern::Application { symbol, arguments }
                        if symbol.name == KoreAttribute::UniqueId.as_str() =>
                    {
                        match arguments.as_slice() {
                            [KorePattern::String(id)] => id.as_utf8().ok().map(str::to_owned),
                            _ => None,
                        }
                    }
                    _ => None,
                })
            }
            _ => None,
        })
        .collect()
}

/// Resolve the rule of `--matched RULE` or `--fired RULE` on the baseline: `FILE:LINE` (a line
/// inside an authored rule of `FILE`), a label (bare or `MODULE.x`, as a mutation edit's), or a
/// compiled id. The rule's ids with a coverage signal (kink's coverage domain) must hold exactly
/// one rewrite id, which is targeted; the sentence's equation ids are listed as untargeted.
fn resolve_rule(
    manifest: &FlowManifest,
    spec: &AdmittedSpec,
    rule: &str,
) -> Result<TargetRule, Refusal> {
    let refused = |reason: &str, detail: String| Refusal::new("rule", reason, detail);
    let authors = RuleAuthors::of(&spec.compiled);
    let domain = coverage_domain(&spec.compiled);
    let rewrites = rewrite_ids(&spec.compiled);
    let texts = rule_texts(manifest, &spec.loaded);
    let (at, ids): (RuleText, Vec<String>) = if is_rule_id(rule) {
        if authors.get(rule).is_none() {
            return Err(refused(
                "unknown-rule-id",
                format!("no axiom of the baseline has the id {rule}"),
            ));
        }
        let Some(at) = texts
            .iter()
            .find(|text| authors.ids_of(&text.at).any(|id| id == rule))
            .cloned()
        else {
            // `coverage` lists programs under the specification's authored rules only, so no
            // program is ever listed for this id and no rule job on it can be confirmed.
            return Err(refused(
                "no-authored-rule",
                format!(
                    "the axiom {rule} was written by no authored rule of the specification (a \
                     prelude rule, or a sentence that is not a rule), and kink's `coverage` lists \
                     programs under authored rules only"
                ),
            ));
        };
        (at, vec![rule.to_owned()])
    } else {
        let by_line = rule
            .rsplit_once(':')
            .and_then(|(file, line)| Some((file, line.parse::<u32>().ok()?)));
        let matches = match by_line {
            Some((file, line)) => texts
                .iter()
                .filter(|text| {
                    text.file
                        .as_deref()
                        .is_some_and(|name| name == file || name.ends_with(&format!("/{file}")))
                        && text.start_line.is_some_and(|start| start <= line)
                        && text.end_line.is_some_and(|end| line <= end)
                })
                .collect::<Vec<_>>(),
            None => texts
                .iter()
                .filter(|text| {
                    text.label.as_deref().is_some_and(|label| {
                        label == rule
                            || label == format!("{}.{rule}", text.at.module)
                            || (!label.contains('.')
                                && rule.strip_prefix(&format!("{}.", text.at.module))
                                    == Some(label))
                    })
                })
                .collect(),
        };
        // A rule as a refusal lists it: its position, its label, and the ids a rule job on it can
        // target (its rewrite ids with a coverage signal), so the author can name it by any of
        // them (final review ux S9: the refusal said "listed" ids and listed none).
        let describe = |text: &RuleText| {
            let ids = authors
                .ids_of(&text.at)
                .filter(|id| rewrites.contains(*id) && domain.contains(*id))
                .collect::<Vec<_>>();
            format!(
                "{}:{} ({}#{}{}) {}",
                text.file.as_deref().unwrap_or("?"),
                text.start_line
                    .map_or_else(|| "?".to_owned(), |l| l.to_string()),
                text.at.module,
                text.at.index,
                text.label
                    .as_deref()
                    .map_or_else(String::new, |label| format!(", label {label}")),
                if ids.is_empty() {
                    "no rewrite id a rule job can target".to_owned()
                } else {
                    format!("id {}", ids.join(", "))
                }
            )
        };
        let listing = |texts: &[&RuleText]| {
            texts
                .iter()
                .map(|text| format!("\n  {}", describe(text)))
                .collect::<String>()
        };
        let one = match matches.as_slice() {
            [] => {
                return Err(match by_line {
                    Some((file, line)) => {
                        let in_file = |text: &&RuleText| {
                            text.file.as_deref().is_some_and(|name| {
                                name == file || name.ends_with(&format!("/{file}"))
                            })
                        };
                        let mut nearest = texts.iter().filter(in_file).collect::<Vec<_>>();
                        let detail = if nearest.is_empty() {
                            let files = texts
                                .iter()
                                .filter_map(|text| text.file.as_deref())
                                .collect::<BTreeSet<_>>();
                            format!(
                                "no authored rule of the specification is written in {file:?}; \
                                 the rules are written in: {}",
                                files.into_iter().collect::<Vec<_>>().join(", ")
                            )
                        } else {
                            nearest.sort_by_key(|text| {
                                let start = text.start_line.unwrap_or(u32::MAX);
                                let end = text.end_line.unwrap_or(start);
                                (start.abs_diff(line).min(end.abs_diff(line)), start)
                            });
                            nearest.truncate(NEAREST_RULES);
                            format!(
                                "no authored rule of the specification spans {rule}; the \
                                 nearest are:{}",
                                listing(&nearest)
                            )
                        };
                        refused("no-rule-at-line", detail)
                    }
                    None => {
                        let wanted = rule.to_lowercase();
                        let near = texts
                            .iter()
                            .filter(|text| {
                                text.label.as_deref().is_some_and(|label| {
                                    let label = label.to_lowercase();
                                    label.contains(&wanted) || wanted.contains(&label)
                                })
                            })
                            .take(NEAREST_RULES)
                            .collect::<Vec<_>>();
                        refused(
                            "unknown-label",
                            if near.is_empty() {
                                format!(
                                    "no rule is labelled {rule:?}, and no label contains it; \
                                     name the rule by FILE:LINE instead"
                                )
                            } else {
                                format!(
                                    "no rule is labelled {rule:?}; the labels that contain it, or \
                                     that it contains, are:{}",
                                    listing(&near)
                                )
                            },
                        )
                    }
                });
            }
            [one] => (*one).clone(),
            several => {
                return Err(refused(
                    if by_line.is_some() {
                        "ambiguous-rule-position"
                    } else {
                        "ambiguous-label"
                    },
                    format!(
                        "{rule:?} names several rules:{}\n{}",
                        listing(several),
                        if by_line.is_some() {
                            "give a longer path"
                        } else {
                            "qualify it with the module"
                        }
                    ),
                ));
            }
        };
        let ids = authors.ids_of(&one.at).map(str::to_owned).collect();
        (one, ids)
    };
    let signalled = ids
        .into_iter()
        .filter(|id| domain.contains(id))
        .collect::<Vec<_>>();
    if signalled.is_empty() {
        return Err(refused(
            "no-coverage-signal",
            format!(
                "{rule:?} compiles to no axiom k-rust's run coverage can name (a macro, a claim, \
                 an smt-lemma or non-executable axiom, or nothing), so kink lists it in no \
                 matched_by"
            ),
        ));
    }
    let (targets, untargeted): (Vec<String>, Vec<String>) =
        signalled.into_iter().partition(|id| rewrites.contains(id));
    match targets.as_slice() {
        [] => Err(refused(
            "equation-target",
            format!(
                "{rule:?} compiles to equations only ({}): a rule job targets a rewrite rule, \
                 whose condition a run matches",
                untargeted.join(", ")
            ),
        )),
        [id] => Ok(TargetRule {
            id: id.clone(),
            at,
            untargeted,
        }),
        several => Err(refused(
            "several-rewrite-ids",
            format!(
                "{rule:?} compiles to several rewrite axioms: {}; give one of them by its id",
                several.join(", ")
            ),
        )),
    }
}

/// Lower a pattern's text exactly as kink's `query` does (its rule grammar and execution
/// definition, checked against the baseline search definition): the target's KORE, or the
/// refusal `invalid-pattern` with k-rust's message.
fn lower_pattern(
    manifest: &FlowManifest,
    spec: &AdmittedSpec,
    text: &str,
) -> Result<String, Refusal> {
    let searcher = Searcher::new(spec, &manifest.spec.main_module, manifest.budget)
        .map_err(|detail| Refusal::new("pattern", "search-backend", detail))?;
    let lowering = Lowering::new(spec, &manifest.spec.main_module)
        .map_err(|detail| Refusal::new("pattern", "search-backend", detail))?;
    lowering
        .lower(text, searcher.definition())
        .map(|lowered| lowered.kore())
        .map_err(|detail| Refusal::new("pattern", INVALID_PATTERN, detail))
}

/// A scratch directory, removed when dropped.
struct Scratch(PathBuf);

impl Scratch {
    fn new() -> std::io::Result<Self> {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let path = std::env::temp_dir().join(format!(
            "kink-flow-fuzz-confirm-{}-{nanos}",
            std::process::id()
        ));
        fs::create_dir_all(&path)?;
        Ok(Self(path))
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// kink's own verdict on `program` for `job`, as the fuzz confirms a candidate ([`confirm`]):
/// the seam for checking a program written by hand, or one the fuzz did not find. A rule job's
/// rule is resolved on the admitted baseline as the fuzz resolves it; a specification kink does
/// not admit, or a rule that does not resolve, gives `{confirmed: false, status: "refused",
/// reason, cause}`.
pub fn confirm_program(
    manifest: &FlowManifest,
    options: &FuzzOptions,
    job: FuzzJob<'_>,
    program: &Program,
) -> Value {
    let refused = |reason: &str, cause: String| json!({"confirmed": false, "status": "refused", "reason": reason, "cause": cause});
    let front = FrontEnd::default();
    let admitted = || {
        let (record, admitted) = admit_spec(manifest);
        match admitted {
            Some((spec, _)) => Ok((record, spec)),
            None => Err(record.refusal.as_ref().map_or_else(
                || refused("refused", String::new()),
                |r| refused(&r.reason, format!("{}: {}", r.stage, r.detail)),
            )),
        }
    };
    let (rule_at, item) = match job {
        FuzzJob::Rule { rule, .. } => {
            let spec = match admitted() {
                Ok((_, spec)) => spec,
                Err(refusal) => return refusal,
            };
            match resolve_rule(manifest, &spec, rule) {
                Ok(target) => (Some(target.at.at), None),
                Err(refusal) => return refused(&refusal.reason, refusal.detail),
            }
        }
        FuzzJob::Refuted { rule } => {
            let (record, spec) = match admitted() {
                Ok(admitted) => admitted,
                Err(refusal) => return refusal,
            };
            let goal = resolve_rule(manifest, &spec, rule)
                .map_err(|refusal| (refusal.reason, refusal.detail))
                .and_then(|target| {
                    crate::fuzz_goal::refuted_item(&spec, &record, manifest, &front, &target.at.at)
                        .map_err(|(reason, detail)| (reason.to_owned(), detail))
                });
            match goal {
                Ok(goal) => (None, Some(goal.item)),
                Err((reason, detail)) => return refused(&reason, detail),
            }
        }
        FuzzJob::Cover { item } => (None, Some(item.to_owned())),
        FuzzJob::Kill { .. } | FuzzJob::Pattern { .. } => (None, None),
    };
    confirm(
        manifest,
        options,
        job,
        Confirming {
            rule_at: rule_at.as_ref(),
            item: item.as_deref(),
            front: &front,
        },
        program,
    )
}

/// What a confirmation reads beside the job: a rule job's authored rule, a coverage goal's
/// obligation id, and the front end whose annotation names the obligation.
#[derive(Clone, Copy)]
struct Confirming<'a> {
    rule_at: Option<&'a SentenceRef>,
    item: Option<&'a str>,
    front: &'a FrontEnd<'a>,
}

/// The proposers of a coverage goal's campaign: blind sampling and the climb, at equal weight
/// (k-rust-fuzz spends at most half of the cases on the climb, which climbs from the cases blind
/// sampling makes).
fn coverage_proposers() -> ProposerConfig {
    ProposerConfig {
        weights: BTreeMap::from([
            (k_rust_fuzz::spec::ProposerKind::Blind, 1),
            (k_rust_fuzz::spec::ProposerKind::Climb, 1),
        ]),
        ..ProposerConfig::default()
    }
}

/// kink's own verdict on a candidate (KF-T4), by kink's code on an overlay of the flow: its
/// `[spec]` with the flow's names and the command line's assumed (sorted, without repeats), its
/// `[budget]`, and `program` (the candidate's fragment) as the only `[[program]]`, with a fresh
/// scratch cache removed on every path, so nothing under the flow's directory or `--cache`
/// changes. A kill is confirmed when `run` kills the mutation with the program as killer; a rule
/// job when `coverage` gives the program class `comparable` and lists it in the `matched_by`
/// (`fired_by`) of the targeted rule, `rule_at`, the authored rule the job resolved (final
/// review S1: a listing under any other rule confirms nothing about the target); a pattern when
/// `query`, asked with `programs = [program]`, confirms the claim. The value is `{confirmed,
/// status, reason, cause}` and the job's `killer`, `class` or `answer`.
fn confirm(
    manifest: &FlowManifest,
    options: &FuzzOptions,
    job: FuzzJob<'_>,
    confirming: Confirming<'_>,
    program: &Program,
) -> Value {
    let rule_at = confirming.rule_at;
    let scratch = match Scratch::new() {
        Ok(scratch) => scratch,
        Err(error) => {
            return json!({
                "confirmed": false,
                "status": "error",
                "reason": "scratch-directory",
                "cause": format!("no scratch cache for the confirmation: {error}"),
            });
        }
    };
    let mut overlay = manifest.clone();
    overlay.programs = vec![program.clone()];
    // A rule job reads the rule's `matched_by` and `fired_by`, which no `[coverage]` value
    // changes; the section's deeper families are what `coverage` may refuse, so the overlay
    // asks for none of them.
    overlay.coverage = crate::manifest::CoverageSection::default();
    let mut names = manifest.spec.assume_joined.clone();
    names.extend(options.assume_joined.iter().cloned());
    names.sort();
    names.dedup();
    overlay.spec.assume_joined = names;
    let cache = Some(scratch.0.clone());
    let id = program.id.as_str();
    match job {
        FuzzJob::Kill { list, mutation, .. } => {
            let list = MutationList {
                mutations: list
                    .mutations
                    .iter()
                    .filter(|m| m.id == mutation)
                    .cloned()
                    .collect(),
            };
            let (run, _) = crate::search::run_with(
                &overlay,
                &list,
                &RunOptions {
                    only: vec![mutation.to_owned()],
                    cache,
                    compile_workers: Some(1),
                    ..RunOptions::default()
                },
                RunMode::Search,
            );
            let row = run["mutations"]
                .as_array()
                .and_then(|rows| rows.iter().find(|row| row["id"] == mutation))
                .cloned()
                .unwrap_or(Value::Null);
            let program = run["programs"]
                .as_array()
                .and_then(|rows| rows.iter().find(|row| row["id"] == id))
                .cloned()
                .unwrap_or(Value::Null);
            let killed = row["status"] == "killed" && row["killer"] == id;
            let cause = if killed {
                Value::Null
            } else if program["cause"].is_null() {
                run["spec"]["detail"].clone()
            } else {
                program["cause"].clone()
            };
            json!({
                "confirmed": killed,
                "status": row["status"],
                "reason": row["reason"],
                "killer": row["killer"],
                "class": program["class"],
                "cause": cause,
            })
        }
        FuzzJob::Rule { fired, .. } => {
            let (document, _) = crate::coverage::coverage(
                &overlay,
                &crate::coverage::CoverageOptions {
                    cache,
                    tier: crate::coverage::Tier::One,
                    ..crate::coverage::CoverageOptions::default()
                },
            );
            let program = document["programs"]
                .as_array()
                .and_then(|rows| rows.iter().find(|row| row["id"] == id))
                .cloned()
                .unwrap_or(Value::Null);
            let key = if fired { "fired_by" } else { "matched_by" };
            // The targeted rule's own item: `coverage` lists each authored rule once, by its
            // `(module, index)`. Without the resolved rule nothing is listed for the target.
            let listed = rule_at.is_some_and(|at| {
                crate::coverage::rule_item(&document, at).is_some_and(|rule| {
                    rule.get(key)
                        .and_then(Value::as_array)
                        .is_some_and(|programs| programs.iter().any(|p| p == id))
                })
            });
            // The classes `coverage` counts, by its own predicate: `comparable`, and under
            // `[observe]` `comparable-prefix` too.
            let comparable = crate::results::ResultClass::can_kill(&program["class"]);
            // `coverage` lists no program that is not comparable under any rule's `matched_by` or
            // `fired_by`, whatever its run
            // matched or fired, so such a program's status says only that it is not counted.
            json!({
                "confirmed": comparable && listed,
                "status": match (fired, comparable, listed) {
                    (_, false, _) => "not-comparable",
                    (false, true, true) => "matched",
                    (false, true, false) => "not-matched",
                    (true, true, true) => "fired",
                    (true, true, false) => "not-fired",
                },
                "reason": if !comparable {
                    "not-comparable"
                } else if listed {
                    "listed"
                } else {
                    "not-listed"
                },
                "class": program["class"],
                "cause": if program["cause"].is_null() {
                    document["spec"]["detail"].clone()
                } else {
                    program["cause"].clone()
                },
            })
        }
        FuzzJob::Refuted { .. } | FuzzJob::Cover { .. } => {
            // The obligation is named as the front end names it, so the document is the
            // front end's, at tier 1: the item's covering list reads only the baseline record.
            let (document, _) = crate::coverage::command(
                &overlay,
                &crate::coverage::CoverageOptions {
                    cache,
                    tier: crate::coverage::Tier::One,
                    ..crate::coverage::CoverageOptions::default()
                },
                confirming.front,
            );
            let program = document["programs"]
                .as_array()
                .and_then(|rows| rows.iter().find(|row| row["id"] == id))
                .cloned()
                .unwrap_or(Value::Null);
            // The classes `coverage` counts, by its own predicate: `comparable`, and under
            // `[observe]` `comparable-prefix` too.
            let comparable = crate::results::ResultClass::can_kill(&program["class"]);
            let covered = confirming
                .item
                .and_then(|item| crate::fuzz_goal::covered_by(&document, item, id));
            json!({
                "confirmed": comparable && covered == Some(true),
                "status": match (comparable, covered) {
                    (false, _) => "not-comparable",
                    (true, Some(true)) => "covered",
                    (true, _) => "not-covered",
                },
                "reason": if !comparable {
                    "not-comparable"
                } else if covered == Some(true) {
                    "listed"
                } else if covered.is_none() {
                    "unknown-item"
                } else {
                    "not-listed"
                },
                "class": program["class"],
                "cause": if program["cause"].is_null() {
                    document["spec"]["detail"].clone()
                } else {
                    program["cause"].clone()
                },
            })
        }
        FuzzJob::Pattern { list, id: pattern } => {
            let claimed = PatternList {
                patterns: list
                    .patterns
                    .iter()
                    .filter(|p| p.id == pattern)
                    .map(|p| crate::pattern::PatternEntry {
                        programs: Some(vec![id.to_owned()]),
                        // The job asks the claim of the fuzz case alone.
                        expect: None,
                        ..p.clone()
                    })
                    .collect(),
            };
            let (document, _) = crate::query::query(
                &overlay,
                &claimed,
                &crate::query::QueryOptions {
                    only: vec![pattern.to_owned()],
                    cache,
                    ..crate::query::QueryOptions::default()
                },
            );
            let row = document["rows"]
                .as_array()
                .and_then(|rows| rows.iter().find(|row| row["program"] == id))
                .cloned()
                .unwrap_or(Value::Null);
            json!({
                "confirmed": row["claim"] == "confirmed",
                "status": row["claim"],
                "reason": row["answer"],
                "answer": row["answer"],
                "cause": if row.is_null() {
                    document["spec"]["detail"].clone()
                } else {
                    row["cause"].clone()
                },
            })
        }
    }
}

#[cfg(test)]
mod streak_tests {
    use super::*;
    use k_rust_fuzz::{CaseNote, OutcomeClass, exec::UnjudgedReason};

    fn note(class: OutcomeClass, unjudged: Option<UnjudgedReason>) -> CaseNote {
        CaseNote {
            case: 0,
            class,
            unjudged,
        }
    }

    /// Of a kill job, `--open-stops` consecutive cases whose mutant run ends not-ceil-free end
    /// the search, a count and never a clock; any other case starts the count again, and a
    /// baseline-side case is not counted. Without an open limit (a rule or pattern job) none
    /// ends it.
    #[test]
    fn consecutive_not_ceil_free_mutant_cases_end_a_kill_search() {
        let open = || note(OutcomeClass::Unsupported, Some(UnjudgedReason::NotCeilFree));
        let mut streak = StackStops::new(25, 3);
        assert!(!streak.observe(&open()));
        assert!(!streak.observe(&open()));
        assert!(!streak.observe(&note(OutcomeClass::Unsupported, None)));
        assert!(!streak.all_open());
        assert!(!streak.observe(&open()));
        assert!(!streak.observe(&open()));
        assert!(!streak.observe(&note(
            OutcomeClass::BaselineIncomplete,
            Some(UnjudgedReason::NotCeilFree)
        )));
        assert!(!streak.observe(&open()));
        assert!(!streak.observe(&open()));
        assert!(streak.observe(&open()));
        assert!(streak.open_ended() && !streak.ended());

        let mut all = StackStops::new(25, 30);
        for _ in 0..4 {
            assert!(!all.observe(&open()));
        }
        assert!(all.all_open());

        let mut rule_job = StackStops::new(25, 0);
        for _ in 0..40 {
            assert!(!rule_job.observe(&open()));
        }
    }

    /// A budget stop whose every case ended holding an open application blames the mutant run
    /// only of a kill job: a rule or pattern job has no mutant.
    #[test]
    fn an_open_budget_stop_names_a_mutant_run_only_of_a_kill_job() {
        assert!(all_open_hint(true).starts_with("Every case's mutant run ended"));
        assert!(all_open_hint(false).starts_with("Every case's run ended"));
        assert!(!all_open_hint(false).contains("mutant"));
    }

    /// The statement of a search kink-flow's observer ended names the count that ended it, not a
    /// caller's cancellation.
    #[test]
    fn an_observer_stop_is_not_called_a_cancellation() {
        assert_eq!(
            observer_stopped(
                "No case witnessed it in 25 cases. The caller cancelled the campaign.",
                "--open-stops"
            ),
            "No case witnessed it in 25 cases. The search ended at its --open-stops count."
        );
    }

    /// A kill job's next steps run its own list and cache: kink-flow names the list as `run`'s
    /// operand, a front end with `--mutations`.
    #[test]
    fn a_kill_jobs_run_names_its_list_and_cache() {
        let list = ListRun {
            inner: &crate::cli::KinkFlowSpelling,
            run: crate::cli::KinkFlowSpelling
                .run_list(Path::new("other/mine.toml"), Some(Path::new("my cache"))),
        };
        assert_eq!(
            list.command(Verb::Run),
            "kink-flow run FLOW.toml other/mine.toml --cache 'my cache'"
        );
        assert_eq!(list.verb(Verb::Run), list.command(Verb::Run));
        assert_eq!(list.verb(Verb::Check), "kink-flow check");
    }
}
