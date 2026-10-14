//! The result cache (flow README 5.3): one record per program's baseline run, keyed by the
//! result schema version, the specification digest, the program digest and the budget.
//!
//! Each program runs as its own zero-mutant campaign through `kink_campaign::run_campaign_multi`
//! (the way kink-corpus admission's `baseline_only` does), with the fixed oracles of README 5.4
//! (exit stop without an exit-code cell, then the whole final term; crash policy `reject`), the
//! all-normal classifier and the manifest's budget, and every program of one command shares one
//! `NativeValidator`, so the baseline compiles once. One program's failure never touches another.
//!
//! A program is `comparable` exactly when that campaign admits its baseline run: the run is
//! complete and every oracle side is a value. Only a comparable program can later kill a mutant.
//! When the campaign refuses the baseline run, the runner returns no evidence; a diagnostic run
//! of the same initial state through the kink-native execution adapter then tells a timeout from
//! an unknown or failed run and supplies the cause, the final states and the coverage for the
//! reader. The diagnostic run never makes a program comparable.
//!
//! The cache is plain JSON under `<cache>/results/<spec digest>/<program digest>.json`. A record
//! is used only when its key equals the current key; any other record, or one that does not
//! parse, is recomputed and replaced. Deleting the cache is always safe.

use crate::{
    admit::{AdmittedSpec, ProgramInputs, admit_spec},
    digest::{program_digest, spec_digest},
    manifest::{Budget, FlowManifest, Program},
};
use k_rust::{
    definition::{AttributeKey, Sentence},
    kore::{
        ast::{Pattern, Sentence as KoreSentence},
        codec::from_value,
        parser::parse_definition,
    },
    names::KoreAttribute,
};
use kink_campaign::{
    Campaign, CampaignFailure, CampaignFailureKind, CampaignOptions, CampaignReport, CrashPolicy,
    FinalResult, OracleDeclaration, OracleSide, OracleValue, Projection, ScheduleMode, SideRun,
    StateProjection, TestCase, run_campaign_multi,
};
use kink_corpus::{
    Store, admission::AdmissionRecord, admission::input_backend, runner::all_normal,
};
use kink_native::{
    K_RUST_REVISION,
    coverage::{RuleAuthors, TestCoverage},
    execution::{ExecutionAdapter, ExecutionBudget, HaltClass, SolverProfile},
};
use kink_patch::{
    CandidateGeneration, Discovery, Patch, SelectionPolicy, SentenceRef, Sha256Digest,
    canonical_json, payload_digest, select,
};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    time::Duration,
};

/// The result schema version, the first component of every result key. It changes whenever
/// kink changes what counts as a comparable result (for example when ground collections are
/// admitted), so that older records are recomputed rather than trusted.
pub const RESULT_SCHEMA_VERSION: &str = "kink-flow/result/v1";
/// The `schema` field of a result record.
pub const RECORD_SCHEMA: &str = "kink-flow-result";
/// Domain of a run digest: the digest of the `run` part of a baseline row.
pub const RUN_DOMAIN: &str = "kink-flow/run/v1";
/// The cache directory's name next to `FLOW.toml`.
pub const CACHE_DIRECTORY: &str = ".kink-flow";
/// Simplifier iterations per rewrite step of every program run (not a manifest key).
pub const SIMPLIFICATION_ITERATIONS: usize = 10_000;
/// The operator name of the empty generation each zero-mutant campaign runs.
const BASELINE_ONLY_OPERATOR: &str = "kink-flow/baseline-only/v1";

/// The class of a program's baseline run (README 5.3).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResultClass {
    /// The baseline run is complete and every oracle side is a value: the program can kill.
    Comparable,
    /// The run did not finish within the budget's time.
    Timeout,
    /// The run produced no comparable value (for example a Map in the final configuration,
    /// a depth limit, or an undecided step).
    Unknown,
    /// The program's input was refused (not read, parsed or assembled); never stored.
    Refused,
    /// The run or the runner failed.
    Error,
}

impl ResultClass {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Comparable => "comparable",
            Self::Timeout => "timeout",
            Self::Unknown => "unknown",
            Self::Refused => "refused",
            Self::Error => "error",
        }
    }
}

/// The names of the oracle slots of [`fixed_oracles`], in slot order.
pub const ORACLE_SLOTS: [&str; 2] = ["exit-stop", "whole-term"];

/// The two oracles of every flow program (README 5.4): the exit stop with no exit-code cell,
/// then the whole final term; a semantic crash is outside the operand domain (`reject`).
pub fn fixed_oracles() -> Vec<OracleDeclaration> {
    [
        StateProjection::ExitStop {
            exit_code_cell: None,
        },
        StateProjection::WholeTerm,
    ]
    .into_iter()
    .map(|projection| {
        OracleDeclaration::new(CrashPolicy::Reject, Projection::State(projection))
            .expect("state projections without term paths are valid")
    })
    .collect()
}

/// The execution budget of every program run.
pub fn execution_budget(budget: Budget) -> ExecutionBudget {
    ExecutionBudget {
        time: Duration::from_millis(budget.time_ms),
        max_simplification_iterations: SIMPLIFICATION_ITERATIONS,
        max_depth: Some(budget.max_depth),
        max_breadth: None,
    }
}

/// The result key: schema version, specification digest, program digest and budget.
pub fn result_key(spec: Sha256Digest, program: Sha256Digest, budget: Budget) -> Value {
    json!({
        "schema_version": RESULT_SCHEMA_VERSION,
        "spec": spec.to_string(),
        "program": program.to_string(),
        "budget": {
            "time_ms": budget.time_ms,
            "max_depth": budget.max_depth,
            "max_simplification_iterations": SIMPLIFICATION_ITERATIONS,
            "max_breadth": null,
        },
    })
}

/// The digest of a baseline row's `run` part, which depends neither on the program id nor on
/// any other test of the campaign. `None` when the row has no `run`.
pub fn run_digest(row: &Value) -> Option<Sha256Digest> {
    let run = row.get("run")?;
    Some(payload_digest(RUN_DOMAIN, canonical_json(run).as_bytes()))
}

/// What one program's baseline run produced.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramResult {
    pub class: ResultClass,
    pub cause: Option<String>,
    /// The baseline row exactly as kink-campaign's report encodes it; comparable only.
    pub baseline: Option<Value>,
    /// The final configurations as KORE text, one per terminal (comparable), or the final
    /// state of each leaf of the diagnostic run (unknown and error runs that have leaves).
    pub final_configuration: Option<Vec<String>>,
    /// The run's rule coverage; `None` when no run produced any.
    pub coverage: Option<TestCoverage>,
}

impl ProgramResult {
    fn refused(cause: String) -> Self {
        Self {
            class: ResultClass::Refused,
            cause: Some(cause),
            baseline: None,
            final_configuration: None,
            coverage: None,
        }
    }

    /// The run digest of the baseline row.
    pub fn run_sha256(&self) -> Option<Sha256Digest> {
        self.baseline.as_ref().and_then(run_digest)
    }
}

/// Runs programs of one admitted specification, each as its own zero-mutant campaign, with one
/// validator (the specification's), so the baseline compiles once.
pub struct BaselineRunner<'a> {
    spec: &'a AdmittedSpec,
    main_module: &'a str,
    module: String,
    generations: Vec<CandidateGeneration<'a>>,
    budget: ExecutionBudget,
    authors: RuleAuthors,
}

impl<'a> BaselineRunner<'a> {
    pub fn new(spec: &'a AdmittedSpec, manifest: &'a FlowManifest) -> Result<Self, String> {
        // The runner needs a generation. A checked empty discovery yields zero candidates,
        // so no operator code and no mutant can be reached (kink-corpus `baseline_only`).
        let discovery = Discovery::empty(spec.validator.baseline(), false, false);
        let generation = select(&discovery, SelectionPolicy::Each, 1)
            .and_then(|selection| {
                selection.fold(BASELINE_ONLY_OPERATOR, |_| -> Patch {
                    unreachable!("an empty discovery has no fold calls")
                })
            })
            .map_err(|e| format!("cannot build the empty generation: {e}"))?;
        assert!(generation.candidates().is_empty());
        Ok(Self {
            spec,
            main_module: &manifest.spec.main_module,
            module: k_rust::kast::identifier::encode(&manifest.spec.main_module),
            generations: vec![generation],
            budget: execution_budget(manifest.budget),
            authors: RuleAuthors::of(&spec.compiled),
        })
    }

    /// Run one admitted program (its oracles are replaced by [`fixed_oracles`]).
    pub fn run(&self, mut test: TestCase) -> ProgramResult {
        test.oracles = fixed_oracles();
        let campaign = Campaign {
            validator: &self.spec.validator,
            module: &self.module,
            observation: &[],
            classify: &all_normal,
            tests: std::slice::from_ref(&test),
            budget: self.budget,
        };
        let options = CampaignOptions {
            schedule: ScheduleMode::FirstKill,
            selection: kink_campaign::SelectionPolicy::None,
            share_evidence: true,
        };
        match run_campaign_multi(&campaign, &self.generations, &options) {
            Ok(run) => {
                assert!(run.mutants.is_empty() && run.baseline.len() == 1);
                let evidence = &run.baseline[0];
                let row = match CampaignReport::baseline_row(evidence) {
                    Ok(row) => row,
                    Err(e) => return self.error(format!("cannot encode the baseline row: {e}")),
                };
                ProgramResult {
                    class: ResultClass::Comparable,
                    cause: None,
                    baseline: Some(row),
                    final_configuration: final_terms(&evidence.run),
                    coverage: run.baseline_coverage.first().cloned(),
                }
            }
            Err(failure) => self.diagnose(&test, &failure),
        }
    }

    fn error(&self, cause: String) -> ProgramResult {
        ProgramResult {
            class: ResultClass::Error,
            cause: Some(cause),
            baseline: None,
            final_configuration: None,
            coverage: None,
        }
    }

    /// The campaign refused the baseline run: run the initial state once more through the
    /// execution adapter, for the class, the cause, the final states and the coverage.
    fn diagnose(&self, test: &TestCase, failure: &CampaignFailure) -> ProgramResult {
        let refused = format!("the campaign runner refused the baseline run ({failure})");
        let mut backend = match input_backend(&self.spec.compiled, self.main_module) {
            Ok(backend) => backend,
            Err(e) => return self.error(format!("{refused}; no diagnostic run: {}", e.detail)),
        };
        let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
        let execution = match adapter.execute(&mut backend, &test.initial_state, self.budget) {
            Ok(execution) => execution,
            Err(e) => return self.error(format!("{refused}; the diagnostic run failed: {e:?}")),
        };
        let coverage = Some(TestCoverage::of_execution(
            &test.id,
            &execution,
            &self.authors,
        ));
        if execution.timed_out() {
            return ProgramResult {
                class: ResultClass::Timeout,
                cause: Some(format!(
                    "the run did not finish within time_ms = {}",
                    self.budget.time.as_millis()
                )),
                baseline: None,
                final_configuration: None,
                coverage,
            };
        }
        let leaves = execution.leaves();
        let class = match failure.kind() {
            CampaignFailureKind::BaselineOracleFailed => ResultClass::Unknown,
            _ => ResultClass::Error,
        };
        let halts = leaves
            .iter()
            .map(|leaf| {
                format!(
                    "{} at depth {}",
                    kebab(&format!("{:?}", leaf.halt)),
                    leaf.branch.depth
                )
            })
            .collect::<Vec<_>>();
        let hint = if leaves.iter().any(|leaf| leaf.halt == HaltClass::DepthBound) {
            format!(
                "the run reached max_depth = {}",
                self.budget.max_depth.unwrap_or_default()
            )
        } else if !leaves.is_empty()
            && leaves.iter().all(|leaf| {
                matches!(
                    leaf.halt,
                    HaltClass::Stuck | HaltClass::Trivial | HaltClass::Vacuous
                )
            })
        {
            "every path ended, but a final configuration is not a value kink can compare \
             (for example it holds a Map, Set or List, an unevaluated function or a symbolic term)"
                .to_owned()
        } else {
            "a path did not end".to_owned()
        };
        let final_configuration = leaves
            .iter()
            .map(|leaf| from_value(&leaf.branch.state).map(|state| state.to_string()))
            .collect::<Result<Vec<_>, _>>()
            .ok();
        ProgramResult {
            class,
            cause: Some(format!(
                "{refused}; {hint}; leaves: {}",
                if halts.is_empty() {
                    "none".to_owned()
                } else {
                    halts.join(", ")
                }
            )),
            baseline: None,
            final_configuration,
            coverage,
        }
    }
}

pub(crate) fn kebab(name: &str) -> String {
    let mut out = String::new();
    for (index, c) in name.chars().enumerate() {
        if index > 0 && c.is_uppercase() {
            out.push('-');
        }
        out.extend(c.to_lowercase());
    }
    out
}

/// The whole-term side's terminal terms as KORE text.
fn final_terms(run: &SideRun) -> Option<Vec<String>> {
    let SideRun::Sides { sides } = run else {
        return None;
    };
    sides.iter().find_map(|side| match side {
        OracleSide::Normal(OracleValue::FinalResult(FinalResult::WholeTerm(terms))) => {
            Some(terms.iter().map(ToString::to_string).collect())
        }
        _ => None,
    })
}

/// A sentence's source position: `{module, index, label, file, start_line, end_line}`.
pub fn sentence_value(spec: &AdmittedSpec, at: &SentenceRef) -> Value {
    let sentence = spec.loaded.baseline.sentence(at);
    let attributes = sentence.map(Sentence::attributes);
    let location = attributes.and_then(|a| a.location());
    json!({
        "module": at.module,
        "index": at.index,
        "label": attributes.and_then(|a| a.string(AttributeKey::Label)),
        "file": attributes.and_then(|a| a.source()),
        "start_line": location.map(|l| l.start_line),
        "end_line": location.map(|l| l.end_line),
    })
}

fn coverage_value(spec: &AdmittedSpec, coverage: &TestCoverage) -> Value {
    json!({
        "complete": coverage.complete,
        "sentences": coverage
            .sentences
            .iter()
            .map(|at| sentence_value(spec, at))
            .collect::<Vec<_>>(),
    })
}

/// The result record of one program (never for a refused program).
pub fn record_value(spec: &AdmittedSpec, key: &Value, id: &str, result: &ProgramResult) -> Value {
    json!({
        "schema": RECORD_SCHEMA,
        "key": key,
        "program_id": id,
        "class": result.class.as_str(),
        "cause": result.cause,
        "baseline": result.baseline,
        "run_sha256": result.run_sha256().map(|d| d.to_string()),
        "final_configuration": result.final_configuration,
        "coverage": result.coverage.as_ref().map(|c| coverage_value(spec, c)),
    })
}

/// A stored record: `None` when the file is absent; `Some(None)` when it exists but does not
/// parse or has another schema or key (it is then recomputed, never used).
fn read_record(path: &Path, key: &Value) -> Option<Option<Value>> {
    let text = fs::read_to_string(path).ok()?;
    Some(
        serde_json::from_str::<Value>(&text)
            .ok()
            .filter(|record| record["schema"] == RECORD_SCHEMA && record["key"] == *key),
    )
}

/// How `--verify` compares a stored record with a new run of its program: every difference,
/// including a record whose `run_sha256` is not the digest of its own baseline row.
fn verify_record(record: &Value, result: &ProgramResult) -> Vec<String> {
    let mut differences = Vec::new();
    let stored_digest = record["run_sha256"].as_str();
    let row_digest = record
        .get("baseline")
        .filter(|row| !row.is_null())
        .and_then(run_digest)
        .map(|d| d.to_string());
    if stored_digest != row_digest.as_deref() {
        differences.push(format!(
            "the record's run_sha256 {} is not the digest of its baseline row ({})",
            stored_digest.unwrap_or("null"),
            row_digest.as_deref().unwrap_or("no row"),
        ));
    }
    if record["class"] != result.class.as_str() {
        differences.push(format!(
            "class: cached {}, now {}",
            record["class"],
            result.class.as_str()
        ));
    }
    let now = result.run_sha256().map(|d| d.to_string());
    if stored_digest != now.as_deref() {
        differences.push(format!(
            "run_sha256: cached {}, now {}",
            stored_digest.unwrap_or("null"),
            now.as_deref().unwrap_or("null"),
        ));
    }
    differences
}

/// Options of the `results` command.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ResultsOptions {
    /// Re-run every program that has a current record and compare (README 5.3).
    pub verify: bool,
    /// The cache directory; default `<directory of FLOW.toml>/.kink-flow`.
    pub cache: Option<PathBuf>,
}

/// One program's row of the results document, with its record when it has one.
pub struct ProgramRow {
    /// The program's row of the results document.
    pub row: Value,
    /// The program's current record (stored or just written), if it has one.
    pub record: Option<Value>,
    /// The program was refused, its run failed or its record could not be written.
    pub failed: bool,
    /// The program's digest, when its text could be read.
    pub digest: Option<Sha256Digest>,
    /// The program's text exactly as its digest was computed from it.
    pub text: Option<String>,
    /// The program's admitted test case (no oracles), when this command assembled it.
    pub test: Option<TestCase>,
}

impl ProgramRow {
    /// The record's class, when the program has a record.
    pub fn class(&self) -> Option<&str> {
        self.record
            .as_ref()
            .and_then(|record| record["class"].as_str())
    }
}

/// The result cache brought up to date for one admitted specification (`results` without
/// the document): one row per manifest program, in manifest order.
pub struct ResultsUpdate {
    pub spec_digest: Sha256Digest,
    pub rows: Vec<ProgramRow>,
    pub mismatches: Vec<Value>,
}

impl ResultsUpdate {
    /// No program was refused or failed and `--verify` found no mismatch.
    pub fn ok(&self) -> bool {
        self.rows.iter().all(|row| !row.failed) && self.mismatches.is_empty()
    }
}

/// The cache directory of a manifest: `options.cache`, else `.kink-flow` next to it.
pub fn cache_directory(manifest: &FlowManifest, cache: Option<&Path>) -> PathBuf {
    cache.map_or_else(
        || manifest.directory.join(CACHE_DIRECTORY),
        Path::to_path_buf,
    )
}

/// The refusal of a specification whose baseline runner cannot be built.
pub fn runner_refusal(detail: String) -> kink_corpus::admission::AdmissionRefusal {
    kink_corpus::admission::AdmissionRefusal {
        stage: "baseline".into(),
        reason: "invalid-declaration".into(),
        detail,
    }
}

/// Bring the result cache of `spec` up to date (README 5.3) with `runner`, whose validator
/// is the specification's, so every program shares one baseline compile.
pub fn update_results(
    spec: &AdmittedSpec,
    manifest: &FlowManifest,
    inputs: &mut ProgramInputs,
    runner: &BaselineRunner<'_>,
    cache: &Path,
    verify: bool,
) -> ResultsUpdate {
    let spec_digest = spec_digest(manifest, &spec.loaded.files);
    let store = Store::new(cache);
    let directory = cache.join("results").join(spec_digest.to_string());
    let mut mismatches = Vec::new();
    let rows = manifest
        .programs
        .iter()
        .map(|program| {
            program_row(
                spec,
                manifest,
                inputs,
                runner,
                &ProgramContext {
                    spec_digest,
                    directory: &directory,
                    cache,
                    store: &store,
                    verify,
                },
                program,
                &mut mismatches,
            )
        })
        .collect::<Vec<_>>();
    ResultsUpdate {
        spec_digest,
        rows,
        mismatches,
    }
}

/// `kink-flow results`: the results document and whether the command found no corpus or
/// infrastructure error (the caller's exit status).
pub fn results(manifest: &FlowManifest, options: &ResultsOptions) -> (Value, bool) {
    let (mut record, admitted) = admit_spec(manifest);
    let Some((spec, mut inputs)) = admitted else {
        return (
            document(&record, None, Vec::new(), Vec::new(), Vec::new()),
            false,
        );
    };
    let cache = cache_directory(manifest, options.cache.as_deref());
    let runner = match BaselineRunner::new(&spec, manifest) {
        Ok(runner) => runner,
        Err(e) => {
            record.refusal = Some(runner_refusal(e));
            return (
                document(&record, None, Vec::new(), Vec::new(), Vec::new()),
                false,
            );
        }
    };
    let update = update_results(
        &spec,
        manifest,
        &mut inputs,
        &runner,
        &cache,
        options.verify,
    );
    let ok = update.ok();
    let rules = rules(&spec, manifest, &update.rows);
    let programs = update.rows.into_iter().map(|row| row.row).collect();
    (
        document(
            &record,
            Some(update.spec_digest),
            programs,
            rules,
            update.mismatches,
        ),
        ok,
    )
}

struct ProgramContext<'a> {
    spec_digest: Sha256Digest,
    directory: &'a Path,
    cache: &'a Path,
    store: &'a Store,
    verify: bool,
}

fn program_row(
    spec: &AdmittedSpec,
    manifest: &FlowManifest,
    inputs: &mut ProgramInputs,
    runner: &BaselineRunner<'_>,
    context: &ProgramContext<'_>,
    program: &Program,
    mismatches: &mut Vec<Value>,
) -> ProgramRow {
    let row = |digest: Option<Sha256Digest>, class: &str, cause: &Value, cached, verify: Value| {
        json!({
            "id": program.id,
            "digest": digest.map(|d| d.to_string()),
            "class": class,
            "cause": cause,
            "cached": cached,
            "verify": verify,
        })
    };
    let refused = |digest, refusal: kink_corpus::admission::AdmissionRefusal| {
        let result = ProgramResult::refused(format!(
            "{}/{}: {}",
            refusal.stage, refusal.reason, refusal.detail
        ));
        ProgramRow {
            row: row(
                digest,
                result.class.as_str(),
                &json!(result.cause),
                false,
                Value::Null,
            ),
            record: None,
            failed: true,
            digest,
            text: None,
            test: None,
        }
    };
    let text = match inputs.text(program) {
        Ok(text) => text,
        Err(refusal) => return refused(None, refusal),
    };
    let digest = program_digest(program, &text);
    let key = result_key(context.spec_digest, digest, manifest.budget);
    let path = context.directory.join(format!("{digest}.json"));
    let stored = read_record(&path, &key).flatten();
    if let (Some(record), false) = (&stored, context.verify) {
        return ProgramRow {
            row: row(
                Some(digest),
                record["class"].as_str().unwrap_or("error"),
                &record["cause"],
                true,
                Value::Null,
            ),
            failed: record["class"] == ResultClass::Error.as_str(),
            record: stored,
            digest: Some(digest),
            text: Some(text),
            test: None,
        };
    }
    let test = match inputs.test_case(spec, program, text.clone()) {
        Ok(test) => test,
        Err(refusal) => return refused(Some(digest), refusal),
    };
    let result = runner.run(test.clone());
    if let Some(record) = stored {
        let differences = verify_record(&record, &result);
        let relative = path
            .strip_prefix(context.cache)
            .unwrap_or(&path)
            .to_string_lossy()
            .into_owned();
        for detail in &differences {
            mismatches.push(json!({"program": program.id, "record": relative, "detail": detail}));
        }
        let verdict = if differences.is_empty() {
            "match"
        } else {
            "mismatch"
        };
        return ProgramRow {
            row: row(
                Some(digest),
                record["class"].as_str().unwrap_or("error"),
                &record["cause"],
                true,
                json!(verdict),
            ),
            failed: record["class"] == ResultClass::Error.as_str(),
            record: Some(record),
            digest: Some(digest),
            text: Some(text),
            test: Some(test),
        };
    }
    let record = record_value(spec, &key, &program.id, &result);
    let mut row = row(
        Some(digest),
        result.class.as_str(),
        &json!(result.cause),
        false,
        Value::Null,
    );
    let mut failed = result.class == ResultClass::Error;
    if let Err(e) = context.store.write_json(&path, &record) {
        row["cache_error"] = json!(format!("cannot write the result record: {e}"));
        failed = true;
    }
    ProgramRow {
        row,
        record: Some(record),
        failed,
        digest: Some(digest),
        text: Some(text),
        test: Some(test),
    }
}

/// Every authored rule of the specification, with the comparable programs whose coverage
/// reaches it: uncovered rules first, then covered rules, then the rules no run can observe
/// (equations and rules that compile to no rewrite rule; coverage sees only rewrite steps).
fn rules(spec: &AdmittedSpec, manifest: &FlowManifest, rows: &[ProgramRow]) -> Vec<Value> {
    let mut reached = BTreeMap::<(String, u64), Vec<&str>>::new();
    for (program, row) in manifest.programs.iter().zip(rows) {
        let Some(record) = &row.record else {
            continue;
        };
        if record["class"] != ResultClass::Comparable.as_str() {
            continue;
        }
        let sentences = record["coverage"]["sentences"].as_array();
        for sentence in sentences.into_iter().flatten() {
            if let (Some(module), Some(index)) =
                (sentence["module"].as_str(), sentence["index"].as_u64())
            {
                reached
                    .entry((module.to_owned(), index))
                    .or_default()
                    .push(&program.id);
            }
        }
    }
    let rewrites = rewrite_rule_ids(&spec.compiled.artifacts().definition_kore);
    let authors = RuleAuthors::of(&spec.compiled);
    let mut groups: [Vec<Value>; 3] = Default::default();
    for (at, sentence) in spec.loaded.baseline.authored_sentences() {
        if !matches!(sentence, Sentence::Rule { .. }) {
            continue;
        }
        let ids = authors.ids_of(&at).collect::<Vec<_>>();
        let mut value = sentence_value(spec, &at);
        let programs = reached
            .get(&(at.module.clone(), u64::from(at.index)))
            .cloned()
            .unwrap_or_default();
        let (group, status) = if !ids.iter().any(|id| rewrites.contains(*id)) {
            (2, "not-observable")
        } else if programs.is_empty() {
            (0, "uncovered")
        } else {
            (1, "covered")
        };
        value["status"] = json!(status);
        value["reached_by"] = json!(programs);
        if status == "not-observable" {
            value["reason"] = json!(if ids.is_empty() {
                "compiles to no rule"
            } else {
                "equation: coverage sees rewrite steps only"
            });
        }
        groups[group].push(value);
    }
    groups.into_iter().flatten().collect()
}

/// The `UNIQUE_ID`s of the rewrite axioms of compiled KORE: the rules a run's trace can
/// name. Equations (`\equals` axioms of functions, `anywhere` and macro rules) never appear in
/// a trace (kink-native coverage.rs, ticket CS-T09). Unparsable KORE gives no id, so every rule
/// is then reported as not observable rather than as uncovered.
fn rewrite_rule_ids(kore: &str) -> BTreeSet<String> {
    let Ok(definition) = parse_definition(kore) else {
        return BTreeSet::new();
    };
    definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            KoreSentence::Axiom {
                pattern,
                attributes,
                ..
            } if matches!(pattern.as_ref(), Pattern::Rewrites { .. }) => {
                attributes.0.iter().find_map(|attribute| match attribute {
                    Pattern::Application { symbol, arguments }
                        if symbol.name == KoreAttribute::UniqueId.as_str() =>
                    {
                        match arguments.as_slice() {
                            [Pattern::String(id)] => id.as_utf8().ok().map(str::to_owned),
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

fn document(
    record: &AdmissionRecord,
    digest: Option<Sha256Digest>,
    programs: Vec<Value>,
    rules: Vec<Value>,
    mismatches: Vec<Value>,
) -> Value {
    let refusal = record.refusal.as_ref();
    let count = |status: &str| rules.iter().filter(|r| r["status"] == status).count();
    let summary = json!({
        "programs": programs.len(),
        "comparable": programs.iter().filter(|p| p["class"] == "comparable").count(),
        "computed": programs.iter().filter(|p| p["cached"] == false).count(),
        "rules": rules.len(),
        "uncovered": count("uncovered"),
        "covered": count("covered"),
        "not_observable": count("not-observable"),
        "mismatches": mismatches.len(),
    });
    json!({
        "schema": "kink-flow-results",
        "version": 1,
        "k_rust_revision": K_RUST_REVISION,
        "profile": SolverProfile::BUILD.name(),
        "result_schema_version": RESULT_SCHEMA_VERSION,
        "spec": {
            "outcome": if refusal.is_some() { "refused" } else { "admitted" },
            "stage": refusal.map(|r| &r.stage),
            "reason": refusal.map(|r| &r.reason),
            "detail": refusal.map(|r| &r.detail),
            "digest": digest.map(|d| d.to_string()),
            "files": record
                .files
                .iter()
                .map(|f| json!({"name": f.name, "sha256": f.sha256.to_string()}))
                .collect::<Vec<_>>(),
        },
        "programs": programs,
        "rules": rules,
        "mismatches": mismatches,
        "summary": summary,
    })
}
