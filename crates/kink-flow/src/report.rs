//! The survivor report (flow README 5.7): what the run document says about each mutation that
//! no program killed, and the `report` command, which prints the last run's document again.
//!
//! The run document (`kink-flow run`, [`crate::search`]) is the report. Beyond the kill
//! search's own fields it carries, for every mutation that is not `killed`, what an LLM needs to
//! write a program that kills it:
//!
//! - `rules`: each edited rule's file, lines, label and K text before and after the edit,
//!   sliced from the file's K view by the sentence's span (F-04's [`EditedRule`], F-10's view),
//!   so no K printer is involved and the text is exactly what the specification and the
//!   mutation list say;
//! - `reaching`: the comparable programs whose cached coverage reaches an edited rule;
//! - `executed`: each program the mutant ran on, with its outcome and, when the outcome is
//!   neither `agree` nor `distinguish`, a `cause` read from the runner's evidence for that run;
//! - `action`: what the status asks of the LLM.
//!
//! At the top level, `survivors` names the mutations no program killed that a new program could
//! kill (status `survived`, `timeout` or `unknown`), and `unusable_programs` lists once every
//! program that cannot kill (its result class is not `comparable`), with its class and cause.
//!
//! Nothing here reads or changes a verdict: every status is the kill search's, which is the
//! campaign runner's fold over live and cached outcomes (README 7.5.3).

use crate::{
    manifest::{Budget, FlowManifest},
    mutation::{EditedRule, ResolvedMutation},
    results::{ORACLE_SLOTS, ResultClass, cache_directory},
    search::REPORT_FILE,
};
use kink_campaign::{ExecutionFailureKind, OracleOutcome, OracleSide, SideRun, TestRun};
use kink_native::{K_RUST_REVISION, execution::SolverProfile};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
};

/// The `schema` of the run document, which is also the report.
pub const RUN_SCHEMA: &str = "kink-flow-run";
/// The run document's version: 2 since F-06 added the survivor fields.
pub const RUN_VERSION: u64 = 2;
/// The `schema` of the document `report` prints when there is no report to print.
pub const MISSING_SCHEMA: &str = "kink-flow-report";

/// The statuses of a survivor: no program killed the mutation, and a new program could.
pub const SURVIVOR_STATUSES: [&str; 3] = ["survived", "timeout", "unknown"];

/// The document's text on stdout, for `run` and `report` alike, so that `report` prints the
/// bytes `run` printed.
pub fn render(document: &Value) -> String {
    serde_json::to_string_pretty(document).expect("JSON values encode")
}

/// One edited rule of a mutation: `{module, index, file, label, start_line, end_line, edits,
/// before, after}`; `after` is null for a deleted rule.
pub fn rule_value(rule: &EditedRule) -> Value {
    json!({
        "module": rule.at.module,
        "index": rule.at.index,
        "file": rule.file,
        "label": rule.label,
        "start_line": rule.start_line,
        "end_line": rule.end_line,
        "edits": rule.edits,
        "before": rule.before,
        "after": rule.after,
    })
}

/// The `rules` of a resolved mutation, in sentence order.
pub fn rules_value(resolved: &ResolvedMutation) -> Value {
    Value::Array(resolved.rules.iter().map(rule_value).collect())
}

/// What a status asks of the LLM; `None` for `killed`. `reason` refines `error`.
pub fn action(status: &str, reason: Option<&str>) -> Option<&'static str> {
    Some(match status {
        "killed" => return None,
        "survived" => {
            "write a program that reaches an edited rule and whose final configuration the edit \
             changes: every executed program reached a comparable result and agreed"
        }
        "timeout" => {
            "write a program that ends under the mutant within budget.time_ms with a different \
             final configuration: a program did not end on the mutant, and no program killed it"
        }
        "unknown" => {
            "write a program whose final configuration under the mutant kink can compare: the \
             cause of each executed program says what stopped the comparison"
        }
        "equivalent" => {
            "nothing can kill it: the mutant compiles to the baseline's definition; drop or \
             change the mutation"
        }
        "invalid" => "fix the mutation: the mutant does not compile (reason)",
        "invalid-mutation" => "fix the mutation: it does not resolve (reason, edit, detail)",
        "error" if reason == Some("outcome-conflict") => {
            "check the outcome cache: a cached agreement says the mutant ran, a live call says it \
             did not; run `kink-flow run FLOW.toml MUTATIONS.toml --verify`"
        }
        "error" if reason.is_some_and(is_corpus_error) => {
            "fix the corpus: a cached result no longer describes its program's baseline run; \
             run `kink-flow results FLOW.toml --verify`"
        }
        "error" if reason == Some("no-comparable-program") => {
            "write a program whose baseline result is comparable: no program can kill yet"
        }
        "error" if reason.is_some_and(|r| r.starts_with("outcome-mismatch:")) => {
            "report it: a cached outcome differs from a live run of the same inputs (top-level \
             mismatches); delete the cache's outcomes/ directory to stop trusting it"
        }
        _ => "report it: the runner failed for the mutant (reason)",
    })
}

fn is_corpus_error(reason: &str) -> bool {
    reason.starts_with("baseline-mismatch:")
        || reason.starts_with("program-refused:")
        || reason == "baseline-count-mismatch"
        || reason == "campaign-refused"
        || reason == "outcome-conflict"
}

/// The `cause` of an executed program's outcome on the mutant, from the runner's evidence for
/// that run: `None` when the outcome is `agree` or `distinguish` (or the test was skipped).
pub fn executed_cause(run: &TestRun, mutant: Option<&SideRun>, budget: Budget) -> Option<String> {
    match run {
        TestRun::SkippedAfterKill => None,
        TestRun::Failed(kind) => Some(failure_cause(*kind, budget)),
        TestRun::Compared(outcomes) => {
            if outcomes.contains(&OracleOutcome::Distinguish)
                || outcomes
                    .iter()
                    .all(|outcome| *outcome == OracleOutcome::Agree)
            {
                return None;
            }
            let sides = match mutant {
                Some(SideRun::Sides { sides }) => sides.as_slice(),
                _ => &[],
            };
            // Slots with the same cause are named together: `exit-stop, whole-term: <cause>`.
            let mut groups: Vec<(Vec<&str>, String)> = Vec::new();
            for (slot, outcome) in outcomes.iter().enumerate() {
                if *outcome == OracleOutcome::Agree {
                    continue;
                }
                let name = ORACLE_SLOTS.get(slot).copied().unwrap_or("slot");
                let cause = slot_cause(*outcome, sides.get(slot), budget);
                match groups.iter_mut().find(|(_, existing)| *existing == cause) {
                    Some((names, _)) => names.push(name),
                    None => groups.push((vec![name], cause)),
                }
            }
            Some(
                groups
                    .iter()
                    .map(|(names, cause)| format!("{}: {cause}", names.join(", ")))
                    .collect::<Vec<_>>()
                    .join("; "),
            )
        }
    }
}

fn failure_cause(kind: ExecutionFailureKind, budget: Budget) -> String {
    match kind {
        ExecutionFailureKind::TimeLimit => format!(
            "the mutant's run did not end within time_ms = {}",
            budget.time_ms
        ),
        ExecutionFailureKind::ResourceLimit => format!(
            "a resource bound stopped the mutant's run (max_depth = {}, or the simplifier's \
             bound)",
            budget.max_depth
        ),
        ExecutionFailureKind::Indeterminate => {
            "the mutant's run could not decide how to proceed (for example an undecided side \
             condition)"
                .into()
        }
        ExecutionFailureKind::Infrastructure => "the backend failed during the mutant's run".into(),
        ExecutionFailureKind::UnsupportedClaims => {
            "the mutant's run was not started: it writes a trusted claim".into()
        }
    }
}

/// Why one oracle slot neither agreed nor distinguished. The baseline side of a comparable
/// program is always a value, so the mutant's side says why.
fn slot_cause(outcome: OracleOutcome, mutant: Option<&OracleSide>, budget: Budget) -> String {
    match mutant {
        Some(OracleSide::Timeout) => format!(
            "a path of the mutant's run did not end within time_ms = {}",
            budget.time_ms
        ),
        Some(OracleSide::Unknown) => format!(
            "the mutant's run did not end in a value kink can compare (a path stopped at \
             max_depth = {} or ended undecided, or a final configuration holds a collection kink \
             cannot compare, such as one with a Bytes key, an unevaluated function or a symbolic term)",
            budget.max_depth
        ),
        Some(OracleSide::Error) => "the backend failed while running the mutant".into(),
        Some(OracleSide::SemanticCrash(_)) => {
            "the mutant's run ended in a semantic crash, which the flow does not compare".into()
        }
        Some(OracleSide::Normal(_)) | None => match outcome {
            OracleOutcome::Incomparable => {
                "the baseline and mutant values are of kinds the oracle cannot compare".into()
            }
            OracleOutcome::Timeout => "the comparison ran out of time".into(),
            OracleOutcome::Unknown => "the comparison was undecided".into(),
            _ => "the comparison failed".into(),
        },
    }
}

/// The ids of the survivors among the document's mutation rows, in run order.
pub fn survivors(mutations: &[Value]) -> Vec<Value> {
    mutations
        .iter()
        .filter(|row| {
            SURVIVOR_STATUSES
                .iter()
                .any(|status| row["status"] == *status)
        })
        .map(|row| row["id"].clone())
        .collect()
}

/// Every program that cannot kill (its result class is not `comparable`), once, from the
/// `results` rows: `{id, class, cause}`.
pub fn unusable_programs(programs: &[Value]) -> Vec<Value> {
    programs
        .iter()
        .filter(|row| row["class"] != ResultClass::Comparable.as_str())
        .map(|row| json!({"id": row["id"], "class": row["class"], "cause": row["cause"]}))
        .collect()
}

/// Options of the `report` command.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ReportOptions {
    /// The cache directory; default `<directory of FLOW.toml>/.kink-flow`.
    pub cache: Option<PathBuf>,
}

/// `kink-flow report`: the stored run document, exactly as `run` last wrote it, or a
/// `kink-flow-report` document saying why there is none; and whether there was one.
pub fn report(manifest: &FlowManifest, options: &ReportOptions) -> (Value, bool) {
    let path = cache_directory(manifest, options.cache.as_deref()).join(REPORT_FILE);
    match read_report(&path) {
        Ok(document) => (document, true),
        Err((outcome, detail)) => (
            json!({
                "schema": MISSING_SCHEMA,
                "version": 1,
                "k_rust_revision": K_RUST_REVISION,
                "profile": SolverProfile::BUILD.name(),
                "outcome": outcome,
                "path": path.display().to_string(),
                "detail": detail,
            }),
            false,
        ),
    }
}

/// The stored run document, or `(outcome, detail)` with outcome `missing` or `unreadable`.
fn read_report(path: &Path) -> Result<Value, (&'static str, String)> {
    let text = fs::read_to_string(path).map_err(|e| {
        (
            "missing",
            format!("no run report ({e}): run `kink-flow run FLOW.toml MUTATIONS.toml` first"),
        )
    })?;
    let document = serde_json::from_str::<Value>(&text)
        .map_err(|e| ("unreadable", format!("the report is not JSON: {e}")))?;
    if document["schema"] != RUN_SCHEMA || document["version"] != RUN_VERSION {
        return Err((
            "unreadable",
            format!(
                "the report has schema {} version {}, not {RUN_SCHEMA} version {RUN_VERSION}: \
                 run `kink-flow run` again",
                document["schema"], document["version"]
            ),
        ));
    }
    Ok(document)
}
