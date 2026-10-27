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
//! - `reaching`: the comparable programs whose cached coverage witnesses an edited rule's edit:
//!   programs that reached the rule (k-rust `matched`) for an edit of its `requires`, programs
//!   that fired it (`applied`) for any other edit (re-pin L2-1-tail);
//! - `executed`: each program the mutant ran on, with its outcome and, when the outcome is
//!   neither `agree` nor `distinguish`, a `cause` read from the runner's evidence for that run;
//! - `action`: what the status asks of the LLM.
//!
//! At the top level, `survivors` names the mutations no program killed that a new program could
//! kill (status `survived`, `timeout` or `unknown`), `unusable_programs` lists once every
//! program that cannot kill (its result class is not `comparable`), with its class and cause,
//! and `untargeted_rules` the rules no mutation of the list targets (flow F-13).
//!
//! Flow F-13 (version 3): an executed entry's `slots` names each oracle slot
//! ([`slots_value`]); a stopped run's cause carries its leaf census ([`census_clause`]).
//!
//! Re-pin R0c-fix-2 (version 4): every resolved mutation's row carries `removed_claims`
//! ([`claims_value`]): the trusted claims its edit leaves unbacked, which the mutant every
//! program runs on does not carry (`removed`), and those no removal takes away, which refuse the
//! mutant (`unsupported`, status `unknown`, reason `unsupported-claims`).
//!
//! Re-pin R0c-fix-3 (version 5): every resolved mutation's row carries `inconsistent_pairs`,
//! each `{first, second, position, reason}`: the pairs of equations k-rust's critical-pair check
//! does not show to join, which refuse a mutant that is not a theory with models (status
//! `invalid`, reason `inconsistent-mutant`, kink-native `consistency`); empty otherwise.
//!
//! Re-pin L2-2-fix-1 (version 6): every row whose patch applies carries `typing_diagnostics`
//! ([`typing_diagnostics_value`]): the edited rules' errors in compilation's typing view, which
//! refuse nothing (compilation decides whether the mutant is valid); empty otherwise.
//!
//! Re-pin adoption A-1 (version 9): an executed entry of a live run whose mutant run lists a
//! contradicted claim carries `specification_diagnostics` ([`specification_diagnostics_value`]),
//! and one whose run took an undecided solver answer carries `smt_unknowns`; a program's row
//! (in `programs`, from its result record) carries both always.
//!
//! fz26 KINK-BASELINE-FINDINGS (version 10): the document carries `data`, the baseline's full
//! critical-pair check under the flow's `[spec] assume_joined`; a mutation made `unknown` with
//! reason `baseline-findings` lists the unnamed `findings`; and a `comparable` program row is
//! marked `unable_to_kill: "baseline-findings"` while such a finding is left.
//!
//! Nothing here reads or changes a verdict: every status is the kill search's, which is the
//! campaign runner's fold over live and cached outcomes (README 7.5.3).

use crate::outcomes::slot_name;
use crate::{
    manifest::{Budget, FlowManifest},
    mutation::{EditedRule, RuleText},
    results::{ORACLE_SLOTS, ResultClass, cache_directory, kebab, non_value_text},
    search::REPORT_FILE,
};
use kink_campaign::{
    CrossCause, CrossEnd, CrossRefusal, ExecutionFailureKind, FinalResult, LeafCensus,
    OracleOutcome, OracleSide, OracleValue, SideRun, TestRun,
};
use kink_native::execution::SolverProfile;
use kink_patch::{Baseline, Claim, SentenceOrigin, TypingDiagnostic, Withdrawal};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
};

/// The `schema` of the run document, which is also the report.
pub const RUN_SCHEMA: &str = "kink-flow-run";
/// The run document's version: 2 since F-06 added the survivor fields; 3 since F-13 named the
/// oracle slots of an executed entry (`slots` is an object keyed by slot name); 4 since re-pin
/// R0c-fix-2 added each row's `removed_claims`; 5 since re-pin R0c-fix-3 added each row's
/// `inconsistent_pairs`; 6 since re-pin L2-2-fix-1 added each row's `typing_diagnostics`; 7 since
/// packet CACHE-ID added `kink`, kink's semantics identity (kink-campaign `identity`), which
/// `report` requires to be this build's; 8 since packet CACHE-ID-fix-1 added `kink_build`, the
/// digest of the executable that wrote it, which `report` requires to be this executable's; 9
/// since re-pin adoption A-1 added `specification_diagnostics` and `smt_unknowns` to program rows
/// and to executed entries; 10 since fz26 KINK-BASELINE-FINDINGS added `data`, a row's
/// `findings` and a program row's `unable_to_kill`.
pub const RUN_VERSION: u64 = 10;

/// k-rust's contradicted-claim records of one run as specification diagnostics (re-pin adoption
/// A-1): each `{claim, symbol, k_label, rule_id, rule_label, application, undefined,
/// observing_rule_id, observing_rule_label, ground, observed_in, says}`, the terms as KORE text.
/// `claim` is `total` or `preserves-definedness`; `observed_in` is `run` or `load` (a load record
/// is a fact about the definition, on every run's list); `says`, for a ground record, states what
/// it shows ("the `total` claim of `f` is false at `f(0)`"), and is null for a non-ground one,
/// which shows nothing. Every record excludes its run (`contradicted-claim`); none is ever
/// evidence for a kill.
pub fn specification_diagnostics_value(
    records: &[k_rust::backend::ContradictedClaimOutput],
) -> Value {
    let text = |term: &Value| {
        k_rust::kore::codec::from_value(term)
            .map_or_else(|_| term.to_string(), |pattern| pattern.to_string())
    };
    Value::Array(
        records
            .iter()
            .map(|record| {
                let claim = serde_json::to_value(record.claim).unwrap_or(Value::Null);
                let observed_in = serde_json::to_value(record.observed_in).unwrap_or(Value::Null);
                let application = text(&record.application);
                let subject = record
                    .k_label
                    .as_deref()
                    .or(record.symbol.as_deref())
                    .or(record.rule_label.as_deref())
                    .unwrap_or(record.rule_id.as_str());
                let says = record.ground.then(|| {
                    format!(
                        "the `{}` claim of `{subject}` is false at `{application}`",
                        claim.as_str().unwrap_or("?")
                    )
                });
                json!({
                    "claim": claim,
                    "symbol": record.symbol,
                    "k_label": record.k_label,
                    "rule_id": record.rule_id,
                    "rule_label": record.rule_label,
                    "application": application,
                    "undefined": text(&record.undefined),
                    "observing_rule_id": record.rewrite_rule_id,
                    "observing_rule_label": record.rewrite_rule_label,
                    "ground": record.ground,
                    "observed_in": observed_in,
                    "says": says,
                })
            })
            .collect(),
    )
}
/// The claims a mutation's edit leaves unbacked (kink-patch `ClaimSupport::withdraw`):
/// `{removed: [claim], unsupported: [claim]}`, each claim `{module, index, label, key, value}`
/// for a baseline sentence (`label` null when it has none) or `{inserted: <edit index>, key,
/// value}` for a sentence the patch inserts. A removed `simplification` claim is a deleted lemma.
pub fn claims_value(baseline: &Baseline, withdrawal: &Withdrawal) -> Value {
    let claim = |claim: &Claim| match &claim.origin {
        SentenceOrigin::Baseline(at) => json!({
            "module": at.module,
            "index": at.index,
            "label": baseline.sentence(at).and_then(|sentence| {
                sentence
                    .attributes()
                    .value(k_rust::definition::AttributeKey::Label)
                    .and_then(Value::as_str)
                    .map(str::to_owned)
            }),
            "key": claim.key,
            "value": claim.value,
        }),
        SentenceOrigin::Inserted { edit } => {
            json!({"inserted": edit, "key": claim.key, "value": claim.value})
        }
    };
    json!({
        "removed": withdrawal.withdrawn.iter().map(claim).collect::<Vec<_>>(),
        "unsupported": withdrawal.unsupported.iter().map(claim).collect::<Vec<_>>(),
    })
}

/// The typing errors of a mutation's edited rules in compilation's typing view (kink-patch
/// `Mutant::typing_diagnostics`), each `{module, index, label, message}` for a baseline
/// sentence (`label` null when it has none) or `{inserted: <edit index>, message}`. Diagnostics
/// only: no typing error refuses a mutation, and compilation decides whether the mutant is valid
/// (k-rust's view refuses shapes compilation accepts; kink-patch crate docs).
pub fn typing_diagnostics_value(baseline: &Baseline, diagnostics: &[TypingDiagnostic]) -> Value {
    Value::Array(
        diagnostics
            .iter()
            .map(|diagnostic| match &diagnostic.origin {
                SentenceOrigin::Baseline(at) => json!({
                    "module": at.module,
                    "index": at.index,
                    "label": baseline.sentence(at).and_then(|sentence| {
                        sentence
                            .attributes()
                            .value(k_rust::definition::AttributeKey::Label)
                            .and_then(Value::as_str)
                            .map(str::to_owned)
                    }),
                    "message": diagnostic.message,
                }),
                SentenceOrigin::Inserted { edit } => {
                    json!({"inserted": edit, "message": diagnostic.message})
                }
            })
            .collect(),
    )
}

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
pub fn rules_value(rules: &[EditedRule]) -> Value {
    Value::Array(rules.iter().map(rule_value).collect())
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
        "unknown" if reason == Some("baseline-findings") => {
            "fix the specification, or name each finding you accept as a premise in [spec] \
             assume_joined: its full critical-pair check has findings (findings), so the \
             definition may identify the ends kink compares and no program can kill"
        }
        "unknown" if reason == Some("mutant-findings") => {
            "report it, or change the mutation: the claim-free mutant's findings outside the \
             heads its edit can change differ from the baseline's, so kink cannot compare its ends"
        }
        "unknown" => {
            "write a program whose final configuration under the mutant kink can compare: the \
             cause of each executed program says what stopped the comparison"
        }
        "equivalent" => {
            "nothing can kill it: the mutant compiles to the baseline's definition; drop or \
             change the mutation"
        }
        "invalid" if reason == Some("inconsistent-mutant") => {
            "fix the mutation: two equations of one function are not shown to agree where both \
             apply, so the mutant may have no model (inconsistent_pairs); make the guards \
             exclusive or the results equal"
        }
        "invalid" => "fix the mutation: the mutant does not compile (reason)",
        "invalid-mutation" => "fix the mutation: it does not resolve (reason, edit, detail)",
        "error" if reason == Some("host-stack-refused") => {
            "rerun where the host grants more address space: the system refused the native stack \
             kink needs to encode this mutation's patch (detail); the mutation is not at fault"
        }
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
        "error" if reason == Some("resolution-mismatch") => {
            "report it: the memo of this mutation's resolution differs from its live resolution \
             (top-level mismatches); delete the cache's memo/ directory to stop trusting it"
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

/// The most characters of one final configuration's KORE text the report shows.
pub const KORE_CAP: usize = 4000;

/// An executed entry's `slots` (flow F-13): an object keyed by slot name
/// ([`ORACLE_SLOTS`]), each `{outcome}`, and for a distinguishing slot `sides`: for
/// `exit-stop` each side's exit-stop kinds (`{"baseline": ["stuck"], "mutant":
/// ["undefined-step"]}`), for `whole-term` each side's number of final configurations and,
/// when `killer_terms` (the killing program's entry), the mutant's final configurations as
/// KORE text, each capped at [`KORE_CAP`] characters (`{"text", "truncated"}`). `sides` is
/// null when the evidence is not at hand (a cached outcome), and for a one-sided kill, whose
/// mutant side is `Unknown` (re-pin L1-2: the mutant's run reached its work budget).
pub fn slots_value(
    outcomes: &[OracleOutcome],
    baseline: Option<&SideRun>,
    mutant: Option<&SideRun>,
    killer_terms: bool,
) -> Value {
    let side = |run: Option<&SideRun>, slot: usize| match run {
        Some(SideRun::Sides { sides }) => sides.get(slot).cloned(),
        _ => None,
    };
    let mut slots = serde_json::Map::new();
    for (slot, outcome) in outcomes.iter().enumerate() {
        let name = ORACLE_SLOTS.get(slot).copied().unwrap_or("slot");
        let mut value = json!({"outcome": slot_name(*outcome)});
        if *outcome == OracleOutcome::Distinguish {
            value["sides"] = slot_sides(side(baseline, slot), side(mutant, slot), killer_terms);
        }
        slots.insert(name.to_owned(), value);
    }
    Value::Object(slots)
}

/// The two sides of a distinguishing slot (both are values, except for a one-sided kill, whose
/// mutant side is `Unknown`: re-pin L1-2); null when either is missing or not a value.
fn slot_sides(
    baseline: Option<OracleSide>,
    mutant: Option<OracleSide>,
    killer_terms: bool,
) -> Value {
    match (baseline, mutant) {
        (
            Some(OracleSide::Normal(OracleValue::ExitStop(baseline))),
            Some(OracleSide::Normal(OracleValue::ExitStop(mutant))),
        ) => {
            let kinds = |stops: &std::collections::BTreeSet<kink_campaign::ExitStop>| {
                stops
                    .iter()
                    .map(|stop| kebab(&format!("{:?}", stop.class)))
                    .collect::<Vec<_>>()
            };
            json!({"baseline": kinds(&baseline), "mutant": kinds(&mutant)})
        }
        (
            Some(OracleSide::Normal(OracleValue::FinalResult(FinalResult::WholeTerm(baseline)))),
            Some(OracleSide::Normal(OracleValue::FinalResult(FinalResult::WholeTerm(mutant)))),
        ) => {
            let mut mutant_side = json!({"final_configurations": mutant.len()});
            if killer_terms {
                mutant_side["kore"] = mutant
                    .iter()
                    .map(|term| capped(term.to_string()))
                    .collect::<Vec<_>>()
                    .into();
            }
            json!({
                "baseline": {"final_configurations": baseline.len()},
                "mutant": mutant_side,
            })
        }
        _ => Value::Null,
    }
}

/// `{text, truncated}`: `text` cut to [`KORE_CAP`] characters.
fn capped(text: String) -> Value {
    match text.char_indices().nth(KORE_CAP) {
        Some((end, _)) => json!({"text": &text[..end], "truncated": true}),
        None => json!({"text": text, "truncated": false}),
    }
}

/// What a run's leaf census says (flow F-13): `k-rust returned 412 leaves (stuck 400, cancelled
/// 12), the deepest at depth 1830`, or that it returned none. After a time stop the leaves are
/// the paths that had ended or were cancelled when the bound fired; many ended paths and a
/// shallow deepest leaf suggest path explosion, few leaves and a deep one non-termination.
pub fn census_clause(census: &LeafCensus) -> String {
    let total = census.total();
    if total == 0 {
        return "k-rust returned no leaves, so neither the paths nor the depth reached are known"
            .to_owned();
    }
    let kinds = census
        .leaves
        .iter()
        .map(|(halt, count)| format!("{} {count}", kebab(&format!("{halt:?}"))))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "k-rust returned {total} {} ({kinds}), the deepest at depth {}",
        if total == 1 { "leaf" } else { "leaves" },
        census.deepest.unwrap_or_default()
    )
}

/// The `cause` of an executed program's outcome on the mutant, from the runner's evidence for
/// that run and, when the session recorded it, the leaf census of the mutant's run: `None` when
/// the outcome is `agree` or `distinguish` (or the test was skipped).
pub fn executed_cause(
    run: &TestRun,
    mutant: Option<&SideRun>,
    across: &[CrossRefusal],
    budget: Budget,
    census: Option<&LeafCensus>,
) -> Option<String> {
    match run {
        TestRun::SkippedAfterKill => None,
        TestRun::Failed(kind) => Some(match (kind, census) {
            (ExecutionFailureKind::TimeLimit, Some(census)) => format!(
                "{}; when the bound fired {}",
                failure_cause(*kind, budget),
                census_clause(census)
            ),
            (ExecutionFailureKind::ResourceLimit, Some(census)) => format!(
                "{}; the mutant's run: {}",
                failure_cause(*kind, budget),
                census_clause(census)
            ),
            _ => failure_cause(*kind, budget),
        }),
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
            // An unknown or timed-out side: the census tells a depth bound from an undecided end.
            // A side the pair's cross-definition judgement refused ended in a value of its own
            // definition, so its census says nothing of the cause (fz26 KINK-CAUSE-SUBTERM).
            let refused = |slot: usize, baseline_end: bool| {
                across
                    .iter()
                    .find(|refusal| refusal.slot == slot && refusal.baseline_end == baseline_end)
            };
            let incomplete = sides.iter().enumerate().any(|(slot, side)| {
                matches!(side, OracleSide::Unknown | OracleSide::Timeout)
                    && refused(slot, false).is_none()
            });
            for (slot, outcome) in outcomes.iter().enumerate() {
                if *outcome == OracleOutcome::Agree {
                    continue;
                }
                let name = ORACLE_SLOTS.get(slot).copied().unwrap_or("slot");
                // The mutant's own refusal first; the baseline's only when the mutant's side is
                // otherwise a value.
                let cross = refused(slot, false).or_else(|| {
                    refused(slot, true).filter(|_| {
                        !matches!(
                            sides.get(slot),
                            Some(OracleSide::Unknown | OracleSide::Timeout)
                        )
                    })
                });
                let cause = cross.map_or_else(
                    || slot_cause(*outcome, sides.get(slot), budget),
                    cross_cause,
                );
                match groups.iter_mut().find(|(_, existing)| *existing == cause) {
                    Some((names, _)) => names.push(name),
                    None => groups.push((vec![name], cause)),
                }
            }
            let mut cause = groups
                .iter()
                .map(|(names, cause)| format!("{}: {cause}", names.join(", ")))
                .collect::<Vec<_>>()
                .join("; ");
            if let (true, Some(census)) = (incomplete, census) {
                cause.push_str(&format!("; the mutant's run: {}", census_clause(census)));
            }
            Some(cause)
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
        ExecutionFailureKind::StackStop => {
            "stack-stop: the mutant's run met a stop for lack of native stack, so its result can \
             depend on the host's threads"
                .into()
        }
        ExecutionFailureKind::LoadStackStop => {
            "load-stack-stop: loading the mutant's definition met a stop for lack of native \
             stack, so its loaded theory can depend on the host's threads"
                .into()
        }
        ExecutionFailureKind::ContradictedClaim => {
            "contradicted-claim: a run of this program (the mutant's, or the baseline's) takes an \
             undefined step that falsifies a `total` or `preserves-definedness` claim, or k-rust \
             lists a contradicted claim the run or the definition's load observed, so the \
             definition is inconsistent there and this program's comparison is no evidence"
                .into()
        }
        ExecutionFailureKind::ImplementationChosenHook => {
            "implementation-chosen-hook: the mutant uses a hook whose value k-rust chooses \
             where the definition leaves it open (choice, map and set listing order, \
             mixed-format or NaN-sign Float, and the hooks k-rust's builtin files leave to the \
             backend or the environment, such as String2Bytes, Bytes2String, Base2String, \
             substitution's renamed variables or I/O)"
                .into()
        }
        ExecutionFailureKind::ShortCircuitReading => {
            "short-circuit-reading: the mutant's result depends on whether andBool, orBool, \
             impliesBool, #if, andThenBool or orElseBool skip an operand that may be undefined, \
             which the definition leaves to the backend; k-rust evaluates every operand"
                .into()
        }
        ExecutionFailureKind::AllowanceRefusal => {
            "allowance-refusal: a Bytes hook of the mutant's run was refused for the process's \
             memory allowance, a property of the host"
                .into()
        }
        ExecutionFailureKind::ImplementationChosenValue => {
            "implementation-chosen-value: the mutant's run read a value the definition leaves \
             open, which k-rust chose (k-rust's list of the run's open values: a map or set \
             listing order, choice, mixed-format or NaN-sign Float, Base2String letter case, \
             substOne names or a #read count)"
                .into()
        }
        ExecutionFailureKind::UnsupportedHook => {
            "unsupported-hook: the mutant's run, or its definition's load, left an application \
             unevaluated as an unsupported hook, which can steer a result without a leaf showing \
             it"
            .into()
        }
        ExecutionFailureKind::EqualsCondition => {
            "equals-condition: a rule or equation condition of the mutant equates two terms \
             ({ A #Equals B }), which k-rust may decide wrongly when they may be undefined"
                .into()
        }
    }
}

/// Why a slot the pair's cross-definition judgement refused is unknown (kink-campaign
/// `judge_across`; fz26 KINK-CAUSE-SUBTERM, KINK-OVERLOAD-VALUE review N4): the side, that its
/// run did end in a value of its own definition, and why that end is not data under the other
/// side's definition.
fn cross_cause(refusal: &CrossRefusal) -> String {
    let (side, other) = if refusal.baseline_end {
        ("baseline", "mutant")
    } else {
        ("mutant", "baseline")
    };
    if refusal.cause == CrossCause::NoEnds {
        return format!(
            "the {side}'s state value has no final configurations to judge under the {other}'s \
             definition, so it is not compared"
        );
    }
    let (head, judge) = match refusal.end {
        CrossEnd::Terminal => (
            format!(
                "the {side}'s run ended in a value of its own definition, but that end is not \
                 data under the {other}'s definition, so the two ends cannot be compared"
            ),
            other,
        ),
        CrossEnd::Binding => (
            format!(
                "a binding of the {side}'s match is not definition-independent under the \
                 mutant's definition, which judges the bindings of both sides"
            ),
            "mutant",
        ),
        CrossEnd::Payload => (
            format!(
                "a term the {side}'s pattern relations read is not definition-independent under \
                 the {other}'s definition, so its relation decisions cannot be compared"
            ),
            other,
        ),
    };
    match &refusal.cause {
        CrossCause::NoData => format!(
            "{head} (the {judge}'s definition admits no end as data: it has no data facts or a \
             finding of its full check is left)"
        ),
        CrossCause::NotData(Some(failure)) => {
            format!("{head}; there, {}", non_value_text(failure))
        }
        CrossCause::NotData(None) | CrossCause::NoEnds => format!(
            "{head} (every node passes its own test there, but its canonical form there differs)"
        ),
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
             max_depth = {} or ended undecided{}, or a final configuration holds a collection kink \
             cannot compare, such as one with a Bytes key, an unevaluated function or a symbolic term)",
            budget.max_depth,
            // Re-pin L1-1: the work budget of the mutant's run, when the manifest sets one (the
            // run's census then says `work-bound 1`).
            budget
                .work_factor
                .map_or_else(String::new, |factor| format!(
                    ", the run reached its work budget (work_factor = {factor})"
                ))
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

/// The authored rules no resolving mutation of the list targets (the mutation-side analogue of
/// rule coverage; flow F-13, from the F-07 decision), in sentence order: `{module, index, label,
/// file, start_line, end_line, address, text}`, where `address` is how a mutation edit can
/// address the rule (`{"rule": label}`, or `{"file", "line"}` for an unlabelled rule) and
/// `text` its K text in the file's K view (null when the rule has no usable span).
/// Informational only: outside every digest and key.
pub fn untargeted_rules(
    rules: &[RuleText],
    targeted: &std::collections::BTreeSet<kink_patch::SentenceRef>,
) -> Vec<Value> {
    rules
        .iter()
        .filter(|rule| !targeted.contains(&rule.at))
        .map(|rule| {
            let address = match &rule.label {
                Some(label) => json!({"rule": label}),
                None => json!({"file": rule.file, "line": rule.start_line}),
            };
            json!({
                "module": rule.at.module,
                "index": rule.at.index,
                "label": rule.label,
                "file": rule.file,
                "start_line": rule.start_line,
                "end_line": rule.end_line,
                "address": address,
                "text": rule.text,
            })
        })
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
                "k_rust_revision": crate::k_rust_revision(),
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
    let document = kink_patch::parse_json(&text).map_err(|e| match e {
        kink_patch::JsonError::Syntax(_) => ("unreadable", format!("the report is not JSON: {e}")),
        // Re-pin L1-3-tail: kink's depth limit or the host's refused stack, not a malformed file.
        other => ("unreadable", format!("the report cannot be read: {other}")),
    })?;
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
    // `report` honours the stored statuses without re-deriving them, so it prints only a document
    // this build wrote (packet CACHE-ID-fix-1): most verdict code has no version constant, and
    // only the build identity tells that it changed.
    if let Some(reason) = kink_campaign::writer_difference(
        &document["kink_build"],
        &document["kink"],
        &kink_campaign::kink_build(),
    ) {
        return Err((
            "unreadable",
            format!(
                "the report is not this build's ({reason}), so its statuses may rest on verdict \
                 code this build no longer runs: run `kink-flow run` again"
            ),
        ));
    }
    if let Some(key) = kink_campaign::identity_difference(&document["kink"]) {
        return Err((
            "unreadable",
            format!(
                "the report was written under another kink identity (`{key}` is missing or \
                 differs), so its statuses may rest on algorithms this build no longer runs: run `kink-flow run` \
                 again"
            ),
        ));
    }
    Ok(document)
}
