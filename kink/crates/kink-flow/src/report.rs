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
//! - `witnesses`: the comparable programs whose cached coverage witnesses the mutant's compiled
//!   edit (kink-campaign `CompiledEdit`, [`crate::search`] step 2): programs that applied a
//!   removed axiom's sentence (k-rust `applied`) when its edit is confined to its right-hand side
//!   or `ensures`, programs that matched it (`matched`) otherwise, every program for an edit that
//!   is not site-local; read from the command's live call, or from the
//!   outcome file on a row tier 1 decided with no call, and `null` when there is neither;
//! - `witnesses_global`: whether the edit is not site-local (an equation's left-hand side or
//!   attribute, a removed or inserted equation, a declaration, ...), so that every program is a
//!   witness whatever its coverage reaches, since a changed pattern can match terms no baseline
//!   run tried; `null` when `witnesses` is `null` or no program is comparable;
//! - `executed`: each program the mutant ran on, with its outcome and, when the outcome is
//!   neither `agree` nor `distinguish`, a `cause` read from the runner's evidence for that run;
//! - `action`: what the status asks of the LLM.
//!
//! A mutation that states the verdict it expects (`expect`, [`crate::Expect`]) has its
//! expectation checked against its row's status ([`mutation_expectation`]): `met`, `unmet` or
//! `inconclusive`, in the row's `expectation` and the document's `expectations`. It changes no
//! status, no digest, no key and no lock line: it is checked again from the row on every run,
//! cached or live, and joins only the exit status (`crate::cli::run_status`).
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
//! `not-admitted`, reason `inconsistent-mutant`, kink-native `consistency`); empty otherwise.
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
//! kink27 R5-WEAKENING (version 11): a mutation whose edit only weakens the specification (it
//! deletes equations of functions or lemmas, or replaces one by an instance of itself: a narrower
//! pattern or `requires`) has the status `unkillable` with reason `weakening`, runs nothing, and
//! its row's `weakening` names each edited equation or lemma (null on every other row); a mutant run's cause names the function whose
//! application an indeterminate leaf holds unreduced ([`executed_cause`]). Since version 28 an
//! edit whose `requires` adds only conditions that hold under every valuation of their variables
//! keeps its equation (kind `valid-condition`), and a mutation of only such edits is `equivalent`
//! with reason `valid-condition`.
//!
//! CF-03 (version 15): a run of a definition whose short-circuit analysis flags a rule is judged
//! by k-rust's `shortCircuitReadings` list of that run, so `spec.exclusion` no longer names the
//! short-circuit reading (the check and coverage documents' `spec.short_circuit` name the flagged
//! rules); an executed entry whose mutant run lists readings that count against it carries
//! `short_circuit_readings` (`crate::exclusion::readings_value`), and its cause names the step;
//! a program's row carries its baseline run's (`coverage`).
//!
//! CF-16 (version 12): every executed entry of a compared program carries `difference`, the kill
//! evidence of a distinguishing one (null otherwise; [`crate::evidence`]): the first differing
//! cell path between an end of one side outside the other's set and its nearest end there, both
//! values as K text (KORE as fallback), bounded, and each end's computation head and class. It is
//! computed at kill time, live, and stored in the killing program's tier-1 record, so a cached
//! kill shows it too, as does a one-sided kill (from the run's one-sided ends, which killed). A
//! distinguishing slot's `sides` is no longer null for a cached or one-sided kill: it is read from
//! the difference ([`slots_value`]). A program's row carries `ends`, each end's `{head, class}`.
//!
//! CF-23 (version 15): the document carries `schedule`, `first-kill` or `full` (`run --full`),
//! and `matrix`, the kill matrix of a full run per comparable program ([`matrix`]; null under
//! first-kill); every row carries `killed_by`, every killing program in corpus order under
//! `full` (null under first-kill and on a row no fold decided). A full row's `executed` lists
//! every program in corpus order, its cached and live cells merged.
//!
//! Version 27: the cause of a mutant run's undecided end names the application of an edited
//! function that a stuck, undefined-step, indeterminate or stop leaf holds unreduced, with its
//! arguments
//! ([`executed_cause`]), and an `unknown` row every undecided program of which, live or from the
//! outcome cache, is undecided by such applications ([`open_application_cause`]: every leaf whose
//! path is incomplete holds one) has the reason `open-application`, with its own `action`, as
//! `stack-stop` has. A program's `mismatches` entry names each side's `open_application`, and a
//! `run --verify` row has the reason `run` gives its cold call (`stack-stop`,
//! `open-application`).
//!
//! Version 29 (the killer record, [`crate::lock`]): the document carries `lock`, null without
//! `--lock`, else `{path, status, reason, header, changes}`: `status` `created`, `written`,
//! `unchanged`, `stale` (under `--locked`, a finding) or `not-written`, `reason` (`only`, `verify`,
//! `stopped`, `refused`, `write-failed` or `locked`) when nothing was written, `header` whether
//! the lines before the first mutation differ, `changes` each mutation whose `(status, killer,
//! reason)` differs, `{mutation, recorded, now}`; a lock that does not decode is `{path, outcome:
//! "refused", detail}` and refuses the run. Every row carries `recorded_killer`, the lock's killer
//! or null, and `killer_change`: null when the killer is the recorded one, else `no-record`,
//! `not-in-corpus`, `not-comparable` (with `unusable_killer`, `source` `record`),
//! `no-longer-kills` or `not-run`. The document's `order` leaves: the search order is fixed.
//!
//! Version 23: an executed entry of a live run on which kink's own solver questions about
//! it (its leaf feasibility and observation decider, kink-campaign
//! `RunNotes::decider_smt_unknowns`) took an undecided answer carries `decider_smt_unknowns`, and
//! a program's row carries its baseline run's always; reported, never an exclusion, as
//! `smt_unknowns` is.
//!
//! Nothing here reads or changes a verdict: every status is the kill search's, which is the
//! campaign runner's fold over live and cached outcomes (README 7.5.3).

use crate::outcomes::slot_name;
use crate::{
    cli::{CommandSpelling, Verb},
    evidence::{EndReader, HEAD_CAP},
    manifest::{Budget, FlowManifest},
    mutation::{EditedRule, InvalidReason, Mutation, RuleText},
    results::{ResultClass, corpus_cache_directory, kebab, non_value_text},
    search::REPORT_FILE,
};
use kink_campaign::{
    CrossCause, CrossEnd, CrossRefusal, ExecutionFailureKind, FinalResult, LeafCensus, Observation,
    ObservationVerdict, OracleOutcome, OracleSide, OracleValue, SideRun, TestEvidence, TestRun,
};
use kink_native::{bridge::OpenApplication, execution::SolverProfile};
use kink_patch::{Baseline, Claim, SentenceOrigin, TypingDiagnostic, Withdrawal};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
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
/// `findings` and a program row's `unable_to_kill`; 11 since kink27 R5-WEAKENING added the status
/// `unkillable` (reason `weakening`) and each row's `weakening`; 12 since CF-16 added each executed
/// entry's `difference`, the sides of a cached or one-sided kill, and each program row's `ends`;
/// 13 since CF-02 added `spec.exclusion`, the definition exclusion and its causes; 14 since the
/// compared cells added `result`, the slots and the cells the programs' second slot compares, so
/// that every survivor is reported with the cells it was compared on, and named that slot `cells`
/// where it leaves some cell out; 15 since CF-03 judged each run of a definition whose
/// short-circuit analysis flags a rule by its own list, taking the short-circuit reading out of
/// `spec.exclusion` and adding each executed entry's and each program row's
/// `short_circuit_readings`; 16 since CF-23 added `schedule`,
/// `matrix` and each row's `killed_by` (`run --full`); 17 since each row's `reaching` is read from
/// the compiled mutant (or the outcome file's copy of its compiled edit), a program whose cached
/// coverage is not complete witnessing every edit as kink-campaign's coverage selection counts
/// it, `[]` on a `no-comparable-program` row (no program of an empty set witnesses an edit) and
/// otherwise `null` on a row with neither, and each call's `programs` are listed in the order the
/// call ran them; 18 since CF-40c2 named each row's `reaching` `witnesses` and the runner status
/// `invalid` `not-admitted`, so that each coverage predicate and each status has one name in every
/// kink-flow document (README, "Coverage predicates"); 19 since a rewrite rule edit that is not
/// confined to its right-hand side or `ensures` (its left-hand side, an attribute, a deletion) is
/// witnessed by `matched`, no longer by `applied`, so a row's `witnesses` and each call's program
/// order can name more programs for the same mutation; 20 since `[stop]`: a corpus with a stop
/// has `stop` (absent without one), each program row's `ends` say how the run reached them
/// (`halt`), a survivor that edits a rule the stop stops before has `stop_hides_edit`, and a mutant
/// on which a rule of the stop labels no rewrite rule is `not-admitted`, reason `stop-unresolved`;
/// 21 since each executed entry's `difference` names its format (`format`), and is the front end's
/// evidence, in the front end's format, where a front end renders it (`crate::evidence`, "The
/// format of the evidence"); 22 since a case document may hold named cases, each a program whose
/// id is the document's path, `#` and its name, and the end its case expects, which kink reads
/// through the front end's renderer: the row of a program with an expectation carries
/// `expectation`, met, unmet with the first difference, or inconclusive with why
/// (`crate::expect`), and a program whose expectation no front end reads is refused at stage
/// `inputs` (`typed-expectation`, `expectation-value`); 23 since each executed entry and each
/// program row carries `decider_smt_unknowns`, the undecided solver answers of kink's own
/// questions about the run beside k-rust's `smt_unknowns` (an entry only when it is not zero),
/// and under the Z3 profile the outcome cache is on where the solver is resource-bounded; 24
/// since an executed entry from the outcome cache (`cached: true`) can be an `unknown` with its
/// `cause` and carries the cached run's undecided-answer counts (CF-33d), and a `mismatches`
/// entry of a program names each side's `cause`, `smt_unknowns` and `decider_smt_unknowns`; 25
/// since `result` may name cells inside `?` and `*` cells, each left out (or compared) in every
/// instance, so a survivor of a `cells` slot may be relative to cells left out of each instance,
/// and a narrowing's `compared` names the key of each Map that encloses a named cell
/// ([`crate::observed`]); 26 since an alias of an edited axiom's left-hand side (K's `#as`, which
/// k-rust's compiler writes for a subterm the right-hand side builds again) is read as the pattern
/// it names, so an edit whose result reuses a subterm of the left-hand side is confined to its
/// result and a row's `witnesses` can name fewer programs, and each row carries
/// `witnesses_global`, whether its witnesses are every program because the edit is not site-local;
/// 27 since an executed program's cause names an open application of an edited function that a
/// stuck leaf, an undefined step or a stop's end holds, not only an indeterminate leaf, with the application and its
/// arguments, an `unknown` row every undecided program of which, live or cached, is undecided by
/// such applications carries the reason `open-application` ([`OPEN_APPLICATION_REASON`]), and a
/// program's `mismatches` entry names each side's `open_application`; 28 since a row's
/// `weakening` kind can be `valid-condition` (an edited equation's `requires` adds only conjuncts
/// that hold under every valuation of their variables, so the equation is the specification's
/// own), and a row every edited sentence of which has that kind is `equivalent` with the reason
/// `valid-condition` ([`crate::search::VALID_CONDITION_REASON`]), not `unkillable`; 29 since the
/// killer record ([`crate::lock`]): the search runs in one order (the document's `order` leaves),
/// a killed row's `killer` is the lock's recorded killer while it kills and is in the corpus, else
/// the first killing program in the search's order, under both schedules, its `killer_source` is
/// `outcome-cache`, `record` (the recorded killer's one-program call) or `search` (`hint` and
/// `stale_killer` leave with the hint store), each row carries `recorded_killer` and
/// `killer_change`, and the document carries `lock`; 30 since `[stop] when`: a stop with a
/// condition names it (`stop.when`, the condition's identity), an executed program whose run's
/// condition was left undecided at an arrival, or refused at one, is `unknown` with the cause
/// `stop-condition`, a mutant whose declarations of the read cells' sorts are not the
/// specification's is `not-admitted`, reason `stop-condition-incompatible`, and a survivor's
/// `stop_hides_edit` is read, under a condition, from the comparable programs' coverage: no
/// comparable program took the stop rule's step; 31 since a lock compared with its rendering
/// names the first line in which the file differs (`lock.difference`, [`crate::lock`]), and a run
/// refused before its lock is read (a manifest or a mutation list that does not decode) carries
/// the lock it left unwritten, and an `equivalent` row withdraws no claim (`removed_claims`
/// empty), since its mutant is the specification's theory; 32 since under the Z3 profile the
/// document names the Z3 build its verdicts were decided on (`z3`, [`crate::with_z3_build`]), and a
/// lock compared with its rendering names each header key whose value differs
/// (`lock.header_changes`), so that `--locked` says when a lock was recorded on another Z3 build;
/// 33 since `[observe]`: a corpus with observation channels names the declaration (`observe`,
/// absent without one), a program row carries the channels its baseline recorded
/// (`observations`) and may be `comparable-prefix`, an executed entry has the slot
/// `observations` after the end slots, with `position` where it distinguished, `horizon` where it
/// agreed up to the baseline's horizons and `cause` where it was unknown, a kill only the channels
/// decided has kink's observation evidence (`difference.position` and both sides' elements,
/// [`crate::evidence`]), a survivor some program of which agreed only up to a horizon carries
/// `horizon` and says so in its action, and a mutant on which a point class's rule labels no
/// rewrite rule, or whose declarations of the observed cells' sorts are not the specification's,
/// is `not-admitted`, reason `point-unresolved` or `observation-incompatible`; 34 since every
/// horizon names why its channel opened: a horizon is `{elements, opening}` in the slot
/// `observations` and a survivor's `horizon`, a program row's `observations` gives each open
/// channel's `opening` and its horizon so, a survivor's action raises the bound only where some
/// horizon's opening is `bound` or `cycle`, and a prefix program none of whose channels kept an
/// element within its budget or closed by a cycle is `unknown`, since it observed nothing; and
/// a channel's `closed` can be `cycle`, and an element of the observation evidence `cycle`; 35
/// since a run that splits is compared by prefix sets: a slot's `position` names the side
/// `outside` the other's set where they differ, and that kill's evidence is
/// `kink-k-sets/1` ([`crate::evidence::K_SET_EVIDENCE_VERSION`]); 36 since a program row's
/// `observations` for a run with several paths gives its prefix sets' facts, `{paths, real,
/// channels: [{name, complete_to}], horizon}`, where version 35 showed each channel open at 0 by
/// `branch` whatever was explored; 37 since a mutation can state the verdict it expects
/// (`expect`, [`crate::Expect`]): every row carries `expect` (`survive`, `kill` or null) and
/// `expectation` (null without `expect`, else `{verdict, detail}`, [`mutation_expectation`]), a
/// met control's `survived` row asks nothing ([`EXPECTED_SURVIVOR_ACTION`]) unless its survival
/// rests on a horizon or a hidden edit, and the document carries `expectations`, the ids of the
/// rows whose expectation is met, unmet and inconclusive, and of the mutations stating one that
/// have no row (`unchecked`).
/// 38 names each finding of the full critical-pair check by its kind, sentences and a digest of its
/// compiled sentences (`root:A,B#D`, k-rust-backend `data_term::names`) where it named it by
/// generated-K positions, gives each finding its `sentences` (`{part, at}`, `at` information only),
/// and refuses a `[spec] assume_joined` name with one of the reasons `malformed`, `position-name`,
/// `unnamed-sentence`, `no-digest`, `changed`, `no-finding`, `decided` or `ambiguous` where it
/// refused `name-refused` (KINK-FINDING-NAMES).
/// 39 keeps a lock entry a run the clock (`budget.time_ms`) stopped could change, rather than
/// rewriting it or reporting it as a difference ([`crate::clock`]): the lock has `kept` and
/// `clock_stopped`, and `--locked` gives the status `undecided` where nothing else differs
/// (FB45-LOCKED-TIMEOUT).
pub const RUN_VERSION: u64 = 39;

/// The name of the observation slot of an executed entry's `slots`, after the end slots
/// ([`crate::observed::ResultProjection::slots`]), under `[observe]`.
pub const OBSERVATION_SLOT: &str = "observations";

/// The observation slot's verdict of a run's notes (kink-campaign `RunNotes::observation`), when
/// the pair judged it.
#[must_use]
pub fn observation_verdict(notes: &kink_campaign::RunNotes) -> Option<&ObservationVerdict> {
    match &notes.observation {
        Some(Observation::Compared(comparison)) => comparison.verdict.as_ref(),
        _ => None,
    }
}

/// What the observation slot reports beside its outcome, as an executed entry's slot and an
/// outcome record keep it: `{position: {channel, index, at_end}}` where it distinguished, with
/// `outside` (kink-campaign `Outside::name`) where the two sides' prefix sets differ,
/// `{horizon: {<channel>: {elements, opening}}}` where it agreed and some channel's agreement
/// rests on the baseline's horizon, each with the number of elements agreed on and why the
/// baseline's channel opened there (kink-campaign `Opening::name`), `{cause}` where it was
/// unknown; null otherwise (an agreement to every channel's end).
#[must_use]
pub fn observation_slot(verdict: &ObservationVerdict) -> Value {
    match verdict.outcome {
        OracleOutcome::Distinguish => verdict.position.as_ref().map_or(Value::Null, |position| {
            let mut slot = json!({"position": {
                "channel": position.channel,
                "index": position.index,
                "at_end": position.at_end,
            }});
            // A difference of prefix sets names the side whose prefix the other lacks.
            if let Some(outside) = position.outside {
                slot["position"]["outside"] = json!(outside.name());
            }
            slot
        }),
        OracleOutcome::Agree if !verdict.horizon.is_empty() => {
            let horizon = verdict
                .horizon
                .iter()
                .map(|(channel, at)| (channel.clone(), at.value()))
                .collect::<serde_json::Map<_, _>>();
            json!({"horizon": horizon})
        }
        OracleOutcome::Unknown => verdict
            .cause
            .as_ref()
            .map_or(Value::Null, |cause| json!({"cause": cause})),
        _ => Value::Null,
    }
}

/// `slots` (an executed entry's) with the members of `observation` ([`observation_slot`]) added to
/// its observation slot; unchanged when `observation` is null or there is no such slot.
pub fn with_observation(slots: &mut Value, observation: &Value) {
    let (Some(slot), Some(members)) = (
        slots
            .get_mut(OBSERVATION_SLOT)
            .and_then(Value::as_object_mut),
        observation.as_object(),
    ) else {
        return;
    };
    for (name, value) in members {
        slot.insert(name.clone(), value.clone());
    }
}

/// The agreements up to a horizon of a survivor's executed entries: `[{program, horizon}]`, each
/// program whose observation slot agreed only up to the baseline's horizons (`horizon` as the
/// slot has it, [`observation_slot`]), in the entries' order; empty when none did.
#[must_use]
pub fn survivor_horizons(executed: &[Value]) -> Vec<Value> {
    executed
        .iter()
        .filter_map(|entry| {
            let horizon = entry["slots"][OBSERVATION_SLOT].get("horizon")?;
            Some(json!({"program": entry["program"], "horizon": horizon}))
        })
        .collect()
}

/// k-rust's contradicted-claim records of one run as specification diagnostics (re-pin adoption
/// A-1): each `{claim, symbol, k_label, rule_id, rule_label, application, undefined,
/// observing_rule_id, observing_rule_label, ground, observed_in, says}`, the terms as KORE text.
/// `claim` is `total` or `preserves-definedness`; `observed_in` is `run` or `load` (a load record
/// is a fact about the definition, on every run's list); `says`, for a ground record, states what
/// it shows ("the `total` claim of `f` is false at `f(0)`"), and is null for a non-ground one,
/// which shows nothing. Every record excludes its run (`contradicted-claim`); none is ever
/// evidence for a kill.
pub fn specification_diagnostics_value(
    records: &[k_rust::backend::ContradictedClaimOutput<k_rust::kore::ast::Pattern>],
) -> Value {
    let text = |term: &k_rust::kore::ast::Pattern| term.to_string();
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

/// What a status asks of the LLM, its next steps spelled by `spelling`; `None` for `killed`.
/// `reason` refines `error`. Under kink-flow's own spelling it is [`action`].
pub fn action_spelled(
    status: &str,
    reason: Option<&str>,
    spelling: &dyn CommandSpelling,
) -> Option<String> {
    match status {
        "error" if reason == Some("outcome-conflict") => Some(format!(
            "check the outcome cache: a cached agreement says the mutant ran, a live call says it \
             did not; run `{} --verify`",
            spelling.command(Verb::Run)
        )),
        "error" if reason.is_some_and(is_corpus_error) => Some(format!(
            "fix the corpus: a cached result no longer describes its program's baseline run; \
             run `{} --verify`",
            spelling.command(Verb::Coverage)
        )),
        _ => action(status, reason).map(str::to_owned),
    }
}

/// What the row of a mutation a front end refused asks of its author
/// ([`InvalidReason::External`]): the front end's next step; `None` for every reason of
/// kink-flow's own, whose action is the status's ([`action`]).
pub fn refused_action(reason: InvalidReason) -> Option<String> {
    match reason {
        InvalidReason::External { next, .. } => {
            Some(format!("fix the mutation: {next} (reason, edit, detail)"))
        }
        _ => None,
    }
}

/// The pseudo-reason [`action`] reads for a `survived` row some program of which agreed only up to
/// a horizon a larger budget can move (the row's `horizon`, opening `bound` or `cycle`); the
/// row's own `reason` stays null.
pub const HORIZON_REASON: &str = "horizon";

/// The pseudo-reason [`action`] reads for a `survived` row some program of which agreed only up to
/// a horizon, and every such horizon is where the baseline's channel opened for a reason of its
/// run, not of the budget (an undecided element, a branch, an undecided path): a larger budget
/// reaches the same horizon. The row's own `reason` stays null.
pub const HORIZON_OPENED_REASON: &str = "horizon-opened";

/// The pseudo-reason of a survivor's horizons ([`survivor_horizons`]): [`HORIZON_REASON`] when
/// some channel's horizon is where a bound cut the baseline's path, or past a cycle-closed
/// baseline channel where the mutant's path may have been cut (opening `cycle`), else
/// [`HORIZON_OPENED_REASON`].
#[must_use]
pub fn horizon_reason(horizons: &[Value]) -> &'static str {
    let bound = horizons.iter().any(|entry| {
        entry["horizon"]
            .as_object()
            .into_iter()
            .flatten()
            .any(|(_, at)| {
                [kink_campaign::Opening::Bound, kink_campaign::Opening::Cycle]
                    .iter()
                    .any(|opening| at["opening"] == opening.name())
            })
    });
    if bound {
        HORIZON_REASON
    } else {
        HORIZON_OPENED_REASON
    }
}

/// What a status asks of the LLM, as `kink-flow` spells its commands
/// ([`action_spelled`]); `None` for `killed`. `reason` refines `error`.
pub fn action(status: &str, reason: Option<&str>) -> Option<&'static str> {
    Some(match status {
        "killed" => return None,
        "survived" if reason == Some(HORIZON_REASON) => {
            "raise the bound or write another program: every executed program agreed, and some \
             agreed only up to the horizon of a baseline's observation channel (horizon): the \
             mutant may differ past it, which no program observed; a larger budget observes more \
             of a channel whose opening is bound, may observe more of the mutant's where it is \
             cycle (the baseline's channel is complete, and the mutant's run stopped before \
             showing whether it emits more), and observes no more of any other"
        }
        "survived" if reason == Some(HORIZON_OPENED_REASON) => {
            "write another program: every executed program agreed, and some agreed only up to the \
             horizon of a baseline's observation channel (horizon), which opened there at an \
             undecided element, a branch or an undecided path (its opening), not at a bound, so \
             a larger budget observes no more of it: the mutant may differ past it, which no \
             program observed"
        }
        "survived" => {
            "write a program that matches an edited rule and whose final configuration the edit \
             changes outside the cells result.not_compared lists: every executed program \
             reached a comparable result and agreed"
        }
        "timeout" => {
            "write a program that ends under the mutant within budget.time_ms with a final \
             configuration that differs outside the cells result.not_compared lists: a program \
             did not end on the mutant, and no program killed it"
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
        "unknown" if reason == Some("stack-stop") => {
            "write a program on an input the mutant ends on, which kills it when its final \
             configuration differs: the mutant's run recursed until it met a stop for lack of \
             native stack, which no budget bounds, so a program on which it does not end cannot \
             kill it; when it recurses without end on every input that reaches the edit, write \
             the misunderstanding as a mutant that ends, or drop the mutation"
        }
        "unknown" if reason == Some(OPEN_APPLICATION_REASON) => {
            "write a program on which the mutant reduces every application it builds of the \
             function the cause names: every program the mutant did not judge ends with such an \
             application, which no equation of the mutant reduces and kink cannot compare; when \
             the edit leaves the function's value open on every input that reaches it (it only \
             narrows the equation), no program can kill it: write the misunderstanding as a \
             replacement, an equation whose result differs, or drop the mutation"
        }
        "unknown" => {
            "write a program whose final configuration under the mutant kink can compare: the \
             cause of each executed program says what stopped the comparison"
        }
        "equivalent" if reason == Some(crate::search::VALID_CONDITION_REASON) => {
            "nothing can kill it: the edit only adds to a requires conditions that hold of every \
             value of their variables' sorts, such as the sort predicate of a variable of that \
             sort, so each edited equation is the specification's own and the mutant has exactly \
             the specification's models (weakening, kind valid-condition); drop or change the \
             mutation"
        }
        "equivalent" => {
            "nothing can kill it: the mutant compiles to the baseline's definition; drop or \
             change the mutation"
        }
        "unkillable" => {
            "nothing can kill it: the edit only deletes equations of functions or lemmas, or \
             replaces one by an instance of itself (a narrower pattern or requires, giving each \
             remaining input the value it had), so every model of the specification is a model \
             of the mutant and no execution can tell them apart (weakening); to test the \
             misunderstanding, write what it gives on the inputs the narrowed equation no longer \
             covers, or change a right-hand side or a rewrite rule, or drop the mutation"
        }
        "not-admitted" if reason == Some("inconsistent-mutant") => {
            "fix the mutation: two equations of one function are not shown to agree where both \
             apply, so the mutant may have no model (inconsistent_pairs). If the edit widened a \
             guard, make the guards exclusive or the results equal; if it only narrowed one (the \
             equation gives every input it still covers the value the baseline gives) and \
             no equation of that function ranks after it (priority, owise), no program can kill \
             it whatever the check says, since the specification is one of its models: change a \
             right-hand side or a rewrite rule instead; a narrowing ranked before another \
             equation of its function widens that one, and the mutant may have no model"
        }
        "not-admitted" if reason == Some("stop-unresolved") => {
            "keep the stop's rule a labelled rewrite rule: the edit removes or renames the label a \
             rule of [stop] names, or turns that rule into an equation, so the observation the \
             stop states is not defined on the mutant; edit the rule's sides instead, or name \
             another rule in [stop]"
        }
        "not-admitted" if reason == Some("point-unresolved") => {
            "keep each point rule a labelled rewrite rule: the edit removes or renames the label a \
             point class of [observe] names, or turns that rule into an equation, so the class has \
             no events on the mutant; edit the rule's sides instead (`requires false` keeps the \
             label and states that the rule never fires), or observe another rule"
        }
        "not-admitted" if reason == Some("observation-incompatible") => {
            "keep the declarations of the observed cells' sorts: the edit declares otherwise a \
             sort or symbol the cells [observe] reads reach, or makes a constructor of one head an \
             axiom, so a cell's content could denote another value on the mutant; edit rules \
             instead, or observe other cells"
        }
        "not-admitted" if reason == Some("stop-condition-incompatible") => {
            "keep the declarations of the stop condition's cells: the edit declares otherwise a \
             sort or symbol the cells [stop] when reads reach, or adds a subsort of one, and the \
             condition reads every side's cells as the specification declares them, so the \
             mutant could be asked another question; edit rules instead, or read other cells"
        }
        "not-admitted" => "fix the mutation: the mutant does not compile (reason)",
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
             run `kink-flow coverage FLOW.toml --verify`"
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

/// An executed entry's `slots` (flow F-13): an object keyed by slot name (`slots`, the
/// specification's, [`crate::observed::ResultProjection::slots`]), each `{outcome}`, and for a
/// distinguishing slot `sides`: for
/// `exit-stop` each side's exit-stop kinds (`{"baseline": ["stuck"], "mutant": []}`: an undefined
/// step is no end and has no kind), for `whole-term` (or `cells`, the final term without the
/// cells left out) each side's number of final configurations and,
/// when `killer_terms` (the killing program's entry), the mutant's final configurations as
/// KORE text, each capped at [`KORE_CAP`] characters (`{"text", "truncated"}`). When the two
/// sides' values are not at hand (a cached outcome, or a one-sided kill, whose mutant side is
/// `Unknown`: re-pin L1-2, the mutant's run reached its work budget), the sides are read from the
/// kill's `difference` (CF-16, [`crate::evidence`]): the same shape, each side's count and classes
/// of the ends the difference compared, and for an incomplete mutant side (its run's one-sided
/// ends) `complete: false` (whole-term) or `mutant_complete: false` (exit-stop); null when
/// there is no difference either.
pub fn slots_value(
    slots: &[&str],
    outcomes: &[OracleOutcome],
    baseline: Option<&SideRun>,
    mutant: Option<&SideRun>,
    killer_terms: bool,
    difference: &Value,
) -> Value {
    let side = |run: Option<&SideRun>, slot: usize| match run {
        Some(SideRun::Sides { sides }) => sides.get(slot).cloned(),
        _ => None,
    };
    let names = slots;
    let mut slots = serde_json::Map::new();
    for (slot, outcome) in outcomes.iter().enumerate() {
        // The observation slot follows the end slots (kink-campaign `RunOptions::observe`).
        let name = names.get(slot).copied().unwrap_or(OBSERVATION_SLOT);
        let mut value = json!({"outcome": slot_name(*outcome)});
        if *outcome == OracleOutcome::Distinguish {
            value["sides"] =
                match slot_sides(side(baseline, slot), side(mutant, slot), killer_terms) {
                    Value::Null => difference_sides(name, difference),
                    sides => sides,
                };
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
            let kinds = |stops: &BTreeSet<kink_campaign::ExitStop>| {
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

/// A distinguishing slot's sides read from a kill's `difference` ([`slots_value`]): kink's own
/// evidence names each side's count and classes, a front end's evidence (`krs-difference/3`,
/// sides `left` and `right`) each side's count of ends (`ends`) and whether it is complete. A
/// front end's evidence is given only where both sides have an end (`crate::evidence`), so the
/// exit stop, which under the flow's classifier distinguishes only a side with no end from one
/// with some, has no sides in it; a document of another shape gives none.
fn difference_sides(slot: &str, difference: &Value) -> Value {
    // The observation slot's sides are the two elements of kink's observation evidence
    // ([`crate::evidence`]); null where the kill's evidence is its ends'.
    if slot == OBSERVATION_SLOT {
        return if difference["position"].is_object() {
            json!({
                "baseline": difference["baseline"]["element"],
                "mutant": difference["mutant"]["element"],
            })
        } else {
            Value::Null
        };
    }
    if difference["format"] != crate::evidence::K_EVIDENCE_VERSION {
        let (baseline, mutant) = (&difference["left"], &difference["right"]);
        if !matches!(slot, "whole-term" | "cells")
            || baseline["name"] != "baseline"
            || mutant["name"] != "mutant"
        {
            return Value::Null;
        }
        let mut mutant_side = json!({"final_configurations": mutant["ends"]});
        if mutant["complete"] != true {
            mutant_side["complete"] = json!(false);
        }
        return json!({
            "baseline": {"final_configurations": baseline["ends"]},
            "mutant": mutant_side,
        });
    }
    let (baseline, mutant) = (&difference["baseline"], &difference["mutant"]);
    if !baseline.is_object() || !mutant.is_object() {
        return Value::Null;
    }
    let complete = mutant["complete"] == true;
    match slot {
        "exit-stop" => {
            let mut sides = json!({"baseline": baseline["classes"], "mutant": mutant["classes"]});
            if !complete {
                sides["mutant_complete"] = json!(false);
            }
            sides
        }
        "whole-term" | "cells" => {
            let mut mutant_side = json!({"final_configurations": mutant["final_configurations"]});
            if !complete {
                mutant_side["complete"] = json!(false);
            }
            json!({
                "baseline": {"final_configurations": baseline["final_configurations"]},
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

/// What [`executed_cause`] reads of a mutant's run beyond the runner's evidence, when the session
/// recorded the run: its leaf census, the functions some of whose equations the mutation edits
/// (kink-patch `ClaimSupport::edited_equation_heads`), and the reader that prints a term of it.
#[derive(Clone, Copy)]
pub struct MutantCensus<'c> {
    pub census: &'c LeafCensus,
    pub edited: &'c BTreeSet<String>,
    pub reader: &'c EndReader,
}

/// The application [`mutant_census_clause`] names: the first open application of the census
/// (kink-campaign `LeafCensus::open`) of a function whose equations the mutation edits, with the
/// function's K label. Only an edited function is named: an application of any other function is
/// unreduced for a reason the edit does not name (it may be irreducible in the baseline as well),
/// and an open value that only a rule's condition reads is in no state, so then none is named.
fn named_open(census: MutantCensus<'_>) -> Option<(&OpenApplication, String)> {
    census.census.open.iter().find_map(|open| {
        let label = k_rust::kast::identifier::label_or_name(&open.symbol);
        census.edited.contains(&label).then_some((open, label))
    })
}

/// [`census_clause`] of a mutant's run, and, when a final leaf of it whose state k-rust normalised
/// (stuck, an undefined step, indeterminate or a stop's) holds an application of a function whose equations the
/// mutation edits that no equation of the mutant reduces ([`named_open`]), that leaf's halt and
/// depth and the application, its arguments printed by the command's reader (kink27
/// R5-WEAKENING, fix round 1). A baseline's census is described by
/// [`census_clause`] alone.
fn mutant_census_clause(census: MutantCensus<'_>) -> String {
    let mut clause = census_clause(census.census);
    if let Some(open) = open_clause(census) {
        clause.push_str("; ");
        clause.push_str(&open);
    }
    clause
}

/// The clause of [`mutant_census_clause`] that names the open application ([`named_open`]):
/// `its stuck leaf at depth 0 holds `plus ( s(zero) , zero )`, an application of the function
/// `plus`, ...: the mutant leaves its value open there`; `None` when none is named.
fn open_clause(census: MutantCensus<'_>) -> Option<String> {
    let (open, label) = named_open(census)?;
    let printed = census.reader.print(&open.application, HEAD_CAP);
    let text = printed["text"].as_str().unwrap_or_default();
    let ellipsis = if printed["truncated"] == true {
        "..."
    } else {
        ""
    };
    Some(format!(
        "its {} leaf at depth {} holds `{text}{ellipsis}`, an application of the function \
         `{label}`, whose equations the mutation edits, that no equation of the mutant reduces: \
         the mutant leaves its value open there",
        kebab(&format!("{:?}", open.halt)),
        open.depth,
    ))
}

/// Whether some compared slot of the mutant's run is `unknown` or `timeout` for a reason of its
/// own run: its side is not a value, and the pair's cross-definition judgement did not refuse it
/// (a side refused there ended in a value of its own definition, so its census says nothing of
/// the cause; fz26 KINK-CAUSE-SUBTERM).
fn incomplete(sides: &[OracleSide], across: &[CrossRefusal]) -> bool {
    sides.iter().enumerate().any(|(slot, side)| {
        matches!(side, OracleSide::Unknown | OracleSide::Timeout)
            && !across
                .iter()
                .any(|refusal| refusal.slot == slot && !refusal.baseline_end)
    })
}

/// Whether an executed program's outcome on the mutant is undecided (neither every slot
/// `agree` nor some slot `distinguish`) because the ends of the mutant's run hold open
/// applications of edited functions: the run was compared, a slot of it is undecided for a reason
/// of its own run ([`incomplete`]), some leaf's path is incomplete, and every leaf whose path is
/// incomplete (kink-campaign `RunNotes::incomplete_leaves`) holds, in its state or its path
/// condition, an application of a function the mutation edits that no equation of the mutant
/// reduces (`LeafCensus::leaf_open`, kink-native `open_symbols`). A failed run is undecided for
/// another reason.
///
/// Each such leaf is final and its state one k-rust normalised (kink-native `open_applications`),
/// so the application is one no equation of the mutant reduces. In its state, it makes a stuck,
/// indeterminate or stop leaf's state no value and keeps an undefined step's pre-step
/// configuration from being shown to exist; in its path condition, it leaves open whether the
/// leaf has an instance (an undefined step whose rule's result is undefined where the function's
/// value is, for example). Either way its path is incomplete by that application, and an
/// incomplete path makes every state slot undecided by its stop before any end is read
/// (kink-campaign `state_side`). When every
/// incomplete path is such a leaf's, the slot is undecided by those applications. A leaf whose path is incomplete for
/// another reason (a depth, breadth or work bound, an undecided step, an undecided feasibility)
/// and that holds none keeps the slot undecided by itself, so its program does not have this
/// cause, although its cause may still name an application another leaf holds
/// ([`executed_cause`]). [`OPEN_APPLICATION_REASON`] is the mutation's reason when every
/// undecided program has this cause.
///
/// `census` is the mutant run's leaf census, when the session recorded it, and `edited` the
/// functions some of whose equations the mutation edits (kink-patch
/// `ClaimSupport::edited_equation_heads`), by K label.
#[must_use]
pub fn open_application_cause(
    run: &TestRun,
    mutant: Option<&TestEvidence>,
    census: Option<&LeafCensus>,
    edited: &BTreeSet<String>,
) -> bool {
    let (TestRun::Compared(outcomes), Some(mutant), Some(census)) = (run, mutant, census) else {
        return false;
    };
    let SideRun::Sides { sides } = &mutant.run else {
        return false;
    };
    let leaves = &mutant.notes.incomplete_leaves;
    let edited = |symbols: &BTreeSet<String>| {
        symbols
            .iter()
            .any(|symbol| edited.contains(&k_rust::kast::identifier::label_or_name(symbol)))
    };
    !outcomes.contains(&OracleOutcome::Distinguish)
        && !outcomes
            .iter()
            .all(|outcome| *outcome == OracleOutcome::Agree)
        && incomplete(sides, &mutant.notes.across)
        && !leaves.is_empty()
        && leaves
            .iter()
            .all(|leaf| census.leaf_open.get(*leaf).is_some_and(edited))
}

/// The `reason` of an `unknown` mutation every undecided program of which ends, under the
/// mutant, with an application of a function the mutation edits that no equation of the mutant
/// reduces ([`open_application_cause`]): the end is no value, so kink cannot compare it.
pub const OPEN_APPLICATION_REASON: &str = "open-application";

/// The `cause` of an executed program's outcome on the mutant, from the runner's evidence for
/// that run and, when the session recorded it, the leaf census of the mutant's run: `None` when
/// the outcome is `agree` or `distinguish` (or the test was skipped). `slots` names the slots
/// ([`slots_value`]); `observation` is the observation slot's verdict, under `[observe]`, whose
/// cause is that slot's.
pub fn executed_cause(
    slots: &[&str],
    run: &TestRun,
    mutant: Option<&SideRun>,
    across: &[CrossRefusal],
    budget: Budget,
    census: Option<MutantCensus<'_>>,
    observation: Option<&ObservationVerdict>,
) -> Option<String> {
    match run {
        TestRun::SkippedAfterKill => None,
        TestRun::Failed(kind) => Some(match (kind, census) {
            (ExecutionFailureKind::TimeLimit, Some(census)) => format!(
                "{}; when the bound fired {}",
                failure_cause(*kind, budget),
                mutant_census_clause(census)
            ),
            (ExecutionFailureKind::ResourceLimit, Some(census)) => format!(
                "{}; the mutant's run: {}",
                failure_cause(*kind, budget),
                mutant_census_clause(census)
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
            // The open application the mutant's run ends holding, when one is named: the cause
            // leads with it, and a slot it leaves undecided needs no list of every other way a
            // run can end short of a value, which the census still shows.
            let open = census
                .filter(|_| incomplete(sides, across))
                .and_then(open_clause);
            // Slots with the same cause are named together: `exit-stop, whole-term: <cause>`.
            let mut groups: Vec<(Vec<&str>, String)> = Vec::new();
            // An unknown or timed-out side: the census tells a depth bound from an undecided end.
            let refused = |slot: usize, baseline_end: bool| {
                across
                    .iter()
                    .find(|refusal| refusal.slot == slot && refusal.baseline_end == baseline_end)
            };
            for (slot, outcome) in outcomes.iter().enumerate() {
                if *outcome == OracleOutcome::Agree {
                    continue;
                }
                let name = slots.get(slot).copied().unwrap_or(OBSERVATION_SLOT);
                if slot >= slots.len() {
                    // The observation slot: its verdict says why it is not decided.
                    let cause = observation
                        .and_then(|verdict| verdict.cause.clone())
                        .unwrap_or_else(|| slot_cause(*outcome, None, budget));
                    match groups.iter_mut().find(|(_, existing)| *existing == cause) {
                        Some((names, _)) => names.push(name),
                        None => groups.push((vec![name], cause)),
                    }
                    continue;
                }
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
                    || match (sides.get(slot), &open) {
                        (Some(OracleSide::Unknown), Some(_)) => {
                            "the mutant's run did not end in a value kink can compare".to_owned()
                        }
                        (side, _) => slot_cause(*outcome, side, budget),
                    },
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
            if let Some(open) = &open {
                cause = format!("{open}; {cause}");
            }
            if let (true, Some(census)) = (incomplete(sides, across), census) {
                // With the open application named first, the census follows without it.
                let clause = if open.is_some() {
                    census_clause(census.census)
                } else {
                    mutant_census_clause(census)
                };
                cause.push_str(&format!("; the mutant's run: {clause}"));
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
             where the definition leaves it open, with no run-level record of the value \
             (String2Bytes, Bytes2String, and the hooks no builtin file documents)"
                .into()
        }
        ExecutionFailureKind::ShortCircuitReading => {
            "short-circuit-reading: a run of this program (the mutant's, or the baseline's) read \
             the definedness of an operand a short-circuiting backend may skip, the operand after \
             the deciding one of andBool, orBool, impliesBool, #if, andThenBool or orElseBool, \
             which k-rust found undefined or left undecided at a step its definition's \
             short-circuit analysis does not clear, so another reading the definition leaves to \
             the backend may give that run another result"
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
        ExecutionFailureKind::PassedStop => {
            "passed-stop: a run of this program went on past a step of a stop rule that had \
             another successor, so its ends need not be the ends of the observation the stop \
             states"
                .into()
        }
        ExecutionFailureKind::StopCondition => {
            "stop-condition: the stop condition ([stop] when) was left undecided at an arrival of \
             the mutant's run of this program (its evaluation ran out of its budget, or the \
             solver answered unknown), or had no value there, so whether the run ended where the \
             condition says is not known"
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

/// The action of a `survived` row whose mutation expects to survive, met
/// ([`mutation_expectation`]) with no qualification ([`survival_limits`]): the run asks nothing
/// of a control the corpus does not kill.
pub const EXPECTED_SURVIVOR_ACTION: &str = "nothing: it survived, as its expectation states";

/// The `expectation` member of a mutation row whose mutation states `expect` (the row's own
/// `expect`, [`crate::Expect`]): `{verdict, detail}`, `verdict` `met`, `unmet` or `inconclusive`
/// as the row's `status` answers the claim, null for a row without `expect`. It is a function of
/// the row's status, which does not depend on the schedule, so it is the same under `--full` and
/// first-kill; `detail` names what the row says against the claim (the killers, the status, the
/// programs left undecided), and says when a met control is vacuous or met only within limits.
///
/// - `killed`: a kill is a difference in every model, so a control's claim is false of the
///   corpus (unmet) and a kill expectation's met.
/// - `survived`: no program distinguished, so a control is met and a kill expectation unmet. A
///   survival that rests on a horizon (`horizon`) or on a stop that hides the edit
///   (`stop_hides_edit`) is weaker: no program observed past the horizon, or took the edited step,
///   so the control is met only within what the runs observed, and `detail` says so
///   ([`survival_limits`]).
/// - `equivalent`, `unkillable`: no program of any corpus can kill the mutant, which a control's
///   claim follows from (met, but vacuous: it tests no observation) and a kill expectation's
///   contradicts (unmet).
/// - `timeout`, `unknown`: kink could not decide whether some program distinguishes, so the claim
///   is neither confirmed nor refuted (inconclusive).
/// - every other status (`invalid-mutation`, `not-admitted`, `error`): no verdict exists to check
///   (inconclusive); the row's own status already fails the run.
#[must_use]
pub fn mutation_expectation(row: &Value) -> Value {
    let Some(expect) = row["expect"].as_str().and_then(crate::Expect::parse) else {
        return Value::Null;
    };
    let survive = expect == crate::Expect::Survive;
    let expected = if survive {
        "expected to survive"
    } else {
        "expected to be killed"
    };
    let status = row["status"].as_str().unwrap_or("no status");
    let (verdict, detail) = match status {
        "killed" if survive => (
            "unmet",
            Some(format!("{expected}, killed by {}", killers(row))),
        ),
        "killed" => ("met", None),
        "survived" if survive => ("met", survival_limits(row)),
        "survived" => ("unmet", Some(format!("{expected}, survived"))),
        "equivalent" | crate::search::UNKILLABLE if survive => (
            "met",
            Some(format!(
                "vacuous: the mutant is {status}, so no program of any corpus can kill it, and the \
                 expectation tests no observation"
            )),
        ),
        "equivalent" | crate::search::UNKILLABLE => (
            "unmet",
            Some(format!(
                "{expected}, {status}: no program of any corpus can kill it"
            )),
        ),
        "timeout" | "unknown" => (
            "inconclusive",
            Some(format!(
                "{expected}, {}: not confirmed",
                undecided(row, status)
            )),
        ),
        _ => (
            "inconclusive",
            Some(format!(
                "{expected}, but it has no verdict: {}",
                with_reason(row, status)
            )),
        ),
    };
    json!({"verdict": verdict, "detail": detail})
}

/// What limits a met control's survival, null when nothing does: a survivor some program of
/// which agreed only up to the horizon of a baseline's observation channel (`horizon`), on which
/// the mutant may differ past it, and one whose edited rule's step the stop hides from every
/// program (`stop_hides_edit`), on which no run shows what the edit changes. Either way the
/// control's claim holds only of what the runs observed, which is weaker than survival.
fn survival_limits(row: &Value) -> Option<String> {
    let mut limits = Vec::new();
    let horizons = row["horizon"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|entry| entry["program"].as_str())
        .collect::<Vec<_>>();
    if !horizons.is_empty() {
        limits.push(format!(
            "{} agreed only up to the horizon of a baseline's observation channel (horizon), and \
             the mutant may differ past it",
            horizons.join(", ")
        ));
    }
    if row["stop_hides_edit"]
        .as_array()
        .is_some_and(|hidden| !hidden.is_empty())
    {
        limits.push(
            "the stop hides the edit from every program (stop_hides_edit), so no run shows what \
             it changes"
                .to_owned(),
        );
    }
    (!limits.is_empty()).then(|| {
        format!(
            "met only within what the runs observed: {}; the row's action says what would \
             observe more",
            limits.join("; ")
        )
    })
}

/// The programs that killed a row: its `killed_by` (`--full`), else its `killer`.
fn killers(row: &Value) -> String {
    let all = row["killed_by"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .collect::<Vec<_>>();
    if all.is_empty() {
        row["killer"].as_str().unwrap_or("a program").to_owned()
    } else {
        all.join(", ")
    }
}

/// `status` with each program the row's search left undecided and its cause (`executed` entries
/// whose outcome is neither `agree` nor `distinguish`), or with the row's reason when it names
/// none.
fn undecided(row: &Value, status: &str) -> String {
    let programs = row["executed"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|entry| entry["outcome"] != "agree" && entry["outcome"] != "distinguish")
        .filter_map(|entry| {
            let program = entry["program"].as_str()?;
            let cause = entry["cause"]
                .as_str()
                .or_else(|| entry["outcome"].as_str())
                .unwrap_or("undecided");
            Some(format!("{program}: {cause}"))
        })
        .collect::<Vec<_>>();
    if programs.is_empty() {
        with_reason(row, status)
    } else {
        format!("{status} ({})", programs.join("; "))
    }
}

/// `status`, with the row's reason in parentheses when it has one.
fn with_reason(row: &Value, status: &str) -> String {
    match row["reason"].as_str() {
        Some(reason) => format!("{status} ({reason})"),
        None => status.to_owned(),
    }
}

/// Each row's `expectation` ([`mutation_expectation`]), and the `survived` row of a met control
/// whose survival nothing limits asks nothing ([`EXPECTED_SURVIVOR_ACTION`]; one resting on a
/// horizon or a hidden edit keeps its action); the run document's `expectations`: the ids of the
/// rows whose expectation is `met`, `unmet` and `inconclusive`, in row order, and `unchecked`,
/// the ids of the mutations of `list` that state `expect` and have no row (the run stopped before
/// them at a corpus error, or `--only` left them out), in list order, so that no expectation the
/// run did not check reads as met.
pub fn check_expectations(mutations: &mut [Value], list: &[Mutation]) -> Value {
    let mut verdicts = BTreeMap::from([
        ("met", Vec::new()),
        ("unmet", Vec::new()),
        ("inconclusive", Vec::new()),
        ("unchecked", Vec::new()),
    ]);
    for row in mutations.iter_mut() {
        let expectation = mutation_expectation(row);
        if let Some(ids) = expectation["verdict"]
            .as_str()
            .and_then(|verdict| verdicts.get_mut(verdict))
        {
            ids.push(row["id"].clone());
        }
        if row["status"] == "survived"
            && row["expect"] == crate::Expect::Survive.as_str()
            && expectation["verdict"] == "met"
            && expectation["detail"].is_null()
        {
            row["action"] = json!(EXPECTED_SURVIVOR_ACTION);
        }
        row["expectation"] = expectation;
    }
    let unchecked = list
        .iter()
        .filter(|mutation| mutation.expect.is_some())
        .filter(|mutation| {
            !mutations
                .iter()
                .any(|row| row["id"] == mutation.id.as_str())
        })
        .map(|mutation| json!(mutation.id))
        .collect();
    verdicts.insert("unchecked", unchecked);
    json!(verdicts)
}

/// One line per mutation row of a run document whose expectation is unmet or inconclusive
/// (`mutation ID: DETAIL`), in row order, which both front ends print on stderr whatever the
/// output format: a run that fails on an expectation says which.
#[must_use]
pub fn expectation_lines(document: &Value) -> Vec<String> {
    document["mutations"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|row| {
            matches!(
                row["expectation"]["verdict"].as_str(),
                Some("unmet" | "inconclusive")
            )
        })
        .map(|row| {
            format!(
                "mutation {}: {}",
                row["id"].as_str().unwrap_or("?"),
                row["expectation"]["detail"].as_str().unwrap_or("no detail")
            )
        })
        .collect()
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

/// The kill matrix of a full run (`run --full`), from its program rows (the `coverage` rows, in
/// corpus order) and its mutation rows: `{programs: [{id, kills, sole_killer_of, undecided}]}`,
/// one entry per program that can kill (`comparable` or `comparable-prefix`), in corpus order (a list, since a JSON
/// object would order the ids by name). `kills` are the mutations (in row order) whose
/// `killed_by` holds the program, `sole_killer_of` those whose `killed_by` is exactly the
/// program, and `undecided` those whose `executed` has an entry of the program with an outcome
/// other than `agree` and `distinguish` (a timeout, an unknown, an incomparable, an error or a
/// failed run): the cells where the program might kill and the run could not tell. A row with no
/// cell (a mutation that does not resolve, an `unkillable` one, a corpus error, a mutant that
/// failed as a whole) is in no list. Nothing reads it back.
pub fn matrix(programs: &[Value], mutations: &[Value]) -> Value {
    let comparable = programs
        .iter()
        .filter(|row| ResultClass::can_kill(&row["class"]))
        .map(|row| {
            let id = &row["id"];
            let ids = |keep: &dyn Fn(&Value) -> bool| {
                mutations
                    .iter()
                    .filter(|mutation| keep(mutation))
                    .map(|mutation| mutation["id"].clone())
                    .collect::<Vec<_>>()
            };
            let killed_by = |mutation: &Value| {
                mutation["killed_by"]
                    .as_array()
                    .map(Vec::as_slice)
                    .unwrap_or_default()
                    .to_vec()
            };
            json!({
                "id": id,
                "kills": ids(&|mutation| killed_by(mutation).contains(id)),
                "sole_killer_of": ids(&|mutation| killed_by(mutation) == [id.clone()]),
                "undecided": ids(&|mutation| {
                    mutation["executed"].as_array().into_iter().flatten().any(|entry| {
                        entry["program"] == *id
                            && entry["outcome"] != "agree"
                            && entry["outcome"] != "distinguish"
                    })
                }),
            })
        })
        .collect::<Vec<_>>();
    json!({"programs": comparable})
}

/// Every program that cannot kill (its result class is not `comparable`), once, from the
/// `coverage` rows: `{id, class, cause}`.
pub fn unusable_programs(programs: &[Value]) -> Vec<Value> {
    programs
        .iter()
        .filter(|row| !ResultClass::can_kill(&row["class"]))
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
    targeted: &BTreeSet<kink_patch::SentenceRef>,
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
    report_spelled(manifest, options, &crate::cli::KinkFlowSpelling)
}

/// [`report`], the next steps of a missing or unreadable report spelled by `spelling`.
pub fn report_spelled(
    manifest: &FlowManifest,
    options: &ReportOptions,
    spelling: &dyn CommandSpelling,
) -> (Value, bool) {
    stored_report(&manifest.directory, options, spelling)
}

/// [`report_spelled`] for the corpus whose manifest is in `directory`: the stored report is a
/// file of the cache, and the cache directory is a function of the manifest's directory and
/// `--cache` alone, so a front end prints it without loading or building the specification.
pub fn stored_report(
    directory: &Path,
    options: &ReportOptions,
    spelling: &dyn CommandSpelling,
) -> (Value, bool) {
    let path = corpus_cache_directory(directory, options.cache.as_deref()).join(REPORT_FILE);
    match read_report(&path, spelling) {
        Ok(document) => (document, true),
        // Version 2 names, under the Z3 profile, the Z3 build of the process that looked
        // (`z3`, `crate::with_z3_build`), as every kink-flow document does: a stored run document
        // decided on another build is `unreadable`, and the two builds are then both named.
        Err((outcome, detail)) => (
            crate::with_z3_build(json!({
                "schema": MISSING_SCHEMA,
                "version": 2,
                "k_rust_revision": crate::k_rust_revision(),
                "profile": SolverProfile::BUILD.name(),
                "outcome": outcome,
                "path": path.display().to_string(),
                "detail": detail,
            })),
            false,
        ),
    }
}

/// The stored run document, or `(outcome, detail)` with outcome `missing` or `unreadable`.
fn read_report(
    path: &Path,
    spelling: &dyn CommandSpelling,
) -> Result<Value, (&'static str, String)> {
    let text = fs::read_to_string(path).map_err(|e| {
        (
            "missing",
            format!(
                "no run report ({e}): run `{}` first",
                spelling.command(Verb::Run)
            ),
        )
    })?;
    let again = spelling.verb(Verb::Run);
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
                 run `{again}` again",
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
                 code this build no longer runs: run `{again}` again"
            ),
        ));
    }
    if let Some(key) = kink_campaign::identity_difference(&document["kink"]) {
        return Err((
            "unreadable",
            format!(
                "the report was written under another kink identity (`{key}` is missing or \
                 differs), so its statuses may rest on algorithms this build no longer runs: run \
                 `{again}` again"
            ),
        ));
    }
    // Under the Z3 profile the statuses are a function of the Z3 build the document names
    // (`z3`), which a dynamically linked Z3 keeps outside the build identity above.
    if let Some(reason) =
        kink_campaign::z3_difference(document.get("z3"), &kink_campaign::z3_build())
    {
        return Err((
            "unreadable",
            format!(
                "the report is not this Z3 build's ({reason}), so its statuses may rest on solver \
                 answers this build does not give: run `{again}` again"
            ),
        ));
    }
    Ok(document)
}

#[cfg(test)]
mod tests {
    use super::*;
    use kink_campaign::{RunNotes, RunStop};
    use std::collections::BTreeMap;

    /// A mutant run's evidence with both slots `unknown` and the leaves whose paths the bridge
    /// left incomplete.
    fn unknown(incomplete: &[usize]) -> TestEvidence {
        TestEvidence {
            test_id: "t".into(),
            run: SideRun::Sides {
                sides: vec![OracleSide::Unknown, OracleSide::Unknown],
            },
            notes: RunNotes {
                incomplete_leaves: incomplete.iter().copied().collect(),
                ..RunNotes::default()
            },
            ends: BTreeSet::new(),
            undefined_steps: false,
            one_sided_ends: BTreeSet::new(),
            stop_ends: BTreeSet::new(),
            payloads: BTreeMap::new(),
        }
    }

    /// A census whose leaves hold, each, the open applications of these KORE symbols.
    fn census(leaf_open: &[&[&str]]) -> LeafCensus {
        LeafCensus {
            stop: RunStop::Finished,
            leaves: BTreeMap::new(),
            deepest: None,
            rule_ids: BTreeSet::new(),
            work: Some(1),
            open: Vec::new(),
            leaf_open: leaf_open
                .iter()
                .map(|symbols| symbols.iter().map(|s| (*s).to_owned()).collect())
                .collect(),
        }
    }

    /// A program is undecided by an open application only when every leaf whose path is
    /// incomplete holds an application of an edited function: a leaf incomplete for another
    /// reason (here a depth-bound leaf, which holds none) keeps the slots undecided by itself,
    /// whatever another leaf holds. A run with no incomplete path, a failed run, a run some slot
    /// of which distinguishes, and an application of a function the mutation does not edit give
    /// no such cause.
    #[test]
    fn an_open_application_is_the_cause_only_when_every_incomplete_leaf_holds_one() {
        let edited = BTreeSet::from(["f".to_owned()]);
        let undecided = TestRun::Compared(vec![OracleOutcome::Unknown, OracleOutcome::Unknown]);
        let cause = |run: &TestRun, incomplete: &[usize], leaves: &[&[&str]]| {
            open_application_cause(
                run,
                Some(&unknown(incomplete)),
                Some(&census(leaves)),
                &edited,
            )
        };
        assert!(cause(&undecided, &[0], &[&["Lblf"]]));
        assert!(cause(&undecided, &[1], &[&[], &["Lblf", "Lblg"]]));
        assert!(cause(&undecided, &[0, 1], &[&["Lblf"], &["Lblf"]]));
        // A second leaf incomplete for another reason.
        assert!(!cause(&undecided, &[0, 1], &[&["Lblf"], &[]]));
        // An application of a function the mutation does not edit.
        assert!(!cause(&undecided, &[0], &[&["Lblg"]]));
        // No incomplete path, or a leaf the census does not know.
        assert!(!cause(&undecided, &[], &[&["Lblf"]]));
        assert!(!cause(&undecided, &[2], &[&["Lblf"]]));
        // Not undecided.
        let distinguished =
            TestRun::Compared(vec![OracleOutcome::Distinguish, OracleOutcome::Unknown]);
        assert!(!cause(&distinguished, &[0], &[&["Lblf"]]));
        let agreed = TestRun::Compared(vec![OracleOutcome::Agree, OracleOutcome::Agree]);
        assert!(!cause(&agreed, &[0], &[&["Lblf"]]));
        assert!(!cause(
            &TestRun::Failed(ExecutionFailureKind::TimeLimit),
            &[0],
            &[&["Lblf"]]
        ));
        // Without a recorded census nothing is known of the leaves.
        assert!(!open_application_cause(
            &undecided,
            Some(&unknown(&[0])),
            None,
            &edited
        ));
    }

    /// A mutant the stop condition cannot read is `not-admitted` under the reason its
    /// mutant-scope failure is named by, `stop-condition-incompatible`, and the action says what
    /// to keep, not that the mutant does not compile; a run whose condition gave no answer is
    /// `unknown` with the cause `stop-condition`.
    #[test]
    fn a_stop_condition_names_its_reason_its_action_and_its_cause() {
        let reason = crate::results::kebab(&format!(
            "{:?}",
            kink_campaign::MutantScopeFailure::StopConditionIncompatible
        ));
        assert_eq!(reason, "stop-condition-incompatible");
        assert_eq!(
            kink_campaign::MutantScopeFailure::StopConditionIncompatible.status(),
            kink_campaign::MutantStatus::NotAdmitted
        );
        let given = action("not-admitted", Some(&reason)).unwrap();
        assert!(given.contains("stop condition's cells"), "{given}");
        assert_ne!(Some(given), action("not-admitted", None));
        let cause = failure_cause(ExecutionFailureKind::StopCondition, Budget::default());
        assert!(cause.starts_with("stop-condition: "), "{cause}");
    }
}
