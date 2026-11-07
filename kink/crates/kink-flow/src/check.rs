//! The resolve-only check of a mutation list (`kink-flow check FLOW.toml --mutations LIST`): every
//! mutation is resolved against the current specification, exactly as `run` resolves it, and no
//! program runs. It is the compile step of an author's loop: each mutation is shown as the rules
//! it edits (before and after, label, file and lines), refused with its reason and next step when
//! it does not resolve, and warned about when it resolves but is likely to mislead.
//!
//! Refusals are resolution's ([`InvalidReason`]): a stale anchor (`unknown-label`,
//! `find-not-found`, `source-changed`, ...), overlapping edits, a sentence that is not a rule, an
//! edit that changes nothing (`no-change`), and the others of the reason table. A refused
//! mutation is one `run` gives the status `invalid-mutation`.
//!
//! The check compiles no mutant, so `ok` means that the mutation resolves, not that `run` will
//! judge it: a mutant that kink does not compile (an unbound variable in the replacement, say) or
//! whose equations may have no model (`inconsistent-mutant`) is found only by `run`, as the status
//! `not-admitted`.
//!
//! Warnings change no status:
//! - `line-anchor`: an edit addressed by `line`, and `text-anchor`: one addressed by `find` alone.
//!   Neither anchor names the rule, so an edit of the specification can move the mutation onto
//!   another rule that happens to hold the same text at that place; the next step names the
//!   rule's label when it has one (the rule the edit alone is addressed to, also when its
//!   mutation is refused for another reason).
//! - `no-coverage-signal`: an edited rule k-rust's coverage cannot record, so no program can be
//!   shown to match it.
//! - `unmatched-rule`: an edited rule no comparable program matched (k-rust `matched`: began to
//!   decide a matched instance's condition) in the cached results, so no program exercises it.
//!   Which programs witness the mutant's edit is read from the compiled mutant (`run`'s program
//!   order), and `check` compiles none: a program can still witness it through what else the
//!   edit changes, such as a widened left-hand side or a claim it withdraws.
//! - `unapplied-rule`: an edited rule some comparable program matched but none applied (k-rust
//!   `applied`: built a candidate of it, defined or rolled back), so every program that matches
//!   it refutes its `requires`. An edit of only the rule's right-hand side or `ensures` keeps its
//!   left-hand side, condition and attributes, so each program's run of the mutant refutes the
//!   edited rule where its baseline run refuted the rule, and no program of the corpus can kill
//!   the edit except through a claim it withdraws or another rule the mutation edits. The
//!   warning is about the edited rule, not the edit, which `check` does not compile: an edit of
//!   the `requires` or the left-hand side can still be killed by a program that matches the
//!   rule, since the edited guard, or the old guard under the edited bindings, can hold where
//!   the old one was refuted. An attribute edit or a deletion keeps the guard wherever the rule
//!   stays, and a rule whose guard is refuted takes no step and blocks no lower priority group
//!   wherever it is placed, so no program's run of the mutant differs at a state where it
//!   matched the rule: such an edit shows only at a state where the rule was a candidate whose
//!   condition the run did not decide (k-rust `offered`, which kink does not collect), such as
//!   one where a higher priority group took the step a raised priority now gives the rule.
//! - `stop-hides-edit`: an edited rule that `[stop]` stops before, where some program's count is
//!   one. Such a program's run ends at the state from which the rule's step is the one successor,
//!   before the step, so the rule's right-hand side and `ensures` build nothing any end holds:
//!   an edit of only those survives on that program whatever it changes. With a count `N` above
//!   1 the run takes the rule's first `N - 1` steps, and an edit of the rule's left-hand side,
//!   `requires` or attributes changes where the stops are, so either can still be killed. Like
//!   `unapplied-rule`, the warning is about the edited rule, since `check` compiles no mutant to
//!   tell which part an edit changes; the run document repeats it on a survivor
//!   (`stop_hides_edit`). Under a stop condition (`[stop] when`) a path takes the rule's step at
//!   every arrival where the condition fails, so the count alone does not say whether a step is
//!   taken: the warning is given for such a rule exactly when the coverage decides (as for
//!   `unmatched-rule`) and no comparable program's run took its step (k-rust `committed`, the
//!   record's `fired_sentences`), which is the case where every arrival of every path was an event
//!   and the path ended at the first.
//! - `stop-rule-deleted`: the mutation deletes a rule `[stop]` names. A deleted rule takes its
//!   label with it, so the stop names no rule of the mutant, and `run` reports the mutant
//!   `not-admitted` (`stop-unresolved`) instead of judging it; the edit's other changes are never
//!   observed. Given in place of `stop-hides-edit` for that rule.
//!
//! The two coverage warnings, `unmatched-rule` and `unapplied-rule`, are given only when every
//! program has a current result record and every comparable program's coverage is complete;
//! otherwise the document's `coverage` says why there is no such warning. A program whose result
//! is never cached (a timeout, an error, an `unknown` the host caused, or every program where the
//! result cache is off, `results::result_store`) has no record, so while the corpus holds one
//! neither warning is given: which programs are comparable is then a fact of the host's run, not
//! of the cached results.
//!
//! [`check_mutations`] returns the typed result, so that a front end can add findings of its own
//! before the document is rendered: a finding with `refusal: true` refuses its mutation as a
//! resolution failure does. The whole command is
//! [`crate::cli::check_corpus_mutations`] (admission, coverage and this check, as data) followed
//! by [`crate::cli::check_mutations_document`] (the document and the exit status), so a front
//! end adds its findings between the two and renders the document `kink-flow check` renders. The KRS front end adds there what only it
//! can judge (edits of nodes KRS generated, overlap by KRS's rules, claim helpers); kink-flow
//! itself knows only K.

use crate::{
    admit::{AdmittedSpec, FlowAdmission, InputSession, ProgramAdmission, admit_spec},
    cli::{CommandSpelling, Verb},
    digest::execution_digest,
    manifest::FlowManifest,
    mutation::{
        InvalidMutation, Mutation, MutationList, ResolvedMutation, addressed_rule, resolve,
    },
    report::rules_value,
    results::{ResultClass, cache_directory, current_record, no_coverage_signal, result_store},
};
use kink_corpus::LoadedSource;
use kink_patch::SentenceRef;
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::Path,
};

/// One finding of the check about a mutation: a warning, or a refusal a front end adds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding {
    /// Whether the finding refuses the mutation (a front end's check); kink-flow's own findings
    /// are warnings, and its refusals are the resolution's.
    pub refusal: bool,
    /// A kebab-case name (`line-anchor`, `unmatched-rule`, ...).
    pub reason: String,
    /// The index of the edit the finding is about, when one is.
    pub edit: Option<usize>,
    /// The baseline sentence the finding is about, when one is.
    pub at: Option<SentenceRef>,
    pub detail: String,
    /// What the author does next.
    pub next: Option<String>,
}

impl Finding {
    /// A warning.
    pub fn warning(
        reason: &str,
        edit: Option<usize>,
        at: Option<SentenceRef>,
        detail: String,
        next: Option<String>,
    ) -> Self {
        Self {
            refusal: false,
            reason: reason.to_owned(),
            edit,
            at,
            detail,
            next,
        }
    }

    /// A refusal: a front end's check that refuses the mutation, as a resolution failure does.
    pub fn refused(
        reason: &str,
        edit: Option<usize>,
        at: Option<SentenceRef>,
        detail: String,
        next: Option<String>,
    ) -> Self {
        Self {
            refusal: true,
            ..Self::warning(reason, edit, at, detail, next)
        }
    }

    fn value(&self) -> Value {
        json!({
            "reason": self.reason,
            "edit": self.edit,
            "rule": self.at.as_ref().map(|at| json!({"module": at.module, "index": at.index})),
            "detail": self.detail,
            "next": self.next,
        })
    }
}

/// The check of one mutation.
#[derive(Clone, Debug)]
pub struct MutationCheckRow {
    pub id: String,
    pub misunderstanding: String,
    /// The resolution `run` would compute.
    pub resolution: Result<ResolvedMutation, InvalidMutation>,
    /// kink-flow's warnings, then those a front end adds.
    pub findings: Vec<Finding>,
    /// A front end's own keys of the row (the krs front end's `krs`), rendered after kink-flow's
    /// keys; a key kink-flow's row already has is not rendered. Empty for kink-flow.
    pub extra: Map<String, Value>,
}

impl MutationCheckRow {
    /// Whether the mutation is refused: it does not resolve, or a finding refuses it.
    pub fn refused(&self) -> bool {
        self.resolution.is_err() || self.findings.iter().any(|finding| finding.refusal)
    }

    /// The row of the check document: `{id, misunderstanding, outcome, digest, rules, refusals,
    /// warnings}`, then the keys of [`Self::extra`]. `outcome` is `ok`, `refused`, or `error` for a
    /// resolution the host refused (`host-stack-refused`, not a fault of the mutation); `rules` is
    /// null when the mutation does not resolve; each refusal and warning is `{reason, edit, rule,
    /// detail, next}`.
    pub fn value(&self) -> Value {
        let mut refusals = Vec::new();
        let (outcome, digest, rules) = match &self.resolution {
            Ok(resolved) => (
                "ok",
                json!(resolved.digest.to_string()),
                rules_value(&resolved.rules),
            ),
            Err(invalid) => {
                refusals.push(json!({
                    "reason": invalid.reason.as_str(),
                    "edit": invalid.edit,
                    "rule": null,
                    "detail": invalid.detail,
                    "next": invalid.reason.next_step(),
                }));
                (
                    if invalid.reason.status() == "error" {
                        "error"
                    } else {
                        "refused"
                    },
                    Value::Null,
                    Value::Null,
                )
            }
        };
        refusals.extend(
            self.findings
                .iter()
                .filter(|finding| finding.refusal)
                .map(Finding::value),
        );
        let outcome = if outcome == "ok" && !refusals.is_empty() {
            "refused"
        } else {
            outcome
        };
        let mut row = json!({
            "id": self.id,
            "misunderstanding": self.misunderstanding,
            "outcome": outcome,
            "digest": digest,
            "rules": rules,
            "refusals": refusals,
            "warnings": self
                .findings
                .iter()
                .filter(|finding| !finding.refusal)
                .map(Finding::value)
                .collect::<Vec<_>>(),
        });
        if let Value::Object(row) = &mut row {
            for (key, value) in &self.extra {
                if !row.contains_key(key) {
                    row.insert(key.clone(), value.clone());
                }
            }
        }
        row
    }
}

/// The check of a whole mutation list, in list order.
#[derive(Clone, Debug)]
pub struct MutationCheck {
    pub rows: Vec<MutationCheckRow>,
}

impl MutationCheck {
    /// Whether some mutation is refused.
    pub fn refused(&self) -> bool {
        self.rows.iter().any(MutationCheckRow::refused)
    }

    /// The check document's `mutations`.
    pub fn value(&self) -> Value {
        Value::Array(self.rows.iter().map(MutationCheckRow::value).collect())
    }
}

/// Which rules the corpus's cached results show programs witness, read without running
/// anything ([`corpus_coverage`]).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CorpusCoverage {
    /// Why the result cache is off (`results::result_store`), when it is: no program then has a
    /// record.
    pub cache_off: Option<&'static str>,
    /// The programs with no current result record: never run under this specification and
    /// build, refused before a record could be made, or with a result that is never cached (a
    /// timeout, an error, an `unknown` the host caused), which every command computes again.
    pub without_record: Vec<String>,
    /// The comparable programs whose recorded coverage is incomplete (their run stopped before
    /// it explored everything, so it may use rules it does not list).
    pub incomplete: Vec<String>,
    /// The rules some comparable program matched (k-rust `matched`).
    pub matched: BTreeSet<SentenceRef>,
    /// The rules some comparable program applied (k-rust `applied`), a subset of `matched`.
    pub applied: BTreeSet<SentenceRef>,
    /// The rules some comparable program fired (k-rust `committed` for a rewrite rule: some path
    /// of its run took the rule's step), a subset of `applied`.
    pub fired: BTreeSet<SentenceRef>,
    /// The rules k-rust's coverage cannot record, with the reason.
    pub no_signal: BTreeMap<SentenceRef, &'static str>,
}

impl CorpusCoverage {
    /// Whether the coverage decides that a rule is unmatched: every program has a current
    /// record and every comparable program's coverage is complete.
    pub fn decides(&self) -> bool {
        self.without_record.is_empty() && self.incomplete.is_empty()
    }

    /// The check document's `coverage`: `{decides, without_record, incomplete, detail}`, its
    /// next step spelled by `spelling`.
    pub fn value(&self, spelling: &dyn CommandSpelling) -> Value {
        let detail = if self.decides() {
            Value::Null
        } else if let Some(reason) = self.cache_off {
            json!(format!(
                "no unmatched-rule or unapplied-rule warning is given: it needs a current result \
                 record of every program, and {reason}"
            ))
        } else {
            json!(format!(
                "no unmatched-rule or unapplied-rule warning is given: it needs a current result \
                 record of every program and complete coverage of every comparable program. A \
                 program without a record has not run under this specification (run `{}`), or its result is never \
                 cached (a timeout, an error, or an unknown the host caused; its row in `results` \
                 says `not_cached`): bound baselines by work with [budget] baseline_max_work, so \
                 that a run that does not finish is a cached unknown, and fix an error",
                spelling.command(Verb::Results)
            ))
        };
        json!({
            "decides": self.decides(),
            "without_record": self.without_record,
            "incomplete": self.incomplete,
            "detail": detail,
        })
    }
}

/// The admission of `manifest` (`crate::admit::admit`) with each case's expectation checked
/// against its current result record in the cache directory `cache` (default `.kink-flow/` next
/// to `FLOW.toml`), read without running a program or writing anything ([`expect_recorded`]).
pub fn admit_checked(manifest: &FlowManifest, cache: Option<&Path>) -> FlowAdmission {
    let (record, admitted) = admit_spec(manifest);
    let Some((spec, mut inputs)) = admitted else {
        return FlowAdmission {
            record,
            spec: None,
            programs: Vec::new(),
            stop: manifest.stop_value(),
        };
    };
    let programs = {
        let mut session = inputs.session(&spec);
        let mut programs = manifest
            .programs
            .iter()
            .map(|program| session.admit(program))
            .collect::<Vec<_>>();
        let cache = cache_directory(manifest, cache);
        expect_recorded(&spec, manifest, &session, &cache, &mut programs);
        programs
    };
    FlowAdmission {
        record,
        spec: Some(spec),
        programs,
        stop: manifest.stop_value(),
    }
}

/// Why the check document has no baseline to check a case's expectation against.
const NO_RECORD: &str = "the case has no current result record to check the expectation \
     against: it has not run under this specification and build (run `results`), or its result is \
     never cached (a timeout, an error, or an unknown the host caused)";

/// Each admission of `programs` (one per manifest program, in order) whose program has `expect`,
/// with its expectation checked against the program's current result record in the cache
/// directory `cache`, read without running anything (`crate::expect`): inconclusive for a refused
/// program and for one without a record.
pub fn expect_recorded(
    spec: &AdmittedSpec,
    manifest: &FlowManifest,
    inputs: &InputSession<'_>,
    cache: &Path,
    programs: &mut [ProgramAdmission],
) {
    if manifest
        .programs
        .iter()
        .all(|program| program.expect.is_none())
    {
        return;
    }
    let execution = execution_digest(manifest, spec);
    for (program, admission) in manifest.programs.iter().zip(programs) {
        if program.expect.is_none() {
            continue;
        }
        let record = match &admission.outcome {
            Err(_) => None,
            Ok(_) => inputs
                .admitted_inputs(program)
                .ok()
                .and_then(|case| current_record(manifest, execution, program, &case, cache)),
        };
        let baseline = match (&admission.outcome, &record) {
            (Err(_), _) => Err("the case is refused, so it has no baseline run"),
            (Ok(_), None) => Err(NO_RECORD),
            (Ok(_), Some(record)) => Ok(crate::expect::Baseline::of_record(record)),
        };
        admission.expectation = inputs.expectation(program, baseline, manifest.stop.as_ref());
    }
}

/// The coverage of the cached results of `manifest`'s programs under the admitted `spec`, in the
/// cache directory `cache`, read without running a program.
pub fn corpus_coverage(
    spec: &AdmittedSpec,
    manifest: &FlowManifest,
    inputs: &InputSession<'_>,
    cache: &Path,
) -> CorpusCoverage {
    let execution = execution_digest(manifest, spec);
    let mut coverage = CorpusCoverage {
        cache_off: result_store(manifest.budget.backend_options()).err(),
        no_signal: no_coverage_signal(spec),
        ..CorpusCoverage::default()
    };
    for program in &manifest.programs {
        let record = inputs
            .read(program)
            .ok()
            .and_then(|case| current_record(manifest, execution, program, &case, cache));
        let Some(record) = record else {
            coverage.without_record.push(program.id.clone());
            continue;
        };
        if record["class"] != ResultClass::Comparable.as_str() {
            continue;
        }
        if record["coverage"]["complete"] != true {
            coverage.incomplete.push(program.id.clone());
        }
        for (key, into) in [
            ("sentences", &mut coverage.matched),
            ("applied_sentences", &mut coverage.applied),
            ("fired_sentences", &mut coverage.fired),
        ] {
            for sentence in record["coverage"][key].as_array().into_iter().flatten() {
                if let (Some(module), Some(index)) = (
                    sentence["module"].as_str(),
                    sentence["index"]
                        .as_u64()
                        .and_then(|i| u32::try_from(i).ok()),
                ) {
                    into.insert(SentenceRef::new(module, index));
                }
            }
        }
    }
    coverage
}

/// The coverage of the programs of a command that holds each program's current record
/// (`results::ProgramRow::record`), as [`corpus_coverage`] reads it from the cache: a program
/// without a record is `without_record`, and a comparable one's record gives its coverage. A run
/// document reads `stop-hides-edit` under a condition from it ([`StopHides::of`]).
pub(crate) fn rows_coverage(rows: &[crate::results::ProgramRow]) -> CorpusCoverage {
    let mut coverage = CorpusCoverage::default();
    for row in rows {
        let Some(record) = &row.record else {
            coverage
                .without_record
                .push(row.row["id"].as_str().unwrap_or_default().to_owned());
            continue;
        };
        if record["class"] != ResultClass::Comparable.as_str() {
            continue;
        }
        if record["coverage"]["complete"] != true {
            coverage
                .incomplete
                .push(row.row["id"].as_str().unwrap_or_default().to_owned());
        }
        for (key, into) in [
            ("sentences", &mut coverage.matched),
            ("applied_sentences", &mut coverage.applied),
            ("fired_sentences", &mut coverage.fired),
        ] {
            for sentence in record["coverage"][key].as_array().into_iter().flatten() {
                if let (Some(module), Some(index)) = (
                    sentence["module"].as_str(),
                    sentence["index"]
                        .as_u64()
                        .and_then(|i| u32::try_from(i).ok()),
                ) {
                    into.insert(SentenceRef::new(module, index));
                }
            }
        }
    }
    coverage
}

/// Resolve every mutation of `list` against the specification `loaded` (as `run` does; nothing
/// is compiled or run) and add kink-flow's warnings, with `coverage` deciding `unmatched-rule` and `unapplied-rule`.
pub fn check_mutations(
    manifest: &FlowManifest,
    loaded: &LoadedSource,
    list: &MutationList,
    coverage: Option<&CorpusCoverage>,
) -> MutationCheck {
    MutationCheck {
        rows: list
            .mutations
            .iter()
            .map(|mutation| {
                let resolution = resolve(manifest, loaded, mutation);
                let findings = warnings(manifest, loaded, mutation, &resolution, coverage);
                MutationCheckRow {
                    id: mutation.id.clone(),
                    misunderstanding: mutation.misunderstanding.clone(),
                    resolution,
                    findings,
                    extra: Map::new(),
                }
            })
            .collect(),
    }
}

/// What a stop before a rule hides (`stop-hides-edit`, module documentation): the rules `[stop]`
/// stops before, by exact label, and why no program takes such a rule's step.
pub(crate) struct StopHides {
    before: BTreeSet<String>,
    hiding: Hiding,
}

/// Why no program's run takes the step of a rule a stop stops before.
enum Hiding {
    /// Without a condition: the programs whose count is 1, whose runs end at their first
    /// arrival, before its step.
    CountOne(Vec<String>),
    /// Under a condition: the rules some comparable program's run fired, read from coverage that
    /// decides. A stop rule outside them took no step on any comparable program.
    Unfired(BTreeSet<SentenceRef>),
}

/// The most program ids a `stop-hides-edit` text names.
const HIDING_PROGRAMS_SHOWN: usize = 5;

impl StopHides {
    /// `None` when `manifest` declares no stop or stops before no rule; without a condition, when
    /// it has no program whose count is 1; under a condition (`[stop] when`), when `coverage` is
    /// not given or does not decide (module documentation): no edit is then shown hidden from
    /// every program by the stop.
    pub(crate) fn of(manifest: &FlowManifest, coverage: Option<&CorpusCoverage>) -> Option<Self> {
        let stop = manifest.stop.as_ref()?;
        if stop.before.is_empty() {
            return None;
        }
        let hiding = if stop.when.is_some() {
            let coverage = coverage.filter(|coverage| coverage.decides())?;
            Hiding::Unfired(coverage.fired.clone())
        } else {
            let count_one = manifest
                .programs
                .iter()
                .filter(|program| program.stop_count.unwrap_or(stop.count).get() == 1)
                .map(|program| program.id.clone())
                .collect::<Vec<_>>();
            if count_one.is_empty() {
                return None;
            }
            Hiding::CountOne(count_one)
        };
        Some(Self {
            before: stop.before.iter().cloned().collect(),
            hiding,
        })
    }

    /// `label`, a rule's label as the loaded specification gives it (`MODULE.x` for a `rule [x]:`,
    /// the attribute's text for `[label(x)]`), the label the backend selects a stop by, when the
    /// stop stops before that rule and no program takes its step; `at` is the rule's sentence.
    pub(crate) fn hidden(&self, label: Option<&str>, at: &SentenceRef) -> Option<String> {
        let label = label?;
        let unfired = match &self.hiding {
            Hiding::CountOne(_) => true,
            Hiding::Unfired(fired) => !fired.contains(at),
        };
        (self.before.contains(label) && unfired).then(|| label.to_owned())
    }

    /// The warning's text for the rule `label`.
    pub(crate) fn detail(&self, label: &str) -> String {
        let count_one = match &self.hiding {
            Hiding::CountOne(count_one) => count_one,
            Hiding::Unfired(_) => {
                return format!(
                    "[stop] stops before {label} under a condition, and no comparable program's \
                     run took its step (each arrival at it was a stop event that ended its path, \
                     or the run met none): an edit of only its right-hand side or ensures changes \
                     no end of those programs (an edit of its left-hand side, requires or \
                     attributes moves the arrivals)"
                );
            }
        };
        let shown = count_one
            .iter()
            .take(HIDING_PROGRAMS_SHOWN)
            .map(|id| format!("{id:?}"))
            .collect::<Vec<_>>()
            .join(", ");
        let more = count_one.len().saturating_sub(HIDING_PROGRAMS_SHOWN);
        let more = if more > 0 {
            format!(" and {more} more")
        } else {
            String::new()
        };
        format!(
            "[stop] stops before {label}, and the run of every program whose count is 1 \
             ({shown}{more}) ends before its step: an edit of only its right-hand side or ensures \
             changes no end of those programs (an edit of its left-hand side, requires or \
             attributes moves the stops, and a count above 1 takes its earlier steps)"
        )
    }

    /// The warning's next step for the rule `label`.
    pub(crate) fn next(&self, label: &str) -> String {
        match self.hiding {
            Hiding::CountOne(_) => format!(
                "stop after {label}, or give the programs a count above 1, if the edit changes \
                 only what the step builds"
            ),
            Hiding::Unfired(_) => format!(
                "stop after {label}, or write a program whose run passes an arrival at it where \
                 the condition fails, if the edit changes only what the step builds"
            ),
        }
    }

    /// `row`, a run document's mutation row, with `stop_hides_edit` when it survived and edits a
    /// rule the stop stops before whose step no program takes: the warning `check` gives,
    /// repeated on the survivor.
    pub(crate) fn annotate_survivor(&self, row: &mut Value) {
        if row["status"] != "survived" {
            return;
        }
        let hidden = row["rules"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|rule| {
                let at = SentenceRef::new(
                    rule["module"].as_str()?,
                    u32::try_from(rule["index"].as_u64()?).ok()?,
                );
                self.hidden(rule["label"].as_str(), &at)
            })
            .map(|label| self.detail(&label))
            .collect::<Vec<_>>();
        if !hidden.is_empty() {
            row["stop_hides_edit"] = json!(hidden);
        }
    }
}

fn warnings(
    manifest: &FlowManifest,
    loaded: &LoadedSource,
    mutation: &Mutation,
    resolution: &Result<ResolvedMutation, InvalidMutation>,
    coverage: Option<&CorpusCoverage>,
) -> Vec<Finding> {
    let resolved = resolution.as_ref().ok();
    // The rule of an edit and its label: from the resolution, or, when the mutation is refused,
    // from addressing the edit alone.
    let rule_of = |edit: usize| match resolved {
        Some(resolved) => resolved
            .rules
            .iter()
            .find(|rule| rule.edits.contains(&edit))
            .map(|rule| (rule.at.clone(), rule.label.clone())),
        None => addressed_rule(manifest, loaded, &mutation.edits[edit]),
    };
    let mut findings = Vec::new();
    for (index, edit) in mutation.edits.iter().enumerate() {
        if edit.rule.is_some() {
            continue;
        }
        let rule = rule_of(index);
        let next = Some(match &rule {
            Some((_, Some(label))) => format!("address the rule by its label: rule = {label:?}"),
            Some((_, None)) => {
                "give the rule a label and address it by `rule = <label>`".to_owned()
            }
            None => {
                "address the rule by its label, `rule = <label>` (giving the rule a label if it \
                 has none)"
                    .to_owned()
            }
        });
        let (reason, detail) = match edit.line {
            Some(line) => (
                "line-anchor",
                format!(
                    "edit[{index}] addresses its rule by line {line}: a line moves whenever \
                     anything above it changes, and the edit then fails or lands on whichever \
                     rule holds the line and the text"
                ),
            ),
            None => (
                "text-anchor",
                format!(
                    "edit[{index}] addresses its rule by its find text alone: after an edit of \
                     the specification the text can occur once in another rule, and the edit then \
                     lands there"
                ),
            ),
        };
        findings.push(Finding::warning(
            reason,
            Some(index),
            rule.map(|(at, _)| at),
            detail,
            next,
        ));
    }
    if let (Some(resolved), Some(stop)) = (resolved, manifest.stop.as_ref()) {
        let hides = StopHides::of(manifest, coverage);
        for rule in &resolved.rules {
            // A deleted rule takes its label with it (a K label names one rule): the stop then
            // names no rule of the mutant, so `run` does not admit it, and nothing of the edit
            // is hidden from a program, since no program runs it.
            if let (None, Some(label)) = (&rule.after, rule.label.as_deref())
                && stop.names(label)
            {
                findings.push(Finding::warning(
                    "stop-rule-deleted",
                    rule.edits.first().copied(),
                    Some(rule.at.clone()),
                    format!(
                        "the mutation deletes {label}, which [stop] names: no rule of the mutant \
                         has the label, so the stop states no observation of the mutant and \
                         `run` reports it not-admitted (stop-unresolved) rather than judging it"
                    ),
                    Some(format!(
                        "edit {label} rather than deleting it, or stop at another rule"
                    )),
                ));
                continue;
            }
            let hidden = hides
                .as_ref()
                .and_then(|hides| Some((hides, hides.hidden(rule.label.as_deref(), &rule.at)?)));
            if let Some((hides, label)) = hidden {
                findings.push(Finding::warning(
                    "stop-hides-edit",
                    rule.edits.first().copied(),
                    Some(rule.at.clone()),
                    hides.detail(&label),
                    Some(hides.next(&label)),
                ));
            }
        }
    }
    let (Some(resolved), Some(coverage)) = (resolved, coverage) else {
        return findings;
    };
    for rule in &resolved.rules {
        let name = rule
            .label
            .clone()
            .unwrap_or_else(|| format!("the rule at {}:{}", rule.file, rule.start_line));
        if let Some(reason) = coverage.no_signal.get(&rule.at) {
            findings.push(Finding::warning(
                "no-coverage-signal",
                rule.edits.first().copied(),
                Some(rule.at.clone()),
                format!("{name}: {reason}, so no program can be shown to match it"),
                None,
            ));
            continue;
        }
        if !coverage.decides() {
            continue;
        }
        let others = if resolved.rules.len() > 1 {
            " (a program that matches another edited rule of the mutation may still kill it)"
        } else {
            ""
        };
        if !coverage.matched.contains(&rule.at) {
            findings.push(Finding::warning(
                "unmatched-rule",
                rule.edits.first().copied(),
                Some(rule.at.clone()),
                format!(
                    "no comparable program matches {name} (begins to decide its requires) in the \
                     cached results, so no program of the corpus exercises this rule{others}"
                ),
                Some(format!(
                    "write a program that matches {name}, or edit a rule the corpus uses"
                )),
            ));
        } else if !coverage.applied.contains(&rule.at) {
            findings.push(Finding::warning(
                "unapplied-rule",
                rule.edits.first().copied(),
                Some(rule.at.clone()),
                format!(
                    "every comparable program that matches {name} refutes its requires in the \
                     cached results (none applies it), so no program of the corpus can kill an \
                     edit of only its right-hand side or ensures, except through a claim the edit \
                     withdraws{others}"
                ),
                Some(format!(
                    "write a program that satisfies the requires of {name}, or edit its requires"
                )),
            ));
        }
    }
    findings
}
