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
//! `invalid`.
//!
//! Warnings change no status:
//! - `line-anchor`: an edit addressed by `line`, and `text-anchor`: one addressed by `find` alone.
//!   Neither anchor names the rule, so an edit of the specification can move the mutation onto
//!   another rule that happens to hold the same text at that place; the next step names the
//!   rule's label when it has one (the rule the edit alone is addressed to, also when its
//!   mutation is refused for another reason).
//! - `unreached-rule`: an edited rule whose edit no comparable program witnesses in the cached
//!   results (reached, k-rust `matched`, for an edit of the rule's `requires`; applied otherwise:
//!   the witness rule of `run`'s program order). Given only when every program has a current
//!   result record and every comparable program's coverage is complete; otherwise the document's
//!   `coverage` says why there is no such warning.
//! - `no-coverage-signal`: an edited rule k-rust's coverage cannot record, so no program can be
//!   shown to reach it.
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
    admit::{AdmittedSpec, InputSession},
    digest::spec_digest,
    manifest::FlowManifest,
    mutation::{
        InvalidMutation, Mutation, MutationList, ResolvedMutation, addressed_rule, resolve,
    },
    report::rules_value,
    results::{ResultClass, current_record, no_coverage_signal},
};
use kink_corpus::LoadedSource;
use kink_patch::SentenceRef;
use serde_json::{Value, json};
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
    /// A kebab-case name (`line-anchor`, `unreached-rule`, ...).
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
}

impl MutationCheckRow {
    /// Whether the mutation is refused: it does not resolve, or a finding refuses it.
    pub fn refused(&self) -> bool {
        self.resolution.is_err() || self.findings.iter().any(|finding| finding.refusal)
    }

    /// The row of the check document: `{id, misunderstanding, outcome, digest, rules, refusals,
    /// warnings}`. `outcome` is `ok`, `refused`, or `error` for a resolution the host refused
    /// (`host-stack-refused`, not a fault of the mutation); `rules` is null when the mutation does
    /// not resolve; each refusal and warning is `{reason, edit, rule, detail, next}`.
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
        json!({
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
        })
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
    /// The programs with no current result record (never run under this specification and
    /// build, or refused before a record could be made).
    pub without_record: Vec<String>,
    /// The comparable programs whose recorded coverage is incomplete (their run stopped before
    /// it explored everything, so it may use rules it does not list).
    pub incomplete: Vec<String>,
    /// The rules some comparable program reached (k-rust `matched`).
    pub reached: BTreeSet<SentenceRef>,
    /// The rules some comparable program applied (k-rust `applied`).
    pub applied: BTreeSet<SentenceRef>,
    /// The rules k-rust's coverage cannot record, with the reason.
    pub no_signal: BTreeMap<SentenceRef, &'static str>,
}

impl CorpusCoverage {
    /// Whether the coverage decides that a rule is unreached: every program has a current
    /// record and every comparable program's coverage is complete.
    pub fn decides(&self) -> bool {
        self.without_record.is_empty() && self.incomplete.is_empty()
    }

    /// The check document's `coverage`: `{decides, without_record, incomplete, detail}`.
    pub fn value(&self) -> Value {
        let detail = if self.decides() {
            Value::Null
        } else {
            json!(
                "no unreached-rule warning is given: it needs a current result record of every \
                 program (run `kink-flow results FLOW.toml`) and complete coverage of every \
                 comparable program"
            )
        };
        json!({
            "decides": self.decides(),
            "without_record": self.without_record,
            "incomplete": self.incomplete,
            "detail": detail,
        })
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
    let digest = spec_digest(manifest, &spec.loaded.files);
    let mut coverage = CorpusCoverage {
        no_signal: no_coverage_signal(spec),
        ..CorpusCoverage::default()
    };
    for program in &manifest.programs {
        let record = inputs
            .text(program)
            .ok()
            .and_then(|text| current_record(manifest, digest, program, &text, cache));
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
            ("sentences", &mut coverage.reached),
            ("applied_sentences", &mut coverage.applied),
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
/// is compiled or run) and add kink-flow's warnings, with `coverage` deciding `unreached-rule`.
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
                }
            })
            .collect(),
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
                format!("{name}: {reason}, so no program can be shown to reach it"),
                None,
            ));
            continue;
        }
        if !coverage.decides() {
            continue;
        }
        let (witnesses, predicate) = if rule.requires_edited {
            (&coverage.reached, "reaches (begins to decide its requires)")
        } else {
            (&coverage.applied, "applies")
        };
        if !witnesses.contains(&rule.at) {
            findings.push(Finding::warning(
                "unreached-rule",
                rule.edits.first().copied(),
                Some(rule.at.clone()),
                format!(
                    "no comparable program {predicate} {name} in the cached results, so no \
                     program of the corpus witnesses this rule's edit{}",
                    if resolved.rules.len() > 1 {
                        " (a program that witnesses another edited rule of the mutation may still \
                         kill it)"
                    } else {
                        ""
                    }
                ),
                Some(format!(
                    "write a program that {predicate} {name}, or edit a rule the corpus uses"
                )),
            ));
        }
    }
    findings
}
