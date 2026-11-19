//! Expectations: the end a case document states its case's run ends in (`expect`), checked
//! against the ends of the case's baseline run.
//!
//! A case may also scope an expectation to one definition, `[expect_for.<definition>]`, the name a
//! flow's definition goes by ([`crate::manifest::SpecDecl::expect_scope`]: a K flow's main module,
//! a KRS flow's facet). `expect` is a claim about the case in every flow that reads it, and a
//! scoped one a claim about it in the flows of that definition, so a flow checks `expect` and the
//! expectation scoped to its own definition, both where the case states both: a scoped
//! expectation adds a check and replaces none. An expectation scoped to another definition is not
//! read: it is no claim about this flow's runs.
//!
//! An expectation states what the specification computes for its case, so a baseline that does
//! not meet it is a finding about the specification against the reference the case was written
//! from. It is reported, and the case is kept: every kill by the case is still a difference
//! between a mutant's ends and the baseline's, which is what a kill means whatever the case
//! expects. So no verdict or status depends on an expectation, and no run does: it
//! is in no digest, no cache key and no stored record, and it is checked again by every command
//! that reports it, from the baseline's ends (a live run's, or the stored record's). Only the
//! exit status of `coverage`, which asks whether each baseline meets its expectation, joins it
//! (`crate::cli::coverage_status`): an unmet expectation is a finding, an inconclusive one no
//! answer.
//!
//! kink reads no expectation itself: an expectation is a document of a front end's encoding of
//! ends, which only the front end that reads the definition's ends at its own level can read, the
//! [`EndRenderer`] of the manifest (`EndRenderer::read_expectation`,
//! `EndRenderer::check_expectation`). A program with `expect` is refused at admission without
//! one (stage `inputs`, reason `typed-expectation`), as a program with typed inputs is without a
//! decoder, and one whose expectation the renderer refuses is refused (`inputs`,
//! `expectation-value`), as a case `krs run --case` refuses before it runs.
//!
//! A program with an expectation its flow checks has an `expectation` member in its row of the
//! coverage, run and query documents and in its row of the check document: `{verdict, detail,
//! difference}`, `verdict`
//! `met`, `unmet` or `inconclusive`, `difference` the front end's document of the first
//! difference where it is `unmet` (null otherwise), and `detail` why it is inconclusive, or how
//! the check compared what kink does not observe in full (null when there is nothing to say). Only a `comparable` baseline
//! has ends kink compares: every other case's expectation is inconclusive, saying why. The check
//! document runs nothing, so it checks an expectation against the program's current result
//! record, and is inconclusive for a program without one. A program with two expectations (`expect`
//! and its flow's `expect_for`) has one member for both ([`combined`]): `unmet` where either is
//! unmet, else `inconclusive` where either is, else `met`, its `detail` naming the expectation
//! that decides it, since both are claims the baseline must meet.

use crate::admit::InputFiles;
use crate::evidence::{DeclaredEnd, EndRenderer, Renderer};
use crate::manifest::{CaseRoot, Program, StopSection};
use crate::results::{ProgramResult, ResultClass, record_final_configuration};
use k_rust::kore::{ast::Pattern, parser::parse_pattern};
use kink_corpus::admission::AdmissionRefusal;
use serde_json::{Value, json};
use std::collections::BTreeSet;
use toml::Table;

/// What a front end's renderer is given to check an expectation against a baseline's ends
/// ([`EndRenderer::check_expectation`]).
pub struct ExpectationCheck<'a> {
    /// The case's `expect` table, as written.
    pub expect: &'a Table,
    /// Reads the files the expectation names, relative to the file the case is written in.
    pub files: &'a mut dyn InputFiles,
    /// The baseline run's ends, every end of its explored system (the run is complete): final
    /// configurations of the K definition kink judges as the second slot compares them, each
    /// cell of `not_compared` replaced by `\top` of its sort.
    pub ends: &'a BTreeSet<Pattern>,
    /// The cells the second slot leaves out, by K cell name (`ResultProjection::not_compared`),
    /// whose content the ends do not state.
    pub not_compared: &'a [String],
    /// The corpus's `[stop]`, its rules by exact K label, when it has one: each end is then an
    /// end of the system truncated at the stop, reached at a stop or where the run ended on its
    /// own, which the ends do not say.
    pub stop: Option<&'a StopSection>,
}

/// Whether a baseline meets its case's expectation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExpectationVerdict {
    /// Every end of the baseline agrees with the expectation.
    Met,
    /// An end does not, which the difference shows.
    Unmet,
    /// Nothing can be concluded: no end to compare, or what the expectation states is not what
    /// kink observes of the case.
    Inconclusive,
}

impl ExpectationVerdict {
    /// The verdict's name in documents.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Met => "met",
            Self::Unmet => "unmet",
            Self::Inconclusive => "inconclusive",
        }
    }
}

/// An expectation's check: its verdict, the first difference where it is unmet, and a detail.
#[derive(Clone, Debug, PartialEq)]
pub struct CheckedExpectation {
    pub verdict: ExpectationVerdict,
    /// Why the verdict is inconclusive, or how a met or unmet verdict compared what kink does not
    /// observe in full.
    pub detail: Option<String>,
    /// The front end's document of the first difference, for an unmet verdict.
    pub difference: Option<Value>,
}

impl CheckedExpectation {
    /// An inconclusive verdict, for `detail`.
    pub fn inconclusive(detail: impl Into<String>) -> Self {
        Self {
            verdict: ExpectationVerdict::Inconclusive,
            detail: Some(detail.into()),
            difference: None,
        }
    }

    /// The row's `expectation` member: `{verdict, detail, difference}`.
    #[must_use]
    pub fn value(&self) -> Value {
        json!({
            "verdict": self.verdict.as_str(),
            "detail": self.detail,
            "difference": self.difference,
        })
    }
}

/// What an expectation is checked against: a program's baseline result, from a live run or a
/// stored record.
#[derive(Clone, Debug)]
pub struct Baseline<'a> {
    /// The result class (a document's program `class`).
    pub class: &'a str,
    /// Its cause, when it has one.
    pub cause: Option<&'a str>,
    /// The run's ends as KORE text, as the result holds them; `None` when it holds none.
    pub ends: Option<Vec<&'a str>>,
}

impl<'a> Baseline<'a> {
    /// The baseline a result record states.
    #[must_use]
    pub fn of_record(record: &'a Value) -> Self {
        Self {
            class: record["class"].as_str().unwrap_or("error"),
            cause: record["cause"].as_str(),
            ends: record_final_configuration(record),
        }
    }

    /// The baseline a live run gave.
    #[must_use]
    pub fn of_result(result: &'a ProgramResult) -> Self {
        Self {
            class: result.class.as_str(),
            cause: result.cause.as_deref(),
            ends: result.final_terms(),
        }
    }
}

/// The expectations `program`'s flow checks (module documentation), each with the key a case
/// document writes it at: the case's `expect`, then the expectation its `expect_for` scopes to the
/// flow's definition (`expect_for.<definition>`).
pub(crate) fn expectations(program: &Program) -> Vec<(String, &Table)> {
    program
        .expect
        .iter()
        .map(|expect| ("expect".to_owned(), expect))
        .chain(
            program
                .expect_for
                .scoped
                .iter()
                .map(|(definition, expect)| (format!("expect_for.{definition}"), expect)),
        )
        .collect()
}

/// The admission of the expectations `program`'s flow checks ([`expectations`]), when it has one:
/// refused without a renderer (`typed-expectation`), or where the renderer refuses one
/// (`expectation-value`, naming it). `root` is the canonical case root.
pub(crate) fn admit_expectation(
    renderer: &Renderer,
    root: &CaseRoot,
    program: &Program,
) -> Result<(), AdmissionRefusal> {
    let expectations = expectations(program);
    if expectations.is_empty() {
        return Ok(());
    }
    let Some(renderer) = renderer.get() else {
        return Err(AdmissionRefusal {
            stage: "inputs".into(),
            reason: "typed-expectation".into(),
            detail: "an expectation is read by the front end that reads the definition's ends at \
                     its own level (the krs front end, `krs kink`); kink reads no expectation"
                .into(),
        });
    };
    for (key, expect) in expectations {
        renderer
            .read_expectation(expect, &mut root.case_files(program))
            .map_err(|message| AdmissionRefusal {
                stage: "inputs".into(),
                reason: "expectation-value".into(),
                detail: format!("{key}: {message}"),
            })?;
    }
    Ok(())
}

/// The `expectation` member of `program`'s row (module documentation), when its flow checks an
/// expectation of it ([`expectations`]): each checked against `baseline`, the program's baseline
/// result, or why it has none, and the checks [`combined`]. `root` is the
/// canonical case root, or why it is unavailable, `not_compared` the cells the second slot
/// leaves out and `stop` the manifest's `[stop]`.
pub(crate) fn expectation_value(
    renderer: &Renderer,
    root: Result<&CaseRoot, &str>,
    program: &Program,
    baseline: Result<Baseline<'_>, &str>,
    not_compared: &[String],
    stop: Option<&StopSection>,
) -> Option<Value> {
    let expectations = expectations(program);
    if expectations.is_empty() {
        return None;
    }
    let checked = expectations
        .into_iter()
        .map(|(key, expect)| {
            let checked = match &baseline {
                Err(reason) => CheckedExpectation::inconclusive(*reason),
                Ok(baseline) => check(
                    renderer,
                    root,
                    program,
                    expect,
                    baseline,
                    not_compared,
                    stop,
                )
                .unwrap_or_else(CheckedExpectation::inconclusive),
            };
            (key, checked)
        })
        .collect();
    Some(combined(checked).value())
}

/// The one check of the expectations a flow checks of a case, each named by its key: one
/// expectation's check as it is; of two, the first unmet one, else the first inconclusive one,
/// else `met`, since the baseline meets the case's expectations only where it meets each. The
/// detail of two names the expectation it is of: the deciding one's, or every met one's that
/// has one.
fn combined(mut checked: Vec<(String, CheckedExpectation)>) -> CheckedExpectation {
    if checked.len() == 1 {
        return checked.remove(0).1;
    }
    let named = |key: &str, detail: Option<&str>, verdict: &str| match detail {
        Some(detail) => format!("`{key}`: {detail}"),
        None => format!("`{key}` is {verdict}"),
    };
    for verdict in [ExpectationVerdict::Unmet, ExpectationVerdict::Inconclusive] {
        if let Some((key, deciding)) = checked.iter().find(|(_, c)| c.verdict == verdict) {
            return CheckedExpectation {
                verdict,
                detail: Some(named(key, deciding.detail.as_deref(), verdict.as_str())),
                difference: deciding.difference.clone(),
            };
        }
    }
    let details = checked
        .iter()
        .filter_map(|(key, c)| Some(named(key, Some(c.detail.as_deref()?), "met")))
        .collect::<Vec<_>>();
    CheckedExpectation {
        verdict: ExpectationVerdict::Met,
        detail: (!details.is_empty()).then(|| details.join("; ")),
        difference: None,
    }
}

/// The finding a program row states of its ends' declared classes (`declared_end`): an end in no
/// declared class that the case does not expect.
pub const UNDECLARED_END: &str = "undeclared-end";
/// The finding of an end whose declared class is not decided.
pub const END_UNDECIDED: &str = "end-undecided";
/// The finding of an end at which ends of both declared classes hold.
pub const END_CLASSES_OVERLAP: &str = "end-classes-overlap";

/// `row`, a program row whose `ends` are the summaries of `baseline`'s ends, with each end at
/// which no rule applies given its declared class (`crate::evidence`, "Declared ends"), and with
/// `declared_end`, `{finding, detail}`, where those classes are a finding: an end of class
/// `none` that the case does not expect (no expectation the flow checks states `class = "none"`)
/// is [`UNDECLARED_END`], since the definition has no rule there and does not call the state an
/// end; one of both classes is [`END_CLASSES_OVERLAP`]; one whose class is not decided is
/// [`END_UNDECIDED`]. Where several ends are findings the row names the first of the most severe
/// (overlap, then a gap, then an undecided class), by exit status. A row of a definition that declares no end, and one with no
/// ends, is left as it is. `stop` is whether the corpus has a `[stop]`: an end then has a class
/// only where its `halt` is `own`.
pub(crate) fn with_declared(
    renderer: &Renderer,
    program: &Program,
    row: &mut Value,
    baseline: &Baseline<'_>,
    not_compared: &[String],
    stop: bool,
) {
    let Some(renderer) = renderer.get() else {
        return;
    };
    if baseline.class != ResultClass::Comparable.as_str() {
        return;
    }
    let (Some(texts), Some(summaries)) = (baseline.ends.as_ref(), row["ends"].as_array()) else {
        return;
    };
    if texts.len() != summaries.len() {
        return;
    }
    let mut asked = Vec::new();
    let mut ends = Vec::new();
    for (index, (text, summary)) in texts.iter().zip(summaries).enumerate() {
        if stop && summary["halt"] != "own" {
            continue;
        }
        let Ok(end) = parse_pattern(text) else {
            return;
        };
        asked.push(index);
        ends.push(end);
    }
    if ends.is_empty() {
        return;
    }
    let Some(declared) = renderer.declared_ends(&ends, not_compared) else {
        return;
    };
    // Either expectation the flow checks may state that the gap is meant.
    let gap_expected = expectations(program)
        .into_iter()
        .any(|(_, expect)| renderer.expected_class(expect).is_some_and(|c| c == "none"));
    let mut finding: Option<(u8, &'static str, String)> = None;
    for (index, class) in asked.into_iter().zip(&declared) {
        class.annotate(&mut row["ends"][index]);
        let found = match class {
            DeclaredEnd::Overlap { finished, refused } => Some((
                0,
                END_CLASSES_OVERLAP,
                format!(
                    "end {index}: the declared ends `{finished}` (finished) and `{refused}` \
                     (refused) both hold; an end is of one class, so the definition contradicts \
                     itself: state the two ends so that no state is in both"
                ),
            )),
            DeclaredEnd::None if !gap_expected => Some((
                1,
                UNDECLARED_END,
                format!(
                    "end {index}: no rule applies and no declared end holds, so the definition \
                     does not account for this end: declare it (`#[k::end(..)]`), add the rule \
                     that is missing, or state `class = \"none\"` in the case's `expect` where \
                     the gap is meant"
                ),
            )),
            DeclaredEnd::Undecided(detail) => Some((
                2,
                END_UNDECIDED,
                format!("end {index}: whether a declared end holds is not decided: {detail}"),
            )),
            _ => None,
        };
        if let Some(found) = found
            && finding.as_ref().is_none_or(|(rank, ..)| found.0 < *rank)
        {
            finding = Some(found);
        }
    }
    if let Some((_, name, detail)) = finding {
        row["declared_end"] = json!({"finding": name, "detail": detail});
    }
}

/// [`expectation_value`]'s check of `expect` against `baseline`, or why there is none.
fn check(
    renderer: &Renderer,
    root: Result<&CaseRoot, &str>,
    program: &Program,
    expect: &Table,
    baseline: &Baseline<'_>,
    not_compared: &[String],
    stop: Option<&StopSection>,
) -> Result<CheckedExpectation, String> {
    let class = baseline.class;
    if class == ResultClass::ComparablePrefix.as_str() {
        return Err(
            "the baseline run is `comparable-prefix`: its bounds cut it before it ended, so it \
             has no end to check an end expectation against; it is compared by its observation \
             channels only"
                .to_owned(),
        );
    }
    if class != ResultClass::Comparable.as_str() {
        let cause = baseline
            .cause
            .map_or_else(String::new, |cause| format!(" ({cause})"));
        return Err(format!(
            "the baseline run is `{class}`{cause}: only a comparable baseline has ends kink \
             compares"
        ));
    }
    let ends = baseline
        .ends
        .as_ref()
        .ok_or("the baseline's result holds no ends")?
        .iter()
        .map(|text| {
            parse_pattern(text).map_err(|e| format!("an end of the baseline does not parse: {e}"))
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    let renderer: &dyn EndRenderer = renderer
        .get()
        .ok_or("no front end reads expectations, so admission refuses the case")?;
    let root = root?;
    renderer
        .check_expectation(ExpectationCheck {
            expect,
            files: &mut root.case_files(program),
            ends: &ends,
            not_compared,
            stop,
        })
        .map_err(|e| format!("the expectation cannot be checked: {e}"))
}

#[cfg(test)]
mod tests {
    use super::{CheckedExpectation, ExpectationVerdict, combined};
    use serde_json::json;

    fn checked(verdict: ExpectationVerdict, detail: Option<&str>) -> CheckedExpectation {
        CheckedExpectation {
            verdict,
            detail: detail.map(str::to_owned),
            difference: (verdict == ExpectationVerdict::Unmet).then(|| json!({"at": detail})),
        }
    }

    /// One expectation's check is the row's as it is; of two, an unmet one decides, then an
    /// inconclusive one, and both must be met for `met`; the detail names the expectation.
    #[test]
    fn two_expectations_are_met_only_where_each_is() {
        use ExpectationVerdict::{Inconclusive, Met, Unmet};
        let one = checked(Inconclusive, Some("no end"));
        assert_eq!(combined(vec![("expect".into(), one.clone())]), one);
        let unscoped = "expect".to_owned();
        let scoped = "expect_for.X".to_owned();
        let unmet = combined(vec![
            (unscoped.clone(), checked(Inconclusive, Some("no end"))),
            (scoped.clone(), checked(Unmet, None)),
        ]);
        assert_eq!(unmet.verdict, Unmet);
        assert_eq!(unmet.detail.as_deref(), Some("`expect_for.X` is unmet"));
        assert_eq!(unmet.difference, Some(json!({"at": null})));
        let inconclusive = combined(vec![
            (unscoped.clone(), checked(Met, None)),
            (scoped.clone(), checked(Inconclusive, Some("no end"))),
        ]);
        assert_eq!(
            inconclusive,
            CheckedExpectation {
                verdict: Inconclusive,
                detail: Some("`expect_for.X`: no end".to_owned()),
                difference: None,
            }
        );
        let met = combined(vec![
            (unscoped.clone(), checked(Met, Some("cells only"))),
            (scoped.clone(), checked(Met, None)),
        ]);
        assert_eq!(met.verdict, Met);
        assert_eq!(met.detail.as_deref(), Some("`expect`: cells only"));
        let bare = combined(vec![
            (unscoped, checked(Met, None)),
            (scoped, checked(Met, None)),
        ]);
        assert_eq!(bare.detail, None);
    }
}
