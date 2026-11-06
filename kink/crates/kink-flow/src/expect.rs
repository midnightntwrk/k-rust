//! Expectations: the end a case document states its case's run ends in (`expect`), checked
//! against the ends of the case's baseline run.
//!
//! An expectation states what the specification computes for its case, so a baseline that does
//! not meet it is a finding about the specification against the reference the case was written
//! from. It is reported, and the case is kept: every kill by the case is still a difference
//! between a mutant's ends and the baseline's, which is what a kill means whatever the case
//! expects. So no verdict or status depends on an expectation, and no run does: it
//! is in no digest, no cache key and no stored record, and it is checked again by every command
//! that reports it, from the baseline's ends (a live run's, or the stored record's). Only the
//! exit status of `results`, which asks whether each baseline meets its expectation, joins it
//! (`crate::cli::results_status`): an unmet expectation is a finding, an inconclusive one no
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
//! A program with `expect` has an `expectation` member in its row of the results, run and query
//! documents and in its row of the check document: `{verdict, detail, difference}`, `verdict`
//! `met`, `unmet` or `inconclusive`, `difference` the front end's document of the first
//! difference where it is `unmet` (null otherwise), and `detail` why it is inconclusive, or how
//! the check compared what kink does not observe in full (null when there is nothing to say). Only a `comparable` baseline
//! has ends kink compares: every other case's expectation is inconclusive, saying why. The check
//! document runs nothing, so it checks an expectation against the program's current result
//! record, and is inconclusive for a program without one.

use crate::admit::{InputFiles, ManifestFiles};
use crate::evidence::{EndRenderer, Renderer};
use crate::manifest::{Program, StopSection};
use crate::results::{ProgramResult, ResultClass, record_final_configuration};
use k_rust::kore::{ast::Pattern, parser::parse_pattern};
use kink_corpus::admission::AdmissionRefusal;
use serde_json::{Value, json};
use std::{collections::BTreeSet, path::Path};
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
    /// The result class (`results`' `class`).
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

/// The admission of `program`'s expectation, when it has one: refused without a renderer
/// (`typed-expectation`), or where the renderer refuses it (`expectation-value`). `root` is the
/// canonical manifest directory.
pub(crate) fn admit_expectation(
    renderer: &Renderer,
    root: &Path,
    program: &Program,
) -> Result<(), AdmissionRefusal> {
    let Some(expect) = &program.expect else {
        return Ok(());
    };
    let Some(renderer) = renderer.get() else {
        return Err(AdmissionRefusal {
            stage: "inputs".into(),
            reason: "typed-expectation".into(),
            detail: "an expectation is read by the front end that reads the definition's ends at \
                     its own level (the krs front end, `krs kink`); kink reads no expectation"
                .into(),
        });
    };
    renderer
        .read_expectation(expect, &mut case_files(root, program))
        .map_err(|message| AdmissionRefusal {
            stage: "inputs".into(),
            reason: "expectation-value".into(),
            detail: format!("expect: {message}"),
        })
}

/// The `expectation` member of `program`'s row (module documentation), when it has `expect`:
/// checked against `baseline`, the program's baseline result, or why it has none. `root` is the
/// canonical manifest directory, `not_compared` the cells the second slot leaves out and `stop`
/// the manifest's `[stop]`.
pub(crate) fn expectation_value(
    renderer: &Renderer,
    root: Option<&Path>,
    program: &Program,
    baseline: Result<Baseline<'_>, &str>,
    not_compared: &[String],
    stop: Option<&StopSection>,
) -> Option<Value> {
    let expect = program.expect.as_ref()?;
    let checked = match baseline {
        Err(reason) => CheckedExpectation::inconclusive(reason),
        Ok(baseline) => check(
            renderer,
            root,
            program,
            expect,
            &baseline,
            not_compared,
            stop,
        )
        .unwrap_or_else(CheckedExpectation::inconclusive),
    };
    Some(checked.value())
}

/// [`expectation_value`]'s check of `expect` against `baseline`, or why there is none.
fn check(
    renderer: &Renderer,
    root: Option<&Path>,
    program: &Program,
    expect: &Table,
    baseline: &Baseline<'_>,
    not_compared: &[String],
    stop: Option<&StopSection>,
) -> Result<CheckedExpectation, String> {
    let class = baseline.class;
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
    let root = root.ok_or("the manifest's directory is unavailable")?;
    renderer
        .check_expectation(ExpectationCheck {
            expect,
            files: &mut case_files(root, program),
            ends: &ends,
            not_compared,
            stop,
        })
        .map_err(|e| format!("the expectation cannot be checked: {e}"))
}

/// The reader of the files `program`'s case names: relative to the file it is written in.
fn case_files<'a>(root: &'a Path, program: &'a Program) -> ManifestFiles<'a> {
    ManifestFiles {
        root,
        document: program.case_file.as_deref().or(program.case.as_deref()),
    }
}
