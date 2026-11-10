//! Chain patterns written in KRS (`k::patterns!`, FB-49).
//!
//! A pattern is a chain of steps over a run: states s1 ≤ s2 ≤ … ≤ sn on one path, each matching
//! its step under one assignment of the variables the steps share, and, where a step has an
//! `unless`, no state strictly between the previous step's state and its own matching it. Each
//! step and each `unless` is a claim subject with no result: a set of states, which the claim's
//! left side denotes. So every part travels as the readable claim it is, carrying a
//! [`PatternDecl`] that says which pattern and which part it is. A claim that carries one is never
//! a sentence of `definition.k` or `spec.k`: it is read only by `emit_patterns`, which writes each
//! part's text for kink.

use serde::{Deserialize, Serialize};

/// The answer a pattern states it expects of the corpus (`#[k::expect(no)]`).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PatternExpect {
    /// No program's run reaches a chain of states that matches the pattern.
    No,
}

impl PatternExpect {
    /// The value as kink writes it.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::No => "no",
        }
    }
}

/// The part of a pattern one claim stands for: a step, or the `unless` of the arrow into a step.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PatternDecl {
    /// The pattern's id: the clause name with `_` written `-`, unique per package.
    pub id: String,
    /// The clause name as written, without `r#`.
    pub name: String,
    /// The step this part belongs to, from 1.
    pub step: u32,
    /// Whether the part is the `unless` of the arrow into [`Self::step`], rather than the step.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub unless: bool,
    /// The binders the part names, in order: those its record binds, then those its conditions
    /// read that an earlier step binds. A binder two parts name is one variable of the pattern,
    /// which each of those parts must write as a variable.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub binders: Vec<String>,
    /// The clause's documentation, which kink shows as the pattern's note.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
    /// The corpus programs the author claims hit the pattern (`#[k::cases(..)]`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub programs: Option<Vec<String>>,
    /// The answer the author claims the corpus gives (`#[k::expect(..)]`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expect: Option<PatternExpect>,
}

/// Why a [`PatternDecl`] is no part of a pattern.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PatternDeclError {
    /// The id or the name is empty.
    EmptyName,
    /// The step is 0.
    StepZero,
    /// Step 1 has an `unless`: no arrow leads into it.
    UnlessOnFirstStep,
    /// `programs` is empty or holds an empty or repeated id.
    Programs,
    /// `programs` and `expect` are both present, which contradict each other.
    ProgramsAndExpect,
}

impl std::fmt::Display for PatternDeclError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::EmptyName => "a pattern part names its pattern",
            Self::StepZero => "a pattern's steps count from 1",
            Self::UnlessOnFirstStep => "step 1 of a pattern has no arrow into it, so no `unless`",
            Self::Programs => {
                "a pattern's programs are at least one distinct, non-empty program id"
            }
            Self::ProgramsAndExpect => {
                "a pattern's programs claim hits, which contradicts `expect = \"no\"`"
            }
        })
    }
}

impl std::error::Error for PatternDeclError {}

impl PatternDecl {
    /// Checks the part's own shape: a named pattern, a step from 1, no `unless` into step 1,
    /// and programs and an expectation that state one claim.
    ///
    /// # Errors
    ///
    /// Returns the first [`PatternDeclError`] the part shows.
    pub fn validate(&self) -> Result<(), PatternDeclError> {
        if self.id.is_empty() || self.name.is_empty() {
            return Err(PatternDeclError::EmptyName);
        }
        if self.step == 0 {
            return Err(PatternDeclError::StepZero);
        }
        if self.step == 1 && self.unless {
            return Err(PatternDeclError::UnlessOnFirstStep);
        }
        if let Some(programs) = &self.programs {
            let mut seen = std::collections::BTreeSet::new();
            if programs.is_empty()
                || programs
                    .iter()
                    .any(|program| program.is_empty() || !seen.insert(program))
            {
                return Err(PatternDeclError::Programs);
            }
            if self.expect.is_some() {
                return Err(PatternDeclError::ProgramsAndExpect);
            }
        }
        Ok(())
    }
}
