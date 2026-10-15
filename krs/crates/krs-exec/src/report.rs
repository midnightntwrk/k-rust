//! The `krs-exec/1` report shapes shared by `--output json` and the browser JSON ABI.

use k_rust::{
    backend::HaltReasonOutput,
    kast::{Term as KastTerm, json as kast_json, printer::Printer},
    kore::ast::Pattern,
};
use serde::{Serialize, Serializer};

/// The schema name every serialized report envelope carries.
pub const REPORT_SCHEMA: &str = "krs-exec/1";

/// One configuration or term, kept as KORE and as user-facing KAST.
///
/// It serializes as the KAST JSON envelope that `krun --output json` prints,
/// so a gate normalizes the native and Java results with one policy.
#[derive(Clone, Debug)]
pub struct Term {
    kore: Pattern,
    kast: KastTerm,
}

impl Term {
    pub(crate) const fn new(kore: Pattern, kast: KastTerm) -> Self {
        Self { kore, kast }
    }

    /// The KORE pattern, as the backend returned it; a run or search result has its Floats in the
    /// form `krun` prints them.
    #[must_use]
    pub const fn kore(&self) -> &Pattern {
        &self.kore
    }

    /// The KAST term converted from the KORE pattern.
    #[must_use]
    pub const fn kast(&self) -> &KastTerm {
        &self.kast
    }

    /// The first item of the `<k>` cell as textual KAST: `Some(None)` when `<k>` is empty, `None` without a `<k>` cell.
    #[must_use]
    pub fn k_head(&self) -> Option<Option<String>> {
        let mut stack = vec![&self.kast];
        while let Some(term) = stack.pop() {
            match term {
                KastTerm::Apply { label, arguments } if label.name == "<k>" => {
                    let [content] = arguments.as_slice() else {
                        return None;
                    };
                    return Some(match content {
                        KastTerm::Sequence(items) => {
                            items.first().map(|item| Printer::new().print_term(item))
                        }
                        item => Some(Printer::new().print_term(item)),
                    });
                }
                KastTerm::Apply { arguments, .. } => stack.extend(arguments.iter().rev()),
                KastTerm::Annotated { term, .. } => stack.push(term),
                _ => {}
            }
        }
        None
    }

    /// The KAST JSON envelope text.
    ///
    /// # Errors
    ///
    /// Returns an error when the term cannot be encoded.
    pub fn kast_json(&self) -> Result<String, kast_json::Error> {
        kast_json::to_string(&self.kast)
    }
}

impl Serialize for Term {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let text = self.kast_json().map_err(serde::ser::Error::custom)?;
        let mut decoder = serde_json::Deserializer::from_str(&text);
        decoder.disable_recursion_limit();
        let value = <serde_json::Value as serde::Deserialize>::deserialize(&mut decoder)
            .map_err(serde::ser::Error::custom)?;
        value.serialize(serializer)
    }
}

/// How a run or one search path ended.
///
/// `stuck`, `depth-bound` and `undefined` are completed results: K has no
/// distinguished finished state, so a program is finished when `<k>` holds only `.K`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Halt {
    /// No rule applies.
    Stuck,
    /// The `--depth` bound was reached.
    DepthBound,
    /// The state is `#Bottom`: a partial function was applied outside its domain.
    Undefined,
    /// Rule applicability could not be decided (no SMT solver, or an undecided condition).
    Indeterminate,
    /// A hooked function has no implementation in the native backend.
    UnsupportedHook,
    /// Simplification failed.
    SimplificationError,
    /// A step exceeded its time budget.
    Timeout,
    /// The backend stopped for a reason a run does not request (branch, cut point, cancellation).
    Interrupted,
}

impl Halt {
    pub(crate) const fn from_backend(reason: HaltReasonOutput) -> Self {
        match reason {
            HaltReasonOutput::Stuck => Self::Stuck,
            HaltReasonOutput::DepthBound => Self::DepthBound,
            HaltReasonOutput::Trivial | HaltReasonOutput::Vacuous => Self::Undefined,
            HaltReasonOutput::Indeterminate => Self::Indeterminate,
            HaltReasonOutput::UnsupportedHook => Self::UnsupportedHook,
            HaltReasonOutput::SimplificationError => Self::SimplificationError,
            HaltReasonOutput::Timeout => Self::Timeout,
            HaltReasonOutput::Cancelled
            | HaltReasonOutput::Branch
            | HaltReasonOutput::CutPoint
            | HaltReasonOutput::Terminal
            | HaltReasonOutput::BreadthBound
            | HaltReasonOutput::WorkBound => Self::Interrupted,
        }
    }

    /// The printed status word.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Stuck => "stuck",
            Self::DepthBound => "depth-bound",
            Self::Undefined => "undefined",
            Self::Indeterminate => "indeterminate",
            Self::UnsupportedHook => "unsupported-hook",
            Self::SimplificationError => "simplification-error",
            Self::Timeout => "timeout",
            Self::Interrupted => "interrupted",
        }
    }

    /// Whether the result is complete (exit status 0) rather than inconclusive (exit status 1).
    #[must_use]
    pub const fn is_complete(self) -> bool {
        matches!(self, Self::Stuck | Self::DepthBound | Self::Undefined)
    }
}

/// Where a rewrite step's rule came from.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum StepOrigin {
    /// An authored KRS sentence.
    Authored {
        /// Package-relative source path.
        file: String,
        /// One-based line, when the source text was supplied.
        #[serde(skip_serializing_if = "Option::is_none")]
        line: Option<u32>,
        /// One-based Unicode-scalar column, when the source text was supplied.
        #[serde(skip_serializing_if = "Option::is_none")]
        column: Option<u32>,
    },
    /// A rule generated by a compiler pass, with the authored sentence it came from when known.
    Generated {
        /// The generating pass (for example `strict`).
        pass: String,
        /// The authored sentence the pass started from.
        #[serde(skip_serializing_if = "Option::is_none")]
        from: Option<SourceSpan>,
    },
    /// A rule of K's builtin closure.
    Builtin {
        /// The K module that declares it.
        module: String,
    },
}

/// An authored location.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct SourceSpan {
    /// Package-relative source path.
    pub file: String,
    /// One-based line, when the source text was supplied.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<u32>,
    /// One-based Unicode-scalar column, when the source text was supplied.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub column: Option<u32>,
}

impl std::fmt::Display for SourceSpan {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.file)?;
        if let (Some(line), Some(column)) = (self.line, self.column) {
            write!(formatter, ":{line}:{column}")?;
        }
        Ok(())
    }
}

/// One rewrite step of a trace. Equation evaluation is not a step.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Step {
    /// One-based step number.
    pub index: u64,
    /// K's rule label (for example `KRS-TOUR-MINIMAL.foo-to-bar`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
    /// The backend's `UNIQUE_ID` of the rule.
    pub rule_id: String,
    /// Where the rule came from.
    pub origin: StepOrigin,
}

/// The result of `run`: one path, as krun follows it.
#[derive(Clone, Debug, Serialize)]
pub struct RunReport {
    /// How the run ended.
    pub halt: Halt,
    /// Rewrite steps taken.
    pub steps: u64,
    /// The final configuration, with each binary32 and binary64 Float as `krun` prints it.
    pub state: Term,
    /// Rewrite steps, when a trace was requested.
    pub trace: Vec<Step>,
    /// The bytes the `stream = "stdout"` cell holds when the run ends; `None` without one.
    pub stdout: Option<Vec<u8>>,
    /// The exit cell's final value after a complete run; `None` without an exit cell.
    pub exit_code: Option<i64>,
    /// The lines `io::log` (K's `IO.logString`) wrote on this path, in order; krun prints each
    /// to standard error.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub log: Vec<String>,
}

/// One final state of a search.
#[derive(Clone, Debug, Serialize)]
pub struct Solution {
    /// The state, with each binary32 and binary64 Float as `krun` prints it.
    pub state: Term,
    /// Rewrite steps from the initial state.
    pub depth: u64,
    /// Rewrite steps, when a trace was requested.
    pub trace: Vec<Step>,
}

/// The result of `search`: the set of reachable states that match the mode.
#[derive(Clone, Debug, Serialize)]
pub struct SearchReport {
    /// Whether every path was explored within the bounds and no solution was dropped.
    pub complete: bool,
    /// The solutions, in backend order.
    pub solutions: Vec<Solution>,
    /// The lines `io::log` (K's `IO.logString`) wrote while the search explored, in order;
    /// `krun --search` prints each to standard error.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub log: Vec<String>,
}

/// K's reachability modality.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Modality {
    /// `all-path`.
    AllPath,
    /// `one-path`.
    OnePath,
}

/// The verdict of one claim, in k-rust's words.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Verdict {
    /// Every path reaches the right-hand side.
    Proven,
    /// A path reaches a state that refutes the claim.
    Disproved,
    /// The proof failed without a counterexample.
    Failed,
    /// The backend could not decide (no SMT solver, or an undecided condition).
    Indeterminate,
    /// The `--depth` bound stopped the proof.
    DepthBound,
    /// The breadth bound stopped the proof.
    BreadthBound,
    /// The claim is `trusted` (KF-042): assumed without proof, never proven.
    Trusted,
}

impl Verdict {
    pub(crate) fn from_backend(status: &str) -> Option<Self> {
        Some(match status {
            "proven" => Self::Proven,
            "disproved" => Self::Disproved,
            "failed" => Self::Failed,
            "indeterminate" => Self::Indeterminate,
            "depth-bound" => Self::DepthBound,
            "breadth-bound" => Self::BreadthBound,
            _ => return None,
        })
    }

    /// The printed verdict word.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Proven => "proven",
            Self::Disproved => "disproved",
            Self::Failed => "failed",
            Self::Indeterminate => "indeterminate",
            Self::DepthBound => "depth-bound",
            Self::BreadthBound => "breadth-bound",
            Self::Trusted => "trusted",
        }
    }
}

/// One residual leaf of a proof.
#[derive(Clone, Debug, Serialize)]
pub struct ProofLeaf {
    /// The leaf state, with its constraint.
    pub state: Term,
    /// Rewrite steps from the claim's left-hand side.
    pub depth: u64,
    /// The backend's leaf outcome, as the k-rust host wire names it (`stuck`, `indeterminate`, ...).
    pub outcome: String,
    /// Why a `timeout`, `stack-exhausted` or `indeterminate` leaf ended there, in the backend's
    /// words; absent for every other outcome.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
}

/// The result of proving one claim.
#[derive(Clone, Debug, Serialize)]
pub struct ProofReport {
    /// The claim label, as `kprove --claims` spells it (`<MAIN>-SPEC.label`).
    pub claim: String,
    /// The claim's modality.
    pub modality: Modality,
    /// The authored claim.
    pub origin: Option<SourceSpan>,
    /// The verdict.
    pub verdict: Verdict,
    /// Residual leaves.
    pub leaves: Vec<ProofLeaf>,
}

/// What a compiled definition supports in this build.
///
/// The fields match the browser lesson's `ExecutionCapabilities`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[expect(
    clippy::struct_excessive_bools,
    reason = "The fields mirror the browser lesson's ExecutionCapabilities record."
)]
pub struct Capabilities {
    /// `run`.
    pub execute: bool,
    /// `search`.
    pub search: bool,
    /// `prove`.
    pub prove: bool,
    /// An SMT solver decides symbolic conditions.
    pub smt: bool,
}

/// One configuration variable: the init parameter that binds it, and its sort.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ConfigVariable {
    /// K's variable name without `$` (`ENV`).
    pub name: String,
    /// The init parameter form (`env`): the ASCII lowercase of the K name.
    pub parameter: String,
    /// The declared sort.
    pub sort: String,
    /// Whether this is `$PGM`, the program bound by FILE.
    pub is_main: bool,
}

impl std::fmt::Display for ConfigVariable {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "${} (init parameter {}): {}",
            self.name, self.parameter, self.sort
        )
    }
}

/// One claim of the compiled definition.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ClaimInfo {
    /// The label as `kprove --claims` spells it (`<MAIN>-SPEC.label`).
    pub label: String,
    /// The emitted K module that holds the claim.
    pub module: String,
    /// The claim's modality.
    pub modality: Modality,
    /// The authored claim.
    pub origin: Option<SourceSpan>,
    /// Whether the claim is `trusted`: assumed without proof (KF-042).
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub trusted: bool,
    /// The backend's label for the claim.
    #[serde(skip)]
    pub(crate) backend_label: String,
}
