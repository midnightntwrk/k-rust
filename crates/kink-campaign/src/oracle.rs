use crate::OracleOutcome;
use k_rust::kore::ast::Pattern;
use kink_pattern::Binding;
use std::collections::BTreeSet;
use std::fmt;

/// The oracle kinds `compare_supplied` can compare. Reachability and structured
/// predicates wait for k-rust search completeness (`upstream/k-rust.toml`
/// `search-completeness`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OracleKind {
    /// Terminal class and declared object-program exit code.
    ExitStop,
    /// Whole final terms or selected final subterms.
    FinalResult,
    /// Execution-pattern outcome, optionally with complete bindings. A pattern failure
    /// (`kink_pattern::evaluate` rejecting its input) on either side must be supplied as
    /// `OracleSide::Error`, never as a value that could Distinguish.
    ExecutionPattern,
}

/// Declaration-owned semantic-crash comparison policy.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CrashPolicy {
    /// A crash is outside the admitted operand domain.
    Reject,
    /// Equal crash terms agree; unequal crashes distinguish; a crash against a
    /// normal value is incomparable.
    CompareIdentity,
    /// Any baseline/mutant crash-shape difference distinguishes.
    Distinguish,
}

/// How a complete, non-crash terminal ended, as the declaration's classifier says.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TerminalClass {
    Normal,
    Stuck,
}

/// One terminal's exit-stop projection.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ExitStop {
    pub class: TerminalClass,
    /// The declared exit-code cell's value, or `None` when no cell is declared.
    pub code: Option<i64>,
}

/// A final-result projection over every terminal of the run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FinalResult {
    /// The whole terminal terms.
    WholeTerm(BTreeSet<Pattern>),
    /// Per terminal, the subterm at each declared child-index path, in path order.
    TermPaths(BTreeSet<Vec<(Vec<u32>, Pattern)>>),
}

/// An execution-pattern value. `Unknown` and `Error` evaluations are never values.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PatternValue {
    /// `bindings` is the set of witness binding tuples when the declaration asks for
    /// them, which requires complete coverage; a set does not depend on witness order.
    Match {
        bindings: Option<BTreeSet<Vec<Binding>>>,
    },
    /// Only from complete evidence.
    NoMatch,
}

/// A complete normal value. State values are sets over the complete terminal set, so a
/// nondeterministic semantics compares as a whole.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OracleValue {
    ExitStop(BTreeSet<ExitStop>),
    FinalResult(FinalResult),
    Pattern(PatternValue),
}

impl OracleValue {
    /// The kind this value belongs to.
    #[must_use]
    pub const fn kind(&self) -> OracleKind {
        match self {
            Self::ExitStop(_) => OracleKind::ExitStop,
            Self::FinalResult(_) => OracleKind::FinalResult,
            Self::Pattern(_) => OracleKind::ExecutionPattern,
        }
    }

    /// Whether the value is of `kind` and names at least one terminal.
    fn is_valid_for(&self, kind: OracleKind) -> bool {
        self.kind() == kind
            && match self {
                Self::ExitStop(stops) => !stops.is_empty(),
                Self::FinalResult(FinalResult::WholeTerm(terms)) => !terms.is_empty(),
                Self::FinalResult(FinalResult::TermPaths(terms)) => !terms.is_empty(),
                Self::Pattern(_) => true,
            }
    }
}

/// One exact declaration-scoped semantic side.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OracleSide {
    /// A value from complete evidence. Incomplete evidence is `Unknown`, never `Normal`.
    Normal(OracleValue),
    /// The run's only terminal, classified as an object-language crash: its own
    /// terminal term.
    SemanticCrash(Pattern),
    /// A declared time bound stopped operand production.
    Timeout,
    /// Operand production was semantically unknown.
    Unknown,
    /// Operand production failed in infrastructure/backend code.
    Error,
}

/// Compares two supplied sides of one declaration.
///
/// A failed side decides first, in the order error, timeout, unknown. Two crashes
/// compare by their terminal terms under `crash_policy`. A normal value of another
/// kind, an empty value, a whole-term value against a term-path value, or a match
/// with bindings against one without is `InvalidKindValue`. This function performs
/// no K parsing, projection, solver work, or discovery.
pub fn compare_supplied(
    kind: OracleKind,
    crash_policy: CrashPolicy,
    baseline: &OracleSide,
    mutant: &OracleSide,
) -> Result<OracleOutcome, OracleFailure> {
    match (baseline, mutant) {
        (OracleSide::Error, _) | (_, OracleSide::Error) => Ok(OracleOutcome::Error),
        (OracleSide::Timeout, _) | (_, OracleSide::Timeout) => Ok(OracleOutcome::Timeout),
        (OracleSide::Unknown, _) | (_, OracleSide::Unknown) => Ok(OracleOutcome::Unknown),
        (OracleSide::Normal(left), OracleSide::Normal(right)) => {
            check_value(kind, left)?;
            check_value(kind, right)?;
            if !same_shape(left, right) {
                return Err(OracleFailure::new(
                    OracleFailureKind::InvalidKindValue,
                    "the two values were projected differently",
                ));
            }
            Ok(if left == right {
                OracleOutcome::Agree
            } else {
                OracleOutcome::Distinguish
            })
        }
        (OracleSide::SemanticCrash(left), OracleSide::SemanticCrash(right)) => match crash_policy {
            CrashPolicy::Reject => Err(crash_rejected()),
            CrashPolicy::CompareIdentity | CrashPolicy::Distinguish => Ok(if left == right {
                OracleOutcome::Agree
            } else {
                OracleOutcome::Distinguish
            }),
        },
        (OracleSide::SemanticCrash(_), OracleSide::Normal(value))
        | (OracleSide::Normal(value), OracleSide::SemanticCrash(_)) => {
            check_value(kind, value)?;
            match crash_policy {
                CrashPolicy::Reject => Err(crash_rejected()),
                CrashPolicy::CompareIdentity => Ok(OracleOutcome::Incomparable),
                CrashPolicy::Distinguish => Ok(OracleOutcome::Distinguish),
            }
        }
    }
}

fn check_value(kind: OracleKind, value: &OracleValue) -> Result<(), OracleFailure> {
    if value.is_valid_for(kind) {
        Ok(())
    } else {
        Err(OracleFailure::new(
            OracleFailureKind::InvalidKindValue,
            "normal value is empty or belongs to another oracle kind",
        ))
    }
}

/// Whether two values of one kind came from the same projection.
const fn same_shape(left: &OracleValue, right: &OracleValue) -> bool {
    match (left, right) {
        (
            OracleValue::FinalResult(FinalResult::WholeTerm(_)),
            OracleValue::FinalResult(FinalResult::TermPaths(_)),
        )
        | (
            OracleValue::FinalResult(FinalResult::TermPaths(_)),
            OracleValue::FinalResult(FinalResult::WholeTerm(_)),
        ) => false,
        (
            OracleValue::Pattern(PatternValue::Match { bindings: left }),
            OracleValue::Pattern(PatternValue::Match { bindings: right }),
        ) => left.is_some() == right.is_some(),
        _ => true,
    }
}

fn crash_rejected() -> OracleFailure {
    OracleFailure::new(
        OracleFailureKind::CrashRejected,
        "declaration terminal policy rejects semantic crashes",
    )
}

/// Closed oracle failure classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OracleFailureKind {
    /// Declaration policy rejects a crash operand.
    CrashRejected,
    /// A normal value does not belong to the selected oracle family.
    InvalidKindValue,
    /// An oracle declaration is not well formed.
    InvalidDeclaration,
}

/// Typed oracle failure with supplemental diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OracleFailure {
    kind: OracleFailureKind,
    detail: String,
}

impl OracleFailure {
    pub(crate) fn new(kind: OracleFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Decision-bearing classification.
    #[must_use]
    pub const fn kind(&self) -> OracleFailureKind {
        self.kind
    }
}

impl fmt::Display for OracleFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for OracleFailure {}
