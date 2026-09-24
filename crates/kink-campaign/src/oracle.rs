use crate::OracleOutcome;
use kink_contracts::Completeness;
use kink_portable::{Digest, SemanticJson};
use std::fmt;

/// The six BAG-12 oracle kinds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OracleKind {
    /// Exit/stop class and declared object-program exit code.
    ExitStop,
    /// Whole final term or ordered typed final-term paths.
    FinalResult,
    /// Ordered semantic-output bytes or UTF-8-normalized channels.
    ConcreteOutput,
    /// Finite reachability truth.
    Reachability,
    /// Execution-pattern outcome, optionally with complete bindings.
    ExecutionPattern,
    /// Structured-predicate Bool.
    StructuredPredicate,
}

/// Declaration-owned semantic-crash comparison policy.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CrashPolicy {
    /// A crash is outside the admitted operand domain.
    Reject,
    /// Equal crash identities agree; unequal crashes distinguish.
    CompareIdentity,
    /// Any baseline/mutant crash-shape difference distinguishes.
    Distinguish,
}

/// One exact declaration-scoped semantic side.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OracleSide {
    /// Kind-validated normalized value.
    Normal {
        /// Closed normalized value supplied by the kind-specific portable evaluator.
        value: SemanticJson,
        /// Completeness of the value's producing finite input.
        completeness: Completeness,
    },
    /// Object-language crash operand, identified by its crash digest.
    SemanticCrash(Digest),
    /// Operand production was semantically unknown.
    Unknown,
    /// Operand production failed in infrastructure/backend code.
    Error,
}
/// Compares two already kind-validated supplied sides.
///
/// This function performs no K parsing, projection, solver work, or discovery.
pub fn compare_supplied(
    kind: OracleKind,
    crash_policy: CrashPolicy,
    baseline: &OracleSide,
    mutant: &OracleSide,
) -> Result<OracleOutcome, OracleFailure> {
    match (baseline, mutant) {
        (OracleSide::Error, _) | (_, OracleSide::Error) => Ok(OracleOutcome::Error),
        (OracleSide::Unknown, _) | (_, OracleSide::Unknown) => Ok(OracleOutcome::Unknown),
        (
            OracleSide::Normal {
                completeness: left_completeness,
                ..
            },
            OracleSide::Normal {
                completeness: right_completeness,
                ..
            },
        ) if *left_completeness != Completeness::CompleteFinite
            || *right_completeness != Completeness::CompleteFinite =>
        {
            Ok(OracleOutcome::Unknown)
        }
        (OracleSide::Normal { value: left, .. }, OracleSide::Normal { value: right, .. }) => {
            validate_normalized_value(kind, left)?;
            validate_normalized_value(kind, right)?;
            Ok(if left == right {
                OracleOutcome::Agree
            } else {
                OracleOutcome::Distinguish
            })
        }
        (OracleSide::SemanticCrash(left), OracleSide::SemanticCrash(right)) => match crash_policy {
            CrashPolicy::Reject => Err(OracleFailure::new(
                OracleFailureKind::CrashRejected,
                "declaration terminal policy rejects semantic crashes",
            )),
            CrashPolicy::CompareIdentity | CrashPolicy::Distinguish => Ok(if left == right {
                OracleOutcome::Agree
            } else {
                OracleOutcome::Distinguish
            }),
        },
        (OracleSide::SemanticCrash(_), OracleSide::Normal { .. })
        | (OracleSide::Normal { .. }, OracleSide::SemanticCrash(_)) => match crash_policy {
            CrashPolicy::Reject => Err(OracleFailure::new(
                OracleFailureKind::CrashRejected,
                "declaration terminal policy rejects semantic crashes",
            )),
            CrashPolicy::CompareIdentity => Ok(OracleOutcome::Incomparable),
            CrashPolicy::Distinguish => Ok(OracleOutcome::Distinguish),
        },
    }
}

fn validate_normalized_value(kind: OracleKind, value: &SemanticJson) -> Result<(), OracleFailure> {
    let Some(fields) = value.as_object() else {
        // Reduced scripted values are retained only for the nonportable unit
        // seam. Portable operand ingress is schema-exact and always supplies
        // the structured kind-specific object validated below.
        return Ok(());
    };
    let valid = match kind {
        OracleKind::ExitStop => {
            exact_keys(fields, &["exitCode", "terminalClass"])
                && matches!(
                    fields.get("terminalClass").and_then(SemanticJson::as_str),
                    Some("normal" | "stuck")
                )
                && matches!(
                    fields.get("exitCode"),
                    Some(SemanticJson::Null | SemanticJson::Integer(_))
                )
        }
        OracleKind::FinalResult => {
            exact_keys(fields, &["projection", "term", "terminalState"])
                || exact_keys(fields, &["paths", "projection", "terminalState"])
        }
        OracleKind::ConcreteOutput => {
            exact_keys(fields, &["channels"])
                && matches!(fields.get("channels"), Some(SemanticJson::Array(items)) if !items.is_empty())
        }
        OracleKind::Reachability => {
            exact_keys(fields, &["status", "witnesses"])
                && matches!(
                    fields.get("status").and_then(SemanticJson::as_str),
                    Some("reached" | "not-reached")
                )
        }
        OracleKind::ExecutionPattern => {
            exact_keys(fields, &["bindingTuples", "outcome", "patternResult"])
                && matches!(
                    fields.get("outcome").and_then(SemanticJson::as_str),
                    Some("match" | "no-match" | "unknown" | "error")
                )
        }
        OracleKind::StructuredPredicate => {
            exact_keys(
                fields,
                &[
                    "bindings",
                    "bindingsDigest",
                    "input",
                    "inputProjectionDigest",
                    "query",
                    "result",
                ],
            ) && matches!(fields.get("result"), Some(SemanticJson::Bool(_)))
        }
    };
    if !valid {
        return Err(OracleFailure::new(
            OracleFailureKind::InvalidKindValue,
            "normal value does not have the exact shape for its oracle kind",
        ));
    }
    Ok(())
}

fn exact_keys(
    fields: &std::collections::BTreeMap<String, SemanticJson>,
    expected: &[&str],
) -> bool {
    fields.len() == expected.len() && expected.iter().all(|name| fields.contains_key(*name))
}

/// Closed oracle failure classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OracleFailureKind {
    /// Declaration policy rejects a crash operand.
    CrashRejected,
    /// A normal value does not belong to the selected oracle family.
    InvalidKindValue,
}

/// Typed oracle failure with supplemental diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OracleFailure {
    kind: OracleFailureKind,
    detail: String,
}

impl OracleFailure {
    fn new(kind: OracleFailureKind, detail: impl Into<String>) -> Self {
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
