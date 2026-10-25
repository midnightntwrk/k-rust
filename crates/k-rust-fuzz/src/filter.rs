//! The witness filter (FZ-COMPARABLE-B; ARCHITECTURE 7): a client's own judgement of candidate
//! witnesses, applied inside the campaign.
//!
//! A client that re-judges a witness with rules of its own (kink, whose end check refuses some
//! domain values) may refuse a candidate the fuzz confirmed. When that refusal depends on the
//! input, refusing only after the campaign ends loses the search: the campaign stops at the first
//! confirmed hit, and shrinking moves toward the values the client refuses. A [`WitnessFilter`]
//! lets the campaign ask the client during the search, through [`crate::Campaign::run_filtered`]:
//! - a hit's case is judged before its confirmation, and the confirmed case after it; a refused
//!   hit is no witness, and the search goes on (its case is `unsupported` with the reason
//!   `client-refused`);
//! - every shrink candidate is judged the same way inside the shrink screen, so a shrunk witness
//!   is one the client accepts;
//! - when shrinking is on, a refused hit's repair candidates ([`WitnessFilter::repair`]) are run
//!   and judged as full cases, and the first that hits with the same kind of kill, is accepted,
//!   is confirmed and is accepted again becomes the witness (its `repaired-from` names the
//!   refused case).
//!
//! The filter only removes candidates: every witness of a filtered campaign is a witness of the
//! unfiltered campaign's judgement too, confirmed the same way. A filter that accepts every case
//! gives the unfiltered report, apart from `identity.filter`.
//!
//! **Determinism.** [`WitnessFilter::judge`] and [`WitnessFilter::repair`] must be pure
//! functions of their arguments (`&mut self` is for caches only), and [`WitnessFilter::id`]
//! must name everything else they read, so that a filtered report is a function of the
//! campaign's inputs and the filter's identity (ARCHITECTURE 5.4). When the two judgements of
//! one hit disagree, the engine compares the two witness cases: equal cases with different
//! verdicts are a client defect (the campaign aborts, `client-defect`); different cases are a
//! difference the fuzz's confirmation did not catch, recorded as an engine defect, and the
//! refusal wins. The filter is called on the campaign's thread, never in parallel; a panic in it
//! aborts the campaign (`client-panic`).

use crate::{report::WitnessCase, values::Value};

/// The most repair candidates the engine runs for one refused hit; a filter's further
/// candidates are ignored.
pub const MAX_REPAIR_CANDIDATES: usize = 4;

/// How many refused hits of one cause the engine repairs without success before it repairs no
/// more hits of that cause: a refusal that holds for every input of the campaign (a value the
/// client refuses whatever it is) would otherwise cost the repair candidates' runs on every hit.
pub const MAX_FAILED_REPAIRS: u64 = 3;

/// The longest cause token, in bytes ([`is_cause`]).
pub const MAX_CAUSE_BYTES: usize = 64;

/// The most refusal causes the report's `client-refusals` describe; the hits of further causes
/// are counted in `totals.filter` alone.
pub const MAX_CLIENT_REFUSALS: usize = 16;

/// A client's judgement of candidate witnesses (module documentation).
pub trait WitnessFilter {
    /// The filter's identity, recorded as the report's `identity.filter`: it names the filter's
    /// rules and every input its judgements read besides the case (configuration, versions of
    /// the rules it composes), so that two filters with one identity judge every case alike.
    fn id(&self) -> String;

    /// Whether the client accepts `case` as a witness, or why it refuses it. A pure function of
    /// `case` (`&mut self` only for caches): the engine judges a hit's case and its confirmation,
    /// and a disagreement on equal cases is a client defect.
    ///
    /// # Errors
    ///
    /// The refusal; its cause must be a cause token ([`is_cause`]), or the campaign aborts
    /// (`client-defect`).
    fn judge(&mut self, case: &WitnessCase) -> Result<(), FilterRefusal>;

    /// Candidate assignments (values in hole order) that may repair the refused `case`, whose
    /// values are `values`, given its `refusal`: at most [`MAX_REPAIR_CANDIDATES`] are run, in
    /// order, each as a full case. A pure function of its arguments. None by default, and for a
    /// refusal no input of the campaign could avoid.
    fn repair(
        &mut self,
        _case: &WitnessCase,
        _values: &[Value],
        _refusal: &FilterRefusal,
    ) -> Vec<Vec<Value>> {
        Vec::new()
    }
}

/// Why a [`WitnessFilter`] refuses a case.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FilterRefusal {
    /// What the client refuses, as a cause token ([`is_cause`]): the report counts refused hits
    /// per cause.
    pub cause: String,
    /// The refusal in the client's words, for the report's `client-refusals`.
    pub detail: String,
    /// What may give a case the client accepts, for the no-witness statement.
    pub remedy: Option<String>,
}

/// Whether `cause` is a cause token: 1 to [`MAX_CAUSE_BYTES`] bytes of lowercase ASCII letters,
/// digits, `-` and `:`.
#[must_use]
pub fn is_cause(cause: &str) -> bool {
    !cause.is_empty()
        && cause.len() <= MAX_CAUSE_BYTES
        && cause.bytes().all(|byte| {
            byte.is_ascii_lowercase() || byte.is_ascii_digit() || matches!(byte, b'-' | b':')
        })
}

#[cfg(test)]
mod tests {
    use super::is_cause;

    #[test]
    fn a_cause_token_is_short_lowercase_kebab() {
        for cause in [
            "domain-value",
            "cross-domain-value",
            "initial-state:x",
            "a",
            "0",
        ] {
            assert!(is_cause(cause), "{cause}");
        }
        for cause in ["", "Domain", "domain value", "é", &"a".repeat(65)] {
            assert!(!is_cause(cause), "{cause}");
        }
        assert!(is_cause(&"a".repeat(64)));
    }
}
