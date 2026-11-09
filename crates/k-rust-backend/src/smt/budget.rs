//! How each solver attempt of a query is bounded: by Z3 resource units, or by the clock
//! (docs/compatibility.md, "Clock-free solver mode").
//!
//! A solver answer must be a function of its query (CF-33): under [`SmtBudget::Units`] whether
//! an attempt answers `sat`, `unsat` or `unknown` is a function of the query, the budget and the
//! Z3 build, and under [`SmtBudget::Clock`] it also depends on the machine's speed and load. So
//! units are the default, and a clock is built only where a caller asks for one: by
//! [`SmtBudget::clock`], or by [`SmtBudget::requested`] from data that names a clock. Both are
//! `disallowed-methods` in the workspace's `clippy.toml`, so every place that can make an answer
//! depend on the clock carries an `#[expect(clippy::disallowed_methods, reason = "...")]` that
//! says why, and `grep -rn 'SmtBudget::clock\|SmtBudget::requested'` lists them all. No other
//! function or impl of this crate yields a clock: [`SmtClock`] has no public constructor, and
//! [`SmtBudget`] implements no `Deserialize`.

use std::{fmt, num::NonZeroU32};

/// The Z3 resource units of the first attempt of the default budget: about the work Z3 5.3.3
/// does in 125 ms.
///
/// Derivation. Z3 counts resource units in its own search, at a rate per millisecond that
/// depends on the query and the Z3 build. 200 queries whose first 125 ms attempt the clock
/// stopped, replayed on Z3 4.16.0 at the host's ordinary load (x86_64), counted a median of
/// about 2,500 units per millisecond, so 125 ms was about 310,000 units on that build. The same
/// 200 queries replayed for 125 ms on Z3 5.3.3 and 4.16.0 side by side, one after the other per
/// query, in three rounds at a load of 57 to 70 on 32 CPUs, counted a median of 1.2 times as many
/// units per millisecond on 5.3.3 (per query p10 0.8, p90 1.9; the round medians 1.18, 1.20 and
/// 1.23), so 125 ms is about 1.2 x 310,000 = 370,000 units on 5.3.3. Read directly, the loaded
/// host's 5.3.3 median of 2,230 to 2,330 units per millisecond, scaled by the 4.16.0 slowdown the
/// same rounds show (1,820 to 1,960 against 2,500), gives 375,000 to 390,000. With the default 3
/// retries at doubled units the attempts are L, 2L, 4L and 8L, 15 L (about 5.6M units) in all.
///
/// The calibration holds for the build it was measured on, not for a version number, and a rate
/// is not a power to decide. One attempt from a fresh context decides each of those 200 queries
/// on both builds within 40M units, and 5.3.3 needs a median of 1.6 times the units 4.16.0 needs
/// (per query p10 0.74, p90 5.2; medians 1.9M and 1.0M), so in the same time it decides fewer of
/// them: with this budget it decides 144 of the 200, where 4.16.0 with 310,000 units decided
/// 177 to 180. Over all 183 claims of that specification's proofs the two builds, each under its
/// own calibration, reach the same verdicts (182 proven, 1 failed on a stuck leaf), with 184 of
/// the 16,001 queries 5.3.3 is asked left undecided against 73 of 15,879 on 4.16.0. In the same
/// 125 ms Z3 4.12.5 counted a median of 3.3 times the units of 4.16.0. An answer under this
/// budget is a function of the query, the budget and the build, and what it decides on another
/// build is known only from runs on that build. The budget is recalibrated on a change of the Z3
/// build, or when a verdict of a pinned corpus moves, not on a drift of units per millisecond.
pub const DEFAULT_SMT_RESOURCE_LIMIT: NonZeroU32 =
    NonZeroU32::new(370_000).expect("the budget is not zero");

/// How each attempt of a query is bounded; each retry doubles the first attempt's bound. Exactly
/// one of the two modes holds.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SmtBudget {
    /// The first attempt's Z3 resource units (`rlimit`), and no wall-clock timeout. Z3 counts
    /// these units in its own search, and every query runs on a Z3 context of its own, so an
    /// answer (sat, unsat or unknown) is a function of the query, the budget, the retries and
    /// the Z3 build, never of the machine's speed or load.
    Units(NonZeroU32),
    /// A wall-clock timeout ([`SmtClock`]), which only [`SmtBudget::clock`] and
    /// [`SmtBudget::requested`] build: whether a query is decided then depends on the machine's
    /// speed and load.
    Clock(SmtClock),
}

/// The clock of [`SmtBudget::Clock`]: the first attempt's wall-clock timeout in milliseconds,
/// with a resource limit proportional to it as a backstop for a cancellation Z3 loses. It has no
/// public constructor: a clock is built only through [`SmtBudget::clock`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SmtClock {
    timeout_ms: u32,
}

impl SmtClock {
    /// The first attempt's wall-clock timeout in milliseconds.
    #[must_use]
    pub const fn timeout_ms(self) -> u32 {
        self.timeout_ms
    }
}

/// Data that names both a clock and a unit budget ([`SmtBudget::requested`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BudgetConflict;

impl fmt::Display for BudgetConflict {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(
            "a solver budget is either a wall-clock timeout or Z3 resource units, not both",
        )
    }
}

impl std::error::Error for BudgetConflict {}

impl SmtBudget {
    /// The default budget: [`DEFAULT_SMT_RESOURCE_LIMIT`] units.
    pub const DEFAULT: Self = Self::Units(DEFAULT_SMT_RESOURCE_LIMIT);

    /// The one door to the clock: each attempt bounded by `timeout_ms` milliseconds, doubled on
    /// each retry. A caller states why its answers may depend on the machine's speed and load in
    /// an `#[expect(clippy::disallowed_methods, reason = "...")]`.
    #[must_use]
    pub const fn clock(timeout_ms: u32) -> Self {
        Self::Clock(SmtClock { timeout_ms })
    }

    /// The budget that data asks for: a clock when it names only a timeout (an explicit
    /// `smtTimeoutMs` or `--smt-timeout` means what it says), those units when it names only
    /// units, and [`Self::DEFAULT`] when it names neither.
    ///
    /// # Errors
    ///
    /// [`BudgetConflict`] when it names both.
    pub const fn requested(
        timeout_ms: Option<u32>,
        units: Option<NonZeroU32>,
    ) -> Result<Self, BudgetConflict> {
        match (timeout_ms, units) {
            (None, None) => Ok(Self::DEFAULT),
            (None, Some(units)) => Ok(Self::Units(units)),
            #[expect(
                clippy::disallowed_methods,
                reason = "the door of data that names a clock; each caller states its own reason"
            )]
            (Some(timeout_ms), None) => Ok(Self::clock(timeout_ms)),
            (Some(_), Some(_)) => Err(BudgetConflict),
        }
    }

    /// The first attempt's resource units, under [`Self::Units`].
    #[must_use]
    pub const fn units(self) -> Option<NonZeroU32> {
        match self {
            Self::Units(units) => Some(units),
            Self::Clock(_) => None,
        }
    }

    /// The first attempt's wall-clock timeout, under [`Self::Clock`].
    #[must_use]
    pub const fn clock_ms(self) -> Option<u32> {
        match self {
            Self::Units(_) => None,
            Self::Clock(clock) => Some(clock.timeout_ms),
        }
    }

    /// Whether an undecided answer under this budget is a function of the query: true under
    /// [`Self::Units`].
    #[must_use]
    pub const fn is_clock_free(self) -> bool {
        matches!(self, Self::Units(_))
    }
}

impl Default for SmtBudget {
    fn default() -> Self {
        Self::DEFAULT
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Data naming neither bound gets the default units, a timeout alone a clock, units alone
    /// those units, and both a refusal.
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the decoding of data that names a clock is what this tests"
    )]
    fn requested_budgets_are_units_unless_a_clock_alone_is_named() {
        let units = NonZeroU32::new(5).unwrap();
        assert_eq!(SmtBudget::requested(None, None), Ok(SmtBudget::DEFAULT));
        assert_eq!(
            SmtBudget::requested(None, Some(units)),
            Ok(SmtBudget::Units(units))
        );
        assert_eq!(
            SmtBudget::requested(Some(40), None).map(SmtBudget::clock_ms),
            Ok(Some(40))
        );
        assert_eq!(
            SmtBudget::requested(Some(40), Some(units)),
            Err(BudgetConflict)
        );
        assert_eq!(SmtBudget::default(), SmtBudget::DEFAULT);
        assert!(SmtBudget::DEFAULT.is_clock_free());
        assert_eq!(SmtBudget::DEFAULT.units(), Some(DEFAULT_SMT_RESOURCE_LIMIT));
    }
}
