//! The red list, `krs/tests/class-matrix/pending.toml`: the cases known not to conform.
//!
//! Each entry is a table keyed by the case's ID, with the `finding` that owns the deviation
//! (`unassigned` while none does), the observed `deviation` exactly as the harness prints it
//! ([`super::invariants::signature`]), and optionally the `step` (`S1` to `S6`) whose design
//! makes the case conform:
//!
//! ```toml
//! ["readable/result/pc/Some(x)"]
//! finding = "unassigned"
//! deviation = "krs::expand::not-a-declaration @ spelling"
//! step = "S5"
//! ```
//!
//! The rules ([`Pending::judge`]):
//! - a case that conforms passes;
//! - a pending case that deviates as recorded passes and counts as red;
//! - a pending case that conforms fails, until it is removed from the list;
//! - a pending case that deviates differently fails, until the new deviation is recorded;
//! - a case that deviates and is not pending fails.
//!
//! So the list only shrinks or changes deliberately, and every fix's regression test is its
//! cases leaving the list.
//!
//! An entry whose ID starts with [`LATTICE`] is not a case: it records one disagreement of K4,
//! the sort judges' test (`lattice/DEFINITION/JUDGE~JUDGE/CLASS`), which judges those entries
//! under the same rules.
//!
//! Both tiers read a case's entry, so for a case the front refuses they must observe it alike.
//! Three prefixes name a case's entries that only the full tier reads:
//! - [`KEYS`], `k1/CASE`: K1's verdict after lowering, on the semantic keys and anchors of the
//!   collected case;
//! - [`CLOSURE`], `k3/CASE`: K3's verdict on the source `krs expand` prints for the case;
//! - [`FULL`], `full/CASE`: the full tier's deviation of a case that the front refuses and the
//!   full tier observes otherwise (rustc adds an error to the front's, say). The full tier reads
//!   it in place of `CASE`'s entry.

use std::collections::BTreeMap;
use std::fmt;

use toml_edit::DocumentMut;

/// The finding of a deviation that no finding owns yet.
pub const UNASSIGNED: &str = "unassigned";

/// The ID prefix of the entries that record a disagreement among sort judges, not a case.
pub const LATTICE: &str = "lattice/";

/// The ID prefix of the full tier's K1 entries, `k1/CASE`.
pub const KEYS: &str = "k1/";

/// The ID prefix of the full tier's K3 entries, `k3/CASE`.
pub const CLOSURE: &str = "k3/";

/// The ID prefix of a case's entry that only the full tier reads, `full/CASE`.
pub const FULL: &str = "full/";

/// The case an entry's ID names: the ID itself, or the ID after [`KEYS`], [`CLOSURE`] or
/// [`FULL`]; `None` for a [`LATTICE`] entry, which names no case.
#[must_use]
pub fn case_of(id: &str) -> Option<&str> {
    if id.starts_with(LATTICE) {
        return None;
    }
    Some(
        id.strip_prefix(KEYS)
            .or_else(|| id.strip_prefix(CLOSURE))
            .or_else(|| id.strip_prefix(FULL))
            .unwrap_or(id),
    )
}

/// One pending case.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PendingEntry {
    /// The finding that owns the deviation, or [`UNASSIGNED`].
    pub finding: String,
    /// The deviation's signature, exactly as observed.
    pub deviation: String,
    /// The step (`S1` to `S6`) that makes the case conform, when known.
    pub step: Option<String>,
}

/// The parsed red list.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Pending {
    /// The pending cases by ID.
    pub entries: BTreeMap<String, PendingEntry>,
}

/// What a case did, against its expectation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Observation<'a> {
    /// The case met its expectation.
    Conforms,
    /// The case deviated; the signature of what it did.
    Deviates(&'a str),
}

/// The verdict of one case under the PENDING rules.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Judgement {
    /// The case conforms and is not pending.
    Conforms,
    /// The case is pending and deviates as recorded.
    Red,
    /// The case is pending but conforms: remove it from `pending.toml`.
    NowConforms,
    /// The case is pending but deviates differently: record the new deviation.
    DeviationChanged {
        /// The recorded signature.
        recorded: String,
        /// The observed signature.
        observed: String,
    },
    /// The case deviates and is not pending.
    Unexpected {
        /// The observed signature.
        observed: String,
    },
}

impl Judgement {
    /// Whether the suite passes this case.
    #[must_use]
    pub const fn passes(&self) -> bool {
        matches!(self, Self::Conforms | Self::Red)
    }
}

impl fmt::Display for Judgement {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Conforms => formatter.write_str("conforms"),
            Self::Red => formatter.write_str("red, as pending.toml records"),
            Self::NowConforms => {
                formatter.write_str("conforms but is pending: remove it from pending.toml")
            }
            Self::DeviationChanged { recorded, observed } => write!(
                formatter,
                "deviates as {observed:?}, but pending.toml records {recorded:?}: record the new deviation"
            ),
            Self::Unexpected { observed } => {
                write!(formatter, "deviates as {observed:?} and is not pending")
            }
        }
    }
}

impl Pending {
    /// Parse the red list's text.
    ///
    /// # Errors
    ///
    /// Returns every entry that does not follow the schema.
    pub fn parse(text: &str) -> Result<Self, Vec<String>> {
        let document = text
            .parse::<DocumentMut>()
            .map_err(|error| vec![format!("pending.toml: {error}")])?;
        let mut errors = Vec::new();
        let mut entries = BTreeMap::new();
        for (id, item) in document.iter() {
            let Some(table) = item.as_table() else {
                errors.push(format!("{id:?} is not a table"));
                continue;
            };
            let field = |key: &str, errors: &mut Vec<String>| match table.get(key) {
                None => None,
                Some(value) => {
                    let text = value.as_str().map(str::to_owned);
                    if text.as_deref().is_none_or(str::is_empty) {
                        errors.push(format!("{id:?}.{key} is not a non-empty string"));
                    }
                    text
                }
            };
            for (key, _) in table {
                if !["finding", "deviation", "step"].contains(&key) {
                    errors.push(format!("{id:?} has the unknown key {key:?}"));
                }
            }
            let finding = field("finding", &mut errors);
            let deviation = field("deviation", &mut errors);
            let step = field("step", &mut errors);
            if step
                .as_deref()
                .is_some_and(|step| !["S1", "S2", "S3", "S4", "S5", "S6"].contains(&step))
            {
                errors.push(format!("{id:?}.step is not one of S1 to S6"));
            }
            match (finding, deviation) {
                (Some(finding), Some(deviation)) => {
                    entries.insert(
                        id.to_owned(),
                        PendingEntry {
                            finding,
                            deviation,
                            step,
                        },
                    );
                }
                _ => errors.push(format!("{id:?} needs a finding and a deviation")),
            }
        }
        if errors.is_empty() {
            Ok(Self { entries })
        } else {
            Err(errors)
        }
    }

    /// Judge one case.
    #[must_use]
    pub fn judge(&self, id: &str, observation: Observation<'_>) -> Judgement {
        match (self.entries.get(id), observation) {
            (None, Observation::Conforms) => Judgement::Conforms,
            (Some(_), Observation::Conforms) => Judgement::NowConforms,
            (Some(entry), Observation::Deviates(observed)) if entry.deviation == observed => {
                Judgement::Red
            }
            (Some(entry), Observation::Deviates(observed)) => Judgement::DeviationChanged {
                recorded: entry.deviation.clone(),
                observed: observed.to_owned(),
            },
            (None, Observation::Deviates(observed)) => Judgement::Unexpected {
                observed: observed.to_owned(),
            },
        }
    }

    /// The pending IDs whose case ([`case_of`]) is no case of `ids`: an entry for a case the
    /// generator no longer produces must leave the list. [`LATTICE`] entries are no cases and are
    /// not listed.
    #[must_use]
    pub fn stale<'a>(&'a self, ids: &[&str]) -> Vec<&'a str> {
        self.entries
            .keys()
            .map(String::as_str)
            .filter(|id| case_of(id).is_some_and(|case| !ids.contains(&case)))
            .collect()
    }

    /// The red count per finding and per step, for the cases `red` names.
    #[must_use]
    pub fn tally<'a>(&self, red: impl IntoIterator<Item = &'a str>) -> Tally {
        let mut tally = Tally::default();
        for id in red {
            let Some(entry) = self.entries.get(id) else {
                continue;
            };
            *tally.by_finding.entry(entry.finding.clone()).or_default() += 1;
            *tally
                .by_step
                .entry(entry.step.clone().unwrap_or_else(|| "no step".to_owned()))
                .or_default() += 1;
        }
        tally
    }
}

/// Red counts, which size each finding and step.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Tally {
    /// Red cases per finding; [`UNASSIGNED`] counts the cases no finding owns yet.
    pub by_finding: BTreeMap<String, usize>,
    /// Red cases per step, `no step` for entries without one.
    pub by_step: BTreeMap<String, usize>,
}
