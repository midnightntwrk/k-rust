//! The red list, `krs/tests/class-matrix/pending.toml`: the cases known not to conform.
//!
//! Each entry is a table keyed by the case's ID, with the `finding` the deviation belongs to and
//! the observed `deviation` exactly as the harness prints it ([`super::invariants::signature`]):
//!
//! ```toml
//! ["readable/result/pc/Some(x)"]
//! finding = "B3"
//! deviation = "krs::expand::not-a-declaration @ spelling"
//! ```
//!
//! The finding is registered in `findings.toml` with its owner (a ticket, or the step `S1` to
//! `S6` whose design makes its cases conform) and its kind ([`super::findings`]); an entry has no
//! owner of its own, so it cannot disagree with its finding's. The harness writes a deviation no
//! entry records with the finding [`UNASSIGNED`], which no finding is: the author names one.
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
//! Seven prefixes name a case's entries that only the full tier reads:
//! - [`KEYS`], `k1/CASE`: K1's verdict after lowering, on the semantic keys and anchors of the
//!   collected case;
//! - [`CLOSURE`], `k3/CASE`: K3's verdict on the source `krs expand` prints for the case;
//! - [`NATIVE`], `k6/CASE`: K6's verdict on the definition the accepted case emits, judged as
//!   `krs check` judges it on the native routes;
//! - [`RUN`], `k7/CASE`: K7's verdict on the case's program, run on that definition;
//! - [`TWIN`], `twin/CASE`: the twin check's verdict on a static clause's result case: the value
//!   its run built beside the value its twin at a `#[k::rule]` fn's result built
//!   ([`super::twins`]);
//! - [`ADVICE`], `k8/CASE`: K8's verdict on a class's advised case (accepted, by K6, by K7), or
//!   on a refused case whose message advises a rewrite while its class names no advised case;
//! - [`FULL`], `full/CASE`: the full tier's deviation of a case that the front refuses and the
//!   full tier observes otherwise (rustc adds an error to the front's, say). The full tier reads
//!   it in place of `CASE`'s entry.
//!
//! **A family entry** ([`FamilyEntry`]) pends, under one finding, every red of one diagnostic
//! kind whose key a glob matches (`expected.toml`'s syntax, [`Glob`]):
//!
//! ```toml
//! [[family]]
//! match = "sweep/{claim,readable}/result/acct/*"
//! finding = "S0-9"
//! kind = "diagnostic"
//! ```
//!
//! A diagnostic red is a program refused as it should be, with the wrong code, site or advice: a
//! fix that moves it moves every case of the family at once, and an exact entry per case would
//! turn each such fix into a rewrite of all of them. So only the kinds of [`FAMILY_KINDS`] may be
//! pended by a family; a red of what KRS accepts, writes or runs (an under- or over-refusal, other
//! K, K1, K3, K4, K6, K7, the twin check) and a bug (an internal code, a panic) stays exact, one
//! entry per case, since any move of it matters. The rules:
//! - a red that both an exact entry and a family match is the exact entry's;
//! - a red the family matches whose kind is not the family's fails ([`Judgement::OtherKind`]): a
//!   diagnostic red that turns into a meaning red is no longer the family's;
//! - a case the family matches that conforms passes: what is given up is that a family does not
//!   notice one of its cases conforming, nor a red moving from one wrong code to another, while
//!   any other case of the family is still red;
//! - a family is stale where a whole run of a shard it reaches (one of the run's keys it matches)
//!   pends no red with it ([`Pending::stale_families`]): the whole family conforms, or no longer
//!   is of its kind. A run that a filter narrows cannot tell, and does not judge it.
//!
//! A family's glob starts with a literal segment, which names its test: `k8/..` for K8, a case's
//! family for K2. It never names `full/..`: a case the two tiers observe otherwise keeps its
//! exact entries. No key may be matched by two families.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use toml_edit::DocumentMut;

use super::table::Glob;

/// The placeholder finding of a deviation the harness writes out for review: no registered
/// finding has this name, so an entry that keeps it fails the registry's audit.
pub const UNASSIGNED: &str = "unassigned";

/// The ID prefix of the entries that record a disagreement among sort judges, not a case.
pub const LATTICE: &str = "lattice/";

/// The ID prefix of the full tier's K1 entries, `k1/CASE`.
pub const KEYS: &str = "k1/";

/// The ID prefix of the full tier's K3 entries, `k3/CASE`.
pub const CLOSURE: &str = "k3/";

/// The ID prefix of the full tier's K6 entries, `k6/CASE`.
pub const NATIVE: &str = "k6/";

/// The ID prefix of the full tier's K7 entries, `k7/CASE`.
pub const RUN: &str = "k7/";

/// The ID prefix of the full tier's twin-check entries, `twin/CASE` ([`super::twins`]).
pub const TWIN: &str = "twin/";

/// The ID prefix of the full tier's K8 entries, `k8/CASE`: the advice check's verdict on a class's
/// advised case, or on a refused case whose message advises a rewrite its class names no case of.
pub const ADVICE: &str = "k8/";

/// The ID prefix of a case's entry that only the full tier reads, `full/CASE`.
pub const FULL: &str = "full/";

/// K2's deviation for an accepted case whose K differs from the K the table records. Under a
/// finding it says the recorded K is the principled one and the product's K is wrong: record
/// mode keeps that K ([`Pending::holds_other_k`]), and the finding states its `risk`.
pub const OTHER_K: &str = "accepted, with other K than recorded";

/// The kinds of red ([`super::findings::Red`]'s display) a family entry may pend: a K2 red of a
/// case the table refuses, refused otherwise than the class says (`diagnostic`, and its
/// `+rust-syntax` tag), a lint's warning missing or unowed where the table accepts the program,
/// and K8's verdict on a refusal's advice. Each is what a correct verdict says, not what KRS
/// accepts, writes or runs.
pub const FAMILY_KINDS: &[&str] = &[
    "diagnostic",
    "diagnostic+rust-syntax",
    "lint-missing",
    "lint-unowed",
    "k8",
];

/// The table key of the family entries, `[[family]]`.
pub const FAMILY: &str = "family";

/// The case an entry's ID names: the ID itself, or the ID after [`KEYS`], [`CLOSURE`],
/// [`NATIVE`], [`RUN`], [`TWIN`], [`ADVICE`] or [`FULL`]; `None` for a [`LATTICE`] entry, which
/// names no case.
#[must_use]
pub fn case_of(id: &str) -> Option<&str> {
    if id.starts_with(LATTICE) {
        return None;
    }
    Some(
        id.strip_prefix(KEYS)
            .or_else(|| id.strip_prefix(CLOSURE))
            .or_else(|| id.strip_prefix(NATIVE))
            .or_else(|| id.strip_prefix(RUN))
            .or_else(|| id.strip_prefix(TWIN))
            .or_else(|| id.strip_prefix(ADVICE))
            .or_else(|| id.strip_prefix(FULL))
            .unwrap_or(id),
    )
}

/// The test a pending key belongs to: `k1`, `k3`, `k6`, `k7`, `twin` or `k8` by its prefix, `k4`
/// for a [`LATTICE`] entry, `k5` for a broken entry point's (`entry/..`), and `k2` otherwise
/// ([`FULL`] included).
#[must_use]
pub fn test_of(key: &str) -> &'static str {
    [
        (KEYS, "k1"),
        (CLOSURE, "k3"),
        (NATIVE, "k6"),
        (RUN, "k7"),
        (TWIN, "twin"),
        (ADVICE, "k8"),
        (LATTICE, "k4"),
        ("entry/", "k5"),
    ]
    .into_iter()
    .find(|(prefix, _)| key.starts_with(prefix))
    .map_or("k2", |(_, test)| test)
}

/// One pending case.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PendingEntry {
    /// The finding the deviation belongs to, registered in `findings.toml`.
    pub finding: String,
    /// The deviation's signature, exactly as observed.
    pub deviation: String,
}

/// A family entry: every red of one kind whose key a glob matches, under one finding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FamilyEntry {
    /// The glob over pending keys, as written.
    pub pattern: String,
    /// The parsed glob.
    pub glob: Glob,
    /// The finding its reds belong to, registered in `findings.toml`.
    pub finding: String,
    /// The kind of red it pends, one of [`FAMILY_KINDS`].
    pub kind: String,
}

/// The parsed red list.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Pending {
    /// The pending cases by ID.
    pub entries: BTreeMap<String, PendingEntry>,
    /// The family entries, in the file's order.
    pub families: Vec<FamilyEntry>,
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
    /// The case has no exact entry, and a family entry matches its key, but the case's red is of
    /// another kind than the family's: record it as an exact entry under its finding.
    OtherKind {
        /// The family's glob.
        family: String,
        /// The family's kind.
        recorded: String,
        /// The kind of the observed red.
        kind: String,
        /// The observed signature.
        observed: String,
    },
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
            Self::OtherKind {
                family,
                recorded,
                kind,
                observed,
            } => write!(
                formatter,
                "deviates as {observed:?}, a {kind} red, but the family entry {family:?} pends \
                 {recorded} reds only: record the red as an exact entry under its finding"
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
        let mut families = Vec::new();
        for (id, item) in document.iter() {
            if id == FAMILY {
                match item.as_array_of_tables() {
                    Some(tables) => {
                        for (index, table) in tables.iter().enumerate() {
                            match parse_family(table) {
                                Ok(family) => families.push(family),
                                Err(more) => {
                                    errors.extend(more.into_iter().map(|error| {
                                        format!("[[{FAMILY}]] {}: {error}", index + 1)
                                    }));
                                }
                            }
                        }
                    }
                    None => errors.push(format!(
                        "{id:?} is not an array of family tables: write each as `[[{FAMILY}]]`"
                    )),
                }
                continue;
            }
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
                if key == "step" {
                    errors.push(format!(
                        "{id:?}.step: a step owns a finding, not an entry; it is the finding's \
                         owner in findings.toml"
                    ));
                } else if !["finding", "deviation"].contains(&key) {
                    errors.push(format!("{id:?} has the unknown key {key:?}"));
                }
            }
            let finding = field("finding", &mut errors);
            let deviation = field("deviation", &mut errors);
            match (finding, deviation) {
                (Some(finding), Some(deviation)) => {
                    entries.insert(id.to_owned(), PendingEntry { finding, deviation });
                }
                _ => errors.push(format!("{id:?} needs a finding and a deviation")),
            }
        }
        if errors.is_empty() {
            Ok(Self { entries, families })
        } else {
            Err(errors)
        }
    }

    /// The family entry that pends a red keyed `key` with no exact entry: the first whose glob
    /// matches it.
    #[must_use]
    pub fn family_of(&self, key: &str) -> Option<&FamilyEntry> {
        self.families.iter().find(|family| family.glob.matches(key))
    }

    /// Whether an entry, exact or family, names the key `key`.
    #[must_use]
    pub fn names(&self, key: &str) -> bool {
        self.entries.contains_key(key) || self.family_of(key).is_some()
    }

    /// The finding of the red keyed `key` that [`Self::judge`] judged [`Judgement::Red`]: its
    /// exact entry's, else its family's.
    #[must_use]
    pub fn finding(&self, key: &str) -> Option<&str> {
        self.entries.get(key).map_or_else(
            || self.family_of(key).map(|family| family.finding.as_str()),
            |entry| Some(entry.finding.as_str()),
        )
    }

    /// Whether the case `id` has a K2 entry (`ID` or `full/ID`) whose deviation is [`OTHER_K`]:
    /// the table's K for it is the principled K, which record mode must not overwrite.
    #[must_use]
    pub fn holds_other_k(&self, id: &str) -> bool {
        [id.to_owned(), format!("{FULL}{id}")]
            .iter()
            .filter_map(|key| self.entries.get(key))
            .any(|entry| entry.deviation == OTHER_K)
    }

    /// Judge one case. `kind` gives the kind of red ([`super::findings::Red`]'s display) of an
    /// observed signature; it is asked only where a family entry, and no exact entry, matches
    /// `id`.
    #[must_use]
    pub fn judge(
        &self,
        id: &str,
        observation: Observation<'_>,
        kind: impl FnOnce(&str) -> String,
    ) -> Judgement {
        let Some(entry) = self.entries.get(id) else {
            return match (self.family_of(id), observation) {
                (_, Observation::Conforms) => Judgement::Conforms,
                (Some(family), Observation::Deviates(observed)) => {
                    let kind = kind(observed);
                    if kind == family.kind {
                        Judgement::Red
                    } else {
                        Judgement::OtherKind {
                            family: family.pattern.clone(),
                            recorded: family.kind.clone(),
                            kind,
                            observed: observed.to_owned(),
                        }
                    }
                }
                (None, Observation::Deviates(observed)) => Judgement::Unexpected {
                    observed: observed.to_owned(),
                },
            };
        };
        match observation {
            Observation::Conforms => Judgement::NowConforms,
            Observation::Deviates(observed) if entry.deviation == observed => Judgement::Red,
            Observation::Deviates(observed) => Judgement::DeviationChanged {
                recorded: entry.deviation.clone(),
                observed: observed.to_owned(),
            },
        }
    }

    /// The pending IDs whose case ([`case_of`]) is no case of `ids`, and the family globs that
    /// match no key of a case of `ids` (its ID, or `k8/ID`): an entry for a case the generator no
    /// longer produces must leave the list. [`LATTICE`] entries are no cases and are not listed.
    #[must_use]
    pub fn stale<'a>(&'a self, ids: &[&str]) -> Vec<&'a str> {
        let entries = self
            .entries
            .keys()
            .map(String::as_str)
            .filter(|id| case_of(id).is_some_and(|case| !ids.contains(&case)));
        let families = self
            .families
            .iter()
            .filter(|family| {
                !ids.iter().any(|id| {
                    family.glob.matches(id) || family.glob.matches(&format!("{ADVICE}{id}"))
                })
            })
            .map(|family| family.pattern.as_str());
        entries.chain(families).collect()
    }

    /// The family globs that a whole run of a shard reaches and that pend no red of it: a glob
    /// that matches a key of `judged` (the keys the run made a verdict on), and no key of `red`
    /// (the keys it judged red) that has no exact entry. Such a family's cases all conform now,
    /// or are no longer of its kind: narrow its glob or remove it. A run that a filter narrows
    /// cannot tell, and must not ask.
    #[must_use]
    pub fn stale_families<'a>(&'a self, judged: &[&str], red: &[&str]) -> Vec<&'a str> {
        let mut reached = vec![false; self.families.len()];
        let mut met = vec![false; self.families.len()];
        for key in judged {
            for (index, family) in self.families.iter().enumerate() {
                reached[index] |= family.glob.matches(key);
            }
        }
        for key in red.iter().filter(|key| !self.entries.contains_key(**key)) {
            if let Some(index) = self
                .families
                .iter()
                .position(|family| family.glob.matches(key))
            {
                met[index] = true;
            }
        }
        self.families
            .iter()
            .zip(reached.into_iter().zip(met))
            .filter(|(_, (reached, met))| *reached && !*met)
            .map(|(family, _)| family.pattern.as_str())
            .collect()
    }

    /// The entries a run should have judged and did not, each with its test: an entry of a test
    /// the run ran (`ran`, by [`test_of`]), whose case ([`case_of`]) the run covers for that test
    /// (`covers(test, case)`: in a run that a filter narrows, the cases it selects), and that names
    /// no case `judged` holds for that test (by test, the cases with a verdict). Such an entry's
    /// case conforms now, or is no case the generator produces: it must leave the list. A run
    /// that a filter narrows judges the entries of its cases as a whole run does, every prefix
    /// alike. [`LATTICE`] entries name no case and are not listed.
    #[must_use]
    pub fn unjudged<'a>(
        &'a self,
        ran: &BTreeSet<&str>,
        judged: &BTreeMap<&str, BTreeSet<&str>>,
        covers: impl Fn(&str, &str) -> bool,
    ) -> Vec<(&'a str, &'static str)> {
        self.entries
            .keys()
            .filter_map(|key| {
                let test = test_of(key);
                let case = case_of(key)?;
                (ran.contains(test)
                    && covers(test, case)
                    && !judged.get(test).is_some_and(|cases| cases.contains(case)))
                .then_some((key.as_str(), test))
            })
            .collect()
    }

    /// The red count per finding, for the cases `red` names.
    #[must_use]
    pub fn tally<'a>(&self, red: impl IntoIterator<Item = &'a str>) -> Tally {
        let mut tally = Tally::default();
        for id in red {
            let Some(finding) = self.finding(id) else {
                continue;
            };
            *tally.by_finding.entry(finding.to_owned()).or_default() += 1;
        }
        tally
    }
}

/// Parse one `[[family]]` table: its glob, finding and kind.
fn parse_family(table: &toml_edit::Table) -> Result<FamilyEntry, Vec<String>> {
    let mut errors = Vec::new();
    for (key, _) in table {
        if !["match", "finding", "kind"].contains(&key) {
            errors.push(format!("the unknown key {key:?}"));
        }
    }
    let mut field = |key: &str| match table.get(key).and_then(|value| value.as_str()) {
        Some(text) if !text.is_empty() => Some(text.to_owned()),
        _ => {
            errors.push(format!("{key} is not a non-empty string"));
            None
        }
    };
    let (pattern, finding, kind) = (field("match"), field("finding"), field("kind"));
    let glob = pattern.as_deref().and_then(|pattern| {
        Glob::parse(pattern)
            .map_err(|reason| errors.push(format!("match {pattern:?}: {reason}")))
            .ok()
    });
    if let Some(pattern) = &pattern {
        let first = pattern.split('/').next().unwrap_or_default();
        if first.contains(['*', '{', '}', ',', '\\']) || !pattern.contains('/') {
            errors.push(format!(
                "match {pattern:?} must start with a literal segment, which names its test"
            ));
        }
        if [FULL, LATTICE, "entry/", KEYS, CLOSURE, NATIVE, RUN, TWIN]
            .iter()
            .any(|prefix| pattern.starts_with(prefix))
        {
            errors.push(format!(
                "match {pattern:?} names {} entries, which stay exact: a family names K2 or K8 \
                 keys only",
                test_of(pattern)
            ));
        }
    }
    if let (Some(pattern), Some(kind)) = (&pattern, &kind) {
        if !FAMILY_KINDS.contains(&kind.as_str()) {
            errors.push(format!(
                "kind {kind:?} is not a diagnostic kind ({}): a red of what KRS accepts, writes or \
                 runs, and a bug, stays exact, one entry per case",
                FAMILY_KINDS.join(", ")
            ));
        } else if (kind == "k8") != (test_of(pattern) == "k8") {
            errors.push(format!(
                "kind {kind:?} is not a kind of the {} test that {pattern:?} names",
                test_of(pattern)
            ));
        }
    }
    match (pattern, glob, finding, kind) {
        (Some(pattern), Some(glob), Some(finding), Some(kind)) if errors.is_empty() => {
            Ok(FamilyEntry {
                pattern,
                glob,
                finding,
                kind,
            })
        }
        _ => Err(errors),
    }
}

/// Red counts, which size each finding.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Tally {
    /// Red cases per finding.
    pub by_finding: BTreeMap<String, usize>,
}
