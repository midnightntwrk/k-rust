//! The findings registry, `krs/tests/class-matrix/findings.toml`: who owns each finding the red
//! list names, and what kind of fix it needs; and the kind of each red, computed from its entry.
//!
//! A red that has no owner stays: nothing makes anyone fix it, and a red list that never shrinks
//! reads as "known". So every finding `pending.toml` names is registered, one table per finding,
//! sorted by name:
//!
//! ```toml
//! ["NT-2-7"]
//! owner = "NT-28"
//! kind = "bug"
//! what = "`_` where no production field gives it a sort is refused"
//! by_test = { k3 = "NT-30" }
//! ```
//!
//! - `owner` ([`Owner`]): a ticket (`NT-28`), a step (`S1` to `S6`), or `kept: REF`, a limit
//!   kept by the decision `REF`. A step owns findings, not entries: an entry has no `step`, so
//!   the two cannot disagree.
//! - `kind` ([`FindingKind`]): what fixing it changes.
//! - `what`: one line saying what is wrong.
//! - `by_test`: the owner of the finding's entries of one test ([`test_of`]), where another owner
//!   owns them, or where one test's owner is stated explicitly.
//! - `risk`: on a finding that holds an under-refusal, and only there, what the K KRS writes for
//!   the spelling means and how that differs from what the spelling says.
//!
//! **The kind of a red** ([`Red`]) is computed, never stated: a K2 entry's deviation is the
//! signature of what the case did ([`super::invariants::signature`]), so against the table's
//! expectation it tells an under-refusal (`accepted`, where the table refuses), an over-refusal
//! (refused, where it accepts), other K (accepted, where it accepts, with other K) and a
//! diagnostic (refused, where it refuses, but not as the class says); any other test's entry is
//! of that test's kind. A red is also *internal* where its deviation names a code the registry
//! files as [`CodeKind::Internal`]: an authored source that reaches one has found a KRS bug, by
//! K2's own rule, whatever the table says. And it *panicked* where its deviation records a panic
//! ([`panicked`]): K2's signature writes a stage's panic as its part `panic`, and the other tests
//! write `panic: MESSAGE`, or `krs expand panicked: MESSAGE`. A panic is a KRS bug by the same
//! rule. K2's other sign of a bug, "internal error" in a message's text, is not in the signature
//! `pending.toml` records, so it cannot be computed from the entry; K2 fails on it as a violation.
//!
//! **What a finding's kind may hold** ([`Red::admits`]). An under-refusal is the red that matters
//! most for soundness: KRS writes K for a spelling the language gives no meaning, and a user who
//! writes it gets that K silently. A red with an internal code, and a red that panicked, is a
//! broken contract inside KRS. All three are bugs, and may sit only under a `bug` finding, whatever
//! test met them, so none can be parked as a message to improve. A red of what KRS wrote or ran
//! (an over-refusal, other K, K1, K3, K4, K6, K7, the twin check) is not fixed by changing a
//! message, so it never sits under a `diagnostic` finding; a diagnostic red, a K5 red and a K8 red
//! (what a refusal says) may sit under any. A K2 red of a case the table does not decide is the
//! generator's to resolve (decide the case in `expected.toml`), so it sits only under a
//! `generator` finding: under another kind, an `accepted` entry would hide what may be an
//! under-refusal once the table decides the case.
//!
//! [`audit`] fails, with the fix in each message, where
//! - a pending entry names a finding the registry does not have;
//! - a registered finding has no entry left (it is done: remove it), or a `by_test` owner has no
//!   entry of its test left;
//! - a red's kind is not one its finding's kind admits;
//! - a finding holds an under-refusal and states no `risk`, or states one and holds none.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use krs_diagnostic::codes::CodeKind;
use toml_edit::DocumentMut;

use super::pending::{Pending, PendingEntry, UNASSIGNED, test_of};
use super::table::Expected;

/// The registry's file name, beside `pending.toml`.
pub const FINDINGS_FILE: &str = "findings.toml";

/// The tests a pending key can belong to ([`test_of`]), which `by_test` names.
pub const TESTS: &[&str] = &["k1", "k2", "k3", "k4", "k5", "k6", "k7", "twin", "k8"];

/// Who owns a finding.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Owner {
    /// A ticket, `NT-28`.
    Ticket(String),
    /// A step of the roadmap, `S1` to `S6`.
    Step(String),
    /// A limit kept by a decision, written `kept: REF`.
    Kept(String),
}

impl Owner {
    /// Parse an owner: `NT-<number>`, `S1` to `S6`, or `kept: REF`.
    ///
    /// # Errors
    ///
    /// Returns why the text names no owner.
    pub fn parse(text: &str) -> Result<Self, String> {
        if let Some(reference) = text.strip_prefix("kept: ") {
            return if reference.trim().is_empty() {
                Err("`kept: ` names no decision".to_owned())
            } else {
                Ok(Self::Kept(reference.trim().to_owned()))
            };
        }
        if ["S1", "S2", "S3", "S4", "S5", "S6"].contains(&text) {
            return Ok(Self::Step(text.to_owned()));
        }
        let ticket = text
            .strip_prefix("NT-")
            .is_some_and(|number| !number.is_empty() && number.bytes().all(|b| b.is_ascii_digit()));
        if ticket {
            Ok(Self::Ticket(text.to_owned()))
        } else {
            Err(format!(
                "{text:?} is no owner: a ticket `NT-<number>`, a step `S1` to `S6`, or `kept: REF`"
            ))
        }
    }
}

impl fmt::Display for Owner {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ticket(name) | Self::Step(name) => formatter.write_str(name),
            Self::Kept(reference) => write!(formatter, "kept: {reference}"),
        }
    }
}

/// What fixing a finding changes.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FindingKind {
    /// KRS does what the language does not mean: it accepts what has no meaning, refuses what
    /// does, writes other K, or breaks an internal contract.
    Bug,
    /// The table admits what KRS does not do yet.
    Feature,
    /// The refusal is right; its code, site or advice is not the mistake's.
    Diagnostic,
    /// The test's own data or harness is wrong.
    Generator,
}

impl FindingKind {
    const ALL: [Self; 4] = [Self::Bug, Self::Feature, Self::Diagnostic, Self::Generator];

    /// The kind's name in the registry.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Bug => "bug",
            Self::Feature => "feature",
            Self::Diagnostic => "diagnostic",
            Self::Generator => "generator",
        }
    }
}

impl fmt::Display for FindingKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.name())
    }
}

/// One registered finding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding {
    /// Who owns its entries, but those of the tests `by_test` names.
    pub owner: Owner,
    /// What fixing it changes.
    pub kind: FindingKind,
    /// One line saying what is wrong.
    pub what: String,
    /// What the K KRS writes means, on a finding that holds an under-refusal.
    pub risk: Option<String>,
    /// The owners of its entries of one test, where another than `owner` owns them.
    pub by_test: BTreeMap<String, Owner>,
}

/// The parsed registry.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Findings {
    /// The findings by name.
    pub findings: BTreeMap<String, Finding>,
}

impl Findings {
    /// Parse the registry's text.
    ///
    /// # Errors
    ///
    /// Returns every table that does not follow the schema, and every name out of order.
    pub fn parse(text: &str) -> Result<Self, Vec<String>> {
        let document = text
            .parse::<DocumentMut>()
            .map_err(|error| vec![format!("{FINDINGS_FILE}: {error}")])?;
        let mut errors = Vec::new();
        let mut findings = BTreeMap::new();
        let mut previous: Option<&str> = None;
        for (name, item) in document.iter() {
            if previous.is_some_and(|previous| previous >= name) {
                errors.push(format!(
                    "{name:?} follows {:?}: keep the findings sorted by name",
                    previous.unwrap_or_default()
                ));
            }
            previous = Some(name);
            if name == UNASSIGNED {
                errors.push(format!(
                    "{name:?} is the placeholder of a deviation no finding owns: name the finding"
                ));
            }
            match parse_finding(name, item) {
                Ok(finding) => {
                    findings.insert(name.to_owned(), finding);
                }
                Err(mut more) => errors.append(&mut more),
            }
        }
        if errors.is_empty() {
            Ok(Self { findings })
        } else {
            Err(errors)
        }
    }

    /// The owner of the pending entry `key` under `finding`: its test's `by_test` owner, or the
    /// finding's; `None` for a finding the registry does not have.
    #[must_use]
    pub fn owner(&self, finding: &str, key: &str) -> Option<&Owner> {
        let finding = self.findings.get(finding)?;
        Some(finding.by_test.get(test_of(key)).unwrap_or(&finding.owner))
    }

    /// The owner of the pending entry `key` under `finding` as a summary names it:
    /// [`Self::owner`], or `unregistered`.
    #[must_use]
    pub fn owner_name(&self, finding: &str, key: &str) -> String {
        self.owner(finding, key)
            .map_or_else(|| "unregistered".to_owned(), ToString::to_string)
    }
}

fn parse_finding(name: &str, item: &toml_edit::Item) -> Result<Finding, Vec<String>> {
    let Some(table) = item.as_table() else {
        return Err(vec![format!("{name:?} is not a table")]);
    };
    let mut errors = Vec::new();
    for (key, _) in table {
        if !["owner", "kind", "what", "risk", "by_test"].contains(&key) {
            errors.push(format!("{name:?} has the unknown key {key:?}"));
        }
    }
    let text = |key: &str, errors: &mut Vec<String>| match table.get(key) {
        None => None,
        Some(value) => {
            let text = value.as_str().map(str::to_owned);
            if text.as_deref().is_none_or(|text| text.trim().is_empty()) {
                errors.push(format!("{name:?}.{key} is not a non-empty string"));
            }
            text
        }
    };
    let owner = text("owner", &mut errors).and_then(|owner| {
        Owner::parse(&owner)
            .map_err(|reason| errors.push(format!("{name:?}.owner: {reason}")))
            .ok()
    });
    let kind = text("kind", &mut errors).and_then(|kind| {
        let parsed = FindingKind::ALL
            .into_iter()
            .find(|known| known.name() == kind);
        if parsed.is_none() {
            errors.push(format!(
                "{name:?}.kind is {kind:?}, not one of bug, feature, diagnostic, generator"
            ));
        }
        parsed
    });
    let what = text("what", &mut errors);
    let risk = text("risk", &mut errors);
    let mut by_test = BTreeMap::new();
    if let Some(value) = table.get("by_test") {
        match value.as_table_like() {
            None => errors.push(format!("{name:?}.by_test is not a table of tests")),
            Some(tests) => {
                for (test, owner) in tests.iter() {
                    if !TESTS.contains(&test) {
                        errors.push(format!(
                            "{name:?}.by_test names {test:?}, not one of {}",
                            TESTS.join(", ")
                        ));
                    }
                    match owner.as_str().map(Owner::parse) {
                        Some(Ok(owner)) => {
                            by_test.insert(test.to_owned(), owner);
                        }
                        Some(Err(reason)) => {
                            errors.push(format!("{name:?}.by_test.{test}: {reason}"));
                        }
                        None => errors.push(format!("{name:?}.by_test.{test} is not a string")),
                    }
                }
            }
        }
    }
    match (owner, kind, what) {
        (Some(owner), Some(kind), Some(what)) if errors.is_empty() => Ok(Finding {
            owner,
            kind,
            what,
            risk,
            by_test,
        }),
        (owner, kind, what) => {
            if owner.is_none() || kind.is_none() || what.is_none() {
                errors.push(format!("{name:?} needs an owner, a kind and a what"));
            }
            Err(errors)
        }
    }
}

/// What a red is, by the test that judged it and, for K2, the table's expectation.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum RedKind {
    /// K2: accepted, where the table refuses.
    UnderRefusal,
    /// K2: refused, where the table accepts.
    OverRefusal,
    /// K2: accepted, where the table accepts, with other K than it records.
    OtherK,
    /// K2: refused, where the table refuses, but not as the class says (code, site, count).
    Diagnostic,
    /// K2: a case the table does not decide, which is a table error of its own.
    Uncovered,
    /// K1, after lowering.
    K1,
    /// K3, the source `krs expand` prints.
    K3,
    /// K4, a disagreement of sort judges.
    K4,
    /// K5, a broken entry point's diagnostics.
    K5,
    /// K6, `krs check` on the definition KRS wrote.
    K6,
    /// K7, the case's run.
    K7,
    /// K7's twin check.
    Twin,
    /// K8, the advice a refusal gives.
    K8,
}

impl RedKind {
    /// The kind's name, as the harness prints it.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::UnderRefusal => "under-refusal",
            Self::OverRefusal => "over-refusal",
            Self::OtherK => "other-k",
            Self::Diagnostic => "diagnostic",
            Self::Uncovered => "uncovered",
            Self::K1 => "k1",
            Self::K3 => "k3",
            Self::K4 => "k4",
            Self::K5 => "k5",
            Self::K6 => "k6",
            Self::K7 => "k7",
            Self::Twin => "twin",
            Self::K8 => "k8",
        }
    }
}

/// The computed kind of one red: its [`RedKind`], whether its deviation names an internal code,
/// and whether it records a panic.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Red {
    /// What the red is.
    pub kind: RedKind,
    /// Whether its deviation names a code the registry files as internal.
    pub internal: bool,
    /// Whether its deviation records a panic ([`panicked`]).
    pub panicked: bool,
}

impl Red {
    /// The kind of the pending entry `key` whose deviation is `deviation`; `expected` is what the
    /// table expects of the entry's case (read for a K2 entry only), and `code_kind` a code's
    /// registered kind.
    #[must_use]
    pub fn of(
        key: &str,
        deviation: &str,
        expected: Option<&Expected<'_>>,
        code_kind: impl Fn(&str) -> Option<CodeKind>,
    ) -> Self {
        let accepted = deviation == "accepted";
        let kind = match test_of(key) {
            "k1" => RedKind::K1,
            "k3" => RedKind::K3,
            "k4" => RedKind::K4,
            "k5" => RedKind::K5,
            "k6" => RedKind::K6,
            "k7" => RedKind::K7,
            "twin" => RedKind::Twin,
            "k8" => RedKind::K8,
            _ => match expected {
                None => RedKind::Uncovered,
                Some(Expected::Refuse { .. }) if accepted => RedKind::UnderRefusal,
                Some(Expected::Refuse { .. }) => RedKind::Diagnostic,
                Some(Expected::Accept(_)) if accepted => RedKind::OtherK,
                Some(Expected::Accept(_)) => RedKind::OverRefusal,
            },
        };
        let internal = codes(deviation).any(|code| code_kind(code) == Some(CodeKind::Internal));
        Self {
            kind,
            internal,
            panicked: panicked(deviation),
        }
    }

    /// Whether the red is a KRS bug whatever its test: an under-refusal, an internal code or a
    /// panic.
    const fn is_bug(self) -> bool {
        self.internal || self.panicked || matches!(self.kind, RedKind::UnderRefusal)
    }

    /// Whether a finding of `kind` may hold this red.
    #[must_use]
    pub fn admits(self, kind: FindingKind) -> bool {
        match self.kind {
            _ if self.is_bug() => kind == FindingKind::Bug,
            RedKind::Uncovered => kind == FindingKind::Generator,
            RedKind::Diagnostic | RedKind::K5 | RedKind::K8 => true,
            RedKind::OverRefusal
            | RedKind::OtherK
            | RedKind::K1
            | RedKind::K3
            | RedKind::K4
            | RedKind::K6
            | RedKind::K7
            | RedKind::Twin
            | RedKind::UnderRefusal => kind != FindingKind::Diagnostic,
        }
    }

    /// Why a finding's kind does not admit this red.
    fn reason(self) -> &'static str {
        if self.is_bug() {
            "an under-refusal (KRS writes K for a spelling with no meaning), an internal code and \
             a panic (a contract inside KRS broken) are KRS bugs: register the red under a `bug` \
             finding"
        } else if self.kind == RedKind::Uncovered {
            "the table does not decide the case: decide it in expected.toml, or register the red \
             under a `generator` finding until then"
        } else {
            "a red of what KRS wrote or ran is not fixed by a message: register it under a `bug`, \
             `feature` or `generator` finding"
        }
    }
}

impl fmt::Display for Red {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.kind.name())?;
        if self.internal {
            formatter.write_str("+internal")?;
        }
        if self.panicked {
            formatter.write_str("+panic")?;
        }
        Ok(())
    }
}

/// Whether a deviation records a panic: a part `panic` of K2's signature, or the word `panic` or
/// `panicked` anywhere in another test's deviation (`panic: MESSAGE`, a counter-witness's
/// `panic: MESSAGE` after its program, `krs expand panicked: MESSAGE`, K6's `a check worker
/// panicked`). No code and no deviation the harness writes holds either word otherwise.
#[must_use]
pub fn panicked(deviation: &str) -> bool {
    deviation
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '-' || c == '_'))
        .any(|word| matches!(word, "panic" | "panicked"))
}

/// The KRS codes (`krs::stage::name`) a deviation names.
pub fn codes(text: &str) -> impl Iterator<Item = &str> {
    text.match_indices("krs::").map(move |(start, _)| {
        let rest = &text[start..];
        let end = rest
            .find(|c: char| !(c.is_ascii_alphanumeric() || matches!(c, '-' | '_' | ':')))
            .unwrap_or(rest.len());
        rest[..end].trim_end_matches(':')
    })
}

/// The registry's failures against the red list, each with its fix; `red` computes an entry's
/// kind ([`Red::of`]).
#[must_use]
pub fn audit(
    findings: &Findings,
    pending: &Pending,
    red: impl Fn(&str, &PendingEntry) -> Red,
) -> Vec<String> {
    let mut errors = Vec::new();
    let mut tests = BTreeMap::<&str, BTreeSet<&str>>::new();
    let mut under = BTreeSet::new();
    for (key, entry) in &pending.entries {
        let Some(finding) = findings.findings.get(&entry.finding) else {
            errors.push(format!(
                "{key}: its finding {:?} is not in {FINDINGS_FILE}: register it with its owner, \
                 kind and what",
                entry.finding
            ));
            continue;
        };
        tests
            .entry(entry.finding.as_str())
            .or_default()
            .insert(test_of(key));
        let red = red(key, entry);
        if red.kind == RedKind::UnderRefusal {
            under.insert(entry.finding.as_str());
        }
        if !red.admits(finding.kind) {
            errors.push(format!(
                "{key}: a red of kind {red} under {}, a {} finding: {}",
                entry.finding,
                finding.kind,
                red.reason()
            ));
        }
    }
    for (name, finding) in &findings.findings {
        let Some(held) = tests.get(name.as_str()) else {
            errors.push(format!(
                "{name}: no pending entry is left under it: it is done, remove it from {FINDINGS_FILE}"
            ));
            continue;
        };
        for test in finding.by_test.keys() {
            if !held.contains(test.as_str()) {
                errors.push(format!(
                    "{name}: by_test gives its {test} entries an owner, but none is left: remove \
                     the {test} owner"
                ));
            }
        }
        if held.iter().all(|test| finding.by_test.contains_key(*test)) {
            let owners = held
                .iter()
                .filter_map(|test| finding.by_test.get(*test).map(ToString::to_string))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            errors.push(match owners.as_slice() {
                [owner] => format!(
                    "{name}: every entry left is owned through by_test: make {owner} the \
                     finding's owner and drop by_test"
                ),
                owners => format!(
                    "{name}: every entry left is owned through by_test, by {}: make one of them \
                     the finding's owner and keep by_test for the others",
                    owners.join(", ")
                ),
            });
        }
        match (finding.risk.is_some(), under.contains(name.as_str())) {
            (false, true) => errors.push(format!(
                "{name} holds an under-refusal: state its risk, what the K KRS writes means and \
                 how it differs from what the spelling says"
            )),
            (true, false) => errors.push(format!(
                "{name} states a risk but holds no under-refusal: remove the risk"
            )),
            _ => {}
        }
    }
    errors
}

/// The reds of one run, counted by kind, by owner, and by kind and finding.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Summary {
    /// Reds per kind ([`Red`]'s display).
    pub by_kind: BTreeMap<String, usize>,
    /// Reds per owner, `unregistered` for a finding the registry does not have.
    pub by_owner: BTreeMap<String, usize>,
    /// Reds per kind and finding, with the finding's owner.
    pub by_kind_and_finding: BTreeMap<(String, String), (String, usize)>,
}

impl Summary {
    /// Count a red of the kind `red` under `finding`, whose owner for the red is `owner`
    /// ([`Findings::owner_name`]).
    pub fn add(&mut self, red: Red, finding: &str, owner: &str) {
        *self.by_kind.entry(red.to_string()).or_default() += 1;
        *self.by_owner.entry(owner.to_owned()).or_default() += 1;
        self.by_kind_and_finding
            .entry((red.to_string(), finding.to_owned()))
            .or_insert_with(|| (owner.to_owned(), 0))
            .1 += 1;
    }

    /// One row per kind and finding: the kind, the finding, its owner and the count.
    pub fn rows(&self) -> impl Iterator<Item = (&str, &str, &str, usize)> {
        self.by_kind_and_finding
            .iter()
            .map(|((kind, finding), (owner, count))| {
                (kind.as_str(), finding.as_str(), owner.as_str(), *count)
            })
    }
}

impl fmt::Display for Summary {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "by kind {:?}; by owner {:?}; by kind and finding: ",
            self.by_kind, self.by_owner
        )?;
        let mut kind = None;
        for ((red, finding), (_, count)) in &self.by_kind_and_finding {
            if kind != Some(red) {
                if kind.is_some() {
                    formatter.write_str("; ")?;
                }
                write!(formatter, "{red}:")?;
                kind = Some(red);
            }
            write!(formatter, " {finding} {count}")?;
        }
        Ok(())
    }
}
