//! The table-free invariants: what every refused case must satisfy, whatever its expected code.
//!
//! A refused case is reported
//! 1. with at least one error whose code is registered in `krs-diagnostic`'s registry (a
//!    refusal that only rustc or a prose message reports is red), not counting
//!    [`FORWARDED_RUSTC`], which only says that rustc reported and KRS did not;
//! 2. with its primary range, the first error's, or one of that error's labels inside the case's
//!    site;
//! 3. with exactly one error (beside rustc's parse error at a position rustc parses, below);
//! 4. with no error whose kind is another than author (an internal or environment code is never
//!    the answer to an author's mistake); the kind is the one the diagnostic was reported with,
//!    since a forwarded native code's kind depends on who wrote the sentence it names;
//! 5. without a panic, and without "internal error" in any message.
//!
//! None of them needs the expected-outcome table, so they hold before the table is reviewed.
//!
//! The site of invariant 2 is the range the table's rule names (`at`) when the table covers the
//! case, and the entry otherwise. The entry, not the spelling, is the default because the mistake
//! a cell-entry case makes can be the pairing of the cell and the spelling (`Some(x)` is legal on
//! an optional cell and a mistake on a plain one), so an error located at the whole entry still
//! names the mistake; a class narrows the site to the spelling, or widens it to the item where
//! the mistake lies outside the entry (an initializer parameter no cell reads). For a term
//! position the entry is the spelling. A label counts as the location because a diagnostic that
//! relates two places names both: `incompatible-binder` puts its primary at the binder's
//! declaration, the thing most fixes change, and labels the occurrence that needs another sort.
//!
//! **Positions rustc parses.** At a position rustc parses as Rust before any KRS macro reads it
//! ([`Case::rustc_parses`](super::Case::rustc_parses): a fn body an attribute macro takes, a
//! `const` value), a construct rustc's parser refuses (`y @ P`) is reported by rustc whatever
//! KRS does: rustc parses the item before it runs the attribute, and no token stream a macro
//! emits removes a parse error in its own input. KRS still answers, since rustc's "expected
//! expression, found `@`" does not say what the construct means. So a refusal there may carry
//! rustc's parse error beside KRS's one error: an uncoded rustc error ([`FORWARDED_RUSTC`]; rustc
//! gives its parse errors no code) inside the case's spelling, and exactly one other error, also
//! inside the spelling. The full tier's K2 judges that other error alone
//! ([`without_rustc_parse_error`]), by the invariants above and by the table's code and site. The
//! rule is the slot's, not a reading of rustc's message, and no other position has it: rustc
//! parses nothing inside a macro's own tokens (a `k::term!`, a `k::rules!` block, an attribute's
//! arguments), and there KRS answers alone. The fast tier's front parses the whole file as Rust
//! first, so it stops at the same parse error (`krs::expand::parse`) and never sees KRS's answer;
//! it leaves such a case to the full tier ([`front_stops_at_rustc_parse`]).

use std::borrow::Cow;
use std::fmt;
use std::ops::Range;

use krs_diagnostic::codes::{self, CodeKind};

use super::Placed;

/// A diagnostic's severity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Severity {
    /// An error, which refuses the case.
    Error,
    /// A warning.
    Warning,
}

/// One diagnostic a case produced, as the harness observed it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObservedDiagnostic {
    /// The severity.
    pub severity: Severity,
    /// The code: a KRS code (`krs::…`), a rustc code or lint as the harness spells it, or none.
    pub code: Option<String>,
    /// The code's kind, as the diagnostic was reported with it; `None` without a code.
    pub kind: Option<CodeKind>,
    /// The primary byte range in the rendered source, if the diagnostic is located there.
    pub range: Option<Range<usize>>,
    /// The byte ranges of its labels, its related locations, in the rendered source.
    pub labels: Vec<Range<usize>>,
    /// The message.
    pub message: String,
    /// The help lines the diagnostic shows after its message.
    pub help: Vec<String>,
}

impl ObservedDiagnostic {
    /// Whether its primary range or one of its labels lies inside `site`.
    #[must_use]
    pub fn located_inside(&self, site: &Range<usize>) -> bool {
        self.range
            .iter()
            .chain(&self.labels)
            .any(|range| site.start <= range.start && range.end <= site.end)
    }
}

/// What a case did.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Observed {
    /// Whether the stage that judged the case accepted it.
    pub accepted: bool,
    /// Every diagnostic, in the order reported.
    pub diagnostics: Vec<ObservedDiagnostic>,
    /// The panic message, if the stage panicked.
    pub panic: Option<String>,
}

impl Observed {
    /// The errors, in the order reported.
    pub fn errors(&self) -> impl Iterator<Item = &ObservedDiagnostic> {
        self.diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.severity == Severity::Error)
    }

    /// Whether the case was refused: not accepted, an error reported, or a panic.
    #[must_use]
    pub fn refused(&self) -> bool {
        !self.accepted || self.errors().next().is_some() || self.panic.is_some()
    }
}

/// One broken invariant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Violation {
    /// Invariant 1: no error carries a registered code.
    NoRegisteredCode,
    /// Invariant 2: the primary error has no range in the source.
    Unlocated,
    /// Invariant 2: the primary error lies outside the case's site.
    OutsideSite {
        /// The primary range.
        range: Range<usize>,
    },
    /// Invariant 3: the number of errors is not one.
    ErrorCount(usize),
    /// Invariant 4: an error is reported with another kind than author.
    NonAuthorCode {
        /// The code.
        code: String,
        /// Its kind.
        kind: CodeKind,
    },
    /// Invariant 5: the stage panicked.
    Panic(String),
    /// Invariant 5: a message says "internal error".
    InternalErrorText(String),
}

impl fmt::Display for Violation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoRegisteredCode => formatter.write_str("no error carries a registered code"),
            Self::Unlocated => formatter.write_str("the primary error is unlocated"),
            Self::OutsideSite { range } => write!(
                formatter,
                "the primary error at {}..{} lies outside the case's site",
                range.start, range.end
            ),
            Self::ErrorCount(count) => write!(formatter, "{count} errors, not one"),
            Self::NonAuthorCode { code, kind } => {
                write!(formatter, "the {kind:?} code {code}, not an author code")
            }
            Self::Panic(message) => write!(formatter, "a panic: {message}"),
            Self::InternalErrorText(message) => {
                write!(formatter, "an internal error: {message}")
            }
        }
    }
}

/// The registered code under which a rustc error on generated code is forwarded: it is no KRS
/// diagnosis of the mistake, so it does not satisfy invariant 1.
pub const FORWARDED_RUSTC: &str = "krs::rust-expansion::uncoded-error";

/// The observation K2 judges: `observed` itself, or, at a position rustc parses, `observed`
/// without rustc's parse error, when that error (an uncoded rustc error) and exactly one other
/// error both lie inside the case's spelling and nothing panicked (see the module documentation).
/// A deviation's signature is still taken from `observed`, so it names both.
#[must_use]
pub fn without_rustc_parse_error<'o>(
    observed: &'o Observed,
    placed: &Placed<'_>,
) -> Cow<'o, Observed> {
    if !placed.case.rustc_parses || observed.panic.is_some() {
        return Cow::Borrowed(observed);
    }
    let rustc_parse = |error: &ObservedDiagnostic| error.code.as_deref() == Some(FORWARDED_RUSTC);
    let errors = observed.errors().collect::<Vec<_>>();
    let parse = match errors.as_slice() {
        [first, second] if rustc_parse(first) && !rustc_parse(second) => *first,
        [first, second] if rustc_parse(second) && !rustc_parse(first) => *second,
        _ => return Cow::Borrowed(observed),
    };
    if !errors.iter().all(|error| in_spelling(error, placed)) {
        return Cow::Borrowed(observed);
    }
    Cow::Owned(Observed {
        accepted: observed.accepted,
        diagnostics: observed
            .diagnostics
            .iter()
            .filter(|diagnostic| !std::ptr::eq(*diagnostic, parse))
            .cloned()
            .collect(),
        panic: None,
    })
}

/// Whether the fast tier's front stopped, at a position rustc parses, at the parse error rustc
/// also reports there: one error, the whole-file front's `krs::expand::parse`, inside the case's
/// spelling. The front ran no macro, so it has not seen KRS's answer, and the full tier judges
/// the case (see the module documentation).
#[must_use]
pub fn front_stops_at_rustc_parse(observed: &Observed, placed: &Placed<'_>) -> bool {
    let errors = observed.errors().collect::<Vec<_>>();
    let [error] = errors.as_slice() else {
        return false;
    };
    placed.case.rustc_parses
        && observed.panic.is_none()
        && error.code.as_deref() == Some(codes::expand::PARSE.as_str())
        && in_spelling(error, placed)
}

/// Whether `error`'s primary range lies inside the case's spelling.
fn in_spelling(error: &ObservedDiagnostic, placed: &Placed<'_>) -> bool {
    error.range.as_ref().is_some_and(|range| {
        placed.spelling.start <= range.start && range.end <= placed.spelling.end
    })
}

/// A code's kind in KRS's registry, `None` for a code the registry does not have: the `kind`
/// that [`violations`] and [`Table::resolve`](super::table::Table::resolve) judge the real
/// registry by.
#[must_use]
pub fn registry_kind(code: &str) -> Option<CodeKind> {
    krs_diagnostic::codes::info(code).map(|info| info.code.kind())
}

/// The invariants `observed` breaks; empty when the case was accepted. `site` is the range in
/// the rendered source the primary error must lie inside, and `kind` answers a code's registered
/// kind, `None` for a code the registry does not have (invariant 1); invariant 4 reads each
/// error's own kind.
#[must_use]
pub fn violations(
    observed: &Observed,
    site: &Range<usize>,
    kind: impl Fn(&str) -> Option<CodeKind>,
) -> Vec<Violation> {
    if !observed.refused() {
        return Vec::new();
    }
    let errors = observed.errors().collect::<Vec<_>>();
    let mut violations = Vec::new();
    if !errors.iter().any(|error| {
        error
            .code
            .as_deref()
            .is_some_and(|code| code != FORWARDED_RUSTC && kind(code).is_some())
    }) {
        violations.push(Violation::NoRegisteredCode);
    }
    match errors.first() {
        Some(error) if error.located_inside(site) => {}
        Some(ObservedDiagnostic {
            range: Some(range), ..
        }) => violations.push(Violation::OutsideSite {
            range: range.clone(),
        }),
        Some(_) | None => violations.push(Violation::Unlocated),
    }
    if errors.len() != 1 {
        violations.push(Violation::ErrorCount(errors.len()));
    }
    for error in &errors {
        if let (Some(code), Some(kind)) = (&error.code, error.kind)
            && kind != CodeKind::Author
        {
            violations.push(Violation::NonAuthorCode {
                code: code.clone(),
                kind,
            });
        }
    }
    if let Some(message) = &observed.panic {
        violations.push(Violation::Panic(message.clone()));
    }
    for diagnostic in &observed.diagnostics {
        if diagnostic.message.to_lowercase().contains("internal error") {
            violations.push(Violation::InternalErrorText(diagnostic.message.clone()));
        }
    }
    violations
}

/// The signature of what a case did, as `pending.toml` records a deviation: `accepted`, or
/// each error as `CODE @ REGION` (`uncoded` for an error without a code, the region the
/// narrowest of the case's ranges that holds the error, `unlocated` without a range), joined by
/// `; `, then `panic` if the stage panicked. Warnings are not part of it.
#[must_use]
pub fn signature(observed: &Observed, placed: &Placed<'_>) -> String {
    let mut parts = observed
        .errors()
        .map(|error| {
            format!(
                "{} @ {}",
                error.code.as_deref().unwrap_or("uncoded"),
                error
                    .range
                    .as_ref()
                    .map_or("unlocated", |range| placed.region(range))
            )
        })
        .collect::<Vec<_>>();
    if observed.panic.is_some() {
        parts.push("panic".to_owned());
    }
    if parts.is_empty() {
        if observed.accepted {
            "accepted".to_owned()
        } else {
            "refused without an error".to_owned()
        }
    } else {
        parts.join("; ")
    }
}
