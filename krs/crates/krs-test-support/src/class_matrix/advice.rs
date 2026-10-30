//! K8's advice check (axis B): a refusal whose message proposes a rewrite names a case that
//! writes it, which must be accepted.
//!
//! **What advises a rewrite, mechanically.** A diagnostic advises a rewrite when it proposes a
//! form to write in place of the refused one:
//!
//! - its message holds, after an advice verb in the imperative ([`VERBS`]: `write`, `mark`,
//!   `declare`, `bind`, `place`, ..), at the start of a clause, a code span in the same clause
//!   ("..; write `map![k -> v, ..m]`", "mark the production `#[k::alias]`"), or says how the
//!   refused construct *is written* or how a pattern *writes* it ("`counter` is written
//!   `Some(..)`", "a pattern writes `int::add` as the call `int::add(..)`");
//! - or one of its help lines does, or shows a form at its end after a colon ("a rule for any
//!   term of a sort is a `for Sort` clause, ..: `k::rules! { for KItem; .. }`").
//!
//! A class of `expected.toml` whose refusal advises carries `advice = "<case ID>"`, a generated
//! case that writes the advised form; the table's resolution requires that case to be one it
//! accepts. The full tier runs [`advised`] on every case a class refuses as the table expects,
//! and reports one whose message advises while its class names no advised case; it also judges
//! each advised case: accepted, passed by K6, and run by K7 where the case has a driver.

use super::invariants::ObservedDiagnostic;

/// The verbs whose imperative proposes a form.
pub const VERBS: [&str; 15] = [
    "write", "mark", "declare", "bind", "place", "rename", "restrict", "narrow", "qualify", "give",
    "add", "drop", "return", "spell", "wrap",
];

/// A message's pieces: prose and code spans, in order.
enum Piece<'a> {
    Prose(&'a str),
    Code(&'a str),
}

fn pieces(text: &str) -> Vec<Piece<'_>> {
    let mut pieces = Vec::new();
    for (index, part) in text.split('`').enumerate() {
        pieces.push(if index % 2 == 0 {
            Piece::Prose(part)
        } else {
            Piece::Code(part)
        });
    }
    pieces
}

/// Whether the prose before `position` in `prose` ends a clause: nothing, or `;`, `:`, `,`, `.`,
/// `(`, an `or`, an `and`, a `then`, an `instead` or a `so`.
fn starts_clause(prose: &str, position: usize) -> bool {
    let before = prose[..position].trim_end();
    before.is_empty()
        || before.ends_with([';', ':', ',', '.', '('])
        || [" or", " and", " then", " instead", " so"]
            .iter()
            .any(|word| before.ends_with(word))
}

/// The form a message advises writing, if it advises one ([module docs](self)).
#[must_use]
pub fn advised_in_message(message: &str) -> Option<&str> {
    let pieces = pieces(message);
    for (at, piece) in pieces.iter().enumerate() {
        let Piece::Prose(prose) = piece else {
            continue;
        };
        let mut offset = 0;
        for word in prose.split(|character: char| !character.is_ascii_alphabetic()) {
            let start = offset;
            offset += word.len() + 1;
            if word.is_empty() {
                continue;
            }
            // A word right after a code span continues that span's clause.
            let clause_start =
                starts_clause(prose, start) && !(at > 0 && prose[..start].trim().is_empty());
            let imperative = VERBS.contains(&word) && clause_start;
            let descriptive = (word == "written" && prose[..start].trim_end().ends_with(" is"))
                || (word == "writes" && prose[..start].trim_end().ends_with("pattern"));
            if !(imperative || descriptive) {
                continue;
            }
            // The clause goes on to its first `;` or `. ` in the prose; a code span in it is
            // the form.
            if prose[start..].contains([';']) || prose[start..].contains(". ") {
                continue;
            }
            if let Some(Piece::Code(code)) = pieces.get(at + 1) {
                return Some(code);
            }
        }
    }
    None
}

/// The form a help line advises writing, if it advises one: as a message does, or shown at its
/// end after a colon ("..: `k::rules! { for KItem; .. }`").
#[must_use]
pub fn advised_in_help(help: &str) -> Option<&str> {
    advised_in_message(help).or_else(|| {
        let shown = help.trim_end().strip_suffix('`')?;
        let start = shown.rfind('`')?;
        shown[..start]
            .trim_end()
            .ends_with(':')
            .then(|| &shown[start + 1..])
    })
}

/// The form `diagnostic` advises writing, if it advises one: in its message or a help line.
#[must_use]
pub fn advised(diagnostic: &ObservedDiagnostic) -> Option<String> {
    advised_in_message(&diagnostic.message)
        .or_else(|| {
            diagnostic
                .help
                .iter()
                .find_map(|help| advised_in_help(help))
        })
        .map(str::to_owned)
}
