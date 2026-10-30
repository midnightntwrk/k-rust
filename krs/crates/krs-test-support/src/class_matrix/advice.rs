//! K8's advice check (axis B): what a refusal advises writing instead, and the case that writes it.
//!
//! **The reviewed field.** Every refusal class of `expected.toml` carries `advice`: `"none"` when
//! its refusal advises no rewrite, or the case that writes the form it advises, an ID or a
//! template whose `{form}` is the refused case's form (its ID's second segment), so that the
//! advice on each form is the advised form on that form (`attrs/{form}/priority = 20`). Each
//! class's messages were read once to write it; the table checks that a plain ID is a case it
//! accepts.
//!
//! **The detector** ([`advised`]) reads, mechanically, the form a diagnostic proposes writing. It
//! is the backstop of the reviewed field: a class marked `none` whose refusal it reads as advice
//! is a K8 deviation. Where it reads a form in a class's refusal, K8 also checks that the advised
//! case writes it: the code span appears in the case's source, or, for advice to drop or remove
//! it, does not. Advice in prose only ("rename the clause") is the reviewed field's alone.
//!
//! A diagnostic proposes a form when its message, or one of its help lines, holds:
//! - an advice verb in the imperative ([`VERBS`], read case-insensitively) at the start of a
//!   clause, and a code span in the same clause, before any `instead of`, `rather than` or `not`
//!   that turns the clause to what not to write ("..; write `map![k -> v, ..m]`", "Mark the
//!   production `#[k::alias]`"); after `replace` the span after `with` or `by`;
//! - the form a construct *is written* or *is written as*, right after the verb ("`counter` is
//!   written `Some(..)`"), or how something *writes* a thing *as* a form ("a pattern writes
//!   `int::add` as the call `int::add(..)`");
//! - (a help line) a form shown at its end after a colon ("..: `k::rules! { for KItem; .. }`").
//!
//! A clause ends at a `;`, a `.` that ends a sentence, or the text's end.

use super::invariants::ObservedDiagnostic;

/// The verbs whose imperative proposes a form.
pub const VERBS: [&str; 22] = [
    "write", "mark", "declare", "bind", "place", "rename", "restrict", "narrow", "qualify", "give",
    "add", "drop", "remove", "return", "spell", "wrap", "use", "replace", "move", "state", "split",
    "put",
];

/// The verbs whose advice is to take the form away.
const REMOVING: [&str; 2] = ["drop", "remove"];

/// The words that, at a clause's end, start the next clause.
const CONNECTIVES: [&str; 6] = ["or", "and", "then", "instead", "so", "otherwise"];

/// What a diagnostic advises: a form to write, or to take away.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Advice {
    /// The code span the advice proposes.
    pub form: String,
    /// Whether the advice is to drop or remove the form, rather than to write it.
    pub removes: bool,
}

impl Advice {
    fn writes(form: &str) -> Self {
        Self {
            form: form.to_owned(),
            removes: false,
        }
    }
}

/// A message's pieces: prose and code spans, in order.
#[derive(Clone, Copy)]
enum Piece<'a> {
    Prose(&'a str),
    Code(&'a str),
}

fn pieces(text: &str) -> Vec<Piece<'_>> {
    text.split('`')
        .enumerate()
        .map(|(index, part)| {
            if index % 2 == 0 {
                Piece::Prose(part)
            } else {
                Piece::Code(part)
            }
        })
        .collect()
}

/// The words of `prose`, each with its byte offset: runs of alphabetic characters.
fn words(prose: &str) -> Vec<(usize, &str)> {
    let mut words = Vec::new();
    let mut start = None;
    for (at, character) in prose.char_indices() {
        match (character.is_alphabetic(), start) {
            (true, None) => start = Some(at),
            (false, Some(from)) => {
                words.push((from, &prose[from..at]));
                start = None;
            }
            _ => {}
        }
    }
    if let Some(from) = start {
        words.push((from, &prose[from..]));
    }
    words
}

/// Whether `before`, the prose before a word, ends a clause: it is empty at the text's start, or
/// ends with `;`, `:`, `,`, `.`, `(`, a dash, or a connective.
fn ends_clause(before: &str, at_text_start: bool) -> bool {
    let before = before.trim_end();
    if before.is_empty() {
        return at_text_start;
    }
    before.ends_with([';', ':', ',', '.', '(', '—', '–', '-'])
        || CONNECTIVES.iter().any(|word| {
            before
                .strip_suffix(word)
                .is_some_and(|rest| rest.is_empty() || rest.ends_with(|c: char| !c.is_alphabetic()))
        })
}

/// Where a clause ends in `prose`: its first `;`, or a `.` followed by a space or the end.
fn clause_end(prose: &str) -> Option<usize> {
    let semicolon = prose.find(';');
    let full_stop = prose
        .match_indices('.')
        .find(|(at, _)| {
            prose[at + 1..]
                .chars()
                .next()
                .is_none_or(char::is_whitespace)
        })
        .map(|(at, _)| at);
    match (semicolon, full_stop) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}

/// Whether `prose`, between an imperative and a span, turns the clause away from the span as
/// the form to write: to what not to write (`instead of`, `rather than`, `not`), or to a clause
/// of its own (`where`, `when`, `if`, `which`, `whose`) that the span belongs to ("use them
/// where a field declares `List`").
fn negates(prose: &str) -> bool {
    let lower = prose.to_lowercase();
    lower.contains("instead of")
        || lower.contains("rather than")
        || words(&lower)
            .iter()
            .any(|(_, word)| matches!(*word, "not" | "where" | "when" | "if" | "which" | "whose"))
}

/// Where the clause that goes on through `prose` ends in it: at a clause's end, or where another
/// imperative starts a clause ("give it one or drop \`x\`": `drop` starts its own).
fn clause_cut(prose: &str) -> Option<usize> {
    let verb = words(prose)
        .into_iter()
        .find(|(start, word)| {
            VERBS.contains(&word.to_lowercase().as_str()) && ends_clause(&prose[..*start], false)
        })
        .map(|(start, _)| start);
    match (clause_end(prose), verb) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}

/// The code spans of the clause that goes on from `from`, the prose after a verb in piece `at`,
/// each with the prose of the clause before it.
fn clause<'a>(pieces: &[Piece<'a>], at: usize, from: &'a str) -> Vec<(String, &'a str)> {
    let mut spans = Vec::new();
    let mut before = String::new();
    let mut first = Some(from);
    for piece in &pieces[at..] {
        match (*piece, first.take()) {
            (_, Some(prose)) | (Piece::Prose(prose), None) => {
                if clause_cut(prose).is_some() {
                    break;
                }
                before.push_str(prose);
            }
            (Piece::Code(code), None) => {
                spans.push((before.clone(), code));
                before.push('`');
                before.push_str(code);
                before.push('`');
            }
        }
    }
    spans
}

/// What a text advises: its advice, in groups of alternatives. Each imperative's advice is a
/// form, or `None` for advice in prose alone (an imperative whose clause holds no span, "give it
/// one"); an imperative after `or` is an alternative of the one before it, any other starts a
/// group of its own, which advice must also follow ("write `Some(..)` and add `initial`").
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Reading {
    /// The groups of alternatives.
    pub groups: Vec<Vec<Option<Advice>>>,
}

impl Reading {
    /// The forms proposed, in order.
    pub fn forms(&self) -> impl Iterator<Item = &Advice> {
        self.groups.iter().flatten().flatten()
    }

    fn push(&mut self, advice: Option<Advice>, alternative: bool) {
        match self.groups.last_mut() {
            Some(group) if alternative => group.push(advice),
            _ => self.groups.push(vec![advice]),
        }
    }
}

/// What a message advises ([module docs](self)).
#[must_use]
pub fn read_message(message: &str) -> Reading {
    let pieces = pieces(message);
    let mut reading = Reading::default();
    for (at, piece) in pieces.iter().enumerate() {
        let Piece::Prose(prose) = *piece else {
            continue;
        };
        for (start, word) in words(prose) {
            let lower = word.to_lowercase();
            let rest = &prose[start + word.len()..];
            if VERBS.contains(&lower.as_str()) && ends_clause(&prose[..start], at == 0) {
                let alternative =
                    prose[..start]
                        .trim_end()
                        .strip_suffix("or")
                        .is_some_and(|rest| {
                            rest.is_empty() || rest.ends_with(|c: char| !c.is_alphabetic())
                        });
                let spans = clause(&pieces, at, rest);
                let found = if lower == "replace" {
                    spans.iter().find(|(before, _)| {
                        words(before)
                            .iter()
                            .any(|(_, word)| matches!(*word, "with" | "by"))
                    })
                } else {
                    spans.first()
                };
                match found {
                    Some((before, form)) if !negates(before) => reading.push(
                        Some(Advice {
                            form: (*form).to_owned(),
                            removes: REMOVING.contains(&lower.as_str()),
                        }),
                        alternative,
                    ),
                    _ => reading.push(None, alternative),
                }
                continue;
            }
            let after_is = prose[..start].trim_end().to_lowercase().ends_with(" is")
                || prose[..start].trim_end().eq_ignore_ascii_case("is");
            if lower == "written" && after_is {
                // The form right after the verb, or after `as`.
                let between = rest.trim();
                if (between.is_empty() || between.eq_ignore_ascii_case("as"))
                    && let Some(Piece::Code(form)) = pieces.get(at + 1)
                {
                    reading.push(Some(Advice::writes(form)), false);
                }
                continue;
            }
            if lower == "writes" {
                // `.. writes A as B`: the first span after `as` in the clause.
                if let Some((_, form)) = clause(&pieces, at, rest)
                    .into_iter()
                    .find(|(before, _)| words(before).iter().any(|(_, word)| *word == "as"))
                {
                    reading.push(Some(Advice::writes(form)), false);
                }
            }
        }
    }
    reading
}

/// The first form a message advises writing, if it advises one ([module docs](self)).
#[must_use]
pub fn advised_in_message(message: &str) -> Option<Advice> {
    read_message(message).forms().next().cloned()
}

/// What a help line advises: as a message does, or a form shown at its end after a colon
/// ("..: `k::rules! { for KItem; .. }`").
#[must_use]
pub fn read_help(help: &str) -> Reading {
    let mut reading = read_message(help);
    if reading.forms().next().is_none()
        && let Some(shown) = help.trim_end().strip_suffix('`')
        && let Some(start) = shown.rfind('`')
        && shown[..start].trim_end().ends_with(':')
    {
        reading.push(Some(Advice::writes(&shown[start + 1..])), false);
    }
    reading
}

/// The first form a help line advises writing, if it advises one.
#[must_use]
pub fn advised_in_help(help: &str) -> Option<Advice> {
    read_help(help).forms().next().cloned()
}

/// What `diagnostic` advises, in its message and its help lines.
#[must_use]
pub fn read(diagnostic: &ObservedDiagnostic) -> Reading {
    let mut reading = read_message(&diagnostic.message);
    for help in &diagnostic.help {
        reading.groups.extend(read_help(help).groups);
    }
    reading
}

/// The first form `diagnostic` advises writing, if it advises one: in its message or a help line.
#[must_use]
pub fn advised(diagnostic: &ObservedDiagnostic) -> Option<Advice> {
    read(diagnostic).forms().next().cloned()
}

/// Whether `source` follows `reading`: in every group, it follows one alternative: writes its
/// form (or, for advice to take a form away, does not write it), or the alternative is advice in
/// prose, which only the reviewed field states.
#[must_use]
pub fn followed_in(reading: &Reading, source: &str) -> bool {
    reading.groups.iter().all(|group| {
        group.iter().any(|advice| {
            advice
                .as_ref()
                .is_none_or(|advice| written_in(advice, source))
        })
    })
}

/// A piece of a form as [`written_in`] compares it.
#[derive(Debug, Eq, PartialEq)]
enum Part {
    /// Text the source writes as it stands.
    Text(String),
    /// An elision, `..`: any text.
    Elided,
    /// A placeholder, a name of one letter (`p`, `e`, `x`, `N`): any one term, text whose
    /// brackets balance and that holds no `;`, `,`, brace, `->` or `=>` outside them.
    Placeholder,
}

/// The parts of `form`, its whitespace removed (after it has told names apart); `...`, prose's
/// elision, is `..`.
fn parts(form: &str) -> Vec<Part> {
    let form = form.replace("...", "..");
    let form = form.as_str();
    let characters = form.char_indices().collect::<Vec<_>>();
    let name = |character: char| character.is_alphanumeric() || character == '_';
    let mut parts = Vec::new();
    let mut text = String::new();
    let mut at = 0;
    while at < characters.len() {
        let (offset, character) = characters[at];
        if form[offset..].starts_with("..") {
            if !text.is_empty() {
                parts.push(Part::Text(std::mem::take(&mut text)));
            }
            parts.push(Part::Elided);
            at += 2;
            continue;
        }
        let before = at.checked_sub(1).map(|index| characters[index].1);
        let after = characters.get(at + 1).map(|(_, next)| *next);
        let placeholder = character.is_ascii_alphabetic()
            && !before.is_some_and(|before| name(before) || before == ':')
            && !after.is_some_and(|after| name(after) || matches!(after, ':' | '"' | '\'' | '!'));
        if placeholder {
            if !text.is_empty() {
                parts.push(Part::Text(std::mem::take(&mut text)));
            }
            parts.push(Part::Placeholder);
        } else if !character.is_whitespace() {
            text.push(character);
        }
        at += 1;
    }
    if !text.is_empty() {
        parts.push(Part::Text(text));
    }
    parts
}

/// The byte ends of the terms `text` starts with: each prefix whose brackets balance, before a
/// `;`, `,`, brace, `->` or `=>` outside them.
fn term_ends(text: &str) -> Vec<usize> {
    let mut ends = Vec::new();
    let mut depth = 0_usize;
    for (offset, character) in text.char_indices() {
        if depth == 0
            && (matches!(character, ';' | ',' | '{' | '}')
                || text[offset..].starts_with("->")
                || text[offset..].starts_with("=>"))
        {
            break;
        }
        match character {
            '(' | '[' | '<' => depth += 1,
            ')' | ']' | '>' => match depth.checked_sub(1) {
                Some(outer) => depth = outer,
                None => break,
            },
            _ => {}
        }
        if depth == 0 {
            ends.push(offset + character.len_utf8());
        }
    }
    ends
}

/// Whether `parts` match `source` from its byte `at` on, in order.
fn matches_from(parts: &[Part], source: &str, at: usize) -> bool {
    let Some((first, rest)) = parts.split_first() else {
        return true;
    };
    match first {
        Part::Text(text) => {
            source[at..].starts_with(text.as_str()) && matches_from(rest, source, at + text.len())
        }
        Part::Elided => source[at..]
            .char_indices()
            .map(|(offset, _)| at + offset)
            .chain([source.len()])
            .any(|end| matches_from(rest, source, end)),
        Part::Placeholder => term_ends(&source[at..])
            .into_iter()
            .any(|end| matches_from(rest, source, at + end)),
    }
}

/// `text` with its whitespace removed, as [`written_in`] compares a form with a source.
#[must_use]
pub fn squeezed(text: &str) -> String {
    text.split_whitespace().collect()
}

/// Whether `source` writes `advice`'s form, or, for advice to take it away, does not. The form
/// is compared with its whitespace removed, since an advised case lays its source out its own
/// way; an elision (`..`) stands for any text, a name of one letter for any term (the form's
/// placeholders, `let p = e;`), and an attribute written without arguments (`#[k::requires]`)
/// for the attribute with any.
#[must_use]
pub fn written_in(advice: &Advice, source: &str) -> bool {
    writes(&squeezed(source), &advice.form) != advice.removes
}

/// Whether `source`, its whitespace removed ([`squeezed`]), writes `form`.
fn writes(source: &str, form: &str) -> bool {
    let found = |form: &str| {
        let mut parts = parts(form);
        // Every text part is in the source, in some order, before the parts are matched.
        if !parts.iter().all(|part| match part {
            Part::Text(text) => source.contains(text.as_str()),
            _ => true,
        }) {
            return false;
        }
        parts.insert(0, Part::Elided);
        matches_from(&parts, source, 0)
    };
    let form = form.trim();
    let bare_attribute = form
        .strip_suffix(']')
        .filter(|open| open.starts_with("#[") && !open.contains('('));
    found(form) || bare_attribute.is_some_and(|open| found(&format!("{open}(")))
}

/// The sources of the generated cases a table accepts, for whether any writes a form: a form
/// no generated case writes is one K8 cannot check an advised case against
/// ([`Corpus::writer`]).
pub struct Corpus {
    sources: Vec<(String, String)>,
    found: std::sync::Mutex<std::collections::HashMap<String, Option<String>>>,
}

impl Corpus {
    /// The corpus of `sources`, each a case's ID and own text.
    #[must_use]
    pub fn new(sources: impl IntoIterator<Item = (String, String)>) -> Self {
        Self {
            sources: sources
                .into_iter()
                .map(|(id, source)| (id, squeezed(&source)))
                .collect(),
            found: std::sync::Mutex::default(),
        }
    }

    /// A case of the corpus that writes `form`, if one does.
    ///
    /// # Panics
    ///
    /// Panics if another thread panicked while it held the corpus's cache.
    #[must_use]
    pub fn writer(&self, form: &str) -> Option<String> {
        if let Some(found) = self.found.lock().expect("the cache").get(form) {
            return found.clone();
        }
        let writer = self
            .sources
            .iter()
            .find(|(_, source)| writes(source, form))
            .map(|(id, _)| id.clone());
        self.found
            .lock()
            .expect("the cache")
            .insert(form.to_owned(), writer.clone());
        writer
    }
}

/// K8's verdict on a refusal's advice against its class's advised cases.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Followed {
    /// Every group of the advice is followed by an advised case.
    Followed,
    /// A group no advised case follows has a form a generated case writes, `writer`: the
    /// advised cases do not write what the refusal advises.
    Unwritten {
        /// The form.
        form: String,
        /// A generated case that writes it.
        writer: String,
    },
    /// The groups no advised case follows propose forms no generated case writes: only the
    /// reviewed field states them.
    Unchecked,
}

/// Whether the advised cases' `sources` follow `reading`: each group of the advice is followed
/// by one of them ([`followed_in`]); a group none follows is checked where a generated case of
/// `corpus` writes one of its forms, and left to the reviewed field where none does.
#[must_use]
pub fn judge(reading: &Reading, sources: &[String], corpus: &Corpus) -> Followed {
    let open = reading
        .groups
        .iter()
        .filter(|group| {
            !sources.iter().any(|source| {
                group.iter().any(|advice| {
                    advice
                        .as_ref()
                        .is_none_or(|advice| written_in(advice, source))
                })
            })
        })
        .collect::<Vec<_>>();
    if open.is_empty() {
        return Followed::Followed;
    }
    open.iter()
        .flat_map(|group| group.iter().flatten())
        .find_map(|advice| {
            let writer = corpus.writer(&advice.form)?;
            Some(Followed::Unwritten {
                form: advice.form.clone(),
                writer,
            })
        })
        .unwrap_or(Followed::Unchecked)
}

#[cfg(test)]
mod tests {
    use super::{
        Advice, advised_in_help, advised_in_message, followed_in, read_message, written_in,
    };

    fn form(message: &str) -> Option<String> {
        advised_in_message(message).map(|advice| advice.form)
    }

    #[test]
    fn an_imperative_at_a_clause_start_proposes_the_clauses_first_span() {
        assert_eq!(
            form("a map rest is framed; write `map![k -> v, ..m]`").as_deref(),
            Some("map![k -> v, ..m]")
        );
        assert_eq!(
            form("Mark the production `#[k::alias]`").as_deref(),
            Some("#[k::alias]")
        );
        assert_eq!(
            form("x is retired: Use `#[k::rule(priority = 20)]`").as_deref(),
            Some("#[k::rule(priority = 20)]")
        );
        assert_eq!(
            form("a key it lacks, or declare the cell `initial`").as_deref(),
            Some("initial")
        );
    }

    #[test]
    fn a_verb_inside_a_clause_proposes_nothing() {
        assert_eq!(form("the rule may write `x` here"), None);
        assert_eq!(form("`x` names what we write `y`"), None);
    }

    #[test]
    fn a_clause_ends_at_a_semicolon_or_a_full_stop() {
        assert_eq!(form("write the operation as a call; `x` is shown"), None);
        assert_eq!(form("write it as a call. `x` is the operand"), None);
        assert_eq!(
            form("write the call `int::add(..)` instead").as_deref(),
            Some("int::add(..)")
        );
    }

    #[test]
    fn another_imperative_starts_its_own_clause() {
        let reading = read_message(
            "`smt_lemma` mentions `Probe`, which Z3 cannot see, so give it one or drop `smt_lemma`",
        );
        assert_eq!(
            reading.groups,
            [vec![
                None,
                Some(Advice {
                    form: "smt_lemma".to_owned(),
                    removes: true
                })
            ]],
            "`give it one` advises in prose, `drop` is its alternative"
        );
        assert!(followed_in(&reading, "#[k::equation(smt_lemma)]"));
        let both = read_message(
            "K needs a template; write Some(<template>) and add `initial` if the cell starts present",
        );
        assert_eq!(both.groups.len(), 2);
        assert!(!followed_in(&both, "counter: Some(0)"));
        assert!(followed_in(&both, "#[k::cell(initial)] counter: Some(0)"));
        let recursive = read_message(
            "recursion is a property of the production: write `recursive` on the production's `#[k::alias]` or `#[k::desugar]` marker, and a plain marker on its clauses",
        );
        assert_eq!(
            recursive
                .forms()
                .map(|advice| advice.form.as_str())
                .collect::<Vec<_>>(),
            ["recursive"]
        );
        assert!(!followed_in(&recursive, "#[k::desugar]"));
        assert!(followed_in(&recursive, "#[k::desugar(recursive)]"));
    }

    #[test]
    fn what_not_to_write_is_no_advice() {
        assert_eq!(
            form(
                "a `k::claims!` clause is labelled by its name: rename the clause instead of writing `label`"
            ),
            None
        );
        assert_eq!(form("write it rather than `x`"), None);
        assert_eq!(
            form("list notation names no list; use them where a field declares `List`"),
            None
        );
        assert_eq!(form("write it, not `x`"), None);
        assert_eq!(form("write `y`, not `x`").as_deref(), Some("y"));
    }

    #[test]
    fn replace_proposes_the_span_after_with() {
        assert_eq!(
            form("replace `#[k::priority(N)]` with `#[k::rule(priority = N)]`").as_deref(),
            Some("#[k::rule(priority = N)]")
        );
        assert_eq!(form("replace `a`, then think"), None);
    }

    #[test]
    fn drop_and_remove_advise_taking_the_form_away() {
        assert_eq!(
            advised_in_message("a desugar takes no condition; remove `#[k::requires]`"),
            Some(Advice {
                form: "#[k::requires]".to_owned(),
                removes: true
            })
        );
        assert!(
            advised_in_message("drop `owise`")
                .is_some_and(|advice| advice.removes && advice.form == "owise")
        );
    }

    #[test]
    fn move_state_split_and_put_propose_their_span() {
        assert_eq!(
            form("move `#[k::requires]` to the rule").as_deref(),
            Some("#[k::requires]")
        );
        assert_eq!(form("state `result = S`").as_deref(), Some("result = S"));
        assert_eq!(form("split it into `a` and `b`").as_deref(), Some("a"));
        assert_eq!(form("put `x` first").as_deref(), Some("x"));
    }

    #[test]
    fn a_form_is_written_right_after_the_verb() {
        assert_eq!(
            form("`counter` is written `Some(..)` when present").as_deref(),
            Some("Some(..)")
        );
        assert_eq!(
            form("an absent cell is written as `None`").as_deref(),
            Some("None")
        );
        assert_eq!(form("`counter` is written without `Some`"), None);
        assert_eq!(form("the key `x` is written twice; two keys are one"), None);
    }

    #[test]
    fn writes_as_proposes_the_span_after_as() {
        assert_eq!(
            form("a method call is not a pattern: a pattern writes `int::add` as the call `int::add(..)`, where ..").as_deref(),
            Some("int::add(..)")
        );
        assert_eq!(
            form("`+` is not a pattern: a pattern writes a builtin operation as its call, `int::add(..)`, or").as_deref(),
            Some("int::add(..)")
        );
        assert_eq!(form("the pattern writes `x` twice"), None);
    }

    #[test]
    fn verbs_are_read_whatever_their_case() {
        assert_eq!(form("Write `x`").as_deref(), Some("x"));
        assert_eq!(form("WRITE `x`").as_deref(), Some("x"));
    }

    #[test]
    fn text_beyond_ascii_is_read_without_panicking() {
        assert_eq!(form("a — b; write `x`").as_deref(), Some("x"));
        assert_eq!(form("a — write `x`").as_deref(), Some("x"));
        assert_eq!(form("é `ü` — ß; Write `ç`").as_deref(), Some("ç"));
        assert_eq!(form("—`—`—"), None);
        assert_eq!(form("``"), None);
        assert_eq!(form("`"), None);
        assert_eq!(form(""), None);
    }

    #[test]
    fn no_text_makes_the_detector_panic() {
        let texts = [
            "a — b; write `x`",
            "`é`ü—; Replace `ß` with `ç`. drop `—`",
            "is written `—` as; writes — as `x`",
            "—`—`—`",
        ];
        for text in texts {
            for (at, _) in text.char_indices().chain([(text.len(), ' ')]) {
                let _ = read_message(&text[..at]);
                let _ = read_message(&text[at..]);
                let _ = super::read_help(&text[at..]);
            }
        }
    }

    #[test]
    fn a_help_line_shows_a_form_after_a_colon() {
        assert_eq!(
            advised_in_help(
                "a rule for any term is a `for Sort` clause: `k::rules! { for KItem; .. }`"
            )
            .map(|advice| advice.form)
            .as_deref(),
            Some("k::rules! { for KItem; .. }")
        );
        assert_eq!(advised_in_help("see `x` for more"), None);
    }

    #[test]
    fn a_source_writes_a_form_up_to_whitespace_and_elisions() {
        let write = |form: &str| Advice {
            form: form.to_owned(),
            removes: false,
        };
        let source = "#[k::equation(priority = 20)]\nfn f(k::term![Probe(x, 1)]) {}";
        assert!(written_in(&write("#[k::equation(priority=20)]"), source));
        assert!(written_in(&write("Probe(..)"), source));
        assert!(!written_in(&write("#[k::rule(priority = 20)]"), source));
        let remove = Advice {
            form: "#[k::requires]".to_owned(),
            removes: true,
        };
        assert!(written_in(&remove, source));
        assert!(!written_in(&remove, "#[k::requires(x)]"));
    }

    #[test]
    fn a_name_of_one_letter_is_a_placeholder() {
        let write = |form: &str| Advice {
            form: form.to_owned(),
            removes: false,
        };
        assert!(written_in(
            &write("let p = e; let P = p;"),
            "{ let y = x; let Cmd::Hold(_) = y; y }"
        ));
        assert!(!written_in(
            &write("let p = e; let P = p;"),
            "{ let y = x; y }"
        ));
        assert!(written_in(
            &write("a.bit_or::<Int>(b)"),
            "x.bit_or::<Int>(1)"
        ));
        assert!(written_in(
            &write("Some(k::configuration::Cell(..))"),
            "counter: Some(k::configuration::Cell(x))"
        ));
        assert!(!written_in(
            &write("k::bytes!(b\"ab\")"),
            "k::bytes!(c\"ab\")"
        ));
        assert!(written_in(
            &write("map![k -> v, ..m]"),
            "k::map![x -> 1, ..rest]"
        ));
        assert!(written_in(
            &write("{ k -> v, .. }"),
            "readable: { env: { y -> x, .. } }"
        ));
        assert!(!written_in(
            &write("{ k -> v, .. }"),
            "fn f() -> Machine { k::cells! { k: x, .. } }"
        ));
    }
}
