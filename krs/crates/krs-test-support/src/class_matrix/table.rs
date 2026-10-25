//! The expected-outcome table, `krs/tests/class-matrix/expected.toml`.
//!
//! The table has three parts:
//!
//! 1. `[class.NAME]`: mistake classes, each with one registered author `code` and a `doc`. A class
//!    names an author mistake, not a site, so every case of the mistake answers with one code.
//!    `proposed = true` marks a code that is not registered yet, whose step will register it;
//!    until then every case of the class is red, and once it is registered the mark must go.
//! 2. `[[refuse]]`: refusal rules, each a `match` glob over case IDs, the `class` of the mistake
//!    the matched cases make, and `at`, the range the error must lie inside (`entry`,
//!    `spelling`, `item`, or `header`).
//! 3. `[accept."ID"]`: an accepted case, with `k`, the K sentences it adds to its base,
//!    normalized, and `same_k_as`, the IDs of other accepted cases that must emit the same
//!    normalized K. `k` is written by the full tier's record mode (`scripts/krs-class.sh
//!    --record`) and reviewed as a diff, never by hand; an entry without `k` is a case that should
//!    be accepted and is refused today, whose K is recorded once it is accepted.
//!
//! Which codes never answer an author mistake is the registry's kind (`krs_diagnostic::codes::
//! CodeKind`), not the table's.
//!
//! **Globs.** `*` matches any run of characters other than `/`, and `{a,b,..}` matches any one
//! of its comma-separated alternatives, which may themselves hold globs. `\` makes the next
//! character literal, since constructs hold braces and commas (`{ y -> x, .. }`): write such a
//! glob in a TOML literal string, `'readable/subject/env/\{ .. \}'`. Every other character
//! matches itself.
//!
//! **Resolution.** A case is decided by the most specific entry that covers it: an accept
//! entry covers its one ID, and a refusal rule the IDs its glob matches. One entry is more
//! specific than another when the cases it covers are a strict subset of the other's, over the
//! generated cases. A case covered by two entries of which neither is more specific than the
//! other is a tie, and a case no entry covers is uncovered; both are table errors, so a
//! complete table decides every case exactly once.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::ops::Range;

use krs_diagnostic::codes::CodeKind;
use toml_edit::{DocumentMut, Item, Table as TomlTable};

use super::Placed;

/// The range a refusal's error must lie inside.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum At {
    /// The slot's unit that holds the construct, `pc: Some(x)` for a cell entry.
    Entry,
    /// The construct itself.
    Spelling,
    /// The case's whole item.
    Item,
    /// The header of the entry point a mutation breaks.
    Header,
}

impl At {
    /// The range of `placed` this site names; a header lies in the case's item.
    #[must_use]
    pub const fn range<'p>(self, placed: &'p Placed<'_>) -> &'p Range<usize> {
        match self {
            Self::Spelling => &placed.spelling,
            Self::Entry => &placed.entry,
            Self::Item | Self::Header => &placed.item,
        }
    }

    fn parse(text: &str) -> Option<Self> {
        match text {
            "entry" => Some(Self::Entry),
            "spelling" => Some(Self::Spelling),
            "item" => Some(Self::Item),
            "header" => Some(Self::Header),
            _ => None,
        }
    }
}

/// One mistake class.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MistakeClass {
    /// The registered code every case of the class answers with.
    pub code: String,
    /// What the author wrote wrong.
    pub doc: String,
    /// Whether the code is proposed and not registered yet.
    pub proposed: bool,
}

/// One refusal rule.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RefuseRule {
    /// The glob over case IDs.
    pub pattern: String,
    /// The mistake class of the matched cases.
    pub class: String,
    /// The range the error must lie inside.
    pub at: At,
}

/// One accepted case.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Accepted {
    /// The K sentences the case adds to its base, normalized; `None` until the case is first
    /// accepted and recorded.
    pub k: Option<String>,
    /// Other accepted cases that must emit the same normalized K.
    pub same_k_as: Vec<String>,
}

/// The parsed table.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Table {
    /// The mistake classes by name.
    pub classes: BTreeMap<String, MistakeClass>,
    /// The refusal rules in table order.
    pub refuse: Vec<RefuseRule>,
    /// The accepted cases by ID.
    pub accept: BTreeMap<String, Accepted>,
}

/// What the table expects of one case.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Expected<'t> {
    /// The case is accepted and emits this K.
    Accept(&'t Accepted),
    /// The case is refused with its class's code, inside the rule's range.
    Refuse {
        /// The deciding rule.
        rule: &'t RefuseRule,
        /// The rule's class.
        class: &'t MistakeClass,
    },
}

impl Expected<'_> {
    /// The range a refusal of the case must lie inside (invariant 2): the refusal rule's site,
    /// and the entry for an accepted case.
    #[must_use]
    pub fn site<'p>(&self, placed: &'p Placed<'_>) -> &'p Range<usize> {
        match self {
            Self::Refuse { rule, .. } => rule.at.range(placed),
            Self::Accept(_) => &placed.entry,
        }
    }
}

/// A defect of the table, or of the table against the generated cases.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TableError {
    /// The text does not follow the table's schema.
    Schema(String),
    /// A glob does not parse.
    Glob {
        /// The glob.
        pattern: String,
        /// What is wrong.
        reason: String,
    },
    /// A rule names a class the table does not declare.
    UnknownClass {
        /// The rule's glob.
        pattern: String,
        /// The class it names.
        class: String,
    },
    /// A class's code is not in the registry.
    Unregistered {
        /// Where the code is named.
        owner: String,
        /// The code.
        code: String,
    },
    /// A class marks its code proposed, but the registry has it.
    ProposedRegistered {
        /// The class.
        class: String,
        /// The code.
        code: String,
    },
    /// A class answers with a code the registry does not give the author kind.
    NonAuthorClassCode {
        /// The class.
        class: String,
        /// The code.
        code: String,
        /// The code's kind.
        kind: CodeKind,
    },
    /// An accept entry or a `same_k_as` names no generated case.
    UnknownCase {
        /// Where the ID is named.
        owner: String,
        /// The ID.
        id: String,
    },
    /// A `same_k_as` names a case that is not accepted.
    SameKNotAccepted {
        /// The accepted case.
        id: String,
        /// The case it names.
        other: String,
    },
    /// A refusal rule matches no generated case.
    UnusedRule {
        /// The rule's glob.
        pattern: String,
    },
    /// No entry covers a case.
    Uncovered {
        /// The case.
        id: String,
    },
    /// Two or more entries cover a case and none is more specific than the others.
    Tie {
        /// The case.
        id: String,
        /// The tied entries: globs, or `accept` for an accept entry.
        entries: Vec<String>,
    },
}

impl fmt::Display for TableError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Schema(message) => write!(formatter, "expected.toml: {message}"),
            Self::Glob { pattern, reason } => write!(formatter, "glob {pattern:?}: {reason}"),
            Self::UnknownClass { pattern, class } => {
                write!(
                    formatter,
                    "rule {pattern:?} names the undeclared class {class:?}"
                )
            }
            Self::Unregistered { owner, code } => {
                write!(formatter, "{owner} names the unregistered code {code:?}")
            }
            Self::ProposedRegistered { class, code } => write!(
                formatter,
                "class {class:?} marks {code:?} proposed, but it is registered: remove `proposed`"
            ),
            Self::NonAuthorClassCode { class, code, kind } => write!(
                formatter,
                "class {class:?} answers with {code:?}, which is no author code but {kind:?}"
            ),
            Self::UnknownCase { owner, id } => {
                write!(
                    formatter,
                    "{owner} names {id:?}, which is no generated case"
                )
            }
            Self::SameKNotAccepted { id, other } => write!(
                formatter,
                "accepted case {id:?} pairs with {other:?}, which is not accepted"
            ),
            Self::UnusedRule { pattern } => {
                write!(formatter, "rule {pattern:?} matches no generated case")
            }
            Self::Uncovered { id } => write!(formatter, "no entry decides {id:?}"),
            Self::Tie { id, entries } => write!(
                formatter,
                "{id:?} is covered by {} with none more specific",
                entries.join(", ")
            ),
        }
    }
}

/// The table's expectation of every case it decides, and its errors.
#[derive(Clone, Debug)]
pub struct Resolution<'t> {
    /// The expectation of each decided case, by ID.
    pub expected: BTreeMap<String, Expected<'t>>,
    /// Every table error; empty for a complete table.
    pub errors: Vec<TableError>,
}

impl Table {
    /// Parse the table's text.
    ///
    /// # Errors
    ///
    /// Returns every schema error and every glob that does not parse.
    pub fn parse(text: &str) -> Result<Self, Vec<TableError>> {
        let document = text
            .parse::<DocumentMut>()
            .map_err(|error| vec![TableError::Schema(error.to_string())])?;
        let mut errors = Vec::new();
        let mut table = Self::default();
        for (key, item) in document.iter() {
            match key {
                "class" => table.classes = parse_classes(item, &mut errors),
                "refuse" => table.refuse = parse_rules(item, &mut errors),
                "accept" => table.accept = parse_accepts(item, &mut errors),
                other => errors.push(schema(format!("unknown part {other:?}"))),
            }
        }
        for rule in &table.refuse {
            if let Err(reason) = Glob::parse(&rule.pattern) {
                errors.push(TableError::Glob {
                    pattern: rule.pattern.clone(),
                    reason,
                });
            }
        }
        if errors.is_empty() {
            Ok(table)
        } else {
            Err(errors)
        }
    }

    /// Decide every case of `ids`, and check the table against them and against the code
    /// registry, which `kind` answers: a code's kind, or `None` for an unregistered code.
    ///
    /// # Panics
    ///
    /// Panics if a rule's glob does not parse, which [`Table::parse`] rules out.
    #[must_use]
    pub fn resolve<'t>(
        &'t self,
        ids: &[&str],
        kind: impl Fn(&str) -> Option<CodeKind>,
    ) -> Resolution<'t> {
        let mut errors = self.check_codes(&kind);
        let known = ids.iter().copied().collect::<BTreeSet<_>>();
        self.check_accepts(&known, &mut errors);

        let mut covers = Vec::<(Entry<'t>, BTreeSet<&str>)>::new();
        for (id, accepted) in &self.accept {
            if known.contains(id.as_str()) {
                covers.push((Entry::Accept(accepted), BTreeSet::from([id.as_str()])));
            }
        }
        for rule in &self.refuse {
            let glob = Glob::parse(&rule.pattern).expect("a parsed table's globs parse");
            let matched = ids
                .iter()
                .copied()
                .filter(|id| glob.matches(id))
                .collect::<BTreeSet<_>>();
            if matched.is_empty() {
                errors.push(TableError::UnusedRule {
                    pattern: rule.pattern.clone(),
                });
            }
            match self.classes.get(&rule.class) {
                Some(class) => covers.push((Entry::Refuse { rule, class }, matched)),
                None => errors.push(TableError::UnknownClass {
                    pattern: rule.pattern.clone(),
                    class: rule.class.clone(),
                }),
            }
        }

        let mut expected = BTreeMap::new();
        for id in ids {
            let covering = covers
                .iter()
                .filter(|(_, covered)| covered.contains(id))
                .collect::<Vec<_>>();
            // The entries that no other covering entry is more specific than; in a finite
            // order, a single one is more specific than every other covering entry.
            let minimal = covering
                .iter()
                .filter(|(_, covered)| {
                    !covering
                        .iter()
                        .any(|(_, other)| other.len() < covered.len() && other.is_subset(covered))
                })
                .collect::<Vec<_>>();
            match minimal.as_slice() {
                [] => errors.push(TableError::Uncovered {
                    id: (*id).to_owned(),
                }),
                [(entry, _)] => {
                    expected.insert((*id).to_owned(), entry.expected());
                }
                tied => errors.push(TableError::Tie {
                    id: (*id).to_owned(),
                    entries: tied.iter().map(|(entry, _)| entry.name()).collect(),
                }),
            }
        }
        Resolution { expected, errors }
    }

    fn check_codes(&self, kind: &impl Fn(&str) -> Option<CodeKind>) -> Vec<TableError> {
        let mut errors = Vec::new();
        for (name, class) in &self.classes {
            match (class.proposed, kind(&class.code)) {
                (true, Some(_)) => errors.push(TableError::ProposedRegistered {
                    class: name.clone(),
                    code: class.code.clone(),
                }),
                (false, None) => errors.push(TableError::Unregistered {
                    owner: format!("class {name:?}"),
                    code: class.code.clone(),
                }),
                (_, Some(CodeKind::Author)) | (true, None) => {}
                (false, Some(kind)) => errors.push(TableError::NonAuthorClassCode {
                    class: name.clone(),
                    code: class.code.clone(),
                    kind,
                }),
            }
        }
        errors
    }

    fn check_accepts(&self, known: &BTreeSet<&str>, errors: &mut Vec<TableError>) {
        for (id, accepted) in &self.accept {
            if !known.contains(id.as_str()) {
                errors.push(TableError::UnknownCase {
                    owner: "an accept entry".to_owned(),
                    id: id.clone(),
                });
            }
            for other in &accepted.same_k_as {
                if !known.contains(other.as_str()) {
                    errors.push(TableError::UnknownCase {
                        owner: format!("same_k_as of {id:?}"),
                        id: other.clone(),
                    });
                } else if !self.accept.contains_key(other) {
                    errors.push(TableError::SameKNotAccepted {
                        id: id.clone(),
                        other: other.clone(),
                    });
                }
            }
        }
    }
}

/// A table entry that decides cases.
#[derive(Clone, Copy, Debug)]
enum Entry<'t> {
    Accept(&'t Accepted),
    Refuse {
        rule: &'t RefuseRule,
        class: &'t MistakeClass,
    },
}

impl<'t> Entry<'t> {
    const fn expected(&self) -> Expected<'t> {
        match *self {
            Self::Accept(accepted) => Expected::Accept(accepted),
            Self::Refuse { rule, class } => Expected::Refuse { rule, class },
        }
    }

    fn name(&self) -> String {
        match self {
            Self::Accept(_) => "accept".to_owned(),
            Self::Refuse { rule, .. } => format!("{:?}", rule.pattern),
        }
    }
}

const fn schema(message: String) -> TableError {
    TableError::Schema(message)
}

fn table_of<'a>(
    item: &'a Item,
    owner: &str,
    errors: &mut Vec<TableError>,
) -> Option<&'a TomlTable> {
    let table = item.as_table();
    if table.is_none() {
        errors.push(schema(format!("{owner} is not a table")));
    }
    table
}

/// The fields of `table`, after checking that it has every `required` key and no key outside
/// `required` and `optional`.
fn fields<'a>(
    table: &'a TomlTable,
    owner: &str,
    required: &[&str],
    optional: &[&str],
    errors: &mut Vec<TableError>,
) -> BTreeMap<&'a str, &'a Item> {
    let fields = table.iter().collect::<BTreeMap<_, _>>();
    for key in fields.keys() {
        if !required.contains(key) && !optional.contains(key) {
            errors.push(schema(format!("{owner} has the unknown key {key:?}")));
        }
    }
    for key in required {
        if !fields.contains_key(key) {
            errors.push(schema(format!("{owner} lacks {key:?}")));
        }
    }
    fields
}

fn string(item: Option<&&Item>, owner: &str, key: &str, errors: &mut Vec<TableError>) -> String {
    match item.map(|item| item.as_str()) {
        Some(Some(text)) => text.to_owned(),
        Some(None) => {
            errors.push(schema(format!("{owner}.{key} is not a string")));
            String::new()
        }
        None => String::new(),
    }
}

fn strings(
    item: Option<&&Item>,
    owner: &str,
    key: &str,
    errors: &mut Vec<TableError>,
) -> Vec<String> {
    let Some(item) = item else {
        return Vec::new();
    };
    let Some(array) = item.as_array() else {
        errors.push(schema(format!("{owner}.{key} is not an array")));
        return Vec::new();
    };
    array
        .iter()
        .filter_map(|value| {
            let text = value.as_str();
            if text.is_none() {
                errors.push(schema(format!(
                    "{owner}.{key} holds a value that is not a string"
                )));
            }
            text.map(str::to_owned)
        })
        .collect()
}

fn parse_classes(item: &Item, errors: &mut Vec<TableError>) -> BTreeMap<String, MistakeClass> {
    let mut classes = BTreeMap::new();
    let Some(table) = table_of(item, "[class]", errors) else {
        return classes;
    };
    for (name, item) in table {
        let owner = format!("class.{name}");
        let Some(class) = table_of(item, &owner, errors) else {
            continue;
        };
        let fields = fields(class, &owner, &["code", "doc"], &["proposed"], errors);
        let proposed = match fields.get("proposed").map(|item| item.as_bool()) {
            None => false,
            Some(Some(proposed)) => proposed,
            Some(None) => {
                errors.push(schema(format!("{owner}.proposed is not a boolean")));
                false
            }
        };
        classes.insert(
            name.to_owned(),
            MistakeClass {
                code: string(fields.get("code"), &owner, "code", errors),
                doc: string(fields.get("doc"), &owner, "doc", errors),
                proposed,
            },
        );
    }
    classes
}

fn parse_rules(item: &Item, errors: &mut Vec<TableError>) -> Vec<RefuseRule> {
    let Some(rules) = item.as_array_of_tables() else {
        errors.push(schema("[[refuse]] is not an array of tables".to_owned()));
        return Vec::new();
    };
    rules
        .iter()
        .enumerate()
        .map(|(index, rule)| {
            let owner = format!("refuse[{index}]");
            let fields = fields(rule, &owner, &["match", "class", "at"], &[], errors);
            let at = string(fields.get("at"), &owner, "at", errors);
            RefuseRule {
                pattern: string(fields.get("match"), &owner, "match", errors),
                class: string(fields.get("class"), &owner, "class", errors),
                at: At::parse(&at).unwrap_or_else(|| {
                    if fields.contains_key("at") {
                        errors.push(schema(format!(
                            "{owner}.at is {at:?}, not entry, spelling, item, or header"
                        )));
                    }
                    At::Entry
                }),
            }
        })
        .collect()
}

fn parse_accepts(item: &Item, errors: &mut Vec<TableError>) -> BTreeMap<String, Accepted> {
    let mut accepts = BTreeMap::new();
    let Some(table) = table_of(item, "[accept]", errors) else {
        return accepts;
    };
    for (id, item) in table {
        let owner = format!("accept.{id:?}");
        let Some(accepted) = table_of(item, &owner, errors) else {
            continue;
        };
        let fields = fields(accepted, &owner, &[], &["k", "same_k_as"], errors);
        accepts.insert(
            id.to_owned(),
            Accepted {
                k: fields
                    .contains_key("k")
                    .then(|| string(fields.get("k"), &owner, "k", errors)),
                same_k_as: strings(fields.get("same_k_as"), &owner, "same_k_as", errors),
            },
        );
    }
    accepts
}

/// A parsed glob over case IDs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Glob(Vec<Token>);

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Literal(char),
    Star,
    Alternatives(Vec<Vec<Token>>),
}

impl Glob {
    /// Parse a glob.
    ///
    /// # Errors
    ///
    /// Returns why the glob does not parse: a brace that is not closed or closes nothing, or a
    /// trailing `\`.
    pub fn parse(pattern: &str) -> Result<Self, String> {
        let (tokens, _) = parse_sequence(&mut pattern.chars(), false)?;
        Ok(Self(tokens))
    }

    /// Whether the glob matches the whole of `id`.
    #[must_use]
    pub fn matches(&self, id: &str) -> bool {
        matches_from(&self.0, &id.chars().collect::<Vec<_>>())
    }
}

/// Parse tokens up to the pattern's end, or, inside braces, up to a `,` or `}`; returns the
/// tokens and whether a `}` ended them.
fn parse_sequence(
    characters: &mut std::str::Chars<'_>,
    nested: bool,
) -> Result<(Vec<Token>, bool), String> {
    let mut tokens = Vec::new();
    while let Some(character) = characters.next() {
        match character {
            '\\' => tokens.push(Token::Literal(
                characters
                    .next()
                    .ok_or_else(|| "a trailing `\\` escapes nothing".to_owned())?,
            )),
            '*' => tokens.push(Token::Star),
            '{' => {
                let mut alternatives = Vec::new();
                loop {
                    let (alternative, closed) = parse_sequence(characters, true)?;
                    alternatives.push(alternative);
                    if closed {
                        break;
                    }
                }
                tokens.push(Token::Alternatives(alternatives));
            }
            '}' if nested => return Ok((tokens, true)),
            ',' if nested => return Ok((tokens, false)),
            '}' => {
                return Err("a `}` closes no `{`; write `\\}` for a literal brace".to_owned());
            }
            other => tokens.push(Token::Literal(other)),
        }
    }
    if nested {
        Err("a `{` is not closed; write `\\{` for a literal brace".to_owned())
    } else {
        Ok((tokens, false))
    }
}

fn matches_from(tokens: &[Token], id: &[char]) -> bool {
    let Some((first, rest)) = tokens.split_first() else {
        return id.is_empty();
    };
    match first {
        Token::Literal(character) => id.first() == Some(character) && matches_from(rest, &id[1..]),
        Token::Star => (0..=id.len())
            .take_while(|&taken| taken == 0 || id[taken - 1] != '/')
            .any(|taken| matches_from(rest, &id[taken..])),
        Token::Alternatives(alternatives) => alternatives.iter().any(|alternative| {
            let joined = alternative.iter().chain(rest).cloned().collect::<Vec<_>>();
            matches_from(&joined, id)
        }),
    }
}
