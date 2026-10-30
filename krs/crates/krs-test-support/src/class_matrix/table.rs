//! The expected-outcome table, `krs/tests/class-matrix/expected.toml`.
//!
//! The table has three parts:
//!
//! 1. `[class.NAME]`: mistake classes, each with one registered author `code` and a `doc`. A class
//!    names an author mistake, not a site, so every case of the mistake answers with one code.
//!    `proposed = true` marks a code that is not registered yet, whose step will register it;
//!    until then every case of the class is red, and once it is registered the mark must go.
//!    `advice = "ID"` names the case that writes the form the class's refusal advises writing
//!    instead ([`super::advice`]), which the table must accept.
//! 2. `[[refuse]]`: refusal rules, each a `match` glob over case IDs, the `class` of the mistake
//!    the matched cases make, and `at`, the range the error must lie inside (`entry`,
//!    `spelling`, `item`, or `header`).
//! 3. `[accept."ID"]`: an accepted case, with `k`, the K sentences it adds to its base,
//!    normalized, and `same_k_as`, the IDs of other accepted cases that must emit the same
//!    normalized K. `k` is written by the full tier's record mode (`scripts/krs-class.sh
//!    --record`) and reviewed as a diff, never by hand; an entry without `k` is a case that should
//!    be accepted and is refused today, whose K is recorded once it is accepted.
//!
//! The term families' accept entries (`terms/..`, `import/..`, `notation/..`) and the attribute
//! axis's (`attrs/..`), the families the oracle judges, live in a file of their own,
//! `krs/tests/class-matrix/accepted-terms.toml` ([`TERM_ACCEPTS_FILE`]), which holds only
//! `[accept."ID"]` entries of those families, in the schema of part 3: they are most of the
//! table, written by the record mode, and apart they leave `expected.toml` readable.
//! [`Table::parse_with_term_accepts`] reads both as one table.
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
//!
//! **The term families.** A `terms/`, `import/` or `notation/` case is judged by the oracle
//! ([`super::oracle`]) first, from its position and its construct's nodes, and the table's
//! entries decide only what the oracle leaves:
//!
//! 1. a refusal the oracle tells by the spelling and its position ([`Stage::Placement`]) decides,
//!    at the spelling, or at the entry when the refused construct is the outer one a depth-2
//!    case's construct stands in (the entry is the outer construct's text);
//! 2. otherwise the most specific refusal rule that covers the case decides: the rules left for
//!    these families name a term's sort and names (`condition-sort`, `let-sort`, `unbound-name`,
//!    `record-update-base`), which the compiler judges for every term alike;
//! 3. otherwise a refusal the oracle tells by resolution ([`Stage::Resolution`]) decides, at the
//!    spelling or the outer construct's entry: a name or sort mistake is met before what a path
//!    resolves to is asked;
//! 4. otherwise the case is accepted, and its accept entry records its K.
//!
//! So no rule refuses such a case for its construct's position: a rule whose class is one the
//! oracle answers with and that matches a term case is a table error. An accept entry never
//! overrides a refusal, and an accept entry of a refused case is a table error. A rule that
//! matches cases but decides none is a table error for every family. The cases where step 2
//! overrides an oracle refusal of step 3 are listed ([`Resolution::overridden`]), so a test can
//! pin them.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::ops::Range;

use krs_diagnostic::codes::CodeKind;
use toml_edit::{DocumentMut, Item, Table as TomlTable};

use super::oracle::{Class as OracleClass, Outcome, Stage};
use super::{Case, Placed};

/// The file beside `expected.toml` that holds the term families' accept entries.
pub const TERM_ACCEPTS_FILE: &str = "accepted-terms.toml";

/// Whether `id` is a case of the families the oracle judges, the term families and the attribute
/// axis, whose accept entries [`TERM_ACCEPTS_FILE`] holds.
#[must_use]
pub fn is_term_case(id: &str) -> bool {
    id.starts_with("terms/")
        || id.starts_with("import/")
        || id.starts_with("notation/")
        || id.starts_with("attrs/")
}

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
    /// The generated case that writes the form the class's refusal advises writing instead
    /// (K8, [`super::advice`]), which the table must accept.
    pub advice: Option<String>,
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
    /// The case is refused with its class's code, inside the deciding range.
    Refuse {
        /// The class's name.
        name: &'t str,
        /// The class.
        class: &'t MistakeClass,
        /// The range the error must lie inside: the deciding rule's, or the spelling for the
        /// oracle's refusal.
        at: At,
    },
}

impl Expected<'_> {
    /// The range a refusal of the case must lie inside (invariant 2): the refusal rule's site,
    /// and the entry for an accepted case.
    #[must_use]
    pub fn site<'p>(&self, placed: &'p Placed<'_>) -> &'p Range<usize> {
        match self {
            Self::Refuse { at, .. } => at.range(placed),
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
    /// The oracle refuses a case with a class the table does not declare.
    UnknownOracleClass {
        /// The case.
        id: String,
        /// The class.
        class: String,
    },
    /// An accept entry names a term case that the oracle or a refusal rule refuses.
    AcceptsRefusedCase {
        /// The case.
        id: String,
        /// The class it is refused with.
        class: String,
    },
    /// A refusal rule names a class the oracle answers with and matches a term case, which the
    /// oracle decides for its construct's position.
    OracleClassRule {
        /// The rule's glob.
        pattern: String,
        /// The class.
        class: String,
    },
    /// A refusal rule matches cases but decides none: a more specific entry or the oracle
    /// decides each.
    ShadowedRule {
        /// The rule's glob.
        pattern: String,
    },
    /// A class's advised case is one the table does not accept.
    AdviceNotAccepted {
        /// The class.
        class: String,
        /// The advised case.
        id: String,
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
            Self::UnknownOracleClass { id, class } => write!(
                formatter,
                "the oracle refuses {id:?} as the undeclared class {class:?}"
            ),
            Self::AcceptsRefusedCase { id, class } => write!(
                formatter,
                "{id:?} has an accept entry, but it is refused as {class:?}"
            ),
            Self::OracleClassRule { pattern, class } => write!(
                formatter,
                "rule {pattern:?} refuses term cases as {class:?}, which the oracle decides"
            ),
            Self::ShadowedRule { pattern } => {
                write!(formatter, "rule {pattern:?} decides no case it matches")
            }
            Self::AdviceNotAccepted { class, id } => write!(
                formatter,
                "class {class:?} advises the form {id:?} writes, which the table does not accept"
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
    /// The term cases a refusal rule decides although the oracle refuses them by resolution,
    /// with the oracle's class: the rule's name or sort mistake is met first.
    pub overridden: BTreeMap<String, &'static str>,
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

    /// Parse `expected.toml`'s text and [`TERM_ACCEPTS_FILE`]'s as one table.
    ///
    /// # Errors
    ///
    /// Returns every error of either text, an accept entry of the first that is a term case, and
    /// an accept entry of the second that is no term case or a part other than `accept`.
    pub fn parse_with_term_accepts(
        text: &str,
        term_accepts: &str,
    ) -> Result<Self, Vec<TableError>> {
        let mut errors = Vec::new();
        let mut table = Self::parse(text).unwrap_or_else(|found| {
            errors.extend(found);
            Self::default()
        });
        for id in table.accept.keys().filter(|id| is_term_case(id)) {
            errors.push(schema(format!(
                "expected.toml accepts the term case {id:?}, whose entry belongs in {TERM_ACCEPTS_FILE}"
            )));
        }
        match Self::parse(term_accepts) {
            Ok(terms) => {
                if !terms.classes.is_empty() || !terms.refuse.is_empty() {
                    errors.push(schema(format!(
                        "{TERM_ACCEPTS_FILE} holds parts other than accept entries"
                    )));
                }
                for (id, accepted) in terms.accept {
                    if is_term_case(&id) {
                        table.accept.insert(id, accepted);
                    } else {
                        errors.push(schema(format!(
                            "{TERM_ACCEPTS_FILE} accepts {id:?}, which is no term case"
                        )));
                    }
                }
            }
            Err(found) => errors.extend(found),
        }
        if errors.is_empty() {
            Ok(table)
        } else {
            Err(errors)
        }
    }

    /// Decide every case of `ids`, and check the table against them and against the code
    /// registry, which `kind` answers: a code's kind, or `None` for an unregistered code.
    /// `oracle` answers the oracle's outcome of a term case and `None` for a case of another
    /// family, which the entries alone decide.
    ///
    /// # Panics
    ///
    /// Panics if a rule's glob does not parse, which [`Table::parse`] rules out.
    #[must_use]
    pub fn resolve<'t>(
        &'t self,
        ids: &[&str],
        oracle: impl Fn(&str) -> Option<Outcome>,
        kind: impl Fn(&str) -> Option<CodeKind>,
    ) -> Resolution<'t> {
        let mut gathered = Gathered {
            errors: self.check_codes(&kind),
            overridden: BTreeMap::new(),
            deciding: BTreeSet::new(),
        };
        let known = ids.iter().copied().collect::<BTreeSet<_>>();
        self.check_accepts(&known, &mut gathered.errors);
        let outcomes = ids
            .iter()
            .map(|id| (*id, oracle(id)))
            .collect::<BTreeMap<_, _>>();
        let oracle_classes = OracleClass::ALL.map(OracleClass::name);

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
                gathered.errors.push(TableError::UnusedRule {
                    pattern: rule.pattern.clone(),
                });
            }
            if oracle_classes.contains(&rule.class.as_str())
                && matched.iter().any(|id| outcomes[id].is_some())
            {
                gathered.errors.push(TableError::OracleClassRule {
                    pattern: rule.pattern.clone(),
                    class: rule.class.clone(),
                });
            }
            match self.classes.get(&rule.class) {
                Some(class) => covers.push((Entry::Refuse { rule, class }, matched)),
                None => gathered.errors.push(TableError::UnknownClass {
                    pattern: rule.pattern.clone(),
                    class: rule.class.clone(),
                }),
            }
        }

        let mut expected = BTreeMap::new();
        for id in ids {
            let decided = match outcomes[id] {
                None => decided(id, most_specific(id, &covers, false), &mut gathered.errors)
                    .map(|entry| gathered.decide(entry)),
                Some(outcome) => self.term_case(id, outcome, &covers, &mut gathered),
            };
            if let Some(decided) = decided {
                expected.insert((*id).to_owned(), decided);
            }
        }
        for (entry, matched) in &covers {
            if let Entry::Refuse { rule, .. } = entry
                && !matched.is_empty()
                && !gathered.deciding.contains(rule.pattern.as_str())
            {
                gathered.errors.push(TableError::ShadowedRule {
                    pattern: rule.pattern.clone(),
                });
            }
        }
        for (name, class) in &self.classes {
            let Some(advice) = &class.advice else {
                continue;
            };
            if !known.contains(advice.as_str()) {
                gathered.errors.push(TableError::UnknownCase {
                    owner: format!("the advice of class {name:?}"),
                    id: advice.clone(),
                });
            } else if !matches!(expected.get(advice), Some(Expected::Accept(_))) {
                gathered.errors.push(TableError::AdviceNotAccepted {
                    class: name.clone(),
                    id: advice.clone(),
                });
            }
        }
        Resolution {
            expected,
            errors: gathered.errors,
            overridden: gathered.overridden,
        }
    }

    /// Decide every case of `cases`, the term cases by their oracle outcome ([`Self::resolve`]).
    #[must_use]
    pub fn resolve_cases<'t>(
        &'t self,
        cases: &[Case],
        kind: impl Fn(&str) -> Option<CodeKind>,
    ) -> Resolution<'t> {
        let ids = cases
            .iter()
            .map(|case| case.id.as_str())
            .collect::<Vec<_>>();
        let outcomes = cases
            .iter()
            .filter_map(|case| Some((case.id.as_str(), case.oracle()?)))
            .collect::<BTreeMap<_, _>>();
        self.resolve(&ids, |id| outcomes.get(id).copied(), kind)
    }

    /// Decide a term case by the families' precedence (the module's documentation): the
    /// oracle's placement refusal, the most specific refusal rule, the oracle's resolution
    /// refusal, the accept entry. `None`, with its error, when nothing decides.
    fn term_case<'t>(
        &'t self,
        id: &str,
        outcome: Outcome,
        covers: &[(Entry<'t>, BTreeSet<&str>)],
        gathered: &mut Gathered<'t>,
    ) -> Option<Expected<'t>> {
        let refusal = match outcome {
            Outcome::Refuse(refusal) if refusal.stage == Stage::Placement => Some(refusal),
            _ => match most_specific(id, covers, true) {
                Ok(Some(rule)) => {
                    if let Outcome::Refuse(refusal) = outcome {
                        gathered
                            .overridden
                            .insert(id.to_owned(), refusal.class.name());
                    }
                    let refused = gathered.decide(rule);
                    return Some(self.refused(id, refused, &mut gathered.errors));
                }
                Ok(None) => match outcome {
                    Outcome::Refuse(refusal) => Some(refusal),
                    Outcome::Accept => None,
                },
                tied @ Err(_) => {
                    return decided(id, tied, &mut gathered.errors)
                        .map(|rule| gathered.decide(rule));
                }
            },
        };
        let errors = &mut gathered.errors;
        let Some(refusal) = refusal else {
            let accepted = self.accept.get(id).map(Expected::Accept);
            return decided(id, Ok(accepted), errors);
        };
        let name = refusal.class.name();
        let Some(class) = self.classes.get(name) else {
            errors.push(TableError::UnknownOracleClass {
                id: id.to_owned(),
                class: name.to_owned(),
            });
            return None;
        };
        let refused = Expected::Refuse {
            name,
            class,
            at: if refusal.outer {
                At::Entry
            } else {
                At::Spelling
            },
        };
        Some(self.refused(id, refused, errors))
    }

    /// A term case's refusal, after checking that no accept entry names the case.
    fn refused<'t>(
        &self,
        id: &str,
        refused: Expected<'t>,
        errors: &mut Vec<TableError>,
    ) -> Expected<'t> {
        if let (true, Expected::Refuse { name, .. }) = (self.accept.contains_key(id), refused) {
            errors.push(TableError::AcceptsRefusedCase {
                id: id.to_owned(),
                class: name.to_owned(),
            });
        }
        refused
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
    fn expected(&self) -> Expected<'t> {
        match *self {
            Self::Accept(accepted) => Expected::Accept(accepted),
            Self::Refuse { rule, class } => Expected::Refuse {
                name: rule.class.as_str(),
                class,
                at: rule.at,
            },
        }
    }

    fn name(&self) -> String {
        match self {
            Self::Accept(_) => "accept".to_owned(),
            Self::Refuse { rule, .. } => format!("{:?}", rule.pattern),
        }
    }
}

/// What deciding the cases gathers besides their expectations.
struct Gathered<'t> {
    errors: Vec<TableError>,
    /// [`Resolution::overridden`].
    overridden: BTreeMap<String, &'static str>,
    /// The globs of the refusal rules that decide some case.
    deciding: BTreeSet<&'t str>,
}

impl<'t> Gathered<'t> {
    /// The expectation of the deciding `entry`, noting a rule that decides.
    fn decide(&mut self, entry: Entry<'t>) -> Expected<'t> {
        if let Entry::Refuse { rule, .. } = entry {
            self.deciding.insert(rule.pattern.as_str());
        }
        entry.expected()
    }
}

/// What decides `id`, given the most specific entry: `None`, with its error, when no entry
/// covers the case or entries tie.
fn decided<T>(
    id: &str,
    entry: Result<Option<T>, Vec<String>>,
    errors: &mut Vec<TableError>,
) -> Option<T> {
    match entry {
        Ok(Some(entry)) => Some(entry),
        Ok(None) => {
            errors.push(TableError::Uncovered { id: id.to_owned() });
            None
        }
        Err(entries) => {
            errors.push(TableError::Tie {
                id: id.to_owned(),
                entries,
            });
            None
        }
    }
}

/// The most specific entry of `covers` that covers `id` (a refusal rule, when `rules_only`):
/// `Ok(None)` when none does, `Err` with the entries that tie.
fn most_specific<'c, 't>(
    id: &str,
    covers: &'c [(Entry<'t>, BTreeSet<&str>)],
    rules_only: bool,
) -> Result<Option<Entry<'t>>, Vec<String>> {
    let covering = covers
        .iter()
        .filter(|(entry, covered)| {
            covered.contains(id) && !(rules_only && matches!(entry, Entry::Accept(_)))
        })
        .collect::<Vec<&'c (Entry<'t>, BTreeSet<&str>)>>();
    // The entries that no other covering entry is more specific than; in a finite order, a
    // single one is more specific than every other covering entry.
    let minimal = covering
        .iter()
        .filter(|(_, covered)| {
            !covering
                .iter()
                .any(|(_, other)| other.len() < covered.len() && other.is_subset(covered))
        })
        .collect::<Vec<_>>();
    match minimal.as_slice() {
        [] => Ok(None),
        [(entry, _)] => Ok(Some(*entry)),
        tied => Err(tied.iter().map(|(entry, _)| entry.name()).collect()),
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
        let fields = fields(
            class,
            &owner,
            &["code", "doc"],
            &["proposed", "advice"],
            errors,
        );
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
                advice: fields
                    .contains_key("advice")
                    .then(|| string(fields.get("advice"), &owner, "advice", errors)),
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
