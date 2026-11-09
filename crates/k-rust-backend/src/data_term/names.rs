//! The names of the findings of a definition's full critical-pair check ([`Finding`]), by which
//! a client assumes a finding
//! ([`BackendDefinition::data_heads_assuming`](crate::definition::BackendDefinition::data_heads_assuming)).
//! Every client that prints a finding or reads an assumed name goes through this module, so a
//! name one client prints is the name another reads (k-rust-fuzz's `assume-joined` and
//! `definition-findings`, kink's `[spec] assume_joined`).
//!
//! # What a name is for
//!
//! A name is written into a premise: the author reviewed a finding the check could not decide
//! and states that it holds anyway (the pair joins, the equation agrees with its hook or applies
//! as written, the precondition is met). The premise is a proposition about the compiled
//! sentences the check read. So a name must keep naming the same proposition after any edit
//! that leaves those sentences alone, and must stop naming anything once they change, so that
//! a premise never silently assumes a pair nobody reviewed. A position in the generated K does
//! neither: an edit above a sentence moves it, and another finding can then occupy the old
//! position. A name is therefore its finding's kind and sentences, which an author reads, and a
//! digest of what the proposition is about.
//!
//! # The grammar
//!
//! ```text
//! root:A,B#D       two equations at the root (A and B sorted; either order is read)
//! self:A#D         an equation paired with itself (several matches of one left-hand side)
//! inner:A,B@1.0#D  A's left-hand side holds the position (argument indexes); B applies there
//! hook:A#D         an equation at an evaluated hook not shown to agree with the hook
//! equation:A#D     another equation the evaluator does not apply to every subject it describes
//! precondition:A#D             a precondition row about the equation A
//! precondition:KIND:SYMBOL..#D a precondition row naming no equation, with the K labels of its
//!                              symbols (`precondition:no-least-common-overload:A:B`)
//! ```
//!
//! A sentence `A` is its K label as K stores it; an unlabelled sentence `id:` and its
//! `UNIQUE_ID`; a compiler-generated overload axiom `overload:GREATER:LESSER`, the K labels of
//! its overloaded pair; a witness equation the check adopted `witness:` and the text it is
//! identified by. One of several equations internalized from one axiom (the alternatives of its
//! left-hand side) adds `~N`. Each word is quoted with `"` when it holds `,`, `@`, `#`, `~`,
//! `"`, `\`, whitespace, or a `:` outside a `::` ([`grammar::word`]). A front end may spell a
//! label its own way ([`Spelling`]: KRS spells a sentence by the item that wrote it,
//! `crate::plus_zero`); the kinds, positions and digest are the same under every spelling.
//!
//! A sentence with no label, no `UNIQUE_ID` and no generated part (hand-written KORE) has no
//! name: its findings cannot be assumed.
//!
//! # The digest
//!
//! `D` is 32 lowercase hexadecimal digits ([`digest`]): SHA-256, truncated to 128 bits, over the
//! digest's version, the kind, an inner pair's position, the hook or precondition row it states,
//! each of the finding's compiled sentences hashed by exclusion (the whole internalized rule but
//! its label, `UNIQUE_ID`, origins and derived attributes, variables renamed by first
//! occurrence) and the declarations of the symbols they apply (argument and result sorts and
//! symbol attributes). A root pair's sentences are hashed in the order of their names before any
//! spelling, so the order an author writes does not change `D`, and swapping two sentences'
//! labels does. It does not cover the subsort or overload relations of the sorts, nor any other
//! equation: what makes the premise true is re-checked on every run, and a change that decides
//! the finding refuses the premise (`decided`).
//!
//! # Matching
//!
//! A premise assumes the findings whose name is byte-equal to it, after reading it back
//! ([`canonical`]: a root pair's sentences sorted, needless quotes dropped). Several findings
//! share a name only when they are one proposition: the hook pairs of one equation (one per
//! equation of the hook's written meaning) are one `hook:` finding. Anything else is refused
//! ([`Refusal`], by [`classify`]).

pub mod digest;
pub mod grammar;

use std::collections::BTreeSet;
use std::sync::Arc;

pub use grammar::{
    Given, PositionName, Readable, Sentence, SentenceBase, parse, position_text, respell, word,
};

use super::Finding;
use crate::{
    confluence::{UnjoinedPair, UnjoinedReason, ViolationKind},
    definition::BackendDefinition,
    rule::{RewriteRule, RuleOrigin, TermIndex, term_index},
};

/// The kind of a finding as its name writes it (the module documentation).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FindingKind {
    Root,
    SelfPair,
    Inner,
    Hook,
    Equation,
    Precondition,
}

impl FindingKind {
    /// Every kind, in the order the documentation lists them.
    pub const ALL: [Self; 6] = [
        Self::Root,
        Self::SelfPair,
        Self::Inner,
        Self::Hook,
        Self::Equation,
        Self::Precondition,
    ];

    /// The keyword a name starts with.
    #[must_use]
    pub const fn keyword(self) -> &'static str {
        match self {
            Self::Root => "root",
            Self::SelfPair => "self",
            Self::Inner => "inner",
            Self::Hook => "hook",
            Self::Equation => "equation",
            Self::Precondition => "precondition",
        }
    }
}

/// One sentence of a finding: what it is called (an overload part with the KORE names of its
/// pair, which [`FindingName::readable`] writes as K labels) and where it is written, which a
/// document shows as information only.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NamedSentence {
    pub sentence: Sentence,
    /// The written position of its first sentence, `FILE:LINE:COLUMN`.
    pub at: Option<String>,
    /// Its `UNIQUE_ID` (else its label), which tells two equations apart.
    pub unique_id: Option<String>,
}

/// The name of one finding (the module documentation): its kind, its sentences (a root pair's
/// in the order its digest reads them), an inner pair's position, a precondition row that names
/// no equation, and the digest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FindingName {
    pub kind: FindingKind,
    pub sentences: Vec<NamedSentence>,
    pub position: Option<Vec<usize>>,
    pub row: Option<ViolationKind>,
    pub digest: String,
}

/// How a client writes the symbols and labels of a name: `symbol` maps a KORE symbol name to
/// the K label it encodes (k-rust's `kast::identifier::label_or_name`), and `sentence` gives a
/// front end's spelling of a K label, `None` to keep the label. [`Spelling::k`] keeps every
/// label, which is how names are matched.
#[derive(Clone, Copy)]
pub struct Spelling<'a> {
    pub symbol: &'a dyn Fn(&str) -> String,
    pub sentence: &'a dyn Fn(&str) -> Option<String>,
}

fn no_spelling(_: &str) -> Option<String> {
    None
}

impl<'a> Spelling<'a> {
    /// The K spelling: symbols decoded by `symbol`, every label kept.
    #[must_use]
    pub fn k(symbol: &'a dyn Fn(&str) -> String) -> Self {
        Self {
            symbol,
            sentence: &no_spelling,
        }
    }

    /// `name` as this spelling writes it.
    #[must_use]
    pub fn text(&self, name: &FindingName) -> String {
        name.text(self)
    }

    /// `name`, a name in the K spelling, as this spelling writes it (unchanged when it is no
    /// name of the grammar).
    #[must_use]
    pub fn respelled(&self, name: &str) -> String {
        respell(name, self.sentence).unwrap_or_else(|| name.to_owned())
    }
}

impl FindingName {
    /// The readable part, symbols written by `symbol`.
    #[must_use]
    pub fn readable(&self, symbol: &dyn Fn(&str) -> String) -> Readable {
        Readable {
            kind: self.kind,
            sentences: self
                .sentences
                .iter()
                .map(|named| decoded(&named.sentence, symbol))
                .collect(),
            position: self.position.clone(),
            row: self.row.as_ref().map(|row| row_parts(row, symbol)),
        }
    }

    /// The name as `spelling` writes it: the readable part, `#` and the digest.
    #[must_use]
    pub fn text(&self, spelling: &Spelling<'_>) -> String {
        format!(
            "{}#{}",
            self.readable(spelling.symbol).text(spelling.sentence),
            self.digest
        )
    }

    /// What tells the finding's proposition apart from another's with the same name: its
    /// kind, its sentences' unique ids, its position and its row. Two findings with one name
    /// and two keys would be [`Refusal::Ambiguous`].
    #[must_use]
    pub fn subjects(&self) -> String {
        format!(
            "{}|{}|{:?}|{:?}",
            self.kind.keyword(),
            self.sentences
                .iter()
                .map(|sentence| format!(
                    "{}~{:?}",
                    sentence.unique_id.as_deref().unwrap_or_default(),
                    sentence.sentence.alternative
                ))
                .collect::<Vec<_>>()
                .join(","),
            self.position,
            self.row
        )
    }
}

/// `sentence` with an overload part's KORE names written by `symbol`.
fn decoded(sentence: &Sentence, symbol: &dyn Fn(&str) -> String) -> Sentence {
    Sentence {
        base: match &sentence.base {
            SentenceBase::Overload(greater, lesser) => {
                SentenceBase::Overload(symbol(greater), symbol(lesser))
            }
            other => other.clone(),
        },
        alternative: sentence.alternative,
    }
}

/// A precondition row's kind and the K labels of its symbols, as words of a name.
fn row_parts(row: &ViolationKind, symbol: &dyn Fn(&str) -> String) -> Vec<String> {
    let kind = grammar::ROW_KINDS[match row {
        ViolationKind::ConstructorHeaded(_) => 0,
        ViolationKind::InjectionHeaded => 1,
        ViolationKind::IndexedAt(_) => 2,
        ViolationKind::OverloadShape(_) => 3,
        ViolationKind::NoLeastCommonOverload(..) => 4,
        ViolationKind::PinnedByInjectiveTotal(_) => 5,
    }]
    .to_owned();
    match row {
        ViolationKind::ConstructorHeaded(name)
        | ViolationKind::OverloadShape(name)
        | ViolationKind::PinnedByInjectiveTotal(name) => vec![kind, symbol(name)],
        ViolationKind::InjectionHeaded => vec![kind],
        ViolationKind::IndexedAt(index) => vec![kind, format!("{index:?}")],
        ViolationKind::NoLeastCommonOverload(first, second) => {
            vec![kind, symbol(first), symbol(second)]
        }
    }
}

/// The symbols a precondition row names, KORE names.
fn row_symbols(row: &ViolationKind) -> Vec<&str> {
    match row {
        ViolationKind::ConstructorHeaded(name)
        | ViolationKind::OverloadShape(name)
        | ViolationKind::PinnedByInjectiveTotal(name) => vec![name],
        ViolationKind::NoLeastCommonOverload(first, second) => vec![first, second],
        ViolationKind::InjectionHeaded | ViolationKind::IndexedAt(_) => Vec::new(),
    }
}

/// What a name calls `rule`: its label, else its overload part (KORE names), its witness text
/// or its `UNIQUE_ID`, with its alternative; `None` when it has none of these.
#[must_use]
pub fn sentence(rule: &RewriteRule) -> Option<Sentence> {
    let attributes = &rule.attributes;
    let base = if let Some(label) = &attributes.label {
        SentenceBase::Label(label.clone())
    } else if let Some((greater, lesser)) = &attributes.overload {
        SentenceBase::Overload(greater.to_string(), lesser.to_string())
    } else if let Some(witness) = attributes
        .identifier()
        .and_then(|id| id.strip_prefix("witness "))
    {
        SentenceBase::Witness(witness.to_owned())
    } else {
        SentenceBase::Id(attributes.identifier()?.to_owned())
    };
    Some(Sentence {
        base,
        alternative: rule.lhs_alternative,
    })
}

/// The written position of `rule`'s first sentence, `FILE:LINE:COLUMN`.
fn written(rule: &RewriteRule) -> Option<String> {
    rule.attributes
        .origins
        .first()
        .and_then(RuleOrigin::written_position)
}

fn named(rule: &RewriteRule) -> Option<NamedSentence> {
    Some(NamedSentence {
        sentence: sentence(rule)?,
        at: written(rule),
        unique_id: rule
            .attributes
            .identifier()
            .map(str::to_owned)
            .or_else(|| rule.attributes.label.clone()),
    })
}

/// Whether a pair is an equation paired with itself.
fn self_pair(pair: &UnjoinedPair) -> bool {
    pair.position.is_empty()
        && (Arc::ptr_eq(&pair.first, &pair.second) || pair.first == pair.second)
}

/// The kind of a finding about one equation: `hook` for an equation at an evaluated hook not
/// shown to agree with it, `equation` otherwise.
#[must_use]
pub fn equation_kind(pair: &UnjoinedPair) -> FindingKind {
    if hook_of(pair).is_some() {
        FindingKind::Hook
    } else {
        FindingKind::Equation
    }
}

/// The hook a hook finding states its equation agrees with.
fn hook_of(pair: &UnjoinedPair) -> Option<&str> {
    match (&pair.hook, &pair.reason) {
        (Some(hook), _) | (None, UnjoinedReason::UnmodelledHook(hook)) => Some(hook),
        _ => None,
    }
}

/// The digest of a finding of `kind` about `rules` (in the order given) of `definition`.
fn digest_of(
    definition: &BackendDefinition,
    kind: FindingKind,
    position: Option<&[usize]>,
    rules: &[&RewriteRule],
    hook: Option<&str>,
    row: Option<&ViolationKind>,
) -> String {
    let mut writer = digest::Writer::new(kind.keyword());
    if let Some(position) = position {
        writer.text(b'P', &position_text(position));
    }
    if let Some(hook) = hook {
        writer.text(b'h', hook);
    }
    if let Some(row) = row {
        writer.text(b'w', &format!("{row:?}"));
        for symbol in row_symbols(row) {
            writer.symbol(symbol);
        }
    }
    writer.number(b'n', rules.len() as u64);
    for rule in rules {
        writer.rule(rule);
    }
    writer.finish(definition)
}

/// The name of `finding` of `definition`'s full check (the module documentation); `None` when
/// a sentence it is about has no name.
#[must_use]
pub fn finding_name(definition: &BackendDefinition, finding: &Finding) -> Option<FindingName> {
    match finding {
        Finding::Pair { pair, .. } => {
            let kind = if self_pair(pair) {
                FindingKind::SelfPair
            } else if pair.position.is_empty() {
                FindingKind::Root
            } else {
                FindingKind::Inner
            };
            let mut subjects = vec![
                (named(&pair.first)?, &*pair.first),
                (named(&pair.second)?, &*pair.second),
            ];
            match kind {
                FindingKind::SelfPair => subjects.truncate(1),
                FindingKind::Root => {
                    subjects.sort_by(|(left, _), (right, _)| left.sentence.cmp(&right.sentence));
                }
                _ => {}
            }
            let position = (kind == FindingKind::Inner).then(|| pair.position.clone());
            let rules = subjects.iter().map(|(_, rule)| *rule).collect::<Vec<_>>();
            let digest = digest_of(definition, kind, position.as_deref(), &rules, None, None);
            Some(FindingName {
                kind,
                sentences: subjects.into_iter().map(|(named, _)| named).collect(),
                position,
                row: None,
                digest,
            })
        }
        Finding::Equation(pair) => {
            let kind = equation_kind(pair);
            Some(FindingName {
                kind,
                sentences: vec![named(&pair.first)?],
                position: None,
                row: None,
                digest: digest_of(definition, kind, None, &[&pair.first], hook_of(pair), None),
            })
        }
        Finding::Precondition(violation) => {
            let (sentences, rules, row) = match &violation.rule {
                Some(rule) => (vec![named(rule)?], vec![&**rule], None),
                None => (Vec::new(), Vec::new(), Some(violation.kind.clone())),
            };
            Some(FindingName {
                kind: FindingKind::Precondition,
                sentences,
                position: None,
                row,
                digest: digest_of(
                    definition,
                    FindingKind::Precondition,
                    None,
                    &rules,
                    None,
                    Some(&violation.kind),
                ),
            })
        }
    }
}

/// Why a premise is refused ([`classify`]); [`Refusal::reason`] is its code.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Refusal {
    /// It is no name of the grammar.
    Malformed(String),
    /// A name of the former grammar, by the generated K's positions: the names of the findings
    /// at that position now, for the author to review.
    PositionName { located: Vec<String> },
    /// A name of the former grammar at a finding whose sentence has no name: the finding's
    /// description.
    UnnamedSentence { descriptions: Vec<String> },
    /// No digest: the names of the findings whose readable part is the premise's.
    NoDigest { candidates: Vec<String> },
    /// The readable part names findings whose digest differs: each one's name and description.
    Changed { current: Vec<(String, String)> },
    /// It names no finding.
    NoFinding,
    /// The check decides the finding: why.
    Decided { why: String },
    /// The sentences are unchanged and the check no longer reports the finding: it now joins,
    /// so nothing is left to assume (code `decided`).
    Resolved,
    /// One name, several propositions: their descriptions.
    Ambiguous { descriptions: Vec<String> },
}

impl Refusal {
    /// The refusal's code.
    #[must_use]
    pub const fn reason(&self) -> &'static str {
        match self {
            Self::Malformed(_) => "malformed",
            Self::PositionName { .. } => "position-name",
            Self::UnnamedSentence { .. } => "unnamed-sentence",
            Self::NoDigest { .. } => "no-digest",
            Self::Changed { .. } => "changed",
            Self::NoFinding => "no-finding",
            Self::Decided { .. } | Self::Resolved => "decided",
            Self::Ambiguous { .. } => "ambiguous",
        }
    }

    /// The names the refusal lists.
    fn mentioned(&self) -> Vec<&str> {
        match self {
            Self::PositionName { located } => located.iter().map(String::as_str).collect(),
            Self::NoDigest { candidates } => candidates.iter().map(String::as_str).collect(),
            Self::Changed { current } => current.iter().map(|(name, _)| name.as_str()).collect(),
            _ => Vec::new(),
        }
    }

    /// Why the premise `given` is refused, in words, ending with a suggestion to label a
    /// sentence wherever an unlabelled one (`id:`) is involved.
    #[must_use]
    pub fn detail(&self, given: &str) -> String {
        let list = |names: &[String]| {
            names
                .iter()
                .map(|name| format!("`{name}`"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let text = match self {
            Self::Malformed(why) => format!(
                "it is not a finding's name ({why}); a name is `KIND:SENTENCES#DIGEST` as the \
                 documents print it"
            ),
            Self::PositionName { located } if located.is_empty() => {
                "it names a finding by its position in the generated K, which another finding \
                 can occupy after an edit; findings are named by their kind, sentences and \
                 digest now, and no finding is at that position"
                    .to_owned()
            }
            Self::PositionName { located } => format!(
                "it names a finding by its position in the generated K, which another finding \
                 can occupy after an edit; findings are named by their kind, sentences and \
                 digest now. At that position now: {}; review each before naming it",
                list(located)
            ),
            Self::UnnamedSentence { descriptions } => format!(
                "it names by position {}, whose sentence has no label, UNIQUE_ID or generated \
                 part, so no name can assume it; give the sentence a label",
                descriptions.join("; ")
            ),
            Self::NoDigest { candidates } => format!(
                "it has no digest (`#...`), which pins the compiled sentences the premise was \
                 reviewed for; the finding(s) it reads as now: {}; review and write the whole \
                 name",
                list(candidates)
            ),
            Self::Changed { current } => format!(
                "the sentences it names changed since the premise was written (the digest \
                 differs), so it no longer names the proposition that was reviewed; now: {}; \
                 review the finding again before replacing the name",
                current
                    .iter()
                    .map(|(name, description)| format!("`{name}` ({description})"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::NoFinding => {
                "it names no finding of the definition's full critical-pair check".to_owned()
            }
            Self::Decided { why } => why.clone(),
            Self::Resolved => "its sentences are unchanged and the check now joins it (it is no \
                               finding any more): nothing is left to assume; remove the name"
                .to_owned(),
            Self::Ambiguous { descriptions } => format!(
                "it names {} different findings with one name, which should not happen ({}); \
                 report it",
                descriptions.len(),
                descriptions.join("; ")
            ),
        };
        let involves_id = |name: &str| matches!(parse(name), Ok(Given::Name { readable, .. }) if readable.has_id());
        if involves_id(given) || self.mentioned().into_iter().any(involves_id) {
            format!(
                "{text}; an `id:` sentence is an unlabelled one named by its UNIQUE_ID, which \
                 changes with any edit of its text: give it a label (`rule [NAME]:` or \
                 `[label(NAME)]`) so that its name reads and survives reformatting"
            )
        } else {
            text
        }
    }
}

/// One finding of a check with its name, as [`classify`] reads it.
#[derive(Clone, Copy)]
pub struct Candidate<'f> {
    pub finding: &'f Finding,
    pub name: Option<&'f FindingName>,
}

/// Whether a premise may assume `finding`: an undecided finding (not genuine, which would make
/// the premise known false, and not decided, a fact no premise removes).
#[must_use]
pub fn assumable(finding: &Finding) -> bool {
    !finding.is_decided() && !finding.is_genuine()
}

/// `given` read back as a name of the grammar with a digest, labels kept as written (a root
/// pair's sentences sorted, needless quotes dropped): what a finding's name in the same
/// spelling is compared with, byte for byte. `None` for anything else, which assumes nothing.
#[must_use]
pub fn canonical(given: &str) -> Option<String> {
    match parse(given).ok()? {
        Given::Name {
            readable,
            digest: Some(digest),
        } => Some(format!("{}#{digest}", readable.text(&no_spelling))),
        Given::Name { digest: None, .. } | Given::Position(_) => None,
    }
}

/// Which of `candidates` the premise `given` assumes, by index, or why it is refused (the
/// module documentation, "Matching"). Names are compared in the K spelling: `given` is one,
/// and `spelling` writes the names a refusal lists. `definition` is the definition the
/// findings are of, read to tell a finding the check now joins (its sentences unchanged) from
/// one whose sentences are gone.
///
/// # Errors
///
/// The [`Refusal`]: `malformed`, `position-name`, `unnamed-sentence`, `no-digest`, `changed`,
/// `no-finding`, `decided` (a decided or genuine finding, or one the check now joins) or
/// `ambiguous`.
pub fn classify(
    given: &str,
    candidates: &[Candidate<'_>],
    definition: &BackendDefinition,
    spelling: &Spelling<'_>,
) -> Result<Vec<usize>, Refusal> {
    let k = Spelling::k(spelling.symbol);
    let (readable, digest) = match parse(given).map_err(Refusal::Malformed)? {
        Given::Position(position) => return Err(located(&position, candidates, spelling)),
        Given::Name { readable, digest } => (readable, digest),
    };
    let readable_text = readable.text(&no_spelling);
    let same_readable = || {
        candidates
            .iter()
            .filter_map(|candidate| {
                let name = candidate.name?;
                (name.readable(spelling.symbol).text(&no_spelling) == readable_text)
                    .then_some((candidate, name))
            })
            .collect::<Vec<_>>()
    };
    let Some(digest) = digest else {
        let candidates = same_readable()
            .into_iter()
            .map(|(_, name)| spelling.text(name))
            .collect::<BTreeSet<_>>();
        return Err(if candidates.is_empty() {
            Refusal::NoFinding
        } else {
            Refusal::NoDigest {
                candidates: candidates.into_iter().collect(),
            }
        });
    };
    let given = format!("{readable_text}#{digest}");
    let matched = candidates
        .iter()
        .enumerate()
        .filter(|(_, candidate)| candidate.name.is_some_and(|name| k.text(name) == given))
        .collect::<Vec<_>>();
    if matched.is_empty() {
        let current = same_readable()
            .into_iter()
            .map(|(candidate, name)| {
                (
                    spelling.text(name),
                    candidate.finding.describe(spelling.symbol),
                )
            })
            .collect::<BTreeSet<_>>();
        if !current.is_empty() {
            return Err(Refusal::Changed {
                current: current.into_iter().collect(),
            });
        }
        if resolved(definition, &readable, &digest, spelling.symbol) {
            return Err(Refusal::Resolved);
        }
        return Err(Refusal::NoFinding);
    }
    let subjects = matched
        .iter()
        .filter_map(|(_, candidate)| candidate.name.map(FindingName::subjects))
        .collect::<BTreeSet<_>>();
    if subjects.len() > 1 {
        return Err(Refusal::Ambiguous {
            descriptions: matched
                .iter()
                .map(|(_, candidate)| candidate.finding.describe(spelling.symbol))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
        });
    }
    if let Some((_, decided)) = matched
        .iter()
        .find(|(_, candidate)| candidate.finding.is_decided())
    {
        return Err(Refusal::Decided {
            why: format!(
                "it names a decided finding ({}), a fact about the definition as written that \
                 no premise removes",
                decided.finding.describe(spelling.symbol)
            ),
        });
    }
    if let Some((_, genuine)) = matched
        .iter()
        .find(|(_, candidate)| candidate.finding.is_genuine())
    {
        return Err(Refusal::Decided {
            why: format!(
                "the check shows it genuine ({}): a ground input has two normal forms, so the \
                 premise would be known to be false; fix the definition",
                genuine.finding.describe(spelling.symbol)
            ),
        });
    }
    Ok(matched.into_iter().map(|(index, _)| index).collect())
}

/// The refusal of a name of the former grammar: the findings at its position, by their names,
/// or `unnamed-sentence` when one of them has no name.
fn located(
    position: &PositionName,
    candidates: &[Candidate<'_>],
    spelling: &Spelling<'_>,
) -> Refusal {
    let at = candidates
        .iter()
        .filter(|candidate| former_names(position, candidate.finding, spelling.symbol))
        .collect::<Vec<_>>();
    let unnamed = at
        .iter()
        .filter(|candidate| candidate.name.is_none())
        .map(|candidate| candidate.finding.describe(spelling.symbol))
        .collect::<BTreeSet<_>>();
    if !unnamed.is_empty() {
        return Refusal::UnnamedSentence {
            descriptions: unnamed.into_iter().collect(),
        };
    }
    Refusal::PositionName {
        located: at
            .iter()
            .filter_map(|candidate| candidate.name.map(|name| spelling.text(name)))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect(),
    }
}

/// Whether a rule part of the former grammar names `rule`: its written position or any
/// trailing part of it after a `/`, its unique id, its label, or its overload part.
fn former_names_rule(given: &str, rule: &RewriteRule, symbol: &dyn Fn(&str) -> String) -> bool {
    let given = given.trim();
    if given.is_empty() {
        return false;
    }
    written(rule).is_some_and(|written| {
        written == given
            || written
                .strip_suffix(given)
                .is_some_and(|prefix| prefix.ends_with('/'))
    }) || rule.attributes.identifier() == Some(given)
        || rule.attributes.label.as_deref() == Some(given)
        || rule
            .attributes
            .overload
            .as_ref()
            .is_some_and(|(greater, lesser)| {
                given == format!("overload:{greater}:{lesser}")
                    || given == format!("overload:{}:{}", symbol(greater), symbol(lesser))
            })
}

/// Whether the former grammar's name `position` names `finding`.
fn former_names(
    position: &PositionName,
    finding: &Finding,
    symbol: &dyn Fn(&str) -> String,
) -> bool {
    match (position.kind, finding, position.parts.as_slice()) {
        (None, Finding::Pair { pair, .. }, [first, second]) => {
            position.position.as_deref().map(str::trim) == Some(&*position_text(&pair.position))
                && ((former_names_rule(first, &pair.first, symbol)
                    && former_names_rule(second, &pair.second, symbol))
                    || (pair.position.is_empty()
                        && former_names_rule(first, &pair.second, symbol)
                        && former_names_rule(second, &pair.first, symbol)))
        }
        (Some(kind), Finding::Equation(pair), [part]) => {
            equation_kind(pair) == kind && former_names_rule(part, &pair.first, symbol)
        }
        (Some(FindingKind::Precondition), Finding::Precondition(violation), [part]) => violation
            .rule
            .as_ref()
            .is_some_and(|rule| former_names_rule(part, rule, symbol)),
        _ => false,
    }
}

/// Whether the sentences `readable` names are still equations of `definition` with the digest
/// `digest`: then a premise naming them names no finding only because the check now joins it.
/// Only names of equations are read (a precondition row is a fact the check reports, not a
/// proposition it can join).
fn resolved(
    definition: &BackendDefinition,
    readable: &Readable,
    digest: &str,
    symbol: &dyn Fn(&str) -> String,
) -> bool {
    let kind = readable.kind;
    if kind == FindingKind::Precondition {
        return false;
    }
    let equations = definition
        .function_theory()
        .values()
        .flat_map(|priorities| priorities.values().flatten())
        .collect::<Vec<_>>();
    let named = |wanted: &Sentence| {
        equations
            .iter()
            .filter(|rule| {
                sentence(rule).is_some_and(|sentence| decoded(&sentence, symbol) == *wanted)
            })
            .map(|rule| &***rule)
            .collect::<Vec<_>>()
    };
    let hook = |rule: &RewriteRule| match term_index(&rule.lhs) {
        TermIndex::Symbol(name) => definition
            .symbols()
            .get(&name)
            .and_then(|symbol| symbol.attributes.hook.as_ref())
            .map(ToString::to_string),
        _ => None,
    };
    let reproduces = |rules: &[&RewriteRule], hook: Option<&str>| {
        digest_of(
            definition,
            kind,
            readable.position.as_deref(),
            rules,
            hook,
            None,
        ) == digest
    };
    match readable.sentences.as_slice() {
        [first, second] => {
            let (firsts, seconds) = (named(first), named(second));
            firsts.iter().any(|first| {
                seconds.iter().any(|second| {
                    let mut rules = [(sentence(first), *first), (sentence(second), *second)];
                    if kind == FindingKind::Root {
                        rules.sort_by(|(left, _), (right, _)| left.cmp(right));
                    }
                    reproduces(&[rules[0].1, rules[1].1], None)
                })
            })
        }
        [only] => named(only).iter().any(|rule| match kind {
            FindingKind::Hook => reproduces(&[rule], hook(rule).as_deref()),
            _ => reproduces(&[rule], None),
        }),
        _ => false,
    }
}
