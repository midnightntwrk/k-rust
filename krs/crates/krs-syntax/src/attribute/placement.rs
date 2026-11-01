//! The one place a marker's key that the marker does not take is refused.
//!
//! The table is the one description of which keys a marker takes ([`Marker::takes`]). Every
//! marker's parser (`#[k::rule]`, `#[k::equation]`, `#[k::claim]`, a static production's
//! `#[k::alias]`, ..) reads each key through [`taken`] before its own arms, so a key the table
//! does not give the marker never reaches them: it is refused here, with the marker it was
//! written on. A key that means something on another sentence is refused for what it is on this
//! one, with the code of that mistake, at the key; any other key is one the marker does not take.
//! So a key another marker takes never falls through to a generic payload or parser error, and a
//! key the table gives a marker whose parser has no arm for it is a disagreement the parser
//! reports as such ([`untaken`]), which the structural tests rule out.
//!
//! What each key means, and so where it is misplaced:
//! - an order (`owise`, `priority`, `nondet`) chooses among the sentences of one kind that match
//!   one term: transitions, and a function's equations (`nondet` only among transitions, since a
//!   function's equations define one value per argument). A claim is proved, a context and a
//!   context alias are ordered by their hole, and a static production's clauses rewrite each of
//!   its applications into one term, so none of them is chosen against another;
//! - `anywhere` lets a term-shaped transition rewrite its subject wherever it occurs;
//! - `concrete`, `symbolic` and `smt_lemma` restrict when an equation or a simplification applies;
//! - `result` names the sort a heated hole's evaluation ends in, on a sentence that heats one;
//! - `recursive` is a property of a static production, on its own marker (on a variant or after
//!   `#[k::constructor(..)]`), not on its clauses;
//! - `unbound_variables` names what a desugar clause's result leaves unbound;
//! - an initializer's and a constant's marker declare, and take no sentence key at all.

use proc_macro2::Span;
use syn::Ident;

use crate::{SyntaxError, SyntaxErrorKind};

use super::rule::{NONDET_ON_FUNCTION, OWISE_ON_SIMPLIFICATION, RESTRICTION_ON_RULE};
use super::sort::{RECURSIVE_ON_CLAUSE, unbound_variables_outside_desugar};

/// A marker whose keys are parsed by `krs-syntax`, with what it marks.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Marker {
    /// `#[k::rule(..)]`: a transition (a rule fn, a readable or `for Sort` clause).
    Rule,
    /// `#[k::equation(..)]`: a function's equation (a fn, a table row).
    Equation,
    /// `#[k::simplification(..)]`.
    Simplification,
    /// `#[k::claim(..)]`.
    Claim,
    /// `#[k::context(..)]`.
    Context,
    /// `#[k::context_alias(..)]`.
    ContextAlias,
    /// `#[k::alias]` on a static production's clause fn.
    AliasClause,
    /// `#[k::desugar]` on a static production's clause fn.
    DesugarClause,
    /// `#[k::alias]` or `#[k::desugar]` on the static production itself (a variant, or after
    /// `#[k::constructor(..)]`).
    StaticProduction,
    /// `#[k::init]`: declares the initial configuration.
    Initializer,
    /// `#[k::constant]`: declares a value.
    Constant,
}

impl Marker {
    /// Every marker.
    pub const ALL: [Self; 11] = [
        Self::Rule,
        Self::Equation,
        Self::Simplification,
        Self::Claim,
        Self::Context,
        Self::ContextAlias,
        Self::AliasClause,
        Self::DesugarClause,
        Self::StaticProduction,
        Self::Initializer,
        Self::Constant,
    ];

    /// The keys the marker takes, each one of [`SENTENCE_KEYS`]; every other key is
    /// [`misplaced_key`]'s. The marker's parser reads exactly these ([`taken`]). (A key taken may
    /// still be refused beside another, or by its value: that is the marker's own refusal.)
    #[must_use]
    pub const fn keys(self) -> &'static [&'static str] {
        match self {
            Self::Rule => &[
                "label", "owise", "priority", "nondet", "anywhere", "heat", "cool", "hole",
                "result",
            ],
            Self::Equation => &[
                "label",
                "owise",
                "priority",
                "concrete",
                "symbolic",
                "smt_lemma",
            ],
            Self::Simplification => &["label", "priority", "concrete", "symbolic", "smt_lemma"],
            Self::Claim => &["all_paths", "one_path", "label", "circularity", "trusted"],
            Self::Context => &["hole", "result", "label"],
            Self::ContextAlias => &["name", "here", "result"],
            Self::DesugarClause => &["unbound_variables"],
            Self::StaticProduction => &["recursive"],
            Self::AliasClause | Self::Initializer | Self::Constant => &[],
        }
    }

    /// Whether the marker takes `key` ([`Self::keys`]).
    #[must_use]
    pub fn takes(self, key: &str) -> bool {
        self.keys().contains(&key)
    }

    /// Whether the marker declares (the initial configuration, a value) rather than states a
    /// sentence or a production: no sentence key means anything on it.
    #[must_use]
    pub const fn declares(self) -> bool {
        matches!(self, Self::Initializer | Self::Constant)
    }
}

/// The keys some marker takes, each of which [`misplaced_key`] answers for what it is on a
/// marker that does not take it.
pub const SENTENCE_KEYS: [&str; 20] = [
    "label",
    "owise",
    "priority",
    "nondet",
    "anywhere",
    "heat",
    "cool",
    "hole",
    "result",
    "concrete",
    "symbolic",
    "smt_lemma",
    "all_paths",
    "one_path",
    "circularity",
    "trusted",
    "unbound_variables",
    "recursive",
    "name",
    "here",
];

/// The key `key`, written on `marker`: its name when the marker takes it, for the marker's
/// parser to read, and [`misplaced_key`]'s refusal otherwise.
///
/// # Errors
///
/// [`misplaced_key`]'s refusal of a key the marker does not take.
pub(crate) fn taken(marker: Marker, key: &Ident) -> Result<String, SyntaxError> {
    let name = key.to_string();
    if marker.takes(&name) {
        Ok(name)
    } else {
        Err(misplaced_key(marker, key))
    }
}

/// A key the table gives `marker` that its parser reads no arm for: the table and the parser
/// disagree, a mistake in KRS that the structural tests rule out
/// (`krs-syntax/tests/attributes.rs`), never the author's.
pub(crate) fn untaken(marker: Marker, key: &str) -> ! {
    unreachable!("the placement table gives {marker:?} the key `{key}`, and its parser reads none")
}

/// A claim is proved, not chosen among sentences.
pub(crate) const ORDER_ON_CLAIM: &str = "a claim is proved, not chosen among other sentences: an order (`owise`, `priority`, `nondet`) means nothing on it";
/// A context and a context alias are ordered by their hole.
pub(crate) const ORDER_ON_CONTEXT: &str = "a context or a context alias is ordered by its hole, not chosen among other sentences: an order (`owise`, `priority`, `nondet`) means nothing on it";
/// A static production's clauses expand each application into one term.
pub(crate) const ORDER_ON_STATIC_CLAUSE: &str = "a static production's clauses rewrite each of its applications into one term as it is read, so they never overlap and none is chosen against another: an order (`owise`, `priority`, `nondet`) means nothing on a clause";
/// A static production is rewritten by its clauses, none chosen against another.
pub(crate) const ORDER_ON_STATIC_PRODUCTION: &str = "a static production's clauses rewrite each of its applications into one term as it is read, so they never overlap and none is chosen against another: an order (`owise`, `priority`, `nondet`) means nothing on the production or its clauses";
/// `anywhere` outside a term-shaped transition.
pub(crate) const ANYWHERE_OUTSIDE_TRANSITION: &str = "`anywhere` lets a term-shaped `#[k::rule]` transition rewrite its subject wherever it occurs; this sentence is no transition";
/// `result` on a sentence that heats nothing.
pub(crate) const RESULT_WITHOUT_EVALUATION: &str = "`result` names the sort a heated hole's evaluation ends in, a key of a heating or cooling rule, a context and a context alias; this sentence heats nothing";
/// `recursive` on a sentence that is no static clause.
pub(crate) const RECURSIVE_ON_SENTENCE: &str = "`recursive` is a property of a static production, a key of its `#[k::alias]` or `#[k::desugar]` marker; a sentence has none";

/// The refusal of `key`, written on `marker`, which does not take it: the mistake the key makes
/// there ([module docs](self)), at the key.
#[must_use]
pub fn misplaced_key(marker: Marker, key: &Ident) -> SyntaxError {
    misplaced_key_named(marker, &key.to_string(), key.span())
}

/// [`misplaced_key`] of the key spelled `name` at `span`.
#[must_use]
pub fn misplaced_key_named(marker: Marker, name: &str, span: Span) -> SyntaxError {
    let rule_key = |reason| SyntaxError::new(SyntaxErrorKind::InvalidRuleKey { reason }, span);
    let unknown = || {
        SyntaxError::new(
            SyntaxErrorKind::UnknownArgument {
                name: name.to_owned(),
            },
            span,
        )
    };
    if marker.declares() {
        return unknown();
    }
    let function = matches!(marker, Marker::Equation | Marker::Simplification);
    let clause = matches!(marker, Marker::AliasClause | Marker::DesugarClause);
    match name {
        "owise" if marker == Marker::Simplification => rule_key(OWISE_ON_SIMPLIFICATION),
        "nondet" if function => rule_key(NONDET_ON_FUNCTION),
        "owise" | "priority" | "nondet" => match marker {
            Marker::Claim => rule_key(ORDER_ON_CLAIM),
            Marker::Context | Marker::ContextAlias => rule_key(ORDER_ON_CONTEXT),
            Marker::AliasClause | Marker::DesugarClause => rule_key(ORDER_ON_STATIC_CLAUSE),
            Marker::StaticProduction => rule_key(ORDER_ON_STATIC_PRODUCTION),
            Marker::Rule
            | Marker::Equation
            | Marker::Simplification
            | Marker::Initializer
            | Marker::Constant => unknown(),
        },
        "anywhere" if marker != Marker::Rule => rule_key(ANYWHERE_OUTSIDE_TRANSITION),
        "concrete" | "symbolic" | "smt_lemma" if !function => rule_key(RESTRICTION_ON_RULE),
        "result"
            if !matches!(
                marker,
                Marker::Rule | Marker::Context | Marker::ContextAlias
            ) =>
        {
            rule_key(RESULT_WITHOUT_EVALUATION)
        }
        "recursive" if clause => rule_key(RECURSIVE_ON_CLAUSE),
        "recursive" => rule_key(RECURSIVE_ON_SENTENCE),
        "unbound_variables" => unbound_variables_outside_desugar(span),
        _ => unknown(),
    }
}
