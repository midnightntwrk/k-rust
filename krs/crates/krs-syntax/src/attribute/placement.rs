//! The one place a marker's key that the marker does not take is refused.
//!
//! Every sentence marker (`#[k::rule]`, `#[k::equation]`, `#[k::claim]`, ..) parses the keys it
//! takes and hands every other key here, with the marker it was written on. A key that means
//! something on another sentence is refused for what it is on this one, with the code of that
//! mistake, at the key; any other key is one the marker does not take. So a key another marker
//! takes never falls through to a generic payload or parser error.
//!
//! What each key means, and so where it is misplaced:
//! - an order (`owise`, `priority`, `nondet`) chooses among the sentences of one kind that match
//!   one term: transitions, and a function's equations (`nondet` only among transitions, since a
//!   function is deterministic). A claim is proved, a context and a context alias are ordered by
//!   their hole, and a static production's clauses rewrite each of its applications into one
//!   term, so none of them is chosen against another;
//! - `anywhere` lets a term-shaped transition rewrite its subject wherever it occurs;
//! - `concrete`, `symbolic` and `smt_lemma` restrict when an equation or a simplification applies;
//! - `result` names the sort a heated hole's evaluation ends in, on a sentence that heats one;
//! - `recursive` is a property of a static production, on its own marker;
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
    /// `#[k::alias]` or `#[k::desugar]` on a static production's clause fn.
    StaticClause,
    /// `#[k::init]`: declares the initial configuration.
    Initializer,
    /// `#[k::constant]`: declares a value.
    Constant,
}

impl Marker {
    /// Every marker.
    pub const ALL: [Self; 9] = [
        Self::Rule,
        Self::Equation,
        Self::Simplification,
        Self::Claim,
        Self::Context,
        Self::ContextAlias,
        Self::StaticClause,
        Self::Initializer,
        Self::Constant,
    ];

    /// Whether the marker's own parser takes `key`, one of [`SENTENCE_KEYS`]; every other is
    /// [`misplaced_key`]'s. (A key taken may still be refused beside another, or by its value:
    /// that is the marker's own refusal.)
    #[must_use]
    pub fn takes(self, key: &str) -> bool {
        let keys: &[&str] = match self {
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
            Self::StaticClause | Self::Initializer | Self::Constant => &[],
        };
        keys.contains(&key)
    }

    /// Whether the marker declares (the initial configuration, a value) rather than states a
    /// sentence: no sentence key means anything on it.
    #[must_use]
    pub const fn declares(self) -> bool {
        matches!(self, Self::Initializer | Self::Constant)
    }
}

/// The keys some sentence marker takes, each of which [`misplaced_key`] answers for what it is
/// on a marker that does not take it.
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

/// A claim is proved, not chosen among sentences.
pub(crate) const ORDER_ON_CLAIM: &str = "a claim is proved, not chosen among other sentences: an order (`owise`, `priority`, `nondet`) means nothing on it";
/// A context and a context alias are ordered by their hole.
pub(crate) const ORDER_ON_CONTEXT: &str = "a context or a context alias is ordered by its hole, not chosen among other sentences: an order (`owise`, `priority`, `nondet`) means nothing on it";
/// A static production's clauses expand each application into one term.
pub(crate) const ORDER_ON_STATIC_CLAUSE: &str = "a static production's clauses rewrite each of its applications into one term as it is read, so they never overlap and none is chosen against another: an order (`owise`, `priority`, `nondet`) means nothing on a clause";
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
    match name {
        "owise" if marker == Marker::Simplification => rule_key(OWISE_ON_SIMPLIFICATION),
        "nondet" if function => rule_key(NONDET_ON_FUNCTION),
        "owise" | "priority" | "nondet" => match marker {
            Marker::Claim => rule_key(ORDER_ON_CLAIM),
            Marker::Context | Marker::ContextAlias => rule_key(ORDER_ON_CONTEXT),
            Marker::StaticClause => rule_key(ORDER_ON_STATIC_CLAUSE),
            _ => unknown(),
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
        "recursive" if marker == Marker::StaticClause => rule_key(RECURSIVE_ON_CLAUSE),
        "recursive" => rule_key(RECURSIVE_ON_SENTENCE),
        "unbound_variables" => unbound_variables_outside_desugar(span),
        _ => unknown(),
    }
}
